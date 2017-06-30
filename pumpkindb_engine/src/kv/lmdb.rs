// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::*;

use core::ops::Deref;
use std::sync::atomic::{AtomicBool, Ordering};

use lmdb;

use std::io;
use std::fs;
#[cfg(not(target_os = "windows"))]
use std::path;
#[cfg(not(target_os = "windows"))]
use std::ffi::CString;
#[cfg(not(target_os = "windows"))]
use libc::statvfs;
#[cfg(not(target_os = "windows"))]
use alloc::heap;
#[cfg(not(target_os = "windows"))]
use core::mem::size_of;

use std::sync::Arc;

pub struct LmdbError(lmdb::Error);

impl Into<Error> for LmdbError {
    fn into(self) -> Error {
        match self.0 {
            lmdb::Error::Code(cint) => Error::Code(cint as i64),
            _ => Error::UnknownError,
        }
    }
}

pub struct LmdbKeyValueStore<'a> {
    db: Arc<lmdb::Database<'a>>,
    env: &'a lmdb::Environment,
    live_writer: Arc<AtomicBool>,
    maxreaders: usize,
}

impl<'a> LmdbKeyValueStore<'a> {
    pub fn new(env: &'a lmdb::Environment) -> Result<LmdbKeyValueStore<'a>, Error> {
        if !env.flags().unwrap().contains(lmdb::open::NOTLS) {
            return Err(Error::Misconfiguration(String::from("env should have NOTLS enabled")));
        }
        Ok(LmdbKeyValueStore {
            env,
            db: Arc::new(lmdb::Database::open(env, None, &lmdb::DatabaseOptions::new(lmdb::db::CREATE))
                .map_err(|v| LmdbError(v).into())?),
            live_writer: Arc::new(AtomicBool::new(false)),
            maxreaders: env.maxreaders().map(|v| v as usize).map_err(|v| LmdbError(v).into())?
        })
    }
}

pub trait Access<'a> {
    type T : Deref<Target = lmdb::ConstAccessor<'a>>;
    fn access(&'a self) -> Self::T;
}

pub struct LmdbCursor<'a : 'txn, 'txn, T : Access<'a> + 'a> {
    txn: &'a T,
    cursor: lmdb::Cursor<'a, 'txn>,
    positioned: bool
}

impl<'a : 'txn, 'txn, T : Access<'a> + 'a> LmdbCursor<'a, 'txn, T> {
    pub fn new(txn: &'a T, cursor: lmdb::Cursor<'a, 'txn>) -> Self {
        LmdbCursor {
            txn,
            cursor,
            positioned: false
        }
    }

}

macro_rules! cursor_op {
  ($this: ident, $name: ident, $($arg : expr),*) => {{
     let access = $this.txn.access();
     $this.cursor.$name::<[u8], [u8]>(&access, $($arg)*)
         .map(|_| $this.positioned = true)
         .map_err(|v| LmdbError(v).into())
  }};
}

impl<'a : 'txn, 'txn, T : Access<'a> + 'a> Cursor for LmdbCursor<'a, 'txn, T> {
    fn first(&mut self) -> Result<(), Error> {
        cursor_op!(self, first,)
    }

    fn last(&mut self) -> Result<(), Error> {
        cursor_op!(self, last,)
    }

    fn next(&mut self) -> Result<(), Error> {
        cursor_op!(self, next,)
    }

    fn prev(&mut self) -> Result<(), Error> {
        cursor_op!(self, prev,)
    }

    fn seek_range_k(&mut self, key: &[u8]) -> Result<(), Error> {
        cursor_op!(self, seek_range_k, key)
    }

    fn is_positioned(&self) -> bool {
        self.positioned
    }

    fn current_key<'b, A: Allocator<'b>>(&mut self, allocator: &mut A) -> Option<&'b [u8]> {
        if self.is_positioned() {
            let access = self.txn.access();
            match self.cursor.get_current::<[u8], [u8]>(&access) {
                Ok((k, _)) => {
                    let mut slice = allocator.alloc(k.len());
                    slice.copy_from_slice(k);
                    Some(slice)
                },
                Err(_) => None
            }
        } else {
            None
        }
    }

    fn current_value<'b, A: Allocator<'b>>(&mut self, allocator: &mut A) -> Option<&'b [u8]> {
        if self.is_positioned() {
            let access = self.txn.access();
            match self.cursor.get_current::<[u8], [u8]>(&access) {
                Ok((_, v)) => {
                    let mut slice = allocator.alloc(v.len());
                    slice.copy_from_slice(v);
                    Some(slice)
                }
                Err(_) => None
            }
        } else {
            None
        }
    }
}



pub struct LmdbReadTransaction<'a>(lmdb::ReadTransaction<'a>, Arc<lmdb::Database<'a>>);

impl<'a> LmdbReadTransaction<'a> {
    pub(crate) fn new(txn: lmdb::ReadTransaction<'a>, db: Arc<lmdb::Database<'a>>) -> Self {
        LmdbReadTransaction(txn, db)
    }
}

pub struct ConstAccessorWrapper<'a>(lmdb::ConstAccessor<'a>);

impl<'a> Deref for ConstAccessorWrapper<'a> {
    type Target = lmdb::ConstAccessor<'a>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> Access<'a> for LmdbReadTransaction<'a> {
    type T = ConstAccessorWrapper<'a>;
    fn access(&'a self) -> Self::T {
        ConstAccessorWrapper(self.0.access())
    }
}

impl<'t> ReadTransaction for LmdbReadTransaction<'t> {
//    type Cursor = LmdbCursor<'t, 't, LmdbReadTransaction<'t>>;
//    fn cursor<'c>(&'c self) -> Result<LmdbCursor<'c, 'c, LmdbReadTransaction<'c>>, Error> {
    fn cursor<'c, C : 'c>(&'c self) -> Result<C, Error> {
        match self.0.cursor(&*self.1).map_err(|v| LmdbError(v).into()) {
            Err(err) => Err(err),
            Ok(v) => Ok(LmdbCursor::new(self, v))
        }
    }

    fn get<'a, A : Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
        let access = self.0.access();
        match access.get::<[u8], [u8]>(&self.1, key).to_opt().map_err(|v| LmdbError(v).into()) {
            Ok(Some(v)) => {
                let mut slice = allocator.alloc(v.len());
                slice.copy_from_slice(v);
                Ok(slice)
            },
            Ok(None) => Err(Error::UnknownKey),
            Err(e) => Err(e),
        }
    }
}


pub struct LmdbWriteTransaction<'a>(lmdb::WriteTransaction<'a>, Arc<lmdb::Database<'a>>, Arc<AtomicBool>);

impl<'a> LmdbWriteTransaction<'a> {
    pub(crate) fn new(txn: lmdb::WriteTransaction<'a>, db: Arc<lmdb::Database<'a>>,
                      live_writer: Arc<AtomicBool>) -> Self {
        LmdbWriteTransaction(txn, db, live_writer)
    }
}

impl<'a> Drop for LmdbWriteTransaction<'a> {
    fn drop(&mut self) {
        self.2.compare_and_swap(true, false, Ordering::SeqCst);
    }
}

use lmdb::traits::LmdbResultExt;
impl<'t> ReadTransaction for LmdbWriteTransaction<'t> {
//    type Cursor = LmdbCursor<'t, 't, LmdbWriteTransaction<'t>>;

    fn cursor<'c, C : 'c>(&'c self) -> Result<C, Error> {
//    fn cursor<'c>(&'c self) -> Result<LmdbCursor<'c, 'c, LmdbReadTransaction<'c>>, Error> {
//    fn cursor(&self) -> Result<Self::Cursor, Error> {
        match self.0.cursor(self.1).map_err(|v| LmdbError(v).into()) {
            Err(err) => Err(err),
            Ok(v) => Ok(LmdbCursor::new(self, v))
        }
    }

    fn get<'a, A : Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
        let access = self.0.access();
        match access.get::<[u8], [u8]>(&self.1, key).to_opt().map_err(|v| LmdbError(v).into()) {
            Ok(Some(v)) => {
                let mut slice = allocator.alloc(v.len());
                slice.copy_from_slice(v);
                Ok(slice)
            },
            Ok(None) => Err(Error::UnknownKey),
            Err(e) => Err(e),
        }
    }
}

impl<'a> Access<'a> for LmdbWriteTransaction<'a> {
    type T = lmdb::WriteAccessor<'a>;
    fn access(&'a self) -> Self::T {
        self.0.access()
    }
}
impl<'t> WriteTransaction for LmdbWriteTransaction<'t> {
    fn commit(self) -> Result<(), Error> {
        self.0.commit().map_err(|v| LmdbError(v).into())
    }
    fn put<'a>(&self, key: &'a [u8], value: &'a [u8]) -> Result<(), Error> {
        let mut access = self.0.access();
        match access.put(&self.1, key, value, lmdb::put::NOOVERWRITE) {
            Ok(_) => Ok(()),
            Err(lmdb::Error::Code(code)) if lmdb::error::KEYEXIST == code => Err(Error::DuplicateKey),
            Err(err) => Err(LmdbError(err).into()),
        }
    }
}

impl<'a> KeyValueStore for LmdbKeyValueStore<'a> {
    type WriteTransaction = LmdbWriteTransaction<'a>;
    type ReadTransaction = LmdbReadTransaction<'a>;
    type Error = lmdb::Error;

    fn read_transaction(&self) -> Result<Self::ReadTransaction, TransactionOriginationError<Self::Error>> {
        lmdb::ReadTransaction::new(self.env)
            .map(|txn| LmdbReadTransaction::new(txn, self.db.clone()))
            .map_err(|v|
                match v {
                    // MDB_READERS_FULL
                    lmdb::Error::Code(-30790) =>
                        TransactionOriginationError::TransactionLimitReached(self.maxreaders),
                    v =>
                        TransactionOriginationError::DatabaseError(v),
                })
    }

    fn write_transaction(&self) -> Result<Self::WriteTransaction, TransactionOriginationError<Self::Error>> {
        match self.live_writer.compare_and_swap(false, true, Ordering::SeqCst) {
            false => lmdb::WriteTransaction::new(self.env)
                .map(|txn| LmdbWriteTransaction::new(txn, self.db.clone(), self.live_writer.clone()))
                .map_err(|v| TransactionOriginationError::DatabaseError(v)),
            true => Err(TransactionOriginationError::TransactionLimitReached(1)),
        }
    }
    fn max_readers(&self) -> usize {
        self.maxreaders
    }

    fn max_writers(&self) -> usize {
        1
    }
    fn max_keysize(&self) -> u32 {
        511
    }
}

#[derive(Debug)]
pub enum EnvironmentCreationError {
    LmdbError(lmdb::Error),
    IoError(io::Error)
}

impl From<lmdb::Error> for EnvironmentCreationError {
    fn from(e: lmdb::Error) -> Self {
        EnvironmentCreationError::LmdbError(e)
    }
}

impl From<io::Error> for EnvironmentCreationError {
    fn from(e: io::Error) -> Self {
        EnvironmentCreationError::IoError(e)
    }
}

pub fn create_environment(storage_path: String,
                          map_size: Option<i64>,
                          maxreaders: Option<u32>) -> Result<lmdb::Environment, EnvironmentCreationError> {
    unsafe {
        let mut env_builder = lmdb::EnvBuilder::new()?;

        // Configure map size
        if !cfg!(target_os = "windows") && map_size.is_none() {
            #[cfg(not(target_os = "windows"))]
                {
                    let path = path::PathBuf::from(storage_path.as_str());
                    let canonical = fs::canonicalize(&path)?;
                    let absolute_path = canonical.as_path().to_str().unwrap();
                    let absolute_path_c = CString::new(absolute_path).unwrap();
                    let statp: *mut statvfs =
                        heap::allocate(size_of::<statvfs>(), size_of::<usize>()) as *mut statvfs;
                    let mut stat = *statp;
                    if statvfs(absolute_path_c.as_ptr(), &mut stat) != 0 {
                        warn!("Can't determine available disk space");
                    } else {
                        let size = (stat.f_frsize * stat.f_bavail as u64) as usize;
                        info!("Available disk space is approx. {}Gb, setting database map size to it",
                        size / (1024 * 1024 * 1024));
                        env_builder.set_mapsize(size)?;
                    }
                    heap::deallocate(statp as *mut u8, size_of::<statvfs>(), size_of::<usize>());
                }
        } else {
            match map_size {
                Some(mapsize) => {
                    env_builder.set_mapsize(1024 * mapsize as usize).expect("can't set map size");
                }
                None => {
                    warn!("No default storage.mapsize set, setting it to 1Gb");
                    env_builder.set_mapsize(1024 * 1024 * 1024).expect("can't set map size");
                }
            }
        }
        if let Some(max) = maxreaders {
            env_builder.set_maxreaders(max)?;
        }

        Ok(env_builder.open(storage_path.as_str(), lmdb::open::NOTLS, 0o600)?)
    }
}

#[cfg(test)]
mod tests {

    use std::fs;
    use tempdir::TempDir;

    use kv::lmdb;
    use kv::KeyValueStore;

    #[test]
    pub fn read_limit() {
        let dir = TempDir::new("pumpkindb").unwrap();
        let path = dir.path().to_str().unwrap();
        fs::create_dir_all(path).expect("can't create directory");
        let env = lmdb::create_environment(String::from(path), None, None).unwrap();
        let store = lmdb::LmdbKeyValueStore::new(&env).expect("can't create store");

        let mut readers = vec![];

        // While we are exhausting max_readers,
        // we should be able to get a read transaction
        for _ in 0..store.max_readers() {
            let r = store.read_transaction();
            assert!(r.is_ok());
            readers.push(r);
        }

        // but when the limit is exhausted,
        // no read transaction should be available
        assert!(store.read_transaction().is_err());

        readers.pop();

        // after we've popped one transaction,
        // we should be able to get it
        let r = store.read_transaction();
        assert!(r.is_ok());
        assert!(store.read_transaction().is_err());
    }


    #[test]
    pub fn write_limit() {
        let dir = TempDir::new("pumpkindb").unwrap();
        let path = dir.path().to_str().unwrap();
        fs::create_dir_all(path).expect("can't create directory");
        let env = lmdb::create_environment(String::from(path), None, None).unwrap();
        let store = lmdb::LmdbKeyValueStore::new(&env).expect("can't create store");

        let mut writers = vec![];

        // While we are exhausting max_writers,
        // we should be able to get a write transaction
        for _ in 0..store.max_writers() {
            let r = store.write_transaction();
            assert!(r.is_ok());
            writers.push(r);
        }

        // but when the limit is exhausted,
        // no read transaction should be available
        assert!(store.write_transaction().is_err());

        writers.pop();

        // after we've popped one transaction,
        // we should be able to get it
        let r = store.write_transaction();
        assert!(r.is_ok());
        assert!(store.write_transaction().is_err());
    }



}
