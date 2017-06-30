// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::*;

use libc::c_int;

#[derive(Debug)]
pub struct LmdbError(c_int);

impl ::std::fmt::Display for LmdbError {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        f.write_str(&format!("LMDB Error {}", self.0))
    }
}
impl ::std::error::Error for LmdbError {
    fn description(&self) -> &str {
        &format!("LMDB Error {}", self.0)
    }
}

impl Into<Error> for LmdbError {
    fn into(self) -> Error {
        match self.0 {
            lmdb::Error::Code(cint) => Error::Code(cint as i64),
            _ => Error::UnknownError,
        }
    }
}

impl Into<TransactionOriginationError<LmdbResult>> for LmdbResult {
    fn into(self) -> TransactionOriginationError<LmdbResult> {
        TransactionOriginationError::DatabaseError(self)
    }
}

pub struct LmdbResult(c_int);

use std::ops::Try;
impl Try for LmdbResult {
    type Ok = ();
    type Error = LmdbError;

    fn into_result(self) -> Result<Self::Ok, Self::Error> {
        if self.0 == 0 {
            Ok(())
        } else {
            Err(LmdbError(self.0))
        }
    }

    fn from_error(v: Self::Error) -> Self {
        LmdbResult(v.0)
    }

    fn from_ok(v: Self::Ok) -> Self {
        LmdbResult(0)
    }
}

macro_rules! mdb_try {
    ($expr: expr) => {{
      mdb_try!($expr, ())
    }};
    ($expr: expr, $cleanup: expr) => {{
       match $expr {
           MDB_SUCCESS => (),
           err => {
               let _ = $cleanup;
               return Err($crate::kv::lmdb::LmdbError(err))
           }
       }
    }};
}

mod store;
pub use self::store::LmdbKeyValueStore;
mod txn;
pub use self::txn::{LmdbReadTransaction, LmdbWriteTransaction};
pub(in kv::lmdb) use self::txn::Txn;
mod cursor;
pub use self::cursor::LmdbCursor;

//
//pub struct LmdbReadTransaction<'a>(lmdb::LmdbReadTransaction<'a>, Arc<lmdb::Database<'a>>);
//
//impl<'a> LmdbReadTransaction<'a> {
//    pub(crate) fn new(txn: lmdb::LmdbReadTransaction<'a>, db: Arc<lmdb::Database<'a>>) -> Self {
//        LmdbReadTransaction(txn, db)
//    }
//}
//
//pub struct ConstAccessorWrapper<'a>(lmdb::ConstAccessor<'a>);
//
//impl<'a> Deref for ConstAccessorWrapper<'a> {
//    type Target = lmdb::ConstAccessor<'a>;
//    fn deref(&self) -> &Self::Target {
//        &self.0
//    }
//}
//
//impl<'a> Access<'a> for LmdbReadTransaction<'a> {
//    type T = ConstAccessorWrapper<'a>;
//    fn access(&'a self) -> Self::T {
//        ConstAccessorWrapper(self.0.access())
//    }
//}
//
//impl<'t> LmdbReadTransaction for LmdbReadTransaction<'t> {
////    type Cursor = LmdbCursor<'t, 't, LmdbReadTransaction<'t>>;
////    fn cursor<'c>(&'c self) -> Result<LmdbCursor<'c, 'c, LmdbReadTransaction<'c>>, Error> {
//    fn cursor<'c, C : 'c>(&'c self) -> Result<C, Error> {
//        match self.0.cursor(&*self.1).map_err(|v| LmdbError(v).into()) {
//            Err(err) => Err(err),
//            Ok(v) => Ok(LmdbCursor::new(self, v))
//        }
//    }
//
//    fn get<'a, A : Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
//        let access = self.0.access();
//        match access.get::<[u8], [u8]>(&self.1, key).to_opt().map_err(|v| LmdbError(v).into()) {
//            Ok(Some(v)) => {
//                let mut slice = allocator.alloc(v.len());
//                slice.copy_from_slice(v);
//                Ok(slice)
//            },
//            Ok(None) => Err(Error::UnknownKey),
//            Err(e) => Err(e),
//        }
//    }
//}
//
//
//pub struct LmdbWriteTransaction<'a>(lmdb::WriteTransaction<'a>, Arc<lmdb::Database<'a>>, Arc<AtomicBool>);
//
//impl<'a> LmdbWriteTransaction<'a> {
//    pub(crate) fn new(txn: lmdb::WriteTransaction<'a>, db: Arc<lmdb::Database<'a>>,
//                      live_writer: Arc<AtomicBool>) -> Self {
//        LmdbWriteTransaction(txn, db, live_writer)
//    }
//}
//
//impl<'a> Drop for LmdbWriteTransaction<'a> {
//    fn drop(&mut self) {
//        self.2.compare_and_swap(true, false, Ordering::SeqCst);
//    }
//}
//
//use lmdb::traits::LmdbResultExt;
//impl<'t> LmdbReadTransaction for LmdbWriteTransaction<'t> {
////    type Cursor = LmdbCursor<'t, 't, LmdbWriteTransaction<'t>>;
//
//    fn cursor<'c, C : 'c>(&'c self) -> Result<C, Error> {
////    fn cursor<'c>(&'c self) -> Result<LmdbCursor<'c, 'c, LmdbReadTransaction<'c>>, Error> {
////    fn cursor(&self) -> Result<Self::Cursor, Error> {
//        match self.0.cursor(self.1).map_err(|v| LmdbError(v).into()) {
//            Err(err) => Err(err),
//            Ok(v) => Ok(LmdbCursor::new(self, v))
//        }
//    }
//
//    fn get<'a, A : Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
//        let access = self.0.access();
//        match access.get::<[u8], [u8]>(&self.1, key).to_opt().map_err(|v| LmdbError(v).into()) {
//            Ok(Some(v)) => {
//                let mut slice = allocator.alloc(v.len());
//                slice.copy_from_slice(v);
//                Ok(slice)
//            },
//            Ok(None) => Err(Error::UnknownKey),
//            Err(e) => Err(e),
//        }
//    }
//}
//
//impl<'a> Access<'a> for LmdbWriteTransaction<'a> {
//    type T = lmdb::WriteAccessor<'a>;
//    fn access(&'a self) -> Self::T {
//        self.0.access()
//    }
//}
//impl<'t> WriteTransaction for LmdbWriteTransaction<'t> {
//    fn commit(self) -> Result<(), Error> {
//        self.0.commit().map_err(|v| LmdbError(v).into())
//    }
//    fn put<'a>(&self, key: &'a [u8], value: &'a [u8]) -> Result<(), Error> {
//        let mut access = self.0.access();
//        match access.put(&self.1, key, value, lmdb::put::NOOVERWRITE) {
//            Ok(_) => Ok(()),
//            Err(lmdb::Error::Code(code)) if lmdb::error::KEYEXIST == code => Err(Error::DuplicateKey),
//            Err(err) => Err(LmdbError(err).into()),
//        }
//    }
//}

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
//        let env = lmdb::create_environment(String::from(path), None, None).unwrap();
        let store = lmdb::LmdbKeyValueStore::new(path, None, None).expect("can't create store");

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

//
//    #[test]
//    pub fn write_limit() {
//        let dir = TempDir::new("pumpkindb").unwrap();
//        let path = dir.path().to_str().unwrap();
//        fs::create_dir_all(path).expect("can't create directory");
//        let env = lmdb::create_environment(String::from(path), None, None).unwrap();
//        let store = lmdb::LmdbKeyValueStore::new(&env).expect("can't create store");
//
//        let mut writers = vec![];
//
//        // While we are exhausting max_writers,
//        // we should be able to get a write transaction
//        for _ in 0..store.max_writers() {
//            let r = store.write_transaction();
//            assert!(r.is_ok());
//            writers.push(r);
//        }
//
//        // but when the limit is exhausted,
//        // no read transaction should be available
//        assert!(store.write_transaction().is_err());
//
//        writers.pop();
//
//        // after we've popped one transaction,
//        // we should be able to get it
//        let r = store.write_transaction();
//        assert!(r.is_ok());
//        assert!(store.write_transaction().is_err());
//    }



}
