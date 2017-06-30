// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use lmdb::*;
use std::ptr;
use libc::c_int;
use kv;
use kv::KeyValueStore;

use std::io;
use std::fs;
#[cfg(not(target_os = "windows"))]
use std::path;
use std::ffi::CString;
#[cfg(not(target_os = "windows"))]
use libc::statvfs;
#[cfg(not(target_os = "windows"))]
use alloc::heap;
#[cfg(not(target_os = "windows"))]
use core::mem::size_of;

use super::{LmdbReadTransaction, LmdbWriteTransaction, LmdbError};

pub const MDB_NOTLS: ::libc::c_uint = 0x200000;

use std::marker::PhantomData;

pub struct LmdbKeyValueStore<'a> {
    dbi: MDB_dbi,
    env: *mut MDB_env,
    live_writer: Arc<AtomicBool>,
    max_readers: usize,
    phantom: PhantomData<&'a ()>,
}

impl<'a> LmdbKeyValueStore<'a> {
    pub fn new<S : AsRef<str>>(path: S,
                               map_size: Option<i64>,
                               max_readers: Option<u32>) ->
                               Result<Self, kv::Error> {
        let mut env = ptr::null_mut();
        unsafe { mdb_try!(mdb_env_create(&mut env)); }
        // Configure map size
        if !cfg!(target_os = "windows") && map_size.is_none() {
            #[cfg(not(target_os = "windows"))]
                {
                    let path = path::PathBuf::from(path.as_ref());
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
                        unsafe { mdb_try!(mdb_env_set_mapsize(env, size), mdb_env_close(env)); }
                    }
                    heap::deallocate(statp as *mut u8, size_of::<statvfs>(), size_of::<usize>());
                }
        } else {
            match map_size {
                Some(mapsize) => {
                    unsafe { mdb_try!(mdb_env_set_mapsize(env, 1024 * mapsize), mdb_env_close(env)); }
                }
                None => {
                    warn!("No default storage.mapsize set, setting it to 1Gb");
                    unsafe { mdb_try!(mdb_env_set_mapsize(env, 1024 * 1024 * 1024), mdb_env_close(env)); }
                }
            }
        }
        let mut retrieved_max_readers = 0;
        unsafe {
            mdb_try!(mdb_env_get_maxreaders(env, &mut retrieved_max_readers), mdb_env_close(env));
        }
        // Open the environment
        unsafe {
            mdb_try!(mdb_env_open(env, CString::new(path.as_ref()), MDB_NOTLS, 0o600), mdb_env_close(env));
        }

        // Create a database
        let mut txn = ptr::null_mut();
        unsafe { mdb_try!(mdb_txn_begin(env, ptr::null_mut(), 0, &mut txn), mdb_env_close(env)); }
        let mut dbi = 0;
        unsafe { mdb_try!(mdb_dbi_open(env, ptr::null(), 0, &mut dbi), {
                 mdb_txn_abort(txn);
                 mdb_env_close(env);
                 });
        }
        unsafe { mdb_try!(mdb_txn_commit(txn), mdb_env_close(env));}

        // Prepare the structure
        Ok(LmdbKeyValueStore {
            dbi,
            env,
            live_writer: Arc::new(AtomicBool::new(false)),
            max_readers: retrieved_max_readers,
            phantom: PhantomData,
        })
    }

    pub(super) fn env(&self) -> *mut MDB_env {
        self.env
    }

    pub(super) fn dbi(&self) -> MDB_dbi {
        self.dbi
    }

}

impl<'a> Drop for LmdbKeyValueStore<'a> {
    fn drop(&mut self) {
        unsafe {
            mdb_dbi_close(self.dbi);
            mdb_env_close(self.env);
        }
    }
}

impl<'a> KeyValueStore for LmdbKeyValueStore<'a> {
    type WriteTransaction = LmdbWriteTransaction<'a>;
    type ReadTransaction = LmdbReadTransaction<'a>;
    type Error = LmdbError;

    fn read_transaction(&self) -> Result<Self::ReadTransaction, kv::TransactionOriginationError<Self::Error>> {
        LmdbReadTransaction::new(self)
            .map_err(|v|
                match v {
                    // MDB_READERS_FULL
                    kv::TransactionOriginationError::DatabaseError(LmdbError(-30790)) =>
                        kv::TransactionOriginationError::TransactionLimitReached(self.maxreaders),
                    v => v,
                })
    }

    fn write_transaction(&self) -> Result<Self::WriteTransaction, kv::TransactionOriginationError<Self::Error>> {
        match self.live_writer.compare_and_swap(false, true, Ordering::SeqCst) {
            false => LmdbWriteTransaction::new(self, self.live_writer.clone()),
            true => Err(kv::TransactionOriginationError::TransactionLimitReached(1)),
        }
    }
    fn max_readers(&self) -> usize {
        self.max_readers
    }

    fn max_writers(&self) -> usize {
        1
    }
    fn max_keysize(&self) -> u32 {
        511
    }
}
