// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::marker::PhantomData;
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use lmdb::*;

use allocator::Allocator;
use super::{LmdbKeyValueStore, LmdbCursor, LmdbError, LmdbResult};
use kv;
use kv::Error;

pub struct LmdbReadTransaction<'store> {
    txn: *mut MDB_txn,
    phantom: PhantomData<&'store ()>,
}

pub(super) trait Txn {
    fn txn(&self) -> *mut MDB_txn;
}

impl<'store> Txn for LmdbReadTransaction<'store> {
    fn txn(&self) -> *mut MDB_txn {
        self.txn
    }
}

impl<'store> LmdbReadTransaction<'store> {
    pub fn new(store: &'store LmdbKeyValueStore) -> Result<Self, kv::TransactionOriginationError<LmdbError>> {
        let mut txn = ptr::null_mut();
        unsafe {
            LmdbResult(mdb_txn_begin(store.env(), ptr::null_mut(), MDB_RDONLY, &mut txn))?;
        }
        Ok(LmdbReadTransaction { txn, phantom: PhantomData })
    }
}

impl<'store> kv::ReadTransaction for LmdbReadTransaction<'store> {

    fn cursor<'c, 'a, A : Allocator<'a>>(&'c self, allocator: &mut A) -> Result<kv::Cursor<A> + 'c, Error> {
//    fn cursor<'c>(&'c self) -> Result<kv::Cursor+ 'c, Error> {
        LmdbCursor::new(self, allocator)
    }

    fn get<'a, A: Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
        unimplemented!()
    }
}

pub struct LmdbWriteTransaction<'store> {
    txn: *mut MDB_txn,
    read_txn: LmdbReadTransaction<'store>,
    live_writer: Arc<AtomicBool>,
    committed: bool,
}

impl<'store> Txn for LmdbWriteTransaction<'store> {
    fn txn(&self) -> *mut MDB_txn {
        self.txn
    }
}


impl<'store> LmdbWriteTransaction<'store> {
    pub fn new(store: &'store LmdbKeyValueStore, live_writer: Arc<AtomicBool>) -> Result<Self, kv::TransactionOriginationError<LmdbError>> {
        let mut txn = ptr::null_mut();
        unsafe {
            LmdbResult(mdb_txn_begin(store.env(), ptr::null_mut(), 0, &mut txn))?;
        }
        Ok(LmdbWriteTransaction{
            txn,
            read_txn: LmdbReadTransaction { txn, phantom: PhantomData },
            live_writer,
            committed: false,
        })
    }
}

impl<'store> Drop for LmdbWriteTransaction<'store> {
    fn drop(&mut self) {
        self.live_writer.compare_and_swap(true, false, Ordering::SeqCst);
        if !self.committed {
            unsafe { mdb_txn_abort(self.txn); }
        }
    }
}

impl<'store> kv::ReadTransaction for LmdbWriteTransaction<'store> {
    fn cursor<'c, 'a, A : Allocator<'a>>(&'c self, allocator: &mut A) -> Result<kv::Cursor<A> + 'c, Error> {
        self.read_txn.cursor(allocator)
    }

    fn get<'a, A: Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error> {
        self.read_txn.get(key, allocator)
    }
}

impl<'store> kv::WriteTransaction for LmdbWriteTransaction<'store> {
    fn put<'a>(&self, key: &'a [u8], value: &'a [u8]) -> Result<(), Error> {
        unimplemented!()
    }

    fn commit(self) -> Result<(), Error> {
        unsafe { LmdbResult(mdb_txn_commit(self.txn))?; }
        self.committed = true;
        Ok(())
    }
}