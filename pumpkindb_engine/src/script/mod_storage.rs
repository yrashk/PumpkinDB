// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
//! # Storage
//!
//! This module handles all instructions and state related to handling storage
//! capabilities
//!

use lmdb;
use lmdb::traits::{LmdbResultExt, AsLmdbBytes, FromLmdbBytes};
use storage;
use std::mem;
use std::error::Error as StdError;
use std::collections::HashMap;
use super::{Env, EnvId, Dispatcher, PassResult, Error, STACK_TRUE, STACK_FALSE, offset_by_size,
            ERROR_EMPTY_STACK, ERROR_INVALID_VALUE, ERROR_DUPLICATE_KEY, ERROR_NO_TX,
            ERROR_UNKNOWN_KEY, ERROR_DATABASE, ERROR_NO_VALUE, TryInstruction};
use snowflake::ProcessUniqueId;
use std::collections::BTreeMap;
use storage::WriteTransactionContainer;
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use serde_cbor;

pub type CursorId = ProcessUniqueId;

instruction!(TXID, b"\x84TXID");
instruction!(WRITE, b"\x85WRITE");
instruction!(WRITE_END, b"\x80\x85WRITE"); // internal instruction

instruction!(READ, b"\x84READ");
instruction!(READ_END, b"\x80\x84READ"); // internal instruction

instruction!(ASSOC, b"\x85ASSOC");
instruction!(ASSOCQ, b"\x86ASSOC?");
instruction!(RETR, b"\x84RETR");

instruction!(CURSOR, b"\x86CURSOR");
instruction!(CURSOR_FIRST, b"\x8CCURSOR/FIRST");
instruction!(CURSOR_LAST, b"\x8BCURSOR/LAST");
instruction!(CURSOR_NEXT, b"\x8BCURSOR/NEXT");
instruction!(CURSOR_PREV, b"\x8BCURSOR/PREV");
instruction!(CURSOR_SEEK, b"\x8BCURSOR/SEEK");
instruction!(CURSOR_POSITIONEDQ, b"\x92CURSOR/POSITIONED?");
instruction!(CURSOR_KEY, b"\x8ACURSOR/KEY");
instruction!(CURSOR_VAL, b"\x8ACURSOR/VAL");

instruction!(COMMIT, b"\x86COMMIT");

instruction!(MAXKEYSIZE, b"\x92$SYSTEM/MAXKEYSIZE");

#[derive(PartialEq, Debug)]
enum TxType {
    Read,
    Write,
}

enum Accessor<'a> {
    Const(lmdb::ConstAccessor<'a>),
    Write(lmdb::WriteAccessor<'a>),
}

//impl<'a> Accessor<'a> {
//    fn get<K: AsLmdbBytes + ?Sized, V: FromLmdbBytes + ?Sized>(&self, db: &lmdb::Database, key: &K)
//        -> Result<Option<&V>, lmdb::Error> {
//        match self {
//            &Accessor::Write(ref access) => {
//                access.get::<K, V>(db, key)
//            },
//            &Accessor::Const(ref access) => {
//                access.get::<K, V>(db, key)
//            }
//        }.to_opt()
//    }
//}


impl<'a> Deref for Accessor<'a> {
    type Target = lmdb::WriteAccessor<'a>;

    fn deref(&self) -> &Self::Target {
        match self {
            &Accessor::Const(_) => panic!("can't deref const accessor to a write one"),
            &Accessor::Write(ref acc) => acc,
        }
    }
}

impl<'a> DerefMut for Accessor<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            &mut Accessor::Const(_) => panic!("can't deref const accessor to a write one"),
            &mut Accessor::Write(ref mut acc) => acc,
        }
    }
}

#[derive(Debug)]
pub struct Cursors<'a>(BTreeMap<Vec<u8>, lmdb::Cursor<'a, 'a>>);

impl<'a> Cursors<'a> {
    pub fn new() -> Self {
        Cursors(BTreeMap::new())
    }
}

impl<'a> Deref for Cursors<'a> {
    type Target = BTreeMap<Vec<u8>, lmdb::Cursor<'a, 'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for Cursors<'a> {

    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub type TxnId<'a> = &'a [u8];

#[derive(Debug)]
pub enum Txn<'a> {
    Read(lmdb::ReadTransaction<'a>, TxnId<'a>, Cursors<'a>),
    Write(WriteTransactionContainer<'a>, TxnId<'a>, Cursors<'a>),
}

impl<'a> Txn<'a> {
    fn access(&self) -> Accessor {
        match self {
            &Txn::Read(ref txn, _, _) => Accessor::Const(txn.access()),
            &Txn::Write(ref txn, _, _) => Accessor::Write(txn.access()),
        }
    }
    fn cursor(&self, db: &'a lmdb::Database) -> Result<lmdb::Cursor, lmdb::Error> {
        match self {
            &Txn::Read(ref txn, _, _) => txn.cursor(db),
            &Txn::Write(ref txn, _, _) => txn.cursor(db),
        }
    }
    fn cursors(&mut self) -> &mut Cursors<'a> {
        match self {
            &mut Txn::Read(_, _, ref mut cursors) => cursors,
            &mut Txn::Write(_, _, ref mut cursors) => cursors,
        }
    }
    fn add_cursor(&mut self, cursor: lmdb::Cursor<'a, 'a>)  -> Vec<u8> {
        let id = CursorId::new();
        let bytes = serde_cbor::to_vec(&id).unwrap();
        match self {
            &mut Txn::Read(_, _, ref mut cursors) => cursors.insert(bytes.clone(), cursor),
            &mut Txn::Write(_, _, ref mut cursors) => cursors.insert(bytes.clone(), cursor),
        };
        bytes
    }

    fn tx_type(&self) -> TxType {
        match self {
            &Txn::Read(_, _, _) => TxType::Read,
            &Txn::Write(_, _, _) => TxType::Write,
        }
    }
    fn id(&self) -> TxnId<'a> {
        match self {
            &Txn::Read(_, txid, _) => txid,
            &Txn::Write(_, txid, _) => txid,
        }
    }

    fn commit(mut self) -> Result<(), lmdb::Error> {
        match self {
            Txn::Read(_, _, _) => panic!("can't commit a read transaction"),
            Txn::Write(txn, _, _) => txn.commit(),
        }
    }
}

use std::sync::Arc;
use super::super::timestamp;
use super::super::nvmem::NonVolatileMemory;

use std::marker::PhantomData;

pub struct Handler<'a, T, N>
    where T : AsRef<storage::Storage<'a>> + 'a,
          N : NonVolatileMemory {
    db: T,
    maxkeysize: Vec<u8>,
    timestamp: Arc<timestamp::Timestamp<N>>,
    phantom: PhantomData<&'a ()>,
}

macro_rules! read_or_write_transaction {
    ($env: expr) => {{
        let txns = &mut $env.txns;
        if txns.is_empty() {
           return Err(error_no_transaction!());
        } else {
           &mut txns[txns.len() - 1]
        }
    }};
}

macro_rules! cursor_op {
    ($env: expr, $op: ident, ($($arg: expr),*)) => {{
        let txn = read_or_write_transaction!($env);
        let c = stack_pop!($env);

        let key = Vec::from(c);
         match txn.cursors().get_mut(&key) {
            Some(ref mut cursor) => {
                let result = match txn.access() {
                    Accessor::Const(acc) => cursor.$op::<[u8], [u8]>(&acc, $($arg)*).is_ok(),
                    Accessor::Write(acc) => cursor.$op::<[u8], [u8]>(&acc, $($arg)*).is_ok()
                };
                if result {
                    $env.push(STACK_TRUE);
                } else {
                    $env.push(STACK_FALSE);
                }
            },
            None => return Err(error_invalid_value!(c))
        };

    }};
}

macro_rules! cursor_map_op {
    ($env: expr, $op: ident, ($($arg: expr),*), $map: expr, $orelse: expr) => {{
        let txn = read_or_write_transaction!($env);
        let c = stack_pop!($env);

        let key = Vec::from(c);
        match txn.cursors().get_mut(&key) {
            Some(ref mut cursor) => {
                match txn.access() {
                    Accessor::Const(acc) => cursor.$op::<[u8], [u8]>(&acc, $($arg)*).map_err($orelse).and_then($map),
                    Accessor::Write(acc) => cursor.$op::<[u8], [u8]>(&acc, $($arg)*).map_err($orelse).and_then($map)
                }
            },
            None => return Err(error_invalid_value!(c))
        }
    }};
}

builtins!("mod_storage.builtins");


use std::ops::{Deref, DerefMut};

pub struct Transactions<'a>(Vec<Txn<'a>>);

impl<'a> Transactions<'a> {
    pub fn new() -> Self {
        Transactions(vec![])
    }
}

impl<'a> Deref for Transactions<'a> {
    type Target = Vec<Txn<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for Transactions<'a> {

    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T, N> Dispatcher<'a> for Handler<'a, T, N>
    where T : AsRef<storage::Storage<'a>> + 'a,
          N : NonVolatileMemory {

    fn handle(&self, env: &mut Env<'a>, instruction: &'a [u8], pid: EnvId) -> PassResult<'a> {
        self.handle_builtins(env, instruction, pid)
        .if_unhandled_try(|| self.handle_write(env, instruction, pid))
        .if_unhandled_try(|| self.handle_read(env, instruction, pid))
        .if_unhandled_try(|| self.handle_txid(env, instruction, pid))
        .if_unhandled_try(|| self.handle_assoc(env, instruction, pid))
        .if_unhandled_try(|| self.handle_assocq(env, instruction, pid))
        .if_unhandled_try(|| self.handle_retr(env, instruction, pid))
        .if_unhandled_try(|| self.handle_commit(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_first(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_next(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_prev(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_last(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_seek(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_positionedq(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_key(env, instruction, pid))
        .if_unhandled_try(|| self.handle_cursor_val(env, instruction, pid))
        .if_unhandled_try(|| self.handle_maxkeysize(env, instruction, pid))
        .if_unhandled_try(|| Err(Error::UnknownInstruction))
    }
}

impl<'a, T, N> Handler<'a, T, N>
    where T : AsRef<storage::Storage<'a>> + 'a,
          N : NonVolatileMemory {
    pub fn new(db: T, timestamp: Arc<timestamp::Timestamp<N>>) -> Self {
        let maxkeysize = BigUint::from_u32(db.as_ref().env.maxkeysize()).unwrap().to_bytes_be();
        Handler {
            db: db,
            maxkeysize: maxkeysize,
            timestamp,
            phantom: PhantomData,
        }
    }

    fn new_txid(&self, env: &mut Env<'a>) -> Result<TxnId<'a>, super::Error> {
        let now = self.timestamp.hlc();
        let slice = env.alloc(16);
        if slice.is_err() {
            return Err(slice.unwrap_err());
        }
        let mut slice = slice.unwrap();
        let _ = now.write_bytes(&mut slice[0..]).unwrap();
        Ok(slice)
    }

    handle_builtins!();

    #[inline]
    pub fn handle_write(&self,
                        env: &mut Env<'a>,
                        instruction: &'a [u8],
                        pid: EnvId)
                        -> PassResult<'a> {
        match instruction {
            WRITE => {
                let v = stack_pop!(env);
                if !env.txns.is_empty() {
                    return Err(error_program!(
                               "Nested WRITEs are not currently allowed".as_bytes(),
                               "".as_bytes(),
                               ERROR_DATABASE));
                }
                match self.db.as_ref().write() {
                    None => Err(Error::Reschedule),
                    Some(result) =>
                        match result {
                            Err(e) => Err(error_database!(e)),
                            Ok(txn) => {
                                let txid = self.new_txid(env).unwrap();
                                let _ = env.txns.push(Txn::Write(txn, txid, Cursors::new()));
                                env.program.push(WRITE_END);
                                env.program.push(v);
                                Ok(())
                            }
                        }
                }
            }
            WRITE_END => {
                let _ = env.txns.pop();
                Ok(())
            }
            _ => Err(Error::UnknownInstruction),
        }
    }

    #[inline]
    pub fn handle_read(&self,
                       env: &mut Env<'a>,
                       instruction: &'a [u8],
                       pid: EnvId)
                       -> PassResult<'a> {
        match instruction {
            READ => {
                let v = stack_pop!(env);
                match self.db.as_ref().read() {
                    None => Err(Error::Reschedule),
                    Some(result) =>
                        match result {
                            Err(e) => Err(error_database!(e)),
                            Ok(txn) => {
                                let txid = self.new_txid(env).unwrap();
                                let _ = env.txns.push(Txn::Read(txn, txid, Cursors::new()));
                                env.program.push(READ_END);
                                env.program.push(v);
                                Ok(())
                            }
                    }
                }
            }
            READ_END => {
                let _ = env.txns.pop();
                Ok(())
            }
            _ => Err(Error::UnknownInstruction),
        }
    }


    #[inline]
    pub fn handle_txid(&self,
                       env: &mut Env<'a>,
                       instruction: &'a [u8],
                       pid: EnvId)
                       -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, TXID);
        let txn = read_or_write_transaction!(env);
        env.push(txn.id());
        Ok(())
    }

    #[inline]
    pub fn handle_assoc(&self,
						env: &mut Env<'a>,
						instruction: &'a [u8],
						pid: EnvId)
						-> PassResult<'a> {
        return_unless_instructions_equal!(instruction, ASSOC);
        let txn = read_or_write_transaction!(env);
        if txn.tx_type() == TxType::Read {
            return Err(error_no_transaction!())
        }
        let value = stack_pop!(env);
        let key = stack_pop!(env);

        let mut access = txn.access();

        match access.put(&self.db.as_ref().db, key, value, lmdb::put::NOOVERWRITE) {
            Ok(_) => Ok(()),
            Err(lmdb::Error::Code(code)) if lmdb::error::KEYEXIST == code => Err(error_duplicate_key!(key)),
            Err(err) => Err(error_database!(err)),
        }
    }

    #[inline]
    pub fn handle_commit(&self,
						 env: &mut Env<'a>,
						 instruction: &'a [u8],
						 pid: EnvId)
						 -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, COMMIT);
        // check if there's a write transaction
        let txn = read_or_write_transaction!(env);
        if txn.tx_type() == TxType::Read {
            return Err(error_no_transaction!())
        }
        // pop it out and commit
        let wtxn = env.txns.pop().unwrap();
        match wtxn.commit() {
            Ok(_) => Ok(()),
            Err(reason) => Err(error_database!(reason))
        }
    }


    #[inline]
    pub fn handle_retr(&self,
                       env: &mut Env<'a>,
                       instruction: &'a [u8],
                       pid: EnvId)
                       -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, RETR);
        let txn = read_or_write_transaction!(env);
        let key = stack_pop!(env);

        let mut access = txn.access();

        match access.get::<[u8], [u8]>(&self.db.as_ref().db, key).to_opt() {
            Ok(Some(val)) => {
                let slice = alloc_and_write!(val, env);
                env.push(slice);
                Ok(())
            },
            Ok(None) => Err(error_unknown_key!(key)),
            Err(err) => Err(error_database!(err)),
        }
    }

    #[inline]
    pub fn handle_assocq(&self,
                         env: &mut Env<'a>,
                         instruction: &'a [u8],
                         pid: EnvId)
                         -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, ASSOCQ);
        let txn = read_or_write_transaction!(env);
        let key = stack_pop!(env);

        let mut access = txn.access();

        match access.get::<[u8], [u8]>(&self.db.as_ref().db, key).to_opt() {
            Ok(Some(_)) => {
                env.push(STACK_TRUE);
                Ok(())
            },
            Ok(None) => {
                env.push(STACK_FALSE);
                Ok(())
            }
            Err(err) => Err(error_database!(err)),
        }
    }

    fn cast_away(cursor: lmdb::Cursor) -> lmdb::Cursor<'a, 'a> {
        unsafe { ::std::mem::transmute(cursor) }
    }

    #[inline]
    pub fn handle_cursor(&self,
						 env: &mut Env<'a>,
						 instruction: &'a [u8],
						 pid: EnvId)
						 -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR);
        let db = self.db.as_ref();
        let txn = read_or_write_transaction!(env);
        match txn.cursor(&db.db) {
            Ok(cursor) => {
                let bytes = txn.add_cursor(Handler::<T, N>::cast_away(cursor));
                let slice = alloc_and_write!(bytes.as_slice(), env);
                env.push(slice);
                Ok(())
            },
            Err(err) => Err(error_database!(err))
        }
    }

    #[inline]
    pub fn handle_cursor_first(&self,
                               env: &mut Env<'a>,
                               instruction: &'a [u8],
                               pid: EnvId)
                               -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_FIRST);
        cursor_op!(env, first, ());
        Ok(())
    }


    #[inline]
    pub fn handle_cursor_next(&self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_NEXT);
        cursor_op!(env, next, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_prev(&self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_PREV);
        cursor_op!(env, prev, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_last(&self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_LAST);
        cursor_op!(env, last, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_seek(&self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_SEEK);
        let key = stack_pop!(env);
        cursor_op!(env, seek_range_k, (key));
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_positionedq(&self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_POSITIONEDQ);
        let result = match cursor_map_op!(env, get_current, (), |_| Ok(true), |_| false) {
            Ok(true) => STACK_TRUE,
            Err(false) => STACK_FALSE,
            Err(true) | Ok(false) => unreachable!(),
        };
        env.push(result);
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_key(&self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             pid: EnvId)
                             -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_KEY);
        cursor_map_op!(env, get_current, (),
           |(key, _) | {
              let slice = alloc_slice!(key.len(), env);
              slice.copy_from_slice(key);
              env.push(slice);
              Ok(())
        }, |_| error_no_value!())
    }

    #[inline]
    pub fn handle_cursor_val(&self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             pid: EnvId)
                             -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, CURSOR_VAL);
        cursor_map_op!(env, get_current, (),
           |(_, val) | {
              let slice = alloc_slice!(val.len(), env);
              slice.copy_from_slice(val);
              env.push(slice);
              Ok(())
        }, |_| error_no_value!())
    }

    #[inline]
    pub fn handle_maxkeysize(&self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             _: EnvId)
                             -> PassResult<'a> {
        return_unless_instructions_equal!(instruction, MAXKEYSIZE);
        let slice = alloc_and_write!(self.maxkeysize.as_slice(), env);
        env.push(slice);
        Ok(())
    }
}

#[cfg(test)]
#[allow(unused_variables, unused_must_use, unused_mut, unused_imports)]
mod tests {
    use pumpkinscript::{parse, offset_by_size};
    use messaging;
    use nvmem::{MmapedFile, MmapedRegion, NonVolatileMemory};
    use script::{Env, Scheduler, Error, RequestMessage, ResponseMessage, EnvId, dispatcher};

    use byteorder::WriteBytesExt;
    use std::sync::mpsc;
    use std::sync::Arc;
    use std::fs;
    use tempdir::TempDir;
    use lmdb;
    use crossbeam;
    use script::binparser;
    use storage;
    use timestamp;
    use rand::Rng;

    const _EMPTY: &'static [u8] = b"";

    #[test]
    fn errors_during_txn() {
        eval!("[[\"Hey\" ASSOC COMMIT] WRITE] TRY [\"Hey\" ASSOC?] READ",
              env,
              result,
              {
                  assert_eq!(Vec::from(env.pop().unwrap()), parsed_data!("0x00"));
              });
        eval!("[[\"Hey\" ASSOC COMMIT] WRITE] TRY DROP [\"Hey\" \"there\" ASSOC COMMIT] WRITE \
               [\"Hey\" ASSOC?] READ",
              env,
              result,
              {
                  assert_eq!(Vec::from(env.pop().unwrap()), parsed_data!("0x01"));
              });

    }

    #[test]
    fn txn_order() {
        eval!("\"hello\" HLC CONCAT DUP [\"world\" ASSOC [ASSOC?] READ] WRITE 0x00 EQUAL?", env, result, {
            assert_eq!(Vec::from(env.pop().unwrap()), parsed_data!("0x01"));
            assert_eq!(env.pop(), None);
        });
    }

    use test::Bencher;

    #[bench]
    fn write_1000_kv_pairs_in_isolated_txns(b: &mut Bencher) {
        bench_eval!("[HLC \"Hello\"] 1000 TIMES [[ASSOC COMMIT] WRITE] 1000 TIMES",
                    b);
    }

    #[bench]
    fn write_1000_kv_pairs_in_isolated_txns_baseline(b: &mut Bencher) {
        let dir = TempDir::new("pumpkindb").unwrap();
        let path = dir.path().to_str().unwrap();
        fs::create_dir_all(path).expect("can't create directory");
        let env = unsafe {
            let mut builder = lmdb::EnvBuilder::new().expect("can't create env builder");
            builder.set_mapsize(1024 * 1024 * 1024).expect("can't set mapsize");
            builder.open(path, lmdb::open::NOTLS, 0o600).expect("can't open env")
        };
        let mut nvmem = MmapedFile::new_anonymous(20).unwrap();
        let region = nvmem.claim(20).unwrap();
        let timestamp = Arc::new(timestamp::Timestamp::new(region));
        let db = storage::Storage::new(&env);
        b.iter(move || {
            let mut timestamps = Vec::new();
            for i in 0..1000 {
                timestamps.push(timestamp.hlc());
            }
            for ts in timestamps {
                let txn = lmdb::WriteTransaction::new(db.env).unwrap();
                {
                    let mut access = txn.access();
                    let mut key: Vec<u8> = Vec::new();

                    ts.write_bytes(&mut key);

                    let _ = access.put(&db.db,
                             key.as_slice(),
                             "Hello".as_bytes(),
                             lmdb::put::NOOVERWRITE)
                        .unwrap();
                }
                let _ = txn.commit().unwrap();
            }
        });
    }

}
