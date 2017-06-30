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

use allocator::Allocator;
use kv;
use kv::{KeyValueStore, WriteTransaction, ReadTransaction};
use std::mem;
use std::error::Error as StdError;
use std::collections::HashMap;
use super::{Env, EnvId, Dispatcher, PassResult, Error, STACK_TRUE, STACK_FALSE, offset_by_size,
            ERROR_EMPTY_STACK, ERROR_INVALID_VALUE, ERROR_DUPLICATE_KEY, ERROR_NO_TX,
            ERROR_UNKNOWN_KEY, ERROR_DATABASE, ERROR_NO_VALUE};
use snowflake::ProcessUniqueId;
use std::collections::BTreeMap;
use num_bigint::BigUint;
use num_traits::FromPrimitive;

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

type TxnId<'a> = &'a [u8];

#[derive(Debug)]
enum Txn<'a, CR : kv::Cursor<'a>, CW : kv::Cursor<'a>,
             R : kv::ReadTransaction<'a, Cursor = CR>,
             W : kv::WriteTransaction<'a, Cursor = CW>> {
    Read(R, TxnId<'a>),
    Write(W, TxnId<'a>),
}

impl<'a, CR : kv::Cursor<'a>, CW : kv::Cursor<'a>,
    R : kv::ReadTransaction<'a, Cursor = CR>,
    W : kv::WriteTransaction<'a, Cursor = CW>> Txn<'a, CR, CW, R, W> {
    fn tx_type(&self) -> TxType {
        match self {
            &Txn::Read(_, _) => TxType::Read,
            &Txn::Write(_, _) => TxType::Write,
        }
    }
    fn id(&self) -> TxnId<'a> {
        match self {
            &Txn::Read(_, txid) => txid,
            &Txn::Write(_, txid) => txid,
        }
    }
}

use std::sync::Arc;
use super::super::timestamp;
use super::super::nvmem::NonVolatileMemory;

use std::marker::PhantomData;

pub struct Handler<'a, KV, T, N, E, CR, CW, R, W>
    where R : kv::ReadTransaction<'a, Cursor = CR> + 'a,
          W : kv::WriteTransaction<'a, Cursor = CW> + 'a,
          E : ::std::error::Error,
          KV : kv::KeyValueStore<'a, Error = E, ReadTransaction = R, WriteTransaction = W> + 'a,
          T : AsRef<KV> + 'a,
          CR : kv::Cursor<'a>, CW : kv::Cursor<'a>,
          N : NonVolatileMemory {
    kv: T,
    txns: HashMap<EnvId, Vec<Txn<'a, CR, CW, R, W>>>,
    read_cursors: BTreeMap<(EnvId, Vec<u8>), (TxType, CR)>,
    write_cursors: BTreeMap<(EnvId, Vec<u8>), (TxType, CW)>,
    maxkeysize: Vec<u8>,
    timestamp: Arc<timestamp::Timestamp<N>>,
    phantom: PhantomData<(E, R, W, KV)>,
}

macro_rules! read_or_write_transaction {
    ($me: expr, $env_id: expr) => {
        match $me.txns.get(&$env_id)
            .and_then(|v| Some(&v[v.len() - 1])) {
            None => return Err(error_no_transaction!()),
            Some(txn) => txn
        }
    };
}

macro_rules! tx_type {
    ($me: expr, $env_id: expr) => {{
        let txn_type = $me.txns.get(&$env_id)
            .and_then(|v| Some(&v[v.len() - 1]))
            .and_then(|txn| Some(txn.tx_type()));
        if txn_type.is_none() {
            return Err(error_no_transaction!())
        }
        txn_type.unwrap()
    }};
}

macro_rules! for_either_txn_type {
    ($txn: expr, $ident: ident, $body: expr) => {{
        match $txn {
           &Txn::Write(ref $ident, _) => $body,
           &Txn::Read(ref $ident, _) => $body,
        }
    }};
}

macro_rules! for_either_cursor_type {
    ($cur: expr, $me: expr, $txn: expr, $env_id: expr, $cursor: ident, $body: expr) => {{
        let tuple = ($env_id, $cur);
        if $txn.tx_type() == TxType::Read {
            let mut $cursor = match $me.read_cursors.remove(&tuple) {
                Some((_, cursor)) => cursor,
                None => return Err(error_invalid_value!($cur))
            };
            let result = $body;
            $me.read_cursors.insert(tuple, (tx_type!($me, &$env_id), $cursor));
            result
        } else {
            let mut $cursor = match $me.write_cursors.remove(&tuple) {
                Some((_, cursor)) => cursor,
                None => return Err(error_invalid_value!($cur))
            };
            let result = $body;
            $me.write_cursors.insert(tuple, (tx_type!($me, &$env_id), $cursor));
            result
        }
    }};
}

macro_rules! cursor_val_op {
    ($me: expr, $env: expr, $env_id: expr, $op: ident, ($($arg: expr),*)) => {{
        let txn = read_or_write_transaction!($me, &$env_id);
        let c = stack_pop!($env);
        for_either_cursor_type!(Vec::from(c), $me, txn, $env_id, cursor, cursor.$op($($arg)*))
    }};
}

macro_rules! cursor_op {
    ($me: expr, $env: expr, $env_id: expr, $op: ident, ($($arg: expr),*)) => {{
        let result = cursor_val_op!($me, $env, $env_id, $op, ($($arg)*));
        if result.is_ok() {
          $env.push(STACK_TRUE);
        } else {
          $env.push(STACK_FALSE);
        }
    }};
}

builtins!("mod_storage.builtins");

impl<'a, KV, T, N, E, CR, CW, R, W> Dispatcher<'a> for Handler<'a, KV, T, N, E, CR, CW, R, W>
    where R : kv::ReadTransaction<'a, Cursor = CR> + 'a,
          W : kv::WriteTransaction<'a, Cursor = CW> + 'a,
          E : ::std::error::Error,
          KV : kv::KeyValueStore<'a, Error = E, ReadTransaction = R, WriteTransaction = W> + 'a,
          T : AsRef<KV> + 'a,
          CR : kv::Cursor<'a>, CW : kv::Cursor<'a>,
          N : NonVolatileMemory {
    fn done(&mut self, _: &mut Env, pid: EnvId) {
        self.txns.get_mut(&pid)
            .and_then(|vec| {
                while vec.len() > 0 {
                    let txn = vec.pop();
                    drop(txn)
                }
                Some(())
            });
    }

    fn handle(&mut self, env: &mut Env<'a>, instruction: &'a [u8], pid: EnvId) -> PassResult<'a> {
        try_instruction!(env, self.handle_builtins(env, instruction, pid));
        try_instruction!(env, self.handle_write(env, instruction, pid));
        try_instruction!(env, self.handle_read(env, instruction, pid));
        try_instruction!(env, self.handle_txid(env, instruction, pid));
        try_instruction!(env, self.handle_assoc(env, instruction, pid));
        try_instruction!(env, self.handle_assocq(env, instruction, pid));
        try_instruction!(env, self.handle_retr(env, instruction, pid));
        try_instruction!(env, self.handle_commit(env, instruction, pid));
        try_instruction!(env, self.handle_cursor(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_first(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_next(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_prev(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_last(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_seek(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_positionedq(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_key(env, instruction, pid));
        try_instruction!(env, self.handle_cursor_val(env, instruction, pid));
        try_instruction!(env, self.handle_maxkeysize(env, instruction, pid));
        Err(Error::UnknownInstruction)
    }
}

impl<'a, KV, T, N, E, CR, CW, R, W> Handler<'a, KV, T, N, E, CR, CW, R, W>
    where R : kv::ReadTransaction<'a, Cursor = CR> + 'a,
          W : kv::WriteTransaction<'a, Cursor = CW> + 'a,
          E : ::std::error::Error,
          KV : kv::KeyValueStore<'a, Error = E, ReadTransaction = R, WriteTransaction = W> + 'a,
          T : AsRef<KV> + 'a,
          CR : kv::Cursor<'a>, CW : kv::Cursor<'a>,
          N : NonVolatileMemory {
    pub fn new(kv: T, timestamp: Arc<timestamp::Timestamp<N>>) -> Self {
        let maxkeysize = BigUint::from_u32(kv.as_ref().max_keysize()).unwrap().to_bytes_be();
        Handler {
            kv,
            txns: HashMap::new(),
            read_cursors: BTreeMap::new(),
            write_cursors: BTreeMap::new(),
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
    pub fn handle_write(&mut self,
                        env: &mut Env<'a>,
                        instruction: &'a [u8],
                        pid: EnvId)
                        -> PassResult<'a> {
        match instruction {
            WRITE => {
                let v = stack_pop!(env);
                if self.txns.get(&pid).is_some() && self.txns.get(&pid).unwrap().len() > 0 {
                    return Err(error_program!(
                               "Nested WRITEs are not currently allowed".as_bytes(),
                               "".as_bytes(),
                               ERROR_DATABASE));
                }
                match self.kv.as_ref().write_transaction() {
                    Err(kv::TransactionOriginationError::TransactionLimitReached(_)) => Err(Error::Reschedule),
                    Err(kv::TransactionOriginationError::DatabaseError(e)) => Err(error_database!(e)),
                    Ok(txn) => {
                                let txid = self.new_txid(env).unwrap();
                                if !self.txns.contains_key(&pid) {
                                    self.txns.insert(pid, Vec::new());
                                }
                                let _ = self.txns.get_mut(&pid).unwrap().push(Txn::Write(txn, txid));
                                env.program.push(WRITE_END);
                                env.program.push(v);
                                Ok(())
                            },
                }
            }
            WRITE_END => {
                match self.txns.get_mut(&pid).unwrap().pop() {
                    Some(_) => {
                        self.write_cursors = mem::replace(&mut self.write_cursors,
                                                    BTreeMap::new()).into_iter()
                            .filter(|t| ((*t).1).0 != TxType::Read).collect();
                    },
                    _ => {}
                };
                Ok(())
            }
            _ => Err(Error::UnknownInstruction),
        }
    }

    #[inline]
    pub fn handle_read(&mut self,
                       env: &mut Env<'a>,
                       instruction: &'a [u8],
                       pid: EnvId)
                       -> PassResult<'a> {
        match instruction {
            READ => {
                let v = stack_pop!(env);
                match self.kv.as_ref().read_transaction() {
                    Err(kv::TransactionOriginationError::TransactionLimitReached(_)) => Err(Error::Reschedule),
                    Err(kv::TransactionOriginationError::DatabaseError(e)) => Err(error_database!(e)),
                    Ok(txn) => {
                        let txid = self.new_txid(env).unwrap();
                        if !self.txns.contains_key(&pid) {
                            self.txns.insert(pid, Vec::new());
                        }
                        let _ = self.txns.get_mut(&pid).unwrap().push(Txn::Read(txn, txid));
                        env.program.push(READ_END);
                        env.program.push(v);
                        Ok(())
                    }
                }
            }
            READ_END => {
                match self.txns.get_mut(&pid).unwrap().pop() {
                    Some(_) => {
                        self.read_cursors = mem::replace(&mut self.read_cursors,
                                                    BTreeMap::new()).into_iter()
                            .filter(|t| ((*t).1).0 != TxType::Read).collect();
                    },
                    _ => {}
                };
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
        instruction_is!(instruction, TXID);
        self.txns.get(&pid)
            .and_then(|v| Some(&v[v.len() - 1]))
            .and_then(|txn| Some(txn.id()))
            .map_or_else(|| Err(error_no_transaction!()),  |txid| {
                env.push(txid);
                Ok(())
            })
    }

    #[inline]
    pub fn handle_assoc(&self,
						env: &mut Env<'a>,
						instruction: &'a [u8],
						pid: EnvId)
						-> PassResult<'a> {
        instruction_is!(instruction, ASSOC);
        match self.txns.get(&pid)
            .and_then(|v| Some(&v[v.len() - 1]))
            .and_then(|txn| match txn.tx_type() {
                TxType::Write => Some(txn),
                _ => None
            }) {
            Some(&Txn::Write(ref txn, _)) => {
                let value = stack_pop!(env);
                let key = stack_pop!(env);

                match txn.put(key, value) {
                    Ok(_) => Ok(()),
                    Err(kv::Error::DuplicateKey) => Err(error_duplicate_key!(key)),
                    Err(err) => Err(error_database!(err)),
                }
            },
            _ => Err(error_no_transaction!())
        }
    }

    #[inline]
    pub fn handle_commit(&mut self,
						 _: &Env<'a>,
						 instruction: &'a [u8],
						 pid: EnvId)
						 -> PassResult<'a> {
        instruction_is!(instruction, COMMIT);
        match self.txns.get_mut(&pid)
            .and_then(|vec| vec.pop()) {
            Some(Txn::Write(txn, _)) => {
                match txn.commit() {
                    Ok(_) => Ok(()),
                    Err(reason) => Err(error_database!(reason))
                }
            },
            Some(txn) => {
                let _ = self.txns.get_mut(&pid).unwrap().push(txn);
                Err(error_no_transaction!())
            },
            None => Err(error_no_transaction!())
        }
    }


    #[inline]
    pub fn handle_retr(&mut self,
                       env: &mut Env<'a>,
                       instruction: &'a [u8],
                       pid: EnvId)
                       -> PassResult<'a> {
        instruction_is!(instruction, RETR);
        let key = stack_pop!(env);
//        match self.txns.get(&pid)
//            .and_then(|v| Some(&v[v.len() - 1])) {
//            None => Err(error_no_transaction!()),
//            Some(txn) =>
//                for_either_txn_type!(txn, tx, match tx.get(key, env) {
//                    Ok(val) => {
//                        let slice = alloc_and_write!(val, env);
//                        env.push(slice);
//                        Ok(())
//                    },
//                    Err(kv::Error::UnknownKey) => Err(error_unknown_key!(key)),
//                    Err(err) => Err(error_database!(err)),
//                }),
//        }
        Ok(())
    }

    #[inline]
    pub fn handle_assocq(&mut self,
                         env: &mut Env<'a>,
                         instruction: &'a [u8],
                         pid: EnvId)
                         -> PassResult<'a> {
        instruction_is!(instruction, ASSOCQ);
        let key = stack_pop!(env);
//        match self.txns.get(&pid)
//            .and_then(|v| Some(&v[v.len() - 1])) {
//            None => Err(error_no_transaction!()),
//            Some(txn) =>
//                for_either_txn_type!(txn, tx, match tx.get(key, env) {
//                    Ok(val) => {
//                        env.push(STACK_TRUE);
//                        Ok(())
//                    },
//                    Err(kv::Error::UnknownKey) => {
//                        env.push(STACK_FALSE);
//                        Ok(())
//                    },
//                    Err(err) => Err(error_database!(err)),
//                }
//            ),
//        }
        Ok(())
    }

//    fn cast_away_read_cursor<'b, C1 : kv::Cursor<'b>>(cursor: C1) -> CR {
//        unsafe { ::std::mem::transmute(cursor) }
//    }
//    fn cast_away_write_cursor<'b, C1 : kv::Cursor<'b>>(cursor: C1) -> CW {
//        unsafe { ::std::mem::transmute(cursor) }
//    }

    #[inline]
    pub fn handle_cursor(&mut self,
						 env: &mut Env<'a>,
						 instruction: &'a [u8],
						 pid: EnvId)
						 -> PassResult<'a> {
        use serde_cbor;
        instruction_is!(instruction, CURSOR);
        match self.txns.get_mut(&pid) {
            None => Err(error_no_transaction!()),
            Some(v) => {
                let txn = v.pop();
                match txn {
                    None => Err(error_no_transaction!()),
                    Some(txn) => {
                        let id = CursorId::new();
                        let bytes = serde_cbor::to_vec(&id).unwrap();

                        match txn {
                            Txn::Read(txn, _) => {
                                match txn.cursor() {
                                    Err(err) => return Err(error_database!(err)),
                                    Ok(cursor) => {
                                        self.read_cursors.insert((pid.clone(), bytes.clone()),
                                                                 (tx_type!(self, pid), cursor));
                                    }
                                }
                            },
                            Txn::Write(txn, _) => {
                                match txn.cursor() {
                                    Err(err) => return Err(error_database!(err)),
                                    Ok(cursor) => {
                                        self.write_cursors.insert((pid.clone(), bytes.clone()),
                                                                  (tx_type!(self, pid), cursor));
                                    },
                                }
                            },
                        }

                        v.push(txn);

                        Ok(())
                    }
                }
            },
        }
    }

    #[inline]
    pub fn handle_cursor_first(&mut self,
                               env: &mut Env<'a>,
                               instruction: &'a [u8],
                               pid: EnvId)
                               -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_FIRST);
        cursor_op!(self, env, pid, first, ());
        Ok(())
    }


    #[inline]
    pub fn handle_cursor_next(&mut self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_NEXT);
        cursor_op!(self, env, pid, next, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_prev(&mut self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_PREV);
        cursor_op!(self, env, pid, prev, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_last(&mut self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_LAST);
        cursor_op!(self, env, pid, last, ());
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_seek(&mut self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_SEEK);
        let key = stack_pop!(env);
        cursor_op!(self, env, pid, seek_range_k, (key));
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_positionedq(&mut self,
                              env: &mut Env<'a>,
                              instruction: &'a [u8],
                              pid: EnvId)
                              -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_POSITIONEDQ);
        let result = match cursor_val_op!(self, env, pid, is_positioned, ()) {
            true => STACK_TRUE,
            false => STACK_FALSE,
        };
        env.push(result);
        Ok(())
    }

    #[inline]
    pub fn handle_cursor_key(&mut self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             pid: EnvId)
                             -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_KEY);
        match cursor_val_op!(self, env, pid, current_key, (env)) {
            Some(key) => {
                env.push(key);
                Ok(())
            },
            None => Err(error_no_value!()),
        }
    }

    #[inline]
    pub fn handle_cursor_val(&mut self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             pid: EnvId)
                             -> PassResult<'a> {
        instruction_is!(instruction, CURSOR_VAL);
        instruction_is!(instruction, CURSOR_KEY);
        match cursor_val_op!(self, env, pid, current_value, (env)) {
            Some(key) => {
                env.push(key);
                Ok(())
            },
            None => Err(error_no_value!()),
        }
    }

    #[inline]
    pub fn handle_maxkeysize(&mut self,
                             env: &mut Env<'a>,
                             instruction: &'a [u8],
                             _: EnvId)
                             -> PassResult<'a> {
        instruction_is!(instruction, MAXKEYSIZE);
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
    use timestamp;
    use rand::Rng;
    use kv;
    use kv::{KeyValueStore, WriteTransaction, ReadTransaction};

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
        let env = kv::lmdb::create_environment(String::from(path), None, None).unwrap();
        let mut nvmem = MmapedFile::new_anonymous(20).unwrap();
        let region = nvmem.claim(20).unwrap();
        let timestamp = Arc::new(timestamp::Timestamp::new(region));
        let db = kv::lmdb::LmdbKeyValueStore::new(&env).unwrap();
        b.iter(move || {
            let mut timestamps = Vec::new();
            for i in 0..1000 {
                timestamps.push(timestamp.hlc());
            }
            for ts in timestamps {
                match db.write_transaction() {
                    Ok(txn) => {
                        let mut key: Vec<u8> = Vec::new();
                        ts.write_bytes(&mut key);
                        txn.put(key.as_slice(), "Hello".as_bytes()).unwrap();
                        let _ = txn.commit().unwrap();
                    },
                    Err(err) => panic!("Error {:?}", err),
                }
            }
        });
    }

}
