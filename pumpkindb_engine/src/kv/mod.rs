// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Misconfiguration(err: String) {
           description("misconfiguration")
           display("Misconfiguration: {}", err)
        }
        DuplicateKey {}
        UnknownKey {}
        Code(code: i64) {}
        UnknownError {}
    }
}

pub trait ReadTransaction {
//    type Cursor: Cursor;
    fn cursor<'c>(&'c self) -> Result<Box<Cursor + 'c>, Error>;
    fn get<'a, A : Allocator<'a>>(&self, key: &[u8], allocator: &mut A) -> Result<&'a [u8], Error>;
}

pub trait WriteTransaction : ReadTransaction {
    fn put<'a>(&self, key: &'a [u8], value: &'a [u8]) -> Result<(), Error>;
    fn commit(self) -> Result<(), Error>;
}

use allocator::Allocator;

pub trait Cursor {
    fn first(&mut self) -> Result<(), Error>;
    fn last(&mut self) -> Result<(), Error>;
    fn next(&mut self) -> Result<(), Error>;
    fn prev(&mut self) -> Result<(), Error>;
    fn seek_range_k(&mut self, key: &[u8]) -> Result<(), Error>;
    fn is_positioned(&self) -> bool;
    fn current_key<'a, A : Allocator<'a>>(&mut self, allocator: &mut A) -> Option<&'a [u8]>;
    fn current_value<'a, A : Allocator<'a>>(&mut self, allocator: &mut A) -> Option<&'a [u8]>;
}

#[derive(Debug)]
pub enum TransactionOriginationError<E> {
    TransactionLimitReached(usize),
    DatabaseError(E),
}

pub trait KeyValueStore {
    type WriteTransaction : WriteTransaction;
    type ReadTransaction : ReadTransaction;
    type Error : ::std::error::Error;
    fn read_transaction(&self) -> Result<Self::ReadTransaction, TransactionOriginationError<Self::Error>>;
    fn write_transaction(&self) -> Result<Self::WriteTransaction, TransactionOriginationError<Self::Error>>;

    fn max_readers(&self) -> usize;
    fn max_writers(&self) -> usize;
    fn max_keysize(&self) -> u32;
}


pub mod lmdb;