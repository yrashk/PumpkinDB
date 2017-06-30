// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use lmdb::*;
use std::ptr;
use libc::c_int;

use std::marker::PhantomData;

use super::{Txn, LmdbError, LmdbResult};
use kv::{Cursor, Error};

use allocator::Allocator;

pub struct LmdbCursor<'a, 'txn, A : Allocator<'a>> {
    cursor: *mut MDB_cursor,
    allocator: A,
    phantom: PhantomData<&'txn ()>,
}

impl<'txn, 'a, A : Allocator<'a>> LmdbCursor<'txn, 'a, A> {
    pub fn new(txn: &'txn Txn, allocator : A) -> Result<Self, Error> {
        Ok(LmdbCursor {
            cursor: (),
            allocator,
            phantom: PhantomData,
        })
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

impl<'a, 'txn, A : Allocator<'a>> Cursor<'txn, A> for LmdbCursor<'a, 'txn, A> {
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

    fn current_key<'b>(&mut self, allocator: &mut A) -> Option<&'b [u8]> {
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

    fn current_value<'b>(&mut self, allocator: &mut A) -> Option<&'b [u8]> {
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
