// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use std::ptr;

pub enum Multibin<'a> {
    Binary(&'a [u8]),
    Cell(*mut Multibin<'a>, *mut Multibin<'a>)
}

impl<'a> Multibin<'a> {
    pub fn empty() -> Self {
        Multibin::Binary(b"")
    }
    pub fn len(&self) -> usize {
        self.into_iter().fold(0, |sz, item| item.len() + sz)
    }
}

impl<'a> Clone for Multibin<'a> {
    fn clone(&self) -> Self {
        match self {
            &Multibin::Binary(bin) => Multibin::Binary(bin),
            &Multibin::Cell(val, next) => Multibin::Cell(next, val),
        }
    }
}

impl<'a> Eq for Multibin<'a> {}

impl<'a> PartialEq for Multibin<'a> {
    fn eq(&self, other: &Multibin<'a>) -> bool {
        for (item1, item2) in self.into_iter().zip(other.into_iter()) {

        }
    }
}

use std::cmp::Ordering;

impl<'a> PartialOrd for Multibin<'a> {
    fn partial_cmp(&self, other: &Multibin<'a>) -> Option<Ordering> {
        // FIXME: not efficient!
        let val: Vec<u8> = self.into();
        val.partial_cmp(other.into())
    }
}

impl<'a> Ord for Multibin<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        // FIXME: not efficient!
        let val: Vec<u8> = self.into();
        val.cmp(other.into())
    }
}

pub struct MultibinIterator<'a>(*mut Multibin<'a>, Vec<*mut Multibin<'a>>);

impl<'a, 'b> IntoIterator for &'b mut Multibin<'a> {
    type Item = &'a [u8];
    type IntoIter = MultibinIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        MultibinIterator(self, vec![])
    }
}

impl<'a> Iterator for MultibinIterator<'a> {
    type Item = &'a [u8];
    fn next(&mut self) -> Option<Self::Item> {
        if self.0 == ptr::null_mut() {
            if self.1.is_empty() {
                return None;
            } else {
                self.0 = self.1.pop().unwrap();
            }
        }
        match unsafe {&*self.0} {
            &Multibin::Binary(bin) => {
                self.0 = self.1.pop().or_else(|| Some(ptr::null_mut())).unwrap();
                Some(bin)
            },
            &Multibin::Cell(cur, next) => {
                self.0 = cur;
                self.1.push(next);
                self.next()
            }
        }
    }
}

impl<'a, 'b: 'a> Into<Vec<u8>> for &'b Multibin<'a> {
    fn into(self) -> Vec<u8> {
        let mut vec = Vec::new();
        for item in self.into_iter() {
            vec.extend_from_slice(item);
        }
        vec
    }
}

#[cfg(test)]
mod tests {
    use super::Multibin;
    use std::ptr;

    #[test]
    pub fn simple() {
        let s = "hello";
        let mut mb = Multibin::Binary(s.as_bytes());
        let expected = vec![s.as_bytes()];
        let actual : Vec<&[u8]> = mb.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    pub fn simple_len() {
        let s = "hello";
        let mut mb = Multibin::Binary(s.as_bytes());
        assert_eq!(mb.len(), s.len());
    }

    #[test]
    pub fn complex() {
        let s1 = "hello";
        let s2 = "goodbye";
        let mut mb0 = Multibin::Binary(s1.as_bytes());
        let mut mb1 = Multibin::Binary(s2.as_bytes());
        let mut mb2 = Multibin::Cell(&mut mb0, &mut mb1);
        let mut mb3 = Multibin::Cell(&mut mb0, ptr::null_mut());
        let mut mb4 = Multibin::Cell(ptr::null_mut(), &mut mb3);
        let mut mb = Multibin::Cell(&mut mb2, &mut mb4);
        let expected = vec![s1.as_bytes(),  s2.as_bytes(), s1.as_bytes()];
        let actual : Vec<&[u8]> = mb.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    pub fn complex_len() {
        let s1 = "hello";
        let s2 = "goodbye";
        let mut mb0 = Multibin::Binary(s1.as_bytes());
        let mut mb1 = Multibin::Binary(s2.as_bytes());
        let mut mb2 = Multibin::Cell(&mut mb0, &mut mb1);
        let mut mb3 = Multibin::Cell(&mut mb0, ptr::null_mut());
        let mut mb4 = Multibin::Cell(ptr::null_mut(), &mut mb3);
        let mut mb = Multibin::Cell(&mut mb2, &mut mb4);
        assert_eq!(mb.len(), s1.len() + s2.len() + s1.len());
    }

}