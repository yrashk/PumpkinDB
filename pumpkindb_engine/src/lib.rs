// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![feature(slice_patterns, advanced_slice_patterns)]
#![feature(struct_field_attributes)]
#![feature(try_trait)]

#![cfg_attr(test, feature(test))]
#![cfg_attr(not(target_os = "windows"), feature(alloc, heap_api))]
#![feature(alloc)]

include!("crates.rs");

pub mod allocator;
pub use allocator::Allocator;
pub mod script;
pub mod messaging;
pub mod timestamp;
pub mod nvmem;
pub mod kv;