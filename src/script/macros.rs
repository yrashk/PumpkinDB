// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

macro_rules! write_size_into_slice {
    ($size:expr, $slice: expr) => {
     match $size {
        0...120 => {
            $slice[0] = $size as u8;
            1
        }
        121...255 => {
            $slice[0] = 121u8;
            $slice[1] = $size as u8;
            2
        }
        256...65535 => {
            $slice[0] = 122u8;
            $slice[1] = ($size >> 8) as u8;
            $slice[2] = $size as u8;
            3
        }
        65536...4294967296 => {
            $slice[0] = 123u8;
            $slice[1] = ($size >> 24) as u8;
            $slice[2] = ($size >> 16) as u8;
            $slice[3] = ($size >> 8) as u8;
            $slice[4] = $size as u8;
            5
        }
        _ => unreachable!(),
    }
    };
}

macro_rules! handle_words {
    ($env: expr, $program: expr, $word: expr, $res: ident,
     $pid: ident, { $($me: expr => $name: ident),* }, $block: expr) => {
    {
      let mut env = $env;
      if $word != TRY_END && env.aborting_try.is_some() {
        let $res : (Env<'a>, Option<Vec<u8>>) = (env, None);
        $block
      } else {
      $(
       env =
        match $me.$name(env, $word, $pid) {
          Err((env, Error::Reschedule)) => return Ok((env, Some($program.clone()))),
          Err((env, Error::UnknownWord)) => env,
          Err((mut env, err @ Error::ProgramError(_))) => {
            if env.tracking_errors {
               env.aborting_try = Some(err);
               let $res : (Env<'a>, Option<Vec<u8>>) = (env, None);
               $block
            } else {
               return Err((env, err))
            }
          },
          Err((env, err)) => return Err((env, err)),
          Ok($res) => $block
        };
      )*
      return Err((env, error_unknown_word!($word)))
      }
    }
    };
}

macro_rules! validate_lockout {
    ($env: expr, $name: expr, $pid: expr) => {
        if let Some((pid_, _)) = $name {
            if pid_ != $pid {
                return Err(($env, Error::Reschedule))
            }
        }
    };
}

macro_rules! read_or_write_transaction {
    ($me: expr, $env: expr) => {
        if let Some((_, ref txn)) = $me.db_write_txn {
            txn.deref()
        } else if let Some((_, ref txn)) = $me.db_read_txn {
            txn.deref()
        } else {
            return Err(($env, error_no_transaction!()));
        };
    };
}

macro_rules! stack_pop {
    ($env: expr) => {
        match $env.pop() {
            None => {
                return Err(($env, error_empty_stack!()))
            }
            Some(e) => {
                e
            }
        }
    }
}

macro_rules! word_is {
    ($env: expr, $word: expr, $exp: expr) => {
        if $word != $exp {
            return Err(($env, Error::UnknownWord))
        }
    };
}

macro_rules! error_program {
    ($desc: expr, $details: expr, $code: expr) => {{
        let mut error = Vec::new();

        write_size_header!($desc, error);
        error.extend_from_slice($desc);

        write_size_header!($details, error);
        error.extend_from_slice($details);

        error.extend_from_slice($code);

        Error::ProgramError(error)
    }}
}

macro_rules! error_database {
    ($err: expr) => {{
        let vec = Vec::new();

        error_program!(
            $err.description().as_bytes(),
            &vec,
            ERROR_DATABASE
        )
    }}
}

macro_rules! error_no_transaction {
    () => {{
        let vec = Vec::new();
        error_program!(
            "No transaction".as_bytes(),
            &vec,
            ERROR_NO_TX
        )
    }}
}

macro_rules! error_unknown_key {
    ($key: expr) => {{
        error_program!(
            "Unknown key".as_bytes(),
            $key,
            ERROR_UNKNOWN_KEY
        )
    }}
}

macro_rules! error_duplicate_key {
    ($key: expr) => {{
        error_program!(
            "Duplicate key".as_bytes(),
            $key,
            ERROR_DUPLICATE_KEY
        )
    }}
}

macro_rules! error_decoding {
    () => {{
        let vec = Vec::new();
        error_program!(
            "Decoding error".as_bytes(),
            &vec,
            ERROR_DECODING
        )
    }}
}

macro_rules! error_empty_stack {
    () => {{
        let vec = Vec::new();
        error_program!(
            "Empty stack".as_bytes(),
            &vec,
            ERROR_EMPTY_STACK
        )
    }}
}

macro_rules! error_invalid_value_word {
    ($value: expr) => {{
        error_program!(
            "Invalid value".as_bytes(),
            $value,
            ERROR_INVALID_VALUE
        )
    }}
}

macro_rules! error_invalid_value {
    ($value: expr) => {{
        let mut details = Vec::new();
        write_size_header!($value, details);
        details.extend_from_slice($value);

        error_program!(
            "Invalid value".as_bytes(),
            &details,
            ERROR_INVALID_VALUE
        )
    }}
}

macro_rules! error_unknown_word {
    ($word: expr) => { {
        let (_, w) = binparser::word($word).unwrap();

        let word = match str::from_utf8(&w[1..]) {
            Ok(word) => word,
            Err(_) => "Error parsing word"
        };

        let desc = format!("Unknown word: {}", word);
        let desc_bytes = desc.as_bytes();

        error_program!(
            desc_bytes,
            $word,
            ERROR_UNKNOWN_WORD
        )
    } }
}

macro_rules! write_size_header {
    ($bytes: expr, $vec: expr) => {{
        let mut header = vec![0;offset_by_size($bytes.len())];
        write_size_into_slice!($bytes.len(), header.as_mut_slice());
        $vec.append(&mut header);
    }};
}

#[cfg(test)]
macro_rules! eval {
        ($script: expr, $env: ident, $expr: expr) => {
           eval!($script, $env, _result, $expr);
        };
        ($script: expr, $env: ident, $result: ident, $expr: expr) => {
           eval!($script, $env, $result, publisher_accessor, {}, $expr);
        };
        ($script: expr, $env: ident, $result: ident, $publisher_accessor: ident, {$($init: tt)*}, $expr: expr) => {
          {
            let dir = TempDir::new("pumpkindb").unwrap();
            let path = dir.path().to_str().unwrap();
            fs::create_dir_all(path).expect("can't create directory");
            let env = unsafe {
                lmdb::EnvBuilder::new()
                    .expect("can't create env builder")
                    .open(path, lmdb::open::Flags::empty(), 0o600)
                    .expect("can't open env")
            };

            let db = lmdb::Database::open(&env,
                                 None,
                                 &lmdb::DatabaseOptions::new(lmdb::db::CREATE))
                                 .expect("can't open database");
            crossbeam::scope(|scope| {
                let mut publisher = pubsub::Publisher::new();
                let $publisher_accessor = publisher.accessor();
                let publisher_thread = scope.spawn(move || publisher.run());
                $($init)*
                let mut vm = VM::new(&env, &db, $publisher_accessor.clone());
                let sender = vm.sender();
                let handle = scope.spawn(move || {
                    vm.run();
                });
                let script = parse($script).unwrap();
                let (callback, receiver) = mpsc::channel::<ResponseMessage>();
                let _ = sender.send(RequestMessage::ScheduleEnv(EnvId::new(),
                                    script.clone(), callback));
                match receiver.recv() {
                   Ok(ResponseMessage::EnvTerminated(_, stack, stack_size)) => {
                      let _ = sender.send(RequestMessage::Shutdown);
                      let $result = Ok::<(), Error>(());
                      let mut $env = Env::new_with_stack(stack, stack_size).unwrap();
                      $expr;
                   }
                   Ok(ResponseMessage::EnvFailed(_, err, stack, stack_size)) => {
                      let _ = sender.send(RequestMessage::Shutdown);
                      let $result = Err::<(), Error>(err);
                      let mut $env = Env::new_with_stack(stack.unwrap(), stack_size.unwrap()).unwrap();
                      $expr;
                   }
                   Err(err) => {
                      panic!("recv error: {:?}", err);
                   }
                }
                let _ = handle.join();
                $publisher_accessor.shutdown();
                let _ = publisher_thread.join();
          });
        };
      }
}

#[cfg(test)]
macro_rules! data {
    ($ptr:expr) => {
        {
          let (_, size) = binparser::data_size($ptr).unwrap();
          &$ptr[offset_by_size(size)..$ptr.len()]
        }
    };
}

#[cfg(test)]
macro_rules! parsed_data {
        ($s: expr) => {
           data!(parse($s).unwrap().as_slice())
        };
}

#[cfg(test)]
macro_rules! assert_error {
    ($result: expr, $expected: expr) => {{
        assert!($result.is_err());
        let error = $result.err().unwrap();
        assert!(matches!(error, Error::ProgramError(_)));
        if let Error::ProgramError(inner) = error {
            assert_eq!(inner, parsed_data!($expected));
        } else {
        }
    }};
}