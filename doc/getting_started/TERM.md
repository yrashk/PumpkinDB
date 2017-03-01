# Accessing PumpkinDB

While the primary "production" way to communicate to
PumpkinDB is use of its TCP protocol, for the purpose of
experimentation and running ad-hoc scripts, something more
human-friendly would be useful. And PumpkinDB something just like that.

But first, we need to start PumpkinDB itself. This is fairly simple,
just run `pumpkindb` executable. To keep it easy, we won't be exploring
its optional configuration capabilities here.

```shell
$ pumpkindb
2017-03-01T11:45:45.585819+07:00 WARN pumpkindb - No logging configuration specified, switching to console logging
2017-03-01T11:45:45.586701+07:00 INFO pumpkindb - Starting up
2017-03-01T11:45:45.587537+07:00 INFO pumpkindb - Available disk space is approx. 27Gb, setting database map size to it
2017-03-01T11:45:45.592105+07:00 INFO pumpkindb::server - Listening on 0.0.0.0:9981
```

Now, in a separate terminal session, you can run `pumpkindb-term`, a utility that allows you to interact with PumpkinDB:

```shell
$ pumpkindb-term
Connected to PumpkinDB at 127.0.0.1:9981
To send an expression, end it with `.`
Type \h for help.
PumpkinDB>
```

You can try sending simple expressions to see if everything works fine:

```shell
PumpkinDB> 1 2 3.
0x01 0x02 0x03
PumpkinDB> "Hello, world!".
"Hello, world!"
```

Note that every expression has to be terminated with a period (`.`) to be sent to the server.

This terminal expressions are actually a construct in a small programming language called [PumpkinScript](../script/README.md). You can proceed with this chapter without knowing too much about it just to get a feel, but in order to operate PumpkinDB you have to have a command of the language.
