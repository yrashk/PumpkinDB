# Storing and retrieving data

We'll start with the most basic operations of data storage and retrieval here. Since at its core PumpkinDB is a key/value database, it defines a
set of low-level primitives to do just that — storing and retrieving data.

PumpkinDB defines a very basic [ASSOC](../script/ASSOC.md) word that
handles just that, associating a value with a key and it looks like this:

```
"my key" 1 ASSOC
```

This maps the binary representation of `1` (variable unsigned big integer) to the key of "my key" (UTF-8 encoded key). However, if you try to run this in the terminal, you will get an error:

```
PumpkinDB> "my key" 1 ASSOC.
"my key" 0x01 Error: "No transaction" "" 0x08
```

That's because all write operations have to happen within boundaries of a write transaction. How do we do that? Simple, by wrapping our code into a closure and passing it to [WRITE](../script/WRITE.md):

```
PumpkinDB> ["my key" 1 ASSOC] WRITE.
PumpkinDB>
```

Let's try reading it with [RETR](../script/RETR.md), similarly wrapped into a [read transaction](../script/READ.md) (reads have to happen within either a read or a write transaction):

```
PumpkinDB> ["my key" RETR] READ.
Error: "Unknown key" 0x066d79206b6579 0x07
```

Why did that happen? That's because we forgot to [commit](../script/COMMIT.md) the association first time around. Let's try this again:

```
PumpkinDB> ["my key" 1 ASSOC COMMIT] WRITE.
PumpkinDB> ["my key" RETR] READ.
0x01
```

Voila! We just retrieved the value back.

Remember that part of PumpkinDB materials that said it is an event sourcing database? At the lowest level, it means that we don't allow overriding key values (there's an escape hatch of controlled key/value association retirement, but we'll touch on that later).

So, if you try to run the association code again, you will get an error:

```
PumpkinDB> ["my key" 1 ASSOC COMMIT] WRITE.
Error: "Duplicate key" 0x066d79206b6579 0x06
```

Now, of course you can [check](../script/ASSOCQ.md) before writing to prevent an error:

```
PumpkinDB> ["my key" DUP ASSOC? [DROP] [1 ASSOC COMMIT] IFELSE] WRITE.
PumpkinDB>
```

This slightly more complicated code checks if "my key" has already been associated, and if it hasn't, it associates it with the value (`1`).

But if keys can't be overriden, how does one provide a new value to something identifiable? Here's what our standard approach to this is like. We treat such updates as new key/value associations with keys appended with unique, monotonously growing values, like this:

```
PumpkinDB> ["my key" 1 CONCAT 1 ASSOC COMMIT] WRITE.
PumpkinDB> ["my key" 2 CONCAT 2 ASSOC COMMIT] WRITE.
PumpkinDB> ["my key" 3 CONCAT 3 ASSOC COMMIT] WRITE.
```

Here we are creating new keys `"my key" 1 CONCAT` becoming "my key\0x01" and so forth. But of course, it isn't very practical to
do enumerations this way. Not only this is inconvenient but you also
need to ensure correct number padding to make these keys properly
sorted lexicographically. Instead of supplying numbers, we'd use a
word that is guaranteed to always return a unique, monotonously growing value. Right now we have one such word implemented, [HLC](../script/HLC.md), which stands for Hybrid Logical Clock. The value it returns is always of the same size, it always grows and it contains an actual timestamp inside!

```
PumpkinDB> HLC (just to see how it looks like).
0x0000000014a7af8b406b391000000000
PumpkinDB> ["hlckey" HLC CONCAT 1 ASSOC COMMIT] WRITE.
PumpkinDB> ["hlckey" HLC CONCAT 2 ASSOC COMMIT] WRITE.
PumpkinDB> ["hlckey" HLC CONCAT 3 ASSOC COMMIT] WRITE.
```

Ok, now that we have stored it, how do we get the last value? It wouldn't be great if we need to keep the last value returned by HLC around just for that! Well, again, we have a [tool](../script/QCURSOR/SEEKLAST.md) just for that:

```
PumpkinDB> [CURSOR "hlckey" ?CURSOR/SEEKLAST] READ UNWRAP NIP.
0x03
```

As you can see, it retrieved the last value (`3`). Why did we have
to do `UNWRAP NIP` on the right? That's just so that we can extract
just the value part of of the pair. `?CURSOR/SEEKLAST` returns a "wrap" of two values: key and value. You'll learn more about this technique later.

`?CURSOR/SEEKLAST` is a part of a bigger family of cursor-related words, and you can learn about them in the [next section](CURSORS.md).
