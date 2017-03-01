# Installing PumpkinDB

You can download PumpkinDB releases [from GitHub](https://github.com/PumpkinDB/PumpkinDB/releases). Simply
unpack a relevant archive and put the binaries where you can
call them from, for example `/usr/local/bin` or somewhere in your
home folder (say, `~/pumpkindb`).

If you are interested in the latest and greatest (since PumpkinDB
is in a state of active development towards 1.0), you are also welcome to clone the repository and build it yourself. You will need Rust Nightly to do this. The easiest way to get it is to use
[rustup](https://www.rust-lang.org/en-US/install.html).

```shell
$ rustup install nightly
$ cd /path/to/pumpkindb
$ rustup override set nightly
$ cargo build --release
```
