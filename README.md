# Flashmap

Rust port of [flashmap](https://chromium.googlesource.com/chromiumos/third_party/flashmap) from ChromiumOS

The library portion is all `no_std`, so suitable to be used in embedded settings. Currently the library does require `alloc`.

Usage of the library should be identical to the original `flashmap`: able to read and write `fmap` data structures from / to memory
