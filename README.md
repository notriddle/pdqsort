# Pattern-defeating quicksort

[![Build Status](https://travis-ci.org/stjepang/pdqsort.svg?branch=master)](https://travis-ci.org/stjepang/pdqsort)
[![License](https://img.shields.io/badge/license-Apache--2.0%2FMIT-blue.svg)](https://github.com/stjepang/pdqsort)
[![Cargo](https://img.shields.io/crates/v/pdqsort.svg)](https://crates.io/crates/pdqsort)
[![Documentation](https://docs.rs/pdqsort/badge.svg)](https://docs.rs/pdqsort)

This sort is significantly faster than the standard sort in Rust. In particular, it sorts
random arrays of integers approximately 40% faster. The key drawback is that it is an unstable
sort (i.e. may reorder equal elements). However, in most cases stability doesn't matter anyway.

The algorithm was designed by Orson Peters and first published at: https://github.com/orlp/pdqsort

#### Properties

* Best-case running time is `O(n)`.
* Worst-case running time is `O(n log n)`.
* Unstable, i.e. may reorder equal elements.
* Does not allocate additional memory.
* Compatible with `#![no_std]`.

#### Example

```rust
extern crate pdqsort;

let mut v = [-5, 4, 1, -3, 2];
pdqsort::sort(&mut v);
assert!(v == [-5, -3, 1, 2, 4]);
```

#### A simple benchmark

Sorting 10 million random numbers of type `u64`:

| Sort              | Time       |
|-------------------|-----------:|
| pdqsort           | **396 ms** |
| slice::sort       |     668 ms |
| [quickersort][qs] |     777 ms |
| [dmsort][ds]      |     728 ms |
| [rdxsort][rs]     |     602 ms |

#### Extensive benchmarks

The benchmarks that follow are [used in Rust][bench] for testing the performance of slice::sort.

| Benchmark               | pdqsort           | slice::sort       | [quickersort][qs] | [dmsort][ds]      | [rdxsort][rs] |
|-------------------------|------------------:|------------------:|------------------:|------------------:|--------------:|
| large_ascending         |      **7,174 ns** |          9,067 ns |        12,049 ns  |         21,918 ns |    358,490 ns |
| large_big_ascending     |    **369,921 ns** |        370,352 ns |       374,000 ns  |        412,064 ns | 49,596,895 ns |
| large_big_descending    |    **426,717 ns** |        441,120 ns |       570,564 ns  |        814,455 ns | 49,675,077 ns |
| large_big_random        |      2,001,114 ns |      2,141,195 ns | **1,970,706 ns**  |      2,308,335 ns | 43,578,405 ns |
| large_descending        |     **10,873 ns** |         13,717 ns |        46,116 ns  |        143,599 ns |    347,355 ns |
| large_mostly_ascending  |         83,789 ns |        239,114 ns |       129,134 ns  |     **44,522 ns** |    352,691 ns |
| large_mostly_descending |        151,457 ns |        268,573 ns |   **134,891 ns**  |        282,361 ns |    349,217 ns |
| large_random            |    **359,871 ns** |        508,701 ns |       533,575 ns  |        543,719 ns |    399,124 ns |
| large_random_expensive  |     63,657,586 ns | **23,689,555 ns** |               -   |     31,210,721 ns |            -  |
| medium_ascending        |         **94 ns** |            145 ns |           148 ns  |            259 ns |      4,509 ns |
| medium_descending       |        **122 ns** |            188 ns |           490 ns  |          1,344 ns |      4,947 ns |
| medium_random           |      **3,053 ns** |          3,297 ns |         3,252 ns  |          3,722 ns |      6,466 ns |
| small_ascending         |         **25 ns** |             32 ns |        **25 ns**  |             47 ns |      1,597 ns |
| small_big_ascending     |         **82 ns** |             95 ns |            89 ns  |            136 ns |     35,749 ns |
| small_big_descending    |        **143 ns** |            246 ns |           420 ns  |            517 ns |     35,807 ns |
| small_big_random        |            508 ns |        **492 ns** |           582 ns  |            671 ns |     46,393 ns |
| small_descending        |         **28 ns** |             55 ns |            51 ns  |            232 ns |      1,595 ns |
| small_random            |            355 ns |            346 ns |       **333 ns**  |            484 ns |      3,841 ns |

[qs]: https://github.com/notriddle/quickersort
[ds]: https://github.com/emilk/drop-merge-sort
[rs]: https://github.com/crepererum/rdxsort-rs
[bench]: https://github.com/rust-lang/rust/blob/468227129d08b52c4cf90313b29fdad1b80e596b/src/libcollectionstest/slice.rs#L1406
