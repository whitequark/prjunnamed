Project Unnamed
===============

Project Unnamed aims to deliver a comprehensive end-to-end FPGA synthesis, placement, routing, and bitstream generation tools targeting multiple FPGA families and integrating with [Project Combine][prjcombine].

The project is currently in the early stage of research and prototyping, and is not suitable for general use.

[prjcombine]: https://github.com/prjunnamed/prjcombine


Development
-----------

In order to build Project Unnamed and run its testsuite, you will need [Rust][] (latest stable release) and [Z3][]. We recommend using [rustup][] or installing Rust from the software repository of your Linux distribution. Once you have these tools, run:

```console
$ cargo test
```

We use [rustfmt][] to ensure consistent formatting of the entire codebase. Prior to sending a pull request, run:

```console
$ cargo fmt
```

[rust]: https://rust-lang.org/
[rustfmt]: https://rust-lang.github.io/rustfmt/
[rustup]: https://rustup.rs/
[z3]: https://github.com/Z3Prover/z3


License
-------

Project Unnamed is distributed under the terms of the [0-clause BSD license](LICENSE-0BSD.txt) and the [Apache License (Version 2.0)](LICENSE-Apache-2.0.txt).

By submitting your contribution you agree to be bound by all provisions of both of these licenses, including the clause 3 (Grant of Patent License) of the Apache License (Version 2.0).
