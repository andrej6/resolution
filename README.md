# ARes

John Andrews and Jacques Becker - April 25th, 2019

A tool for verifying resolution graphs. Minimal goals are to support
creation and verification of resolution-based proofs of propositional logic
arguments. 

Created as a term project for Professor Bram van Heuveln's _Computability and
Logic_ course at RPI, Spring 2019.

## Building

This project is written in Rust and uses Cargo as a build system. The following
should download all dependencies and build the project:

```bash
$ cargo build
```

## How to Use

To use ARes, run the binary from the command line with the resolution graph's filename
as the first argument:

```bash
$ ./ARes filename
```

The file must have the following format:

```
label1: {P, Q} ()
label2: {~Q, R} ()
label3: {P, R} (label1, label2)
```

Each clause must have an identifying label ending in a colon. The clause literals themselves
are a comma separated list of identifiers contained between curly braces. The identifiers
can be any string. If a clause is the product of the resolution of other clauses, it must
list its parent clauses in a parenthesized, comma-separated list after the list of literals.
The parentheses must be present even if the clause has no parents.

## Documentation

We will strive to keep the in-source developer documentation up to date. To
build and view the documentation:

```bash
$ cargo doc --open
```

## License

MIT license. See [LICENSE.txt](LICENSE.txt) for further details.
