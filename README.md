# Resolution

(Working title.)

A proof interface for creating resolution graphs. Minimal goals are to support
creation and verification of resolution-based proofs of propositional logic
arguments. Hopefully we will also include first-order logic arguments.

Created as a term project for Professor Bram van Heuveln's _Computability and
Logic_ course at RPI, Spring 2019.

## Building

This project is written in Rust and uses Cargo as a build system.

```bash
cargo build
```

Currently, there are no dependencies, so that should do the trick.
We will eventually be depending on (at least)
[gtk-rs](https://crates.io/crates/gtk),
which requires the GTK+3 development libraries to be installed. On
Debian-based Linux:

```bash
sudo apt update; sudo apt install libgtk-3-dev
```

See the gtk-rs docs for other platforms and troubleshooting.

## Documentation

We will strive to keep the in-source developer documentation up to date. To
build and view the documentation:

```bash
cargo doc --open
```

## License

MIT license. See [LICENSE.txt](LICENSE.txt) for further details.
