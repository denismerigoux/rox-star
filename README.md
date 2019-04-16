# Rox-star

The full context for this work is presented [on the author's blog](https://blog.merigoux.ovh/en/2019/04/16/verifying-rust.html).

## Examples

This repo contains motivating examples for a Rust -> Oxide -> F\* verification toolchain. The two main examples are in the folders `textinput` and `bloom-filter`. Each one is a Rust crate that you can `cargo build` or `cargo test`, along with an F\* implementation that you can `make verify` or `make test`.

To install F*, please follow the instructions [here](https://github.com/FStarLang/FStar).
