# Formally Verified Asynchronous Dataflow Compiler (Anonymized)

Welcome to the anonymized artifact of Wavelet, a formally verified asynchronous dataflow compiler.

Our frontend type system can be found in `dfx` and
our verified core passes in Lean 4 can be found in `lean/Wavelet`.

## Building Wavelet

Requirements:
- [Lake 5.0.0 (Lean 4.24.0)](https://lean-lang.org/doc/reference/4.24.0/Build-Tools-and-Distribution/Lake/)
- [Cargo 1.89.0](https://doc.rust-lang.org/cargo/getting-started/installation.html)

To check all proofs and build the compiler in Lean:
```
cd lean
lake exec cache get
lake build
```

To build the type checker
```
cd dfx
cargo build
```

Or directly
```
cargo run -- --help
```

## Running Wavelet

Take one of our eval programs as example, `eval/src/dmv.rs`,
which does (dense) matrix-vector multiplication.
```
# At the root of the repo

# Converts dmv.rs with types and fences to an IR accepted by the Lean backend
dfx/target/debug/dfx eval/src/dmv.rs > dmv.json

# Compiles the input program and outputs a DOT format of the dataflow graph
lean/.lake/build/bin/wavelet dmv.json --format dot --no-out --stats
```

You can visualize the dataflow graph in DOT format (`digraph { ... }`)
in an online Graphviz renderer, such as <https://dreampuf.github.io/GraphvizOnline/>.
