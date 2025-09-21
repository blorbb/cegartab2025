# Formalised CEGAR-Tableaux

WIP.

See the rendered Rocq documentation at https://blorbb.github.io/cegartab2025/toc.html.

## Usage

Rocq proofs in `theories/`. OCaml extraction and bindings in `cegarbox/`.

Requires Rocq 9.0.0 and OCaml 5.3.0.

Install Rocq and OCaml in any way, or through an `opam` switch:

```sh
opam switch create rocq 5.3.0
opam switch rocq
eval $(opam env)
opam pin add rocq-prover 9.0.0
```

Running the OCaml code requires `dune`, `minisat` and `menhir`.

```sh
opam install dune minisat menhir
```

To run,

```sh
cd cegarbox
dune exec --profile release cegarbox -- file1 [file2 [...]]
```

Where each of the files is a formula in InToHyLo format.
A bunch of example formulae are provided in `cegarbox/data` which should all provide a SAT result.

### Compiling

Recompile the Rocq source and regenerate the OCaml extractions by running

```sh
make clean && make
```

### Building Documentation

```sh
make doc
```

## Credits

Thanks to [Ian Shillito](https://github.com/ianshil) for helpful instructions on getting this working.

Most styling and custom features from [CoqdocJS](https://github.com/rocq-community/coqdocjs).

The OCaml lexer and parser are from https://github.com/jogiet/MOLOSS.
