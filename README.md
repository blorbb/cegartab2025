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
dune exec cegarbox [file1 [file2 [...]]]
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
The problems in `data` are from MOLOSS as well.

Extra problems can be found at [mdk-verifier](https://www.cril.univ-artois.fr/~montmirail/mdk-verifier/) ([paper](https://www.researchgate.net/publication/304783698_On_Checking_Kripke_Models_for_Modal_Logic_K)).
However, many of them are far too big for the current implementation to solve in a reasonable amount of time.
The current solver can solve the ones up to around level `3`.
