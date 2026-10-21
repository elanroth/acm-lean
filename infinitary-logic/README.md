# Infinitary Logic

Lean 4 formalization of infinitary logic centered on `L_{ω₁,ω}`: syntax, semantics, normal forms,
embeddings, Scott families, Scott sentences and Scott rank. The `acm` package in this repository
consumes it by path.

## Status

`Syntax.lean`, `Semantics.lean` and `Embedding.lean` are `sorry`-free. `NormalForm.lean` and the
modules under `Unfinished/` (`Rank.lean`, `ScottFamily.lean`, `ScottSentence.lean`) contain
`sorry`s and are work in progress. Nothing in `acm`'s gated theorems depends on a `sorry` here;
`acm/Test/AxiomGate.lean` would fail the build if that changed.

## Build

```bash
lake build
```

## Import graph

The `scripts/` directory generates an HTML import DAG with `lake exe graph` and a small renderer:

```bash
./scripts/construct-and-view-dag.sh                      # whole library
./scripts/construct-and-view-dag.sh InfinitaryLogic.Syntax
```

Licensed under Apache-2.0 (see `LICENSE`).
