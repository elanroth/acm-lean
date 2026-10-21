# Scott complexity of reduced abelian p-groups, in Lean 4

A Lean 4 / Mathlib formalization of the back-and-forth characterization that drives the Scott
complexity classification of countable reduced abelian p-groups, together with the first Lean 4
proof of **Ulm's theorem**. Written by Elan Roth during a 2025–26 Fulbright year at the University
of Waterloo, continuing work on the Alvir–Csima–MacLean (ACM) program.

| | |
|---|---|
| Lean | `leanprover/lean4:v4.30.0-rc1` (see `acm/lean-toolchain`) |
| Mathlib | pinned in `acm/lake-manifest.json` |
| Size | 86 `.lean` files, about 28,000 lines, about 810 theorems and lemmas under `acm/Lib` |
| Proof status | no `sorry` under `acm/Lib` or `acm/Test`; public theorems depend only on `propext`, `Classical.choice`, `Quot.sound` |
| License | Apache-2.0 |

## The axiom gate

A `sorry`-free source tree is not the same claim as a `sorry`-free proof: a hole anywhere in the
transitive proof term shows up as `sorryAx` in the kernel's axiom list, whatever the source says.
So the claim above is enforced by [`acm/Test/AxiomGate.lean`](acm/Test/AxiomGate.lean), which is
part of the default build. For every public theorem it runs `#print axioms` under `#guard_msgs`
against the expected list, so the build fails if a hole, a new axiom, or a dependency on the
`sorry`-carrying `infinitary-logic` package ever enters one of these proofs:

```lean
/-- info: 'bf_odd_iff_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bf_odd_iff_algebraic
```

The gated theorems are `bf_odd_iff_algebraic`, `bf_even_iff_algebraic`, `bf_limit_iff_algebraic`,
`acmCharacterizationAtRank`, `acmNecessityAtRank`, `acmSufficiencyAtRank`, `ulm_theorem` and
`ulm_invariants_of_iso`. The GitHub Actions workflow in `.github/workflows/build.yml` runs the
same build and prints the axiom lists in the job log.

## Main results

All statements are for countable reduced abelian p-groups `G`, `H` (`IsReducedPGroup p G`),
ordinals `α : Ordinal.{0}`, and tuples `a : Fin n → G`, `b : Fin n → H`. `BFRel p α n a b` is the
ACM back-and-forth relation `(G, a) ≤_α (H, b)`.

```lean
-- acm/Lib/BackForth/Characterization.lean
theorem bf_odd_iff_algebraic   : BFRel p (2 * α + 1) n a b ↔ AlgBFOddCond p hG hH α a b
theorem bf_even_iff_algebraic  : BFRel p (2 * α + 2) n a b ↔ AlgBFEvenExactCond p hG hH α a b
theorem bf_limit_iff_algebraic (hα : Order.IsSuccLimit α ∨ α = 0) :
                                 BFRel p α n a b ↔ AlgBFLimitCond p hG hH α a b

-- acm/Lib/Ulm/Theorem.lean
theorem ulm_theorem : Nonempty (G ≃+ H) ↔ ∀ α, ulmInvariant p α (G := G) = ulmInvariant p α (G := H)
```

The odd clause is a **room–kernel budget**: with `χ_β` the composite of the source
reachable-to-jump quotient and the induced map `ḡ_β`, a full-rank selector exists exactly when
`dim ker χ_β ≤ dim R_{A,F}(β)` at every height. The even clause is the forward Hill inequality
plus reverse cumulative room. Both replaced a conjectured map-free comparison of dimensions that
the project refuted with a finite counterexample at height 0 (`acm/Test/D5Example.lean`,
`acm/Test/KernelRoomRegression.lean`).

The proof solves all height equations first, as one consistent linear system, and then applies
Rado's independent-transversal theorem to the remaining nested affine access sets
(`acm/Lib/BackForth/FiniteRado.lean`, `HeightRado.lean`).

## Building

```bash
cd acm
lake exe cache get   # Mathlib oleans; saves a multi-hour compile
lake build           # builds Lib, the Test regression library, and the axiom gate
```

`acm` depends on `infinitary-logic` by **path** (`../infinitary-logic`), so clone the whole
repository. The two packages deliberately keep separate `lean-toolchain` files; `lake` handles the
mismatch because `infinitary-logic` is consumed as a dependency, not built as a root.

## Layout

| Path | Contents |
|---|---|
| `acm/Lib/PGroups/` | p-power subgroups, ordinal-indexed Ulm filtration, heights, socles `P_α = G[p] ∩ p^α G`, Ulm / Hill / marked-graded / overhang invariants |
| `acm/Lib/Ulm/` | purity and height-preserving partial maps, Kaplansky's extension interface, the countable back-and-forth assembly, `ulm_theorem` |
| `acm/Lib/BackForth/` | the ACM relations `BFRel`, room and jump space (`JumpSpace.lean`), induced maps, finite challenges and Rado arguments, odd/even/limit sufficiency and necessity, `Characterization.lean` |
| `acm/Lib/Scott/` | Scott-side back-and-forth conditions, algebraic tails, Scott sentence templates |
| `acm/Lib/Logic/BackAndForthCore.lean` | the generic back-and-forth core shared with `infinitary-logic` |
| `acm/Test/` | 18 regression modules. Every module is imported from `acm/Test.lean`, so none can silently drop out of the build |
| `infinitary-logic/` | an independent library on `L_{ω₁,ω}`, Scott families and Scott rank; `acm` uses its definitions. Its `Unfinished/` modules contain `sorry`s, which is why the axiom gate exists |

Comments inside some modules cite research notes (`knowledge/…`, `AUTHORITATIVE.md`, decision
numbers like D-20) that live in the private research repository alongside the paper, not here.

## How it was built

Most of the Lean text was drafted by AI coding agents working under written instructions and a
review structure designed for a volume of proof no one person could read:

- an append-only **decision log** with authority over theorem wording and notation, so a disputed
  definition was settled once and a wrong decision was superseded by a dated entry rather than
  silently edited;
- the **axiom gate** above and the `Test/` regression suite, which pin earlier counterexamples
  and lemma shapes;
- an **adversarial verification pass** before any claim was adopted. That pass is how the
  original target of the project, a conjectured local odd characterization, was found to be false
  at the finite level and replaced by the room–kernel criterion.

Lean identifiers were deliberately frozen while the paper's names evolved (`jumpSpace` is the
paper's `S_{A,E}(β)`), so the code stays stable while the exposition catches up.

## Status and caveats

- The back-and-forth characterization is closed in both directions at every ordinal block.
- Calvert-style index-set verification of the Scott complexity bounds is **not** formalized;
  `acm/Lib/Scott/Complexity.lean` carries sentence-template data only and asserts no bounds.
- `infinitary-logic` has 16 `sorry`s in `NormalForm.lean` and `Unfinished/`; nothing in `acm`'s
  gated theorems depends on them.
- Ulm's theorem here is a candidate for upstreaming to Mathlib; it has not been submitted yet.

## Citing

See `CITATION.cff`. The underlying research paper, *Extending Isomorphisms of Reduced Abelian
p-Groups*, is in preparation.
