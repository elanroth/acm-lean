# `acm` — the Lean package

See the [repository README](../README.md) for the overview, build instructions and the axiom gate.
This file documents the package's internals.

## Build targets

`lakefile.toml` declares two libraries and one executable:

| Target | Root | Purpose |
|---|---|---|
| `Lib` | `Lib.lean` | the formalization |
| `Test` | `Test.lean` | regression modules and `Test/AxiomGate.lean`; built by default so a failing gate fails `lake build` |
| `acm` | `Main.lean` | a trivial executable kept so `lake build` has a binary target |

```bash
lake exe cache get && lake build
lake env lean Test/AxiomGate.lean   # print the axiom lists on demand
```

## Module structure

```text
Lib/
  Basic.lean                  — shared imports, notation, project scope
  Logic/BackAndForthCore.lean — generic back-and-forth core
  PGroups/
    Defs.lean                 — p-power and p-image subgroups
    Subgroups.lean, Basic.lean
    UlmSubgroups.lean         — ordinal-indexed transfinite Ulm filtration G_α
    Heights.lean              — primary, reduced, separable; finite p-height
    Socle.lean                — socle layers P_α = G[p] ∩ G_α and quotient-module setup
    FiniteSocle.lean, FiniteLength.lean
    UlmInvariants.lean        — Ulm, Hill, relative, marked-graded, overhang invariants
    Morphisms.lean            — invariance lemmas (public entry point)
  Ulm/
    Pure.lean                 — purity, height-preserving partial maps, IsProper
    Extension.lean            — Kaplansky relative range and finite-stage extension
    Classification.lean       — finite partial-isomorphism back-and-forth assembly
    Invariance.lean           — easy direction of Ulm's theorem
    Theorem.lean              — ulm_theorem, ulm_theorem_forward, ulm_theorem_backward
  BackForth/
    Relations.lean            — the ACM relations BFRel
    JumpSpace.lean            — room R_{A,E}(β), jump space S_{A,E}(β), relative root lemmas
    RoomTail.lean, Reachable.lean, HeightCell.lean
    InducedMap.lean           — the induced map ḡ_β and its kernel
    KernelRoom.lean           — the room–kernel budget
    FiniteChallenge.lean, FiniteEmbedding.lean, LocalFiniteEmbedding.lean
    FiniteRado.lean, HeightRado.lean, FilteredBasis.lean
    SocleLift.lean, LocalSocleLift.lean
    MarkedCorrection.lean, MarkedGradedTransfer.lean, OverhangTransfer.lean,
    ExactStageTransfer.lean
    OddFiniteExtension.lean, OddLongCountdown.lean      — odd sufficiency
    EvenWindow.lean, EvenToOdd.lean, EvenHighCountdown.lean,
    EvenFiniteExtension.lean                            — even sufficiency
    LimitRestriction.lean                               — limit/zero case
    Survival.lean, Algebraic.lean                       — algebraic packages
    Necessity.lean                                      — all necessity directions
    Characterization.lean                               — the three public biconditionals
  Scott/
    BarkerDefs.lean, AlgebraicTail.lean, Domination.lean, Tuples.lean
    BackAndForth.lean, UpperBounds.lean, LowerBounds.lean, Classification.lean
    Complexity.lean           — Scott sentence templates (data only; no bounds asserted)
Test/                         — 18 regression modules, all imported from Test.lean
```

## Key definitions

```text
pPow p n G                  = p^n · G                                   (AddSubgroup)
ulmSubgroup p α             = G_α, ordinal-indexed by transfinite recursion
pSocleAt p α                = P_α = G[p] ∩ G_α
ulmInvariant p α G          = dim_{ℤ/pℤ}(P_α / P_{α+1})                 (Cardinal)
hillInvariant p S α         = dim P_α / ((S + G_{α+1}) ∩ P_α)
markedGradedInvariant p S α = dim P_α / (P_{α+1} + (S ∩ P_α))
overhangInvariant p S α     = dim ker(markedGraded_α(S) → Hill_α(S))
ulmLength p G               = sInf { α | G_α = 0 }                        (Ordinal)

room p E β                  = R_{A,E}(β) = P_β / (E ∩ P_β)
jumpSpace p E β             = S_{A,E}(β) = (pE ∩ G_{β+1}) / p(E ∩ G_β)
IsProper p E x              = h(x) ≥ h(x + e) for all e ∈ E
```

`room` is a third quotient of `P_β`, distinct from the marked-graded and Hill quotients; the
denominators are ordered `E ∩ P_β ≤ P_{β+1} + (E ∩ P_β) ≤ (E + G_{β+1}) ∩ P_β`, and
`Test/JumpSpaceRegression.lean` pins that ordering.

## Conventions

- Ordinals are `Ordinal.{0}` throughout.
- Names of record: `room`, `hill*`, `jumpSpace`, `K_beta`. These were frozen on purpose while the
  paper's notation changed; do not rename to match prose.
- Every `Test/` module must be imported from `Test.lean`, or `lake build` will not compile it.
- Comments citing `knowledge/…`, `AUTHORITATIVE.md` or decision numbers (D-5, D-20, …) refer to
  research notes in the private repository, not to files here.
