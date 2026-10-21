import Lib.PGroups.Socle
import Lib.PGroups.UlmInvariants

/-!
# Algebraic tail invariants and socle data

This module packages the algebraic data used in the Scott-complexity track:

- cumulative socle dimensions
- ambient socle dimensions relative to a subgroup
- relative Ulm invariants
- tail invariants and tail sums

These are the algebraic quantities appearing in the March 18 notes.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

section SocleDimensions

variable {G : Type u} [AddCommGroup G]

/-- The cumulative socle dimension `s_k(G)`, for finite-height level `k`. -/
noncomputable def socleDim (k : ℕ) : Cardinal := by
  let Pk := pSocleAt p (k : Ordinal.{0}) (G := G)
  let _ : Module (ZMod p) Pk := pSocleAt_ZMod_module (p := p) (G := G) (k : Ordinal.{0})
  exact Module.rank (ZMod p) Pk

/-- The ambient socle dimension `s_k(F; G)` of a subgroup `F ≤ G`. -/
noncomputable def ambientSocleDim (F : AddSubgroup G) (k : ℕ) : Cardinal := by
  let Pk := F ⊓ pSocleAt p (k : Ordinal.{0}) (G := G)
  let _ : Module (ZMod p) Pk := by
    classical
    refine AddCommGroup.zmodModule (n := p) (G := Pk) ?_
    intro x
    have hx : p • ((x : Pk) : G) = 0 :=
      (mem_pSocleAt p (k : Ordinal) (((x : Pk) : G))).1 x.property.2 |>.1
    ext
    simpa using hx
  exact Module.rank (ZMod p) Pk

end SocleDimensions

section TailData

variable {G : Type u} [AddCommGroup G]

/-- The `i`-th tail Ulm invariant at base level `ω·γ`. -/
noncomputable def tailInvariant (γ : Ordinal.{0}) (i : ℕ) : Cardinal :=
  ulmInvariant p (ω * γ + i) (G := G)

/-- The `i`-th relative tail Ulm invariant. -/
noncomputable def tailRelInvariant (γ : Ordinal.{0}) (C : AddSubgroup G) (i : ℕ) : Cardinal :=
  relativeUlmInvariant p C (ω * γ + i)

/-- The cumulative tail sum `∑_{i ≥ k} f_G(ω·γ+i)`. -/
noncomputable def tailSum (γ : Ordinal.{0}) (k : ℕ) : Cardinal :=
  Cardinal.sum fun i : ℕ => tailInvariant p (G := G) γ (i + k)

/-- The cumulative relative tail sum `∑_{i ≥ k} f_{G,C}(ω·γ+i)`. -/
noncomputable def tailRelSum (γ : Ordinal.{0}) (C : AddSubgroup G) (k : ℕ) : Cardinal :=
  Cardinal.sum fun i : ℕ => tailRelInvariant p (G := G) γ C (i + k)

end TailData
