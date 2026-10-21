/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Normal Form for L_{ω₁,ω}: The Σ_α / Π_α Hierarchy

This file defines the normal form hierarchy for infinitary formulas, where formulas
are classified as Σ_α or Π_α for ordinals α.

## Main Definitions

- `IsQF` — a formula is quantifier-free.
- `IsSigma o φ` — the formula `φ` is Σ_o.
- `IsPi o φ` — the formula `φ` is Π_o.

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Section 6.4.
-/

import InfinitaryLogic.Semantics
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v u'

namespace FirstOrder.Language

variable (L : Language.{u, v}) (α : Type u')

namespace InfBoundedFormula

abbrev Formula (n : ℕ) : Type _ :=
  LOmegaOneBoundedFormula.{u, v, u'} L α n

abbrev LevelPred :=
  {n : ℕ} → Formula L α n → Prop

structure SigmaPiPred where
  sigma : LevelPred L α
  pi : LevelPred L α

/-- A formula is quantifier-free if it contains no quantifiers (`all`) and no
infinitary connectives (`iSup`, `iInf`). This is the finitary open class Σ₀ = Π₀. -/
inductive IsQF : {n : ℕ} → Formula L α n → Prop where
  | falsum {n} : IsQF (.falsum : Formula L α n)
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
      IsQF (.equal t₁ t₂ : Formula L α n)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      IsQF (.rel R ts : Formula L α n)
  | imp {n} {φ ψ : Formula L α n} :
      IsQF φ → IsQF ψ → IsQF (φ.imp ψ)

theorem IsQF.not {n : ℕ} {φ : Formula L α n} (h : IsQF L α φ) : IsQF L α φ.not :=
  .imp h .falsum

/-! ### Sigma/Pi hierarchy -/

noncomputable def sigmaPiHierarchy : Ordinal → SigmaPiPred L α :=
  WellFounded.fix Ordinal.lt_wf (fun o rec =>
    let sigma : LevelPred L α := fun {n} φ =>
      if o = 0 then IsQF L α φ else
        ∃ (ι : Type) (ks : ι → ℕ) (ψ : (i : ι) → Formula L α (n + ks i))
          (β : ι → Ordinal) (hβ : ∀ i, β i < o),
          (∀ i, (rec (β i) (hβ i)).pi (ψ i)) ∧
          φ.SemEquiv (.iSup ι (fun i => existsClosure (ks i) (ψ i)))
    let pi : LevelPred L α := fun {n} φ =>
      if o = 0 then IsQF L α φ else
        ∃ (ι : Type) (ks : ι → ℕ) (ψ : (i : ι) → Formula L α (n + ks i))
          (β : ι → Ordinal) (hβ : ∀ i, β i < o),
          (∀ i, (rec (β i) (hβ i)).sigma (ψ i)) ∧
          φ.SemEquiv (.iInf ι (fun i => forallClosure (ks i) (ψ i)))
    { sigma := sigma, pi := pi })

variable {L} {α}

/-- A formula is Σ_o in the Ash-Knight hierarchy.
- Σ_0 = quantifier-free formulas
- Σ_o (o > 0) = disjunction of ∃x̄.ψ where ψ is Π_β for some β < o -/
noncomputable abbrev IsSigma (o : Ordinal) {n : ℕ} (φ : Formula L α n) : Prop :=
  (sigmaPiHierarchy L α o).sigma φ

/-- A formula is Π_o in the Ash-Knight hierarchy.
- Π_0 = quantifier-free formulas
- Π_o (o > 0) = conjunction of ∀x̄.ψ where ψ is Σ_β for some β < o -/
noncomputable abbrev IsPi (o : Ordinal) {n : ℕ} (φ : Formula L α n) : Prop :=
  (sigmaPiHierarchy L α o).pi φ

theorem isSigma_def (o : Ordinal) {n : ℕ} (φ : Formula L α n) :
    IsSigma o φ =
      if o = 0 then IsQF L α φ else
        ∃ (ι : Type) (ks : ι → ℕ) (ψ : (i : ι) → Formula L α (n + ks i))
          (β : ι → Ordinal) (_hβ : ∀ i, β i < o),
          (∀ i, IsPi (β i) (ψ i)) ∧
          φ.SemEquiv (.iSup ι (fun i => existsClosure (ks i) (ψ i))) := by
  rw [IsSigma, sigmaPiHierarchy, WellFounded.fix_eq]
  simp [IsPi, sigmaPiHierarchy]

theorem isPi_def (o : Ordinal) {n : ℕ} (φ : Formula L α n) :
    IsPi o φ =
      if o = 0 then IsQF L α φ else
        ∃ (ι : Type) (ks : ι → ℕ) (ψ : (i : ι) → Formula L α (n + ks i))
          (β : ι → Ordinal) (_hβ : ∀ i, β i < o),
          (∀ i, IsSigma (β i) (ψ i)) ∧
          φ.SemEquiv (.iInf ι (fun i => forallClosure (ks i) (ψ i))) := by
  rw [IsPi, sigmaPiHierarchy, WellFounded.fix_eq]
  simp [IsSigma, sigmaPiHierarchy]

/-! ### Basic properties -/

theorem isQF_iff_sigma_zero {n : ℕ} {φ : Formula L α n} :
    φ.IsQF ↔ IsSigma 0 φ := by
  rw [isSigma_def]; simp

theorem isQF_iff_pi_zero {n : ℕ} {φ : Formula L α n} :
    φ.IsQF ↔ IsPi 0 φ := by
  rw [isPi_def]; simp

/-- Negation of a Σ_o formula is Π_o. -/
theorem neg_sigma_isPi {o : Ordinal} {n : ℕ} {φ : Formula L α n} (h : IsSigma o φ) :
    IsPi o φ.not := by
  sorry

/-- Negation of a Π_o formula is Σ_o. -/
theorem neg_pi_isSigma {o : Ordinal} {n : ℕ} {φ : Formula L α n} (h : IsPi o φ) :
    IsSigma o φ.not := by
  sorry

/-- Monotonicity: Σ_o implies Σ_{o'} for o ≤ o'. -/
theorem IsSigma.mono {o o' : Ordinal} (hle : o ≤ o') {n : ℕ}
    {φ : Formula L α n} (h : IsSigma o φ) : IsSigma o' φ := by
  sorry

/-- Monotonicity: Π_o implies Π_{o'} for o ≤ o'. -/
theorem IsPi.mono {o o' : Ordinal} (hle : o ≤ o') {n : ℕ}
    {φ : Formula L α n} (h : IsPi o φ) : IsPi o' φ := by
  sorry

/-! ### Normal Form Theorem (Theorem 6.2) -/

/-- **Normal Form Theorem** (Ash-Knight Theorem 6.2):
Every L_{ω₁,ω} formula is logically equivalent to both a Σ_α formula and a Π_α formula
for some countable ordinal α. -/
theorem normalFormTheorem {n : ℕ} (φ : L.LOmegaOneBoundedFormula α n)
    (hφ : φ.IsLOmegaOne) :
    ∃ o : Ordinal, o < omegaOne ∧ IsSigma o φ ∧ IsPi o φ := by
  sorry

end InfBoundedFormula

end FirstOrder.Language
