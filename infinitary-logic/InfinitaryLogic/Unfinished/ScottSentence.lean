/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Scott's Isomorphism Theorem

Every countable structure has a **Scott sentence**: an L_{ω₁,ω} sentence whose
countable models are exactly the isomorphic copies of the structure.

## Main Definitions

- `IsScottSentence σ M` — σ is a Scott sentence for M.
- `scottSentenceOfFamily` — constructs a Scott sentence from a Scott family.

## Key Theorems

- `exists_scottSentence` — Scott's Isomorphism Theorem (Theorem 6.5):
  every countable structure has a Scott sentence.
- `countable_infEquiv_iff_iso` — countable structures are L_{ω₁,ω}-equivalent iff isomorphic.

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Section 6.6.
- D. Scott, "Logic with denumerably long formulas and finite strings of quantifiers", 1965.
-/

import InfinitaryLogic.Unfinished.ScottFamily

universe u v w

namespace FirstOrder.Language

variable (L : Language.{u, v})

/-- A **Scott sentence** for a structure M is an L_{ω₁,ω} sentence σ such that
for any countable structure N:
  N ⊨ σ  ↔  N ≅ M

That is, the countable models of σ are exactly the isomorphic copies of M. -/
def IsScottSentence (σ : @LOmegaOneSentence.{u, v} L) (M : Type*) [L.Structure M] : Prop :=
  σ.IsLOmegaOne ∧
  ∀ (N : Type*) [L.Structure N] [Countable N] [Nonempty N],
    (InfSentence.Realize σ N ↔ Nonempty (M ≃[L] N))

variable {L}

/-! ### Construction of Scott sentence from a Scott family -/

/-- Given a Scott family Φ = {φ^n_j : j ∈ J_n, n ∈ ω} for a structure M,
the Scott sentence is the conjunction of:

1. **σ_∃**: For each n, every n-tuple satisfies some formula in the family:
   ⋀_n ∀x₁...∀xₙ. ⋁_{φ ∈ Φ(n)} φ(x₁,...,xₙ)

2. **σ_back**: For each φ(x₁,...,xₙ) ∈ Φ(n), every element has a witness
   satisfying some extension formula:
   ⋀_n ⋀_{φ ∈ Φ(n)} ∀x₁...∀xₙ. (φ(x̄) → ∀y. ⋁_{ψ ∈ Φ(n+1)} ψ(x̄,y))

3. **σ_forth**: Symmetric to σ_back, for the forth direction.

The conjunction σ_∃ ∧ σ_back ∧ σ_forth gives the Scott sentence. -/
noncomputable def scottSentenceOfFamily {M : Type*} [L.Structure M] [Countable M]
    (Φ : ScottFamily L M) : @LOmegaOneSentence.{u, v} L :=
  sorry

/-- The Scott sentence constructed from a Scott family is indeed a Scott sentence. -/
theorem scottSentenceOfFamily_isScott {M : Type*} [L.Structure M] [Countable M]
    [Nonempty M] (Φ : ScottFamily L M) :
    IsScottSentence L (scottSentenceOfFamily Φ) M := by
  sorry

/-! ### Scott's Isomorphism Theorem -/

/-- **Scott's Isomorphism Theorem** (Theorem 6.5, Ash-Knight):
Every countable nonempty L-structure has a Scott sentence — an L_{ω₁,ω} sentence
whose countable models are exactly the isomorphic copies of M.

The proof combines:
1. Lemma 6.7: M has a Scott family Φ with no parameters.
2. The construction above: Φ yields a Scott sentence σ.
3. Verification that σ characterizes M among countable structures. -/
theorem exists_scottSentence (M : Type*) [L.Structure M] [Countable M] [Nonempty M] :
    ∃ σ : @LOmegaOneSentence.{u, v} L, IsScottSentence L σ M := by
  sorry

/-- **Corollary**: Two countable structures are L_{ω₁,ω}-elementarily equivalent
if and only if they are isomorphic.

Each has a Scott sentence; if they satisfy the same sentences, they satisfy each
other's Scott sentences and are therefore isomorphic. -/
theorem countable_infEquiv_iff_iso (M N : Type*)
    [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    [Nonempty M] [Nonempty N] :
    infElementarilyEquivalent (L := L) M N ↔ Nonempty (M ≃[L] N) := by
  sorry

/-! ### Uniqueness of Scott sentences -/

/-- Any two Scott sentences for the same structure are semantically equivalent
on countable structures: they have exactly the same countable models. -/
theorem scottSentence_unique {M : Type*} [L.Structure M] [Countable M] [Nonempty M]
    {σ τ : @LOmegaOneSentence.{u, v} L}
    (hσ : IsScottSentence L σ M) (hτ : IsScottSentence L τ M) :
    ∀ (N : Type*) [L.Structure N] [Countable N] [Nonempty N],
      InfSentence.Realize σ N ↔ InfSentence.Realize τ N := by
  sorry

end FirstOrder.Language
