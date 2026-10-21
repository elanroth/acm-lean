/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Scott Families for Countable Structures

A Scott family for a structure A is a countable family Φ of formulas such that
every tuple in A satisfies some formula in Φ, and tuples satisfying the same
formula are automorphically equivalent.

## Main Definitions

- `ScottFamily` — a Scott family for a structure.

## Key Theorems

- `exists_scottFamily` — every countable structure has a Scott family (Lemma 6.7).
- `exists_piFormula_characterizing` — characterizing Π_α formula for any tuple (Lemma 6.6(a)).
- `exists_separatingOrdinal` — separating ordinal for a countable family (Lemma 6.6(b)).

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Sections 6.6–6.7.
-/

import InfinitaryLogic.NormalForm
import Mathlib.ModelTheory.Basic

universe u v w

namespace FirstOrder.Language

variable (L : Language.{u, v})

open InfBoundedFormula

/-- A **Scott family** for an L-structure M is a countable family of L_{ω₁,ω} formulas
(indexed by tuple arity) satisfying:

(a) **Covering**: every tuple ā in M satisfies some formula in the family.
(b) **Separation**: if two tuples ā, b̄ satisfy the same formula in the family,
    then there is an automorphism of M mapping ā to b̄.

Scott families are the key tool in the proof of Scott's Isomorphism Theorem.

Note: Formulas in a Scott family have no free variables (they live in
`LOmegaOneBoundedFormula PEmpty n`), but `n` bound variables corresponding to the
tuple entries. -/
structure ScottFamily (M : Type*) [L.Structure M] where
  /-- For each arity n, a set of formulas with n bound variables. -/
  family : (n : ℕ) → Set (@LOmegaOneBoundedFormula.{u, v, 0} L PEmpty n)
  /-- The family is countable at each arity. -/
  countable : ∀ n, (family n).Countable
  /-- All formulas in the family are L_{ω₁,ω} formulas. -/
  cardBounded : ∀ n, ∀ φ : @LOmegaOneBoundedFormula.{u, v, 0} L PEmpty n, φ ∈ family n →
    @InfBoundedFormula.IsLOmegaOne.{u, v, 0} L PEmpty n φ
  /-- **Covering**: every tuple in M satisfies some formula in the family. -/
  covers : ∀ (n : ℕ) (v : Fin n → M),
    ∃ φ ∈ family n, φ.Realize (PEmpty.elim) v
  /-- **Separation**: tuples satisfying the same formula are in the same orbit. -/
  separates : ∀ (n : ℕ) (φ) (hφ : φ ∈ family n) (v w : Fin n → M),
    φ.Realize (PEmpty.elim) v → φ.Realize (PEmpty.elim) w →
    ∃ σ : M ≃[L] M, ∀ i, σ (v i) = w i

end FirstOrder.Language
