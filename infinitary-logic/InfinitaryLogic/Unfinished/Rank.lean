/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Scott Ranks

This file defines three notions of Scott rank for countable structures, measuring
the complexity of formulas needed to distinguish tuples up to automorphism.

## Main Definitions

- `tupleRank` — `p(ā)`: the least ordinal α such that Π_α formulas distinguish ā from
  all non-automorphically-equivalent tuples.
- `scottRank_r` — `r(A)`: the least α such that Π_α formulas distinguish all tuples.
- `scottRank_R` — `R(A)`: the supremum of tuple ranks `p(ā)` over all tuples ā.
- `scottRank_SR` — `SR(A)`: based on symmetric back-and-forth equivalence relations.

## Key Theorems

- `scottRank_r_le_scottRank_R` — `r(A) ≤ R(A)`.
- `scottRank_R_le_succ_scottRank_r` — `R(A) ≤ r(A) + 1`.
- `scottFamily_of_rank` — structures of rank α have Π_α Scott families (Prop 6.9).

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Section 6.7.
-/

import InfinitaryLogic.Unfinished.ScottFamily

universe u v

namespace FirstOrder.Language

variable (L : Language.{u, v})

open InfBoundedFormula

/-! ### Back-and-forth equivalence relations -/

/-- Two tuples ā in M and b̄ in N are **α-back-and-forth equivalent** if they satisfy
the same Π_α formulas. This is defined for all ordinals α.

At level 0: ā ~₀ b̄ iff they satisfy the same quantifier-free formulas.
At level α > 0: ā ~_α b̄ iff for all β < α,
  (forth) for all m ∈ M, ∃ n ∈ N such that (ā,m) ~_β (b̄,n),
  (back)  for all n ∈ N, ∃ m ∈ M such that (ā,m) ~_β (b̄,n).

The α-back-and-forth relations are the "asymmetric" version used by Ash and Knight,
as opposed to Scott's symmetric version. -/
noncomputable def backForthEquiv (o : Ordinal.{0})
    {k : ℕ} {M N : Type*} [L.Structure M] [L.Structure N]
    (v : Fin k → M) (w : Fin k → N) : Prop :=
  ∀ ψ : @LOmegaOneBoundedFormula.{u, v, 0} L PEmpty k,
    InfBoundedFormula.IsPi o ψ → (ψ.Realize PEmpty.elim v ↔ ψ.Realize PEmpty.elim w)

/-- Symmetric back-and-forth equivalence on a single structure,
as used in the definition of SR(A). -/
noncomputable def symBackForthEquiv (o : Ordinal.{0})
    {k : ℕ} {M : Type*} [L.Structure M]
    (v w : Fin k → M) : Prop :=
  backForthEquiv L o v w ∧ backForthEquiv L o w v

variable {L}

/-! ### Tuple rank -/

/-- The **tuple rank** `p(ā)` of a tuple ā in a countable structure M is the least
ordinal β such that for all tuples b̄ of the same length, if all Π_β formulas true
of ā are true of b̄, then all L_{ω₁,ω} formulas true of ā are true of b̄.

Equivalently, p(ā) is the least level at which the Π hierarchy stabilizes for ā. -/
noncomputable def tupleRank {M : Type*} [L.Structure M] [Countable M]
    {k : ℕ} (v : Fin k → M) : Ordinal.{0} :=
  sInf {β : Ordinal | ∀ (w : Fin k → M),
    backForthEquiv L β v w →
    ∀ ψ : @LOmegaOneBoundedFormula.{u, v, 0} L PEmpty k,
      @InfBoundedFormula.IsLOmegaOne.{u, v, 0} L PEmpty k ψ →
      (ψ.Realize PEmpty.elim v → ψ.Realize PEmpty.elim w)}

/-! ### Structure ranks -/

/-- **Scott rank r(A)**: the least ordinal α such that Π_α formulas separate
all non-automorphically-equivalent tuples in A.

Formally, r(A) is the least α such that for all tuples ā, b̄ of the same length,
if they satisfy the same Π_α formulas, then they satisfy the same L_{ω₁,ω} formulas. -/
noncomputable def scottRank_r (M : Type*) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal | ∀ (k : ℕ) (v w : Fin k → M),
    backForthEquiv L α v w →
    ∀ ψ : @LOmegaOneBoundedFormula.{u, v, 0} L PEmpty k,
      @InfBoundedFormula.IsLOmegaOne.{u, v, 0} L PEmpty k ψ →
      (ψ.Realize PEmpty.elim v → ψ.Realize PEmpty.elim w)}

/-- **Scott rank R(A)**: the supremum of tuple ranks p(ā) over all finite tuples ā in A.

R(A) = sup { p(ā) + 1 : ā ∈ A^{<ω} }

Note: R(A) is defined as the least ordinal strictly greater than all tuple ranks,
not as their supremum. -/
noncomputable def scottRank_R (M : Type*) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sSup {Order.succ (tupleRank (L := L) v) | (k : ℕ) (v : Fin k → M)}

/-- **Scott rank SR(A)**: based on Scott's symmetric back-and-forth equivalence relations.

SR(A) is the least ordinal α such that for all tuples ā, b̄, if ā ~^sym_α b̄
then ā and b̄ are in the same automorphism orbit.

This is the most commonly studied notion of Scott rank in the literature. -/
noncomputable def scottRank_SR (M : Type*) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal | ∀ (k : ℕ) (v w : Fin k → M),
    symBackForthEquiv L α v w →
    ∃ σ : M ≃[L] M, ∀ i, σ (v i) = w i}

/-! ### Relationships between ranks (Proposition 6.8) -/

/-- The three Scott ranks are always countable for countable structures. -/
theorem scottRank_r_lt_omega1 (M : Type*) [L.Structure M] [Countable M] [Nonempty M] :
    scottRank_r (L := L) M < omegaOne := by
  sorry

theorem scottRank_R_lt_omega1 (M : Type*) [L.Structure M] [Countable M] [Nonempty M] :
    scottRank_R (L := L) M < omegaOne := by
  sorry

theorem scottRank_SR_lt_omega1 (M : Type*) [L.Structure M] [Countable M] [Nonempty M] :
    scottRank_SR (L := L) M < omegaOne := by
  sorry

/-- **Proposition 6.8**: The ranks r(A) and R(A) are close together.
Specifically, r(A) ≤ R(A). -/
theorem scottRank_r_le_scottRank_R (M : Type*) [L.Structure M] [Countable M] :
    scottRank_r (L := L) M ≤ scottRank_R (L := L) M := by
  sorry

/-- **Proposition 6.8**: If p(ā) = r(A) for some tuple ā, then R(A) = r(A) + 1;
otherwise R(A) = r(A). In either case, R(A) ≤ r(A) + 1. -/
theorem scottRank_R_le_succ_scottRank_r (M : Type*) [L.Structure M] [Countable M] :
    scottRank_R (L := L) M ≤ Order.succ (scottRank_r (L := L) M) := by
  sorry

/-- SR(A) ≤ R(A). -/
theorem scottRank_SR_le_scottRank_R (M : Type*) [L.Structure M] [Countable M] :
    scottRank_SR (L := L) M ≤ scottRank_R (L := L) M := by
  sorry


end FirstOrder.Language
