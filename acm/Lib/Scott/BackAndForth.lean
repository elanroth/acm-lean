import Lib.Scott.Tuples
import Lib.BackForth.Characterization

/-!
# Algebraic back-and-forth for Scott complexity of reduced abelian p-groups

This file connects the current algebraic BF packages to the Scott complexity
layer. The `ScottBFRel` is the back-and-forth
relation whose quantifier complexity determines the Scott sentence complexity.

The three exact characterization theorems connect `ScottBFRel` to their
corresponding algebraic conditions.  The crossed even package remains only an
internal strong sufficient condition.

The parameter shapes are:
- Odd (γ = 2α+1): `AlgBFOddCond`
- Even (γ = 2α+2): `AlgBFEvenExactCond`
- Limit (relation level `α`, algebraic cutoff `ω·α`): `AlgBFLimitCond`
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
variable {n : ℕ}

/-- Scott-side algebraic back-and-forth relation at ordinal level γ.
    This is the relation whose definability complexity determines the
    Scott sentence complexity. -/
def ScottBFRel (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (γ : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  BFRel p γ n a b

/-- Odd-case characterization: ScottBFRel at level 2α+1 is equivalent
    to the algebraic odd conditions. -/
theorem ScottBFRel_eq_odd [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    ScottBFRel p hG hH (2 * α + 1) a b ↔ AlgBFOddCond p hG hH α a b :=
  bf_odd_iff_algebraic p hG hH α a b

/-- Exact even-case characterization at level `2α+2`. -/
theorem ScottBFRel_eq_even [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    ScottBFRel p hG hH (2 * α + 2) a b ↔
      AlgBFEvenExactCond p hG hH α a b :=
  bf_even_iff_algebraic p hG hH α a b

/-- The crossed package remains available under an explicitly strong name. -/
theorem ScottBFRel_of_strong_even [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    AlgBFEvenStrongCond p hG hH α a b →
      ScottBFRel p hG hH (2 * α + 2) a b :=
  bf_even_of_strong_algebraic p hG hH α a b

/-- Limit-case characterization.  The level is `α` itself, for `α` a limit or
zero, while the clauses are measured at `ω·α` -- this is part 3 of the theorem of
record, and the previous statement at level `ω·α` did not match it. -/
theorem ScottBFRel_eq_limit [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (hα : Order.IsSuccLimit α ∨ α = 0)
    (a : Fin n → G) (b : Fin n → H) :
    ScottBFRel p hG hH α a b ↔ AlgBFLimitCond p hG hH α a b :=
  bf_limit_iff_algebraic p hG hH α hα a b
