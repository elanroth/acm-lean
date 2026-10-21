import Lib.Scott.BackAndForth
import Lib.Scott.Domination

/-!
# Scott-complexity target templates

This module records the sentence-template targets from the March 18 draft,
organized around five tail cases for groups of length `ω·γ + n`.

It intentionally does not define an "optimal Scott complexity". The current
library has no infinitary-formula syntax, satisfaction relation, or minimality
predicate from which such an object could be constructed. The exact algebraic
back-and-forth characterization is exposed below as the proved input for that
future logic layer; the templates remain bookkeeping, not asserted upper or
lower bounds.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- The two Scott-sentence complexity flavors tracked by the draft. -/
inductive ScottFlavor
  | pi
  | dSigma
  deriving DecidableEq, Repr

/-- A lightweight record for a target sentence class. -/
structure ScottSentenceTemplate where
  base : Ordinal
  flavor : ScottFlavor
  index : ℕ

/-- The finite tail below the top nonzero Ulm level is pointwise finite. -/
def TailAllFinite {G : Type u} [AddCommGroup G] (γ : Ordinal) (n : ℕ) : Prop :=
  ∀ k : Fin n, tailInvariant p (G := G) γ k.1 < ℵ₀

/-- Exactly one tail Ulm invariant is infinite. -/
def TailUniqueInfinite {G : Type u} [AddCommGroup G] (γ : Ordinal) (n : ℕ) : Prop :=
  ∃! k : Fin n, ℵ₀ ≤ tailInvariant p (G := G) γ k.1

/-- All tail levels strictly below a chosen index are zero. -/
def TailZeroBelow {G : Type u} [AddCommGroup G] (γ : Ordinal) (k : ℕ) : Prop :=
  ∀ i : ℕ, i < k → tailInvariant p (G := G) γ i = 0

/-- All tail levels strictly below a chosen index are finite but not all zero. -/
def TailFiniteNonzeroBelow {G : Type u} [AddCommGroup G] (γ : Ordinal) (k : ℕ) : Prop :=
  (∀ i : ℕ, i < k → tailInvariant p (G := G) γ i < ℵ₀) ∧
    ∃ i : ℕ, i < k ∧ tailInvariant p (G := G) γ i ≠ 0

/-- At least two tail Ulm invariants are infinite. -/
def TailAtLeastTwoInfinite {G : Type u} [AddCommGroup G] (γ : Ordinal) (n : ℕ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ℵ₀ ≤ tailInvariant p (G := G) γ i.1 ∧
    ℵ₀ ≤ tailInvariant p (G := G) γ j.1

/-- Draft target for the all-finite successor-tail case. -/
def scottSentence_allFinite (γ : Ordinal) (n : ℕ) : ScottSentenceTemplate :=
  ⟨γ, ScottFlavor.dSigma, 2 * n + 1⟩

/-- Draft target for the unique-infinite-tail, zeros-below case. -/
def scottSentence_uniqueInfinite_zeroBelow (γ : Ordinal) (n : ℕ) :
    ScottSentenceTemplate :=
  ⟨γ, ScottFlavor.pi, 2 * n + 2⟩

/-- Draft target for the unique-infinite-tail, finite-nonzero-below case. -/
def scottSentence_uniqueInfinite_finiteBelow (γ : Ordinal) (n : ℕ) :
    ScottSentenceTemplate :=
  ⟨γ, ScottFlavor.dSigma, 2 * n + 2⟩

/-- Draft target for the case of at least two infinite tail invariants. -/
def scottSentence_twoInfinite (γ : Ordinal) (n : ℕ) : ScottSentenceTemplate :=
  ⟨γ, ScottFlavor.pi, 2 * n + 3⟩

/-- Draft target for the limit-length case. -/
def scottSentence_limit (γ : Ordinal) : ScottSentenceTemplate :=
  ⟨γ, ScottFlavor.pi, 1⟩

@[simp] theorem scottSentence_allFinite_flavor (γ : Ordinal) (n : ℕ) :
    (scottSentence_allFinite γ n).flavor = ScottFlavor.dSigma := rfl

@[simp] theorem scottSentence_allFinite_index (γ : Ordinal) (n : ℕ) :
    (scottSentence_allFinite γ n).index = 2 * n + 1 := rfl

@[simp] theorem scottSentence_uniqueInfinite_zeroBelow_flavor (γ : Ordinal) (n : ℕ) :
    (scottSentence_uniqueInfinite_zeroBelow γ n).flavor = ScottFlavor.pi := rfl

@[simp] theorem scottSentence_uniqueInfinite_zeroBelow_index (γ : Ordinal) (n : ℕ) :
    (scottSentence_uniqueInfinite_zeroBelow γ n).index = 2 * n + 2 := rfl

@[simp] theorem scottSentence_uniqueInfinite_finiteBelow_flavor (γ : Ordinal) (n : ℕ) :
    (scottSentence_uniqueInfinite_finiteBelow γ n).flavor = ScottFlavor.dSigma := rfl

@[simp] theorem scottSentence_uniqueInfinite_finiteBelow_index (γ : Ordinal) (n : ℕ) :
    (scottSentence_uniqueInfinite_finiteBelow γ n).index = 2 * n + 2 := rfl

@[simp] theorem scottSentence_twoInfinite_flavor (γ : Ordinal) (n : ℕ) :
    (scottSentence_twoInfinite γ n).flavor = ScottFlavor.pi := rfl

@[simp] theorem scottSentence_twoInfinite_index (γ : Ordinal) (n : ℕ) :
    (scottSentence_twoInfinite γ n).index = 2 * n + 3 := rfl

@[simp] theorem scottSentence_limit_flavor (γ : Ordinal) :
    (scottSentence_limit γ).flavor = ScottFlavor.pi := rfl

@[simp] theorem scottSentence_limit_index (γ : Ordinal) :
    (scottSentence_limit γ).index = 1 := rfl

/-- The five syntactic targets tracked by the draft at one block and tail
length. This is a catalog only: proving that a target is realized and optimal
requires the future infinitary-formula layer. -/
structure ScottClassificationTargets where
  limit : ScottSentenceTemplate
  allFinite : ScottSentenceTemplate
  uniqueInfiniteZeroBelow : ScottSentenceTemplate
  uniqueInfiniteFiniteBelow : ScottSentenceTemplate
  twoInfinite : ScottSentenceTemplate

/-- Assemble the five draft targets without making an optimality claim. -/
def scottClassificationTargets (γ : Ordinal) (n : ℕ) :
    ScottClassificationTargets where
  limit := scottSentence_limit γ
  allFinite := scottSentence_allFinite γ n
  uniqueInfiniteZeroBelow := scottSentence_uniqueInfinite_zeroBelow γ n
  uniqueInfiniteFiniteBelow := scottSentence_uniqueInfinite_finiteBelow γ n
  twoInfinite := scottSentence_twoInfinite γ n

/-- The exact algebraic characterization at every literal relation rank is the
proved input available to a future Scott-formula complexity development. -/
theorem scottBackAndForth_characterization (ξ : Ordinal.{0}) :
    ACMCharacterizationAtRank p ξ :=
  acmCharacterizationAtRank p ξ
