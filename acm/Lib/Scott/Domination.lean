import Lib.Scott.AlgebraicTail

/-!
# Domination conditions for finite tails

This module collects the domination predicates used in the algebraic
back-and-forth analysis.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

section FiniteDomination

variable {C D : Type u} [AddCommGroup C] [AddCommGroup D]

/-- Cumulative domination of `C` by `D` via socle dimensions. -/
def CumulativeDom : Prop :=
  ∀ k : ℕ, socleDim p (G := C) k ≤ socleDim p (G := D) k

/-- Pointwise domination of `C` by `D` via Ulm invariants. -/
def PointwiseDom : Prop :=
  ∀ i : ℕ, ulmInvariant p (i : Ordinal.{0}) (G := C) ≤ ulmInvariant p (i : Ordinal.{0}) (G := D)

/-- Adjusted socle domination relative to chosen subgroups. -/
def AdjustedSocleDomination (F : AddSubgroup C) (E : AddSubgroup D) : Prop :=
  ∀ k : ℕ,
    socleDim p (G := C) k + ambientSocleDim p E k ≤
      socleDim p (G := D) k + ambientSocleDim p F k

end FiniteDomination

section TailDomination

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]

/-- Tail cumulative domination at base level `ω·γ`. -/
def TailCumulativeDom (γ : Ordinal) : Prop :=
  ∀ k : ℕ, tailSum p (G := H) γ k ≤ tailSum p (G := G) γ k

/-- Tail pointwise domination at base level `ω·γ`. -/
def TailPointwiseDom (γ : Ordinal) : Prop :=
  ∀ i : ℕ, tailInvariant p (G := H) γ i ≤ tailInvariant p (G := G) γ i

/-- Relative tail cumulative domination. -/
def RelativeTailCumulativeDom (γ : Ordinal) (C : AddSubgroup H) (D : AddSubgroup G) : Prop :=
  ∀ k : ℕ, tailRelSum p (G := H) γ C k ≤ tailRelSum p (G := G) γ D k

/-- Relative tail pointwise domination. -/
def RelativeTailPointwiseDom (γ : Ordinal) (C : AddSubgroup H) (D : AddSubgroup G) : Prop :=
  ∀ i : ℕ, tailRelInvariant p (G := H) γ C i ≤ tailRelInvariant p (G := G) γ D i

lemma pointwise_imp_cumulative (γ : Ordinal) :
    TailPointwiseDom p (G := G) (H := H) γ → TailCumulativeDom p (G := G) (H := H) γ := by
  intro h k
  unfold TailPointwiseDom at h
  simpa [tailSum] using
    Cardinal.sum_le_sum
      (fun i : ℕ => tailInvariant p (G := H) γ (i + k))
      (fun i : ℕ => tailInvariant p (G := G) γ (i + k))
      (fun i => h (i + k))

lemma relPointwise_imp_relCumulative (γ : Ordinal) (C : AddSubgroup H) (D : AddSubgroup G) :
    RelativeTailPointwiseDom p (G := G) (H := H) γ C D →
      RelativeTailCumulativeDom p (G := G) (H := H) γ C D := by
  intro h k
  unfold RelativeTailPointwiseDom at h
  simpa [tailRelSum] using
    Cardinal.sum_le_sum
      (fun i : ℕ => tailRelInvariant p (G := H) γ C (i + k))
      (fun i : ℕ => tailRelInvariant p (G := G) γ D (i + k))
      (fun i => h (i + k))

end TailDomination
