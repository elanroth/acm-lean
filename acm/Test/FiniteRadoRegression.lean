import Lib.BackForth.HeightRado
import Lib.BackForth.FilteredBasis

/-!
# Finite Rado regression tests

These compile-time checks pin both directions of the independent-transversal
criterion used in the finite height--Rado proof.
-/

noncomputable section

open Set Submodule Module

universe u v w x y

variable {K : Type u} {V : Type v} {ι : Type w}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [Fintype ι] [FiniteDimensional K V]

/-- The packaged theorem is the exact finite linear Rado equivalence. -/
example (D : ι → Set V) :
    FiniteRado.HasIndependentTransversal (K := K) D ↔
      FiniteRado.Condition (K := K) D :=
  FiniteRado.finite_linear_rado D

/-- Necessity is independently exposed for restricted index finsets. -/
example (D : ι → Set V) (s : Finset ι)
    (h : FiniteRado.HasIndependentTransversalOn (K := K) D s) :
    FiniteRado.ConditionOn (K := K) D s :=
  FiniteRado.conditionOn_of_hasIndependentTransversalOn h

/-- Sufficiency is independently exposed for restricted index finsets. -/
example (D : ι → Set V) (s : Finset ι)
    (h : FiniteRado.ConditionOn (K := K) D s) :
    FiniteRado.HasIndependentTransversalOn (K := K) D s :=
  FiniteRado.hasIndependentTransversalOn_of_conditionOn h

variable {Q : Type x} [AddCommGroup Q] [Module K Q]
variable [SMulCommClass K K V]

/-- Rado's selector is exactly an injective linear realization of the access
sets on any fixed source basis. -/
example (b : Basis ι K Q) (D : ι → Set V) :
    FiniteRado.HasInjectiveRealization b D ↔
      FiniteRado.Condition (K := K) D :=
  FiniteRado.hasInjectiveRealization_iff b D

variable {Λ : Type y} [LinearOrder Λ]
variable [FiniteDimensional K Q]

/-- The abstract D-22 assembly theorem turns the kernel-room inequalities
for a compatible reach basis into an injective affine access realization. -/
example (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : HeightRado.CompatibleWithReach b r X)
    (hbudget : ∀ β, Module.finrank K
        (LinearMap.ker (HeightRado.residueMap Φ X Z β)) ≤
      Module.finrank K (Z β)) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess Φ Z b r) :=
  HeightRado.hasInjectiveRealization_affineAccess
    Φ X Z b r hcompat hbudget

/-- The completed finite-dimensional Height--Rado criterion is an iff, not
only a sufficient matching lemma. -/
example (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : HeightRado.CompatibleWithReach b r X)
    (hZ : Antitone Z) :
    FiniteRado.HasInjectiveRealization b
        (HeightRado.affineAccess Φ Z b r) ↔
      ∀ β, Module.finrank K
        (LinearMap.ker (HeightRado.residueMap Φ X Z β)) ≤
          Module.finrank K (Z β) :=
  HeightRado.hasInjectiveRealization_affineAccess_iff
    Φ X Z b r hcompat hZ

/-- A finite increasing filtration admits one basis set with a spanning subset
at every level. -/
example (X : ℕ → Submodule K V) (hX : Monotone X) (n : ℕ)
    (hTop : X n = ⊤) :
    ∃ b : Set V,
      LinearIndepOn K id b ∧
      span K b = ⊤ ∧
      ∀ k ≤ n, ∃ c : Set V, c ⊆ b ∧ span K c = X k :=
  FilteredBasis.exists_basis_set X hX n hTop

/-- The filtration result is also packaged as an actual finitely indexed
basis, ready for the Height--Rado access construction. -/
example (X : ℕ → Submodule K V) (hX : Monotone X) (n : ℕ)
    (hTop : X n = ⊤) :
    ∃ (s : Set V) (b : Basis s K V),
      Finite s ∧
      ∀ k ≤ n, ∃ I : Set s, span K (b '' I) = X k :=
  FilteredBasis.exists_compatible_basis X hX n hTop
