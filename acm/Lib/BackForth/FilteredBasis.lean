import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bases compatible with a finite filtration

The height--Rado argument needs a basis which simultaneously spans every
member of a finite nested filtration by a subset.  This file constructs that
basis set by repeatedly extending a linearly independent spanning set inside
the next subspace.
-/

noncomputable section

open Function Module Set Submodule

universe u v

namespace FilteredBasis

variable {K : Type u} {V : Type v}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Up to any finite stage of an increasing filtration, there is one linearly
independent set spanning the last subspace and containing a spanning subset
for every earlier subspace. -/
theorem exists_compatible_set (X : ℕ → Submodule K V) (hX : Monotone X)
    (n : ℕ) :
    ∃ b : Set V,
      b ⊆ X n ∧
      LinearIndepOn K id b ∧
      span K b = X n ∧
      ∀ k ≤ n, ∃ c : Set V, c ⊆ b ∧ span K c = X k := by
  induction n with
  | zero =>
      obtain ⟨b, hbX, hbspan, hbind⟩ :=
        exists_linearIndependent K (X 0 : Set V)
      have hbspan' : span K b = X 0 := by
        simpa using hbspan
      refine ⟨b, hbX, ?_, hbspan', ?_⟩
      · exact linearIndependent_subtype_iff.mp hbind
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        exact ⟨b, subset_rfl, hbspan'⟩
  | succ n ih =>
      obtain ⟨b, hbX, hbind, hbspan, hbcompat⟩ := ih
      have hbXsucc : b ⊆ X (n + 1) :=
        hbX.trans (SetLike.coe_mono (hX (Nat.le_succ n)))
      obtain ⟨b', hb'X, hbb', hXspan, hb'ind⟩ :=
        exists_linearIndepOn_id_extension hbind hbXsucc
      have hb'span : span K b' = X (n + 1) := by
        apply le_antisymm
        · exact span_le.mpr hb'X
        · intro x hx
          exact hXspan hx
      refine ⟨b', hb'X, hb'ind, hb'span, ?_⟩
      intro k hk
      rcases eq_or_lt_of_le hk with hkn | hkn
      · subst k
        exact ⟨b', subset_rfl, hb'span⟩
      · obtain ⟨c, hcb, hcspan⟩ := hbcompat k (Nat.le_of_lt_succ hkn)
        exact ⟨c, hcb.trans hbb', hcspan⟩

/-- If the final filtration member is the whole space, the compatible set is
a basis set of the ambient space. -/
theorem exists_basis_set (X : ℕ → Submodule K V) (hX : Monotone X)
    (n : ℕ) (hTop : X n = ⊤) :
    ∃ b : Set V,
      LinearIndepOn K id b ∧
      span K b = ⊤ ∧
      ∀ k ≤ n, ∃ c : Set V, c ⊆ b ∧ span K c = X k := by
  obtain ⟨b, -, hbind, hbspan, hbcompat⟩ :=
    exists_compatible_set X hX n
  exact ⟨b, hbind, hbspan.trans hTop, hbcompat⟩

/-- A finite increasing filtration ending at the whole space admits an actual
basis whose suitable subfamilies span every filtration level.  The index type
is finite when the ambient space is finite-dimensional. -/
theorem exists_compatible_basis [FiniteDimensional K V]
    (X : ℕ → Submodule K V) (hX : Monotone X)
    (n : ℕ) (hTop : X n = ⊤) :
    ∃ (s : Set V) (b : Basis s K V),
      Finite s ∧
      ∀ k ≤ n, ∃ I : Set s, span K (b '' I) = X k := by
  obtain ⟨s, hsli, hsspan, hscompat⟩ :=
    exists_basis_set X hX n hTop
  have hli : LinearIndependent K (Subtype.val : s → V) :=
    linearIndependent_subtype_iff.mpr hsli
  have hrange : Set.range (Subtype.val : s → V) = s := by
    ext x
    simp
  have hsp : ⊤ ≤ span K (Set.range (Subtype.val : s → V)) := by
    rw [hrange, hsspan]
  let b : Basis s K V := Basis.mk hli hsp
  refine ⟨s, b, hli.finite, ?_⟩
  intro k hk
  obtain ⟨c, hcs, hcspan⟩ := hscompat k hk
  let I : Set s := {i | (i : V) ∈ c}
  refine ⟨I, ?_⟩
  have himage : b '' I = c := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa [b, I] using hi
    · intro hx
      let i : s := ⟨x, hcs hx⟩
      refine ⟨i, ?_, ?_⟩
      · exact hx
      · simp [b, i]
  rw [himage, hcspan]

end FilteredBasis
