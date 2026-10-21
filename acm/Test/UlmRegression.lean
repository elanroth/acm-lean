import Lib.Ulm.Theorem
import Lib.BackForth.Algebraic

/-!
# Ulm specification regressions

These checks protect the distinctions that the original Ulm scaffold collapsed:

* primary is not the same property as reduced or separable;
* the public `IsReducedPGroup` bundle carries primaryity explicitly;
* an `H_(ω+1)`-shaped group, with a nonzero `G_ω` layer but
  `G_(ω+1) = 0`, is reduced and nonseparable;
* finite back-and-forth stages carry actual partial isomorphisms, so codomain
  membership cannot be mistaken for image coverage.
-/

example : ¬ IsPrimaryPGroup 2 ℤ := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  have hpow : (2 ^ n : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn' : (2 ^ n : ℤ) = 0 := by simpa using hn
  apply hpow
  exact_mod_cast hn'

example {p : ℕ} {G : Type*} [AddCommGroup G]
    (h : IsReducedPGroup p G) : IsPrimaryPGroup p G :=
  h.primary

/-- The defining filtration profile of the generalized Prüfer group
`H_(ω+1)` is a semantic regression against collapsing reducedness back to
separability: its nonzero `ω`-layer survives, while the successor layer is zero. -/
example {p : ℕ} [Fact p.Prime] {G : Type*} [AddCommGroup G]
    (hprimary : IsPrimaryPGroup p G)
    (hωsucc : ulmSubgroup p (Order.succ (Ordinal.omega0 : Ordinal.{0})) (G := G) = ⊥)
    (x : G) (hxω : x ∈ ulmSubgroup p (Ordinal.omega0 : Ordinal.{0})) (hx0 : x ≠ 0) :
    IsReducedPGroup p G ∧ ¬ IsPSeparable p G := by
  constructor
  · exact ⟨hprimary, ⟨Order.succ (Ordinal.omega0 : Ordinal.{0}), hωsucc⟩⟩
  · intro hseparable
    apply hx0
    apply hseparable x
    intro n
    have hxn : x ∈ ulmSubgroup p (n : Ordinal) :=
      ulmSubgroup_antitone p (Ordinal.natCast_lt_omega0 n).le hxω
    exact (mem_ulmSubgroup_nat_iff p n x).mp hxn

universe u

example {p : ℕ} {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (s : UlmStage p (G := G) (H := H)) : Function.Surjective s.e :=
  s.e.surjective

example {p : ℕ} {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (s : UlmStage p (G := G) (H := H)) :
    Set.Finite (s.A : Set G) ∧ Set.Finite (s.B : Set H) :=
  ⟨s.hAfinite, s.hBfinite⟩

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (a : Fin n → G) (b : Fin n → H) :
    BFBase p n a b ↔
      ∃ φ : AddSubgroup.closure (Set.range a) ≃+
          AddSubgroup.closure (Set.range b),
        ∀ i : Fin n,
          φ ⟨a i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
            ⟨b i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩ :=
  Iff.rfl

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H} (g : TupleIsoMap a b) :
    g.symm.equiv = g.equiv.symm :=
  TupleIsoMap.symm_equiv g

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (a : Fin n → G) (b : Fin n → H) :
    BFRel p 0 n a b ↔ BFBase p n a b :=
  BFRel_zero p n a b

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    BFRel p (Order.succ α) n a b ↔
      ∀ (m : ℕ) (c : Fin m → H), ∃ d : Fin m → G,
        BFRelReverse p α (n + m) (Fin.append b c) (Fin.append a d) :=
  BFRel_succ p α n a b

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (α : Ordinal.{0}) (b : Fin n → H) (a : Fin n → G) :
    BFRelReverse p (Order.succ α) n b a ↔
      ∀ (m : ℕ) (d : Fin m → G), ∃ c : Fin m → H,
        BFRel p α (n + m) (Fin.append a d) (Fin.append b c) :=
  BFRelReverse_succ p α n b a

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (o : Ordinal.{0}) (ho : Order.IsSuccLimit o)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p o n a b ↔ ∀ β (_hβ : β < o), BFRel p β n a b :=
  BFRel_limit p o ho n a b

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (o : Ordinal.{0}) (ho : Order.IsSuccLimit o)
    (b : Fin n → H) (a : Fin n → G) :
    BFRelReverse p o n b a ↔
      ∀ β (_hβ : β < o), BFRelReverse p β n b a :=
  BFRelReverse_limit p o ho n b a

example {p : ℕ} [Fact p.Prime] {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (α : Ordinal.{0}) (b : Fin n → H) (a : Fin n → G) :
    BFRelReverse p α n b a ↔
      BFRel (G := H) (H := G) p α n b a :=
  BFRelReverse_iff_BFRel_swap p α n b a

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (α : Ordinal.{0}) :
    hillInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) :=
  hillInvariant_bot p α

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    hillInvariant p S α +
        Module.rank (ZMod p) (overhangSubmodule p S α) =
      markedGradedInvariant p S α :=
  hillInvariant_add_overhangInvariant p S α

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    relativeUlmInvariant p S α = hillInvariant p S α :=
  rfl

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    hillDen p S α =
      (pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))).comap
        (pSocleAt p α).subtype :=
  rfl

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    markedGradedDen p S α =
      (pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)).comap
        (pSocleAt p α).subtype :=
  rfl

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (α : Ordinal.{0}) (k : ℕ) :
    InfiniteAtLevel p (G := G) α k ↔
      Set.Infinite (pSocleAt p (Ordinal.omega0 * α + k) (G := G) : Set G) :=
  by simp [InfiniteAtLevel]

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (α : Ordinal.{0}) (k : ℕ) :
    FiniteAtLevel p (G := G) α k ↔
      Set.Finite (pSocleAt p (Ordinal.omega0 * α + k) (G := G) : Set G) :=
  by simp [FiniteAtLevel]

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    relativeUlmInvariant p S α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p S α) =
      ulmInvariant p α (G := G) :=
  relativeUlmInvariant_add_occupiedInvariant p S α

example {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]
    (hG : IsReducedPGroup p G) {x : G} (hx0 : x ≠ 0) :
    ∃ α : Ordinal.{0},
      x ∈ ulmSubgroup p α ∧ x ∉ ulmSubgroup p (Order.succ α) :=
  exists_ulmHeight_eq_of_ne_zero (p := p) hG hx0

/-- A forth extension needs reducedness only on its source; target reducedness
is supplied separately when the theorem is used in the back direction. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hG : IsReducedPGroup p G)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a :=
  kaplansky_extend (p := p) hG hinv s g
