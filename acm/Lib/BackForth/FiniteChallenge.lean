import Lib.BackForth.FiniteEmbedding

/-!
# Finite challenges with ambient Ulm heights

This file localizes the finite marked-embedding construction to a finite
subgroup `D` of a possibly infinite ambient source `B`.  The finite source
space is the image of `D ∩ P₀(B)` in the ambient room `R_{B,F}(0)`.  Its reach
filtration is pulled back from the ambient reachable filtration, so no
intrinsic subgroup height is introduced.
-/

noncomputable section

open Module Ordinal

universe u v

variable (p : ℕ) [hp : Fact p.Prime]

namespace FiniteChallenge

section SourceSpace

variable {B : Type u} [AddCommGroup B]

/-- The order-`p` elements of the finite challenge `D`, kept as a subspace of
the ambient socle `P₀(B)`. -/
noncomputable def challengeSocle (D : AddSubgroup B) :
    Submodule (ZMod p) (pSocleAt p (0 : Ordinal.{0}) (G := B)) :=
  AddSubgroup.toZModSubmodule p
    (D.comap (pSocleAt p (0 : Ordinal.{0}) (G := B)).subtype)

/-- Map the challenge socle into the ambient marked room. -/
noncomputable def challengeToRoom (F D : AddSubgroup B) :
    challengeSocle p D →ₗ[ZMod p] room p F 0 :=
  (roomSubmodule p F 0).mkQ.comp (challengeSocle p D).subtype

/-- The finite challenge quotient, realized as its concrete image inside the
ambient height-zero room. -/
noncomputable def challengeRoom (F D : AddSubgroup B) :
    Submodule (ZMod p) (room p F 0) :=
  LinearMap.range (challengeToRoom p F D)

/-- The quotient map from the actual challenge socle onto its concrete room. -/
noncomputable def challengeQuotientMap (F D : AddSubgroup B) :
    challengeSocle p D →ₗ[ZMod p] challengeRoom p F D :=
  (challengeToRoom p F D).rangeRestrict

theorem challengeQuotientMap_surjective (F D : AddSubgroup B) :
    Function.Surjective (challengeQuotientMap p F D) := by
  rintro ⟨q, x, rfl⟩
  exact ⟨x, rfl⟩

/-- Pull back the ambient reachable filtration to the finite challenge room.
This is the source filtration used by the local Height--Rado theorem. -/
noncomputable def challengeReach (F D : AddSubgroup B) (β : Ordinal.{0}) :
    Submodule (ZMod p) (challengeRoom p F D) :=
  (reachableSubspace p F β).comap (challengeRoom p F D).subtype

theorem challengeReach_antitone (F D : AddSubgroup B) :
    Antitone (challengeReach p F D) := by
  intro β γ hβγ q hq
  exact reachableSubspace_antitone p F hβγ hq

theorem challengeReach_zero_eq_top (F D : AddSubgroup B) :
    challengeReach p F D 0 = ⊤ := by
  rw [challengeReach, FiniteEmbedding.reachableSubspace_zero_eq_top]
  rfl

/-- Membership in the local reach filtration has the expected ambient
translate form: a challenge-socle representative can be translated by the
old marked subgroup into the ambient Ulm tail. -/
theorem mem_challengeReach_iff
    {F D : AddSubgroup B}
    (x : challengeSocle p D) (β : Ordinal.{0}) :
    challengeQuotientMap p F D x ∈ challengeReach p F D β ↔
      ∃ e : F, (x : B) - (e : B) ∈ ulmSubgroup p β (G := B) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ :=
      (reachableDenSubmodule p F 0 β).mkQ_surjective c
    have hroom :
        (roomSubmodule p F 0).mkQ (reachableNumToSocle p F β c) =
          (roomSubmodule p F 0).mkQ ((challengeSocle p D).subtype x) := by
      exact hc
    have hdiff := (Submodule.Quotient.eq (roomSubmodule p F 0)).mp hroom
    have hcxF : (c : B) - (x : B) ∈ F := by
      exact hdiff.1
    obtain ⟨a, ha, z, hz, haz⟩ := (AddSubgroup.mem_sup).mp c.property.2
    let e : F := ⟨a - ((c : B) - (x : B)),
      F.sub_mem ha hcxF⟩
    refine ⟨e, ?_⟩
    convert hz using 1
    change (x : B) - (a - ((c : B) - (x : B))) = z
    rw [← haz]
    abel
  · rintro ⟨e, he⟩
    let c : reachableNum p F 0 β :=
      ⟨(x : B), ⟨(x : pSocleAt p (0 : Ordinal.{0}) (G := B)).property,
        (AddSubgroup.mem_sup).mpr
        ⟨(e : B), e.property, (x : B) - (e : B), he, by abel⟩⟩⟩
    refine ⟨(reachableDenSubmodule p F 0 β).mkQ c, ?_⟩
    rfl

/-- A finite challenge subgroup makes its concrete room finite-dimensional,
without any finiteness assumption on the ambient source group. -/
theorem challengeRoom_finiteDimensional
    {F D : AddSubgroup B} (hD : Set.Finite (D : Set B)) :
    FiniteDimensional (ZMod p) (challengeRoom p F D) := by
  letI : Fintype D := hD.fintype
  let toD : challengeSocle p D → D := fun x ↦
    ⟨(x : B), x.property⟩
  letI : Finite (challengeSocle p D) :=
    Finite.of_injective toD (by
      intro x y hxy
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : D ↦ (z : B)) hxy))
  letI : Finite (challengeRoom p F D) :=
    Finite.of_surjective (challengeQuotientMap p F D)
      (challengeQuotientMap_surjective p F D)
  let b := Basis.ofVectorSpace (ZMod p) (challengeRoom p F D)
  letI : Finite
      (Basis.ofVectorSpaceIndex (ZMod p) (challengeRoom p F D)) :=
    Finite.of_injective b b.injective
  exact b.finiteDimensional_of_finite

end SourceSpace

section TransfiniteFilteredBasis

variable {K : Type u} {V : Type v}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A finite-dimensional antitone ordinal filtration admits one basis which
simultaneously spans every filtration member by a subfamily.  Unlike the
finite-ambient wrapper in `FiniteEmbedding`, this lemma does not assume the
filtration dies at a natural stage.

The proof reindexes the (possibly transfinite) chain by the finite dimensions
of its members.  In a chain, two members with the same finite dimension are
equal, so the reindexed natural filtration retains every original level. -/
theorem exists_basis_spans_antitone
    [FiniteDimensional K V]
    (X : Ordinal.{0} → Submodule K V) (hX : Antitone X)
    (hzero : X 0 = ⊤) :
    ∃ (s : Set V) (b : Basis s K V),
      Finite s ∧ ∀ β : Ordinal.{0},
        ∃ I : Set s, Submodule.span K (b '' I) = X β := by
  let N := Module.finrank K V
  let Y : ℕ → Submodule K V := fun k ↦
    ⨆ β : Ordinal.{0}, ⨆ (_h : Module.finrank K (X β) ≤ k), X β
  have hY : Monotone Y := by
    intro k l hkl
    apply iSup_le
    intro β
    apply iSup_le
    intro hβ
    exact le_iSup_of_le β
      (le_iSup_of_le (hβ.trans hkl) le_rfl)
  have hYtop : Y N = ⊤ := by
    have hdim0 : Module.finrank K (X 0) ≤ N := by
      dsimp only [N]
      simpa using (Submodule.finrank_mono
        (show X 0 ≤ (⊤ : Submodule K V) from le_top))
    apply top_unique
    rw [← hzero]
    exact le_iSup_of_le (0 : Ordinal.{0})
      (le_iSup_of_le hdim0 le_rfl)
  obtain ⟨s, b, hs, hb⟩ :=
    FilteredBasis.exists_compatible_basis Y hY N hYtop
  refine ⟨s, b, hs, ?_⟩
  intro β
  have hYX : Y (Module.finrank K (X β)) = X β := by
    apply le_antisymm
    · apply iSup_le
      intro γ
      apply iSup_le
      intro hγdim
      rcases le_total β γ with hβγ | hγβ
      · exact hX hβγ
      · have hβγsub : X β ≤ X γ := hX hγβ
        have hβdim : Module.finrank K (X β) ≤
            Module.finrank K (X γ) :=
          Submodule.finrank_mono hβγsub
        have hdim : Module.finrank K (X β) =
            Module.finrank K (X γ) :=
          Nat.le_antisymm hβdim hγdim
        exact (Submodule.eq_of_le_of_finrank_eq hβγsub hdim).ge
    · exact le_iSup_of_le β (le_iSup_of_le le_rfl le_rfl)
  have hβN : Module.finrank K (X β) ≤ N := by
    dsimp only [N]
    simpa using (Submodule.finrank_mono
      (show X β ≤ (⊤ : Submodule K V) from le_top))
  obtain ⟨I, hI⟩ := hb (Module.finrank K (X β)) hβN
  exact ⟨I, hI.trans hYX⟩

end TransfiniteFilteredBasis

section AmbientReachBasis

variable {B : Type u} [AddCommGroup B]

/-- A nonzero class in the finite challenge room has an attained maximal
ambient reach.  The maximum is taken over the finite marked coset, and every
height in that coset is an ambient `B`-height. -/
theorem exists_exact_challengeReach
    (hB : IsReducedPGroup p B)
    {F D : AddSubgroup B} (hD : Set.Finite (D : Set B))
    (hFD : F ≤ D) (q : challengeRoom p F D) (hq : q ≠ 0) :
    ∃ ρ : Ordinal.{0}, ∀ β : Ordinal.{0},
      q ∈ challengeReach p F D β ↔ β ≤ ρ := by
  obtain ⟨x, rfl⟩ := challengeQuotientMap_surjective p F D q
  have hxq : challengeQuotientMap p F D x ≠ 0 := hq
  letI : Fintype D := hD.fintype
  let toD : F → D := fun e ↦ ⟨(e : B), hFD e.property⟩
  letI : Finite F := Finite.of_injective toD (by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : D ↦ (z : B)) hab)
  letI : Fintype F := Fintype.ofFinite F
  have hxe0 : ∀ e : F, (x : B) - (e : B) ≠ 0 := by
    intro e hzero
    apply hxq
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero (roomSubmodule p F 0)).mpr
    constructor
    · change (x : B) ∈ F
      have hxe : (x : B) = (e : B) := sub_eq_zero.mp hzero
      rw [hxe]
      exact e.property
    · exact (x : pSocleAt p (0 : Ordinal.{0}) (G := B)).property
  let height : F → Ordinal.{0} := fun e ↦
    Classical.choose (exists_ulmHeight_eq_of_ne_zero (p := p) hB (hxe0 e))
  have hheight_mem : ∀ e : F,
      (x : B) - (e : B) ∈ ulmSubgroup p (height e) (G := B) := fun e ↦
    (Classical.choose_spec
      (exists_ulmHeight_eq_of_ne_zero (p := p) hB (hxe0 e))).1
  have hheight_succ : ∀ e : F,
      (x : B) - (e : B) ∉
        ulmSubgroup p (Order.succ (height e)) (G := B) := fun e ↦
    (Classical.choose_spec
      (exists_ulmHeight_eq_of_ne_zero (p := p) hB (hxe0 e))).2
  have hmem_height : ∀ (e : F) (β : Ordinal.{0}),
      (x : B) - (e : B) ∈ ulmSubgroup p β (G := B) ↔
        β ≤ height e := by
    intro e β
    constructor
    · intro hmem
      by_contra hnot
      have hsucc : Order.succ (height e) ≤ β :=
        Order.succ_le_iff.mpr (lt_of_not_ge hnot)
      exact hheight_succ e (ulmSubgroup_antitone p hsucc hmem)
    · intro hle
      exact ulmSubgroup_antitone p hle (hheight_mem e)
  let heights : Finset Ordinal.{0} := Finset.univ.image height
  have hheights : heights.Nonempty := by
    exact ⟨height 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  let ρ : Ordinal.{0} := heights.max' hheights
  refine ⟨ρ, ?_⟩
  intro β
  rw [mem_challengeReach_iff]
  constructor
  · rintro ⟨e, he⟩
    exact (hmem_height e β).mp he |>.trans
      (heights.le_max' (height e)
        (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩))
  · intro hβρ
    have hρmem : ρ ∈ heights := heights.max'_mem hheights
    obtain ⟨e, _he, heρ⟩ := Finset.mem_image.mp hρmem
    refine ⟨e, (hmem_height e β).mpr ?_⟩
    simpa [heρ] using hβρ

/-- A finite challenge room has a basis with exact transfinite reaches for the
ambient filtration. -/
theorem exists_challenge_basis_compatibleWithReach
    (hB : IsReducedPGroup p B)
    {F D : AddSubgroup B} (hD : Set.Finite (D : Set B))
    (hFD : F ≤ D) :
    ∃ (s : Set (challengeRoom p F D))
      (b : Basis s (ZMod p) (challengeRoom p F D)),
      Finite s ∧ ∃ r : s → Ordinal.{0},
        HeightRado.CompatibleWithReach b r (challengeReach p F D) := by
  letI : FiniteDimensional (ZMod p) (challengeRoom p F D) :=
    challengeRoom_finiteDimensional p hD
  obtain ⟨s, b, hs, hb⟩ := exists_basis_spans_antitone
    (challengeReach p F D) (challengeReach_antitone p F D)
    (challengeReach_zero_eq_top p F D)
  have hexact : ∀ i : s, ∃ ρ : Ordinal.{0}, ∀ β : Ordinal.{0},
      b i ∈ challengeReach p F D β ↔ β ≤ ρ := by
    intro i
    exact exists_exact_challengeReach p hB hD hFD (b i) (b.ne_zero i)
  let r : s → Ordinal.{0} := fun i ↦ Classical.choose (hexact i)
  have hr : ∀ (i : s) (β : Ordinal.{0}),
      b i ∈ challengeReach p F D β ↔ β ≤ r i := fun i ↦
    Classical.choose_spec (hexact i)
  refine ⟨s, b, hs, r, ?_⟩
  intro β
  obtain ⟨I, hI⟩ := hb β
  have hIeq : I = {i : s | β ≤ r i} := by
    ext i
    constructor
    · intro hi
      apply (hr i β).mp
      rw [← hI]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · intro hi
      have himem : b i ∈ challengeReach p F D β := (hr i β).mpr hi
      rw [← hI] at himem
      exact b.self_mem_span_image.mp himem
  rw [← hIeq]
  exact hI.symm

end AmbientReachBasis

section LocalHeightCell

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F D : AddSubgroup B} {E : AddSubgroup A}

/-- A compatible local basis vector belongs to the challenge reach space at
its assigned ambient reach. -/
theorem challengeBasis_mem_reach
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    b i ∈ challengeReach p F D (r i) := by
  rw [hcompat (r i)]
  apply Submodule.subset_span
  refine ⟨i, ?_, rfl⟩
  change r i ≤ r i
  exact le_rfl

/-- Include the local reach space into the ambient concrete reachable
subspace.  This is the map through which the local selector kernel embeds in
the global selector kernel. -/
noncomputable def challengeReachToAmbient (β : Ordinal.{0}) :
    challengeReach p F D β →ₗ[ZMod p] reachableSubspace p F β where
  toFun q := ⟨((q : challengeRoom p F D) : room p F 0), q.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem challengeReachToAmbient_injective (β : Ordinal.{0}) :
    Function.Injective (challengeReachToAmbient p (F := F) (D := D) β) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun q : reachableSubspace p F β ↦ (q : room p F 0)) hxy

/-- The ambient reachable class represented by a local basis vector at its
own reach. -/
noncomputable def challengeSourceAtReach
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    reachableSpace p F 0 (r i) :=
  (reachableEquivSubspace p F (r i)).symm
    (challengeReachToAmbient p (F := F) (D := D) (r i)
      ⟨b i, challengeBasis_mem_reach p b r hcompat i⟩)

@[simp] theorem challengeSourceAtReach_toRoom
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    reachableToRoomZeroLinearMap p F (r i)
        (challengeSourceAtReach p b r hcompat i) =
      ((b i : challengeRoom p F D) : room p F 0) := by
  change ((reachableEquivSubspace p F (r i))
      ((reachableEquivSubspace p F (r i)).symm _) : room p F 0) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Forced target jump residue of a local basis vector. -/
noncomputable def challengeBasisJumpTarget
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) : jumpSpace p E (r i) :=
  jumpLinearMap p φ (hfloor (Order.succ (r i))) (hfloor (r i))
    (reachableToJumpLinearMap p F (r i)
      (challengeSourceAtReach p b r hcompat i))

/-- Choose a target reachable lift of the forced local jump residue. -/
noncomputable def challengeTargetAtReach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) : reachableSpace p E 0 (r i) :=
  Classical.choose (reachableToJumpLinearMap_surjective p E (r i)
    (challengeBasisJumpTarget p φ hfloor b r hcompat i))

theorem challengeTargetAtReach_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    reachableToJumpLinearMap p E (r i)
        (challengeTargetAtReach p φ hfloor b r hcompat i) =
      challengeBasisJumpTarget p φ hfloor b r hcompat i :=
  Classical.choose_spec (reachableToJumpLinearMap_surjective p E (r i)
    (challengeBasisJumpTarget p φ hfloor b r hcompat i))

/-- Restrict the source class from its own reach to an earlier level. -/
noncomputable def challengeSourceAtLevel
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) : reachableSpace p F 0 β :=
  reachableRestriction p F hβi
    (challengeSourceAtReach p b r hcompat i)

/-- Restrict the target lift from its own reach to an earlier level. -/
noncomputable def challengeTargetAtLevel
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) : reachableSpace p E 0 β :=
  reachableRestriction p E hβi
    (challengeTargetAtReach p φ hfloor b r hcompat i)

@[simp] theorem challengeSourceAtLevel_toRoom
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) :
    reachableToRoomZeroLinearMap p F β
        (challengeSourceAtLevel p b r hcompat hβi) =
      ((b i : challengeRoom p F D) : room p F 0) := by
  rw [challengeSourceAtLevel, reachableRestriction_toRoomZero,
    challengeSourceAtReach_toRoom]

/-- The forced residue equality is natural under restriction to any earlier
height. -/
theorem challengeTargetAtLevel_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) :
    reachableToJumpLinearMap p E β
        (challengeTargetAtLevel p φ hfloor b r hcompat hβi) =
      jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (reachableToJumpLinearMap p F β
          (challengeSourceAtLevel p b r hcompat hβi)) := by
  calc
    reachableToJumpLinearMap p E β
        (challengeTargetAtLevel p φ hfloor b r hcompat hβi) =
        jumpRestriction p E hβi
          (reachableToJumpLinearMap p E (r i)
            (challengeTargetAtReach p φ hfloor b r hcompat i)) :=
      reachableToJump_restriction p E hβi _
    _ = jumpRestriction p E hβi
        (challengeBasisJumpTarget p φ hfloor b r hcompat i) := by
      rw [challengeTargetAtReach_residue]
    _ = jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (jumpRestriction p F hβi
          (reachableToJumpLinearMap p F (r i)
            (challengeSourceAtReach p b r hcompat i))) := by
      exact jumpRestriction_jumpLinearMap p φ hfloor hβi _
    _ = jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (reachableToJumpLinearMap p F β
          (challengeSourceAtLevel p b r hcompat hβi)) := by
      rw [challengeSourceAtLevel, reachableToJump_restriction]

/-- Feasible base map on the finite challenge room. -/
noncomputable def challengeHeightCellBaseMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) :
    challengeRoom p F D →ₗ[ZMod p] room p E 0 :=
  b.constr (ZMod p) (fun i ↦
    reachableToRoomZeroLinearMap p E (r i)
      (challengeTargetAtReach p φ hfloor b r hcompat i))

@[simp] theorem challengeHeightCellBaseMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    challengeHeightCellBaseMap p φ hfloor b r hcompat (b i) =
      reachableToRoomZeroLinearMap p E (r i)
        (challengeTargetAtReach p φ hfloor b r hcompat i) :=
  b.constr_basis (ZMod p) _ i

theorem challengeHeightCellBaseMap_basis_mem_reachable
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (i : ι) :
    challengeHeightCellBaseMap p φ hfloor b r hcompat (b i) ∈
      reachableSubspace p E (r i) := by
  rw [challengeHeightCellBaseMap_basis]
  exact ⟨challengeTargetAtReach p φ hfloor b r hcompat i, rfl⟩

/-- All-vector feasibility for the local base map. -/
theorem challengeHeightCellBaseMap_mem_reachable
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0})
    (q : challengeRoom p F D) (hq : q ∈ challengeReach p F D β) :
    challengeHeightCellBaseMap p φ hfloor b r hcompat q ∈
      reachableSubspace p E β := by
  exact HeightRado.map_mem_of_compatible
    (challengeHeightCellBaseMap p φ hfloor b r hcompat)
    (challengeReach p F D) (reachableSubspace p E) b r hcompat
    (fun _ _ h ↦ reachableSubspace_antitone p E h)
    (challengeHeightCellBaseMap_basis_mem_reachable
      p φ hfloor b r hcompat) β q hq

/-- Restrict the local feasible map to a challenge reach space. -/
noncomputable def challengeHeightCellReachMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0}) :
    challengeReach p F D β →ₗ[ZMod p] reachableSpace p E 0 β :=
  (reachableEquivSubspace p E β).symm.toLinearMap.comp
    (((challengeHeightCellBaseMap p φ hfloor b r hcompat).domRestrict
      (challengeReach p F D β)).codRestrict
        (reachableSubspace p E β)
        (fun q ↦ challengeHeightCellBaseMap_mem_reachable
          p φ hfloor b r hcompat β
          (q : challengeRoom p F D) q.property))

/-- Jump residue of the local feasible map. -/
noncomputable def challengeHeightCellJumpMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0}) :
    challengeReach p F D β →ₗ[ZMod p] jumpSpace p E β :=
  (reachableToJumpLinearMap p E β).comp
    (challengeHeightCellReachMap p φ hfloor b r hcompat β)

/-- The ambient selector restricted to the local challenge reach space. -/
noncomputable def challengeSelectorMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (β : Ordinal.{0}) :
    challengeReach p F D β →ₗ[ZMod p] jumpSpace p E β :=
  (KernelRoom.selectorResidueMap p φ
      (hfloor (Order.succ β)) (hfloor β)).comp
    ((reachableEquivSubspace p F β).symm.toLinearMap.comp
      (challengeReachToAmbient p (F := F) (D := D) β))

/-- At an earlier level, the reachable representative of a local basis value
is the restricted target lift chosen at the vector's own reach. -/
theorem challengeHeightCellReachMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) :
    challengeHeightCellReachMap p φ hfloor b r hcompat β
        ⟨b i, challengeReach_antitone p F D hβi
          (challengeBasis_mem_reach p b r hcompat i)⟩ =
      challengeTargetAtLevel p φ hfloor b r hcompat hβi := by
  apply reachableToRoomZeroLinearMap_injective p E β
  simp only [challengeHeightCellReachMap, LinearMap.comp_apply]
  change reachableToRoomZeroLinearMap p E β
      ((reachableEquivSubspace p E β).symm
        ⟨challengeHeightCellBaseMap p φ hfloor b r hcompat (b i), _⟩) =
    reachableToRoomZeroLinearMap p E β
      (challengeTargetAtLevel p φ hfloor b r hcompat hβi)
  rw [reachableEquivSubspace_symm_toRoomZero]
  change challengeHeightCellBaseMap p φ hfloor b r hcompat (b i) =
    reachableToRoomZeroLinearMap p E β
      (challengeTargetAtLevel p φ hfloor b r hcompat hβi)
  rw [challengeHeightCellBaseMap_basis, challengeTargetAtLevel,
    reachableRestriction_toRoomZero]

/-- Transporting the concrete local basis vector back through the ambient
reachable equivalence gives its restricted source class. -/
theorem challengeSourceEquiv_symm_basis
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) :
    (reachableEquivSubspace p F β).symm
        (challengeReachToAmbient p (F := F) (D := D) β
          ⟨b i, challengeReach_antitone p F D hβi
            (challengeBasis_mem_reach p b r hcompat i)⟩) =
      challengeSourceAtLevel p b r hcompat hβi := by
  apply reachableToRoomZeroLinearMap_injective p F β
  rw [reachableEquivSubspace_symm_toRoomZero]
  change ((b i : challengeRoom p F D) : room p F 0) =
    reachableToRoomZeroLinearMap p F β
      (challengeSourceAtLevel p b r hcompat hβi)
  rw [challengeSourceAtLevel_toRoom]

/-- The local jump map and restricted ambient selector agree on every basis
vector present at the level. -/
theorem challengeHeightCellJumpMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) {β : Ordinal.{0}} {i : ι}
    (hβi : β ≤ r i) :
    challengeHeightCellJumpMap p φ hfloor b r hcompat β
        ⟨b i, challengeReach_antitone p F D hβi
          (challengeBasis_mem_reach p b r hcompat i)⟩ =
      challengeSelectorMap p φ hfloor (D := D) β
        ⟨b i, challengeReach_antitone p F D hβi
          (challengeBasis_mem_reach p b r hcompat i)⟩ := by
  rw [challengeHeightCellJumpMap, LinearMap.comp_apply,
    challengeHeightCellReachMap_basis, challengeSelectorMap,
    LinearMap.comp_apply, LinearMap.comp_apply]
  have hsource := challengeSourceEquiv_symm_basis
    p b r hcompat hβi
  change reachableToJumpLinearMap p E β
      (challengeTargetAtLevel p φ hfloor b r hcompat hβi) =
    jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
      (reachableToJumpLinearMap p F β
        ((reachableEquivSubspace p F β).symm
          (challengeReachToAmbient p (F := F) (D := D) β
            ⟨b i, _⟩)))
  rw [hsource]
  exact challengeTargetAtLevel_residue
    p φ hfloor b r hcompat hβi

/-- The local feasible map has exactly the restricted ambient selector residue
at every height. -/
theorem challengeHeightCellJumpMap_eq_selectorMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0}) :
    challengeHeightCellJumpMap p φ hfloor b r hcompat β =
      challengeSelectorMap p φ hfloor (D := D) β := by
  let f := challengeHeightCellJumpMap p φ hfloor b r hcompat β
  let g := challengeSelectorMap p φ hfloor (D := D) β
  let S : Set (challengeRoom p F D) := b '' {i | β ≤ r i}
  let lift : ∀ x : challengeRoom p F D,
      x ∈ Submodule.span (ZMod p) S → challengeReach p F D β :=
    fun x hx ↦ ⟨x, by rw [hcompat β]; exact hx⟩
  apply LinearMap.ext
  intro q
  have hqspan : (q : challengeRoom p F D) ∈
      Submodule.span (ZMod p) S := by
    rw [← hcompat β]
    exact q.property
  have hmain : f (lift (q : challengeRoom p F D) hqspan) =
      g (lift (q : challengeRoom p F D) hqspan) := by
    refine Submodule.span_induction (p := fun x hx ↦
      f (lift x hx) = g (lift x hx)) ?_ ?_ ?_ ?_ hqspan
    · rintro x ⟨i, hi, rfl⟩
      change f ⟨b i, _⟩ = g ⟨b i, _⟩
      simpa only [f, g] using
        challengeHeightCellJumpMap_basis p φ hfloor b r hcompat hi
    · change f (⟨0, _⟩ : challengeReach p F D β) =
        g (⟨0, _⟩ : challengeReach p F D β)
      convert (show f 0 = g 0 by simp) using 1
    · intro x y hx hy hxfg hyfg
      have hlift : lift (x + y) (Submodule.add_mem _ hx hy) =
          lift x hx + lift y hy := Subtype.ext rfl
      rw [hlift, map_add, map_add, hxfg, hyfg]
    · intro a x hx hxfg
      have hlift : lift (a • x) (Submodule.smul_mem _ a hx) =
          a • lift x hx := Subtype.ext rfl
      rw [hlift, map_smul, map_smul, hxfg]
  have hliftq : lift (q : challengeRoom p F D) hqspan = q :=
    Subtype.ext rfl
  simpa only [f, g, hliftq] using hmain

/-- The kernel of the local affine residue is the kernel of the local jump
map. -/
theorem ker_challengeResidue_eq_ker_jump
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0}) :
    LinearMap.ker (HeightRado.residueMap
      (challengeHeightCellBaseMap p φ hfloor b r hcompat)
      (challengeReach p F D) (roomSubspace p E) β) =
      LinearMap.ker
        (challengeHeightCellJumpMap p φ hfloor b r hcompat β) := by
  ext q
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change (roomSubspace p E β).mkQ
      (challengeHeightCellBaseMap p φ hfloor b r hcompat
        (q : challengeRoom p F D)) = 0 ↔
    reachableToJumpLinearMap p E β
      (challengeHeightCellReachMap p φ hfloor b r hcompat β q) = 0
  have hexact := reachableToRoomZero_mem_roomSubspace_iff p E β
    (challengeHeightCellReachMap p φ hfloor b r hcompat β q)
  have hglobal : reachableToRoomZeroLinearMap p E β
      (challengeHeightCellReachMap p φ hfloor b r hcompat β q) =
      challengeHeightCellBaseMap p φ hfloor b r hcompat
        (q : challengeRoom p F D) := by
    simp [challengeHeightCellReachMap]
  rw [hglobal] at hexact
  constructor
  · intro hq
    exact hexact.mp ((Submodule.Quotient.mk_eq_zero _).mp hq)
  · intro hq
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hexact.mpr hq)

/-- Send a vector in the local selector kernel to the same ambient reachable
class in the global selector kernel. -/
noncomputable def challengeKernelToGlobal
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (β : Ordinal.{0}) :
    LinearMap.ker (challengeSelectorMap p φ hfloor (D := D) β) →ₗ[ZMod p]
      LinearMap.ker (KernelRoom.selectorResidueMap p φ
        (hfloor (Order.succ β)) (hfloor β)) where
  toFun q :=
    ⟨(reachableEquivSubspace p F β).symm
      (challengeReachToAmbient p (F := F) (D := D) β
        (q : challengeReach p F D β)), by
      exact q.property⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp

theorem challengeKernelToGlobal_injective
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (β : Ordinal.{0}) :
    Function.Injective
      (challengeKernelToGlobal p φ hfloor (D := D) β) := by
  intro x y hxy
  apply Subtype.ext
  apply challengeReachToAmbient_injective p β
  apply (reachableEquivSubspace p F β).symm.injective
  exact congrArg
    (fun q : LinearMap.ker (KernelRoom.selectorResidueMap p φ
      (hfloor (Order.succ β)) (hfloor β)) ↦
        (q : reachableSpace p F 0 β)) hxy

/-- The local affine residue kernel injects into the global selector kernel.
Consequently the global `K_β` inequality pays every finite challenge without
any finiteness assumption on the ambient target. -/
theorem challengeResidueKernel_rank_le_global
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D)) (β : Ordinal.{0}) :
    Module.rank (ZMod p)
        (LinearMap.ker (HeightRado.residueMap
          (challengeHeightCellBaseMap p φ hfloor b r hcompat)
          (challengeReach p F D) (roomSubspace p E) β)) ≤
      Module.rank (ZMod p)
        (LinearMap.ker (KernelRoom.selectorResidueMap p φ
          (hfloor (Order.succ β)) (hfloor β))) := by
  rw [ker_challengeResidue_eq_ker_jump]
  rw [challengeHeightCellJumpMap_eq_selectorMap]
  exact (challengeKernelToGlobal p φ hfloor (D := D) β).rank_le_of_injective
    (challengeKernelToGlobal_injective p φ hfloor (D := D) β)

/-- **Finite local height-cell selection from the ambient `K_β` budget.**
This is the quantitative seam needed by the finite embedding theorem: only the
challenge room is finite-dimensional, while target room directions may be
arbitrarily large. -/
theorem hasInjectiveChallengeHeightCellSelection_of_reach_budget
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (challengeRoom p F D)]
    (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D))
    (hbudget : ∀ i : ι,
      Survival.KernelRoomBudgetAt p φ (r i)
        (hfloor (Order.succ (r i))) (hfloor (r i))) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (challengeHeightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := by
  apply HeightRado.hasInjectiveRealization_affineAccess_of_rank_reach_budget
    (challengeHeightCellBaseMap p φ hfloor b r hcompat)
    (challengeReach p F D) (roomSubspace p E) b r hcompat
  intro i
  rw [roomSubspace_rank]
  exact (challengeResidueKernel_rank_le_global
    p φ hfloor b r hcompat (r i)).trans
      ((Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le
        p φ (r i) (hfloor (Order.succ (r i))) (hfloor (r i))).mp
          (hbudget i))

/-- The all-height budget is a convenient wrapper around the exact
finite-range interface above. -/
theorem hasInjectiveChallengeHeightCellSelection_of_budget
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (challengeRoom p F D)]
    (b : Basis ι (ZMod p) (challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (challengeReach p F D))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (challengeHeightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := by
  apply HeightRado.hasInjectiveRealization_affineAccess_of_rank_reach_budget
    (challengeHeightCellBaseMap p φ hfloor b r hcompat)
    (challengeReach p F D) (roomSubspace p E) b r hcompat
  intro i
  rw [roomSubspace_rank]
  exact (challengeResidueKernel_rank_le_global
    p φ hfloor b r hcompat (r i)).trans
      ((Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le
        p φ (r i) (hfloor (Order.succ (r i))) (hfloor (r i))).mp
          (hbudget (r i)))

end LocalHeightCell

end FiniteChallenge
