import Lib.BackForth.HeightCell

/-!
# Lifting room maps to the actual socles

The affine Height--Rado selector lives on the room quotients

`P(B)/(F ∩ P(B)) → P(A)/(E ∩ P(A))`.

This file isolates the purely linear bridge back to the actual `p`-socles.  A
map on the source marked socle is first extended to the whole source socle. A
linear section of the target quotient then corrects that extension so that the
prescribed quotient map commutes exactly. The stronger construction chooses
coherent source and target representatives along a compatible filtration
basis. Its main theorem lifts the affine Rado selector injectively while
preserving every marked height equation.
-/

noncomputable section

open Module Ordinal

universe u v w

namespace SocleLift

/-! ### Abstract quotient lifting -/

variable {K : Type u} {V : Type v} {W : Type w}
variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A linear map on a subspace and an arbitrary map on the corresponding
quotients admit one common lift to the ambient spaces, provided the prescribed
subspace map lands in the target denominator. -/
theorem exists_compatible_quotient_lift
    (U : Submodule K V) (T : Submodule K W)
    (g : U →ₗ[K] W) (hg : ∀ u, g u ∈ T)
    (L : (V ⧸ U) →ₗ[K] (W ⧸ T)) :
    ∃ Φ : V →ₗ[K] W,
      Φ.comp U.subtype = g ∧
      T.mkQ.comp Φ = L.comp U.mkQ := by
  obtain ⟨G, hG⟩ := g.exists_extend
  let d : V →ₗ[K] W ⧸ T := L.comp U.mkQ - T.mkQ.comp G
  obtain ⟨s, hs⟩ := T.mkQ.exists_rightInverse_of_surjective T.range_mkQ
  let Φ : V →ₗ[K] W := G + s.comp d
  refine ⟨Φ, ?_, ?_⟩
  · apply LinearMap.ext
    intro u
    have hGu : G (u : V) = g u := by
      exact LinearMap.ext_iff.mp hG u
    have hdu : d (u : V) = 0 := by
      have hU : U.mkQ (u : V) = 0 :=
        (Submodule.Quotient.mk_eq_zero U).mpr u.property
      have hT : T.mkQ (g u) = 0 :=
        (Submodule.Quotient.mk_eq_zero T).mpr (hg u)
      simp [d, hGu, hU, hT]
    simp [Φ, hGu, hdu]
  · apply LinearMap.ext
    intro x
    have hsx : T.mkQ (s (d x)) = d x := by
      exact LinearMap.ext_iff.mp hs (d x)
    simp only [LinearMap.comp_apply, Φ, LinearMap.add_apply, map_add, hsx]
    simp [d]

/-! ### The marked map on the socle denominator -/

variable (p : ℕ) [hp : Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A}

/-- The partial homomorphism restricted to `F ∩ P(B)`, with codomain the
actual target `p`-socle. -/
noncomputable def markedSocleValue (φ : F →+ E)
    (x : roomSubmodule p F 0) : pSocleAt p 0 (G := A) := by
  let xf : F :=
    ⟨((x : pSocleAt p 0 (G := B)) : B), x.property.1⟩
  refine ⟨(φ xf : A), ?_⟩
  rw [mem_pSocleAt]
  constructor
  · have hx0 : p • (((x : pSocleAt p 0 (G := B)) : B)) = 0 :=
      (x : pSocleAt p 0 (G := B)).property.1
    have hxf0 : p • xf = 0 := Subtype.ext hx0
    calc
      p • (φ xf : A) = (φ (p • xf) : A) := by
        exact congrArg Subtype.val (φ.map_nsmul xf p).symm
      _ = 0 := by rw [hxf0, map_zero]; rfl
  · simp [ulmSubgroup_zero]

@[simp] theorem markedSocleValue_coe (φ : F →+ E)
    (x : roomSubmodule p F 0) :
    (markedSocleValue p φ x : A) =
      (φ ⟨((x : pSocleAt p 0 (G := B)) : B), x.property.1⟩ : A) := by
  rfl

noncomputable def markedSocleMap (φ : F →+ E) :
    roomSubmodule p F 0 →ₗ[ZMod p] pSocleAt p 0 (G := A) :=
  ({
    toFun := markedSocleValue p φ
    map_zero' := by
      apply Subtype.ext
      rw [markedSocleValue_coe]
      have hzero :
          (⟨((0 : roomSubmodule p F 0) : pSocleAt p 0 (G := B)),
            (0 : roomSubmodule p F 0).property.1⟩ : F) = 0 :=
        Subtype.ext rfl
      rw [hzero, map_zero]
      rfl
    map_add' := by
      intro x y
      apply Subtype.ext
      change (markedSocleValue p φ (x + y) : A) =
        (markedSocleValue p φ x : A) + (markedSocleValue p φ y : A)
      rw [markedSocleValue_coe, markedSocleValue_coe,
        markedSocleValue_coe]
      have hxy :
          (⟨(((x + y : roomSubmodule p F 0) :
              pSocleAt p 0 (G := B)) : B), (x + y).property.1⟩ : F) =
            ⟨((x : pSocleAt p 0 (G := B)) : B), x.property.1⟩ +
            ⟨((y : pSocleAt p 0 (G := B)) : B), y.property.1⟩ :=
        Subtype.ext rfl
      rw [hxy, map_add]
      rfl
  } : roomSubmodule p F 0 →+ pSocleAt p 0 (G := A)).toZModLinearMap p

/-- The marked socle map lands in the target room denominator. -/
theorem markedSocleMap_mem_roomSubmodule (φ : F →+ E)
    (x : roomSubmodule p F 0) :
    markedSocleMap p φ x ∈ roomSubmodule p E 0 := by
  constructor
  · change (φ ⟨((x : pSocleAt p 0 (G := B)) : B), x.property.1⟩ : A) ∈ E
    exact (φ ⟨((x : pSocleAt p 0 (G := B)) : B), x.property.1⟩).property
  · exact (markedSocleMap p φ x).property

/-- **Room-to-socle lifting.**  Every prescribed room map has a lift on the
actual source and target `p`-socles which agrees with the partial homomorphism
on the marked source socle and induces exactly the prescribed room map. -/
theorem exists_socle_lift (φ : F →+ E)
    (L : room p F 0 →ₗ[ZMod p] room p E 0) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ := by
  exact exists_compatible_quotient_lift
    (roomSubmodule p F 0) (roomSubmodule p E 0)
    (markedSocleMap p φ) (markedSocleMap_mem_roomSubmodule p φ) L

/-! ### Height-valid representatives -/

/-- A target reachable class with the forced jump residue has an actual
`p`-socle representative satisfying the corresponding marked height
equation.  The correction term extracted from the jump denominator is what
makes the representative simultaneously `p`-torsion and height-valid. -/
theorem exists_heightValid_representative
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (β : Ordinal.{0}) (x : reachableNum p F 0 β) (e : F)
    (hxe : (x : B) - (e : B) ∈ ulmSubgroup p β)
    (q : reachableSpace p E 0 β)
    (hjump : reachableToJumpLinearMap p E β q =
      jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (reachableToJumpLinearMap p F β
          ((reachableDenSubmodule p F 0 β).mkQ x))) :
    ∃ y : pSocleAt p 0 (G := A),
      (roomSubmodule p E 0).mkQ y =
        reachableToRoomZeroLinearMap p E β q ∧
      (y : A) - (φ e : A) ∈ ulmSubgroup p β := by
  refine Quotient.inductionOn q ?_ hjump
  intro u hu
  rw [reachableToJumpLinearMap_mk_of_anchor p F β x (e : B) e.property hxe] at hu
  change QuotientAddGroup.mk (reachableAnchorMultiple p E β u) =
    QuotientAddGroup.mk
      (jumpNumMap p φ (hfloor (Order.succ β))
        (reachableAnchorMultipleOf p F β x (e : B) e.property hxe)) at hu
  rw [QuotientAddGroup.eq_iff_sub_mem] at hu
  change ((reachableAnchorMultiple p E β u : jumpNum p E β) : A) -
      ((jumpNumMap p φ (hfloor (Order.succ β))
        (reachableAnchorMultipleOf p F β x (e : B) e.property hxe) :
          jumpNum p E β) : A) ∈ jumpDen p E β at hu
  rw [jumpNumMap_coe] at hu
  change p • reachableAnchor p E β u -
      (φ (p • e) : A) ∈ jumpDen p E β at hu
  rw [map_nsmul] at hu
  change p • reachableAnchor p E β u - p • (φ e : A) ∈
    jumpDen p E β at hu
  obtain ⟨t, ht, hpt⟩ := hu
  let yA : A := (u : A) - reachableAnchor p E β u + (φ e : A) + t
  have hy0 : p • yA = 0 := by
    simp only [yA, smul_add, smul_sub]
    have hu0 : p • (u : A) = 0 :=
      (mem_pSocleAt p 0 (u : A)).1 u.property.1 |>.1
    rw [hu0, hpt]
    abel
  let y : pSocleAt p 0 (G := A) := by
    refine ⟨yA, ?_⟩
    rw [mem_pSocleAt]
    exact ⟨hy0, by simp [ulmSubgroup_zero]⟩
  refine ⟨y, ?_, ?_⟩
  · change (roomSubmodule p E 0).mkQ y =
      (roomSubmodule p E 0).mkQ (reachableNumToSocle p E β u)
    apply (Submodule.Quotient.eq _).2
    constructor
    · change yA - (u : A) ∈ E
      convert E.add_mem
        (E.add_mem (E.neg_mem (reachableAnchor_mem p E β u)) (φ e).property)
        ht.1 using 1
      simp [yA]
      abel
    · change (((y - reachableNumToSocle p E β u :
          pSocleAt p 0 (G := A))) : A) ∈ pSocleAt p 0 (G := A)
      exact (y - reachableNumToSocle p E β u).property
  · change yA - (φ e : A) ∈ ulmSubgroup p β
    have hres := reachableResidual_mem p E β u
    convert (ulmSubgroup p β).add_mem hres ht.2 using 1
    simp [yA]
    abel

/-! ### Coherent basis representatives -/

variable {ι : Type v}

/-- A numerator representative of the canonical reachable class of a source
basis vector at its own reach. -/
noncomputable def sourceBasisNum
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : reachableNum p F 0 (r i) :=
  Classical.choose
    ((reachableDenSubmodule p F 0 (r i)).mkQ_surjective
      (HeightCell.sourceAtReach p b r hcompat i))

theorem sourceBasisNum_mk
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    (reachableDenSubmodule p F 0 (r i)).mkQ
        (sourceBasisNum p b r hcompat i) =
      HeightCell.sourceAtReach p b r hcompat i :=
  Classical.choose_spec
    ((reachableDenSubmodule p F 0 (r i)).mkQ_surjective
      (HeightCell.sourceAtReach p b r hcompat i))

/-- The actual source-socle lift of one quotient basis vector. -/
noncomputable def sourceBasisSocle
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : pSocleAt p 0 (G := B) :=
  reachableNumToSocle p F (r i) (sourceBasisNum p b r hcompat i)

@[simp] theorem sourceBasisSocle_mkQ
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    (roomSubmodule p F 0).mkQ (sourceBasisSocle p b r hcompat i) = b i := by
  rw [sourceBasisSocle, ← reachableToRoomZeroLinearMap_mk,
    sourceBasisNum_mk, HeightCell.sourceAtReach_toRoom]

/-- A marked anchor for the chosen source numerator. -/
noncomputable def sourceBasisAnchor
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : F :=
  ⟨reachableAnchor p F (r i) (sourceBasisNum p b r hcompat i),
    reachableAnchor_mem p F (r i) (sourceBasisNum p b r hcompat i)⟩

theorem sourceBasisSocle_sub_anchor_mem
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    (sourceBasisSocle p b r hcompat i : B) -
        (sourceBasisAnchor p b r hcompat i : B) ∈ ulmSubgroup p (r i) := by
  exact reachableResidual_mem p F (r i) (sourceBasisNum p b r hcompat i)

/-- The room-direction correction selected by an affine access witness. -/
noncomputable def accessRoomWitness
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) : room p E (r i) :=
  Classical.choose (haccess i)

theorem accessRoomWitness_toRoomZero
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) :
    roomToRoomZeroLinearMap p E (r i)
        (accessRoomWitness p φ hfloor b r hcompat L haccess i) =
      L (b i) - HeightCell.heightCellBaseMap p φ hfloor b r hcompat (b i) :=
  Classical.choose_spec (haccess i)

/-- The target reachable class obtained by adding the selected room direction
to the canonical forced-residue lift. -/
noncomputable def targetBasisReach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) : reachableSpace p E 0 (r i) :=
  HeightCell.targetAtReach p φ hfloor b r hcompat i +
    roomToReachableLinearMap p E (r i)
      (accessRoomWitness p φ hfloor b r hcompat L haccess i)

theorem targetBasisReach_toRoomZero
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) :
    reachableToRoomZeroLinearMap p E (r i)
        (targetBasisReach p φ hfloor b r hcompat L haccess i) = L (b i) := by
  rw [targetBasisReach, map_add]
  change reachableToRoomZeroLinearMap p E (r i)
      (HeightCell.targetAtReach p φ hfloor b r hcompat i) +
    roomToRoomZeroLinearMap p E (r i)
      (accessRoomWitness p φ hfloor b r hcompat L haccess i) = L (b i)
  rw [← HeightCell.heightCellBaseMap_basis,
    accessRoomWitness_toRoomZero]
  abel

theorem targetBasisReach_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) :
    reachableToJumpLinearMap p E (r i)
        (targetBasisReach p φ hfloor b r hcompat L haccess i) =
      jumpLinearMap p φ (hfloor (Order.succ (r i))) (hfloor (r i))
        (reachableToJumpLinearMap p F (r i)
          ((reachableDenSubmodule p F 0 (r i)).mkQ
            (sourceBasisNum p b r hcompat i))) := by
  rw [targetBasisReach, map_add, reachableToJump_roomToReachable_zero, add_zero,
    sourceBasisNum_mk]
  exact HeightCell.targetAtReach_residue p φ hfloor b r hcompat i

/-- A height-valid actual target-socle representative of the selected room
value on one source basis vector. -/
noncomputable def targetBasisSocle
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) : pSocleAt p 0 (G := A) :=
  Classical.choose (exists_heightValid_representative p φ hfloor (r i)
    (sourceBasisNum p b r hcompat i) (sourceBasisAnchor p b r hcompat i)
    (sourceBasisSocle_sub_anchor_mem p b r hcompat i)
    (targetBasisReach p φ hfloor b r hcompat L haccess i)
    (targetBasisReach_residue p φ hfloor b r hcompat L haccess i))

theorem targetBasisSocle_spec
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) :
    (roomSubmodule p E 0).mkQ
        (targetBasisSocle p φ hfloor b r hcompat L haccess i) = L (b i) ∧
      (targetBasisSocle p φ hfloor b r hcompat L haccess i : A) -
          (φ (sourceBasisAnchor p b r hcompat i) : A) ∈
        ulmSubgroup p (r i) := by
  have hspec := Classical.choose_spec
    (exists_heightValid_representative p φ hfloor (r i)
      (sourceBasisNum p b r hcompat i) (sourceBasisAnchor p b r hcompat i)
      (sourceBasisSocle_sub_anchor_mem p b r hcompat i)
      (targetBasisReach p φ hfloor b r hcompat L haccess i)
      (targetBasisReach_residue p φ hfloor b r hcompat L haccess i))
  exact ⟨hspec.1.trans
    (targetBasisReach_toRoomZero p φ hfloor b r hcompat L haccess i), hspec.2⟩

/-- A linear section of the source room quotient whose basis representatives
come with canonical reach witnesses. -/
noncomputable def sourceSocleSection
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F)) :
    room p F 0 →ₗ[ZMod p] pSocleAt p 0 (G := B) :=
  b.constr (ZMod p) (sourceBasisSocle p b r hcompat)

@[simp] theorem sourceSocleSection_basis
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    sourceSocleSection p b r hcompat (b i) = sourceBasisSocle p b r hcompat i :=
  b.constr_basis (ZMod p) _ i

theorem sourceSocleSection_rightInverse
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F)) :
    (roomSubmodule p F 0).mkQ.comp (sourceSocleSection p b r hcompat) =
      LinearMap.id := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, sourceSocleSection_basis, LinearMap.id_apply]
  exact sourceBasisSocle_mkQ p b r hcompat i

/-- The corresponding height-valid target values, extended linearly from the
same quotient basis. -/
noncomputable def targetSocleSection
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i) :
    room p F 0 →ₗ[ZMod p] pSocleAt p 0 (G := A) :=
  b.constr (ZMod p) (targetBasisSocle p φ hfloor b r hcompat L haccess)

@[simp] theorem targetSocleSection_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (i : ι) :
    targetSocleSection p φ hfloor b r hcompat L haccess (b i) =
      targetBasisSocle p φ hfloor b r hcompat L haccess i :=
  b.constr_basis (ZMod p) _ i

theorem targetSocleSection_quotient
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i) :
    (roomSubmodule p E 0).mkQ.comp
        (targetSocleSection p φ hfloor b r hcompat L haccess) = L := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, targetSocleSection_basis]
  exact (targetBasisSocle_spec p φ hfloor b r hcompat L haccess i).1

/-- On every reachable source quotient vector, the paired source and target
sections admit one marked anchor and satisfy the two height equations at the
same level. -/
theorem exists_pairedAnchor_on_reach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i)
    (β : Ordinal.{0}) (q : room p F 0) (hq : q ∈ reachableSubspace p F β) :
    ∃ e : F,
      (sourceSocleSection p b r hcompat q : B) - (e : B) ∈ ulmSubgroup p β ∧
      (targetSocleSection p φ hfloor b r hcompat L haccess q : A) -
          (φ e : A) ∈ ulmSubgroup p β := by
  rw [hcompat β] at hq
  refine Submodule.span_induction (p := fun q _ => ∃ e : F,
      (sourceSocleSection p b r hcompat q : B) - (e : B) ∈ ulmSubgroup p β ∧
      (targetSocleSection p φ hfloor b r hcompat L haccess q : A) -
        (φ e : A) ∈ ulmSubgroup p β) ?_ ?_ ?_ ?_ hq
  · rintro q ⟨i, hi, rfl⟩
    refine ⟨sourceBasisAnchor p b r hcompat i, ?_, ?_⟩
    · rw [sourceSocleSection_basis]
      exact ulmSubgroup_antitone p hi
        (sourceBasisSocle_sub_anchor_mem p b r hcompat i)
    · rw [targetSocleSection_basis]
      exact ulmSubgroup_antitone p hi
        (targetBasisSocle_spec p φ hfloor b r hcompat L haccess i).2
  · refine ⟨0, ?_, ?_⟩ <;> simp
  · intro x y hx hy
    rintro ⟨ex, hsx, htx⟩ ⟨ey, hsy, hty⟩
    refine ⟨ex + ey, ?_, ?_⟩
    · simpa only [map_add, AddSubgroup.coe_add, add_sub_add_comm] using
        (ulmSubgroup p β).add_mem hsx hsy
    · simpa only [map_add, AddSubgroup.coe_add, add_sub_add_comm] using
        (ulmSubgroup p β).add_mem htx hty
  · intro a x hx
    rintro ⟨e, hs, ht⟩
    let z : ℤ := ZMod.cast a
    have hza : (z : ZMod p) = a := ZMod.intCast_zmod_cast a
    refine ⟨z • e, ?_, ?_⟩
    · rw [map_smul, ← hza, Int.cast_smul_eq_zsmul]
      simpa only [AddSubgroup.coe_zsmul, smul_sub] using
        (ulmSubgroup p β).zsmul_mem hs z
    · rw [map_smul, ← hza, Int.cast_smul_eq_zsmul]
      simpa only [map_zsmul, AddSubgroup.coe_zsmul, smul_sub] using
        (ulmSubgroup p β).zsmul_mem ht z

/-! ### The height-compatible socle lift -/

/-- Every marked height equation relating a source socle element to the
partial domain is preserved by the socle map. -/
def IsMarkedHeightFloor (φ : F →+ E)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)) : Prop :=
  ∀ (β : Ordinal.{0}) (x : pSocleAt p 0 (G := B)) (e : F),
    (x : B) - (e : B) ∈ ulmSubgroup p β →
      (Φ x : A) - (φ e : A) ∈ ulmSubgroup p β

/-- Additive form of the marked height equations used in the paper. -/
theorem IsMarkedHeightFloor.add_mem
    {φ : F →+ E}
    {Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)}
    (h : IsMarkedHeightFloor p φ Φ)
    (β : Ordinal.{0}) (x : pSocleAt p 0 (G := B)) (e : F)
    (hxe : (x : B) + (e : B) ∈ ulmSubgroup p β) :
    (Φ x : A) + (φ e : A) ∈ ulmSubgroup p β := by
  have hmain := h β x (-e) (by simpa using hxe)
  simpa using hmain

/-- **Height-compatible quotient-to-socle lifting.**  An affine selector on
the room quotient satisfying the basis access sets has a lift to the actual
`p`-socles which agrees with the marked map, induces the selector exactly,
and preserves every marked height equation. -/
theorem exists_heightCompatible_socle_lift
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ ∧
      IsMarkedHeightFloor p φ Φ := by
  obtain ⟨G, hG⟩ := (markedSocleMap p φ).exists_extend
  let S := sourceSocleSection p b r hcompat
  let T := targetSocleSection p φ hfloor b r hcompat L haccess
  let qB := (roomSubmodule p F 0).mkQ
  let Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A) :=
    G + T.comp qB - G.comp (S.comp qB)
  have hS : qB.comp S = LinearMap.id :=
    sourceSocleSection_rightInverse p b r hcompat
  have hT : (roomSubmodule p E 0).mkQ.comp T = L :=
    targetSocleSection_quotient p φ hfloor b r hcompat L haccess
  have hmark : Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ := by
    apply LinearMap.ext
    intro u
    have hq : qB ((roomSubmodule p F 0).subtype u) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr u.property
    have hGu : G ((roomSubmodule p F 0).subtype u) = markedSocleMap p φ u :=
      LinearMap.ext_iff.mp hG u
    change G ((roomSubmodule p F 0).subtype u) +
        T (qB ((roomSubmodule p F 0).subtype u)) -
        G (S (qB ((roomSubmodule p F 0).subtype u))) = markedSocleMap p φ u
    rw [hq, map_zero, map_zero, map_zero, hGu]
    simp
  have hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp (roomSubmodule p F 0).mkQ := by
    apply LinearMap.ext
    intro x
    let qx := qB x
    let sx := S qx
    have hqs : qB sx = qx := by
      exact LinearMap.ext_iff.mp hS qx
    have hd : x - sx ∈ roomSubmodule p F 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change qB (x - sx) = 0
      simp [map_sub, hqs, qx]
    let d : roomSubmodule p F 0 := ⟨x - sx, hd⟩
    have hGd : G (x - sx) = markedSocleMap p φ d := by
      have := LinearMap.ext_iff.mp hG d
      exact this
    have hGdmem : G (x - sx) ∈ roomSubmodule p E 0 := by
      rw [hGd]
      exact markedSocleMap_mem_roomSubmodule p φ d
    have hTG : (roomSubmodule p E 0).mkQ (T qx) = L qx := by
      exact LinearMap.ext_iff.mp hT qx
    change (roomSubmodule p E 0).mkQ (Φ x) = L (qB x)
    rw [show Φ x = T qx + G (x - sx) by simp [Φ, qx, sx]; abel]
    rw [map_add, hTG,
      show (roomSubmodule p E 0).mkQ (G (x - sx)) = 0 by
        exact (Submodule.Quotient.mk_eq_zero _).mpr hGdmem,
      add_zero]
  refine ⟨Φ, hmark, hquot, ?_⟩
  intro β x e hxe
  let xn : reachableNum p F 0 β :=
    ⟨(x : B), ⟨x.property,
      (AddSubgroup.mem_sup).2
        ⟨(e : B), e.property, (x : B) - (e : B), hxe, by abel⟩⟩⟩
  have hqx : qB x ∈ reachableSubspace p F β := by
    refine ⟨(reachableDenSubmodule p F 0 β).mkQ xn, ?_⟩
    change reachableToRoomZeroLinearMap p F β
        ((reachableDenSubmodule p F 0 β).mkQ xn) = qB x
    rfl
  obtain ⟨a, hSa, hTa⟩ := exists_pairedAnchor_on_reach
    p φ hfloor b r hcompat L haccess β (qB x) hqx
  let sx := S (qB x)
  have hqs : qB sx = qB x := by
    exact LinearMap.ext_iff.mp hS (qB x)
  have hd : x - sx ∈ roomSubmodule p F 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change qB (x - sx) = 0
    simp [map_sub, hqs]
  let d : roomSubmodule p F 0 := ⟨x - sx, hd⟩
  let de : F := ⟨((x - sx : pSocleAt p 0 (G := B)) : B), hd.1⟩
  have hdea : (de : B) + (a : B) - (e : B) ∈ ulmSubgroup p β := by
    convert (ulmSubgroup p β).sub_mem hxe hSa using 1
    simp [de, sx, S]
    abel
  have hφdea : (φ (de + a - e) : A) ∈ ulmSubgroup p β :=
    hfloor β (de + a - e) hdea
  have hGd : G (x - sx) = markedSocleMap p φ d :=
    LinearMap.ext_iff.mp hG d
  have hGd_coe : (G (x - sx) : A) = (φ de : A) := by
    rw [hGd]
    rfl
  have hΦx : Φ x = T (qB x) + G (x - sx) := by
    simp [Φ, sx]
    abel
  change (Φ x : A) - (φ e : A) ∈ ulmSubgroup p β
  rw [hΦx]
  have hsum := (ulmSubgroup p β).add_mem hTa hφdea
  convert hsum using 1
  change (T (qB x) : A) + (G (x - sx) : A) - (φ e : A) =
    (T (qB x) : A) - (φ a : A) + (φ (de + a - e) : A)
  rw [hGd_coe, map_sub, map_add]
  simp
  abel

/-- Injectivity on the room quotient reflects target-denominator membership
back to the source denominator. -/
theorem source_mem_of_socleLift_mem
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp (roomSubmodule p F 0).mkQ)
    (x : pSocleAt p 0 (G := B))
    (hx : Φ x ∈ roomSubmodule p E 0) :
    x ∈ roomSubmodule p F 0 := by
  have htarget : (roomSubmodule p E 0).mkQ (Φ x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hcomm := LinearMap.ext_iff.mp hquot x
  change (roomSubmodule p E 0).mkQ (Φ x) =
    L ((roomSubmodule p F 0).mkQ x) at hcomm
  have hLzero : L ((roomSubmodule p F 0).mkQ x) = 0 := by
    exact hcomm.symm.trans htarget
  have hsource : (roomSubmodule p F 0).mkQ x = 0 := by
    apply hL
    simpa using hLzero
  exact (Submodule.Quotient.mk_eq_zero _).mp hsource

/-- Marked injectivity and quotient injectivity together imply injectivity of
any compatible map on the full source socle. -/
theorem socleLift_injective
    (φ : F →+ E) (hφ : Function.Injective φ)
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (hmark : Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ)
    (hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp (roomSubmodule p F 0).mkQ) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxU : x ∈ roomSubmodule p F 0 :=
    source_mem_of_socleLift_mem p L hL Φ hquot x
      (by rw [hx]; exact (roomSubmodule p E 0).zero_mem)
  let xU : roomSubmodule p F 0 := ⟨x, hxU⟩
  have hmarkx : Φ x = markedSocleMap p φ xU :=
    LinearMap.ext_iff.mp hmark xU
  have hmarked0 : markedSocleMap p φ xU = 0 := by
    rw [← hmarkx, hx]
  have hφzero : φ
      ⟨((x : pSocleAt p 0 (G := B)) : B), hxU.1⟩ = 0 := by
    apply Subtype.ext
    have hval := congrArg
      (fun z : pSocleAt p 0 (G := A) => (z : A)) hmarked0
    change (φ ⟨((x : pSocleAt p 0 (G := B)) : B), hxU.1⟩ : A) = 0 at hval
    exact hval
  have hxFzero :
      (⟨((x : pSocleAt p 0 (G := B)) : B), hxU.1⟩ : F) = 0 := by
    apply hφ
    simpa using hφzero
  apply Subtype.ext
  change ((x : pSocleAt p 0 (G := B)) : B) = 0
  exact congrArg Subtype.val hxFzero

/-- **Injective room selectors lift algebraically to injective socle maps.**
If the marked homomorphism and the prescribed room map are injective, the
compatible lift can be chosen injective on the full source `p`-socle. -/
theorem exists_injective_socle_lift
    (φ : F →+ E) (hφ : Function.Injective φ)
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ := by
  obtain ⟨Φ, hmark, hquot⟩ := exists_socle_lift p φ L
  exact ⟨Φ, socleLift_injective p φ hφ L hL Φ hmark hquot, hmark, hquot⟩

/-- An injective affine selector has an injective lift satisfying every marked
height equation, not merely an algebraically compatible lift. -/
theorem exists_injective_heightCompatible_socle_lift
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0)) (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ ∧
      IsMarkedHeightFloor p φ Φ := by
  obtain ⟨Φ, hmark, hquot, hheight⟩ :=
    exists_heightCompatible_socle_lift p φ hfloor b r hcompat L haccess
  exact ⟨Φ, socleLift_injective p φ hφ L hL Φ hmark hquot,
    hmark, hquot, hheight⟩

/-- **D-23 produces an injective algebraic socle lift.**  From a compatible
reach basis and the room--kernel budgets, first choose the injective affine
room selector and then lift it to an injective map on the actual source
`p`-socle which agrees with the marked homomorphism on `F ∩ P(B)`.

The returned access-set condition retains precisely the data needed for the
remaining height-equation proof. -/
theorem exists_injective_socle_lift_of_budget
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (room p F 0)]
    [FiniteDimensional (ZMod p) (room p E 0)]
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (L : room p F 0 →ₗ[ZMod p] room p E 0)
      (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ := by
  obtain ⟨L, hL, haccess⟩ :=
    HeightCell.hasInjectiveHeightCellSelection_of_budget
      p φ hfloor b r hcompat hbudget
  obtain ⟨Φ, hΦ, hmark, hquot⟩ :=
    exists_injective_socle_lift p φ hφ L hL
  exact ⟨L, Φ, hL, haccess, hΦ, hmark, hquot⟩

/-- **D-23 produces an injective, height-compatible socle lift.**  This is
the complete quotient-to-socle bridge: the room--kernel budget chooses the
injective affine selector, and the coherent representative construction lifts
it to the actual source socle while preserving every marked height equation. -/
theorem exists_injective_heightCompatible_socle_lift_of_budget
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (room p F 0)]
    [FiniteDimensional (ZMod p) (room p E 0)]
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (L : room p F 0 →ₗ[ZMod p] room p E 0)
      (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ ∧
      IsMarkedHeightFloor p φ Φ := by
  obtain ⟨L, hL, haccess⟩ :=
    HeightCell.hasInjectiveHeightCellSelection_of_budget
      p φ hfloor b r hcompat hbudget
  obtain ⟨Φ, hΦ, hmark, hquot, hheight⟩ :=
    exists_injective_heightCompatible_socle_lift
      p φ hφ hfloor b r hcompat L hL haccess
  exact ⟨L, Φ, hL, haccess, hΦ, hmark, hquot, hheight⟩

end SocleLift
