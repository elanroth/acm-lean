import Lib.BackForth.FiniteChallenge

/-!
# Local lifting from a finite challenge room to its ambient socle

This file lifts an injective affine selector on
`(D ∩ P₀(B))/(F ∩ P₀(B))` to the actual challenge socle `D ∩ P₀(B)`.
All Ulm heights remain heights in the ambient groups `B` and `A`.
-/

noncomputable section

open Module Ordinal

universe u v

variable (p : ℕ) [hp : Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace LocalSocleLift

variable {F D : AddSubgroup B} {E : AddSubgroup A}
variable {ι : Type v}

/-- The part of the finite challenge socle already marked by `F`. -/
noncomputable def challengeDenominator :
    Submodule (ZMod p) (FiniteChallenge.challengeSocle p D) :=
  (roomSubmodule p F 0).comap
    (FiniteChallenge.challengeSocle p D).subtype

/-- Include the local marked denominator in the ambient marked socle. -/
noncomputable def challengeDenominatorToMarked :
    challengeDenominator p (F := F) (D := D) →ₗ[ZMod p]
      roomSubmodule p F 0 where
  toFun x := ⟨((x : FiniteChallenge.challengeSocle p D) :
    pSocleAt p 0 (G := B)), x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The marked map on `F ∩ D ∩ P₀(B)`. -/
noncomputable def challengeMarkedSocleMap (φ : F →+ E) :
    challengeDenominator p (F := F) (D := D) →ₗ[ZMod p]
      pSocleAt p 0 (G := A) :=
  (SocleLift.markedSocleMap p φ).comp
    (challengeDenominatorToMarked p (F := F) (D := D))

/-- Choose an actual challenge-socle representative of a local room basis
vector. -/
noncomputable def sourceBasisSocle
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (i : ι) : FiniteChallenge.challengeSocle p D :=
  Classical.choose
    (FiniteChallenge.challengeQuotientMap_surjective p F D (b i))

@[simp] theorem sourceBasisSocle_quotient
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (i : ι) :
    FiniteChallenge.challengeQuotientMap p F D
        (sourceBasisSocle p b i) = b i :=
  Classical.choose_spec
    (FiniteChallenge.challengeQuotientMap_surjective p F D (b i))

/-- A marked anchor witnessing the assigned ambient reach of a local basis
representative. -/
noncomputable def sourceBasisAnchor
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D)) (i : ι) : F :=
  Classical.choose
    ((FiniteChallenge.mem_challengeReach_iff p
      (sourceBasisSocle p b i) (r i)).mp (by
        rw [sourceBasisSocle_quotient]
        exact FiniteChallenge.challengeBasis_mem_reach
          p b r hcompat i))

theorem sourceBasisSocle_sub_anchor_mem
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D)) (i : ι) :
    (sourceBasisSocle p b i : B) -
        (sourceBasisAnchor p b r hcompat i : B) ∈
      ulmSubgroup p (r i) (G := B) :=
  Classical.choose_spec
    ((FiniteChallenge.mem_challengeReach_iff p
      (sourceBasisSocle p b i) (r i)).mp (by
        rw [sourceBasisSocle_quotient]
        exact FiniteChallenge.challengeBasis_mem_reach
          p b r hcompat i))

/-- The reachable numerator built from the actual challenge representative
and its marked anchor. -/
noncomputable def sourceBasisNum
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D)) (i : ι) :
    reachableNum p F 0 (r i) :=
  ⟨(sourceBasisSocle p b i : B),
    ⟨((sourceBasisSocle p b i :
      FiniteChallenge.challengeSocle p D) :
        pSocleAt p 0 (G := B)).property,
      (AddSubgroup.mem_sup).mpr
        ⟨(sourceBasisAnchor p b r hcompat i : B),
          (sourceBasisAnchor p b r hcompat i).property,
          (sourceBasisSocle p b i : B) -
            (sourceBasisAnchor p b r hcompat i : B),
          sourceBasisSocle_sub_anchor_mem p b r hcompat i, by abel⟩⟩⟩

theorem sourceBasisNum_mk_eq_sourceAtReach
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D)) (i : ι) :
    (reachableDenSubmodule p F 0 (r i)).mkQ
        (sourceBasisNum p b r hcompat i) =
      FiniteChallenge.challengeSourceAtReach p b r hcompat i := by
  apply reachableToRoomZeroLinearMap_injective p F (r i)
  rw [reachableToRoomZeroLinearMap_mk,
    FiniteChallenge.challengeSourceAtReach_toRoom]
  change (roomSubmodule p F 0).mkQ
      ((sourceBasisSocle p b i :
        FiniteChallenge.challengeSocle p D) :
          pSocleAt p 0 (G := B)) =
    ((b i : FiniteChallenge.challengeRoom p F D) : room p F 0)
  have hq := sourceBasisSocle_quotient p b i
  exact congrArg
    (fun q : FiniteChallenge.challengeRoom p F D ↦
      (q : room p F 0)) hq

/-- The room correction selected by one affine access witness. -/
noncomputable def accessRoomWitness
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) : room p E (r i) :=
  Classical.choose (haccess i)

theorem accessRoomWitness_toRoomZero
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) :
    roomToRoomZeroLinearMap p E (r i)
        (accessRoomWitness p φ hfloor b r hcompat L haccess i) =
      L (b i) - FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat (b i) :=
  Classical.choose_spec (haccess i)

/-- Correct the canonical forced-residue lift by the chosen target room
direction. -/
noncomputable def targetBasisReach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) : reachableSpace p E 0 (r i) :=
  FiniteChallenge.challengeTargetAtReach p φ hfloor b r hcompat i +
    roomToReachableLinearMap p E (r i)
      (accessRoomWitness p φ hfloor b r hcompat L haccess i)

theorem targetBasisReach_toRoomZero
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) :
    reachableToRoomZeroLinearMap p E (r i)
        (targetBasisReach p φ hfloor b r hcompat L haccess i) = L (b i) := by
  rw [targetBasisReach, map_add]
  change reachableToRoomZeroLinearMap p E (r i)
      (FiniteChallenge.challengeTargetAtReach
        p φ hfloor b r hcompat i) +
    roomToRoomZeroLinearMap p E (r i)
      (accessRoomWitness p φ hfloor b r hcompat L haccess i) = L (b i)
  rw [← FiniteChallenge.challengeHeightCellBaseMap_basis,
    accessRoomWitness_toRoomZero]
  abel

theorem targetBasisReach_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) :
    reachableToJumpLinearMap p E (r i)
        (targetBasisReach p φ hfloor b r hcompat L haccess i) =
      jumpLinearMap p φ (hfloor (Order.succ (r i))) (hfloor (r i))
        (reachableToJumpLinearMap p F (r i)
          ((reachableDenSubmodule p F 0 (r i)).mkQ
            (sourceBasisNum p b r hcompat i))) := by
  rw [targetBasisReach, map_add, reachableToJump_roomToReachable_zero,
    add_zero, sourceBasisNum_mk_eq_sourceAtReach]
  exact FiniteChallenge.challengeTargetAtReach_residue
    p φ hfloor b r hcompat i

/-- A height-valid actual target-socle value for one local basis vector. -/
noncomputable def targetBasisSocle
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) : pSocleAt p 0 (G := A) :=
  Classical.choose (SocleLift.exists_heightValid_representative
    p φ hfloor (r i) (sourceBasisNum p b r hcompat i)
    (sourceBasisAnchor p b r hcompat i)
    (sourceBasisSocle_sub_anchor_mem p b r hcompat i)
    (targetBasisReach p φ hfloor b r hcompat L haccess i)
    (targetBasisReach_residue p φ hfloor b r hcompat L haccess i))

theorem targetBasisSocle_spec
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) :
    (roomSubmodule p E 0).mkQ
        (targetBasisSocle p φ hfloor b r hcompat L haccess i) = L (b i) ∧
      (targetBasisSocle p φ hfloor b r hcompat L haccess i : A) -
          (φ (sourceBasisAnchor p b r hcompat i) : A) ∈
        ulmSubgroup p (r i) := by
  have hspec := Classical.choose_spec
    (SocleLift.exists_heightValid_representative
      p φ hfloor (r i) (sourceBasisNum p b r hcompat i)
      (sourceBasisAnchor p b r hcompat i)
      (sourceBasisSocle_sub_anchor_mem p b r hcompat i)
      (targetBasisReach p φ hfloor b r hcompat L haccess i)
      (targetBasisReach_residue p φ hfloor b r hcompat L haccess i))
  exact ⟨hspec.1.trans
    (targetBasisReach_toRoomZero p φ hfloor b r hcompat L haccess i),
    hspec.2⟩

/-- Linear section of the challenge quotient using actual elements of
`D ∩ P₀(B)`. -/
noncomputable def sourceSocleSection
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D)) :
    FiniteChallenge.challengeRoom p F D →ₗ[ZMod p]
      FiniteChallenge.challengeSocle p D :=
  b.constr (ZMod p) (sourceBasisSocle p b)

@[simp] theorem sourceSocleSection_basis
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (i : ι) :
    sourceSocleSection p b (b i) = sourceBasisSocle p b i :=
  b.constr_basis (ZMod p) _ i

theorem sourceSocleSection_rightInverse
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D)) :
    (FiniteChallenge.challengeQuotientMap p F D).comp
        (sourceSocleSection p b) = LinearMap.id := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, sourceSocleSection_basis,
    LinearMap.id_apply]
  exact sourceBasisSocle_quotient p b i

/-- Height-valid target values, extended linearly from the same local basis. -/
noncomputable def targetSocleSection
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i) :
    FiniteChallenge.challengeRoom p F D →ₗ[ZMod p]
      pSocleAt p 0 (G := A) :=
  b.constr (ZMod p)
    (targetBasisSocle p φ hfloor b r hcompat L haccess)

@[simp] theorem targetSocleSection_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (i : ι) :
    targetSocleSection p φ hfloor b r hcompat L haccess (b i) =
      targetBasisSocle p φ hfloor b r hcompat L haccess i :=
  b.constr_basis (ZMod p) _ i

theorem targetSocleSection_quotient
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i) :
    (roomSubmodule p E 0).mkQ.comp
        (targetSocleSection p φ hfloor b r hcompat L haccess) = L := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, targetSocleSection_basis]
  exact (targetBasisSocle_spec
    p φ hfloor b r hcompat L haccess i).1

/-- On any local quotient vector reachable at `β`, the paired source and
target sections admit one common marked anchor and satisfy the ambient height
equations. -/
theorem exists_pairedAnchor_on_reach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i)
    (β : Ordinal.{0}) (q : FiniteChallenge.challengeRoom p F D)
    (hq : q ∈ FiniteChallenge.challengeReach p F D β) :
    ∃ e : F,
      (sourceSocleSection p b q : B) - (e : B) ∈
          ulmSubgroup p β ∧
      (targetSocleSection p φ hfloor b r hcompat L haccess q : A) -
          (φ e : A) ∈ ulmSubgroup p β := by
  rw [hcompat β] at hq
  refine Submodule.span_induction (p := fun q _ ↦ ∃ e : F,
      (sourceSocleSection p b q : B) - (e : B) ∈ ulmSubgroup p β ∧
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
    · rw [map_add]
      change (sourceSocleSection p b x : B) +
          (sourceSocleSection p b y : B) - ((ex : B) + (ey : B)) ∈
        ulmSubgroup p β
      simpa only [add_sub_add_comm] using
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

/-- Ambient marked height equations restricted to the finite challenge
socle. -/
def IsChallengeMarkedHeightFloor (φ : F →+ E)
    (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
      pSocleAt p 0 (G := A)) : Prop :=
  ∀ (β : Ordinal.{0}) (x : FiniteChallenge.challengeSocle p D) (e : F),
    (x : B) - (e : B) ∈ ulmSubgroup p β →
      (Φ x : A) - (φ e : A) ∈ ulmSubgroup p β

theorem challengeQuotientMap_eq_zero_iff
    (x : FiniteChallenge.challengeSocle p D) :
    FiniteChallenge.challengeQuotientMap p F D x = 0 ↔
      x ∈ challengeDenominator p (F := F) (D := D) := by
  constructor
  · intro hx
    change ((x : FiniteChallenge.challengeSocle p D) :
      pSocleAt p 0 (G := B)) ∈ roomSubmodule p F 0
    apply (Submodule.Quotient.mk_eq_zero (roomSubmodule p F 0)).mp
    exact congrArg
      (fun q : FiniteChallenge.challengeRoom p F D ↦
        (q : room p F 0)) hx
  · intro hx
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero (roomSubmodule p F 0)).mpr hx

/-- **Local height-compatible quotient-to-socle lifting.**  An affine
selector on the finite challenge room lifts to the actual `D ∩ P₀(B)`, agrees
with the marked map on `F ∩ P₀(B)`, and preserves every ambient marked height
equation involving an element of the challenge socle. -/
theorem exists_heightCompatible_challengeSocle_lift
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (FiniteChallenge.challengeHeightCellBaseMap
        p φ hfloor b r hcompat) (roomSubspace p E) b r i) :
    ∃ Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
        pSocleAt p 0 (G := A),
      Φ.comp (challengeDenominator p (F := F) (D := D)).subtype =
          challengeMarkedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
          L.comp (FiniteChallenge.challengeQuotientMap p F D) ∧
      IsChallengeMarkedHeightFloor p φ Φ := by
  obtain ⟨G, hG⟩ := (challengeMarkedSocleMap p φ).exists_extend
  let S := sourceSocleSection p b
  let T := targetSocleSection p φ hfloor b r hcompat L haccess
  let qB := FiniteChallenge.challengeQuotientMap p F D
  let Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
      pSocleAt p 0 (G := A) :=
    G + T.comp qB - G.comp (S.comp qB)
  have hS : qB.comp S = LinearMap.id :=
    sourceSocleSection_rightInverse p b
  have hT : (roomSubmodule p E 0).mkQ.comp T = L :=
    targetSocleSection_quotient p φ hfloor b r hcompat L haccess
  have hmark : Φ.comp
      (challengeDenominator p (F := F) (D := D)).subtype =
        challengeMarkedSocleMap p φ := by
    apply LinearMap.ext
    intro u
    have hq : qB
        ((challengeDenominator p (F := F) (D := D)).subtype u) = 0 :=
      (challengeQuotientMap_eq_zero_iff p _).mpr u.property
    have hGu : G
        ((challengeDenominator p (F := F) (D := D)).subtype u) =
          challengeMarkedSocleMap p φ u :=
      LinearMap.ext_iff.mp hG u
    change G ((challengeDenominator p (F := F) (D := D)).subtype u) +
        T (qB ((challengeDenominator p (F := F) (D := D)).subtype u)) -
        G (S (qB ((challengeDenominator p (F := F) (D := D)).subtype u))) =
      challengeMarkedSocleMap p φ u
    rw [hq, map_zero, map_zero, map_zero, hGu]
    simp
  have hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp qB := by
    apply LinearMap.ext
    intro x
    let qx := qB x
    let sx := S qx
    have hqs : qB sx = qx := LinearMap.ext_iff.mp hS qx
    have hd : x - sx ∈ challengeDenominator p (F := F) (D := D) := by
      apply (challengeQuotientMap_eq_zero_iff p (x - sx)).mp
      change qB (x - sx) = 0
      simp [map_sub, hqs, qx]
    let d : challengeDenominator p (F := F) (D := D) := ⟨x - sx, hd⟩
    have hGd : G (x - sx) = challengeMarkedSocleMap p φ d := by
      exact LinearMap.ext_iff.mp hG d
    have hGdmem : G (x - sx) ∈ roomSubmodule p E 0 := by
      rw [hGd]
      exact SocleLift.markedSocleMap_mem_roomSubmodule p φ
        (challengeDenominatorToMarked p (F := F) (D := D) d)
    have hTG : (roomSubmodule p E 0).mkQ (T qx) = L qx :=
      LinearMap.ext_iff.mp hT qx
    change (roomSubmodule p E 0).mkQ (Φ x) = L (qB x)
    rw [show Φ x = T qx + G (x - sx) by simp [Φ, qx, sx]; abel]
    rw [map_add, hTG,
      show (roomSubmodule p E 0).mkQ (G (x - sx)) = 0 by
        exact (Submodule.Quotient.mk_eq_zero _).mpr hGdmem,
      add_zero]
  refine ⟨Φ, hmark, hquot, ?_⟩
  intro β x e hxe
  have hqx : qB x ∈ FiniteChallenge.challengeReach p F D β := by
    apply (FiniteChallenge.mem_challengeReach_iff p x β).mpr
    exact ⟨e, hxe⟩
  obtain ⟨a, hSa, hTa⟩ := exists_pairedAnchor_on_reach
    p φ hfloor b r hcompat L haccess β (qB x) hqx
  let sx := S (qB x)
  have hqs : qB sx = qB x := LinearMap.ext_iff.mp hS (qB x)
  have hd : x - sx ∈ challengeDenominator p (F := F) (D := D) := by
    apply (challengeQuotientMap_eq_zero_iff p (x - sx)).mp
    change qB (x - sx) = 0
    simp [map_sub, hqs]
  let d : challengeDenominator p (F := F) (D := D) := ⟨x - sx, hd⟩
  let de : F :=
    ⟨((x - sx : FiniteChallenge.challengeSocle p D) : B), hd.1⟩
  have hdea : (de : B) + (a : B) - (e : B) ∈ ulmSubgroup p β := by
    convert (ulmSubgroup p β).sub_mem hxe hSa using 1
    simp [de, sx, S]
    abel
  have hφdea : (φ (de + a - e) : A) ∈ ulmSubgroup p β :=
    hfloor β (de + a - e) hdea
  have hGd : G (x - sx) = challengeMarkedSocleMap p φ d :=
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

/-- Injectivity on the finite challenge quotient plus injectivity of the
marked map implies injectivity of the local socle lift. -/
theorem challengeSocleLift_injective
    (φ : F →+ E) (hφ : Function.Injective φ)
    (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L)
    (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
      pSocleAt p 0 (G := A))
    (hmark : Φ.comp
      (challengeDenominator p (F := F) (D := D)).subtype =
        challengeMarkedSocleMap p φ)
    (hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp (FiniteChallenge.challengeQuotientMap p F D)) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have htarget : (roomSubmodule p E 0).mkQ (Φ x) = 0 := by
    rw [hx]
    exact map_zero _
  have hcomm := LinearMap.ext_iff.mp hquot x
  have hLzero : L (FiniteChallenge.challengeQuotientMap p F D x) = 0 := by
    exact hcomm.symm.trans htarget
  have hqzero : FiniteChallenge.challengeQuotientMap p F D x = 0 := by
    apply hL
    simpa using hLzero
  have hxden : x ∈ challengeDenominator p (F := F) (D := D) :=
    (challengeQuotientMap_eq_zero_iff p x).mp hqzero
  let xd : challengeDenominator p (F := F) (D := D) := ⟨x, hxden⟩
  have hmarkx : Φ x = challengeMarkedSocleMap p φ xd :=
    LinearMap.ext_iff.mp hmark xd
  have hmarked0 : challengeMarkedSocleMap p φ xd = 0 := by
    rw [← hmarkx, hx]
  have hφzero : φ
      ⟨(x : B), hxden.1⟩ = 0 := by
    apply Subtype.ext
    exact congrArg
      (fun z : pSocleAt p 0 (G := A) ↦ (z : A)) hmarked0
  have hxF : (⟨(x : B), hxden.1⟩ : F) = 0 := by
    apply hφ
    simpa using hφzero
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : F ↦ (z : B)) hxF

/-- The ambient `K_β` budget produces an injective, height-compatible map on
the actual finite challenge socle.  No target-finiteness hypothesis occurs. -/
theorem exists_injective_heightCompatible_challengeSocle_lift_of_reach_budget
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    [Fintype ι]
    [FiniteDimensional (ZMod p) (FiniteChallenge.challengeRoom p F D)]
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (hbudget : ∀ i : ι,
      Survival.KernelRoomBudgetAt p φ (r i)
        (hfloor (Order.succ (r i))) (hfloor (r i))) :
    ∃ (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
      (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
        pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (FiniteChallenge.challengeHeightCellBaseMap
          p φ hfloor b r hcompat) (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (challengeDenominator p (F := F) (D := D)).subtype =
        challengeMarkedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (FiniteChallenge.challengeQuotientMap p F D) ∧
      IsChallengeMarkedHeightFloor p φ Φ := by
  obtain ⟨L, hL, haccess⟩ :=
    FiniteChallenge.hasInjectiveChallengeHeightCellSelection_of_reach_budget
      p φ hfloor b r hcompat hbudget
  obtain ⟨Φ, hmark, hquot, hheight⟩ :=
    exists_heightCompatible_challengeSocle_lift
      p φ hfloor b r hcompat L haccess
  exact ⟨L, Φ, hL, haccess,
    challengeSocleLift_injective p φ hφ L hL Φ hmark hquot,
    hmark, hquot, hheight⟩

/-- The all-height budget wrapper used by the general finite challenge
theorem. -/
theorem exists_injective_heightCompatible_challengeSocle_lift_of_budget
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    [Fintype ι]
    [FiniteDimensional (ZMod p) (FiniteChallenge.challengeRoom p F D)]
    (b : Basis ι (ZMod p) (FiniteChallenge.challengeRoom p F D))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (FiniteChallenge.challengeReach p F D))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (L : FiniteChallenge.challengeRoom p F D →ₗ[ZMod p] room p E 0)
      (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
        pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (FiniteChallenge.challengeHeightCellBaseMap
          p φ hfloor b r hcompat) (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (challengeDenominator p (F := F) (D := D)).subtype =
        challengeMarkedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (FiniteChallenge.challengeQuotientMap p F D) ∧
      IsChallengeMarkedHeightFloor p φ Φ := by
  obtain ⟨L, hL, haccess⟩ :=
    FiniteChallenge.hasInjectiveChallengeHeightCellSelection_of_budget
      p φ hfloor b r hcompat hbudget
  obtain ⟨Φ, hmark, hquot, hheight⟩ :=
    exists_heightCompatible_challengeSocle_lift
      p φ hfloor b r hcompat L haccess
  exact ⟨L, Φ, hL, haccess,
    challengeSocleLift_injective p φ hφ L hL Φ hmark hquot,
    hmark, hquot, hheight⟩

end LocalSocleLift
