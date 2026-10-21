import Lib.BackForth.Algebraic
import Lib.BackForth.ExactStageTransfer
import Lib.BackForth.FiniteEmbedding
import Lib.BackForth.Relations
import Lib.BackForth.RoomTail

/-!
# Necessity lemmas for the ACM algebraic characterization

This module runs the back-and-forth relation in the direction opposite to the
finite-extension construction.  Its first job is deliberately local: a
rank-one response to a tuple enumerating an entire finite source group yields
an injective height-nondecreasing homomorphism of that whole source into the
target.  This is the bridge from ACM's finite-tuple quantifier to the finite
room--kernel necessity theorem.
-/

noncomputable section

open Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]

namespace ACMNecessity

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]

/-- An additive homomorphism restricts linearly to the height-zero
`p`-socles.  This small adapter is useful for reading an atomic tuple
isomorphism as a linear map on a finite family of order-`p` witnesses. -/
noncomputable def pSocleZeroMap
    {K L : Type u} [AddCommGroup K] [AddCommGroup L] (f : K →+ L) :
    pSocleAt p (0 : Ordinal.{0}) (G := K) →ₗ[ZMod p]
      pSocleAt p (0 : Ordinal.{0}) (G := L) :=
  ({
    toFun := fun x ↦ ⟨f x, by
      rw [mem_pSocleAt]
      constructor
      · simpa [map_nsmul] using congrArg f
          ((mem_pSocleAt p 0 (x : K)).1 x.property |>.1)
      · simp [ulmSubgroup_zero]⟩
    map_zero' := by ext; simp
    map_add' := by intro x y; ext; simp
  } : pSocleAt p (0 : Ordinal.{0}) (G := K) →+
      pSocleAt p (0 : Ordinal.{0}) (G := L)).toZModLinearMap p

@[simp] theorem pSocleZeroMap_coe
    {K L : Type u} [AddCommGroup K] [AddCommGroup L] (f : K →+ L)
    (x : pSocleAt p (0 : Ordinal.{0}) (G := K)) :
    (pSocleZeroMap p f x : L) = f x := rfl

/-- Atomicity of an enlarged tuple response preserves linear independence
modulo the old marked subgroup.

The source witnesses are selected coordinates of the challenge and are
assumed independent in the height-zero source room.  The enlarged tuple
isomorphism sends them to the corresponding response coordinates.  If a
linear combination of those responses fell back into the old target mark,
restriction to the old tuple map and injectivity of the enlarged isomorphism
would put the source combination back into the old source mark. -/
theorem exists_roomZero_linearIndependent_response
    {n r m : ℕ} {a : Fin n → G} {b : Fin n → H}
    (C : TupleIsoMap a b)
    (d : Fin r → H) (c : Fin r → G)
    (C' : TupleIsoMap (Fin.append a c) (Fin.append b d))
    (j : Fin m → Fin r)
    (x : Fin m → pSocleAt p (0 : Ordinal.{0}) (G := H))
    (hxcoord : ∀ i, d (j i) = (x i : H))
    (hlin : LinearIndependent (ZMod p) (fun i ↦
      (roomSubmodule p (tupleSubgroup b) 0).mkQ (x i))) :
    ∃ y : Fin m → pSocleAt p (0 : Ordinal.{0}) (G := G),
      (∀ i, (y i : G) = c (j i)) ∧
      LinearIndependent (ZMod p) (fun i ↦
        (roomSubmodule p (tupleSubgroup a) 0).mkQ (y i)) := by
  let sourceGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨d (j i), AddSubgroup.subset_closure
      (show d (j i) ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (j i), by simp⟩)⟩
  let sourceSocle (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0})
        (G := tupleSubgroup (Fin.append b d)) :=
    ⟨sourceGen i, by
      rw [mem_pSocleAt]
      constructor
      · apply Subtype.ext
        change p • d (j i) = 0
        rw [hxcoord i]
        exact (mem_pSocleAt p 0 (x i : H)).1 (x i).property |>.1
      · simp [ulmSubgroup_zero]⟩
  let Φ := pSocleZeroMap p C'.equiv.toAddMonoidHom
  let includeSource := pSocleZeroMap p
    (tupleSubgroup (Fin.append b d)).subtype
  let includeTarget := pSocleZeroMap p
    (tupleSubgroup (Fin.append a c)).subtype
  let y : Fin m → pSocleAt p (0 : Ordinal.{0}) (G := G) :=
    fun i ↦ includeTarget (Φ (sourceSocle i))
  have hycoord : ∀ i, (y i : G) = c (j i) := by
    intro i
    change (C'.equiv (sourceGen i) : G) = c (j i)
    have hmap := congrArg Subtype.val
      (C'.map_gen (Fin.natAdd n (j i)))
    simpa [sourceGen] using hmap
  have hsourceCoord : ∀ i, includeSource (sourceSocle i) = x i := by
    intro i
    apply Subtype.ext
    simpa [includeSource, sourceSocle, sourceGen] using hxcoord i
  refine ⟨y, hycoord, ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  apply Fintype.linearIndependent_iff.mp hlin g ?_ i
  let targetSum : pSocleAt p (0 : Ordinal.{0}) (G := G) :=
    ∑ k, g k • y k
  let sourceSum : pSocleAt p (0 : Ordinal.{0})
      (G := tupleSubgroup (Fin.append b d)) :=
    ∑ k, g k • sourceSocle k
  let sourceAmbientSum : pSocleAt p (0 : Ordinal.{0}) (G := H) :=
    ∑ k, g k • x k
  have htargetQ :
      (roomSubmodule p (tupleSubgroup a) 0).mkQ
          targetSum = 0 := by
    simpa only [targetSum, map_sum, map_smul] using hg
  have htargetMem :
      (targetSum : G) ∈ tupleSubgroup a :=
    ((Submodule.Quotient.mk_eq_zero
      (roomSubmodule p (tupleSubgroup a) 0)).1 htargetQ).1
  let oldTarget : tupleSubgroup a :=
    ⟨(targetSum : G), htargetMem⟩
  let oldSource : tupleSubgroup b := C.equiv.symm oldTarget
  let oldInclusion : tupleSubgroup b →+
      tupleSubgroup (Fin.append b d) :=
    AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
  have hsourceEq :
      sourceSum =
        ⟨oldInclusion oldSource, by
          rw [mem_pSocleAt]
          constructor
          · apply Subtype.ext
            have htargetZero : p • oldTarget = 0 := by
              apply Subtype.ext
              exact (mem_pSocleAt p 0 (targetSum : G)).1
                targetSum.property |>.1
            have hsourceZero : p • oldSource = 0 := by
              apply C.equiv.injective
              rw [map_nsmul, map_zero]
              simpa [oldSource] using htargetZero
            exact congrArg Subtype.val
              (by simpa using congrArg oldInclusion hsourceZero)
          · simp [ulmSubgroup_zero]⟩ := by
    apply Subtype.ext
    apply C'.equiv.injective
    apply Subtype.ext
    change (C'.equiv (sourceSum :
      tupleSubgroup (Fin.append b d)) : G) =
      (C'.equiv (oldInclusion oldSource) : G)
    have hmapSum : includeTarget (Φ sourceSum) = targetSum := by
      simp [sourceSum, targetSum, y]
    calc
      (C'.equiv (sourceSum :
          tupleSubgroup (Fin.append b d)) : G) =
          (targetSum : G) := congrArg Subtype.val hmapSum
      _ = (oldTarget : G) := rfl
      _ = (C.equiv oldSource : G) := by simp [oldSource]
      _ = (C'.equiv (oldInclusion oldSource) : G) :=
        C.append_left_equiv_apply_eq C' oldSource
  have hsourceMem :
      (sourceAmbientSum : H) ∈ tupleSubgroup b := by
    have hval := congrArg (fun z :
      pSocleAt p (0 : Ordinal.{0})
        (G := tupleSubgroup (Fin.append b d)) ↦
          (((z : tupleSubgroup (Fin.append b d)) : H))) hsourceEq
    have hambient : (sourceAmbientSum : H) = (oldSource : H) := by
      have hsumMap : includeSource sourceSum = sourceAmbientSum := by
        simp [sourceSum, sourceAmbientSum, hsourceCoord]
      calc
        (sourceAmbientSum : H) = (includeSource sourceSum : H) :=
          congrArg Subtype.val hsumMap.symm
        _ = (((sourceSum : pSocleAt p (0 : Ordinal.{0})
            (G := tupleSubgroup (Fin.append b d))) :
              tupleSubgroup (Fin.append b d)) : H) := rfl
        _ = (oldSource : H) := hval
    rw [hambient]
    exact oldSource.property
  have hsourceQ :
      (roomSubmodule p (tupleSubgroup b) 0).mkQ sourceAmbientSum = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (roomSubmodule p (tupleSubgroup b) 0)).2
      ⟨hsourceMem, sourceAmbientSum.property⟩
  simpa only [sourceAmbientSum, map_sum, map_smul] using hsourceQ

/-- A finite independent family in the selector kernel at a natural level can
be realized as an independent family in the target room at that level.

Choose reachable socle representatives `xᵢ = eᵢ + p^k zᵢ` and challenge with
both `xᵢ` and the roots `zᵢ`.  Atomicity preserves the displayed equations and
independence modulo the old mark.  The selector-kernel equation says that
`p C(eᵢ)` has a preimage in the marked part of the target `k`-th Ulm subgroup;
adding that correction to `yᵢ - C(eᵢ)` produces an order-`p` target element at
height `k` without changing its class modulo the old target mark. -/
theorem exists_room_linearIndependent_response_of_selectorKernel_nat
    {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b)
    (C : TupleIsoMap a b)
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (k : Ordinal.{0})))
    (hk : IsHeightFloorAt p C.equiv.toAddMonoidHom (k : Ordinal.{0}))
    (v : Fin m → LinearMap.ker
      (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → room p (tupleSubgroup a) (k : Ordinal.{0}),
      LinearIndependent (ZMod p) w := by
  choose x hx using fun i ↦
    (reachableDenSubmodule p (tupleSubgroup b) 0 (k : Ordinal.{0})).mkQ_surjective
      ((v i : LinearMap.ker
        (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
          reachableSpace p (tupleSubgroup b) 0 (k : Ordinal.{0}))
  let e : Fin m → H := fun i ↦
    reachableAnchor p (tupleSubgroup b) (k : Ordinal.{0}) (x i)
  have he : ∀ i, e i ∈ tupleSubgroup b := fun i ↦
    reachableAnchor_mem p (tupleSubgroup b) (k : Ordinal.{0}) (x i)
  have hres : ∀ i, (x i : H) - e i ∈
      ulmSubgroup p (k : Ordinal.{0}) := fun i ↦
    reachableResidual_mem p (tupleSubgroup b) (k : Ordinal.{0}) (x i)
  choose z hz using fun i ↦
    (mem_ulmSubgroup_nat_iff p k ((x i : H) - e i)).mp (hres i)
  let d : Fin (m + m) → H := Fin.append (fun i ↦ (x i : H)) z
  obtain ⟨c, ⟨C'⟩⟩ :=
    exists_finiteTuple_baseResponse_of_BFRel p (by norm_num) h d
  let first : Fin m → Fin (m + m) := fun i ↦ i.castAdd m
  have hdfirst : ∀ i, d (first i) = (x i : H) := by
    intro i
    change Fin.append (fun i ↦ (x i : H)) z (Fin.castAdd m i) = (x i : H)
    exact Fin.append_left _ _ i
  have hsource : LinearIndependent (ZMod p) (fun i ↦
      (roomSubmodule p (tupleSubgroup b) 0).mkQ
        (reachableNumToSocle p (tupleSubgroup b) (k : Ordinal.{0}) (x i))) := by
    have hvReach : LinearIndependent (ZMod p) (fun i ↦
        ((v i : LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
            reachableSpace p (tupleSubgroup b) 0 (k : Ordinal.{0}))) :=
      hv.map' (LinearMap.ker
        (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)).subtype
        (Submodule.ker_subtype _)
    have himage := hvReach.map_injOn
      (reachableToRoomZeroLinearMap p (tupleSubgroup b) (k : Ordinal.{0}))
      (reachableToRoomZeroLinearMap_injective
        p (tupleSubgroup b) (k : Ordinal.{0})).injOn
    simpa only [Function.comp_apply, ← hx,
      reachableToRoomZeroLinearMap_mk] using himage
  obtain ⟨y, hycoord, hyind⟩ :=
    exists_roomZero_linearIndependent_response p C d c C' first
      (fun i ↦ reachableNumToSocle p (tupleSubgroup b)
        (k : Ordinal.{0}) (x i))
      (fun i ↦ by
        rw [hdfirst i]
        rfl) hsource
  let rootCoord : Fin m → Fin (m + m) := fun i ↦ Fin.natAdd m i
  let targetRoot : Fin m → G := fun i ↦ c (rootCoord i)
  have hdroot : ∀ i, d (rootCoord i) = z i := by
    intro i
    change Fin.append (fun i ↦ (x i : H)) z (Fin.natAdd m i) = z i
    exact Fin.append_right _ _ i
  have hresponseEquation : ∀ i,
      (y i : G) - (C.equiv ⟨e i, he i⟩ : G) =
        p ^ k • targetRoot i := by
    intro i
    have hsourceEquation : (x i : H) = e i + p ^ k • z i := by
      rw [hz i]
      abel
    have hmapEquation := congrArg C'.equiv
      (show (⟨(x i : H), AddSubgroup.subset_closure
          (show (x i : H) ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
            tupleSubgroup (Fin.append b d)) =
          AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
              ⟨e i, he i⟩ +
            p ^ k •
              ⟨z i, AddSubgroup.subset_closure
                (show z i ∈ Set.range (Fin.append b d) from
                  ⟨Fin.natAdd n (rootCoord i), by
                    rw [Fin.append_right, hdroot i]⟩)⟩ by
        apply Subtype.ext
        exact hsourceEquation)
    have hxmap : (C'.equiv
        (⟨(x i : H), AddSubgroup.subset_closure
          (show (x i : H) ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
              tupleSubgroup (Fin.append b d)) : G) = c (first i) := by
      have hm := congrArg Subtype.val (C'.map_gen (Fin.natAdd n (first i)))
      simpa [d, first] using hm
    have hzmap : (C'.equiv
        (⟨z i, AddSubgroup.subset_closure
          (show z i ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (rootCoord i), by
              rw [Fin.append_right, hdroot i]⟩)⟩ :
              tupleSubgroup (Fin.append b d)) : G) = targetRoot i := by
      have hm := congrArg Subtype.val (C'.map_gen (Fin.natAdd n (rootCoord i)))
      simpa only [Fin.append_right, hdroot i, targetRoot] using hm
    have hemap : (C'.equiv
        (AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
          ⟨e i, he i⟩) : G) = (C.equiv ⟨e i, he i⟩ : G) :=
      (C.append_left_equiv_apply_eq C' ⟨e i, he i⟩).symm
    rw [map_add, map_nsmul] at hmapEquation
    have hambient : c (first i) =
        (C'.equiv
          (AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
            ⟨e i, he i⟩) : G) +
          p ^ k • (C'.equiv
            (⟨z i, AddSubgroup.subset_closure
              (show z i ∈ Set.range (Fin.append b d) from
                ⟨Fin.natAdd n (rootCoord i), by
                  rw [Fin.append_right, hdroot i]⟩)⟩ :
                tupleSubgroup (Fin.append b d)) : G) := by
      calc
        c (first i) = (C'.equiv
            (⟨(x i : H), AddSubgroup.subset_closure
              (show (x i : H) ∈ Set.range (Fin.append b d) from
                ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
                  tupleSubgroup (Fin.append b d)) : G) := hxmap.symm
        _ = (C'.equiv
              (AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
                ⟨e i, he i⟩) +
              p ^ k • C'.equiv
                (⟨z i, AddSubgroup.subset_closure
                  (show z i ∈ Set.range (Fin.append b d) from
                    ⟨Fin.natAdd n (rootCoord i), by
                      rw [Fin.append_right, hdroot i]⟩)⟩ :
                    tupleSubgroup (Fin.append b d)) : G) :=
          congrArg Subtype.val hmapEquation
        _ = _ := rfl
    rw [hycoord i, hambient, hemap, hzmap]
    abel
  have hcorrection : ∀ i, ∃ t : G,
      t ∈ tupleSubgroup a ∧
      t ∈ ulmSubgroup p (k : Ordinal.{0}) ∧
      p • t = (C.equiv ⟨p • e i, (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := by
    intro i
    have hker := (v i).property
    change jumpMap p C.equiv.toAddMonoidHom hsucc hk
        (reachableToJumpLinearMap p (tupleSubgroup b) (k : Ordinal.{0})
          ((v i : LinearMap.ker
            (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
              reachableSpace p (tupleSubgroup b) 0 (k : Ordinal.{0}))) = 0 at hker
    rw [← hx i, reachableToJumpLinearMap_mk_of_anchor p (tupleSubgroup b)
      (k : Ordinal.{0}) (x i) (e i) (he i) (hres i), jumpMap_mk] at hker
    have hden := (QuotientAddGroup.eq_zero_iff _).mp hker
    change ((jumpNumMap p C.equiv.toAddMonoidHom hsucc
      (reachableAnchorMultipleOf p (tupleSubgroup b) (k : Ordinal.{0})
        (x i) (e i) (he i) (hres i)) :
          jumpNum p (tupleSubgroup a) (k : Ordinal.{0})) : G) ∈
      jumpDen p (tupleSubgroup a) (k : Ordinal.{0}) at hden
    obtain ⟨t, ht, hpt⟩ := hden
    refine ⟨t, ht.1, ht.2, ?_⟩
    calc
      p • t = ((jumpNumMap p C.equiv.toAddMonoidHom hsucc
          (reachableAnchorMultipleOf p (tupleSubgroup b) (k : Ordinal.{0})
            (x i) (e i) (he i) (hres i)) :
              jumpNum p (tupleSubgroup a) (k : Ordinal.{0})) : G) := hpt
      _ = (C.equiv ⟨p • e i,
          (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := rfl
  choose t htE htk hpt using hcorrection
  let s : Fin m → pSocleAt p (k : Ordinal.{0}) (G := G) := fun i ↦
    ⟨(y i : G) - (C.equiv ⟨e i, he i⟩ : G) + t i, by
      rw [mem_pSocleAt]
      constructor
      · have hy0 : p • (y i : G) = 0 :=
          (mem_pSocleAt p 0 (y i : G)).1 (y i).property |>.1
        have hCmul : p • (C.equiv ⟨e i, he i⟩ : G) =
            (C.equiv ⟨p • e i,
              (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := by
          simpa using congrArg Subtype.val
            (C.equiv.toAddMonoidHom.map_nsmul ⟨e i, he i⟩ p).symm
        rw [smul_add, smul_sub, hy0, hCmul, hpt i]
        abel
      · exact (ulmSubgroup p (k : Ordinal.{0})).add_mem
          (hresponseEquation i ▸ by
            rw [mem_ulmSubgroup_nat_iff]
            exact ⟨targetRoot i, rfl⟩)
          (htk i)⟩
  let w : Fin m → room p (tupleSubgroup a) (k : Ordinal.{0}) := fun i ↦
    (roomSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ (s i)
  refine ⟨w, ?_⟩
  have hrestricted : LinearIndependent (ZMod p) (fun i ↦
      roomRestriction p (tupleSubgroup a) (show (0 : Ordinal.{0}) ≤ k by simp)
        (w i)) := by
    have heq : ∀ i,
        roomRestriction p (tupleSubgroup a) (show (0 : Ordinal.{0}) ≤ k by simp)
            (w i) =
          (roomSubmodule p (tupleSubgroup a) 0).mkQ (y i) := by
      intro i
      rw [roomRestriction_mk]
      apply (Submodule.Quotient.eq _).mpr
      constructor
      · change (s i : G) - (y i : G) ∈ tupleSubgroup a
        have hmem := (tupleSubgroup a).add_mem
          ((tupleSubgroup a).neg_mem (C.equiv ⟨e i, he i⟩).property)
          (htE i)
        convert hmem using 1
        dsimp [s]
        abel
      · exact (pSocleAt p 0).sub_mem
          (pSocleAt_antitone p (by simp) (s i).property) (y i).property
    simpa only [heq] using hyind
  exact (hrestricted.of_comp
    (roomRestriction p (tupleSubgroup a) (show (0 : Ordinal.{0}) ≤ k by simp)))

/-- The selector-kernel finite-family transfer at an arbitrary level of the
active block.  The challenge includes roots in `H_(omega·alpha)`; the even
boundary relation left after the challenge keeps the response roots in
`G_(omega·alpha)`, after which the rank-one room argument is unchanged. -/
theorem exists_room_linearIndependent_response_of_selectorKernel_block
    {alpha : Ordinal.{0}} {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b)
    (boundary : ∀ {r : ℕ} (d : Fin r → H) (c : Fin r → G),
      BFRelReverse p (2 * alpha) (n + r) (Fin.append b d) (Fin.append a c) →
        ∃ C' : TupleIsoMap (Fin.append a c) (Fin.append b d),
          ∀ gamma : Ordinal.{0}, gamma < ω * alpha →
            IsHeightFloorAt p C'.equiv.toAddMonoidHom gamma)
    (C : TupleIsoMap a b)
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (ω * alpha + k)))
    (hk : IsHeightFloorAt p C.equiv.toAddMonoidHom (ω * alpha + k))
    (v : Fin m → LinearMap.ker
      (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → room p (tupleSubgroup a) (ω * alpha + k),
      LinearIndependent (ZMod p) w := by
  choose x hx using fun i ↦
    (reachableDenSubmodule p (tupleSubgroup b) 0 (ω * alpha + k)).mkQ_surjective
      ((v i : LinearMap.ker
        (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
          reachableSpace p (tupleSubgroup b) 0 (ω * alpha + k))
  let e : Fin m → H := fun i ↦
    reachableAnchor p (tupleSubgroup b) (ω * alpha + k) (x i)
  have he : ∀ i, e i ∈ tupleSubgroup b := fun i ↦
    reachableAnchor_mem p (tupleSubgroup b) (ω * alpha + k) (x i)
  have hres : ∀ i, (x i : H) - e i ∈
      ulmSubgroup p (ω * alpha + k) := fun i ↦
    reachableResidual_mem p (tupleSubgroup b) (ω * alpha + k) (x i)
  choose z hzbase hz using fun i ↦
    (mem_ulmSubgroup_add_nat_iff p (ω * alpha) k ((x i : H) - e i)).mp
      (hres i)
  let d : Fin (m + m) → H := Fin.append (fun i ↦ (x i : H)) z
  have hstep : BFRel p (Order.succ (2 * alpha)) n a b := by
    simpa [Order.succ_eq_add_one] using h
  obtain ⟨c, hc⟩ := (BFRel_succ p (2 * alpha) n a b).mp hstep (m + m) d
  obtain ⟨C', hbaseFloor⟩ := boundary d c hc
  let first : Fin m → Fin (m + m) := fun i ↦ i.castAdd m
  have hdfirst : ∀ i, d (first i) = (x i : H) := by
    intro i
    change Fin.append (fun i ↦ (x i : H)) z (Fin.castAdd m i) = (x i : H)
    exact Fin.append_left _ _ i
  have hsource : LinearIndependent (ZMod p) (fun i ↦
      (roomSubmodule p (tupleSubgroup b) 0).mkQ
        (reachableNumToSocle p (tupleSubgroup b) (ω * alpha + k) (x i))) := by
    have hvReach : LinearIndependent (ZMod p) (fun i ↦
        ((v i : LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
            reachableSpace p (tupleSubgroup b) 0 (ω * alpha + k))) :=
      hv.map' (LinearMap.ker
        (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)).subtype
        (Submodule.ker_subtype _)
    have himage := hvReach.map_injOn
      (reachableToRoomZeroLinearMap p (tupleSubgroup b) (ω * alpha + k))
      (reachableToRoomZeroLinearMap_injective
        p (tupleSubgroup b) (ω * alpha + k)).injOn
    simpa only [Function.comp_apply, ← hx,
      reachableToRoomZeroLinearMap_mk] using himage
  obtain ⟨y, hycoord, hyind⟩ :=
    exists_roomZero_linearIndependent_response p C d c C' first
      (fun i ↦ reachableNumToSocle p (tupleSubgroup b)
        (ω * alpha + k) (x i))
      (fun i ↦ by rw [hdfirst i]; rfl) hsource
  let rootCoord : Fin m → Fin (m + m) := fun i ↦ Fin.natAdd m i
  let targetRoot : Fin m → G := fun i ↦ c (rootCoord i)
  have hdroot : ∀ i, d (rootCoord i) = z i := by
    intro i
    change Fin.append (fun i ↦ (x i : H)) z (Fin.natAdd m i) = z i
    exact Fin.append_right _ _ i
  have htargetRootBase : ∀ i, targetRoot i ∈
      ulmSubgroup p (ω * alpha) := by
    intro i
    by_cases halpha : alpha = 0
    · subst alpha
      simp
    · rw [mem_ulmSubgroup_limit_iff p
          ((Ordinal.isSuccLimit_iff_omega0_dvd).2
            ⟨mul_ne_zero omega0_ne_zero halpha, ⟨alpha, rfl⟩⟩)]
      intro gamma hgamma
      let sourceRoot : tupleSubgroup (Fin.append b d) :=
        ⟨z i, AddSubgroup.subset_closure
          (show z i ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (rootCoord i), by
              rw [Fin.append_right, hdroot i]⟩)⟩
      have hmapRoot : (C'.equiv sourceRoot : G) = targetRoot i := by
        have hm := congrArg Subtype.val (C'.map_gen (Fin.natAdd n (rootCoord i)))
        simpa only [Fin.append_right, hdroot i, sourceRoot, targetRoot] using hm
      rw [← hmapRoot]
      apply hbaseFloor gamma hgamma sourceRoot
      exact ulmSubgroup_antitone p hgamma.le (hzbase i)
  have hresponseEquation : ∀ i,
      (y i : G) - (C.equiv ⟨e i, he i⟩ : G) = p ^ k • targetRoot i := by
    intro i
    have hsourceEquation : (x i : H) = e i + p ^ k • z i := by
      rw [hz i]
      abel
    have hmapEquation := congrArg C'.equiv
      (show (⟨(x i : H), AddSubgroup.subset_closure
          (show (x i : H) ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
            tupleSubgroup (Fin.append b d)) =
          AddSubgroup.inclusion (tupleSubgroup_le_append_left b d) ⟨e i, he i⟩ +
            p ^ k • ⟨z i, AddSubgroup.subset_closure
              (show z i ∈ Set.range (Fin.append b d) from
                ⟨Fin.natAdd n (rootCoord i), by
                  rw [Fin.append_right, hdroot i]⟩)⟩ by
        apply Subtype.ext
        exact hsourceEquation)
    have hxmap : (C'.equiv
        (⟨(x i : H), AddSubgroup.subset_closure
          (show (x i : H) ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
              tupleSubgroup (Fin.append b d)) : G) = c (first i) := by
      have hm := congrArg Subtype.val (C'.map_gen (Fin.natAdd n (first i)))
      simpa [d, first] using hm
    have hzmap : (C'.equiv
        (⟨z i, AddSubgroup.subset_closure
          (show z i ∈ Set.range (Fin.append b d) from
            ⟨Fin.natAdd n (rootCoord i), by
              rw [Fin.append_right, hdroot i]⟩)⟩ :
              tupleSubgroup (Fin.append b d)) : G) = targetRoot i := by
      have hm := congrArg Subtype.val (C'.map_gen (Fin.natAdd n (rootCoord i)))
      simpa only [Fin.append_right, hdroot i, targetRoot] using hm
    have hemap : (C'.equiv
        (AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
          ⟨e i, he i⟩) : G) = (C.equiv ⟨e i, he i⟩ : G) :=
      (C.append_left_equiv_apply_eq C' ⟨e i, he i⟩).symm
    rw [map_add, map_nsmul] at hmapEquation
    have hambient : c (first i) =
        (C'.equiv (AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
          ⟨e i, he i⟩) : G) +
          p ^ k • (C'.equiv
            (⟨z i, AddSubgroup.subset_closure
              (show z i ∈ Set.range (Fin.append b d) from
                ⟨Fin.natAdd n (rootCoord i), by
                  rw [Fin.append_right, hdroot i]⟩)⟩ :
                tupleSubgroup (Fin.append b d)) : G) := by
      calc
        c (first i) = (C'.equiv
            (⟨(x i : H), AddSubgroup.subset_closure
              (show (x i : H) ∈ Set.range (Fin.append b d) from
                ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩ :
                  tupleSubgroup (Fin.append b d)) : G) := hxmap.symm
        _ = _ := congrArg Subtype.val hmapEquation
    rw [hycoord i, hambient, hemap, hzmap]
    abel
  have hcorrection : ∀ i, ∃ t : G,
      t ∈ tupleSubgroup a ∧ t ∈ ulmSubgroup p (ω * alpha + k) ∧
      p • t = (C.equiv ⟨p • e i, (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := by
    intro i
    have hker := (v i).property
    change jumpMap p C.equiv.toAddMonoidHom hsucc hk
        (reachableToJumpLinearMap p (tupleSubgroup b) (ω * alpha + k)
          ((v i : LinearMap.ker
            (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :
              reachableSpace p (tupleSubgroup b) 0 (ω * alpha + k))) = 0 at hker
    rw [← hx i, reachableToJumpLinearMap_mk_of_anchor p (tupleSubgroup b)
      (ω * alpha + k) (x i) (e i) (he i) (hres i), jumpMap_mk] at hker
    have hden := (QuotientAddGroup.eq_zero_iff _).mp hker
    change ((jumpNumMap p C.equiv.toAddMonoidHom hsucc
      (reachableAnchorMultipleOf p (tupleSubgroup b) (ω * alpha + k)
        (x i) (e i) (he i) (hres i)) :
          jumpNum p (tupleSubgroup a) (ω * alpha + k)) : G) ∈
      jumpDen p (tupleSubgroup a) (ω * alpha + k) at hden
    obtain ⟨t, ht, hpt⟩ := hden
    refine ⟨t, ht.1, ht.2, ?_⟩
    calc
      p • t = ((jumpNumMap p C.equiv.toAddMonoidHom hsucc
          (reachableAnchorMultipleOf p (tupleSubgroup b) (ω * alpha + k)
            (x i) (e i) (he i) (hres i)) :
              jumpNum p (tupleSubgroup a) (ω * alpha + k)) : G) := hpt
      _ = (C.equiv ⟨p • e i,
          (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := rfl
  choose t htE htk hpt using hcorrection
  let s : Fin m → pSocleAt p (ω * alpha + k) (G := G) := fun i ↦
    ⟨(y i : G) - (C.equiv ⟨e i, he i⟩ : G) + t i, by
      rw [mem_pSocleAt]
      constructor
      · have hy0 : p • (y i : G) = 0 :=
          (mem_pSocleAt p 0 (y i : G)).1 (y i).property |>.1
        have hCmul : p • (C.equiv ⟨e i, he i⟩ : G) =
            (C.equiv ⟨p • e i,
              (tupleSubgroup b).nsmul_mem (he i) p⟩ : G) := by
          simpa using congrArg Subtype.val
            (C.equiv.toAddMonoidHom.map_nsmul ⟨e i, he i⟩ p).symm
        rw [smul_add, smul_sub, hy0, hCmul, hpt i]
        abel
      · exact (ulmSubgroup p (ω * alpha + k)).add_mem
          (hresponseEquation i ▸
            (mem_ulmSubgroup_add_nat_iff p (ω * alpha) k _).2
              ⟨targetRoot i, htargetRootBase i, rfl⟩)
          (htk i)⟩
  let w : Fin m → room p (tupleSubgroup a) (ω * alpha + k) := fun i ↦
    (roomSubmodule p (tupleSubgroup a) (ω * alpha + k)).mkQ (s i)
  refine ⟨w, ?_⟩
  have hrestricted : LinearIndependent (ZMod p) (fun i ↦
      roomRestriction p (tupleSubgroup a)
        (show (0 : Ordinal.{0}) ≤ ω * alpha + k by simp) (w i)) := by
    have heq : ∀ i,
        roomRestriction p (tupleSubgroup a)
            (show (0 : Ordinal.{0}) ≤ ω * alpha + k by simp) (w i) =
          (roomSubmodule p (tupleSubgroup a) 0).mkQ (y i) := by
      intro i
      rw [roomRestriction_mk]
      apply (Submodule.Quotient.eq _).mpr
      constructor
      · change (s i : G) - (y i : G) ∈ tupleSubgroup a
        have hmem := (tupleSubgroup a).add_mem
          ((tupleSubgroup a).neg_mem (C.equiv ⟨e i, he i⟩).property)
          (htE i)
        convert hmem using 1
        dsimp [s]
        abel
      · exact (pSocleAt p 0).sub_mem
          (pSocleAt_antitone p (by simp) (s i).property) (y i).property
    simpa only [heq] using hyind
  exact hrestricted.of_comp
    (roomRestriction p (tupleSubgroup a)
      (show (0 : Ordinal.{0}) ≤ ω * alpha + k by simp))

/-- At a natural level with finite target filtered socle, rank-one
back-and-forth forces the complete selector-kernel budget.

If the selector kernel had larger rank than the target room, it would contain
an independent family of size `finrank(target room) + 1`.  The preceding
finite challenge transfers that family to the target room, contradicting its
finite dimension. -/
theorem kernelRoomBudgetAt_of_finite_targetSocle_nat
    {n k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b)
    (C : TupleIsoMap a b)
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (k : Ordinal.{0})))
    (hk : IsHeightFloorAt p C.equiv.toAddMonoidHom (k : Ordinal.{0}))
    (hfinite : Set.Finite
      (pSocleAt p (k : Ordinal.{0}) (G := G) : Set G)) :
    Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom
      (k : Ordinal.{0}) hsucc hk := by
  rw [Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le]
  letI : Finite (pSocleAt p (k : Ordinal.{0}) (G := G)) :=
    Set.finite_coe_iff.mpr hfinite
  letI : Finite (room p (tupleSubgroup a) (k : Ordinal.{0})) :=
    Finite.of_surjective
      (roomSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ
      (roomSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ_surjective
  letI : Module.Finite (ZMod p)
      (room p (tupleSubgroup a) (k : Ordinal.{0})) :=
    Module.Finite.of_finite
  by_contra hle
  have hlt : Module.rank (ZMod p)
        (room p (tupleSubgroup a) (k : Ordinal.{0})) <
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :=
    lt_of_not_ge hle
  have hfinrank_lt : (Module.finrank (ZMod p)
        (room p (tupleSubgroup a) (k : Ordinal.{0})) : Cardinal) <
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) := by
    rw [Module.finrank_eq_rank]
    exact hlt
  have hlarge : (Module.finrank (ZMod p)
          (room p (tupleSubgroup a) (k : Ordinal.{0})) + 1 : ℕ) ≤
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Cardinal.natCast_add_one_le_iff.mpr hfinrank_lt
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hlarge
  obtain ⟨w, hw⟩ :=
    exists_room_linearIndependent_response_of_selectorKernel_nat
      p h C hsucc hk v hv
  have hcard := hw.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  exact (Nat.not_succ_le_self
    (Module.finrank (ZMod p)
      (room p (tupleSubgroup a) (k : Ordinal.{0})))) hcard

/-- Rank-one back-and-forth forces the marked tuple map to preserve every
finite level of the ambient Ulm filtration.

For `x = p^k y` in the source marked subgroup, challenge with the one-element
tuple `(y)`.  The atomic response preserves the equation
`p^k y = x`; uniqueness of tuple-induced maps identifies the restriction of
that enlarged response with the original marked map.
-/
theorem exists_tupleIsoMap_natFloor_of_BFRel_one
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    ∃ C : TupleIsoMap a b,
      ∀ k : ℕ, IsHeightFloorAt p C.equiv.toAddMonoidHom (k : Ordinal.{0}) := by
  obtain ⟨C⟩ := tupleIsoMap_of_BFRel p 1 h
  refine ⟨C, ?_⟩
  intro k x hx
  rw [mem_ulmSubgroup_nat_iff] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  let d : Fin 1 → H := fun _ ↦ y
  obtain ⟨c, ⟨C'⟩⟩ :=
    exists_finiteTuple_baseResponse_of_BFRel p (by norm_num) h d
  let last : Fin (n + 1) := Fin.natAdd n 0
  let y' : tupleSubgroup (Fin.append b d) :=
    ⟨y, AddSubgroup.subset_closure
      (show y ∈ Set.range (Fin.append b d) from
        ⟨last, by simp [last, d]⟩)⟩
  have hC'y : (C'.equiv y' : G) = c 0 := by
    have hmap := congrArg Subtype.val (C'.map_gen last)
    simpa [last, y', d] using hmap
  let inclusion : tupleSubgroup b →+ tupleSubgroup (Fin.append b d) :=
    AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
  have hinc : inclusion x = p ^ k • y' := by
    apply Subtype.ext
    exact hy.symm
  refine ⟨c 0, ?_⟩
  calc
    p ^ k • c 0 = p ^ k • (C'.equiv y' : G) := by rw [hC'y]
    _ = (C'.equiv (p ^ k • y') : G) := by
      simpa using congrArg Subtype.val
        (C'.equiv.map_nsmul y' (p ^ k)).symm
    _ = (C'.equiv (inclusion x) : G) := by rw [hinc]
    _ = (C.equiv x : G) :=
      (C.append_left_equiv_apply_eq C' x).symm

/-- The finite-level floor forced by rank one is exactly the directional
height clause at odd parameter `0`, whose cap is `ω`.

If the source height is below `ω`, it is a natural level and the preceding
root-chain argument applies there.  If it reaches `ω`, applying that argument
at every natural level puts the image in the limit subgroup `G_ω`.
-/
theorem generatedHeightsDirectional_zero_of_BFRel_one
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    GeneratedHeightsDirectional p 0 ω a b := by
  obtain ⟨C, hnat⟩ := exists_tupleIsoMap_natFloor_of_BFRel_one p h
  refine ⟨C, ?_⟩
  intro x
  right
  constructor
  · simp
  · by_cases hsmall : ulmHeight p (x : H) <
        ((ω : Ordinal.{0}) : WithTop Ordinal.{0})
    · obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp hsmall.ne_top
      have hγω : γ < ω := by
        apply WithTop.coe_lt_coe.mp
        simpa [hγ] using hsmall
      obtain ⟨k, rfl⟩ := lt_omega0.1 hγω
      rw [min_eq_left hsmall.le, ← hγ]
      exact coe_le_ulmHeight_of_mem p (C.equiv x : G) (k : Ordinal.{0})
        (hnat k x (mem_ulmSubgroup_of_le_ulmHeight p (x : H)
          (k : Ordinal.{0}) (by simpa [hγ])))
    · have hlarge :
          ((ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            ulmHeight p (x : H) := le_of_not_gt hsmall
      rw [min_eq_right hlarge]
      apply coe_le_ulmHeight_of_mem p (C.equiv x : G) ω
      rw [mem_ulmSubgroup_limit_iff p Ordinal.isSuccLimit_omega0]
      intro β hβ
      obtain ⟨k, rfl⟩ := lt_omega0.1 hβ
      apply hnat k x
      apply mem_ulmSubgroup_of_le_ulmHeight p (x : H) (k : Ordinal.{0})
      exact (WithTop.coe_le_coe.mpr (natCast_lt_omega0 k).le).trans hlarge

/-- An odd-rank relation carries one tuple map which preserves every source
filtration level below the end of its active omega window.

The proof follows the rank recursion.  At a successor parameter, one outer
challenge chooses a finite root and an empty second challenge restores the
original orientation at the preceding odd rank.  At a limit parameter, the
limit relation is symmetric, so the same argument is available at every
smaller odd rank. -/
theorem exists_tupleIsoMap_oddFloorBelowCap_of_BFRel
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b) :
    ∃ C : TupleIsoMap a b, ∀ gamma : Ordinal.{0},
      gamma < ω * alpha + ω →
        IsHeightFloorAt p C.equiv.toAddMonoidHom gamma := by
  induction alpha using Ordinal.limitRecOn generalizing G H n with
  | zero =>
      obtain ⟨C, hnat⟩ := exists_tupleIsoMap_natFloor_of_BFRel_one p (by simpa using h)
      refine ⟨C, ?_⟩
      intro gamma hgamma
      obtain ⟨k, rfl⟩ := lt_omega0.1 (by simpa using hgamma)
      exact hnat k
  | succ alpha ih =>
      obtain ⟨C⟩ := tupleIsoMap_of_BFRel p (2 * (Order.succ alpha) + 1) h
      refine ⟨C, ?_⟩
      intro gamma hgamma x hx
      have hbaseEq : ω * (Order.succ alpha) = ω * alpha + ω := by
        rw [Ordinal.mul_succ]
      by_cases hlow : gamma < ω * (Order.succ alpha)
      · have hlower : BFRel p (2 * alpha + 1) n a b :=
          BFRel_antitone p (by
            have hle := (Ordinal.add_le_add_iff_right
              (a := 2 * alpha) (b := 2 * (Order.succ alpha)) 1).2
                (mul_le_mul_right (Order.le_succ alpha) 2)
            simpa only [Nat.cast_one] using hle) a b h
        obtain ⟨D, hD⟩ := ih hlower
        have hgamma' : gamma < ω * alpha + ω := by
          rw [← hbaseEq]
          exact hlow
        have hmem := hD gamma hgamma' x hx
        have heq := TupleIsoMap.equiv_apply_eq D C x
        change (C.equiv x : G) ∈ ulmSubgroup p gamma
        rw [← heq]
        exact hmem
      · have hbase : ω * (Order.succ alpha) ≤ gamma := le_of_not_gt hlow
        have htail : gamma - ω * (Order.succ alpha) < ω := by
          have := hgamma
          rw [← Ordinal.add_sub_cancel_of_le hbase,
            add_lt_add_iff_left] at this
          exact this
        obtain ⟨k, hk⟩ := lt_omega0.1 htail
        have hgammaEq : gamma = ω * (Order.succ alpha) + k := by
          rw [← hk, Ordinal.add_sub_cancel_of_le hbase]
        rw [hgammaEq] at hx ⊢
        obtain ⟨y, hybase, hpy⟩ :=
          (mem_ulmSubgroup_add_nat_iff p (ω * (Order.succ alpha)) k (x : H)).1 hx
        let d : Fin 1 → H := fun _ ↦ y
        have hstep : BFRel p (Order.succ (2 * alpha + 2)) n a b := by
          rw [← show 2 * (Order.succ alpha) + 1 =
              Order.succ (2 * alpha + 2) by
            rw [Ordinal.mul_succ]
            rfl]
          exact h
        obtain ⟨c, hc⟩ := (BFRel_succ p (2 * alpha + 2) n a b).mp hstep 1 d
        have hrev : BFRel (G := H) (H := G) p (2 * alpha + 2)
            (n + 1) (Fin.append b d) (Fin.append a c) :=
          (BFRelReverse_iff_BFRel_swap p (2 * alpha + 2) (n + 1)
            (Fin.append b d) (Fin.append a c)).mp hc
        have hrevSucc : BFRel (G := H) (H := G) p
            (Order.succ (2 * alpha + 1))
            (n + 1) (Fin.append b d) (Fin.append a c) := by
          simpa [Order.succ_eq_add_one, add_assoc, one_add_one_eq_two] using hrev
        obtain ⟨e, he⟩ := (BFRel_succ p (2 * alpha + 1) (n + 1)
          (Fin.append b d) (Fin.append a c)).mp hrevSucc 0 Fin.elim0
        have he0 : e = (Fin.elim0 : Fin 0 → H) := Subsingleton.elim _ _
        subst e
        have hsame : BFRel (G := G) (H := H) p (2 * alpha + 1)
            (n + 1) (Fin.append a c) (Fin.append b d) := by
          have he' : BFRelReverse (G := H) (H := G) p (2 * alpha + 1)
              (n + 1) (Fin.append a c) (Fin.append b d) := by
            simpa using he
          exact (BFRelReverse_iff_BFRel_swap p (2 * alpha + 1) (n + 1)
            (Fin.append a c) (Fin.append b d)).mp he'
        obtain ⟨D, hD⟩ := ih hsame
        let last : Fin (n + 1) := Fin.natAdd n 0
        let y' : tupleSubgroup (Fin.append b d) :=
          ⟨y, AddSubgroup.subset_closure
            (show y ∈ Set.range (Fin.append b d) from
              ⟨last, by simp [last, d]⟩)⟩
        have hDy : (D.equiv y' : G) = c 0 := by
          have hmap := congrArg Subtype.val (D.map_gen last)
          simpa [last, y', d] using hmap
        have hDbase : (D.equiv y' : G) ∈
            ulmSubgroup p (ω * (Order.succ alpha)) (G := G) := by
          rw [hbaseEq] at hybase
          rw [hbaseEq, mem_ulmSubgroup_limit_iff p
            (Ordinal.isSuccLimit_add (ω * alpha) Ordinal.isSuccLimit_omega0)]
          intro delta hdelta
          apply hD delta hdelta
          exact ulmSubgroup_antitone p hdelta.le hybase
        have hcbase : c 0 ∈
            ulmSubgroup p (ω * (Order.succ alpha)) (G := G) := by
          simpa [hDy] using hDbase
        refine (mem_ulmSubgroup_add_nat_iff p
          (ω * (Order.succ alpha)) k (C.equiv x : G)).2 ⟨c 0, hcbase, ?_⟩
        let inclusion : tupleSubgroup b →+
            tupleSubgroup (Fin.append b d) :=
          AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
        have hinc : inclusion x = p ^ k • y' := by
          apply Subtype.ext
          exact hpy.symm
        calc
          p ^ k • c 0 = p ^ k • (D.equiv y' : G) := by rw [hDy]
          _ = (D.equiv (p ^ k • y') : G) := by
            simpa using congrArg Subtype.val (D.equiv.map_nsmul y' (p ^ k)).symm
          _ = (D.equiv (inclusion x) : G) := by rw [hinc]
          _ = (C.equiv x : G) :=
            (C.append_left_equiv_apply_eq D x).symm
  | limit alpha halpha ih =>
      obtain ⟨C⟩ := tupleIsoMap_of_BFRel p (2 * alpha + 1) h
      refine ⟨C, ?_⟩
      intro gamma hgamma x hx
      by_cases hlow : gamma < ω * alpha
      · obtain ⟨delta, hdelta, r, hr, hgammaEq⟩ := (lt_mul_iff.mp hlow)
        have hrank : 2 * delta + 1 < 2 * alpha := by
          calc
            2 * delta + 1 < 2 * delta + 2 := by simp
            _ = 2 * (Order.succ delta) := by
              rw [Ordinal.mul_succ]
            _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
        have hlower : BFRel p (2 * delta + 1) n a b :=
          BFRel_antitone p
            (hrank.trans_le (Ordinal.le_add_right (2 * alpha) 1)).le a b h
        obtain ⟨D, hD⟩ := ih delta hdelta hlower
        have hgamma' : gamma < ω * delta + ω := by
          rw [hgammaEq]
          exact (add_lt_add_iff_left (ω * delta)).2 hr
        have hmem := hD gamma hgamma' x hx
        have heq := TupleIsoMap.equiv_apply_eq D C x
        change (C.equiv x : G) ∈ ulmSubgroup p gamma
        rw [← heq]
        exact hmem
      · have hbase : ω * alpha ≤ gamma := le_of_not_gt hlow
        have htail : gamma - ω * alpha < ω := by
          have := hgamma
          rw [← Ordinal.add_sub_cancel_of_le hbase,
            add_lt_add_iff_left] at this
          exact this
        obtain ⟨k, hk⟩ := lt_omega0.1 htail
        have hgammaEq : gamma = ω * alpha + k := by
          rw [← hk, Ordinal.add_sub_cancel_of_le hbase]
        rw [hgammaEq] at hx ⊢
        obtain ⟨y, hybase, hpy⟩ :=
          (mem_ulmSubgroup_add_nat_iff p (ω * alpha) k (x : H)).1 hx
        let d : Fin 1 → H := fun _ ↦ y
        have hstep : BFRel p (Order.succ alpha) n a b := by
          rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
          simpa [Order.succ_eq_add_one] using h
        obtain ⟨c, hc⟩ := (BFRel_succ p alpha n a b).mp hstep 1 d
        have hrev : BFRel (G := H) (H := G) p alpha
            (n + 1) (Fin.append b d) (Fin.append a c) :=
          (BFRelReverse_iff_BFRel_swap p alpha (n + 1)
            (Fin.append b d) (Fin.append a c)).mp hc
        have hsame : BFRel (G := G) (H := H) p alpha
            (n + 1) (Fin.append a c) (Fin.append b d) :=
          BFRel_symm_of_isSuccLimit p halpha
            (Fin.append b d) (Fin.append a c) hrev
        obtain ⟨D⟩ := tupleIsoMap_of_BFRel p alpha hsame
        let last : Fin (n + 1) := Fin.natAdd n 0
        let y' : tupleSubgroup (Fin.append b d) :=
          ⟨y, AddSubgroup.subset_closure
            (show y ∈ Set.range (Fin.append b d) from
              ⟨last, by simp [last, d]⟩)⟩
        have hDy : (D.equiv y' : G) = c 0 := by
          have hmap := congrArg Subtype.val (D.map_gen last)
          simpa [last, y', d] using hmap
        have hDbase : (D.equiv y' : G) ∈
            ulmSubgroup p (ω * alpha) (G := G) := by
          rw [mem_ulmSubgroup_limit_iff p
            (Ordinal.isSuccLimit_mul_right omega0_pos halpha)]
          intro eta heta
          obtain ⟨delta, hdelta, r, hr, hetaEq⟩ := (lt_mul_iff.mp heta)
          have hrank : 2 * delta + 1 < alpha := by
            rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
            calc
              2 * delta + 1 < 2 * delta + 2 := by simp
              _ = 2 * (Order.succ delta) := by
                rw [Ordinal.mul_succ]
              _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
          have hlower : BFRel (G := G) (H := H) p (2 * delta + 1)
              (n + 1) (Fin.append a c) (Fin.append b d) :=
            BFRel_antitone p hrank.le _ _ hsame
          obtain ⟨E, hE⟩ := ih delta hdelta hlower
          have heta' : eta < ω * delta + ω := by
            rw [hetaEq]
            exact (add_lt_add_iff_left (ω * delta)).2 hr
          have hmem := hE eta heta' y'
            (ulmSubgroup_antitone p heta.le hybase)
          have heq := TupleIsoMap.equiv_apply_eq E D y'
          change (D.equiv y' : G) ∈ ulmSubgroup p eta
          rw [← heq]
          exact hmem
        have hcbase : c 0 ∈ ulmSubgroup p (ω * alpha) (G := G) := by
          simpa [hDy] using hDbase
        refine (mem_ulmSubgroup_add_nat_iff p
          (ω * alpha) k (C.equiv x : G)).2 ⟨c 0, hcbase, ?_⟩
        let inclusion : tupleSubgroup b →+
            tupleSubgroup (Fin.append b d) :=
          AddSubgroup.inclusion (tupleSubgroup_le_append_left b d)
        have hinc : inclusion x = p ^ k • y' := by
          apply Subtype.ext
          exact hpy.symm
        calc
          p ^ k • c 0 = p ^ k • (D.equiv y' : G) := by rw [hDy]
          _ = (D.equiv (p ^ k • y') : G) := by
            simpa using congrArg Subtype.val (D.equiv.map_nsmul y' (p ^ k)).symm
          _ = (D.equiv (inclusion x) : G) := by rw [hinc]
          _ = (C.equiv x : G) :=
            (C.append_left_equiv_apply_eq D x).symm

/-- An even boundary relation, read in the opposite orientation, carries a
tuple map preserving every filtration level strictly below its omega base.

At a successor boundary, the empty challenge exposes the preceding odd
relation.  At a limit boundary, symmetry of the limit relation and cofinal
lower odd ranks provide the same floors. -/
theorem exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha) n a b) :
    ∃ C : TupleIsoMap b a, ∀ gamma : Ordinal.{0},
      gamma < ω * alpha → IsHeightFloorAt p C.equiv.toAddMonoidHom gamma := by
  induction alpha using Ordinal.limitRecOn generalizing G H n with
  | zero =>
      obtain ⟨D⟩ := tupleIsoMap_of_BFRel p 0 (by simpa using h)
      refine ⟨D.symm, ?_⟩
      intro gamma hgamma
      simp at hgamma
  | succ alpha _ih =>
      have hstep : BFRel p (Order.succ (2 * alpha + 1)) n a b := by
        rw [← show 2 * (Order.succ alpha) =
            Order.succ (2 * alpha + 1) by
          calc
            2 * (Order.succ alpha) = 2 * alpha + 2 := by
              rw [Ordinal.mul_succ]
            _ = 2 * alpha + (1 + 1) := by norm_num
            _ = (2 * alpha + 1) + 1 := (add_assoc _ _ _).symm
            _ = Order.succ (2 * alpha + 1) := rfl]
        exact h
      obtain ⟨d, hd⟩ := (BFRel_succ p (2 * alpha + 1) n a b).mp
        hstep 0 Fin.elim0
      have hd0 : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
      subst d
      have hswap : BFRel (G := H) (H := G) p (2 * alpha + 1) n b a := by
        have hd' : BFRelReverse p (2 * alpha + 1) n b a := by
          simpa using hd
        exact (BFRelReverse_iff_BFRel_swap p (2 * alpha + 1) n b a).mp hd'
      obtain ⟨C, hC⟩ := exists_tupleIsoMap_oddFloorBelowCap_of_BFRel p hswap
      refine ⟨C, ?_⟩
      intro gamma hgamma
      apply hC gamma
      simpa only [Ordinal.mul_succ] using hgamma
  | limit alpha halpha _ih =>
      have hlimit : BFRel p alpha n a b := by
        rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
        exact h
      have hswap : BFRel (G := H) (H := G) p alpha n b a :=
        BFRel_symm_of_isSuccLimit p halpha a b hlimit
      obtain ⟨C⟩ := tupleIsoMap_of_BFRel p alpha hswap
      refine ⟨C, ?_⟩
      intro gamma hgamma
      obtain ⟨delta, hdelta, r, hr, hgammaEq⟩ := lt_mul_iff.mp hgamma
      have hrank : 2 * delta + 1 < alpha := by
        rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
        calc
          2 * delta + 1 < 2 * delta + 2 := by simp
          _ = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
          _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
      have hlower : BFRel (G := H) (H := G) p (2 * delta + 1) n b a :=
        BFRel_antitone p hrank.le b a hswap
      obtain ⟨D, hD⟩ := exists_tupleIsoMap_oddFloorBelowCap_of_BFRel p hlower
      have hgamma' : gamma < ω * delta + ω := by
        rw [hgammaEq]
        exact (add_lt_add_iff_left (ω * delta)).2 hr
      intro x hx
      have hmem := hD gamma hgamma' x hx
      have heq := TupleIsoMap.equiv_apply_eq D C x
      change (C.equiv x : H) ∈ ulmSubgroup p gamma
      rw [← heq]
      exact hmem

/-- Filtration floors strictly below a successor-limit cap give the truncated
height inequality at that cap. -/
theorem min_ulmHeight_le_of_floorBelow
    {F : AddSubgroup H} {E : AddSubgroup G} (f : F →+ E)
    {theta : Ordinal.{0}} (htheta : Order.IsSuccLimit theta)
    (hfloor : ∀ gamma : Ordinal.{0}, gamma < theta →
      IsHeightFloorAt p f gamma) (x : F) :
    min (ulmHeight p (x : H)) (theta : WithTop Ordinal.{0}) ≤
      ulmHeight p (f x : G) := by
  by_cases hsmall : ulmHeight p (x : H) <
      (theta : WithTop Ordinal.{0})
  · obtain ⟨beta, hbeta⟩ := WithTop.ne_top_iff_exists.mp hsmall.ne_top
    have hbetaTheta : beta < theta := by
      rw [← hbeta] at hsmall
      exact WithTop.coe_lt_coe.mp hsmall
    rw [min_eq_left hsmall.le, ← hbeta]
    apply coe_le_ulmHeight_of_mem p (f x : G) beta
    apply hfloor beta hbetaTheta x
    apply mem_ulmSubgroup_of_le_ulmHeight p (x : H) beta
    rw [← hbeta]
  · have hlarge : (theta : WithTop Ordinal.{0}) ≤
        ulmHeight p (x : H) := le_of_not_gt hsmall
    rw [min_eq_right hlarge]
    apply coe_le_ulmHeight_of_mem p (f x : G) theta
    rw [mem_ulmSubgroup_limit_iff p htheta]
    intro gamma hgamma
    apply hfloor gamma hgamma x
    apply mem_ulmSubgroup_of_le_ulmHeight p (x : H) gamma
    exact (WithTop.coe_le_coe.mpr hgamma.le).trans hlarge

/-- General odd rank forces the directional marked-height clause, with one
chosen tuple map shared by all later odd fields. -/
theorem generatedHeightsDirectional_of_BFRel_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b) :
    GeneratedHeightsDirectional p (ω * alpha) (ω * alpha + ω) a b := by
  obtain ⟨C, hforward⟩ := exists_tupleIsoMap_oddFloorBelowCap_of_BFRel p h
  have hstep : BFRel p (Order.succ (2 * alpha)) n a b := by
    simpa [Order.succ_eq_add_one] using h
  obtain ⟨e, he⟩ := (BFRel_succ p (2 * alpha) n a b).mp hstep 0 Fin.elim0
  have he0 : e = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst e
  have hswap : BFRel (G := H) (H := G) p (2 * alpha) n b a := by
    have he' : BFRelReverse p (2 * alpha) n b a := by
      simpa using he
    exact (BFRelReverse_iff_BFRel_swap p (2 * alpha) n b a).mp he'
  have hinverse : ∀ gamma : Ordinal.{0}, gamma < ω * alpha →
      IsHeightFloorAt p C.equiv.symm.toAddMonoidHom gamma := by
    intro gamma hgamma
    obtain ⟨delta, hdelta, r, hr, hgammaEq⟩ := lt_mul_iff.mp hgamma
    have hrank : 2 * delta + 1 < 2 * alpha := by
      calc
        2 * delta + 1 < 2 * delta + 2 := by simp
        _ = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
        _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
    have hlower : BFRel (G := H) (H := G) p (2 * delta + 1) n b a :=
      BFRel_antitone p hrank.le b a hswap
    obtain ⟨D, hD⟩ := exists_tupleIsoMap_oddFloorBelowCap_of_BFRel p hlower
    have hgamma' : gamma < ω * delta + ω := by
      rw [hgammaEq]
      exact (add_lt_add_iff_left (ω * delta)).2 hr
    intro x hx
    have hmem := hD gamma hgamma' x hx
    have heq := TupleIsoMap.equiv_apply_eq D C.symm x
    change (C.symm.equiv x : H) ∈ ulmSubgroup p gamma
    rw [← heq]
    exact hmem
  have hpres : IsHeightPresBelowOn p C.equiv.toAddMonoidHom (ω * alpha) := by
    intro gamma hgamma x
    constructor
    · exact hforward gamma (hgamma.trans_le (Ordinal.le_add_right _ _)) x
    · intro hx
      have hmem := hinverse gamma hgamma (C.equiv x) hx
      simpa using hmem
  have hbasePre : Order.IsSuccPrelimit (ω * alpha) :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.2 ⟨alpha, rfl⟩
  have hmatch := heightsMatchBelow_of_heightPresBelowOn
    p hG hH hbasePre C hpres
  refine ⟨C, fun x ↦ ?_⟩
  rcases hmatch x with hlow | hhigh
  · exact Or.inl hlow
  · exact Or.inr ⟨hhigh.1,
      min_ulmHeight_le_of_floorBelow p C.equiv.toAddMonoidHom
        (Ordinal.isSuccLimit_add (ω * alpha) Ordinal.isSuccLimit_omega0)
        hforward x⟩

/-- At a finite target filtered socle, the relativized selector challenge
forces the exact room--kernel budget at `omega·alpha+k`. -/
theorem kernelRoomBudgetAt_of_finite_targetSocle_block
    {alpha : Ordinal.{0}} {n k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b)
    (C : TupleIsoMap a b)
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (ω * alpha + k)))
    (hk : IsHeightFloorAt p C.equiv.toAddMonoidHom (ω * alpha + k))
    (hfinite : Set.Finite
      (pSocleAt p (ω * alpha + k) (G := G) : Set G)) :
    Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom
      (ω * alpha + k) hsucc hk := by
  rw [Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le]
  letI : Finite (pSocleAt p (ω * alpha + k) (G := G)) :=
    Set.finite_coe_iff.mpr hfinite
  letI : Finite (room p (tupleSubgroup a) (ω * alpha + k)) :=
    Finite.of_surjective
      (roomSubmodule p (tupleSubgroup a) (ω * alpha + k)).mkQ
      (roomSubmodule p (tupleSubgroup a) (ω * alpha + k)).mkQ_surjective
  letI : Module.Finite (ZMod p)
      (room p (tupleSubgroup a) (ω * alpha + k)) :=
    Module.Finite.of_finite
  by_contra hle
  have hlt : Module.rank (ZMod p)
        (room p (tupleSubgroup a) (ω * alpha + k)) <
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) :=
    lt_of_not_ge hle
  have hfinrank_lt : (Module.finrank (ZMod p)
        (room p (tupleSubgroup a) (ω * alpha + k)) : Cardinal) <
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) := by
    rw [Module.finrank_eq_rank]
    exact hlt
  have hlarge : (Module.finrank (ZMod p)
          (room p (tupleSubgroup a) (ω * alpha + k)) + 1 : ℕ) ≤
      Module.rank (ZMod p)
        (LinearMap.ker
          (KernelRoom.selectorResidueMap p C.equiv.toAddMonoidHom hsucc hk)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Cardinal.natCast_add_one_le_iff.mpr hfinrank_lt
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hlarge
  obtain ⟨w, hw⟩ :=
    exists_room_linearIndependent_response_of_selectorKernel_block p h
      (fun d c hc ↦
        exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p
          ((BFRelReverse_iff_BFRel_swap p (2 * alpha) _
            (Fin.append b d) (Fin.append a c)).mp hc))
      C hsucc hk v hv
  have hcard := hw.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  exact (Nat.not_succ_le_self
    (Module.finrank (ZMod p)
      (room p (tupleSubgroup a) (ω * alpha + k)))) hcard

/-- At every natural level, rank-one back-and-forth transfers nonvanishing of
the source Ulm subgroup to nonvanishing of the target Ulm subgroup.

Choose a nonzero `x = p^k y` at that level and challenge with `y`.  Atomicity
of the response preserves the nonzero equation `p^k y = x`.
-/
theorem ulmSubgroup_nat_ne_bot_of_BFRel_one
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) (k : ℕ)
    (hne : ulmSubgroup p (k : Ordinal.{0}) (G := H) ≠ ⊥) :
    ulmSubgroup p (k : Ordinal.{0}) (G := G) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hx0
    simpa [hxzero]
  rw [mem_ulmSubgroup_nat_iff] at hx
  obtain ⟨y, hy⟩ := hx
  let d : Fin 1 → H := fun _ ↦ y
  obtain ⟨c, ⟨C'⟩⟩ :=
    exists_finiteTuple_baseResponse_of_BFRel p (by norm_num) h d
  let last : Fin (n + 1) := Fin.natAdd n 0
  let y' : tupleSubgroup (Fin.append b d) :=
    ⟨y, AddSubgroup.subset_closure
      (show y ∈ Set.range (Fin.append b d) from
        ⟨last, by simp [last, d]⟩)⟩
  have hC'y : (C'.equiv y' : G) = c 0 := by
    have hmap := congrArg Subtype.val (C'.map_gen last)
    simpa [last, y', d] using hmap
  let z : G := p ^ k • c 0
  have hzmem : z ∈ ulmSubgroup p (k : Ordinal.{0}) (G := G) := by
    rw [mem_ulmSubgroup_nat_iff]
    exact ⟨c 0, rfl⟩
  intro hbot
  have hz0 : z = 0 := by
    rw [hbot] at hzmem
    simpa using hzmem
  have hmapPow : (C'.equiv (p ^ k • y') : G) = z := by
    calc
      (C'.equiv (p ^ k • y') : G) = p ^ k • (C'.equiv y' : G) := by
        simpa using congrArg Subtype.val (C'.equiv.map_nsmul y' (p ^ k))
      _ = z := by rw [hC'y]
  have hCzero : C'.equiv (p ^ k • y') = 0 := by
    apply Subtype.ext
    exact hmapPow.trans hz0
  have hsourceZero : p ^ k • y' = 0 :=
    C'.equiv.injective (by simpa using hCzero)
  apply hxne
  rw [← hy]
  exact congrArg Subtype.val hsourceZero

/-- Below the Ulm length the filtration has not yet vanished. -/
theorem ulmSubgroup_ne_bot_of_lt_ulmLength
    (hH : IsReducedPGroup p H) {β : Ordinal.{0}}
    (hβ : β < ulmLength p (G := H) hH) :
    ulmSubgroup p β (G := H) ≠ ⊥ := by
  intro hbot
  have hle : ulmLength p (G := H) hH ≤ β := by
    unfold ulmLength
    exact csInf_le' hbot
  exact (not_le_of_gt hβ) hle

/-- General odd rank transfers nonvanishing of every source Ulm subgroup
strictly below the end of its active omega window.

Below the base, the even-boundary response map directly preserves the
filtration.  In the active block, challenge a base-tail root as well; the same
map keeps that root in the target base and atomicity preserves the finite
power equation. -/
theorem ulmSubgroup_ne_bot_of_BFRel_odd
    {alpha gamma : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b)
    (hgamma : gamma < ω * alpha + ω)
    (hne : ulmSubgroup p gamma (G := H) ≠ ⊥) :
    ulmSubgroup p gamma (G := G) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hx0
    simpa [hxzero]
  have hstep : BFRel p (Order.succ (2 * alpha)) n a b := by
    simpa [Order.succ_eq_add_one] using h
  by_cases hlow : gamma < ω * alpha
  · let d : Fin 1 → H := fun _ ↦ x
    obtain ⟨c, hc⟩ := (BFRel_succ p (2 * alpha) n a b).mp hstep 1 d
    have hrev : BFRel (G := H) (H := G) p (2 * alpha) (n + 1)
        (Fin.append b d) (Fin.append a c) :=
      (BFRelReverse_iff_BFRel_swap p (2 * alpha) (n + 1)
        (Fin.append b d) (Fin.append a c)).mp hc
    obtain ⟨C, hfloor⟩ :=
      exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p hrev
    let last : Fin (n + 1) := Fin.natAdd n 0
    let challenge : tupleSubgroup (Fin.append b d) :=
      ⟨x, AddSubgroup.subset_closure
        (show x ∈ Set.range (Fin.append b d) from
          ⟨last, by simp [last, d]⟩)⟩
    let response : tupleSubgroup (Fin.append a c) :=
      ⟨c 0, AddSubgroup.subset_closure
        (show c 0 ∈ Set.range (Fin.append a c) from
          ⟨last, by simp [last]⟩)⟩
    have hmap : C.equiv challenge = response := by
      have hm := C.map_gen last
      apply Subtype.ext
      simpa [last, challenge, response, d] using congrArg Subtype.val hm
    have hmem : (response : G) ∈ ulmSubgroup p gamma := by
      rw [← hmap]
      exact hfloor gamma hlow challenge hx
    intro hbot
    have hzero : (response : G) = 0 := by
      rw [hbot] at hmem
      simpa using hmem
    apply hxne
    have hchallengeZero : challenge = 0 := by
      apply C.equiv.injective
      rw [hmap, map_zero]
      apply Subtype.ext
      exact hzero
    exact congrArg Subtype.val hchallengeZero
  · have hbase : ω * alpha ≤ gamma := le_of_not_gt hlow
    have htail : gamma - ω * alpha < ω := by
      have := hgamma
      rw [← Ordinal.add_sub_cancel_of_le hbase, add_lt_add_iff_left] at this
      exact this
    obtain ⟨k, hk⟩ := lt_omega0.1 htail
    have hgammaEq : gamma = ω * alpha + k := by
      rw [← hk, Ordinal.add_sub_cancel_of_le hbase]
    obtain ⟨y, hybase, hpy⟩ :=
      (mem_ulmSubgroup_add_nat_iff p (ω * alpha) k x).1
        (hgammaEq ▸ hx)
    let d : Fin (1 + 1) → H := Fin.append (fun _ : Fin 1 ↦ x) (fun _ ↦ y)
    obtain ⟨c, hc⟩ := (BFRel_succ p (2 * alpha) n a b).mp hstep 2 d
    have hrev : BFRel (G := H) (H := G) p (2 * alpha) (n + 2)
        (Fin.append b d) (Fin.append a c) := by
      simpa only [one_add_one_eq_two] using
        (BFRelReverse_iff_BFRel_swap p (2 * alpha) (n + 2)
          (Fin.append b d) (Fin.append a c)).mp hc
    obtain ⟨C, hfloor⟩ :=
      exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p hrev
    let first : Fin 2 := Fin.castAdd 1 (0 : Fin 1)
    let root : Fin 2 := Fin.natAdd 1 (0 : Fin 1)
    let challenge (j : Fin 2) : tupleSubgroup (Fin.append b d) :=
      ⟨d j, AddSubgroup.subset_closure
        (show d j ∈ Set.range (Fin.append b d) from
          ⟨Fin.natAdd n j, by simp⟩)⟩
    let response (j : Fin 2) : tupleSubgroup (Fin.append a c) :=
      ⟨c j, AddSubgroup.subset_closure
        (show c j ∈ Set.range (Fin.append a c) from
          ⟨Fin.natAdd n j, by simp⟩)⟩
    have hmap : ∀ j, C.equiv (challenge j) = response j := by
      intro j
      have hm := C.map_gen (Fin.natAdd n j)
      apply Subtype.ext
      simpa [challenge, response] using congrArg Subtype.val hm
    have hdfirst : d first = x := by
      exact Fin.append_left (fun _ : Fin 1 ↦ x) (fun _ ↦ y) 0
    have hdroot : d root = y := by
      exact Fin.append_right (fun _ : Fin 1 ↦ x) (fun _ ↦ y) 0
    have hresponseEq : p ^ k • response root = response first := by
      have hsourceEq : p ^ k • challenge root = challenge first := by
        apply Subtype.ext
        change p ^ k • d root = d first
        rw [hdfirst, hdroot]
        exact hpy
      have hmapped := congrArg C.equiv hsourceEq
      simpa only [map_nsmul, hmap] using hmapped
    have hresponseRootBase : (response root : G) ∈
        ulmSubgroup p (ω * alpha) := by
      by_cases halpha : alpha = 0
      · subst alpha
        simp
      · rw [mem_ulmSubgroup_limit_iff p
            ((Ordinal.isSuccLimit_iff_omega0_dvd).2
              ⟨mul_ne_zero omega0_ne_zero halpha, ⟨alpha, rfl⟩⟩)]
        intro eta heta
        rw [← hmap root]
        apply hfloor eta heta (challenge root)
        change d root ∈ ulmSubgroup p eta
        rw [hdroot]
        exact ulmSubgroup_antitone p heta.le hybase
    have hresponseMem : (response first : G) ∈
        ulmSubgroup p gamma := by
      rw [hgammaEq]
      exact (mem_ulmSubgroup_add_nat_iff p (ω * alpha) k _).2
        ⟨response root, hresponseRootBase,
          congrArg Subtype.val hresponseEq⟩
    intro hbot
    have hzero : (response first : G) = 0 := by
      rw [hbot] at hresponseMem
      simpa using hresponseMem
    apply hxne
    have hchallengeZero : challenge first = 0 := by
      apply C.equiv.injective
      rw [hmap, map_zero]
      apply Subtype.ext
      exact hzero
    rw [← hdfirst]
    exact congrArg Subtype.val hchallengeZero

/-- The odd length alternative at an arbitrary omega block follows from
nonvanishing transfer through the active cap, together with the reversed
lower odd relations below the base. -/
theorem odd_lengths_of_BFRel
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b) :
    ((ulmLength p (G := G) hG : Ordinal.{0}) =
        (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * alpha) ∨
    (ω * alpha ≤ (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * alpha + ω) ≤
        (ulmLength p (G := G) hG : Ordinal.{0})) := by
  have hcap : min (ulmLength p (G := H) hH : Ordinal.{0})
        (ω * alpha + ω) ≤ (ulmLength p (G := G) hG : Ordinal.{0}) := by
    apply le_of_not_gt
    intro hbad
    have hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) <
        ω * alpha + ω := hbad.trans_le (min_le_right _ _)
    have hGH : (ulmLength p (G := G) hG : Ordinal.{0}) <
        (ulmLength p (G := H) hH : Ordinal.{0}) :=
      hbad.trans_le (min_le_left _ _)
    have hneH := ulmSubgroup_ne_bot_of_lt_ulmLength p hH hGH
    have hneG := ulmSubgroup_ne_bot_of_BFRel_odd p h hGcap hneH
    apply hneG
    exact ulmLength.at_ulmLength (p := p) (hred := hG)
  by_cases hHbase : (ulmLength p (G := H) hH : Ordinal.{0}) < ω * alpha
  · left
    have hHG : (ulmLength p (G := H) hH : Ordinal.{0}) ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) :=
      (min_eq_left (hHbase.le.trans le_self_add)) ▸ hcap
    have hGH : (ulmLength p (G := G) hG : Ordinal.{0}) ≤
        (ulmLength p (G := H) hH : Ordinal.{0}) := by
      apply le_of_not_gt
      intro hbad
      obtain ⟨delta, hdelta, r, hr, hHEq⟩ := lt_mul_iff.mp hHbase
      have hrank : 2 * delta + 1 < 2 * alpha := by
        calc
          2 * delta + 1 < 2 * delta + 2 := by simp
          _ = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
          _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
      have hlower : BFRel p (2 * delta + 1) n a b :=
        BFRel_antitone p (hrank.trans_le le_self_add).le a b h
      have htwoSucc : 2 * delta + 2 ≤ 2 * alpha := by
        calc
          2 * delta + 2 = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
          _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
      have hstep : BFRel p (Order.succ (2 * delta)) n a b := by
        simpa [Order.succ_eq_add_one] using hlower
      obtain ⟨d, hd⟩ := (BFRel_succ p (2 * delta) n a b).mp
        hstep 0 Fin.elim0
      have hd0 : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
      subst d
      have hswap : BFRel (G := H) (H := G) p (2 * delta) n b a := by
        have hd' : BFRelReverse p (2 * delta) n b a := by simpa using hd
        exact (BFRelReverse_iff_BFRel_swap p (2 * delta) n b a).mp hd'
      have hswapOdd : BFRel (G := H) (H := G) p (2 * delta + 1) n b a := by
        -- Use the original relation one rank higher before the empty response.
        exact (BFRelReverse_iff_BFRel_swap p (2 * delta + 1) n b a).mp
          (by
            have hrel : BFRel p (Order.succ (2 * delta + 1)) n a b := by
              have hr := BFRel_antitone p (htwoSucc.trans le_self_add) a b h
              rw [show Order.succ (2 * delta + 1) = 2 * delta + 2 by
                calc
                  Order.succ (2 * delta + 1) = (2 * delta + 1) + 1 := rfl
                  _ = 2 * delta + (1 + 1) := add_assoc _ _ _
                  _ = 2 * delta + 2 := by norm_num]
              exact hr
            have hs := (BFRel_succ p (2 * delta + 1) n a b).mp
              hrel 0 Fin.elim0
            obtain ⟨e, he⟩ := hs
            have he0 : e = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
            subst e
            simpa using he)
      have hneG : ulmSubgroup p (ulmLength p (G := H) hH) (G := G) ≠ ⊥ :=
        ulmSubgroup_ne_bot_of_lt_ulmLength p hG hbad
      have hlevelCap : (ulmLength p (G := H) hH : Ordinal.{0}) <
          ω * delta + ω := by
        rw [hHEq]
        exact (add_lt_add_iff_left (ω * delta)).2 hr
      have hneH := ulmSubgroup_ne_bot_of_BFRel_odd p hswapOdd hlevelCap hneG
      apply hneH
      exact ulmLength.at_ulmLength (p := p) (hred := hH)
    exact ⟨le_antisymm hGH hHG, hGH.trans_lt hHbase⟩
  · exact Or.inr ⟨le_of_not_gt hHbase, hcap⟩

/-- Rank-one back-and-forth forces the odd base length inequality in arbitrary
reduced ambient groups. -/
theorem length_min_omega_le_of_BFRel_one
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    min (ulmLength p (G := H) hH : Ordinal.{0}) ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}) := by
  apply le_of_not_gt
  intro hbad
  have hGω : (ulmLength p (G := G) hG : Ordinal.{0}) < ω :=
    hbad.trans_le (min_le_right _ _)
  obtain ⟨k, hk⟩ := lt_omega0.1 hGω
  have hkH : (k : Ordinal.{0}) < ulmLength p (G := H) hH := by
    rw [← hk]
    exact hbad.trans_le (min_le_left _ _)
  have hneH : ulmSubgroup p (k : Ordinal.{0}) (G := H) ≠ ⊥ :=
    ulmSubgroup_ne_bot_of_lt_ulmLength p hH hkH
  have hneG : ulmSubgroup p (k : Ordinal.{0}) (G := G) ≠ ⊥ :=
    ulmSubgroup_nat_ne_bot_of_BFRel_one p h k hneH
  apply hneG
  rw [← hk]
  exact ulmLength.at_ulmLength (p := p) (hred := hG)

/-- At a level where the target filtered socle is infinite, the room--kernel
budget is automatic for finite marked subgroups in countable ambient groups.

Removing a finite mark from an infinite filtered socle leaves countably
infinite target room.  Source room has dimension at most `ℵ₀`, and the jump
kernel of a finite marked source is finite-dimensional, so their sum still
fits into that target room.  Thus the genuine necessity problem is confined
to levels with finite target filtered socle. -/
theorem kernelRoomBudgetAt_of_infinite_targetSocle
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (C : TupleIsoMap a b) (β : Ordinal.{0})
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom (Order.succ β))
    (hβ : IsHeightFloorAt p C.equiv.toAddMonoidHom β)
    (hinfinite : Set.Infinite (pSocleAt p β (G := G) : Set G)) :
    Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β hsucc hβ := by
  have hsourceFinite : Set.Finite (tupleSubgroup b : Set H) :=
    tupleSubgroup_finite p hH.primary b
  have htargetFinite : Set.Finite (tupleSubgroup a : Set G) :=
    tupleSubgroup_finite p hG.primary a
  have htargetRoom :
      roomInvariant p (tupleSubgroup a) β = Cardinal.aleph0 :=
    roomInvariant_eq_aleph0_of_infinite
      p (tupleSubgroup a) htargetFinite β hinfinite
  have hsourceRoom :
      roomInvariant p (tupleSubgroup b) β ≤ Cardinal.aleph0 :=
    (rank_le_card (R := ZMod p)
      (M := room p (tupleSubgroup b) β)).trans
      ((Cardinal.mk_le_of_surjective
        (roomSubmodule p (tupleSubgroup b) β).mkQ_surjective).trans
        Cardinal.mk_le_aleph0)
  have hkernel :
      jumpKernelInvariant p C.equiv.toAddMonoidHom hsucc hβ <
        Cardinal.aleph0 :=
    jumpKernelInvariant_lt_aleph0_of_finite_source
      p hsourceFinite C.equiv.toAddMonoidHom hsucc hβ
  unfold Survival.KernelRoomBudgetAt
  rw [htargetRoom]
  exact Cardinal.add_le_aleph0.2 ⟨hsourceRoom, hkernel.le⟩

/-- Every active-window level satisfies the odd room--kernel budget.  Infinite
target filtered socle is absorbed by countability; finite target filtered
socle is handled by the relativized selector challenge. -/
theorem kernelRoomBudgetAt_of_BFRel_odd
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha beta : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b)
    (C : TupleIsoMap a b)
    (hbase : ω * alpha ≤ beta) (hcap : beta < ω * alpha + ω)
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom (Order.succ beta))
    (hbeta : IsHeightFloorAt p C.equiv.toAddMonoidHom beta) :
    Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom beta hsucc hbeta := by
  have htail : beta - ω * alpha < ω := by
    have := hcap
    rw [← Ordinal.add_sub_cancel_of_le hbase, add_lt_add_iff_left] at this
    exact this
  obtain ⟨k, hk⟩ := lt_omega0.1 htail
  have hbetaEq : beta = ω * alpha + k := by
    rw [← hk, Ordinal.add_sub_cancel_of_le hbase]
  subst beta
  by_cases htarget : Set.Finite
      (pSocleAt p (ω * alpha + k) (G := G) : Set G)
  · exact kernelRoomBudgetAt_of_finite_targetSocle_block
      p h C hsucc hbeta htarget
  · exact kernelRoomBudgetAt_of_infinite_targetSocle
      p hG hH C (ω * alpha + k) hsucc hbeta htarget

/-- Assemble the complete odd algebraic package at parameter `0` once the
single remaining global room--kernel obligation is supplied.

Tuple isomorphism, the capped length inequality, and the directional height
clause are all already forced by rank-one finite challenges.  This theorem
makes the unresolved general-ambient necessity seam explicit and map-sensitive
instead of hiding it inside the headline biconditional.
-/
theorem odd_zero_necessity_of_kernelRoom
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b)
    (C : TupleIsoMap a b)
    (heights : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.equiv x : G) ∧
        ulmHeight p (x : H) < ω * 0) ∨
      (ω * 0 ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H))
          (((ω * 0 + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
            ulmHeight p (C.equiv x : G)))
    (hkernel : ∀ (β : Ordinal.{0}) (hβω : β < ω),
      Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β
        (heightFloorAt_of_heights p C heights (Order.succ β)
          (by simpa using Order.succ_le_of_lt hβω))
        (heightFloorAt_of_heights p C heights β
          (by simpa using hβω.le))) :
    AlgBFOddCond p hG hH 0 a b := by
  refine ⟨{
    iso := C
    lengths := ?_
    ulm_below := ?_
    heights := heights
    kernel_room := ?_ }⟩
  · right
    constructor
    · simp
    · simpa using length_min_omega_le_of_BFRel_one p hG hH h
  · intro β hβ
    simp at hβ
  · intro β _hβ hβω
    exact hkernel β (by simpa using hβω)

/-- For countable ambient groups, the odd base necessity theorem only needs
the room--kernel budget to be proved at levels where the target filtered
socle is finite.  Infinite target-socle levels are discharged by
`kernelRoomBudgetAt_of_infinite_targetSocle`.

This is the exact remaining interface for the finite-witness argument: it
retains the same chosen tuple map and the floor proofs derived from its height
clause, so no map-sensitive information is hidden by existential packaging. -/
theorem odd_zero_necessity_of_finiteTargetSocleKernelRoom
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b)
    (C : TupleIsoMap a b)
    (heights : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.equiv x : G) ∧
        ulmHeight p (x : H) < ω * 0) ∨
      (ω * 0 ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H))
          (((ω * 0 + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
            ulmHeight p (C.equiv x : G)))
    (hfinite : ∀ (β : Ordinal.{0}) (hβω : β < ω),
      Set.Finite (pSocleAt p β (G := G) : Set G) →
      Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β
        (heightFloorAt_of_heights p C heights (Order.succ β)
          (by simpa using Order.succ_le_of_lt hβω))
        (heightFloorAt_of_heights p C heights β
          (by simpa using hβω.le))) :
    AlgBFOddCond p hG hH 0 a b := by
  apply odd_zero_necessity_of_kernelRoom p hG hH h C heights
  intro β hβω
  by_cases htarget : Set.Finite (pSocleAt p β (G := G) : Set G)
  · exact hfinite β hβω htarget
  · exact kernelRoomBudgetAt_of_infinite_targetSocle
      p hG hH C β _ _ htarget

/-- **The odd base case of ACM necessity for arbitrary countable ambient
groups.**

Rank-one finite challenges first determine one tuple map with the required
directional heights.  At each `β < ω`, an infinite target filtered socle makes
the room budget automatic; a finite target filtered socle is handled by the
finite selector-kernel challenge above.  Together with the rank-one length
argument, these are exactly all fields of the odd algebraic package at
parameter zero. -/
theorem odd_zero_necessity_of_BFRel_one
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    AlgBFOddCond p hG hH 0 a b := by
  obtain ⟨C, heights⟩ := generatedHeightsDirectional_zero_of_BFRel_one p h
  have heights' : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.equiv x : G) ∧
        ulmHeight p (x : H) < ω * 0) ∨
      (ω * 0 ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H))
          (((ω * 0 + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
            ulmHeight p (C.equiv x : G)) := by
    simpa using heights
  apply odd_zero_necessity_of_finiteTargetSocleKernelRoom
    p hG hH h C heights'
  intro β hβω hfinite
  obtain ⟨k, rfl⟩ := lt_omega0.1 hβω
  exact kernelRoomBudgetAt_of_finite_targetSocle_nat
    p h C _ _ hfinite

/-- A rank-two challenge transfers every finite linearly independent family
in a natural Ulm layer from the right ambient group to the left one.

Representatives of the family are challenged together with `p^k`-roots.
Atomicity puts the responses in the `k`-th filtered socle.  The returned
rank-one relation supplies a height floor at `k+1`; hence a response
combination can fall into the next socle layer only if the corresponding
challenged combination already did. -/
theorem exists_ulmQuotient_linearIndependent_response_nat
    {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b)
    (v : Fin m → ulmQuotient p (k : Ordinal.{0}) (G := H))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → ulmQuotient p (k : Ordinal.{0}) (G := G),
      LinearIndependent (ZMod p) w := by
  choose x hx using fun i ↦
    (ulmDenSubmodule p (k : Ordinal.{0})).mkQ_surjective (v i)
  have hxfil : ∀ i, (x i : H) ∈
      ulmSubgroup p (k : Ordinal.{0}) (G := H) := fun i ↦
    (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1 (x i).property |>.2
  choose z hz using fun i ↦
    (mem_ulmSubgroup_nat_iff p k (x i : H)).mp (hxfil i)
  let d : Fin (m + m) → H := Fin.append (fun i ↦ (x i : H)) z
  have htwo : Order.succ (1 : Ordinal.{0}) = 2 := by norm_num
  have hsucc : BFRel p (Order.succ 1) n a b := by
    rw [htwo]
    exact h
  obtain ⟨c, hc⟩ := (BFRel_succ p 1 n a b).mp hsucc (m + m) d
  have hrev : BFRel (G := H) (H := G) p 1 (n + (m + m))
      (Fin.append b d) (Fin.append a c) :=
    (BFRelReverse_iff_BFRel_swap p 1 (n + (m + m))
      (Fin.append b d) (Fin.append a c)).mp hc
  obtain ⟨C, heights⟩ := generatedHeightsDirectional_zero_of_BFRel_one p hrev
  have hfloorSucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (k : Ordinal.{0})) :=
    heightFloorAt_of_heights (α := 0) p C (by simpa using heights)
      (Order.succ (k : Ordinal.{0})) (by
        simpa [Order.succ_eq_add_one] using
          (natCast_lt_omega0 (k + 1)).le)
  let first : Fin m → Fin (m + m) := fun i ↦ i.castAdd m
  let root : Fin m → Fin (m + m) := fun i ↦ Fin.natAdd m i
  let responseGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (first i), AddSubgroup.subset_closure
      (show c (first i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (first i), by simp⟩)⟩
  let responseRootGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (root i), AddSubgroup.subset_closure
      (show c (root i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (root i), by simp⟩)⟩
  let challengeGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨(x i : H), AddSubgroup.subset_closure
      (show (x i : H) ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩
  let challengeRootGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨z i, AddSubgroup.subset_closure
      (show z i ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (root i), by
          rw [Fin.append_right]
          exact Fin.append_right _ _ i⟩)⟩
  have hmap : ∀ i, C.equiv (responseGen i) = challengeGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (first i))
    apply Subtype.ext
    simpa [responseGen, challengeGen, d, first] using congrArg Subtype.val hm
  have hmapRoot : ∀ i, C.equiv (responseRootGen i) = challengeRootGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (root i))
    apply Subtype.ext
    change (C.equiv (responseRootGen i) : H) = z i
    calc
      (C.equiv (responseRootGen i) : H) = d (root i) := by
        simpa only [Fin.append_right, responseRootGen]
          using congrArg Subtype.val hm
      _ = z i := by
        exact Fin.append_right (fun j ↦ (x j : H)) z i
  have hresponseEq : ∀ i,
      responseGen i = p ^ k • responseRootGen i := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, hmapRoot i]
    apply Subtype.ext
    exact (hz i).symm
  have hresponseOrder : ∀ i, p • responseGen i = 0 := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, map_zero]
    apply Subtype.ext
    exact (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1
      (x i).property |>.1
  let y : Fin m → pSocleAt p (k : Ordinal.{0}) (G := G) := fun i ↦
    ⟨c (first i), by
      rw [mem_pSocleAt]
      constructor
      · exact congrArg Subtype.val (hresponseOrder i)
      · rw [mem_ulmSubgroup_nat_iff]
        exact ⟨(c (root i)), (congrArg Subtype.val (hresponseEq i)).symm⟩⟩
  let responseSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append a c)) :=
    ⟨responseGen i, by
      rw [mem_pSocleAt]
      exact ⟨hresponseOrder i, by simp [ulmSubgroup_zero]⟩⟩
  let challengeSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append b d)) :=
    ⟨challengeGen i, by
      rw [mem_pSocleAt]
      constructor
      · apply Subtype.ext
        exact (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1
          (x i).property |>.1
      · simp [ulmSubgroup_zero]⟩
  let includeResponse := pSocleZeroMap p
    (tupleSubgroup (Fin.append a c)).subtype
  let includeChallenge := pSocleZeroMap p
    (tupleSubgroup (Fin.append b d)).subtype
  let Φ := pSocleZeroMap p C.equiv.toAddMonoidHom
  have hΦ : ∀ i, Φ (responseSocleGen i) = challengeSocleGen i := by
    intro i
    apply Subtype.ext
    exact hmap i
  have hincludeY : ∀ i,
      includeResponse (responseSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) (y i) := by
    intro i
    apply Subtype.ext
    rfl
  have hincludeX : ∀ i,
      includeChallenge (challengeSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) (x i) := by
    intro i
    apply Subtype.ext
    rfl
  let w : Fin m → ulmQuotient p (k : Ordinal.{0}) (G := G) := fun i ↦
    (ulmDenSubmodule p (k : Ordinal.{0})).mkQ (y i)
  refine ⟨w, ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  apply Fintype.linearIndependent_iff.mp hv g ?_ i
  let ysum : pSocleAt p (k : Ordinal.{0}) (G := G) := ∑ j, g j • y j
  have hysumNext : (ysum : G) ∈
      pSocleAt p (Order.succ (k : Ordinal.{0})) := by
    have hq : (ulmDenSubmodule p (k : Ordinal.{0})).mkQ ysum = 0 := by
      simpa only [ysum, w, map_sum, map_smul] using hg
    exact (Submodule.Quotient.mk_eq_zero
      (ulmDenSubmodule p (k : Ordinal.{0}))).1 hq
  let responseSum : pSocleAt p (0 : Ordinal.{0})
      (G := tupleSubgroup (Fin.append a c)) :=
    ∑ j, g j • responseSocleGen j
  have hresponseSum : includeResponse responseSum =
      pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) ysum := by
    simp only [responseSum, ysum, map_sum, map_smul, hincludeY]
  let ysumGen : tupleSubgroup (Fin.append a c) := responseSum
  have hysumVal : (ysumGen : G) = (ysum : G) := by
    exact congrArg Subtype.val hresponseSum
  have himageNext : (C.equiv ysumGen : H) ∈
      pSocleAt p (Order.succ (k : Ordinal.{0})) := by
    rw [mem_pSocleAt]
    constructor
    · have hzero := (mem_pSocleAt p 0
          (includeChallenge (Φ responseSum) : H)).1
          (includeChallenge (Φ responseSum)).property |>.1
      simpa [includeChallenge, Φ, ysumGen] using hzero
    · apply hfloorSucc ysumGen
      rw [hysumVal]
      exact (mem_pSocleAt p (Order.succ (k : Ordinal.{0})) (ysum : G)).1
        hysumNext |>.2
  let xsum : pSocleAt p (k : Ordinal.{0}) (G := H) := ∑ j, g j • x j
  let challengeSum : pSocleAt p (0 : Ordinal.{0})
      (G := tupleSubgroup (Fin.append b d)) :=
    ∑ j, g j • challengeSocleGen j
  have hΦsum : Φ responseSum = challengeSum := by
    simp only [responseSum, challengeSum, map_sum, map_smul, hΦ]
  have hchallengeSum : includeChallenge challengeSum =
      pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) xsum := by
    simp only [challengeSum, xsum, map_sum, map_smul, hincludeX]
  have himage : (C.equiv ysumGen : H) = (xsum : H) := by
    calc
      (C.equiv ysumGen : H) = (includeChallenge (Φ responseSum) : H) := rfl
      _ = (includeChallenge challengeSum : H) :=
        congrArg Subtype.val (congrArg includeChallenge hΦsum)
      _ = (xsum : H) := congrArg Subtype.val hchallengeSum
  have hxsumNext : (xsum : H) ∈
      pSocleAt p (Order.succ (k : Ordinal.{0})) := by
    rw [← himage]
    exact himageNext
  have hxq : (ulmDenSubmodule p (k : Ordinal.{0})).mkQ xsum = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (ulmDenSubmodule p (k : Ordinal.{0}))).2 hxsumNext
  simpa only [xsum, map_sum, map_smul, hx] using hxq

/-- A rank `2·δ+2` challenge transfers finite independent families in
every ordinary Ulm layer of the block beginning at `ω·δ`.

The representatives are challenged together with roots in the base tail.
The returned odd relation supplies the next-level floor, while its even
boundary supplies the oppositely oriented floors below the base; those floors
keep the response roots inside the target base tail. -/
theorem exists_ulmQuotient_linearIndependent_response_block
    {delta : Ordinal.{0}} {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * delta + 2) n a b)
    (v : Fin m → ulmQuotient p (ω * delta + k) (G := H))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → ulmQuotient p (ω * delta + k) (G := G),
      LinearIndependent (ZMod p) w := by
  choose x hx using fun i ↦
    (ulmDenSubmodule p (ω * delta + k)).mkQ_surjective (v i)
  have hxfil : ∀ i, (x i : H) ∈
      ulmSubgroup p (ω * delta + k) (G := H) := fun i ↦
    (mem_pSocleAt p (ω * delta + k) (x i : H)).1 (x i).property |>.2
  choose z hzbase hz using fun i ↦
    (mem_ulmSubgroup_add_nat_iff p (ω * delta) k (x i : H)).mp (hxfil i)
  let d : Fin (m + m) → H := Fin.append (fun i ↦ (x i : H)) z
  have hstep : BFRel p (Order.succ (2 * delta + 1)) n a b := by
    rw [← show 2 * delta + 2 = Order.succ (2 * delta + 1) by
      calc
        2 * delta + 2 = 2 * delta + (1 + 1) := by norm_num
        _ = (2 * delta + 1) + 1 := (add_assoc _ _ _).symm
        _ = Order.succ (2 * delta + 1) := rfl]
    exact h
  obtain ⟨c, hc⟩ := (BFRel_succ p (2 * delta + 1) n a b).mp
    hstep (m + m) d
  have hrev : BFRel (G := H) (H := G) p (2 * delta + 1)
      (n + (m + m)) (Fin.append b d) (Fin.append a c) :=
    (BFRelReverse_iff_BFRel_swap p (2 * delta + 1) (n + (m + m))
      (Fin.append b d) (Fin.append a c)).mp hc
  obtain ⟨C, hfloor⟩ := exists_tupleIsoMap_oddFloorBelowCap_of_BFRel p hrev
  have hfloorSucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (ω * delta + k)) := by
    apply hfloor
    have hkomega : (k + 1 : Ordinal.{0}) < ω := natCast_lt_omega0 (k + 1)
    simpa [Order.succ_eq_add_one, add_assoc] using
      (add_lt_add_iff_left (ω * delta)).2 hkomega
  have hboundary : BFRel (G := H) (H := G) p (2 * delta)
      (n + (m + m)) (Fin.append b d) (Fin.append a c) :=
    BFRel_antitone p (by simp) _ _ hrev
  obtain ⟨Cbase, hbaseFloor⟩ :=
    exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p hboundary
  let first : Fin m → Fin (m + m) := fun i ↦ i.castAdd m
  let root : Fin m → Fin (m + m) := fun i ↦ Fin.natAdd m i
  let responseGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (first i), AddSubgroup.subset_closure
      (show c (first i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (first i), by simp⟩)⟩
  let responseRootGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (root i), AddSubgroup.subset_closure
      (show c (root i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (root i), by simp⟩)⟩
  let challengeGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨(x i : H), AddSubgroup.subset_closure
      (show (x i : H) ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩
  let challengeRootGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨z i, AddSubgroup.subset_closure
      (show z i ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (root i), by
          rw [Fin.append_right]
          exact Fin.append_right _ _ i⟩)⟩
  have hmap : ∀ i, C.equiv (responseGen i) = challengeGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (first i))
    apply Subtype.ext
    simpa [responseGen, challengeGen, d, first] using congrArg Subtype.val hm
  have hmapRoot : ∀ i, C.equiv (responseRootGen i) = challengeRootGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (root i))
    apply Subtype.ext
    change (C.equiv (responseRootGen i) : H) = z i
    calc
      (C.equiv (responseRootGen i) : H) = d (root i) := by
        simpa only [Fin.append_right, responseRootGen]
          using congrArg Subtype.val hm
      _ = z i := Fin.append_right (fun j ↦ (x j : H)) z i
  have hmapRootBase : ∀ i,
      Cbase.equiv (challengeRootGen i) = responseRootGen i := by
    intro i
    have hm := Cbase.map_gen (Fin.natAdd n (root i))
    apply Subtype.ext
    change (Cbase.equiv (challengeRootGen i) : G) = c (root i)
    simpa only [Fin.append_right, challengeRootGen, d, root]
      using congrArg Subtype.val hm
  have hresponseEq : ∀ i,
      responseGen i = p ^ k • responseRootGen i := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, hmapRoot i]
    apply Subtype.ext
    exact (hz i).symm
  have hresponseOrder : ∀ i, p • responseGen i = 0 := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, map_zero]
    apply Subtype.ext
    exact (mem_pSocleAt p (ω * delta + k) (x i : H)).1
      (x i).property |>.1
  have hresponseRootBase : ∀ i, (responseRootGen i : G) ∈
      ulmSubgroup p (ω * delta) := by
    intro i
    by_cases hdelta : delta = 0
    · subst delta
      simp
    · rw [mem_ulmSubgroup_limit_iff p
          ((Ordinal.isSuccLimit_iff_omega0_dvd).2
            ⟨mul_ne_zero omega0_ne_zero hdelta, ⟨delta, rfl⟩⟩)]
      intro gamma hgamma
      rw [← hmapRootBase i]
      exact hbaseFloor gamma hgamma (challengeRootGen i)
        (ulmSubgroup_antitone p hgamma.le (hzbase i))
  let y : Fin m → pSocleAt p (ω * delta + k) (G := G) := fun i ↦
    ⟨c (first i), by
      rw [mem_pSocleAt]
      constructor
      · exact congrArg Subtype.val (hresponseOrder i)
      · exact (mem_ulmSubgroup_add_nat_iff p (ω * delta) k _).2
          ⟨c (root i), hresponseRootBase i,
            (congrArg Subtype.val (hresponseEq i)).symm⟩⟩
  let responseSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0})
        (G := tupleSubgroup (Fin.append a c)) :=
    ⟨responseGen i, by
      rw [mem_pSocleAt]
      exact ⟨hresponseOrder i, by simp [ulmSubgroup_zero]⟩⟩
  let challengeSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0})
        (G := tupleSubgroup (Fin.append b d)) :=
    ⟨challengeGen i, by
      rw [mem_pSocleAt]
      constructor
      · apply Subtype.ext
        exact (mem_pSocleAt p (ω * delta + k) (x i : H)).1
          (x i).property |>.1
      · simp [ulmSubgroup_zero]⟩
  let includeResponse := pSocleZeroMap p
    (tupleSubgroup (Fin.append a c)).subtype
  let includeChallenge := pSocleZeroMap p
    (tupleSubgroup (Fin.append b d)).subtype
  let Φ := pSocleZeroMap p C.equiv.toAddMonoidHom
  have hΦ : ∀ i, Φ (responseSocleGen i) = challengeSocleGen i := by
    intro i
    apply Subtype.ext
    exact hmap i
  have hincludeY : ∀ i,
      includeResponse (responseSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ ω * delta + k by simp)
          (y i) := by
    intro i
    apply Subtype.ext
    rfl
  have hincludeX : ∀ i,
      includeChallenge (challengeSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ ω * delta + k by simp)
          (x i) := by
    intro i
    apply Subtype.ext
    rfl
  let w : Fin m → ulmQuotient p (ω * delta + k) (G := G) := fun i ↦
    (ulmDenSubmodule p (ω * delta + k)).mkQ (y i)
  refine ⟨w, ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  apply Fintype.linearIndependent_iff.mp hv g ?_ i
  let ysum : pSocleAt p (ω * delta + k) (G := G) := ∑ j, g j • y j
  have hysumNext : (ysum : G) ∈
      pSocleAt p (Order.succ (ω * delta + k)) := by
    have hq : (ulmDenSubmodule p (ω * delta + k)).mkQ ysum = 0 := by
      simpa only [ysum, w, map_sum, map_smul] using hg
    exact (Submodule.Quotient.mk_eq_zero
      (ulmDenSubmodule p (ω * delta + k))).1 hq
  let responseSum : pSocleAt p (0 : Ordinal.{0})
      (G := tupleSubgroup (Fin.append a c)) :=
    ∑ j, g j • responseSocleGen j
  have hresponseSum : includeResponse responseSum =
      pSocleRestriction p
        (show (0 : Ordinal.{0}) ≤ ω * delta + k by simp) ysum := by
    simp only [responseSum, ysum, map_sum, map_smul, hincludeY]
  let ysumGen : tupleSubgroup (Fin.append a c) := responseSum
  have hysumVal : (ysumGen : G) = (ysum : G) := by
    exact congrArg Subtype.val hresponseSum
  have himageNext : (C.equiv ysumGen : H) ∈
      ulmSubgroup p (Order.succ (ω * delta + k)) := by
    apply hfloorSucc ysumGen
    rw [hysumVal]
    exact (mem_pSocleAt p (Order.succ (ω * delta + k)) (ysum : G)).1
      hysumNext |>.2
  let xsum : pSocleAt p (ω * delta + k) (G := H) := ∑ j, g j • x j
  let challengeSum : pSocleAt p (0 : Ordinal.{0})
      (G := tupleSubgroup (Fin.append b d)) :=
    ∑ j, g j • challengeSocleGen j
  have hΦsum : Φ responseSum = challengeSum := by
    simp only [responseSum, challengeSum, map_sum, map_smul, hΦ]
  have hchallengeSum : includeChallenge challengeSum =
      pSocleRestriction p
        (show (0 : Ordinal.{0}) ≤ ω * delta + k by simp) xsum := by
    simp only [challengeSum, xsum, map_sum, map_smul, hincludeX]
  have himage : (C.equiv ysumGen : H) = (xsum : H) := by
    calc
      (C.equiv ysumGen : H) =
          (includeChallenge (Φ responseSum) : H) := rfl
      _ = (includeChallenge challengeSum : H) :=
        congrArg Subtype.val (congrArg includeChallenge hΦsum)
      _ = (xsum : H) := congrArg Subtype.val hchallengeSum
  have hxsumNext : (xsum : H) ∈
      pSocleAt p (Order.succ (ω * delta + k)) := by
    rw [mem_pSocleAt]
    constructor
    · exact (xsum.property.1)
    · rw [← himage]
      exact himageNext
  have hxq : (ulmDenSubmodule p (ω * delta + k)).mkQ xsum = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (ulmDenSubmodule p (ω * delta + k))).2 hxsumNext
  simpa only [xsum, map_sum, map_smul, hx] using hxq

/-- Finite-family block transfer yields cardinal domination in every layer
`omega·delta+k` for countable ambient groups. -/
theorem ulmInvariant_block_le_of_BFRel
    [Countable G] [Countable H]
    {delta : Ordinal.{0}} {n k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * delta + 2) n a b) :
    ulmInvariant p (ω * delta + k) (G := H) ≤
      ulmInvariant p (ω * delta + k) (G := G) := by
  have hsourceCountable : ulmInvariant p (ω * delta + k) (G := H) ≤
      Cardinal.aleph0 :=
    (rank_le_card (R := ZMod p)
      (M := ulmQuotient p (ω * delta + k) (G := H))).trans
      ((Cardinal.mk_le_of_surjective
        (ulmDenSubmodule p (ω * delta + k)).mkQ_surjective).trans
        Cardinal.mk_le_aleph0)
  by_cases htargetLarge : Cardinal.aleph0 ≤
      ulmInvariant p (ω * delta + k) (G := G)
  · exact hsourceCountable.trans htargetLarge
  · have htargetFinite : ulmInvariant p (ω * delta + k) (G := G) <
        Cardinal.aleph0 := lt_of_not_ge htargetLarge
    letI : Module.Finite (ZMod p)
        (ulmQuotient p (ω * delta + k) (G := G)) :=
      Module.rank_lt_aleph0_iff.mp htargetFinite
    by_contra hle
    have hlt : ulmInvariant p (ω * delta + k) (G := G) <
        ulmInvariant p (ω * delta + k) (G := H) := lt_of_not_ge hle
    have hfinrank_lt : (Module.finrank (ZMod p)
          (ulmQuotient p (ω * delta + k) (G := G)) : Cardinal) <
        ulmInvariant p (ω * delta + k) (G := H) := by
      rw [Module.finrank_eq_rank]
      exact hlt
    have hlarge : (Module.finrank (ZMod p)
          (ulmQuotient p (ω * delta + k) (G := G)) + 1 : ℕ) ≤
        Module.rank (ZMod p)
          (ulmQuotient p (ω * delta + k) (G := H)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Cardinal.natCast_add_one_le_iff.mpr hfinrank_lt
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hlarge
    obtain ⟨w, hw⟩ :=
      exists_ulmQuotient_linearIndependent_response_block p h v hv
    have hcard := hw.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self
      (Module.finrank (ZMod p)
        (ulmQuotient p (ω * delta + k) (G := G)))) hcard

/-- General odd rank forces equality of the ordinary Ulm invariants strictly
below its omega base.  Each lower block is visible in both orientations: the
forward comparison uses rank `2·delta+2`, while one empty challenge at rank
`2·delta+3` supplies the reverse comparison. -/
theorem ulmInvariant_eq_belowBase_of_BFRel_odd
    [Countable G] [Countable H]
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b) :
    ∀ beta : Ordinal.{0}, beta < ω * alpha →
      ulmInvariant p beta (G := H) = ulmInvariant p beta (G := G) := by
  intro beta hbeta
  obtain ⟨delta, hdelta, r, hr, hbetaEq⟩ := lt_mul_iff.mp hbeta
  obtain ⟨k, hk⟩ := lt_omega0.1 hr
  have htwoSucc : 2 * delta + 2 ≤ 2 * alpha := by
    calc
      2 * delta + 2 = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
      _ ≤ 2 * alpha := mul_le_mul_right (Order.succ_le_of_lt hdelta) 2
  have hforward : BFRel p (2 * delta + 2) n a b :=
    BFRel_antitone p (htwoSucc.trans le_self_add) a b h
  have hthree : 2 * delta + 3 ≤ 2 * alpha + 1 := by
    have hle := add_le_add_left htwoSucc 1
    simpa [add_assoc, show (3 : Ordinal.{0}) = 2 + 1 by norm_num] using hle
  have hstep : BFRel p (Order.succ (2 * delta + 2)) n a b := by
    have hlower := BFRel_antitone p hthree a b h
    rw [show Order.succ (2 * delta + 2) = 2 * delta + 3 by
      calc
        Order.succ (2 * delta + 2) = (2 * delta + 2) + 1 := rfl
        _ = 2 * delta + (2 + 1) := add_assoc _ _ _
        _ = 2 * delta + 3 := by norm_num]
    exact hlower
  obtain ⟨d, hd⟩ := (BFRel_succ p (2 * delta + 2) n a b).mp
    hstep 0 Fin.elim0
  have hd0 : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst d
  have hreverse : BFRel (G := H) (H := G) p (2 * delta + 2) n b a := by
    have hd' : BFRelReverse p (2 * delta + 2) n b a := by
      simpa using hd
    exact (BFRelReverse_iff_BFRel_swap p (2 * delta + 2) n b a).mp hd'
  rw [hbetaEq, hk]
  apply le_antisymm
  · exact ulmInvariant_block_le_of_BFRel p hforward
  · exact ulmInvariant_block_le_of_BFRel p hreverse

/-- **General odd necessity.**  A rank `2·alpha+1` relation supplies one
tuple map shared by the length, low-Ulm, directional-height, and active
room--kernel fields of the algebraic package. -/
theorem odd_necessity_of_BFRel
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 1) n a b) :
    AlgBFOddCond p hG hH alpha a b := by
  obtain ⟨C, heights⟩ := generatedHeightsDirectional_of_BFRel_odd p hG hH h
  refine ⟨{
    iso := C
    lengths := odd_lengths_of_BFRel p hG hH h
    ulm_below := ulmInvariant_eq_belowBase_of_BFRel_odd p h
    heights := heights
    kernel_room := ?_ }⟩
  intro beta hbase hcap
  exact kernelRoomBudgetAt_of_BFRel_odd p hG hH h C hbase hcap
    (heightFloorAt_of_heights p C heights (Order.succ beta)
      (Order.succ_le_of_lt hcap))
    (heightFloorAt_of_heights p C heights beta (le_of_lt hcap))

/-- A rank-two challenge transfers every finite linearly independent family
of standard-Hill classes at a natural level from the right marked pair to the
left marked pair.

The challenge is the same representative-and-root challenge used for ordinary
Ulm layers.  If a response combination lies in the left Hill denominator,
split it into an old-mark element plus a next-level element.  The enlarged
atomic map agrees with the inverse old tuple map on the mark, while its
rank-one height floor carries the next-level remainder into the right
next-level subgroup.  Thus the challenged combination lies in the right Hill
denominator. -/
theorem exists_hillQuotient_linearIndependent_response_nat
    {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) (C₀ : TupleIsoMap a b)
    (v : Fin m → hillQuotient p (tupleSubgroup b) (k : Ordinal.{0}))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → hillQuotient p (tupleSubgroup a) (k : Ordinal.{0}),
      LinearIndependent (ZMod p) w := by
  choose x hx using fun i ↦
    (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0})).mkQ_surjective (v i)
  have hxfil : ∀ i, (x i : H) ∈
      ulmSubgroup p (k : Ordinal.{0}) (G := H) := fun i ↦
    (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1 (x i).property |>.2
  choose z hz using fun i ↦
    (mem_ulmSubgroup_nat_iff p k (x i : H)).mp (hxfil i)
  let d : Fin (m + m) → H := Fin.append (fun i ↦ (x i : H)) z
  have htwo : Order.succ (1 : Ordinal.{0}) = 2 := by norm_num
  have hsucc : BFRel p (Order.succ 1) n a b := by
    rw [htwo]
    exact h
  obtain ⟨c, hc⟩ := (BFRel_succ p 1 n a b).mp hsucc (m + m) d
  have hrev : BFRel (G := H) (H := G) p 1 (n + (m + m))
      (Fin.append b d) (Fin.append a c) :=
    (BFRelReverse_iff_BFRel_swap p 1 (n + (m + m))
      (Fin.append b d) (Fin.append a c)).mp hc
  obtain ⟨C, heights⟩ := generatedHeightsDirectional_zero_of_BFRel_one p hrev
  have hfloorSucc : IsHeightFloorAt p C.equiv.toAddMonoidHom
      (Order.succ (k : Ordinal.{0})) :=
    heightFloorAt_of_heights (α := 0) p C (by simpa using heights)
      (Order.succ (k : Ordinal.{0})) (by
        simpa [Order.succ_eq_add_one] using
          (natCast_lt_omega0 (k + 1)).le)
  let first : Fin m → Fin (m + m) := fun i ↦ i.castAdd m
  let root : Fin m → Fin (m + m) := fun i ↦ Fin.natAdd m i
  let responseGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (first i), AddSubgroup.subset_closure
      (show c (first i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (first i), by simp⟩)⟩
  let responseRootGen (i : Fin m) : tupleSubgroup (Fin.append a c) :=
    ⟨c (root i), AddSubgroup.subset_closure
      (show c (root i) ∈ Set.range (Fin.append a c) from
        ⟨Fin.natAdd n (root i), by simp⟩)⟩
  let challengeGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨(x i : H), AddSubgroup.subset_closure
      (show (x i : H) ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (first i), by simp [d, first]⟩)⟩
  let challengeRootGen (i : Fin m) : tupleSubgroup (Fin.append b d) :=
    ⟨z i, AddSubgroup.subset_closure
      (show z i ∈ Set.range (Fin.append b d) from
        ⟨Fin.natAdd n (root i), by
          rw [Fin.append_right]
          exact Fin.append_right _ _ i⟩)⟩
  have hmap : ∀ i, C.equiv (responseGen i) = challengeGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (first i))
    apply Subtype.ext
    simpa [responseGen, challengeGen, d, first] using congrArg Subtype.val hm
  have hmapRoot : ∀ i, C.equiv (responseRootGen i) = challengeRootGen i := by
    intro i
    have hm := C.map_gen (Fin.natAdd n (root i))
    apply Subtype.ext
    change (C.equiv (responseRootGen i) : H) = z i
    calc
      (C.equiv (responseRootGen i) : H) = d (root i) := by
        simpa only [Fin.append_right, responseRootGen]
          using congrArg Subtype.val hm
      _ = z i := Fin.append_right (fun j ↦ (x j : H)) z i
  have hresponseEq : ∀ i,
      responseGen i = p ^ k • responseRootGen i := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, hmapRoot i]
    apply Subtype.ext
    exact (hz i).symm
  have hresponseOrder : ∀ i, p • responseGen i = 0 := by
    intro i
    apply C.equiv.injective
    rw [map_nsmul, hmap i, map_zero]
    apply Subtype.ext
    exact (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1
      (x i).property |>.1
  let y : Fin m → pSocleAt p (k : Ordinal.{0}) (G := G) := fun i ↦
    ⟨c (first i), by
      rw [mem_pSocleAt]
      constructor
      · exact congrArg Subtype.val (hresponseOrder i)
      · rw [mem_ulmSubgroup_nat_iff]
        exact ⟨c (root i), (congrArg Subtype.val (hresponseEq i)).symm⟩⟩
  let responseSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append a c)) :=
    ⟨responseGen i, by
      rw [mem_pSocleAt]
      exact ⟨hresponseOrder i, by simp [ulmSubgroup_zero]⟩⟩
  let challengeSocleGen (i : Fin m) :
      pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append b d)) :=
    ⟨challengeGen i, by
      rw [mem_pSocleAt]
      constructor
      · apply Subtype.ext
        exact (mem_pSocleAt p (k : Ordinal.{0}) (x i : H)).1
          (x i).property |>.1
      · simp [ulmSubgroup_zero]⟩
  let includeResponse := pSocleZeroMap p
    (tupleSubgroup (Fin.append a c)).subtype
  let includeChallenge := pSocleZeroMap p
    (tupleSubgroup (Fin.append b d)).subtype
  let Φ := pSocleZeroMap p C.equiv.toAddMonoidHom
  have hΦ : ∀ i, Φ (responseSocleGen i) = challengeSocleGen i := by
    intro i
    apply Subtype.ext
    exact hmap i
  have hincludeY : ∀ i,
      includeResponse (responseSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) (y i) := by
    intro i
    apply Subtype.ext
    rfl
  have hincludeX : ∀ i,
      includeChallenge (challengeSocleGen i) =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) (x i) := by
    intro i
    apply Subtype.ext
    rfl
  let w : Fin m → hillQuotient p (tupleSubgroup a) (k : Ordinal.{0}) := fun i ↦
    (hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ (y i)
  refine ⟨w, ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  let ysum : pSocleAt p (k : Ordinal.{0}) (G := G) := ∑ j, g j • y j
  have hysumHill : ysum ∈
      hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0}) := by
    apply (Submodule.Quotient.mk_eq_zero
      (hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0}))).1
    change ∑ j, g j •
      (hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ (y j) = 0 at hg
    calc
      (hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ ysum =
          ∑ j, g j •
            (hillSubmodule p (tupleSubgroup a) (k : Ordinal.{0})).mkQ (y j) := by
        simp only [ysum, map_sum, map_smul]
      _ = 0 := hg
  have hysumSup : (ysum : G) ∈
      tupleSubgroup a ⊔ ulmSubgroup p (Order.succ (k : Ordinal.{0})) := by
    change (ysum : G) ∈
      pSocleAt p (k : Ordinal.{0}) ⊓
        (tupleSubgroup a ⊔ ulmSubgroup p (Order.succ (k : Ordinal.{0}))) at hysumHill
    exact hysumHill.2
  rcases AddSubgroup.mem_sup.mp hysumSup with ⟨e, he, t, ht, het⟩
  let responseSocleSum :
      pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append a c)) :=
    ∑ j, g j • responseSocleGen j
  let responseSum : tupleSubgroup (Fin.append a c) := responseSocleSum
  let oldResponse : tupleSubgroup a := ⟨e, he⟩
  let oldResponseIn : tupleSubgroup (Fin.append a c) :=
    AddSubgroup.inclusion (tupleSubgroup_le_append_left a c) oldResponse
  let highResponse : tupleSubgroup (Fin.append a c) := responseSum - oldResponseIn
  have hresponseSumVal : (responseSum : G) = (ysum : G) := by
    have hsum : includeResponse responseSocleSum =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) ysum := by
      simp only [responseSocleSum, ysum, map_sum, map_smul, hincludeY]
    exact congrArg Subtype.val hsum
  have hhighVal : (highResponse : G) = t := by
    change (responseSum : G) - e = t
    rw [hresponseSumVal, ← het]
    abel
  have hhighImage : (C.equiv highResponse : H) ∈
      ulmSubgroup p (Order.succ (k : Ordinal.{0})) := by
    apply hfloorSucc highResponse
    rw [hhighVal]
    exact ht
  let xsum : pSocleAt p (k : Ordinal.{0}) (G := H) := ∑ j, g j • x j
  have hresponseImage : (C.equiv responseSum : H) = (xsum : H) := by
    let challengeSocleSum :
        pSocleAt p (0 : Ordinal.{0}) (G := tupleSubgroup (Fin.append b d)) :=
      ∑ j, g j • challengeSocleGen j
    have hΦsum : Φ responseSocleSum = challengeSocleSum := by
      simp only [responseSocleSum, challengeSocleSum, map_sum, map_smul, hΦ]
    have hchallengeSum : includeChallenge challengeSocleSum =
        pSocleRestriction p (show (0 : Ordinal.{0}) ≤ k by simp) xsum := by
      simp only [challengeSocleSum, xsum, map_sum, map_smul, hincludeX]
    calc
      (C.equiv responseSum : H) = (includeChallenge (Φ responseSocleSum) : H) := rfl
      _ = (includeChallenge challengeSocleSum : H) :=
        congrArg Subtype.val (congrArg includeChallenge hΦsum)
      _ = (xsum : H) := congrArg Subtype.val hchallengeSum
  have hxsumDecomp : (xsum : H) =
      (C₀.symm.equiv oldResponse : H) + (C.equiv highResponse : H) := by
    calc
      (xsum : H) = (C.equiv responseSum : H) := hresponseImage.symm
      _ = (C.equiv (oldResponseIn + highResponse) : H) := by
        congr 2
        simp [highResponse]
      _ = (C.equiv oldResponseIn : H) + (C.equiv highResponse : H) :=
        congrArg Subtype.val (C.equiv.map_add oldResponseIn highResponse)
      _ = _ := congrArg (fun z : H ↦ z + (C.equiv highResponse : H))
        (C₀.symm.append_left_equiv_apply_eq C oldResponse).symm
  have hxsumHill : xsum ∈
      hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0}) := by
    change (xsum : H) ∈
      pSocleAt p (k : Ordinal.{0}) ⊓
        (tupleSubgroup b ⊔ ulmSubgroup p (Order.succ (k : Ordinal.{0})))
    refine ⟨xsum.property, AddSubgroup.mem_sup.mpr ?_⟩
    exact ⟨(C₀.symm.equiv oldResponse : H),
      (C₀.symm.equiv oldResponse).property,
      (C.equiv highResponse : H), hhighImage, hxsumDecomp.symm⟩
  have hxq :
      (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0})).mkQ xsum = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0}))).2 hxsumHill
  have hsourceZero : ∑ j, g j • v j = 0 := by
    calc
      ∑ j, g j • v j = ∑ j, g j •
          (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0})).mkQ (x j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hx j]
      _ = (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0})).mkQ xsum := by
        simp only [xsum, map_sum, map_smul]
      _ = 0 := hxq
  exact Fintype.linearIndependent_iff.mp hv g hsourceZero i

/-- The finite-family transfer yields the absolute Ulm comparison at every
natural level in countable ambient groups. -/
theorem ulmInvariant_nat_le_of_BFRel_two
    [Countable G] [Countable H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) (k : ℕ) :
    ulmInvariant p (k : Ordinal.{0}) (G := H) ≤
      ulmInvariant p (k : Ordinal.{0}) (G := G) := by
  have hsourceCountable : ulmInvariant p (k : Ordinal.{0}) (G := H) ≤
      Cardinal.aleph0 :=
    (rank_le_card (R := ZMod p)
      (M := ulmQuotient p (k : Ordinal.{0}) (G := H))).trans
      ((Cardinal.mk_le_of_surjective
        (ulmDenSubmodule p (k : Ordinal.{0})).mkQ_surjective).trans
        Cardinal.mk_le_aleph0)
  by_cases htargetLarge : Cardinal.aleph0 ≤
      ulmInvariant p (k : Ordinal.{0}) (G := G)
  · exact hsourceCountable.trans htargetLarge
  · have htargetFinite : ulmInvariant p (k : Ordinal.{0}) (G := G) <
        Cardinal.aleph0 := lt_of_not_ge htargetLarge
    letI : Module.Finite (ZMod p)
        (ulmQuotient p (k : Ordinal.{0}) (G := G)) :=
      Module.rank_lt_aleph0_iff.mp htargetFinite
    by_contra hle
    have hlt : ulmInvariant p (k : Ordinal.{0}) (G := G) <
        ulmInvariant p (k : Ordinal.{0}) (G := H) := lt_of_not_ge hle
    have hfinrank_lt : (Module.finrank (ZMod p)
          (ulmQuotient p (k : Ordinal.{0}) (G := G)) : Cardinal) <
        ulmInvariant p (k : Ordinal.{0}) (G := H) := by
      rw [Module.finrank_eq_rank]
      exact hlt
    have hlarge : (Module.finrank (ZMod p)
          (ulmQuotient p (k : Ordinal.{0}) (G := G)) + 1 : ℕ) ≤
        Module.rank (ZMod p)
          (ulmQuotient p (k : Ordinal.{0}) (G := H)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Cardinal.natCast_add_one_le_iff.mpr hfinrank_lt
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hlarge
    obtain ⟨w, hw⟩ :=
      exists_ulmQuotient_linearIndependent_response_nat p h v hv
    have hcard := hw.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self
      (Module.finrank (ZMod p)
        (ulmQuotient p (k : Ordinal.{0}) (G := G)))) hcard

/-- The finite standard-Hill family transfer upgrades to the required
cardinal comparison at every natural level in countable ambient groups. -/
theorem hillInvariant_nat_le_of_BFRel_two
    [Countable G] [Countable H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) (C : TupleIsoMap a b) (k : ℕ) :
    hillInvariant p (tupleSubgroup b) (k : Ordinal.{0}) ≤
      hillInvariant p (tupleSubgroup a) (k : Ordinal.{0}) := by
  have hsourceCountable :
      hillInvariant p (tupleSubgroup b) (k : Ordinal.{0}) ≤ Cardinal.aleph0 :=
    (rank_le_card (R := ZMod p)
      (M := hillQuotient p (tupleSubgroup b) (k : Ordinal.{0}))).trans
      ((Cardinal.mk_le_of_surjective
        (hillSubmodule p (tupleSubgroup b) (k : Ordinal.{0})).mkQ_surjective).trans
        Cardinal.mk_le_aleph0)
  by_cases htargetLarge : Cardinal.aleph0 ≤
      hillInvariant p (tupleSubgroup a) (k : Ordinal.{0})
  · exact hsourceCountable.trans htargetLarge
  · have htargetFinite :
        hillInvariant p (tupleSubgroup a) (k : Ordinal.{0}) < Cardinal.aleph0 :=
      lt_of_not_ge htargetLarge
    letI : Module.Finite (ZMod p)
        (hillQuotient p (tupleSubgroup a) (k : Ordinal.{0})) :=
      Module.rank_lt_aleph0_iff.mp htargetFinite
    by_contra hle
    have hlt : hillInvariant p (tupleSubgroup a) (k : Ordinal.{0}) <
        hillInvariant p (tupleSubgroup b) (k : Ordinal.{0}) := lt_of_not_ge hle
    have hfinrank_lt : (Module.finrank (ZMod p)
          (hillQuotient p (tupleSubgroup a) (k : Ordinal.{0})) : Cardinal) <
        hillInvariant p (tupleSubgroup b) (k : Ordinal.{0}) := by
      rw [Module.finrank_eq_rank]
      exact hlt
    have hlarge : (Module.finrank (ZMod p)
          (hillQuotient p (tupleSubgroup a) (k : Ordinal.{0})) + 1 : ℕ) ≤
        Module.rank (ZMod p)
          (hillQuotient p (tupleSubgroup b) (k : Ordinal.{0})) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Cardinal.natCast_add_one_le_iff.mpr hfinrank_lt
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hlarge
    obtain ⟨w, hw⟩ :=
      exists_hillQuotient_linearIndependent_response_nat p h C v hv
    have hcard := hw.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self
      (Module.finrank (ZMod p)
        (hillQuotient p (tupleSubgroup a) (k : Ordinal.{0})))) hcard

/-- Rank two supplies the absolute half of the even base window. -/
theorem even_zero_absolute_of_BFRel_two
    [Countable G] [Countable H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) :
    ∀ β : Ordinal.{0}, 0 ≤ β → β < ω →
      ulmInvariant p β (G := H) ≤ ulmInvariant p β (G := G) := by
  intro β _hzero hβ
  obtain ⟨k, rfl⟩ := lt_omega0.1 hβ
  exact ulmInvariant_nat_le_of_BFRel_two p h k

/-!
The oppositely oriented marked comparison does **not** follow in arbitrary
countable ambient groups.  The infinite-reserve example

`B = ⊕_ℕ Z/p²`, `A = B ⊕ Z/p`

with empty tuples satisfies `BFRel p 2`: every finite challenge uses only
finitely many coordinates, and the extra order-`p` direction can be sent to
`p` times a fresh `Z/p²` coordinate.  Nevertheless the height-zero Ulm (and
hence empty-mark marked-graded) invariants are `0` for `B` and `1` for `A`.
Thus the current crossed package is a valid sufficient strengthening, but not
an exact necessity statement for countable ambient groups.  The finite engine
cannot expose this obstruction because a finite target has no fresh-coordinate
reserve.
-/

/-- Rank two supplies the reversed rank-one relation on the unchanged marked
tuple by answering the empty challenge. -/
theorem swapped_BFRel_one_of_BFRel_two
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) :
    BFRel (G := H) (H := G) p 1 n b a := by
  have hrank : Order.succ (1 : Ordinal.{0}) = 2 := by norm_num
  have hsucc : BFRel p (Order.succ 1) n a b := by
    rw [hrank]
    exact h
  obtain ⟨d, hd⟩ := (BFRel_succ p 1 n a b).mp hsucc 0 Fin.elim0
  have hswap :=
    (BFRelReverse_iff_BFRel_swap p 1 n
      (Fin.append b Fin.elim0) (Fin.append a d)).mp hd
  have hdempty : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst d
  simpa using hswap

/-- An even successor relation supplies the reversed odd predecessor on the
unchanged marked tuple by answering the empty outer challenge. -/
theorem swapped_BFRel_odd_of_BFRel_even
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 2) n a b) :
    BFRel (G := H) (H := G) p (2 * alpha + 1) n b a := by
  have hrank : Order.succ (2 * alpha + 1) = 2 * alpha + 2 := by
    rw [Order.succ_eq_add_one, ← one_add_one_eq_two, ← add_assoc]
  have hsucc : BFRel p (Order.succ (2 * alpha + 1)) n a b := by
    rw [hrank]
    exact h
  obtain ⟨d, hd⟩ := (BFRel_succ p (2 * alpha + 1) n a b).mp
    hsucc 0 Fin.elim0
  have hswap :=
    (BFRelReverse_iff_BFRel_swap p (2 * alpha + 1) n
      (Fin.append b Fin.elim0) (Fin.append a d)).mp hd
  have hdempty : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst d
  simpa using hswap

/-- The tuple isomorphism returned by reversed rank-one necessity is the
inverse of the forward tuple isomorphism.  This is forced by the displayed
generators, independently of how either necessity proof chose its witness. -/
theorem reverse_odd_iso_comp_forward_eq
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH alpha a b)
    (D : AlgBFOddCondData p hH hG alpha b a)
    (x : tupleSubgroup b) :
    (D.iso.equiv (C.iso.equiv x) : H) = (x : H) := by
  have hu := TupleIsoMap.equiv_apply_eq D.iso C.iso.symm (C.iso.equiv x)
  calc
    (D.iso.equiv (C.iso.equiv x) : H) =
        (C.iso.symm.equiv (C.iso.equiv x) : H) := hu
    _ = (x : H) := congrArg Subtype.val
      (C.iso.equiv.symm_apply_apply x)

/-- Reversed odd-zero necessity already contains the exact-even reverse room
comparison: discard the nonnegative inverse jump-kernel summand from its
room--kernel budget. -/
theorem roomInvariant_nat_le_of_reverse_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (D : AlgBFOddCondData p hH hG 0 b a) (k : ℕ) :
    roomInvariant p (tupleSubgroup a) (k : Ordinal.{0}) ≤
      roomInvariant p (tupleSubgroup b) (k : Ordinal.{0}) := by
  have hkω : (k : Ordinal.{0}) < ω * 0 + ω := by
    simpa using natCast_lt_omega0 k
  have hbudget := D.kernel_room (k : Ordinal.{0}) (by simp)
    hkω
  calc
    roomInvariant p (tupleSubgroup a) (k : Ordinal.{0}) =
        roomInvariant p (tupleSubgroup a) (k : Ordinal.{0}) + 0 := by simp
    _ ≤ roomInvariant p (tupleSubgroup a) (k : Ordinal.{0}) +
        jumpKernelInvariant p D.iso.equiv.toAddMonoidHom
          (heightFloorAt_of_heights p D.iso D.heights
            (Order.succ (k : Ordinal.{0}))
            (Order.succ_le_of_lt hkω))
          (heightFloorAt_of_heights p D.iso D.heights (k : Ordinal.{0})
            (le_of_lt hkω)) :=
      add_le_add_right (zero_le _) _
    _ ≤ roomInvariant p (tupleSubgroup b) (k : Ordinal.{0}) := hbudget

/-- Reversed odd necessity contains the exact-even reverse-room inequality at
every point of the active block: discard the nonnegative jump-kernel summand
from its room--kernel budget. -/
theorem roomInvariant_le_of_reverse_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha beta : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (D : AlgBFOddCondData p hH hG alpha b a)
    (hbase : ω * alpha ≤ beta) (hcap : beta < ω * alpha + ω) :
    roomInvariant p (tupleSubgroup a) beta ≤
      roomInvariant p (tupleSubgroup b) beta := by
  have hbudget := D.kernel_room beta hbase hcap
  calc
    roomInvariant p (tupleSubgroup a) beta =
        roomInvariant p (tupleSubgroup a) beta + 0 := by simp
    _ ≤ roomInvariant p (tupleSubgroup a) beta +
        jumpKernelInvariant p D.iso.equiv.toAddMonoidHom
          (heightFloorAt_of_heights p D.iso D.heights (Order.succ beta)
            (Order.succ_le_of_lt hcap))
          (heightFloorAt_of_heights p D.iso D.heights beta
            (le_of_lt hcap)) :=
      add_le_add_right (zero_le _) _
    _ ≤ roomInvariant p (tupleSubgroup b) beta := hbudget

/-- Either branch of odd length necessity implies its directional truncated
length inequality at the end of the active omega block. -/
theorem min_ulmLength_cap_le_of_oddData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH alpha a b) :
    min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * alpha + ω) ≤
      (ulmLength p (G := G) hG : Ordinal.{0}) := by
  rcases C.lengths with hshort | hlong
  · calc
      min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * alpha + ω) ≤
          (ulmLength p (G := H) hH : Ordinal.{0}) := min_le_left _ _
      _ = (ulmLength p (G := G) hG : Ordinal.{0}) := hshort.1.symm
  · exact hlong.2

/-- Either branch of odd marked-height necessity implies the directional
truncated height inequality at the end of the active omega block. -/
theorem min_ulmHeight_cap_le_of_oddData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH alpha a b)
    (x : tupleSubgroup b) :
    min (ulmHeight p (x : H))
        ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
      ulmHeight p (C.iso.equiv x : G) := by
  rcases C.heights x with hlow | hhigh
  · calc
      min (ulmHeight p (x : H))
          ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (x : H) := min_le_left _ _
      _ = ulmHeight p (C.iso.equiv x : G) := hlow.1
  · exact hhigh.2

/-- Assemble even parameter-zero data from rank two once the extra marked
window comparison is supplied.

Rank two gives rank one in both orientations: directly by monotonicity and in
the reverse orientation by the empty challenge.  The completed odd base
necessity theorem therefore supplies the two directional length and height
inequalities.  Pairing them yields the even length dichotomy and exact height
matching below `ω`.  Rank two itself supplies the absolute window comparison;
the marked comparison remains an explicit strengthening and is not necessary
in arbitrary countable ambient groups (see the infinite-reserve note above). -/
theorem even_zero_of_BFRel_two_of_markedWindow
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b)
    (hmarked : ∀ β : Ordinal.{0}, 0 ≤ β → β < ω →
      markedGradedInvariant p (tupleSubgroup a) β ≤
        markedGradedInvariant p (tupleSubgroup b) β) :
    AlgBFEvenCond p hG hH 0 a b := by
  have hone : BFRel p 1 n a b :=
    BFRel_antitone p (by norm_num) a b h
  obtain ⟨C⟩ := odd_zero_necessity_of_BFRel_one p hG hH hone
  have hswap : BFRel (G := H) (H := G) p 1 n b a :=
    swapped_BFRel_one_of_BFRel_two p h
  obtain ⟨D⟩ := odd_zero_necessity_of_BFRel_one p hH hG hswap
  have hmap : ∀ x : tupleSubgroup b,
      (D.iso.equiv (C.iso.equiv x) : H) = (x : H) := by
    intro x
    have hu := TupleIsoMap.equiv_apply_eq D.iso C.iso.symm (C.iso.equiv x)
    calc
      (D.iso.equiv (C.iso.equiv x) : H) =
          (C.iso.symm.equiv (C.iso.equiv x) : H) := hu
      _ = (x : H) := congrArg Subtype.val
        (C.iso.equiv.symm_apply_apply x)
  have hforwardHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (x : H))
          ((ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (C.iso.equiv x : G) := by
    intro x
    rcases C.heights x with hlow | hhigh
    · simp at hlow
    · simpa using hhigh.2
  have hreverseHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (C.iso.equiv x : G))
          ((ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (x : H) := by
    intro x
    rcases D.heights (C.iso.equiv x) with hlow | hhigh
    · simp at hlow
    · rw [hmap x] at hhigh
      simpa using hhigh.2
  have hforwardLength :
      min (ulmLength p (G := H) hH : Ordinal.{0}) ω ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) := by
    rcases C.lengths with hshort | hlong
    · simp at hshort
    · simpa using hlong.2
  have hreverseLength :
      min (ulmLength p (G := G) hG : Ordinal.{0}) ω ≤
        (ulmLength p (G := H) hH : Ordinal.{0}) := by
    rcases D.lengths with hshort | hlong
    · simp at hshort
    · simpa using hlong.2
  refine ⟨{
    iso := C.iso
    lengths := ?_
    ulm_below := ?_
    window := {
      absolute := by simpa using even_zero_absolute_of_BFRel_two p h
      marked := by simpa using hmarked }
    heights := ?_ }⟩
  · by_cases hGshort : (ulmLength p (G := G) hG : Ordinal.{0}) < ω
    · left
      have hHshort : (ulmLength p (G := H) hH : Ordinal.{0}) < ω := by
        apply lt_of_not_ge
        intro hHlong
        have := hforwardLength
        rw [min_eq_right hHlong] at this
        exact (not_le_of_gt hGshort) this
      constructor
      · apply le_antisymm
        · simpa [min_eq_left hGshort.le] using hreverseLength
        · simpa [min_eq_left hHshort.le] using hforwardLength
      · simpa using hGshort
    · right
      have hGlong : ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) :=
        le_of_not_gt hGshort
      constructor
      · simpa using hGlong
      · simpa [min_eq_right hGlong] using hreverseLength
  · intro β hβ
    simp at hβ
  · intro x
    let cap : WithTop Ordinal.{0} :=
      ((ω : Ordinal.{0}) : WithTop Ordinal.{0})
    by_cases hxshort : ulmHeight p (x : H) < cap
    · left
      have hCxshort : ulmHeight p (C.iso.equiv x : G) < cap := by
        apply lt_of_not_ge
        intro hCxlong
        have hr := hreverseHeight x
        rw [min_eq_right hCxlong] at hr
        exact (not_le_of_gt hxshort) hr
      constructor
      · apply le_antisymm
        · have hf := hforwardHeight x
          rw [min_eq_left hxshort.le] at hf
          exact hf
        · have hr := hreverseHeight x
          rw [min_eq_left hCxshort.le] at hr
          exact hr
      · simpa [cap] using hxshort
    · right
      have hxlong : cap ≤ ulmHeight p (x : H) := le_of_not_gt hxshort
      constructor
      · simpa [cap] using hxlong
      · have hf := hforwardHeight x
        rw [min_eq_right hxlong] at hf
        simpa [cap] using hf

/-- Rank two implies the exact-even algebraic condition at parameter
zero in arbitrary countable reduced ambient groups.

The forward standard-Hill comparison is the finite-family transfer above.
The reverse room comparison comes from reversed odd-zero necessity after the
inverse tuple map has been identified and its nonnegative jump-kernel summand
discarded.  The two odd directions also supply the common length and marked
height fields. -/
theorem even_zero_exact_of_BFRel_two
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) :
    AlgBFEvenExactCond p hG hH 0 a b := by
  have hone : BFRel p 1 n a b :=
    BFRel_antitone p (by norm_num) a b h
  obtain ⟨C⟩ := odd_zero_necessity_of_BFRel_one p hG hH hone
  have hswap : BFRel (G := H) (H := G) p 1 n b a :=
    swapped_BFRel_one_of_BFRel_two p h
  obtain ⟨D⟩ := odd_zero_necessity_of_BFRel_one p hH hG hswap
  have hmap : ∀ x : tupleSubgroup b,
      (D.iso.equiv (C.iso.equiv x) : H) = (x : H) :=
    reverse_odd_iso_comp_forward_eq p hG hH C D
  have hforwardHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (x : H))
          ((ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (C.iso.equiv x : G) := by
    intro x
    rcases C.heights x with hlow | hhigh
    · simp at hlow
    · simpa using hhigh.2
  have hreverseHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (C.iso.equiv x : G))
          ((ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (x : H) := by
    intro x
    rcases D.heights (C.iso.equiv x) with hlow | hhigh
    · simp at hlow
    · rw [hmap x] at hhigh
      simpa using hhigh.2
  have hforwardLength :
      min (ulmLength p (G := H) hH : Ordinal.{0}) ω ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) := by
    rcases C.lengths with hshort | hlong
    · simp at hshort
    · simpa using hlong.2
  have hreverseLength :
      min (ulmLength p (G := G) hG : Ordinal.{0}) ω ≤
        (ulmLength p (G := H) hH : Ordinal.{0}) := by
    rcases D.lengths with hshort | hlong
    · simp at hshort
    · simpa using hlong.2
  refine ⟨{
    iso := C.iso
    lengths := ?_
    ulm_below := ?_
    window := {
      hill_forward := ?_
      room_reverse := ?_ }
    heights := ?_ }⟩
  · by_cases hGshort : (ulmLength p (G := G) hG : Ordinal.{0}) < ω
    · left
      have hHshort : (ulmLength p (G := H) hH : Ordinal.{0}) < ω := by
        apply lt_of_not_ge
        intro hHlong
        have hlength := hforwardLength
        rw [min_eq_right hHlong] at hlength
        exact (not_le_of_gt hGshort) hlength
      constructor
      · apply le_antisymm
        · simpa [min_eq_left hGshort.le] using hreverseLength
        · simpa [min_eq_left hHshort.le] using hforwardLength
      · simpa using hGshort
    · right
      have hGlong : ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) :=
        le_of_not_gt hGshort
      constructor
      · simpa using hGlong
      · simpa [min_eq_right hGlong] using hreverseLength
  · intro β hβ
    simp at hβ
  · intro β _hzero hβ
    have hβω : β < ω := by simpa using hβ
    obtain ⟨k, rfl⟩ := lt_omega0.1 hβω
    exact hillInvariant_nat_le_of_BFRel_two p h C.iso k
  · intro β _hzero hβ
    have hβω : β < ω := by simpa using hβ
    obtain ⟨k, rfl⟩ := lt_omega0.1 hβω
    exact roomInvariant_nat_le_of_reverse_odd p hG hH D k
  · intro x
    let cap : WithTop Ordinal.{0} :=
      ((ω : Ordinal.{0}) : WithTop Ordinal.{0})
    by_cases hxshort : ulmHeight p (x : H) < cap
    · left
      have hCxshort : ulmHeight p (C.iso.equiv x : G) < cap := by
        apply lt_of_not_ge
        intro hCxlong
        have hr := hreverseHeight x
        rw [min_eq_right hCxlong] at hr
        exact (not_le_of_gt hxshort) hr
      constructor
      · apply le_antisymm
        · have hf := hforwardHeight x
          rw [min_eq_left hxshort.le] at hf
          exact hf
        · have hr := hreverseHeight x
          rw [min_eq_left hCxshort.le] at hr
          exact hr
      · simpa [cap] using hxshort
    · right
      have hxlong : cap ≤ ulmHeight p (x : H) := le_of_not_gt hxshort
      constructor
      · simpa [cap] using hxlong
      · have hf := hforwardHeight x
        rw [min_eq_right hxlong] at hf
        simpa [cap] using hf

/-- **General exact-even necessity.**  A rank `2·alpha+2` relation gives odd
necessity in both orientations.  Pairing those directional packages yields
the exact length and marked-height fields.  N1 supplies the ordinary Ulm
comparison in the active block; finite-stage cancellation converts it to the
standard-Hill comparison.  The reversed odd room--kernel budget supplies
reverse room after its nonnegative kernel term is discarded. -/
theorem even_exact_of_BFRel_even
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p (2 * alpha + 2) n a b) :
    AlgBFEvenExactCond p hG hH alpha a b := by
  have hone : BFRel p (2 * alpha + 1) n a b :=
    BFRel_antitone p (by simp) a b h
  obtain ⟨C⟩ := odd_necessity_of_BFRel p hG hH hone
  have hswap : BFRel (G := H) (H := G) p (2 * alpha + 1) n b a :=
    swapped_BFRel_odd_of_BFRel_even p h
  obtain ⟨D⟩ := odd_necessity_of_BFRel p hH hG hswap
  have hmap : ∀ x : tupleSubgroup b,
      (D.iso.equiv (C.iso.equiv x) : H) = (x : H) :=
    reverse_odd_iso_comp_forward_eq p hG hH C D
  have hforwardLength :
      min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * alpha + ω) ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) :=
    min_ulmLength_cap_le_of_oddData p hG hH C
  have hreverseLength :
      min (ulmLength p (G := G) hG : Ordinal.{0}) (ω * alpha + ω) ≤
        (ulmLength p (G := H) hH : Ordinal.{0}) :=
    min_ulmLength_cap_le_of_oddData p hH hG D
  have hforwardHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (x : H))
          ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (C.iso.equiv x : G) :=
    min_ulmHeight_cap_le_of_oddData p hG hH C
  have hreverseHeight : ∀ x : tupleSubgroup b,
      min (ulmHeight p (C.iso.equiv x : G))
          ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (x : H) := by
    intro x
    have hr := min_ulmHeight_cap_le_of_oddData p hH hG D (C.iso.equiv x)
    rw [hmap x] at hr
    exact hr
  have hheights : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.iso.equiv x : G) ∧
        ulmHeight p (x : H) <
          ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
      (((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (x : H) ∧
        ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (C.iso.equiv x : G)) := by
    intro x
    let cap : WithTop Ordinal.{0} :=
      ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0})
    by_cases hxshort : ulmHeight p (x : H) < cap
    · left
      have hCxshort : ulmHeight p (C.iso.equiv x : G) < cap := by
        apply lt_of_not_ge
        intro hCxlong
        have hr := hreverseHeight x
        rw [min_eq_right hCxlong] at hr
        exact (not_le_of_gt hxshort) hr
      constructor
      · apply le_antisymm
        · have hf := hforwardHeight x
          rw [min_eq_left hxshort.le] at hf
          exact hf
        · have hr := hreverseHeight x
          rw [min_eq_left hCxshort.le] at hr
          exact hr
      · simpa [cap] using hxshort
    · right
      have hxlong : cap ≤ ulmHeight p (x : H) := le_of_not_gt hxshort
      constructor
      · simpa [cap] using hxlong
      · have hf := hforwardHeight x
        rw [min_eq_right hxlong] at hf
        simpa [cap] using hf
  have hpres : IsHeightPresBelowOn p C.iso.equiv.toAddMonoidHom
      (ω * alpha + ω) := by
    intro gamma hgamma x
    rw [mem_ulmSubgroup_iff_le_ulmHeight,
      mem_ulmSubgroup_iff_le_ulmHeight]
    change ((gamma : WithTop Ordinal.{0}) ≤ ulmHeight p (x : H)) ↔
      ((gamma : WithTop Ordinal.{0}) ≤
        ulmHeight p (C.iso.equiv x : G))
    rcases hheights x with hlow | hhigh
    · rw [hlow.1]
    · have hgammaCap :
          (gamma : WithTop Ordinal.{0}) ≤
            ((ω * alpha + ω : Ordinal.{0}) : WithTop Ordinal.{0}) :=
        WithTop.coe_le_coe.mpr (le_of_lt hgamma)
      exact iff_of_true (hgammaCap.trans hhigh.1)
        (hgammaCap.trans hhigh.2)
  refine ⟨{
    iso := C.iso
    lengths := ?_
    ulm_below := C.ulm_below
    window := {
      hill_forward := ?_
      room_reverse := ?_ }
    heights := hheights }⟩
  · by_cases hGshort :
        (ulmLength p (G := G) hG : Ordinal.{0}) < ω * alpha + ω
    · left
      have hHshort :
          (ulmLength p (G := H) hH : Ordinal.{0}) < ω * alpha + ω := by
        apply lt_of_not_ge
        intro hHlong
        have hlength := hforwardLength
        rw [min_eq_right hHlong] at hlength
        exact (not_le_of_gt hGshort) hlength
      constructor
      · apply le_antisymm
        · simpa [min_eq_left hGshort.le] using hreverseLength
        · simpa [min_eq_left hHshort.le] using hforwardLength
      · exact hGshort
    · right
      have hGlong : ω * alpha + ω ≤
          (ulmLength p (G := G) hG : Ordinal.{0}) := le_of_not_gt hGshort
      constructor
      · exact hGlong
      · simpa [min_eq_right hGlong] using hreverseLength
  · intro beta hbase hcap
    have hdiff : beta - ω * alpha < ω := by
      rw [← Ordinal.add_sub_cancel_of_le hbase, add_lt_add_iff_left] at hcap
      exact hcap
    obtain ⟨k, hk⟩ := lt_omega0.1 hdiff
    have hbeta : beta = ω * alpha + k := by
      rw [← Ordinal.add_sub_cancel_of_le hbase, hk]
    have hcapLimit : Order.IsSuccLimit (ω * alpha + ω) :=
      Ordinal.isSuccLimit_add (ω * alpha) Ordinal.isSuccLimit_omega0
    have hsuccCap : Order.succ beta < ω * alpha + ω :=
      hcapLimit.succ_lt hcap
    have hsuccSuccCap : Order.succ (Order.succ beta) < ω * alpha + ω :=
      hcapLimit.succ_lt hsuccCap
    let stage : UlmStageAt p (G := H) (H := G) beta :=
      { A := tupleSubgroup b
        B := tupleSubgroup a
        hAfinite := tupleSubgroup_finite p hH.primary b
        hBfinite := tupleSubgroup_finite p hG.primary a
        e := C.iso.equiv
        hφ_at := fun x ↦ hpres beta hcap x
        hφ_succ := fun x ↦ hpres (Order.succ beta) hsuccCap x
        hφ_succSucc := fun x ↦
          hpres (Order.succ (Order.succ beta)) hsuccSuccCap x }
    apply ExactStageTransfer.hillInvariant_le_of_ulmInvariant_le p stage
    rw [hbeta]
    exact ulmInvariant_block_le_of_BFRel p h
  · intro beta hbase hcap
    exact roomInvariant_le_of_reverse_odd p hG hH D hbase hcap

/-- If one ambient Ulm length lies below the base of a nonzero limit
relation, a lower exact-even window already sees that endpoint and forces the
two lengths to be equal. -/
theorem ulmLength_eq_of_lt_limitBase
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b)
    (hshort : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * alpha) :
    (ulmLength p (G := G) hG : Ordinal.{0}) =
      (ulmLength p (G := H) hH : Ordinal.{0}) := by
  obtain ⟨delta, hdelta, r, hr, hlength⟩ := lt_mul_iff.mp hshort
  have hdeltaSucc : Order.succ delta < alpha := halpha.succ_lt hdelta
  have hrank : 2 * delta + 2 < alpha := by
    rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
    calc
      2 * delta + 2 = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
      _ < 2 * alpha := mul_lt_mul_of_pos_left hdeltaSucc (by norm_num)
  have hlower : BFRel p (2 * delta + 2) n a b :=
    BFRel_antitone p hrank.le a b h
  obtain ⟨E⟩ := even_exact_of_BFRel_even p hG hH hlower
  have hlengthCap :
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * delta + ω := by
    rw [hlength]
    exact (add_lt_add_iff_left (ω * delta)).2 hr
  rcases E.lengths with heq | hlong
  · exact heq.1
  · exact (not_le_of_gt hlengthCap hlong.1).elim

/-- A nonzero limit relation forces the exact Ulm-length dichotomy at its
limit base.  Symmetry supplies the same short-endpoint argument in the
opposite orientation. -/
theorem limit_lengths_of_BFRel
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b) :
    ((ulmLength p (G := G) hG : Ordinal.{0}) =
        (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * alpha) ∨
    (ω * alpha ≤ (ulmLength p (G := G) hG : Ordinal.{0}) ∧
      ω * alpha ≤ (ulmLength p (G := H) hH : Ordinal.{0})) := by
  by_cases hGshort : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * alpha
  · exact Or.inl ⟨ulmLength_eq_of_lt_limitBase p hG hH halpha h hGshort,
      hGshort⟩
  · right
    refine ⟨le_of_not_gt hGshort, ?_⟩
    by_contra hHlong
    have hHshort : (ulmLength p (G := H) hH : Ordinal.{0}) < ω * alpha :=
      lt_of_not_ge hHlong
    have hswap : BFRel (G := H) (H := G) p alpha n b a :=
      BFRel_symm_of_isSuccLimit p halpha a b h
    have heq := ulmLength_eq_of_lt_limitBase p hH hG halpha hswap hHshort
    exact hGshort (by rw [← heq]; exact hHshort)

/-- Every ordinary Ulm invariant below a nonzero limit base is seen in a
lower even block.  Limit symmetry gives the reverse comparison. -/
theorem ulmInvariant_eq_belowBase_of_BFRel_limit
    [Countable G] [Countable H]
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b) :
    ∀ beta : Ordinal.{0}, beta < ω * alpha →
      ulmInvariant p beta (G := H) = ulmInvariant p beta (G := G) := by
  intro beta hbeta
  obtain ⟨delta, hdelta, r, hr, hbetaEq⟩ := lt_mul_iff.mp hbeta
  obtain ⟨k, hk⟩ := lt_omega0.1 hr
  have hdeltaSucc : Order.succ delta < alpha := halpha.succ_lt hdelta
  have hrank : 2 * delta + 2 < alpha := by
    rw [← Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
    calc
      2 * delta + 2 = 2 * (Order.succ delta) := by rw [Ordinal.mul_succ]
      _ < 2 * alpha := mul_lt_mul_of_pos_left hdeltaSucc (by norm_num)
  have hforward : BFRel p (2 * delta + 2) n a b :=
    BFRel_antitone p hrank.le a b h
  have hswap : BFRel (G := H) (H := G) p alpha n b a :=
    BFRel_symm_of_isSuccLimit p halpha a b h
  have hreverse : BFRel (G := H) (H := G) p (2 * delta + 2) n b a :=
    BFRel_antitone p hrank.le b a hswap
  rw [hbetaEq, hk]
  apply le_antisymm
  · exact ulmInvariant_block_le_of_BFRel p hforward
  · exact ulmInvariant_block_le_of_BFRel p hreverse

/-- At a nonzero limit rank, one tuple isomorphism preserves the whole
filtration below `omega·alpha`.  The two directional floors come from the
same even boundary relation read in both orientations; uniqueness of the
tuple-induced map identifies them as inverse maps. -/
theorem exists_tupleIsoMap_heightPresBelow_limit
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b) :
    ∃ C : TupleIsoMap a b,
      IsHeightPresBelowOn p C.equiv.toAddMonoidHom (ω * alpha) := by
  have hboundary : BFRel p (2 * alpha) n a b := by
    rw [Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
    exact h
  have hswap : BFRel (G := H) (H := G) p alpha n b a :=
    BFRel_symm_of_isSuccLimit p halpha a b h
  have hboundarySwap : BFRel (G := H) (H := G) p (2 * alpha) n b a := by
    rw [Ordinal.two_mul_eq_self_of_isSuccLimit halpha]
    exact hswap
  obtain ⟨R, hR⟩ :=
    exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p hboundary
  obtain ⟨C, hC⟩ :=
    exists_swappedTupleIsoMap_floorBelowBase_of_BFRel_evenBoundary p
      hboundarySwap
  refine ⟨C, ?_⟩
  intro gamma hgamma x
  constructor
  · exact hC gamma hgamma x
  · intro hx
    have hmem := hR gamma hgamma (C.equiv x) hx
    have heq := TupleIsoMap.equiv_apply_eq R C.symm (C.equiv x)
    have hmem' : (C.symm.equiv (C.equiv x) : H) ∈
        ulmSubgroup p gamma := by
      rw [← heq]
      exact hmem
    simpa using hmem'

/-- The tuple map forced by a nonzero limit relation has exactly matching
marked heights below the limit base and sends the remaining elements above
that base in both directions. -/
theorem limit_heights_of_BFRel
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b) :
    ∃ C : TupleIsoMap a b, ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.equiv x : G) ∧
        ulmHeight p (x : H) <
          ((ω * alpha : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
      (((ω * alpha : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (x : H) ∧
        ((ω * alpha : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (C.equiv x : G)) := by
  obtain ⟨C, hpres⟩ := exists_tupleIsoMap_heightPresBelow_limit p halpha h
  have hbasePre : Order.IsSuccPrelimit (ω * alpha) :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.2 ⟨alpha, rfl⟩
  exact ⟨C, heightsMatchBelow_of_heightPresBelowOn
    p hG hH hbasePre C hpres⟩

/-- **Nonzero-limit necessity.**  The limit relation supplies the four
fields of the algebraic package through lower exact-even blocks and the
limit-boundary filtration equivalence. -/
theorem limit_necessity_of_BFRel
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {alpha : Ordinal.{0}} (halpha : Order.IsSuccLimit alpha)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p alpha n a b) :
    AlgBFLimitCond p hG hH alpha a b := by
  obtain ⟨C, heights⟩ := limit_heights_of_BFRel p hG hH halpha h
  exact ⟨{
    iso := C
    lengths := limit_lengths_of_BFRel p hG hH halpha h
    ulm_below := ulmInvariant_eq_belowBase_of_BFRel_limit p halpha h
    heights := heights }⟩

/-- An enumeration of a finite group generates the whole group. -/
theorem tupleSubgroup_equivFin_symm_eq_top [Fintype H] :
    tupleSubgroup ((Fintype.equivFin H).symm : Fin (Fintype.card H) → H) = ⊤ := by
  apply top_unique
  intro x _hx
  apply AddSubgroup.subset_closure
  exact ⟨Fintype.equivFin H x, by simp⟩

/-- A rank-one relation into a finite source contains a whole-source
height-nondecreasing embedding into the target.

The finite challenge is an enumeration of `H`.  Its atomic response is an
isomorphism from the subgroup generated by that enumeration (hence all of
`H`) onto a subgroup of `G`.  The returned marked tuple map is the restriction
of the same embedding, so the extension equation is part of the conclusion.
-/
theorem exists_finiteSource_embedding_of_BFRel_one
    [Fintype H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    ∃ (f : (⊤ : AddSubgroup H) →+ (⊤ : AddSubgroup G))
      (C : TupleIsoMap a b),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
        ∀ x : tupleSubgroup b,
          (f ⟨(x : H), trivial⟩ : G) = (C.equiv x : G) := by
  let enumH : Fin (Fintype.card H) → H := (Fintype.equivFin H).symm
  obtain ⟨c, ⟨C'⟩⟩ :=
    exists_finiteTuple_baseResponse_of_BFRel p (by norm_num) h enumH
  have hsource :
      tupleSubgroup (Fin.append b enumH) = (⊤ : AddSubgroup H) := by
    apply top_unique
    intro x _hx
    apply AddSubgroup.subset_closure
    let j : Fin (Fintype.card H) := Fintype.equivFin H x
    exact ⟨Fin.natAdd n j, by simp [enumH, j]⟩
  have htop_le :
      (⊤ : AddSubgroup H) ≤ tupleSubgroup (Fin.append b enumH) := by
    rw [hsource]
  let toTopH : H →+ (⊤ : AddSubgroup H) :=
    { toFun := fun x ↦ ⟨x, trivial⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let inclusion : (⊤ : AddSubgroup H) →+
      tupleSubgroup (Fin.append b enumH) :=
    AddSubgroup.inclusion htop_le
  let fAmbient : H →+ G :=
    (tupleSubgroup (Fin.append a c)).subtype.comp
      (C'.equiv.toAddMonoidHom.comp (inclusion.comp toTopH))
  have hfAmbient : Function.Injective fAmbient := by
    intro x y hxy
    have hC : C'.equiv (inclusion (toTopH x)) =
        C'.equiv (inclusion (toTopH y)) := by
      exact Subtype.ext hxy
    have hinc : inclusion (toTopH x) = inclusion (toTopH y) :=
      C'.equiv.injective hC
    have htop : toTopH x = toTopH y :=
      AddSubgroup.inclusion_injective htop_le hinc
    exact congrArg Subtype.val htop
  let f : (⊤ : AddSubgroup H) →+ (⊤ : AddSubgroup G) :=
    (fAmbient.comp (⊤ : AddSubgroup H).subtype).codRestrict
      (⊤ : AddSubgroup G) (fun _ ↦ trivial)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hfAmbient
    simpa [f] using congrArg Subtype.val hxy
  have hfloor : IsHeightFloorOn p f := by
    intro γ x hx
    change fAmbient (x : H) ∈ ulmSubgroup p γ (G := G)
    exact map_ulmSubgroup_le p fAmbient γ ⟨(x : H), hx, rfl⟩
  let fMarked : tupleSubgroup b →+ G :=
    fAmbient.comp (tupleSubgroup b).subtype
  have hfMarked : Function.Injective fMarked := by
    intro x y hxy
    apply Subtype.ext
    exact hfAmbient hxy
  have hgen : ∀ i : Fin n,
      fMarked ⟨b i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩ = a i := by
    intro i
    change (C'.equiv (inclusion (toTopH (b i))) : G) = a i
    have hinc : inclusion (toTopH (b i)) =
        ⟨b i, AddSubgroup.subset_closure
          (show b i ∈ Set.range (Fin.append b enumH) from
            ⟨i.castAdd (Fintype.card H), by simp⟩)⟩ := rfl
    rw [hinc]
    have hmap := congrArg Subtype.val
      (C'.map_gen (i.castAdd (Fintype.card H)))
    simpa using hmap
  let C : TupleIsoMap a b :=
    TupleIsoMap.ofInjectiveOnGenerators fMarked hfMarked hgen
  refine ⟨f, C, hf, hfloor, ?_⟩
  intro x
  change fAmbient (x : H) = (C.equiv x : G)
  symm
  exact TupleIsoMap.ofInjectiveOnGenerators_apply fMarked hfMarked hgen x

/-- The whole-source embedding is available from every positive relation rank,
by monotonicity down to rank one. -/
theorem exists_finiteSource_embedding_of_BFRel
    [Fintype H]
    {α : Ordinal.{0}} (hα : 1 ≤ α)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p α n a b) :
    ∃ (f : (⊤ : AddSubgroup H) →+ (⊤ : AddSubgroup G))
      (C : TupleIsoMap a b),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
        ∀ x : tupleSubgroup b,
          (f ⟨(x : H), trivial⟩ : G) = (C.equiv x : G) := by
  exact exists_finiteSource_embedding_of_BFRel_one p
    (BFRel_antitone p hα a b h)

/-- An injective whole-source height floor bounds the source Ulm length by the
target Ulm length. -/
theorem ulmLength_le_of_wholeSource_embedding
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (f : (⊤ : AddSubgroup H) →+ (⊤ : AddSubgroup G))
    (hf : Function.Injective f) (hfloor : IsHeightFloorOn p f) :
    (ulmLength p (G := H) hH : Ordinal.{0}) ≤
      (ulmLength p (G := G) hG : Ordinal.{0}) := by
  apply csInf_le'
  apply le_bot_iff.mp
  intro x hx
  have hfx : f ⟨x, trivial⟩ = 0 := by
    apply Subtype.ext
    have := hfloor (ulmLength p (G := G) hG) ⟨x, trivial⟩ hx
    simpa [ulmLength.at_ulmLength (p := p) (hred := hG)] using this
  have hx0 : (⟨x, trivial⟩ : (⊤ : AddSubgroup H)) = 0 :=
    hf (by simpa using hfx)
  exact congrArg Subtype.val hx0

/-- A finite reduced primary group has Ulm length below `ω`. -/
theorem ulmLength_lt_omega_of_finite
    [Finite H] (hH : IsReducedPGroup p H) :
    (ulmLength p (G := H) hH : Ordinal.{0}) < ω := by
  obtain ⟨N, hN⟩ :=
    FiniteEmbedding.exists_ulmSubgroup_nat_eq_bot p hH.primary
  have hlenN : (ulmLength p (G := H) hH : Ordinal.{0}) ≤ N := by
    unfold ulmLength
    exact csInf_le' hN
  exact hlenN.trans_lt (natCast_lt_omega0 N)

/-- **Finite rank-one room--kernel necessity.**

For finite ambient groups, the whole-source embedding extracted from the
rank-one relation satisfies the hypotheses of
`FiniteEmbedding.kernelRoomBudget_of_finite_embedding`.  Thus the marked tuple
map carried by the relation obeys the exact D-23 budget at every ordinal.
-/
theorem exists_kernelRoomBudget_of_finite_BFRel_one
    [Fintype G] [Fintype H]
    (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    ∃ (C : TupleIsoMap a b) (hfloor : IsHeightFloorOn p C.equiv.toAddMonoidHom),
      ∀ β : Ordinal.{0},
        Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β
          (hfloor (Order.succ β)) (hfloor β) := by
  obtain ⟨f, C, hf, hffloor, hext⟩ :=
    exists_finiteSource_embedding_of_BFRel_one p h
  have hfloor : IsHeightFloorOn p C.equiv.toAddMonoidHom := by
    intro γ x hx
    change (C.equiv x : G) ∈ ulmSubgroup p γ (G := G)
    rw [← hext x]
    exact hffloor γ ⟨(x : H), trivial⟩ hx
  refine ⟨C, hfloor, ?_⟩
  exact FiniteEmbedding.kernelRoomBudget_of_finite_embedding
    p hH (tupleSubgroup b) (tupleSubgroup a)
      C.equiv.toAddMonoidHom C.equiv.surjective hfloor
      f hf hffloor hext

/-- The finite room--kernel necessity conclusion at any positive relation
rank, obtained by monotonicity to rank one. -/
theorem exists_kernelRoomBudget_of_finite_BFRel
    [Fintype G] [Fintype H]
    (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} (hα : 1 ≤ α)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p α n a b) :
    ∃ (C : TupleIsoMap a b) (hfloor : IsHeightFloorOn p C.equiv.toAddMonoidHom),
      ∀ β : Ordinal.{0},
        Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β
          (hfloor (Order.succ β)) (hfloor β) := by
  exact exists_kernelRoomBudget_of_finite_BFRel_one p hH
    (BFRel_antitone p hα a b h)

/-- **The finite odd base case of ACM necessity.**

At parameter `0`, absolute invariants below the base are vacuous.  The
rank-one whole-source embedding gives the length inequality and directional
height floor, while finite height makes the cap `ω` inactive.  The exact
room--kernel clause is the preceding finite necessity theorem.
-/
theorem odd_zero_necessity_of_finite_BFRel_one
    [Fintype G] [Fintype H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    AlgBFOddCond p hG hH 0 a b := by
  obtain ⟨f, C, hf, hffloor, hext⟩ :=
    exists_finiteSource_embedding_of_BFRel_one p h
  have hfloor : IsHeightFloorOn p C.equiv.toAddMonoidHom := by
    intro γ x hx
    change (C.equiv x : G) ∈ ulmSubgroup p γ (G := G)
    rw [← hext x]
    exact hffloor γ ⟨(x : H), trivial⟩ hx
  have hlenHG :
      (ulmLength p (G := H) hH : Ordinal.{0}) ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) :=
    ulmLength_le_of_wholeSource_embedding p hG hH f hf hffloor
  have hlenHω : (ulmLength p (G := H) hH : Ordinal.{0}) < ω :=
    ulmLength_lt_omega_of_finite p hH
  obtain ⟨N, hN⟩ :=
    FiniteEmbedding.exists_ulmSubgroup_nat_eq_bot p hH.primary
  refine ⟨{
    iso := C
    lengths := ?_
    ulm_below := ?_
    heights := ?_
    kernel_room := ?_ }⟩
  · right
    constructor
    · simp
    · simpa [min_eq_left hlenHω.le] using hlenHG
  · intro β hβ
    simp at hβ
  · intro x
    right
    constructor
    · simp
    · by_cases hx0 : (x : H) = 0
      · have hx : x = 0 := Subtype.ext hx0
        have hCx0 : (C.equiv x : G) = 0 := by
          rw [hx]
          simp
        calc
          min (ulmHeight p (x : H))
              (((ω * 0 + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
              (((ω * 0 + ω : Ordinal.{0})) : WithTop Ordinal.{0}) :=
            min_le_right _ _
          _ ≤ ulmHeight p (C.equiv x : G) := by
            rw [hCx0]
            exact coe_le_ulmHeight_of_mem p (0 : G) (ω * 0 + ω) (by simp)
      · obtain ⟨γ, hxγ, hxsucc⟩ :=
          exists_ulmHeight_eq_of_ne_zero p hH hx0
        have hγω : γ < ω := by
          have hγN : γ < (N : Ordinal.{0}) := by
            apply (lt_or_ge γ (N : Ordinal.{0})).resolve_right
            intro hNγ
            have hxN : (x : H) ∈
                ulmSubgroup p (N : Ordinal.{0}) (G := H) :=
              ulmSubgroup_antitone p hNγ hxγ
            rw [hN] at hxN
            exact hx0 (by simpa using hxN)
          exact hγN.trans (natCast_lt_omega0 N)
        rw [ulmHeight_eq_of_mem_not_mem_succ p (x : H) γ hxγ hxsucc]
        rw [mul_zero, zero_add]
        rw [min_eq_left (WithTop.coe_le_coe.mpr hγω.le)]
        exact coe_le_ulmHeight_of_mem p (C.equiv x : G) γ
          (hfloor γ x hxγ)
  · intro β _hβ hβω
    exact FiniteEmbedding.kernelRoomBudget_of_finite_embedding
      p hH (tupleSubgroup b) (tupleSubgroup a)
        C.equiv.toAddMonoidHom C.equiv.surjective hfloor
        f hf hffloor hext β

end ACMNecessity
