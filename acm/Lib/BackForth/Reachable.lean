import Lib.BackForth.JumpSpace

/-!
# Reachable socle space and its jump quotient

This file formalizes the second canonical exact sequence adopted in D-21:

`0 → room p E β → reachableSpace p E 0 β → jumpSpace p E β → 0`.

The reachable numerator is

`P_ρ(G) ∩ (E + G_σ)`,

and the denominator is `E ∩ P_ρ(G)`.  For `ρ = 0`, write a reachable
socle element as `u = e + z`, with `e ∈ E` and `z ∈ G_β`, and send its
class to `[p e]` in the jump space.  A decomposition is chosen only to
define a representative.  All theorems below prove that the resulting
quotient class is additive and independent of that choice.
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]

/-! ### The reachable quotient -/

/-- The reachable numerator `P_ρ(G) ∩ (E + G_σ)`. -/
noncomputable def reachableNum (E : AddSubgroup G) (ρ σ : Ordinal.{0}) :
    AddSubgroup G :=
  pSocleAt p ρ ⊓ (E ⊔ ulmSubgroup p σ)

/-- A reachable numerator is killed by `p`, hence is a `ZMod p`-module. -/
noncomputable instance reachableNum_module (E : AddSubgroup G)
    (ρ σ : Ordinal.{0}) : Module (ZMod p) (reachableNum p E ρ σ) := by
  refine AddCommGroup.zmodModule (n := p) (G := reachableNum p E ρ σ) ?_
  intro x
  apply Subtype.ext
  change p • (x : G) = 0
  exact (mem_pSocleAt p ρ (x : G)).1 x.property.1 |>.1

/-- The denominator `E ∩ P_ρ(G)`, viewed inside the reachable numerator. -/
noncomputable def reachableDen (E : AddSubgroup G) (ρ σ : Ordinal.{0}) :
    AddSubgroup (reachableNum p E ρ σ) :=
  (E ⊓ pSocleAt p ρ).comap (reachableNum p E ρ σ).subtype

/-- The reachable denominator as a `ZMod p`-submodule. -/
noncomputable def reachableDenSubmodule (E : AddSubgroup G)
    (ρ σ : Ordinal.{0}) : Submodule (ZMod p) (reachableNum p E ρ σ) :=
  AddSubgroup.toZModSubmodule p (reachableDen p E ρ σ)

/-- The reachable space
`C_{G,E}(ρ,σ) = (P_ρ(G) ∩ (E + G_σ)) / (E ∩ P_ρ(G))`. -/
abbrev reachableSpace (E : AddSubgroup G) (ρ σ : Ordinal.{0}) : Type u :=
  reachableNum p E ρ σ ⧸ reachableDenSubmodule p E ρ σ

/-- The dimension of the reachable space. -/
noncomputable def reachableInvariant (E : AddSubgroup G)
    (ρ σ : Ordinal.{0}) : Cardinal :=
  Module.rank (ZMod p) (reachableSpace p E ρ σ)

/-! ### Restriction to an earlier reach -/

/-- A reachable numerator at a later reach is also reachable at every earlier
reach. -/
noncomputable def reachableNumRestriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    reachableNum p E 0 γ →+ reachableNum p E 0 β where
  toFun x :=
    ⟨(x : G), ⟨x.property.1,
      (sup_le_sup_left (ulmSubgroup_antitone p hβγ) E) x.property.2⟩⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The reachable denominator is preserved by restriction. -/
lemma reachableDen_maps_restriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    reachableDenSubmodule p E 0 γ ≤
      (reachableDenSubmodule p E 0 β).comap
        ((reachableNumRestriction p E hβγ).toZModLinearMap p) := by
  intro x hx
  exact ⟨hx.1, hx.2⟩

/-- The canonical linear restriction `C(0,γ) → C(0,β)` for `β ≤ γ`. -/
noncomputable def reachableRestriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    reachableSpace p E 0 γ →ₗ[ZMod p] reachableSpace p E 0 β :=
  (reachableDenSubmodule p E 0 γ).mapQ
    (reachableDenSubmodule p E 0 β)
    ((reachableNumRestriction p E hβγ).toZModLinearMap p)
    (reachableDen_maps_restriction p E hβγ)

@[simp] theorem reachableRestriction_mk (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (x : reachableNum p E 0 γ) :
    reachableRestriction p E hβγ
        ((reachableDenSubmodule p E 0 γ).mkQ x) =
      (reachableDenSubmodule p E 0 β).mkQ
        (reachableNumRestriction p E hβγ x) :=
  Submodule.mapQ_apply _ _ _ x

/-! ### The canonical map `C(0,β) → S_β` -/

omit hp in
/-- A reachable socle representative has an anchor in `E` whose residual
lies in `G_β`. -/
lemma exists_reachableAnchor (E : AddSubgroup G) (β : Ordinal.{0})
    (x : reachableNum p E 0 β) :
    ∃ e : G, e ∈ E ∧ (x : G) - e ∈ ulmSubgroup p β := by
  obtain ⟨e, he, z, hz, hez⟩ := (AddSubgroup.mem_sup).1 x.property.2
  refine ⟨e, he, ?_⟩
  convert hz using 1
  rw [← hez]
  abel

/-- A chosen anchor for a reachable socle representative.  Only its quotient
class after multiplication by `p` will be used. -/
noncomputable def reachableAnchor (E : AddSubgroup G) (β : Ordinal.{0})
    (x : reachableNum p E 0 β) : G :=
  Classical.choose (exists_reachableAnchor p E β x)

lemma reachableAnchor_mem (E : AddSubgroup G) (β : Ordinal.{0})
    (x : reachableNum p E 0 β) : reachableAnchor p E β x ∈ E :=
  (Classical.choose_spec (exists_reachableAnchor p E β x)).1

lemma reachableResidual_mem (E : AddSubgroup G) (β : Ordinal.{0})
    (x : reachableNum p E 0 β) :
    (x : G) - reachableAnchor p E β x ∈ ulmSubgroup p β :=
  (Classical.choose_spec (exists_reachableAnchor p E β x)).2

/-- The representative `p e ∈ pE ∩ G_{β+1}` determined by a chosen anchor. -/
noncomputable def reachableAnchorMultiple (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : reachableNum p E 0 β) : jumpNum p E β := by
  refine ⟨p • reachableAnchor p E β x, ?_⟩
  constructor
  · exact ⟨reachableAnchor p E β x, reachableAnchor_mem p E β x, rfl⟩
  · rw [ulmSubgroup_succ]
    refine ⟨-((x : G) - reachableAnchor p E β x),
      (ulmSubgroup p β).neg_mem (reachableResidual_mem p E β x), ?_⟩
    have hx0 : p • (x : G) = 0 :=
      (mem_pSocleAt p 0 (x : G)).1 x.property.1 |>.1
    simp [smul_sub, hx0]

/-- The jump-numerator representative obtained from any valid anchor, not just
the classically chosen one. -/
def reachableAnchorMultipleOf (E : AddSubgroup G) (β : Ordinal.{0})
    (x : reachableNum p E 0 β) (e : G) (he : e ∈ E)
    (hres : (x : G) - e ∈ ulmSubgroup p β) : jumpNum p E β := by
  refine ⟨p • e, ?_⟩
  constructor
  · exact ⟨e, he, rfl⟩
  · rw [ulmSubgroup_succ]
    refine ⟨-((x : G) - e), (ulmSubgroup p β).neg_mem hres, ?_⟩
    have hx0 : p • (x : G) = 0 :=
      (mem_pSocleAt p 0 (x : G)).1 x.property.1 |>.1
    simp [smul_sub, hx0]

/-- Before quotienting the reachable denominator, `[u] ↦ [p e]` is additive.
The chosen anchors need not themselves be additive; their defect lies in
`E ∩ G_β`, and therefore disappears in the jump quotient. -/
noncomputable def reachablePreMap (E : AddSubgroup G) (β : Ordinal.{0}) :
    reachableNum p E 0 β →+ jumpSpace p E β where
  toFun x := QuotientAddGroup.mk (reachableAnchorMultiple p E β x)
  map_zero' := by
    apply (QuotientAddGroup.eq_zero_iff _).2
    change p • reachableAnchor p E β 0 ∈ jumpDen p E β
    refine ⟨reachableAnchor p E β 0, ⟨reachableAnchor_mem p E β 0, ?_⟩, rfl⟩
    have hres := reachableResidual_mem p E β (0 : reachableNum p E 0 β)
    change (0 : G) - reachableAnchor p E β 0 ∈ ulmSubgroup p β at hres
    simpa using (ulmSubgroup p β).neg_mem hres
  map_add' x y := by
    change QuotientAddGroup.mk (reachableAnchorMultiple p E β (x + y)) =
      QuotientAddGroup.mk
        (reachableAnchorMultiple p E β x + reachableAnchorMultiple p E β y)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    change p • reachableAnchor p E β (x + y) -
        (p • reachableAnchor p E β x + p • reachableAnchor p E β y) ∈
      jumpDen p E β
    let d := reachableAnchor p E β (x + y) -
      reachableAnchor p E β x - reachableAnchor p E β y
    refine ⟨d, ?_, ?_⟩
    · constructor
      · exact E.sub_mem
          (E.sub_mem (reachableAnchor_mem p E β (x + y))
            (reachableAnchor_mem p E β x))
          (reachableAnchor_mem p E β y)
      · have hxy := reachableResidual_mem p E β (x + y)
        have hx := reachableResidual_mem p E β x
        have hy := reachableResidual_mem p E β y
        have hres :
            ((x + y : reachableNum p E 0 β) : G) -
                reachableAnchor p E β (x + y) -
              ((x : G) - reachableAnchor p E β x) -
              ((y : G) - reachableAnchor p E β y) ∈
            ulmSubgroup p β :=
          (ulmSubgroup p β).sub_mem
            ((ulmSubgroup p β).sub_mem hxy hx) hy
        change d ∈ ulmSubgroup p β
        convert (ulmSubgroup p β).neg_mem hres using 1 <;> simp [d] <;> abel
    · simp [d, smul_sub]
      abel

/-- **Independence of decomposition.**  Every anchor `e ∈ E` with
`x-e ∈ G_β` gives the same jump class as the chosen anchor. -/
theorem reachablePreMap_eq_mk_anchorMultipleOf (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : reachableNum p E 0 β) (e : G) (he : e ∈ E)
    (hres : (x : G) - e ∈ ulmSubgroup p β) :
    reachablePreMap p E β x =
      QuotientAddGroup.mk (reachableAnchorMultipleOf p E β x e he hres) := by
  change QuotientAddGroup.mk (reachableAnchorMultiple p E β x) =
    QuotientAddGroup.mk (reachableAnchorMultipleOf p E β x e he hres)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change p • reachableAnchor p E β x - p • e ∈ jumpDen p E β
  let d := reachableAnchor p E β x - e
  refine ⟨d, ?_, ?_⟩
  · constructor
    · exact E.sub_mem (reachableAnchor_mem p E β x) he
    · have hchosen := reachableResidual_mem p E β x
      have hd := (ulmSubgroup p β).sub_mem hres hchosen
      change d ∈ ulmSubgroup p β
      convert hd using 1 <;> simp [d]
  · simp [d, smul_sub]

/-- The reachable denominator is killed by the pre-map, so the latter descends
to `C(0,β)`. -/
lemma reachableDen_le_preMap_ker (E : AddSubgroup G) (β : Ordinal.{0}) :
    reachableDenSubmodule p E 0 β ≤
      LinearMap.ker ((reachablePreMap p E β).toZModLinearMap p) := by
  intro x hx
  rw [LinearMap.mem_ker]
  change reachablePreMap p E β x = 0
  apply (QuotientAddGroup.eq_zero_iff _).2
  change p • reachableAnchor p E β x ∈ jumpDen p E β
  let z := (x : G) - reachableAnchor p E β x
  refine ⟨-z, ?_, ?_⟩
  · constructor
    · apply E.neg_mem
      apply E.sub_mem hx.1
      exact reachableAnchor_mem p E β x
    · exact (ulmSubgroup p β).neg_mem (reachableResidual_mem p E β x)
  · have hx0 : p • (x : G) = 0 :=
      (mem_pSocleAt p 0 (x : G)).1 x.property.1 |>.1
    simp [z, smul_sub, hx0]

/-- The canonical linear map
`π_β : C_{G,E}(0,β) → S_β(G,E)`, sending `[u]` to `[p e]`. -/
noncomputable def reachableToJumpLinearMap (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableSpace p E 0 β →ₗ[ZMod p] jumpSpace p E β :=
  (reachableDenSubmodule p E 0 β).liftQ
    ((reachablePreMap p E β).toZModLinearMap p)
    (reachableDen_le_preMap_ker p E β)

@[simp] lemma reachableToJumpLinearMap_mk (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : reachableNum p E 0 β) :
    reachableToJumpLinearMap p E β
        ((reachableDenSubmodule p E 0 β).mkQ x) =
      QuotientAddGroup.mk (reachableAnchorMultiple p E β x) :=
  rfl

/-- The quotient map can be computed from any valid decomposition `x=e+z`.
This is the usable canonicality statement for `π_β`. -/
lemma reachableToJumpLinearMap_mk_of_anchor (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : reachableNum p E 0 β) (e : G) (he : e ∈ E)
    (hres : (x : G) - e ∈ ulmSubgroup p β) :
    reachableToJumpLinearMap p E β
        ((reachableDenSubmodule p E 0 β).mkQ x) =
      QuotientAddGroup.mk (reachableAnchorMultipleOf p E β x e he hres) := by
  rw [reachableToJumpLinearMap_mk]
  exact reachablePreMap_eq_mk_anchorMultipleOf p E β x e he hres

/-- The reachable-to-jump map is natural under restriction to an earlier
height. -/
theorem reachableToJump_restriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (q : reachableSpace p E 0 γ) :
    reachableToJumpLinearMap p E β (reachableRestriction p E hβγ q) =
      jumpRestriction p E hβγ (reachableToJumpLinearMap p E γ q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change reachableToJumpLinearMap p E β
      (reachableRestriction p E hβγ
        ((reachableDenSubmodule p E 0 γ).mkQ x)) =
    jumpRestriction p E hβγ
      (reachableToJumpLinearMap p E γ
        ((reachableDenSubmodule p E 0 γ).mkQ x))
  rw [reachableRestriction_mk]
  rw [reachableToJumpLinearMap_mk_of_anchor p E β
    (reachableNumRestriction p E hβγ x)
    (reachableAnchor p E γ x) (reachableAnchor_mem p E γ x)
    (ulmSubgroup_antitone p hβγ (reachableResidual_mem p E γ x))]
  rw [reachableToJumpLinearMap_mk, jumpRestriction_mk]
  rfl

/-- Every jump class has a reachable socle representative. -/
theorem reachableToJumpLinearMap_surjective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Surjective (reachableToJumpLinearMap p E β) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  obtain ⟨e, he, hpe⟩ := c.property.1
  have hcU := c.property.2
  rw [ulmSubgroup_succ] at hcU
  obtain ⟨z, hz, hpz⟩ := hcU
  let u : reachableNum p E 0 β :=
    ⟨e - z, by
      constructor
      · change p • (e - z) = 0 ∧ e - z ∈ ulmSubgroup p 0
        constructor
        · rw [smul_sub, hpe, hpz]
          simp
        · simpa [ulmSubgroup_zero]
      · apply (AddSubgroup.mem_sup).2
        exact ⟨e, he, -z, (ulmSubgroup p β).neg_mem hz, by abel⟩⟩
  refine ⟨(reachableDenSubmodule p E 0 β).mkQ u, ?_⟩
  rw [reachableToJumpLinearMap_mk, QuotientAddGroup.eq_iff_sub_mem]
  change p • reachableAnchor p E β u - (c : G) ∈ jumpDen p E β
  let d := reachableAnchor p E β u - e
  refine ⟨d, ?_, ?_⟩
  · constructor
    · exact E.sub_mem (reachableAnchor_mem p E β u) he
    · have hres := reachableResidual_mem p E β u
      have hue : (u : G) - e ∈ ulmSubgroup p β := by
        change (e - z) - e ∈ ulmSubgroup p β
        convert (ulmSubgroup p β).neg_mem hz using 1 <;> abel
      have hd : ((u : G) - e) -
          ((u : G) - reachableAnchor p E β u) ∈ ulmSubgroup p β :=
        (ulmSubgroup p β).sub_mem hue hres
      change d ∈ ulmSubgroup p β
      convert hd using 1 <;> simp [d]
  · simpa [d, smul_sub, hpe]

/-! ### The reachable filtration inside the global socle quotient -/

/-- Forget the reach witness and include a reachable socle numerator in the
global socle `P_0(G)`. -/
noncomputable def reachableNumToSocleAdd (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableNum p E 0 β →+ pSocleAt p 0 (G := G) where
  toFun := fun x ↦ ⟨(x : G), x.property.1⟩
  map_zero' := Subtype.ext rfl
  map_add' := fun _ _ ↦ Subtype.ext rfl

/-- The numerator inclusion as a `ZMod p`-linear map. -/
noncomputable def reachableNumToSocle (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableNum p E 0 β →ₗ[ZMod p] pSocleAt p 0 (G := G) :=
  (reachableNumToSocleAdd p E β).toZModLinearMap p

/-- The reachable denominator maps into the denominator of the global room. -/
lemma reachableDen_le_roomZero_ker (E : AddSubgroup G) (β : Ordinal.{0}) :
    reachableDenSubmodule p E 0 β ≤ LinearMap.ker
      ((roomSubmodule p E 0).mkQ.comp (reachableNumToSocle p E β)) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).2
  constructor
  · change (x : G) ∈ E
    exact hx.1
  · change (x : G) ∈ pSocleAt p 0
    exact x.property.1

/-- The canonical inclusion
`C_{G,E}(0,β) → P(G)/(E ∩ P(G))`. -/
noncomputable def reachableToRoomZeroLinearMap (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableSpace p E 0 β →ₗ[ZMod p] room p E 0 :=
  (reachableDenSubmodule p E 0 β).liftQ
    ((roomSubmodule p E 0).mkQ.comp (reachableNumToSocle p E β))
    (reachableDen_le_roomZero_ker p E β)

@[simp] lemma reachableToRoomZeroLinearMap_mk (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : reachableNum p E 0 β) :
    reachableToRoomZeroLinearMap p E β
        ((reachableDenSubmodule p E 0 β).mkQ x) =
      (roomSubmodule p E 0).mkQ (reachableNumToSocle p E β x) :=
  rfl

/-- Restricting a reachable class does not change its image in the global
height-zero room. -/
theorem reachableRestriction_toRoomZero (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (q : reachableSpace p E 0 γ) :
    reachableToRoomZeroLinearMap p E β (reachableRestriction p E hβγ q) =
      reachableToRoomZeroLinearMap p E γ q := by
  refine Quotient.inductionOn q ?_
  intro x
  change reachableToRoomZeroLinearMap p E β
      (reachableRestriction p E hβγ
        ((reachableDenSubmodule p E 0 γ).mkQ x)) =
    reachableToRoomZeroLinearMap p E γ
      ((reachableDenSubmodule p E 0 γ).mkQ x)
  rw [reachableRestriction_mk, reachableToRoomZeroLinearMap_mk,
    reachableToRoomZeroLinearMap_mk]
  rfl

/-- Reachable classes remain distinct in the global socle quotient. -/
theorem reachableToRoomZeroLinearMap_injective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Injective (reachableToRoomZeroLinearMap p E β) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  refine Quotient.inductionOn q ?_ hq
  intro x hx
  change reachableToRoomZeroLinearMap p E β
      ((reachableDenSubmodule p E 0 β).mkQ x) = 0 at hx
  rw [reachableToRoomZeroLinearMap_mk] at hx
  have hden := (Submodule.Quotient.mk_eq_zero _).1 hx
  apply (Submodule.Quotient.mk_eq_zero _).2
  constructor
  · change (x : G) ∈ E
    exact hden.1
  · change (x : G) ∈ pSocleAt p 0
    exact x.property.1

/-- The actual filtered subspace `X_β=C_{G,E}(0,β)` inside the global quotient
`P(G)/(E ∩ P(G))`. -/
noncomputable def reachableSubspace (E : AddSubgroup G) (β : Ordinal.{0}) :
    Submodule (ZMod p) (room p E 0) :=
  LinearMap.range (reachableToRoomZeroLinearMap p E β)

/-- The abstract reachable quotient is canonically equivalent to its image
subspace in the global quotient. -/
noncomputable def reachableEquivSubspace (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableSpace p E 0 β ≃ₗ[ZMod p] reachableSubspace p E β :=
  LinearEquiv.ofInjective (reachableToRoomZeroLinearMap p E β)
    (reachableToRoomZeroLinearMap_injective p E β)

@[simp] theorem reachableEquivSubspace_symm_toRoomZero
    (E : AddSubgroup G) (β : Ordinal.{0})
    (q : reachableSubspace p E β) :
    reachableToRoomZeroLinearMap p E β
        ((reachableEquivSubspace p E β).symm q) = (q : room p E 0) := by
  change (((reachableEquivSubspace p E β)
    ((reachableEquivSubspace p E β).symm q) : reachableSubspace p E β) :
      room p E 0) = (q : room p E 0)
  simp

/-- The concrete filtered subspace has the reachable invariant as its rank. -/
theorem reachableSubspace_rank (E : AddSubgroup G) (β : Ordinal.{0}) :
    Module.rank (ZMod p) (reachableSubspace p E β) =
      reachableInvariant p E 0 β := by
  unfold reachableInvariant
  exact (reachableEquivSubspace p E β).rank_eq.symm

/-- The reachable subspaces are nested: reaching the later filtration level is
a stronger condition. -/
theorem reachableSubspace_antitone (E : AddSubgroup G) {β γ : Ordinal.{0}}
    (hβγ : β ≤ γ) : reachableSubspace p E γ ≤ reachableSubspace p E β := by
  intro q hq
  obtain ⟨x, rfl⟩ := hq
  obtain ⟨u, rfl⟩ :=
    (reachableDenSubmodule p E 0 γ).mkQ_surjective x
  let uβ : reachableNum p E 0 β :=
    ⟨(u : G), ⟨u.property.1,
      (sup_le_sup_left (ulmSubgroup_antitone p hβγ) E) u.property.2⟩⟩
  refine ⟨(reachableDenSubmodule p E 0 β).mkQ uβ, ?_⟩
  rw [reachableToRoomZeroLinearMap_mk, reachableToRoomZeroLinearMap_mk]
  rfl

/-! ### The room inside the kernel -/

/-- Include `P_β` into the reachable numerator `P(G) ∩ (E + G_β)`. -/
noncomputable def roomNumToReachableAdd (E : AddSubgroup G) (β : Ordinal.{0}) :
    pSocleAt p β (G := G) →+ reachableNum p E 0 β where
  toFun := fun x =>
    ⟨(x : G),
      ⟨pSocleAt_antitone p (bot_le : (0 : Ordinal) ≤ β) x.property,
        AddSubgroup.mem_sup_right x.property.2⟩⟩
  map_zero' := Subtype.ext rfl
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl

/-- The same numerator inclusion as a `ZMod p`-linear map. -/
noncomputable def roomNumToReachable (E : AddSubgroup G) (β : Ordinal.{0}) :
    pSocleAt p β (G := G) →ₗ[ZMod p] reachableNum p E 0 β :=
  (roomNumToReachableAdd p E β).toZModLinearMap p

/-- The room denominator maps into the reachable denominator. -/
lemma roomSubmodule_le_reachable_ker (E : AddSubgroup G) (β : Ordinal.{0}) :
    roomSubmodule p E β ≤ LinearMap.ker
      ((reachableDenSubmodule p E 0 β).mkQ.comp
        (roomNumToReachable p E β)) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).2
  constructor
  · change (x : G) ∈ E
    exact hx.1
  · change (x : G) ∈ pSocleAt p 0
    exact pSocleAt_antitone p (bot_le : (0 : Ordinal) ≤ β) x.property

/-- The canonical inclusion `R_{G,E}(β) → C_{G,E}(0,β)`. -/
noncomputable def roomToReachableLinearMap (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    room p E β →ₗ[ZMod p] reachableSpace p E 0 β :=
  (roomSubmodule p E β).liftQ
    ((reachableDenSubmodule p E 0 β).mkQ.comp
      (roomNumToReachable p E β))
    (roomSubmodule_le_reachable_ker p E β)

@[simp] lemma roomToReachableLinearMap_mk (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : pSocleAt p β (G := G)) :
    roomToReachableLinearMap p E β ((roomSubmodule p E β).mkQ x) =
      (reachableDenSubmodule p E 0 β).mkQ (roomNumToReachable p E β x) :=
  rfl

/-- The room inclusion is injective. -/
theorem roomToReachableLinearMap_injective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Injective (roomToReachableLinearMap p E β) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  refine Quotient.inductionOn q ?_ hq
  intro x hx
  change roomToReachableLinearMap p E β
      ((roomSubmodule p E β).mkQ x) = 0 at hx
  rw [roomToReachableLinearMap_mk] at hx
  have hden := (Submodule.Quotient.mk_eq_zero _).1 hx
  apply (Submodule.Quotient.mk_eq_zero _).2
  constructor
  · change (x : G) ∈ E
    exact hden.1
  · exact x.property

/-! ### The target-room filtration inside the global socle quotient -/

/-- Include the room at height `β` into the global room at height zero.  The
factorization through the reachable space records both canonical maps in the
D-21 exact sequence. -/
noncomputable def roomToRoomZeroLinearMap (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    room p E β →ₗ[ZMod p] room p E 0 :=
  (reachableToRoomZeroLinearMap p E β).comp
    (roomToReachableLinearMap p E β)

@[simp] lemma roomToRoomZeroLinearMap_mk (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : pSocleAt p β (G := G)) :
    roomToRoomZeroLinearMap p E β ((roomSubmodule p E β).mkQ x) =
      (roomSubmodule p E 0).mkQ
        (reachableNumToSocle p E β (roomNumToReachable p E β x)) := by
  rfl

/-- A high room class remains distinct in the global room. -/
theorem roomToRoomZeroLinearMap_injective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Injective (roomToRoomZeroLinearMap p E β) :=
  (reachableToRoomZeroLinearMap_injective p E β).comp
    (roomToReachableLinearMap_injective p E β)

/-- The concrete target-room direction `Z_β ≤ R_{G,E}(0)` used by the affine
Height--Rado theorem. -/
noncomputable def roomSubspace (E : AddSubgroup G) (β : Ordinal.{0}) :
    Submodule (ZMod p) (room p E 0) :=
  LinearMap.range (roomToRoomZeroLinearMap p E β)

/-- The abstract room quotient is linearly equivalent to its concrete image
inside the global room. -/
noncomputable def roomEquivSubspace (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    room p E β ≃ₗ[ZMod p] roomSubspace p E β :=
  LinearEquiv.ofInjective (roomToRoomZeroLinearMap p E β)
    (roomToRoomZeroLinearMap_injective p E β)

/-- The concrete direction has exactly the room invariant as its rank. -/
theorem roomSubspace_rank (E : AddSubgroup G) (β : Ordinal.{0}) :
    Module.rank (ZMod p) (roomSubspace p E β) =
      roomInvariant p E β := by
  unfold roomInvariant
  exact (roomEquivSubspace p E β).rank_eq.symm

/-- Target-room directions are nested with height. -/
theorem roomSubspace_antitone (E : AddSubgroup G) {β γ : Ordinal.{0}}
    (hβγ : β ≤ γ) : roomSubspace p E γ ≤ roomSubspace p E β := by
  intro q hq
  obtain ⟨x, rfl⟩ := hq
  obtain ⟨u, rfl⟩ := (roomSubmodule p E γ).mkQ_surjective x
  let uβ : pSocleAt p β (G := G) :=
    ⟨(u : G), pSocleAt_antitone p hβγ u.property⟩
  refine ⟨(roomSubmodule p E β).mkQ uβ, ?_⟩
  rw [roomToRoomZeroLinearMap_mk, roomToRoomZeroLinearMap_mk]
  rfl

/-- A room representative maps to zero in the jump quotient. -/
lemma reachableToJump_roomNum_zero (E : AddSubgroup G) (β : Ordinal.{0})
    (x : pSocleAt p β (G := G)) :
    reachableToJumpLinearMap p E β
        ((reachableDenSubmodule p E 0 β).mkQ
          (roomNumToReachable p E β x)) = 0 := by
  rw [reachableToJumpLinearMap_mk]
  apply (QuotientAddGroup.eq_zero_iff _).2
  change p • reachableAnchor p E β (roomNumToReachable p E β x) ∈
    jumpDen p E β
  refine ⟨reachableAnchor p E β (roomNumToReachable p E β x),
    ⟨reachableAnchor_mem p E β (roomNumToReachable p E β x), ?_⟩, rfl⟩
  have hres := reachableResidual_mem p E β (roomNumToReachable p E β x)
  have hres' : (x : G) - reachableAnchor p E β (roomNumToReachable p E β x) ∈
      ulmSubgroup p β := by
    simpa using hres
  have hsub := (ulmSubgroup p β).sub_mem x.property.2 hres'
  convert hsub using 1 <;> abel

/-- The composite `room → C(0,β) → S_β` is zero. -/
theorem reachableToJump_roomToReachable_zero (E : AddSubgroup G)
    (β : Ordinal.{0}) (q : room p E β) :
    reachableToJumpLinearMap p E β (roomToReachableLinearMap p E β q) = 0 := by
  refine Quotient.inductionOn q ?_
  intro x
  change reachableToJumpLinearMap p E β
    (roomToReachableLinearMap p E β ((roomSubmodule p E β).mkQ x)) = 0
  rw [roomToReachableLinearMap_mk]
  exact reachableToJump_roomNum_zero p E β x

/-- The room inclusion with codomain restricted to the kernel of `π_β`. -/
noncomputable def roomToReachableKernel (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    room p E β →ₗ[ZMod p] LinearMap.ker (reachableToJumpLinearMap p E β) :=
  (roomToReachableLinearMap p E β).codRestrict
    (LinearMap.ker (reachableToJumpLinearMap p E β))
    (reachableToJump_roomToReachable_zero p E β)

/-- Restricting the codomain does not lose injectivity. -/
theorem roomToReachableKernel_injective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Injective (roomToReachableKernel p E β) := by
  intro x y hxy
  apply roomToReachableLinearMap_injective p E β
  exact congrArg Subtype.val hxy

/-- Every element of `ker π_β` comes from a room class. -/
theorem roomToReachableKernel_surjective (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    Function.Surjective (roomToReachableKernel p E β) := by
  intro q
  obtain ⟨u, hu⟩ :=
    (reachableDenSubmodule p E 0 β).mkQ_surjective
      (q : reachableSpace p E 0 β)
  have hπ : reachableToJumpLinearMap p E β
      ((reachableDenSubmodule p E 0 β).mkQ u) = 0 := by
    rw [hu]
    exact q.property
  rw [reachableToJumpLinearMap_mk] at hπ
  have hden := (QuotientAddGroup.eq_zero_iff _).1 hπ
  change p • reachableAnchor p E β u ∈ jumpDen p E β at hden
  obtain ⟨t, ht, hpt⟩ := hden
  let x : pSocleAt p β (G := G) :=
    ⟨(u : G) - reachableAnchor p E β u + t, by
      rw [mem_pSocleAt]
      constructor
      · have hu0 : p • (u : G) = 0 :=
          (mem_pSocleAt p 0 (u : G)).1 u.property.1 |>.1
        rw [smul_add, smul_sub, hu0, hpt]
        simp
      · exact (ulmSubgroup p β).add_mem
          (reachableResidual_mem p E β u) ht.2⟩
  refine ⟨(roomSubmodule p E β).mkQ x, ?_⟩
  apply Subtype.ext
  change roomToReachableLinearMap p E β
      ((roomSubmodule p E β).mkQ x) = (q : reachableSpace p E 0 β)
  rw [roomToReachableLinearMap_mk, ← hu]
  apply (Submodule.Quotient.eq _).2
  constructor
  · change ((x : G) - (u : G)) ∈ E
    have : t - reachableAnchor p E β u ∈ E :=
      E.sub_mem ht.1 (reachableAnchor_mem p E β u)
    convert this using 1 <;> simp [x] <;> abel
  · change ((roomNumToReachable p E β x : reachableNum p E 0 β) - u :
      reachableNum p E 0 β) ∈
        (pSocleAt p 0 (G := G)).comap (reachableNum p E 0 β).subtype
    exact (reachableNum p E 0 β).sub_mem
      (roomNumToReachable p E β x).property u.property |>.1

/-- Exactness inside the global room: a reachable class lands in the concrete
room direction exactly when its jump residue vanishes. -/
theorem reachableToRoomZero_mem_roomSubspace_iff (E : AddSubgroup G)
    (β : Ordinal.{0}) (q : reachableSpace p E 0 β) :
    reachableToRoomZeroLinearMap p E β q ∈ roomSubspace p E β ↔
      reachableToJumpLinearMap p E β q = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    have hqx : roomToReachableLinearMap p E β x = q := by
      apply reachableToRoomZeroLinearMap_injective p E β
      change roomToRoomZeroLinearMap p E β x =
        reachableToRoomZeroLinearMap p E β q
      exact hx
    rw [← hqx]
    exact reachableToJump_roomToReachable_zero p E β x
  · intro hq
    let qker : LinearMap.ker (reachableToJumpLinearMap p E β) := ⟨q, hq⟩
    obtain ⟨x, hx⟩ := roomToReachableKernel_surjective p E β qker
    refine ⟨x, ?_⟩
    change reachableToRoomZeroLinearMap p E β
        (roomToReachableLinearMap p E β x) =
      reachableToRoomZeroLinearMap p E β q
    have hx' : roomToReachableLinearMap p E β x = q :=
      congrArg Subtype.val hx
    rw [hx']

/-- The kernel of the reachable-to-jump map is canonically the room. -/
noncomputable def roomEquivReachableKernel (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    room p E β ≃ₗ[ZMod p] LinearMap.ker (reachableToJumpLinearMap p E β) :=
  LinearEquiv.ofBijective (roomToReachableKernel p E β)
    ⟨roomToReachableKernel_injective p E β,
      roomToReachableKernel_surjective p E β⟩

/-- **The D-21 reachable exact sequence, in rank form.** -/
theorem reachable_rank_eq_room_add_jump (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    reachableInvariant p E 0 β =
      roomInvariant p E β + jumpInvariant p E β := by
  unfold reachableInvariant roomInvariant jumpInvariant
  calc
    Module.rank (ZMod p) (reachableSpace p E 0 β) =
        Module.rank (ZMod p) (jumpSpace p E β) +
          Module.rank (ZMod p)
            (LinearMap.ker (reachableToJumpLinearMap p E β)) :=
      LinearMap.rank_eq_of_surjective
        (reachableToJumpLinearMap_surjective p E β)
    _ = Module.rank (ZMod p) (jumpSpace p E β) +
        Module.rank (ZMod p) (room p E β) := by
      rw [← (roomEquivReachableKernel p E β).rank_eq]
    _ = Module.rank (ZMod p) (room p E β) +
        Module.rank (ZMod p) (jumpSpace p E β) := add_comm _ _
