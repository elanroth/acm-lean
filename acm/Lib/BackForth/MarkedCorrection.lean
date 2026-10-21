import Lib.PGroups.UlmInvariants

/-!
# The finite correction in a marked Ulm layer

This file isolates the linear algebra behind the marked-graded invariant.  The
marked denominator is the ordinary Ulm denominator plus the part contributed by
the marked subgroup.  Consequently the ordinary Ulm invariant is the sum of
the marked-graded invariant and a correction rank.  If the marked subgroup is
finite, that correction rank is finite.

No height-preserving map and no back-and-forth relation appears here.  Those
belong to `MarkedGradedTransfer`.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]

/-- The part of the `α`-socle lying in the marked subgroup. -/
noncomputable def markedPartSubmodule
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p
    ((S ⊓ pSocleAt p α).comap (pSocleAt p α).subtype)

/-- The marked denominator is the ordinary denominator plus the marked part. -/
lemma markedGradedSubmodule_eq_sup
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    markedGradedSubmodule p S α =
      ulmDenSubmodule p α ⊔ markedPartSubmodule p S α := by
  ext x
  change
    ((x : G) ∈ pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)) ↔
      x ∈ ulmDenSubmodule p α ⊔ markedPartSubmodule p S α
  rw [Submodule.mem_sup]
  constructor
  · intro hx
    change (x : G) ∈ pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) at hx
    rcases AddSubgroup.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    refine ⟨⟨y, pSocleAt_antitone p (Order.le_succ α) hy⟩, ?_,
      ⟨z, hz.2⟩, ?_, ?_⟩
    · change y ∈ pSocleAt p (Order.succ α)
      exact hy
    · change (z : G) ∈ S ⊓ pSocleAt p α
      exact hz
    · apply Subtype.ext
      exact hyz
  · rintro ⟨y, hy, z, hz, rfl⟩
    apply AddSubgroup.add_mem
    · apply AddSubgroup.mem_sup_left
      change (y : G) ∈ pSocleAt p (Order.succ α)
      exact hy
    · apply AddSubgroup.mem_sup_right
      change (z : G) ∈ S ⊓ pSocleAt p α at hz
      exact hz

lemma ulmDenSubmodule_le_markedGradedSubmodule
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    ulmDenSubmodule p α ≤ markedGradedSubmodule p S α := by
  rw [markedGradedSubmodule_eq_sup p S α]
  exact le_sup_left

/-- The subspace of the ordinary Ulm layer occupied by the marked subgroup. -/
noncomputable def markedCorrectionSubmodule
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  (markedGradedSubmodule p S α).map (ulmDenSubmodule p α).mkQ

/-- Quotienting the ordinary Ulm layer by the correction gives the
marked-graded quotient. -/
noncomputable def markedCorrectionQuotientEquiv
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    (ulmQuotient p α (G := G) ⧸ markedCorrectionSubmodule p S α) ≃ₗ[ZMod p]
      markedGradedQuotient p S α :=
  Submodule.quotientQuotientEquivQuotient
    (ulmDenSubmodule p α) (markedGradedSubmodule p S α)
    (ulmDenSubmodule_le_markedGradedSubmodule p S α)

/-- Dimension equation: marked-graded rank plus marked correction equals the
ordinary Ulm invariant. -/
theorem markedGradedInvariant_add_correctionInvariant
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    markedGradedInvariant p S α +
        Module.rank (ZMod p) (markedCorrectionSubmodule p S α) =
      ulmInvariant p α (G := G) := by
  unfold markedGradedInvariant ulmInvariant
  rw [← (markedCorrectionQuotientEquiv p S α).rank_eq]
  exact Submodule.rank_quotient_add_rank (markedCorrectionSubmodule p S α)

lemma markedCorrectionSubmodule_eq_map_part
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    markedCorrectionSubmodule p S α =
      (markedPartSubmodule p S α).map (ulmDenSubmodule p α).mkQ := by
  unfold markedCorrectionSubmodule
  rw [markedGradedSubmodule_eq_sup p S α, Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq]

/-- The marked part modulo the vectors already killed by the ordinary Ulm
quotient. -/
abbrev markedPartLayerQuotient
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :=
  let f := (ulmDenSubmodule p α).mkQ.domRestrict (markedPartSubmodule p S α)
  markedPartSubmodule p S α ⧸ LinearMap.ker f

noncomputable def markedPartLayerEquivCorrection
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    markedPartLayerQuotient p S α ≃ₗ[ZMod p]
      markedCorrectionSubmodule p S α :=
  let f := (ulmDenSubmodule p α).mkQ.domRestrict (markedPartSubmodule p S α)
  (LinearMap.quotKerEquivRange f).trans
    (LinearEquiv.ofEq f.range (markedCorrectionSubmodule p S α) (by
      rw [LinearMap.range_domRestrict,
        ← markedCorrectionSubmodule_eq_map_part p S α]))

theorem markedCorrection_rank_eq_partLayer_rank
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (α : Ordinal.{0}) :
    Module.rank (ZMod p) (markedCorrectionSubmodule p S α) =
      Module.rank (ZMod p) (markedPartLayerQuotient p S α) := by
  exact (markedPartLayerEquivCorrection p S α).rank_eq.symm

/-- A finite marked subgroup contributes a finite correction rank. -/
theorem markedCorrection_rank_lt_aleph0
    {G : Type u} [AddCommGroup G] (S : AddSubgroup G) (hS : Set.Finite (S : Set G))
    (α : Ordinal.{0}) :
    Module.rank (ZMod p) (markedCorrectionSubmodule p S α) < ℵ₀ := by
  rw [markedCorrection_rank_eq_partLayer_rank p S α]
  letI : Finite S := Set.finite_coe_iff.mp hS
  let toS : markedPartSubmodule p S α → S := fun x ↦
    ⟨(x : G), by
      have hx := x.property
      change (x : G) ∈ S ⊓ pSocleAt p α at hx
      exact hx.1⟩
  have htoS : Function.Injective toS := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : G)) hxy
  letI : Finite (markedPartSubmodule p S α) :=
    Finite.of_injective toS htoS
  let f := (ulmDenSubmodule p α).mkQ.domRestrict (markedPartSubmodule p S α)
  letI : Finite (markedPartLayerQuotient p S α) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := LinearMap.ker f))
      (Submodule.Quotient.mk_surjective (LinearMap.ker f))
  exact Module.rank_lt_aleph0 (ZMod p) (markedPartLayerQuotient p S α)
