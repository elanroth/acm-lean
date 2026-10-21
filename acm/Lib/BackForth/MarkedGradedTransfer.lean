import Lib.BackForth.MarkedCorrection
import Lib.Ulm.Pure

/-!
# Transfer of marked-graded invariants across a finite height equivalence

This module formalizes the finite-mark transfer used in ACM Lemma 1.3.  It is
deliberately separated into four checkable layers:

1. the height condition preserves filtration membership through the cutoff;
2. the induced linear map identifies the marked parts of one Ulm layer;
3. it identifies their quotients by the successor-layer kernel; and
4. the resulting common finite correction can be cancelled from the dimension
   equations in `MarkedCorrection`.

There is no back-and-forth relation in this file.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]

/-- The ACM height disjunction preserves filtration membership at every level
at or below its cutoff. -/
lemma mem_ulmSubgroup_equiv_of_heightCondition
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (δ : Ordinal) (hδ : δ ≤ θ) (x : F) :
    (x : G) ∈ ulmSubgroup p δ (G := G) ↔
      (φ x : H) ∈ ulmSubgroup p δ (G := H) := by
  rw [mem_ulmSubgroup_iff_le_ulmHeight, mem_ulmSubgroup_iff_le_ulmHeight]
  rcases hφ x with hlow | hhigh
  · rw [hlow.1]
  · have hδ' : (δ : WithTop Ordinal) ≤ (θ : WithTop Ordinal) :=
      WithTop.coe_le_coe.mpr hδ
    exact iff_of_true (hδ'.trans hhigh.1) (hδ'.trans hhigh.2)

/-- The height equivalence restricted to the part of the `γ`-socle lying in the
marked subgroup. -/
noncomputable def markedPartMap
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    markedPartSubmodule p F γ →ₗ[ZMod p] markedPartSubmodule p E γ :=
  ({
    toFun := fun x ↦ by
      have hxmark := x.property
      change (x : G) ∈ F ⊓ pSocleAt p γ at hxmark
      let xF : F := ⟨(x : G), hxmark.1⟩
      have hxp := (mem_pSocleAt p γ (x : G)).1 hxmark.2
      have hfil : (φ xF : H) ∈ ulmSubgroup p γ (G := H) :=
        (mem_ulmSubgroup_equiv_of_heightCondition p F E φ θ hφ γ
          (le_of_lt hγ) xF).mp hxp.2
      have htor : p • (φ xF : H) = 0 := by
        change ((p • φ xF : E) : H) = 0
        rw [← map_nsmul]
        have hxF : p • xF = 0 := by
          apply Subtype.ext
          exact hxp.1
        rw [hxF, map_zero]
        rfl
      have hsoc : (φ xF : H) ∈ pSocleAt p γ :=
        (mem_pSocleAt p γ (φ xF : H)).2 ⟨htor, hfil⟩
      refine ⟨⟨(φ xF : H), hsoc⟩, ?_⟩
      change (φ xF : H) ∈ E ⊓ pSocleAt p γ
      exact ⟨(φ xF).property, hsoc⟩
    map_zero' := by
      apply Subtype.ext
      apply Subtype.ext
      simp
    map_add' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      change ((φ ⟨(x : G) + (y : G), _⟩ : E) : H) =
        (φ ⟨(x : G), _⟩ : H) + (φ ⟨(y : G), _⟩ : H)
      have hxmark := x.property
      change (x : G) ∈ F ⊓ pSocleAt p γ at hxmark
      have hymark := y.property
      change (y : G) ∈ F ⊓ pSocleAt p γ at hymark
      have hxyF :
          (⟨(x : G) + (y : G), F.add_mem hxmark.1 hymark.1⟩ : F) =
            (⟨(x : G), hxmark.1⟩ : F) + ⟨(y : G), hymark.1⟩ := rfl
      rw [hxyF, map_add]
      rfl
  } : markedPartSubmodule p F γ →+ markedPartSubmodule p E γ).toZModLinearMap p

theorem markedPartMap_bijective
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    Function.Bijective (markedPartMap p F E φ θ hφ γ hγ) := by
  constructor
  · intro x y hxy
    have hunder :
        (φ ⟨(x : G), by
          have hx := x.property
          change (x : G) ∈ F ⊓ pSocleAt p γ at hx
          exact hx.1⟩ : H) =
        (φ ⟨(y : G), by
          have hy := y.property
          change (y : G) ∈ F ⊓ pSocleAt p γ at hy
          exact hy.1⟩ : H) := by
      exact congrArg (fun z : markedPartSubmodule p E γ ↦ (z : H)) hxy
    have hsub :
        φ ⟨(x : G), by
          have hx := x.property
          change (x : G) ∈ F ⊓ pSocleAt p γ at hx
          exact hx.1⟩ =
        φ ⟨(y : G), by
          have hy := y.property
          change (y : G) ∈ F ⊓ pSocleAt p γ at hy
          exact hy.1⟩ := Subtype.ext hunder
    have hF := φ.injective hsub
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F ↦ (z : G)) hF
  · intro y
    have hymark := y.property
    change (y : H) ∈ E ⊓ pSocleAt p γ at hymark
    let yE : E := ⟨(y : H), hymark.1⟩
    let xF : F := φ.symm yE
    have hyp := (mem_pSocleAt p γ (y : H)).1 hymark.2
    have hxfil : (xF : G) ∈ ulmSubgroup p γ (G := G) := by
      apply (mem_ulmSubgroup_equiv_of_heightCondition p F E φ θ hφ γ
        (le_of_lt hγ) xF).mpr
      simpa [xF, yE] using hyp.2
    have hxtorF : p • xF = 0 := by
      apply φ.injective
      rw [map_nsmul, map_zero]
      apply Subtype.ext
      simpa [xF, yE] using hyp.1
    have hxtor : p • (xF : G) = 0 :=
      congrArg (fun z : F ↦ (z : G)) hxtorF
    have hxsoc : (xF : G) ∈ pSocleAt p γ :=
      (mem_pSocleAt p γ (xF : G)).2 ⟨hxtor, hxfil⟩
    let x : markedPartSubmodule p F γ :=
      ⟨⟨(xF : G), hxsoc⟩, by
        change (xF : G) ∈ F ⊓ pSocleAt p γ
        exact ⟨xF.property, hxsoc⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp [markedPartMap, x, xF, yE]

/-- The induced equivalence on the marked parts before quotienting by the next
socle layer. -/
noncomputable def markedPartEquiv
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    markedPartSubmodule p F γ ≃ₗ[ZMod p] markedPartSubmodule p E γ :=
  LinearEquiv.ofBijective (markedPartMap p F E φ θ hφ γ hγ)
    (markedPartMap_bijective p F E φ θ hφ γ hγ)

/-- The marked-part map preserves exactly the vectors killed by the ordinary
Ulm quotient.  The successor level is why `γ < θ`, not merely `γ ≤ θ`, is
needed. -/
theorem markedPartMap_mem_layerKernel_iff
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) (x : markedPartSubmodule p F γ) :
    markedPartMap p F E φ θ hφ γ hγ x ∈
        LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
          (markedPartSubmodule p E γ)) ↔
      x ∈ LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
        (markedPartSubmodule p F γ)) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply,
    Submodule.mkQ_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  change
    (markedPartMap p F E φ θ hφ γ hγ x).val ∈ ulmDenSubmodule p γ ↔
      x.val ∈ ulmDenSubmodule p γ
  change
    ((markedPartMap p F E φ θ hφ γ hγ x :
        markedPartSubmodule p E γ) : H) ∈ pSocleAt p (Order.succ γ) ↔
      (x : G) ∈ pSocleAt p (Order.succ γ)
  rw [mem_pSocleAt, mem_pSocleAt]
  have hxmark := x.property
  change (x : G) ∈ F ⊓ pSocleAt p γ at hxmark
  have hxtor : p • (x : G) = 0 :=
    ((mem_pSocleAt p γ (x : G)).1 hxmark.2).1
  have hytor : p • (markedPartMap p F E φ θ hφ γ hγ x : H) = 0 :=
    ((mem_pSocleAt p γ
      (markedPartMap p F E φ θ hφ γ hγ x : H)).1
        (markedPartMap p F E φ θ hφ γ hγ x).val.property).1
  simp only [hxtor, hytor, true_and]
  let xF : F := ⟨(x : G), hxmark.1⟩
  have hmem := mem_ulmSubgroup_equiv_of_heightCondition p F E φ θ hφ
    (Order.succ γ) (Order.succ_le_of_lt hγ) xF
  exact hmem.symm

/-- The induced map after quotienting by the successor-layer kernel. -/
noncomputable def markedPartLayerMap
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    markedPartLayerQuotient p F γ →ₗ[ZMod p] markedPartLayerQuotient p E γ := by
  let KF := LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
    (markedPartSubmodule p F γ))
  let KE := LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
    (markedPartSubmodule p E γ))
  exact KF.mapQ KE (markedPartMap p F E φ θ hφ γ hγ) (by
    intro x hx
    exact (markedPartMap_mem_layerKernel_iff p F E φ θ hφ γ hγ x).mpr hx)

theorem markedPartLayerMap_bijective
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    Function.Bijective (markedPartLayerMap p F E φ θ hφ γ hγ) := by
  let KF := LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
    (markedPartSubmodule p F γ))
  let KE := LinearMap.ker ((ulmDenSubmodule p γ).mkQ.domRestrict
    (markedPartSubmodule p E γ))
  constructor
  · intro q₁ q₂ hq
    rw [← sub_eq_zero]
    have hzero : ∀ q : markedPartLayerQuotient p F γ,
        markedPartLayerMap p F E φ θ hφ γ hγ q = 0 → q = 0 := by
      intro q
      refine Submodule.Quotient.induction_on KF q ?_
      intro x hx
      rw [markedPartLayerMap, Submodule.mapQ_apply] at hx
      apply (Submodule.Quotient.mk_eq_zero KF).2
      apply (markedPartMap_mem_layerKernel_iff p F E φ θ hφ γ hγ x).1
      exact (Submodule.Quotient.mk_eq_zero KE).1 hx
    apply hzero (q₁ - q₂)
    calc
      markedPartLayerMap p F E φ θ hφ γ hγ (q₁ - q₂) =
          markedPartLayerMap p F E φ θ hφ γ hγ q₁ -
            markedPartLayerMap p F E φ θ hφ γ hγ q₂ :=
        (markedPartLayerMap p F E φ θ hφ γ hγ).map_sub q₁ q₂
      _ = 0 := by rw [hq]; exact sub_self _
  · intro q
    refine Submodule.Quotient.induction_on KE q ?_
    intro y
    rcases (markedPartMap_bijective p F E φ θ hφ γ hγ).2 y with ⟨x, hxy⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [markedPartLayerMap, Submodule.mapQ_apply, hxy]

noncomputable def markedPartLayerEquiv
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    markedPartLayerQuotient p F γ ≃ₗ[ZMod p] markedPartLayerQuotient p E γ :=
  LinearEquiv.ofBijective (markedPartLayerMap p F E φ θ hφ γ hγ)
    (markedPartLayerMap_bijective p F E φ θ hφ γ hγ)

/-- The two finite marked subgroups occupy linearly equivalent subspaces of the
ordinary Ulm layer. -/
theorem markedCorrection_rank_eq_of_heightCondition
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    Module.rank (ZMod p) (markedCorrectionSubmodule p F γ) =
      Module.rank (ZMod p) (markedCorrectionSubmodule p E γ) := by
  rw [markedCorrection_rank_eq_partLayer_rank p F γ,
    markedCorrection_rank_eq_partLayer_rank p E γ]
  exact (markedPartLayerEquiv p F E φ θ hφ γ hγ).rank_eq

/-- Finite-mark form of ACM Lemma 1.3.

The height equivalence identifies the correction terms in the ordinary Ulm
layers.  Finiteness makes the common correction cancellable in cardinal
addition, yielding equivalence of absolute and marked-graded equality. -/
theorem markedGradedInvariant_eq_iff_of_finiteHeightEquiv
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H)
    (hF : Set.Finite (F : Set G)) (φ : F ≃+ E) (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    ulmInvariant p γ (G := G) = ulmInvariant p γ (G := H) ↔
      markedGradedInvariant p F γ = markedGradedInvariant p E γ := by
  let cF := Module.rank (ZMod p) (markedCorrectionSubmodule p F γ)
  let cE := Module.rank (ZMod p) (markedCorrectionSubmodule p E γ)
  have hc : cF = cE :=
    markedCorrection_rank_eq_of_heightCondition p F E φ θ hφ γ hγ
  have hcfin : cF < ℵ₀ := markedCorrection_rank_lt_aleph0 p F hF γ
  have hGF : markedGradedInvariant p F γ + cF = ulmInvariant p γ (G := G) :=
    markedGradedInvariant_add_correctionInvariant p F γ
  have hHE : markedGradedInvariant p E γ + cE = ulmInvariant p γ (G := H) :=
    markedGradedInvariant_add_correctionInvariant p E γ
  rw [← hGF, ← hHE, ← hc]
  exact Cardinal.add_right_inj_of_lt_aleph0 hcfin

/-- The oppositely oriented absolute and marked inequalities collapse to
equalities when the common marked correction is finite.

This is the pointwise linear-algebra reason the crossed even package is much
stronger than either inequality in isolation. -/
theorem crossedInvariantInequalities_eq_of_finiteHeightEquiv
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H)
    (hF : Set.Finite (F : Set G)) (φ : F ≃+ E) (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ)
    (habsolute : ulmInvariant p γ (G := H) ≤ ulmInvariant p γ (G := G))
    (hmarked : markedGradedInvariant p F γ ≤ markedGradedInvariant p E γ) :
    ulmInvariant p γ (G := G) = ulmInvariant p γ (G := H) ∧
      markedGradedInvariant p F γ = markedGradedInvariant p E γ := by
  let cF := Module.rank (ZMod p) (markedCorrectionSubmodule p F γ)
  let cE := Module.rank (ZMod p) (markedCorrectionSubmodule p E γ)
  have hc : cF = cE :=
    markedCorrection_rank_eq_of_heightCondition p F E φ θ hφ γ hγ
  have hcfin : cF < ℵ₀ := markedCorrection_rank_lt_aleph0 p F hF γ
  have hGF : markedGradedInvariant p F γ + cF = ulmInvariant p γ (G := G) :=
    markedGradedInvariant_add_correctionInvariant p F γ
  have hHE : markedGradedInvariant p E γ + cE = ulmInvariant p γ (G := H) :=
    markedGradedInvariant_add_correctionInvariant p E γ
  have hmarkedRev :
      markedGradedInvariant p E γ ≤ markedGradedInvariant p F γ := by
    apply (Cardinal.add_le_add_iff_of_lt_aleph0 hcfin).1
    rw [hGF, hc, hHE]
    exact habsolute
  have hmarkedEq := le_antisymm hmarked hmarkedRev
  exact ⟨(markedGradedInvariant_eq_iff_of_finiteHeightEquiv
    p F E hF φ θ hφ γ hγ).2 hmarkedEq, hmarkedEq⟩
