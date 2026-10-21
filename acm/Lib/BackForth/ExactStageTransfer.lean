import Lib.BackForth.MarkedCorrection
import Lib.BackForth.JumpSpace
import Lib.BackForth.InducedMap
import Lib.Ulm.Extension

/-!
# Exact finite-stage transfer of Hill and room inequalities

An exact-even response grows a finite height-equivalent partial isomorphism.
The two candidate inequalities must therefore be available relative to the
current finite marks, not only relative to the original tuple marks.

This file isolates the fixed-level rank calculation.  A finite
height-equivalent stage contributes the same finite occupied rank to the
ordinary Ulm layer on both sides, and the same finite marked-socle rank to the
ambient filtered socle.  Consequently:

* a Hill inequality at one stage is equivalent to the corresponding ambient
  Ulm inequality, and hence transfers to every other stage between the same
  ambient groups;
* a reverse room inequality at one stage is equivalent to the corresponding
  ambient filtered-socle inequality, and transfers in the same way.

All cancellation is by an explicitly finite rank.
-/

noncomputable section

open Cardinal Module Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]

namespace ExactStageTransfer

/-- Filtration equivalence below a cutoff is symmetric for an additive
equivalence. -/
theorem heightPresBelowOn_symm
    {F : AddSubgroup G} {E : AddSubgroup H} (e : F ≃+ E)
    {θ : Ordinal.{0}}
    (h : IsHeightPresBelowOn p e.toAddMonoidHom θ) :
    IsHeightPresBelowOn p e.symm.toAddMonoidHom θ := by
  intro β hβ y
  have hx := h β hβ (e.symm y)
  simpa using hx.symm

/-- The stage equivalence restricted to the marked order-`p` part at its
distinguished height. -/
noncomputable def markedPartMapAt {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    markedPartSubmodule p s.A α →ₗ[ZMod p]
      markedPartSubmodule p s.B α :=
  ({
    toFun := fun x ↦ by
      have hx := x.property
      change (x : G) ∈ s.A ⊓ pSocleAt p α at hx
      let xA : s.A := ⟨(x : G), hx.1⟩
      have hxP := (mem_pSocleAt p α (x : G)).1 hx.2
      have hfil : (s.e xA : H) ∈ ulmSubgroup p α (G := H) :=
        (s.hφ_at xA).mp hxP.2
      have htor : p • (s.e xA : H) = 0 := by
        change ((p • s.e xA : s.B) : H) = 0
        rw [← map_nsmul]
        have hxzero : p • xA = 0 := Subtype.ext hxP.1
        rw [hxzero, map_zero]
        rfl
      have hsoc : (s.e xA : H) ∈ pSocleAt p α :=
        (mem_pSocleAt p α (s.e xA : H)).2 ⟨htor, hfil⟩
      exact ⟨⟨(s.e xA : H), hsoc⟩, ⟨(s.e xA).property, hsoc⟩⟩
    map_zero' := by
      apply Subtype.ext
      apply Subtype.ext
      simp
    map_add' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      change (s.e ⟨(x : G) + (y : G), _⟩ : H) =
        (s.e ⟨(x : G), _⟩ : H) + (s.e ⟨(y : G), _⟩ : H)
      have hx := x.property
      change (x : G) ∈ s.A ⊓ pSocleAt p α at hx
      have hy := y.property
      change (y : G) ∈ s.A ⊓ pSocleAt p α at hy
      have hxy :
          (⟨(x : G) + (y : G), s.A.add_mem hx.1 hy.1⟩ : s.A) =
            (⟨(x : G), hx.1⟩ : s.A) + ⟨(y : G), hy.1⟩ := rfl
      rw [hxy, map_add]
      rfl
  } : markedPartSubmodule p s.A α →+
      markedPartSubmodule p s.B α).toZModLinearMap p

theorem markedPartMapAt_bijective {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    Function.Bijective (markedPartMapAt p s) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg
      (fun z : markedPartSubmodule p s.B α ↦ (z : H)) hxy
    have hx := x.property
    change (x : G) ∈ s.A ⊓ pSocleAt p α at hx
    have hy := y.property
    change (y : G) ∈ s.A ⊓ pSocleAt p α at hy
    have heq : s.e ⟨(x : G), hx.1⟩ = s.e ⟨(y : G), hy.1⟩ :=
      Subtype.ext hval
    exact congrArg (fun z : s.A ↦ (z : G)) (s.e.injective heq)
  · intro y
    have hy := y.property
    change (y : H) ∈ s.B ⊓ pSocleAt p α at hy
    let yB : s.B := ⟨(y : H), hy.1⟩
    let xA : s.A := s.e.symm yB
    have hyP := (mem_pSocleAt p α (y : H)).1 hy.2
    have hxfil : (xA : G) ∈ ulmSubgroup p α (G := G) := by
      apply (s.hφ_at xA).mpr
      simpa [xA, yB] using hyP.2
    have hxtorA : p • xA = 0 := by
      apply s.e.injective
      rw [map_nsmul, map_zero]
      apply Subtype.ext
      simpa [xA, yB] using hyP.1
    have hxtor : p • (xA : G) = 0 :=
      congrArg (fun z : s.A ↦ (z : G)) hxtorA
    have hxP : (xA : G) ∈ pSocleAt p α :=
      (mem_pSocleAt p α (xA : G)).2 ⟨hxtor, hxfil⟩
    let x : markedPartSubmodule p s.A α :=
      ⟨⟨(xA : G), hxP⟩, ⟨xA.property, hxP⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp [markedPartMapAt, x, xA, yB]

noncomputable def markedPartEquivAt {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    markedPartSubmodule p s.A α ≃ₗ[ZMod p]
      markedPartSubmodule p s.B α :=
  LinearEquiv.ofBijective (markedPartMapAt p s)
    (markedPartMapAt_bijective p s)

/-- A fixed-height stage has equal marked-socle denominator ranks. -/
theorem roomSubmodule_rank_eq {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (roomSubmodule p s.A α) =
      Module.rank (ZMod p) (roomSubmodule p s.B α) := by
  change Module.rank (ZMod p) (markedPartSubmodule p s.A α) =
    Module.rank (ZMod p) (markedPartSubmodule p s.B α)
  exact (markedPartEquivAt p s).rank_eq

/-- The common room denominator rank of a finite stage is finite. -/
theorem roomSubmodule_rank_lt_aleph0 {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (roomSubmodule p s.A α) < ℵ₀ := by
  letI : Finite s.A := s.hAfinite.to_subtype
  let toA : roomSubmodule p s.A α → s.A := fun x ↦
    ⟨(x : G), x.property.1⟩
  have htoA : Function.Injective toA := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : s.A ↦ (z : G)) hxy
  letI : Finite (roomSubmodule p s.A α) :=
    Finite.of_injective toA htoA
  exact Module.rank_lt_aleph0 (ZMod p) (roomSubmodule p s.A α)

/-- Kaplansky's finite domain quotient identifies the occupied part of the
ordinary Ulm layer, so exact finite stages have equal occupied ranks. -/
theorem relativeOccupied_rank_eq {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) =
      Module.rank (ZMod p) (relativeOccupiedSubmodule p s.B α) := by
  let fA := kaplanskyLinearMap p s.A α (kaplanskyMap p s.A α)
  let fB := kaplanskyLinearMap p s.B α (kaplanskyMap p s.B α)
  calc
    Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) =
        Module.rank (ZMod p) (LinearMap.range fA) := by
      rw [kaplanskyMap_range p s.A α]
    _ = Module.rank (ZMod p) (kaplanskyDomainQuotient p s.A α) :=
      (LinearEquiv.ofInjective fA (kaplanskyMap_injective p s.A α)).rank_eq.symm
    _ = Module.rank (ZMod p) (kaplanskyDomainQuotient p s.B α) :=
      kaplanskyDomain_rank_eq p s
    _ = Module.rank (ZMod p) (LinearMap.range fB) :=
      (LinearEquiv.ofInjective fB (kaplanskyMap_injective p s.B α)).rank_eq
    _ = Module.rank (ZMod p) (relativeOccupiedSubmodule p s.B α) := by
      rw [kaplanskyMap_range p s.B α]

/-- The common occupied rank of a finite stage is finite. -/
theorem relativeOccupied_rank_lt_aleph0 {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) < ℵ₀ := by
  let fA := kaplanskyLinearMap p s.A α (kaplanskyMap p s.A α)
  letI : Module.Finite (ZMod p) (kaplanskyDomainQuotient p s.A α) :=
    kaplanskyDomain_module_finite p s.A s.hAfinite α
  calc
    Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) =
        Module.rank (ZMod p) (LinearMap.range fA) := by
      rw [kaplanskyMap_range p s.A α]
    _ = Module.rank (ZMod p) (kaplanskyDomainQuotient p s.A α) :=
      (LinearEquiv.ofInjective fA (kaplanskyMap_injective p s.A α)).rank_eq.symm
    _ < ℵ₀ := Module.rank_lt_aleph0 _ _

/-- Hill domination at a finite exact stage implies the corresponding ambient
Ulm domination. -/
theorem ulmInvariant_le_of_hillInvariant_le {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α)
    (h : hillInvariant p s.A α ≤ hillInvariant p s.B α) :
    ulmInvariant p α (G := G) ≤ ulmInvariant p α (G := H) := by
  have hocc := relativeOccupied_rank_eq p s
  calc
    ulmInvariant p α (G := G) =
        hillInvariant p s.A α +
          Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) :=
      (relativeUlmInvariant_add_occupiedInvariant p s.A α).symm
    _ ≤ hillInvariant p s.B α +
          Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) :=
      add_le_add_left h _
    _ = hillInvariant p s.B α +
          Module.rank (ZMod p) (relativeOccupiedSubmodule p s.B α) := by rw [hocc]
    _ = ulmInvariant p α (G := H) :=
      relativeUlmInvariant_add_occupiedInvariant p s.B α

/-- Ambient Ulm domination transfers back to Hill domination at any finite
exact stage. -/
theorem hillInvariant_le_of_ulmInvariant_le {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α)
    (h : ulmInvariant p α (G := G) ≤ ulmInvariant p α (G := H)) :
    hillInvariant p s.A α ≤ hillInvariant p s.B α := by
  have hocc := relativeOccupied_rank_eq p s
  have hfin := relativeOccupied_rank_lt_aleph0 p s
  apply (Cardinal.add_le_add_iff_of_lt_aleph0 hfin).1
  calc
    hillInvariant p s.A α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) =
      ulmInvariant p α (G := G) :=
        relativeUlmInvariant_add_occupiedInvariant p s.A α
    _ ≤ ulmInvariant p α (G := H) := h
    _ = hillInvariant p s.B α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p s.B α) :=
      (relativeUlmInvariant_add_occupiedInvariant p s.B α).symm
    _ = hillInvariant p s.B α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p s.A α) := by rw [hocc]

/-- Reverse room domination at a finite exact stage implies domination of the
ambient filtered-socle ranks in the same reverse direction. -/
theorem pSocle_rank_le_of_roomInvariant_reverse {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α)
    (h : roomInvariant p s.B α ≤ roomInvariant p s.A α) :
    Module.rank (ZMod p) (pSocleAt p α (G := H)) ≤
      Module.rank (ZMod p) (pSocleAt p α (G := G)) := by
  have hden := roomSubmodule_rank_eq p s
  calc
    Module.rank (ZMod p) (pSocleAt p α (G := H)) =
        roomInvariant p s.B α +
          Module.rank (ZMod p) (roomSubmodule p s.B α) :=
      (Submodule.rank_quotient_add_rank (roomSubmodule p s.B α)).symm
    _ ≤ roomInvariant p s.A α +
          Module.rank (ZMod p) (roomSubmodule p s.B α) :=
      add_le_add_left h _
    _ = roomInvariant p s.A α +
          Module.rank (ZMod p) (roomSubmodule p s.A α) := by rw [hden]
    _ = Module.rank (ZMod p) (pSocleAt p α (G := G)) :=
      Submodule.rank_quotient_add_rank (roomSubmodule p s.A α)

/-- Ambient filtered-socle domination transfers back to reverse room
domination at any finite exact stage. -/
theorem roomInvariant_reverse_of_pSocle_rank_le {α : Ordinal.{0}}
    (s : UlmStageAt p (G := G) (H := H) α)
    (h : Module.rank (ZMod p) (pSocleAt p α (G := H)) ≤
      Module.rank (ZMod p) (pSocleAt p α (G := G))) :
    roomInvariant p s.B α ≤ roomInvariant p s.A α := by
  have hden := roomSubmodule_rank_eq p s
  have hfin := roomSubmodule_rank_lt_aleph0 p s
  apply (Cardinal.add_le_add_iff_of_lt_aleph0 hfin).1
  calc
    roomInvariant p s.B α +
        Module.rank (ZMod p) (roomSubmodule p s.A α) =
      roomInvariant p s.B α +
        Module.rank (ZMod p) (roomSubmodule p s.B α) := by rw [hden]
    _ = Module.rank (ZMod p) (pSocleAt p α (G := H)) :=
      Submodule.rank_quotient_add_rank (roomSubmodule p s.B α)
    _ ≤ Module.rank (ZMod p) (pSocleAt p α (G := G)) := h
    _ = roomInvariant p s.A α +
        Module.rank (ZMod p) (roomSubmodule p s.A α) :=
      (Submodule.rank_quotient_add_rank (roomSubmodule p s.A α)).symm

/-- Hill domination transfers from an initial finite exact stage to every
other finite exact stage between the same ambient groups. -/
theorem hillInvariant_le_of_initial {α : Ordinal.{0}}
    (initial current : UlmStageAt p (G := G) (H := H) α)
    (h : hillInvariant p initial.A α ≤ hillInvariant p initial.B α) :
    hillInvariant p current.A α ≤ hillInvariant p current.B α :=
  hillInvariant_le_of_ulmInvariant_le p current
    (ulmInvariant_le_of_hillInvariant_le p initial h)

/-- Reverse room domination transfers from an initial finite exact stage to
every other finite exact stage between the same ambient groups. -/
theorem roomInvariant_reverse_of_initial {α : Ordinal.{0}}
    (initial current : UlmStageAt p (G := G) (H := H) α)
    (h : roomInvariant p initial.B α ≤ roomInvariant p initial.A α) :
    roomInvariant p current.B α ≤ roomInvariant p current.A α :=
  roomInvariant_reverse_of_pSocle_rank_le p current
    (pSocle_rank_le_of_roomInvariant_reverse p initial h)

end ExactStageTransfer
