import Lib.BackForth.KernelRoom

/-!
# The feasible height-cell base map

This file constructs the group-specific feasible map required by the affine
Height--Rado theorem.  A source basis vector of reach `r i` has a unique class
in the reachable quotient at that level.  Its forced jump residue is carried
across the partial homomorphism and then lifted through the surjective target
reachable-to-jump map.  Extending these chosen target lifts linearly gives the
base map `heightCellBaseMap`.

The main theorem `heightCellBaseMap_mem_reachable` proves the genuine
all-vector height condition: the base map sends the complete source filtered
space at level `β` into the target reachable filtered space at `β`.
-/

noncomputable section

open Module Ordinal

universe u v

variable (p : ℕ) [hp : Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace HeightCell

variable {F : AddSubgroup B} {E : AddSubgroup A}

/-- A compatible basis vector belongs to the reachable subspace at its own
reach. -/
theorem basis_mem_reachable
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : b i ∈ reachableSubspace p F (r i) := by
  rw [hcompat (r i)]
  apply Submodule.subset_span
  refine ⟨i, ?_, rfl⟩
  show i ∈ {j : ι | r i ≤ r j}
  change r i ≤ r i
  exact le_refl (r i)

/-- The source basis vector, regarded as a class in the reachable quotient at
its own reach. -/
noncomputable def sourceAtReach
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : reachableSpace p F 0 (r i) :=
  (reachableEquivSubspace p F (r i)).symm
    ⟨b i, basis_mem_reachable p b r hcompat i⟩

@[simp] theorem sourceAtReach_toRoom
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    reachableToRoomZeroLinearMap p F (r i)
        (sourceAtReach p b r hcompat i) = b i := by
  change ((reachableEquivSubspace p F (r i))
      ((reachableEquivSubspace p F (r i)).symm
        ⟨b i, basis_mem_reachable p b r hcompat i⟩) : room p F 0) = b i
  simp

/-- The forced target jump class of one source basis vector at its reach. -/
noncomputable def basisJumpTarget
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : jumpSpace p E (r i) :=
  jumpLinearMap p φ (hfloor (Order.succ (r i))) (hfloor (r i))
    (reachableToJumpLinearMap p F (r i) (sourceAtReach p b r hcompat i))

/-- Choose a target reachable class whose jump residue is the forced image of
the source basis residue.  Existence is exactly surjectivity in the D-21
reachable exact sequence. -/
noncomputable def targetAtReach
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) : reachableSpace p E 0 (r i) :=
  Classical.choose
    (reachableToJumpLinearMap_surjective p E (r i)
      (basisJumpTarget p φ hfloor b r hcompat i))

theorem targetAtReach_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    reachableToJumpLinearMap p E (r i)
        (targetAtReach p φ hfloor b r hcompat i) =
      basisJumpTarget p φ hfloor b r hcompat i :=
  Classical.choose_spec
    (reachableToJumpLinearMap_surjective p E (r i)
      (basisJumpTarget p φ hfloor b r hcompat i))

/-- Restrict the source basis class from its own reach to any earlier level. -/
noncomputable def sourceAtLevel
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    reachableSpace p F 0 β :=
  reachableRestriction p F hβi (sourceAtReach p b r hcompat i)

/-- Restrict the chosen target lift from the basis vector's own reach to an
earlier level. -/
noncomputable def targetAtLevel
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    reachableSpace p E 0 β :=
  reachableRestriction p E hβi
    (targetAtReach p φ hfloor b r hcompat i)

@[simp] theorem sourceAtLevel_toRoom
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    reachableToRoomZeroLinearMap p F β
        (sourceAtLevel p b r hcompat hβi) = b i := by
  rw [sourceAtLevel, reachableRestriction_toRoomZero,
    sourceAtReach_toRoom]

/-- The residue equality chosen at a basis vector's own reach remains exact
at every earlier height. -/
theorem targetAtLevel_residue
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    reachableToJumpLinearMap p E β
        (targetAtLevel p φ hfloor b r hcompat hβi) =
      jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (reachableToJumpLinearMap p F β
          (sourceAtLevel p b r hcompat hβi)) := by
  calc
    reachableToJumpLinearMap p E β
        (targetAtLevel p φ hfloor b r hcompat hβi) =
        jumpRestriction p E hβi
          (reachableToJumpLinearMap p E (r i)
            (targetAtReach p φ hfloor b r hcompat i)) :=
      reachableToJump_restriction p E hβi _
    _ = jumpRestriction p E hβi
        (basisJumpTarget p φ hfloor b r hcompat i) := by
      rw [targetAtReach_residue]
    _ = jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (jumpRestriction p F hβi
          (reachableToJumpLinearMap p F (r i)
            (sourceAtReach p b r hcompat i))) := by
      exact jumpRestriction_jumpLinearMap p φ hfloor hβi _
    _ = jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (reachableToJumpLinearMap p F β
          (sourceAtLevel p b r hcompat hβi)) := by
      rw [sourceAtLevel, reachableToJump_restriction]

/-- The feasible height-cell base map.  On a basis vector it is the global
room image of a target reachable lift of the forced jump residue. -/
noncomputable def heightCellBaseMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F)) :
    room p F 0 →ₗ[ZMod p] room p E 0 :=
  b.constr (ZMod p) (fun i =>
    reachableToRoomZeroLinearMap p E (r i)
      (targetAtReach p φ hfloor b r hcompat i))

@[simp] theorem heightCellBaseMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    heightCellBaseMap p φ hfloor b r hcompat (b i) =
      reachableToRoomZeroLinearMap p E (r i)
        (targetAtReach p φ hfloor b r hcompat i) :=
  b.constr_basis (ZMod p) _ i

/-- Every basis value of the height-cell map has its required reach. -/
theorem heightCellBaseMap_basis_mem_reachable
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (i : ι) :
    heightCellBaseMap p φ hfloor b r hcompat (b i) ∈
      reachableSubspace p E (r i) := by
  rw [heightCellBaseMap_basis]
  exact ⟨targetAtReach p φ hfloor b r hcompat i, rfl⟩

/-- **All-vector feasibility of the group-specific base map.**  For every
height `β`, the complete compatible source reach space maps into the target
reachable space at the same height. -/
theorem heightCellBaseMap_mem_reachable
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) (q : room p F 0)
    (hq : q ∈ reachableSubspace p F β) :
    heightCellBaseMap p φ hfloor b r hcompat q ∈
      reachableSubspace p E β := by
  exact HeightRado.map_mem_of_compatible
    (heightCellBaseMap p φ hfloor b r hcompat)
    (reachableSubspace p F) (reachableSubspace p E) b r hcompat
    (fun _ _ h => reachableSubspace_antitone p E h)
    (heightCellBaseMap_basis_mem_reachable p φ hfloor b r hcompat)
    β q hq

/-- Restrict the feasible base map to the source reachable subspace and express
its value in the target reachable quotient. -/
noncomputable def heightCellReachMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) :
    reachableSubspace p F β →ₗ[ZMod p] reachableSpace p E 0 β :=
  (reachableEquivSubspace p E β).symm.toLinearMap.comp
    (((heightCellBaseMap p φ hfloor b r hcompat).domRestrict
      (reachableSubspace p F β)).codRestrict
        (reachableSubspace p E β)
        (fun q => heightCellBaseMap_mem_reachable p φ hfloor b r hcompat
          β (q : room p F 0) q.property))

/-- The jump residue of the feasible base map on one source reach level. -/
noncomputable def heightCellJumpMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) :
    reachableSubspace p F β →ₗ[ZMod p] jumpSpace p E β :=
  (reachableToJumpLinearMap p E β).comp
    (heightCellReachMap p φ hfloor b r hcompat β)

/-- The intrinsic selector residue map, transported from the abstract source
reachable quotient to its concrete global subspace. -/
noncomputable def selectorSubspaceMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    (β : Ordinal.{0}) :
    reachableSubspace p F β →ₗ[ZMod p] jumpSpace p E β :=
  (KernelRoom.selectorResidueMap p φ
    (hfloor (Order.succ β)) (hfloor β)).comp
      (reachableEquivSubspace p F β).symm.toLinearMap

/-- At every earlier level, the reachable representative of a basis value of
the base map is the restricted chosen target lift. -/
theorem heightCellReachMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    heightCellReachMap p φ hfloor b r hcompat β
        ⟨b i, reachableSubspace_antitone p F hβi
          (basis_mem_reachable p b r hcompat i)⟩ =
      targetAtLevel p φ hfloor b r hcompat hβi := by
  apply reachableToRoomZeroLinearMap_injective p E β
  simp only [heightCellReachMap, LinearMap.comp_apply]
  change reachableToRoomZeroLinearMap p E β
      ((reachableEquivSubspace p E β).symm
        ⟨heightCellBaseMap p φ hfloor b r hcompat (b i),
          heightCellBaseMap_mem_reachable p φ hfloor b r hcompat β (b i)
            (reachableSubspace_antitone p F hβi
              (basis_mem_reachable p b r hcompat i))⟩) =
    reachableToRoomZeroLinearMap p E β
      (targetAtLevel p φ hfloor b r hcompat hβi)
  rw [reachableEquivSubspace_symm_toRoomZero]
  change heightCellBaseMap p φ hfloor b r hcompat (b i) =
    reachableToRoomZeroLinearMap p E β
      (targetAtLevel p φ hfloor b r hcompat hβi)
  rw [heightCellBaseMap_basis, targetAtLevel,
    reachableRestriction_toRoomZero]

/-- The source reachable equivalence sends a concrete basis vector at level
`β` to the corresponding restricted source class. -/
theorem sourceEquiv_symm_basis
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    (reachableEquivSubspace p F β).symm
        ⟨b i, reachableSubspace_antitone p F hβi
          (basis_mem_reachable p b r hcompat i)⟩ =
      sourceAtLevel p b r hcompat hβi := by
  apply reachableToRoomZeroLinearMap_injective p F β
  rw [reachableEquivSubspace_symm_toRoomZero]
  change b i = reachableToRoomZeroLinearMap p F β
    (sourceAtLevel p b r hcompat hβi)
  rw [sourceAtLevel_toRoom]

/-- The two residue maps agree on every compatible basis vector present at
level `β`. -/
theorem heightCellJumpMap_basis
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    {β : Ordinal.{0}} {i : ι} (hβi : β ≤ r i) :
    heightCellJumpMap p φ hfloor b r hcompat β
        ⟨b i, reachableSubspace_antitone p F hβi
          (basis_mem_reachable p b r hcompat i)⟩ =
      selectorSubspaceMap p φ hfloor β
        ⟨b i, reachableSubspace_antitone p F hβi
          (basis_mem_reachable p b r hcompat i)⟩ := by
  rw [heightCellJumpMap, LinearMap.comp_apply, heightCellReachMap_basis,
    selectorSubspaceMap, LinearMap.comp_apply]
  have hsource :
      (reachableEquivSubspace p F β).symm
          ⟨b i, reachableSubspace_antitone p F hβi
            (basis_mem_reachable p b r hcompat i)⟩ =
        sourceAtLevel p b r hcompat hβi :=
    sourceEquiv_symm_basis p b r hcompat hβi
  change reachableToJumpLinearMap p E β
      (targetAtLevel p φ hfloor b r hcompat hβi) =
    jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
      (reachableToJumpLinearMap p F β
        ((reachableEquivSubspace p F β).symm
          ⟨b i, reachableSubspace_antitone p F hβi
            (basis_mem_reachable p b r hcompat i)⟩))
  rw [hsource]
  exact targetAtLevel_residue p φ hfloor b r hcompat hβi

/-- **The feasible base map has exactly the concrete selector residue at every
height.**  Compatibility of the basis upgrades the preceding basiswise
naturality calculation to equality of linear maps on the entire source
reachable subspace. -/
theorem heightCellJumpMap_eq_selectorSubspaceMap
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) :
    heightCellJumpMap p φ hfloor b r hcompat β =
      selectorSubspaceMap p φ hfloor β := by
  let f := heightCellJumpMap p φ hfloor b r hcompat β
  let g := selectorSubspaceMap p φ hfloor β
  let S : Set (room p F 0) := b '' {i | β ≤ r i}
  let lift : ∀ x : room p F 0, x ∈ Submodule.span (ZMod p) S →
      reachableSubspace p F β := fun x hx =>
    ⟨x, by
      rw [hcompat β]
      exact hx⟩
  apply LinearMap.ext
  intro q
  have hqspan : (q : room p F 0) ∈ Submodule.span (ZMod p) S := by
    rw [← hcompat β]
    exact q.property
  have hmain : f (lift (q : room p F 0) hqspan) =
      g (lift (q : room p F 0) hqspan) := by
    refine Submodule.span_induction (p := fun x hx =>
      f (lift x hx) = g (lift x hx)) ?_ ?_ ?_ ?_ hqspan
    · rintro x ⟨i, hi, rfl⟩
      change f ⟨b i, _⟩ = g ⟨b i, _⟩
      simpa only [f, g] using
        heightCellJumpMap_basis p φ hfloor b r hcompat hi
    · change f (⟨0, _⟩ : reachableSubspace p F β) =
        g (⟨0, _⟩ : reachableSubspace p F β)
      convert (show f 0 = g 0 by simp) using 1
    · intro x y hx hy hxfg hyfg
      have hlift : lift (x + y) (Submodule.add_mem _ hx hy) =
          lift x hx + lift y hy := Subtype.ext rfl
      rw [hlift, map_add, map_add, hxfg, hyfg]
    · intro a x hx hxfg
      have hlift : lift (a • x) (Submodule.smul_mem _ a hx) =
          a • lift x hx := Subtype.ext rfl
      rw [hlift, map_smul, map_smul, hxfg]
  have hliftq : lift (q : room p F 0) hqspan = q := Subtype.ext rfl
  simpa only [f, g, hliftq] using hmain

/-- The kernel of the affine Height--Rado residue map is the kernel of the
target jump residue of the constructed base map. -/
theorem ker_heightCellResidue_eq_ker_heightCellJump
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) :
    LinearMap.ker (HeightRado.residueMap
      (heightCellBaseMap p φ hfloor b r hcompat)
      (reachableSubspace p F) (roomSubspace p E) β) =
      LinearMap.ker (heightCellJumpMap p φ hfloor b r hcompat β) := by
  ext q
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change (roomSubspace p E β).mkQ
      (heightCellBaseMap p φ hfloor b r hcompat (q : room p F 0)) = 0 ↔
    reachableToJumpLinearMap p E β
      (heightCellReachMap p φ hfloor b r hcompat β q) = 0
  have hexact := reachableToRoomZero_mem_roomSubspace_iff p E β
    (heightCellReachMap p φ hfloor b r hcompat β q)
  have hglobal : reachableToRoomZeroLinearMap p E β
      (heightCellReachMap p φ hfloor b r hcompat β q) =
      heightCellBaseMap p φ hfloor b r hcompat (q : room p F 0) := by
    simp [heightCellReachMap]
  rw [hglobal] at hexact
  constructor
  · intro hq
    exact hexact.mp ((Submodule.Quotient.mk_eq_zero _).mp hq)
  · intro hq
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hexact.mpr hq)

/-- **The missing residue-rank bridge.**  The feasible height-cell base map
has a residue kernel of exactly the same rank as the concrete group-theoretic
selector `χ_β`. -/
theorem heightCellBaseMap_residueKernel_rank
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (β : Ordinal.{0}) :
    Module.rank (ZMod p)
        (LinearMap.ker (HeightRado.residueMap
          (heightCellBaseMap p φ hfloor b r hcompat)
          (reachableSubspace p F) (roomSubspace p E) β)) =
      Module.rank (ZMod p)
        (LinearMap.ker (KernelRoom.selectorResidueMap p φ
          (hfloor (Order.succ β)) (hfloor β))) := by
  rw [ker_heightCellResidue_eq_ker_heightCellJump]
  rw [heightCellJumpMap_eq_selectorSubspaceMap]
  change Module.rank (ZMod p)
      (LinearMap.ker ((KernelRoom.selectorResidueMap p φ
        (hfloor (Order.succ β)) (hfloor β)).comp
          (reachableEquivSubspace p F β).symm.toLinearMap)) = _
  calc
    Module.rank (ZMod p)
        (LinearMap.ker ((KernelRoom.selectorResidueMap p φ
          (hfloor (Order.succ β)) (hfloor β)).comp
            (reachableEquivSubspace p F β).symm.toLinearMap)) =
        Module.rank (ZMod p)
            (LinearMap.ker
              (reachableEquivSubspace p F β).symm.toLinearMap) +
          Module.rank (ZMod p)
            (LinearMap.ker (KernelRoom.selectorResidueMap p φ
              (hfloor (Order.succ β)) (hfloor β))) :=
      KernelRoom.rank_ker_comp_of_surjective p
        (reachableEquivSubspace p F β).symm.toLinearMap
        (KernelRoom.selectorResidueMap p φ
          (hfloor (Order.succ β)) (hfloor β))
        (reachableEquivSubspace p F β).symm.surjective
    _ = Module.rank (ZMod p)
        (LinearMap.ker (KernelRoom.selectorResidueMap p φ
          (hfloor (Order.succ β)) (hfloor β))) := by
      rw [LinearMap.ker_eq_bot.mpr
        (reachableEquivSubspace p F β).symm.injective]
      simp

/-- **Finite height-cell selection with no abstract base-map hypotheses.**
The group-specific base map and its residue identification are now constructed
internally; the room--kernel budget is the only remaining quantitative input
to the finite affine Rado step. -/
theorem hasInjectiveHeightCellSelection
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (room p F 0)]
    [FiniteDimensional (ZMod p) (room p E 0)]
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Module.rank (ZMod p)
          (LinearMap.ker (KernelRoom.selectorResidueMap p φ
            (hfloor (Order.succ β)) (hfloor β))) ≤
        roomInvariant p E β) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := by
  exact KernelRoom.hasInjectiveHeightSelection p φ hfloor
    (heightCellBaseMap p φ hfloor b r hcompat) b r hcompat
    (heightCellBaseMap_residueKernel_rank p φ hfloor b r hcompat)
    hbudget

/-- The same conclusion stated directly from D-23's room--kernel budget. -/
theorem hasInjectiveHeightCellSelection_of_budget
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (room p F 0)]
    [FiniteDimensional (ZMod p) (room p E 0)]
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := by
  apply hasInjectiveHeightCellSelection p φ hfloor b r hcompat
  intro β
  exact (Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le
    p φ β (hfloor (Order.succ β)) (hfloor β)).mp (hbudget β)

end HeightCell
