import Lib.BackForth.HeightCell

/-!
# Room--kernel regression tests

These compile-time regressions pin the three pieces the corrected formalization
must retain: proof-independent jump-kernel rank, the D-23 kernel splitting, and
the automatic budget above an absorbed source tail.
-/

open Module Ordinal

universe u v

variable (p : ℕ) [Fact p.Prime]

noncomputable section

section Linear

variable {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
variable [Module (ZMod p) X] [Module (ZMod p) Y]

/-- Precomposition by the identity specializes the D-23 split to the ordinary
kernel rank. -/
example (f : X →ₗ[ZMod p] Y) :
    Module.rank (ZMod p) (LinearMap.ker (f.comp LinearMap.id)) =
      Module.rank (ZMod p) (LinearMap.ker (LinearMap.id : X →ₗ[ZMod p] X)) +
        Module.rank (ZMod p) (LinearMap.ker f) := by
  apply KernelRoom.rank_ker_comp_of_surjective p
  intro x
  exact ⟨x, rfl⟩

end Linear

section Reachable

variable {G : Type u} [AddCommGroup G]
variable (E : AddSubgroup G) (β : Ordinal.{0})

/-- The canonical map is independent of which reachable decomposition is used. -/
example (x : reachableNum p E 0 β) (e : G) (he : e ∈ E)
    (hres : (x : G) - e ∈ ulmSubgroup p β) :
    reachableToJumpLinearMap p E β
        ((reachableDenSubmodule p E 0 β).mkQ x) =
      QuotientAddGroup.mk (reachableAnchorMultipleOf p E β x e he hres) :=
  reachableToJumpLinearMap_mk_of_anchor p E β x e he hres

/-- The paper's canonical reachable map is onto. -/
example : Function.Surjective (reachableToJumpLinearMap p E β) :=
  reachableToJumpLinearMap_surjective p E β

/-- Its kernel is the room, not merely a space of the same rank. -/
example : room p E β ≃ₗ[ZMod p]
    LinearMap.ker (reachableToJumpLinearMap p E β) :=
  roomEquivReachableKernel p E β

/-- The `C/R/S` exact sequence gives the cardinal rank identity. -/
example : reachableInvariant p E 0 β =
    roomInvariant p E β + jumpInvariant p E β :=
  reachable_rank_eq_room_add_jump p E β

/-- Each reachable quotient is concretely a subspace of the global socle
quotient. -/
example : Function.Injective (reachableToRoomZeroLinearMap p E β) :=
  reachableToRoomZeroLinearMap_injective p E β

/-- Those concrete reachable subspaces are nested with the height
filtration. -/
example {γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    reachableSubspace p E γ ≤ reachableSubspace p E β :=
  reachableSubspace_antitone p E hβγ

/-- Restriction preserves the global room class. -/
example {γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (q : reachableSpace p E 0 γ) :
    reachableToRoomZeroLinearMap p E β (reachableRestriction p E hβγ q) =
      reachableToRoomZeroLinearMap p E γ q :=
  reachableRestriction_toRoomZero p E hβγ q

/-- Restriction commutes with the reachable jump residue. -/
example {γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (q : reachableSpace p E 0 γ) :
    reachableToJumpLinearMap p E β (reachableRestriction p E hβγ q) =
      jumpRestriction p E hβγ (reachableToJumpLinearMap p E γ q) :=
  reachableToJump_restriction p E hβγ q

/-- The target room at each height is concretely embedded in the global room. -/
example : Function.Injective (roomToRoomZeroLinearMap p E β) :=
  roomToRoomZeroLinearMap_injective p E β

/-- The concrete target direction has the original room rank. -/
example : Module.rank (ZMod p) (roomSubspace p E β) =
    roomInvariant p E β :=
  roomSubspace_rank p E β

/-- Target-room directions are nested with height. -/
example {γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    roomSubspace p E γ ≤ roomSubspace p E β :=
  roomSubspace_antitone p E hβγ

end Reachable

section Stage

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
variable {β : Ordinal.{0}}
variable (hsucc : IsHeightFloorAt p φ (Order.succ β))
variable (hβ : IsHeightFloorAt p φ β)

/-- Absorbing the source tail makes the corrected budget automatic. -/
example (htail : ulmSubgroup p β (G := B) ≤ F) :
    Survival.KernelRoomBudgetAt p φ β hsucc hβ :=
  Survival.KernelRoomBudgetAt.of_ulmSubgroup_le p φ β hsucc hβ htail

/-- The jump-kernel cardinal cannot depend on proof terms. -/
example (hsucc' : IsHeightFloorAt p φ (Order.succ β))
    (hβ' : IsHeightFloorAt p φ β) :
    jumpKernelInvariant p φ hsucc hβ =
      jumpKernelInvariant p φ hsucc' hβ' :=
  jumpKernelInvariant_proof_irrel p φ hsucc hsucc' hβ hβ'

/-- D-23 is now the rank of the actual selector residue kernel. -/
example :
    Module.rank (ZMod p)
        (LinearMap.ker (KernelRoom.selectorResidueMap p φ hsucc hβ)) =
      roomInvariant p F β + jumpKernelInvariant p φ hsucc hβ :=
  KernelRoom.rank_selectorKernel_eq_room_add_jumpKernel p φ hsucc hβ

/-- Consequently the quantitative budget is exactly selector-kernel capacity. -/
example : Survival.KernelRoomBudgetAt p φ β hsucc hβ ↔
    Module.rank (ZMod p)
        (LinearMap.ker (KernelRoom.selectorResidueMap p φ hsucc hβ)) ≤
      roomInvariant p E β :=
  Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le p φ β hsucc hβ

/-- Induced jump maps commute with restriction in the height filtration. -/
example (hfloor : IsHeightFloorOn p φ) {γ : Ordinal.{0}}
    (hβγ : β ≤ γ) (q : jumpSpace p F γ) :
    jumpRestriction p E hβγ
        (jumpLinearMap p φ (hfloor (Order.succ γ)) (hfloor γ) q) =
      jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (jumpRestriction p F hβγ q) :=
  jumpRestriction_jumpLinearMap p φ hfloor hβγ q

end Stage

section HeightSelection

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
variable (hfloor : IsHeightFloorOn p φ)
variable {ι : Type v} [Fintype ι]
variable [FiniteDimensional (ZMod p) (room p F 0)]
variable [FiniteDimensional (ZMod p) (room p E 0)]

/-- Once the height-equation solution has the intrinsic selector residue,
the room--kernel budgets feed the concrete affine Height--Rado theorem. -/
example (Φ₀ : room p F 0 →ₗ[ZMod p] room p E 0)
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (reachableSubspace p F))
    (hresidue : ∀ β : Ordinal.{0},
      Module.rank (ZMod p)
          (LinearMap.ker (HeightRado.residueMap Φ₀
            (reachableSubspace p F) (roomSubspace p E) β)) =
        Module.rank (ZMod p)
          (LinearMap.ker (KernelRoom.selectorResidueMap p φ
            (hfloor (Order.succ β)) (hfloor β))))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess Φ₀ (roomSubspace p E) b r) := by
  apply KernelRoom.hasInjectiveHeightSelection p φ hfloor Φ₀ b r hcompat hresidue
  intro β
  exact (Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le
    p φ β (hfloor (Order.succ β)) (hfloor β)).mp (hbudget β)

end HeightSelection

section ConstructedHeightSelection

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
variable (hfloor : IsHeightFloorOn p φ)
variable {ι : Type v} [Fintype ι]
variable [FiniteDimensional (ZMod p) (room p F 0)]
variable [FiniteDimensional (ZMod p) (room p E 0)]

/-- The group-specific base map and residue identification are constructed,
so a room--kernel budget now yields the selector directly. -/
example (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := by
  exact HeightCell.hasInjectiveHeightCellSelection_of_budget
    p φ hfloor b r hcompat hbudget

end ConstructedHeightSelection
