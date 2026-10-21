import Lib.BackForth.Survival
import Lib.BackForth.Reachable
import Lib.BackForth.HeightRado

/-!
# The room--kernel stage

This file introduces the quantitative invariant selected by D-23.  At a height
`β`, its demand is the remaining source room plus the kernel of the induced jump
map; the target room is the supply:

`roomInvariant p src β + jumpKernelInvariant p iso floor floor ≤
  roomInvariant p tgt β`.

The old `Survival.Stage` keeps only two endpoint shadows of this inequality:
room domination, and jump-map injectivity when target room is zero.  Theorems
below prove that every room--kernel stage supplies those old fields.

The first section also formalizes the linear-algebra identity behind D-23.  If
`π : X → Y` is onto, then

`rank ker (f ∘ π) = rank ker π + rank ker f`.

This is the abstract rank form of the exact sequence which splits total finite
demand into unanchored room demand and anchored jump-kernel demand.
-/

open Module Ordinal

universe u v

variable (p : ℕ) [hp : Fact p.Prime]

namespace KernelRoom

variable {X Y Z : Type u}
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module (ZMod p) X] [Module (ZMod p) Y] [Module (ZMod p) Z]

/-- **The abstract finite-demand estimate.**  Suppose `d` sends a demand space
into the kernel of the forced residue map, and the kernel of `d` injects into
source room.  Then total demand is bounded by room plus the residue kernel.

This is the rank-nullity core of Lemma 2.1 in the Height--Rado proof.  The
group-specific work left for the demand formalization is precisely to construct
`d` and the kernel injection. -/
theorem rank_demand_le_room_add_kernel
    {M R : Type u} [AddCommGroup M] [AddCommGroup R]
    [Module (ZMod p) M] [Module (ZMod p) R]
    (f : Y →ₗ[ZMod p] Z) (d : M →ₗ[ZMod p] LinearMap.ker f)
    (toRoom : LinearMap.ker d →ₗ[ZMod p] R)
    (htoRoom : Function.Injective toRoom) :
    Module.rank (ZMod p) M ≤
      Module.rank (ZMod p) R + Module.rank (ZMod p) (LinearMap.ker f) := by
  calc
    Module.rank (ZMod p) M =
        Module.rank (ZMod p) (LinearMap.range d) +
          Module.rank (ZMod p) (LinearMap.ker d) :=
      (LinearMap.rank_range_add_rank_ker d).symm
    _ ≤ Module.rank (ZMod p) (LinearMap.ker f) + Module.rank (ZMod p) R :=
      add_le_add (Submodule.rank_le _) (toRoom.rank_le_of_injective htoRoom)
    _ = Module.rank (ZMod p) R + Module.rank (ZMod p) (LinearMap.ker f) :=
      add_comm _ _

/-- When the demand map is onto and its kernel is exactly the room, the demand
rank is room plus jump-kernel rank.  This is the equality used for a finite full
source group. -/
theorem rank_demand_eq_room_add_kernel
    {M R : Type u} [AddCommGroup M] [AddCommGroup R]
    [Module (ZMod p) M] [Module (ZMod p) R]
    (f : Y →ₗ[ZMod p] Z) (d : M →ₗ[ZMod p] LinearMap.ker f)
    (hd : Function.Surjective d)
    (roomEquiv : LinearMap.ker d ≃ₗ[ZMod p] R) :
    Module.rank (ZMod p) M =
      Module.rank (ZMod p) R + Module.rank (ZMod p) (LinearMap.ker f) := by
  calc
    Module.rank (ZMod p) M =
        Module.rank (ZMod p) (LinearMap.ker f) +
          Module.rank (ZMod p) (LinearMap.ker d) :=
      LinearMap.rank_eq_of_surjective hd
    _ = Module.rank (ZMod p) (LinearMap.ker f) + Module.rank (ZMod p) R := by
      rw [roomEquiv.rank_eq]
    _ = Module.rank (ZMod p) R + Module.rank (ZMod p) (LinearMap.ker f) :=
      add_comm _ _

/-- Restrict an onto map `π` to the kernel of `f ∘ π`, with codomain
the kernel of `f`. -/
noncomputable def kerCompToKer (π : X →ₗ[ZMod p] Y) (f : Y →ₗ[ZMod p] Z) :
    LinearMap.ker (f.comp π) →ₗ[ZMod p] LinearMap.ker f where
  toFun x := ⟨π (x : X), by
    change f (π (x : X)) = 0
    exact x.property⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

/-- If `π` is onto, its restriction from `ker (f ∘ π)` onto `ker f` is
onto as well. -/
theorem kerCompToKer_surjective (π : X →ₗ[ZMod p] Y) (f : Y →ₗ[ZMod p] Z)
    (hπ : Function.Surjective π) : Function.Surjective (kerCompToKer p π f) := by
  intro y
  obtain ⟨x, hx⟩ := hπ (y : Y)
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change f (π x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

/-- Include `ker π` into the kernel of the restricted map
`kerCompToKer`. -/
noncomputable def kerToKerCompKernel (π : X →ₗ[ZMod p] Y) (f : Y →ₗ[ZMod p] Z) :
    LinearMap.ker π →ₗ[ZMod p] LinearMap.ker (kerCompToKer p π f) where
  toFun x :=
    ⟨⟨(x : X), by
      change f (π (x : X)) = 0
      rw [x.property]
      exact map_zero f⟩, Subtype.ext x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The kernel of `kerCompToKer` is canonically equivalent to `ker π`. -/
noncomputable def kerEquivKerCompToKer (π : X →ₗ[ZMod p] Y) (f : Y →ₗ[ZMod p] Z) :
    LinearMap.ker π ≃ₗ[ZMod p] LinearMap.ker (kerCompToKer p π f) :=
  LinearEquiv.ofBijective (kerToKerCompKernel p π f)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : LinearMap.ker (kerCompToKer p π f) =>
          ((z : LinearMap.ker (f.comp π)) : X)) hxy,
    by
      intro y
      have hy : π ((y : LinearMap.ker (f.comp π)) : X) = 0 := by
        exact congrArg Subtype.val y.property
      refine ⟨⟨((y : LinearMap.ker (f.comp π)) : X), hy⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl⟩

/-- **The kernel-splitting identity behind D-23.**  Precomposing a linear map
with a surjection adds exactly the kernel rank of the surjection. -/
theorem rank_ker_comp_of_surjective (π : X →ₗ[ZMod p] Y) (f : Y →ₗ[ZMod p] Z)
    (hπ : Function.Surjective π) :
    Module.rank (ZMod p) (LinearMap.ker (f.comp π)) =
      Module.rank (ZMod p) (LinearMap.ker π) +
        Module.rank (ZMod p) (LinearMap.ker f) := by
  calc
    Module.rank (ZMod p) (LinearMap.ker (f.comp π)) =
        Module.rank (ZMod p) (LinearMap.ker f) +
          Module.rank (ZMod p) (LinearMap.ker (kerCompToKer p π f)) :=
      LinearMap.rank_eq_of_surjective (kerCompToKer_surjective p π f hπ)
    _ = Module.rank (ZMod p) (LinearMap.ker f) +
        Module.rank (ZMod p) (LinearMap.ker π) := by
      rw [← (kerEquivKerCompToKer p π f).rank_eq]
    _ = Module.rank (ZMod p) (LinearMap.ker π) +
        Module.rank (ZMod p) (LinearMap.ker f) := add_comm _ _

end KernelRoom

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace KernelRoom

/-! ### The concrete D-23 exact sequence -/

/-- The height-selector residue map
`χ_β = ḡ_β ∘ π^B_β : C_{B,F}(0,β) → S_{A,E}(β)`. -/
noncomputable def selectorResidueMap {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    reachableSpace p F 0 β →ₗ[ZMod p] jumpSpace p E β :=
  (jumpLinearMap p φ hsucc hβ).comp (reachableToJumpLinearMap p F β)

/-- Restriction of `π^B_β` sends `ker χ_β` onto `ker ḡ_β`. -/
noncomputable def selectorKernelToJump {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    LinearMap.ker (selectorResidueMap p φ hsucc hβ) →ₗ[ZMod p]
      LinearMap.ker (jumpLinearMap p φ hsucc hβ) :=
  kerCompToKer p (reachableToJumpLinearMap p F β)
    (jumpLinearMap p φ hsucc hβ)

/-- The right-hand map in the D-23 kernel sequence is onto. -/
theorem selectorKernelToJump_surjective
    {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    Function.Surjective (selectorKernelToJump p φ hsucc hβ) :=
  kerCompToKer_surjective p (reachableToJumpLinearMap p F β)
    (jumpLinearMap p φ hsucc hβ)
    (reachableToJumpLinearMap_surjective p F β)

/-- The kernel of `ker χ_β → ker ḡ_β` is canonically the source room.
Together with `selectorKernelToJump_surjective`, this is the exact sequence

`0 → R_{B,F}(β) → ker χ_β → ker ḡ_β → 0`.
-/
noncomputable def roomEquivSelectorKernelKernel
    {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    room p F β ≃ₗ[ZMod p]
      LinearMap.ker (selectorKernelToJump p φ hsucc hβ) :=
  (roomEquivReachableKernel p F β).trans
    (kerEquivKerCompToKer p (reachableToJumpLinearMap p F β)
      (jumpLinearMap p φ hsucc hβ))

/-- **D-23, concrete kernel identity.**  The selector kernel is exactly source
room plus the kernel of the induced jump map. -/
theorem rank_selectorKernel_eq_room_add_jumpKernel
    {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    Module.rank (ZMod p)
        (LinearMap.ker (selectorResidueMap p φ hsucc hβ)) =
      roomInvariant p F β + jumpKernelInvariant p φ hsucc hβ := by
  unfold selectorResidueMap roomInvariant jumpKernelInvariant
  calc
    Module.rank (ZMod p)
        (LinearMap.ker ((jumpLinearMap p φ hsucc hβ).comp
          (reachableToJumpLinearMap p F β))) =
        Module.rank (ZMod p)
            (LinearMap.ker (reachableToJumpLinearMap p F β)) +
          Module.rank (ZMod p)
            (LinearMap.ker (jumpLinearMap p φ hsucc hβ)) :=
      rank_ker_comp_of_surjective p (reachableToJumpLinearMap p F β)
        (jumpLinearMap p φ hsucc hβ)
        (reachableToJumpLinearMap_surjective p F β)
    _ = Module.rank (ZMod p) (room p F β) +
        Module.rank (ZMod p)
          (LinearMap.ker (jumpLinearMap p φ hsucc hβ)) := by
      rw [← (roomEquivReachableKernel p F β).rank_eq]

/-! ### Assembly with the affine Height--Rado theorem -/

/-- **Room--kernel budget supplies the Rado selector.**

Suppose `Φ₀ : R_{B,F}(0) → R_{A,E}(0)` is a solution of the height equations,
expressed by the intrinsic statement that its residue kernel on each concrete
reachable subspace has the same rank as `ker χ_β`.  If a source basis is
compatible with those reachable subspaces, then the D-23 room--kernel budget
produces an injective choice from all affine height access sets.

This theorem is the formal composition of D-21, D-23, and the abstract D-22
Height--Rado theorem.  The remaining group-specific construction is now
isolated in the two explicit inputs `Φ₀` and `hresidue`. -/
theorem hasInjectiveHeightSelection
    {F : AddSubgroup B} {E : AddSubgroup A}
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {ι : Type v} [Fintype ι]
    [FiniteDimensional (ZMod p) (room p F 0)]
    [FiniteDimensional (ZMod p) (room p E 0)]
    (Φ₀ : room p F 0 →ₗ[ZMod p] room p E 0)
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r
      (reachableSubspace p F))
    (hresidue : ∀ β : Ordinal.{0},
      Module.rank (ZMod p)
          (LinearMap.ker (HeightRado.residueMap Φ₀
            (reachableSubspace p F) (roomSubspace p E) β)) =
        Module.rank (ZMod p)
          (LinearMap.ker (selectorResidueMap p φ
            (hfloor (Order.succ β)) (hfloor β))))
    (hbudget : ∀ β : Ordinal.{0},
      Module.rank (ZMod p)
          (LinearMap.ker (selectorResidueMap p φ
            (hfloor (Order.succ β)) (hfloor β))) ≤
        roomInvariant p E β) :
    FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess Φ₀ (roomSubspace p E) b r) := by
  apply HeightRado.hasInjectiveRealization_affineAccess_of_rank_budget
    Φ₀ (reachableSubspace p F) (roomSubspace p E) b r hcompat
  intro β
  rw [hresidue β, roomSubspace_rank]
  exact hbudget β

end KernelRoom

namespace Survival

/-- The D-23 room--kernel budget at one height. -/
def KernelRoomBudgetAt {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
    (β : Ordinal.{0}) (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) : Prop :=
  roomInvariant p F β + jumpKernelInvariant p φ hsucc hβ ≤
    roomInvariant p E β

/-- The room--kernel budget is exactly the statement that the finite selector
kernel fits inside the target room. -/
theorem KernelRoomBudgetAt.iff_selectorKernelRank_le
    {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
    (β : Ordinal.{0}) (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    KernelRoomBudgetAt p φ β hsucc hβ ↔
      Module.rank (ZMod p)
          (LinearMap.ker (KernelRoom.selectorResidueMap p φ hsucc hβ)) ≤
        roomInvariant p E β := by
  unfold KernelRoomBudgetAt
  rw [KernelRoom.rank_selectorKernel_eq_room_add_jumpKernel]

/-- **The absorbed-tail branch of preservation.**  Once the new source stage
contains the whole tail `G_β`, both source demand terms vanish: the room is
zero and the source jump space is trivial.  The room--kernel budget at `β` is
therefore automatic, independently of the target.

This is equation (19) of the Height--Rado proof, isolated without any finiteness
or reducedness assumptions; those assumptions are needed only to show that the
tail can be absorbed by a finite response. -/
theorem KernelRoomBudgetAt.of_ulmSubgroup_le
    {F : AddSubgroup B} {E : AddSubgroup A} (φ : F →+ E)
    (β : Ordinal.{0}) (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β)
    (htail : ulmSubgroup p β (G := B) ≤ F) :
    KernelRoomBudgetAt p φ β hsucc hβ := by
  have hroom_le : pSocleAt p β (G := B) ≤ F := fun _ hx => htail hx.2
  have hroom : roomInvariant p F β = 0 :=
    rank_zero_iff.mpr ((room_subsingleton_iff p F β).mpr hroom_le)
  have hsource : Subsingleton (jumpSpace p F β) :=
    jumpSpace_subsingleton_of_ulmSubgroup_le p F β htail
  have hkernel : jumpKernelInvariant p φ hsucc hβ = 0 :=
    (jumpKernelInvariant_eq_zero_iff p φ hsucc hβ).mpr
      (jumpMap_injective_of_source_subsingleton p φ hsucc hβ hsource)
  unfold KernelRoomBudgetAt
  rw [hroom, hkernel, zero_add]
  exact zero_le _

/-- A stage carrying the quantitative room--kernel invariant rather than the
refuted old local survival package. -/
structure KernelRoomStage (α : Ordinal.{0}) where
  /-- The current source subgroup. -/
  src : AddSubgroup B
  /-- The current target subgroup. -/
  tgt : AddSubgroup A
  /-- The current partial isomorphism. -/
  iso : src ≃+ tgt
  /-- The whole-subgroup height floor. -/
  floor : IsHeightFloorOn p iso.toAddMonoidHom
  /-- The room--kernel budget throughout the active window. -/
  budget : ∀ β : Ordinal.{0}, InWindow α β →
    KernelRoomBudgetAt p iso.toAddMonoidHom β (floor (Order.succ β)) (floor β)

/-- The quantitative budget implies ordinary room domination. -/
theorem KernelRoomStage.room_dom {α : Ordinal.{0}}
    (S : KernelRoomStage p (A := A) (B := B) α)
    (β : Ordinal.{0}) (hβ : InWindow α β) :
    roomInvariant p S.src β ≤ roomInvariant p S.tgt β := by
  calc
    roomInvariant p S.src β = roomInvariant p S.src β + 0 := by simp
    _ ≤ roomInvariant p S.src β +
        jumpKernelInvariant p S.iso.toAddMonoidHom
          (S.floor (Order.succ β)) (S.floor β) :=
      add_le_add_right (zero_le _) _
    _ ≤ roomInvariant p S.tgt β := S.budget β hβ

/-- If target room is zero, the budget forces both source room and the jump
kernel to vanish. -/
theorem KernelRoomStage.zero_room_and_kernel {α : Ordinal.{0}}
    (S : KernelRoomStage p (A := A) (B := B) α)
    (β : Ordinal.{0}) (hβ : InWindow α β)
    (htgt : roomInvariant p S.tgt β = 0) :
    roomInvariant p S.src β = 0 ∧
      jumpKernelInvariant p S.iso.toAddMonoidHom
        (S.floor (Order.succ β)) (S.floor β) = 0 := by
  have hbudget : roomInvariant p S.src β +
      jumpKernelInvariant p S.iso.toAddMonoidHom
        (S.floor (Order.succ β)) (S.floor β) ≤ 0 := by
    rw [← htgt]
    exact S.budget β hβ
  constructor
  · apply le_antisymm _ (zero_le _)
    exact le_trans
      (by
        calc
          roomInvariant p S.src β = roomInvariant p S.src β + 0 := by simp
          _ ≤ roomInvariant p S.src β +
              jumpKernelInvariant p S.iso.toAddMonoidHom
                (S.floor (Order.succ β)) (S.floor β) :=
            add_le_add_right (zero_le _) _)
      hbudget
  · apply le_antisymm _ (zero_le _)
    exact le_trans
      (by
        calc
          jumpKernelInvariant p S.iso.toAddMonoidHom
              (S.floor (Order.succ β)) (S.floor β) =
              0 + jumpKernelInvariant p S.iso.toAddMonoidHom
                (S.floor (Order.succ β)) (S.floor β) := by simp
          _ ≤ roomInvariant p S.src β +
              jumpKernelInvariant p S.iso.toAddMonoidHom
                (S.floor (Order.succ β)) (S.floor β) :=
            add_le_add_left (zero_le _) _)
      hbudget

/-- Every room--kernel stage satisfies the old guarded endpoint conditions.

This is a compatibility map only: the converse is false by the padded D-5
witness, and no old one-line survival theorem is recovered. -/
noncomputable def KernelRoomStage.toStage {α : Ordinal.{0}}
    (S : KernelRoomStage p (A := A) (B := B) α) :
    Stage p (A := A) (B := B) α where
  src := S.src
  tgt := S.tgt
  iso := S.iso
  floor := S.floor
  room_dom := S.room_dom
  jump_inj := by
    intro β hβ htgt
    exact (jumpKernelInvariant_eq_zero_iff p S.iso.toAddMonoidHom
      (S.floor (Order.succ β)) (S.floor β)).mp
        (KernelRoomStage.zero_room_and_kernel p S β hβ htgt).2

end Survival
