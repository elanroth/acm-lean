import Lib.BackForth.Algebraic
import Lib.BackForth.OverhangTransfer
import Lib.BackForth.RoomTail
import Lib.PGroups.FiniteSocle

/-!
# The kernel-free part of the even-to-odd reduction

This file separates the local steps which a large parity biconditional can
easily conflate.  The even height clause makes the induced jump map injective
throughout the capped window, so its kernel term is zero.  The one-step room
sequence handles the bounded tail, while the finite-socle theorem handles the
long tail.  Consequently corrected even data restricts to odd data, in either
orientation, without an additional room or map-sensitive hypothesis.

This is a restriction theorem for the existing tuple.  It does not construct
or preserve odd data after adjoining a new challenge response.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

namespace AlgBFEvenCondData

/-- The even height clause is exactly filtration preservation below its cap. -/
theorem heightPresBelowCap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    IsHeightPresBelowOn p C.iso.equiv.toAddMonoidHom (ω * α + ω) := by
  intro γ hγ x
  rw [mem_ulmSubgroup_iff_le_ulmHeight, mem_ulmSubgroup_iff_le_ulmHeight]
  change ((γ : WithTop Ordinal.{0}) ≤ ulmHeight p (x : H)) ↔
    ((γ : WithTop Ordinal.{0}) ≤ ulmHeight p (C.iso.equiv x : G))
  rcases C.heights x with hlow | hhigh
  · rw [hlow.1]
  · have hγcap :
        (γ : WithTop Ordinal.{0}) ≤
          ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) :=
      WithTop.coe_le_coe.mpr (le_of_lt hγ)
    exact iff_of_true (hγcap.trans hhigh.1) (hγcap.trans hhigh.2)

/-- Every induced jump map named by even data has zero kernel below the cap. -/
theorem jumpKernelInvariant_eq_zero_belowCap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (β : Ordinal.{0}) (hβ : β < ω * α + ω) :
    jumpKernelInvariant p C.iso.equiv.toAddMonoidHom
        (fun x hx ↦ (C.heightPresBelowCap p hG hH
          (Order.succ β)
          ((Ordinal.isSuccLimit_add (ω * α) Ordinal.isSuccLimit_omega0).succ_lt hβ) x).mp hx)
        (fun x hx ↦ (C.heightPresBelowCap p hG hH β hβ x).mp hx) = 0 := by
  apply jumpKernelInvariant_eq_zero_of_equiv_of_heightPresBelow p C.iso.equiv
  exact (Ordinal.isSuccLimit_add (ω * α) Ordinal.isSuccLimit_omega0).succ_lt hβ
  exact C.heightPresBelowCap p hG hH

/-- The crossed inequalities in even data are equalities throughout the active
window.  Finite generation of the marked subgroups supplies the finite
correction needed for cardinal cancellation. -/
theorem window_eq
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (β : Ordinal.{0}) (hbase : ω * α ≤ β) (hcap : β < ω * α + ω) :
    ulmInvariant p β (G := G) = ulmInvariant p β (G := H) ∧
      markedGradedInvariant p (tupleSubgroup a) β =
        markedGradedInvariant p (tupleSubgroup b) β := by
  have hsymm : ∀ x : tupleSubgroup a,
      (ulmHeight p (C.iso.equiv.symm x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < ω * α + ω) ∨
      (ω * α + ω ≤ ulmHeight p (x : G) ∧
        ω * α + ω ≤ ulmHeight p (C.iso.equiv.symm x : H)) := by
    intro x
    let y : tupleSubgroup b := C.iso.equiv.symm x
    have hy : C.iso.equiv y = x := C.iso.equiv.apply_symm_apply x
    rcases C.heights y with hlow | hhigh
    · exact Or.inl ⟨by simpa [y, hy] using hlow.1,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [y] using hhigh.1⟩
  exact crossedInvariantInequalities_eq_of_finiteHeightEquiv p
    (tupleSubgroup a) (tupleSubgroup b) (tupleSubgroup_finite p hG.primary a)
    C.iso.equiv.symm (ω * α + ω) hsymm β hcap
    (C.window.absolute β hbase hcap) (C.window.marked β hbase hcap)

/-- Even data gives ordinary Ulm equality at every level strictly below its
cap.  Below the base this is a field of the package; in the active window it
is the equality extracted from the crossed absolute/marked comparisons.

The orientation is source `H` to target `G`, matching the finite extension
arguments used in the even response. -/
theorem ulm_eq_belowCap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (β : Ordinal.{0}) (hβ : β < ω * α + ω) :
    ulmInvariant p β (G := H) = ulmInvariant p β (G := G) := by
  by_cases hbase : β < ω * α
  · exact C.ulm_below β hbase
  · exact (C.window_eq p hG hH β (le_of_not_gt hbase) hβ).1.symm

/-- Corrected even data is symmetric for finite tuple marks.  The source-facing
fields are crossed, but `window_eq` upgrades both of them to equalities before
the two ambient groups are exchanged. -/
noncomputable def symm
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    AlgBFEvenCondData p hH hG α b a := by
  let hsymm : ∀ x : tupleSubgroup a,
      (ulmHeight p (x : G) = ulmHeight p (C.iso.equiv.symm x : H) ∧
        ulmHeight p (x : G) < ω * α + ω) ∨
      (ω * α + ω ≤ ulmHeight p (x : G) ∧
        ω * α + ω ≤ ulmHeight p (C.iso.equiv.symm x : H)) := by
    intro x
    let y : tupleSubgroup b := C.iso.equiv.symm x
    have hy : C.iso.equiv y = x := C.iso.equiv.apply_symm_apply x
    rcases C.heights y with hlow | hhigh
    · exact Or.inl ⟨by simpa [y, hy] using hlow.1.symm,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [y] using hhigh.1⟩
  refine {
    iso := C.iso.symm
    lengths := ?_
    ulm_below := ?_
    window := ?_
    heights := hsymm }
  · rcases C.lengths with hshort | hlong
    · exact Or.inl ⟨hshort.1.symm, by simpa [← hshort.1] using hshort.2⟩
    · exact Or.inr ⟨hlong.2, hlong.1⟩
  · intro β hβ
    exact (C.ulm_below β hβ).symm
  · apply EvenWindowCrossed.of_eq
    · intro β hbase hcap
      exact (C.window_eq p hG hH β hbase hcap).1
    · intro β hbase hcap
      exact (C.window_eq p hG hH β hbase hcap).2.symm

/-- Every point of the finite tail below `ω * α + ω` has that omega boundary
as its next omega limit. -/
theorem add_omega_eq_of_mem_window
    {α β : Ordinal.{0}} (hbase : ω * α ≤ β)
    (hcap : β < ω * α + ω) :
    β + ω = ω * α + ω := by
  have hdiff : β - ω * α < ω := by
    rw [← Ordinal.add_sub_cancel_of_le hbase, add_lt_add_iff_left] at hcap
    exact hcap
  calc
    β + ω = (ω * α + (β - ω * α)) + ω := by
      rw [Ordinal.add_sub_cancel_of_le hbase]
    _ = ω * α + ((β - ω * α) + ω) := by rw [add_assoc]
    _ = ω * α + ω := by rw [Ordinal.add_omega0 hdiff]

/-- In the short branch of the even length clause, the common Ulm length is a
finite distance above every active-window level.  The room exact sequence
therefore telescopes from a common zero endpoint, and pointwise marked-graded
equality gives room equality. -/
theorem roomInvariant_eq_of_shortLengths
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hshort :
      (ulmLength p (G := G) hG : Ordinal.{0}) =
          (ulmLength p (G := H) hH : Ordinal.{0}) ∧
        (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (β : Ordinal.{0}) (hbase : ω * α ≤ β) (hcap : β < ω * α + ω) :
    roomInvariant p (tupleSubgroup b) β =
      roomInvariant p (tupleSubgroup a) β := by
  have hβomega := add_omega_eq_of_mem_window hbase hcap
  have hlengthTail :
      (ulmLength p (G := G) hG : Ordinal.{0}) < β + ω := by
    simpa [hβomega] using hshort.2
  rw [← Ordinal.iSup_add_natCast β] at hlengthTail
  obtain ⟨N, hN⟩ := Ordinal.lt_iSup_iff.mp hlengthTail
  have hNcap : β + N < ω * α + ω := by
    rw [← hβomega, add_lt_add_iff_left]
    exact Ordinal.natCast_lt_omega0 N
  have hGbot : ulmSubgroup p (β + N) (G := G) = ⊥ := by
    apply le_bot_iff.mp
    calc
      ulmSubgroup p (β + N) (G := G) ≤
          ulmSubgroup p (ulmLength p (G := G) hG) (G := G) :=
        ulmSubgroup_antitone p (le_of_lt hN)
      _ = ⊥ := ulmLength.at_ulmLength (p := p) (hred := hG)
  have hNH :
      (ulmLength p (G := H) hH : Ordinal.{0}) < β + N := by
    simpa [← hshort.1] using hN
  have hHbot : ulmSubgroup p (β + N) (G := H) = ⊥ := by
    apply le_bot_iff.mp
    calc
      ulmSubgroup p (β + N) (G := H) ≤
          ulmSubgroup p (ulmLength p (G := H) hH) (G := H) :=
        ulmSubgroup_antitone p (le_of_lt hNH)
      _ = ⊥ := ulmLength.at_ulmLength (p := p) (hred := hH)
  have htargetSource := roomInvariant_eq_of_markedGraded_eq_to_add_nat p
    (tupleSubgroup a) (tupleSubgroup b) β N (by
      intro k hk
      have hkN : β + k < β + N := by
        rw [add_lt_add_iff_left]
        exact_mod_cast hk
      exact (C.window_eq p hG hH (β + k)
        (hbase.trans le_self_add) (hkN.trans hNcap)).2) (by
      rw [roomInvariant_eq_zero_of_ulmSubgroup_eq_bot p
          (tupleSubgroup a) (β + N) hGbot,
        roomInvariant_eq_zero_of_ulmSubgroup_eq_bot p
          (tupleSubgroup b) (β + N) hHbot])
  exact htargetSource.symm

/-- In the long branch, infinite filtered socles on both sides leave
countably infinite room after removing the finite tuple marks. -/
theorem roomInvariant_eq_of_infiniteSocles
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (β : Ordinal.{0})
    (hGinf : Set.Infinite (pSocleAt p β (G := G) : Set G))
    (hHinf : Set.Infinite (pSocleAt p β (G := H) : Set H)) :
    roomInvariant p (tupleSubgroup b) β =
      roomInvariant p (tupleSubgroup a) β := by
  rw [roomInvariant_eq_aleph0_of_infinite p (tupleSubgroup b)
      (tupleSubgroup_finite p hH.primary b) β hHinf,
    roomInvariant_eq_aleph0_of_infinite p (tupleSubgroup a)
      (tupleSubgroup_finite p hG.primary a) β hGinf]

/-- Reaching the right edge of an even window forces every filtered socle in
that finite tail to be infinite. -/
theorem infinite_pSocleAt_of_longWindow
    (hG : IsReducedPGroup p G)
    {α β : Ordinal.{0}}
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (hbase : ω * α ≤ β) (hcap : β < ω * α + ω) :
    Set.Infinite (pSocleAt p β (G := G) : Set G) := by
  apply infinite_pSocleAt_of_add_omega_le_ulmLength p hG β
  rw [add_omega_eq_of_mem_window hbase hcap]
  exact hlong

/-- The crossed even-window package itself implies the ordinary room
domination required by odd data.  The short branch telescopes to a common zero
endpoint; the long branch uses the finite-socle theorem. -/
theorem roomDomination
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup b) β ≤
        roomInvariant p (tupleSubgroup a) β := by
  intro β hbase hcap
  rcases C.lengths with hshort | hlong
  · exact (C.roomInvariant_eq_of_shortLengths p hG hH
      hshort β hbase hcap).le
  · exact (roomInvariant_eq_of_infiniteSocles p hG hH β
      (infinite_pSocleAt_of_longWindow p hG hlong.1 hbase hcap)
      (infinite_pSocleAt_of_longWindow p hH hlong.2 hbase hcap)).le

/-- The established crossed package implies the exact Hill/room candidate.
The Hill equality uses the mark-only overhang transport; room equality uses
the same short/long split as the even-to-odd restriction. -/
noncomputable def toExactData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    AlgBFEvenExactCondData p hG hH α a b := by
  have hhill : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      hillInvariant p (tupleSubgroup b) β =
        hillInvariant p (tupleSubgroup a) β := by
    intro β _hbase hcap
    have hβ₁ : Order.succ β < ω * α + ω :=
      (Ordinal.isSuccLimit_add (ω * α) Ordinal.isSuccLimit_omega0).succ_lt hcap
    have hβ₂ : Order.succ (Order.succ β) < ω * α + ω :=
      (Ordinal.isSuccLimit_add (ω * α) Ordinal.isSuccLimit_omega0).succ_lt hβ₁
    exact hillInvariant_eq_of_markedGraded_eq_of_heightPresBelow p
      (tupleSubgroup b) (tupleSubgroup a)
      (tupleSubgroup_finite p hH.primary b) C.iso.equiv (ω * α + ω)
      (C.heightPresBelowCap p hG hH) β hcap hβ₂
      (C.window_eq p hG hH β _hbase hcap).2.symm
  have hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β =
        roomInvariant p (tupleSubgroup b) β := by
    intro β hbase hcap
    rcases C.lengths with hshort | hlong
    · exact (C.roomInvariant_eq_of_shortLengths p hG hH
        hshort β hbase hcap).symm
    · exact (roomInvariant_eq_of_infiniteSocles p hG hH β
        (infinite_pSocleAt_of_longWindow p hG hlong.1 hbase hcap)
        (infinite_pSocleAt_of_longWindow p hH hlong.2 hbase hcap)).symm
  exact C.toExactData_of_windowEq p hG hH hhill hroom

/-- The complete room comparison from even data, conditional only on the
classical Kaplansky consequence used in the long-length branch.

The two hypotheses are deliberately stated as implications from the actual
length lower bound.  They are discharged by the classical theorem that a
reduced primary group with finite socle is finite: otherwise a finite
`P_β` below an omega boundary would make the tail die after finitely many
successors. -/
theorem roomDomination_of_kaplanskyLongSocles
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hGkap : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) →
      ∀ β : Ordinal.{0}, β < ω * α + ω →
        Set.Infinite (pSocleAt p β (G := G) : Set G))
    (hHkap : ω * α + ω ≤ (ulmLength p (G := H) hH : Ordinal.{0}) →
      ∀ β : Ordinal.{0}, β < ω * α + ω →
        Set.Infinite (pSocleAt p β (G := H) : Set H)) :
    ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup b) β ≤
        roomInvariant p (tupleSubgroup a) β := by
  intro β hbase hcap
  rcases C.lengths with hshort | hlong
  · exact (C.roomInvariant_eq_of_shortLengths p hG hH hshort β hbase hcap).le
  · exact (roomInvariant_eq_of_infiniteSocles p hG hH β
      (hGkap hlong.1 β hcap) (hHkap hlong.2 β hcap)).le

/-- Even data becomes odd data at the same index once room domination is
available on the active window.

This theorem proves that the map-sensitive term in the odd room--kernel budget
is already zero.  The more specialized `toOddData` below discharges its
remaining map-free room hypothesis from even data. -/
noncomputable def toOddData_of_roomDom
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup b) β ≤ roomInvariant p (tupleSubgroup a) β) :
    AlgBFOddCondData p hG hH α a b := by
  let hoddHeights : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (C.iso.equiv x : G) ∧
        ulmHeight p (x : H) < ω * α) ∨
      (ω * α ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H))
          (((ω * α + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
            ulmHeight p (C.iso.equiv x : G)) := by
    intro x
    rcases C.heights x with hlow | hhigh
    · rcases lt_or_ge (ulmHeight p (x : H))
        (((ω * α : Ordinal.{0})) : WithTop Ordinal.{0}) with hxlt | hxge
      · exact Or.inl ⟨hlow.1, hxlt⟩
      · exact Or.inr ⟨hxge, by
          rw [min_eq_left (le_of_lt hlow.2), ← hlow.1]⟩
    · have hbaseCap :
          ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) :=
        WithTop.coe_le_coe.mpr le_self_add
      exact Or.inr ⟨hbaseCap.trans hhigh.1,
        (min_le_right _ _).trans hhigh.2⟩
  refine {
    iso := C.iso
    lengths := ?_
    ulm_below := C.ulm_below
    heights := hoddHeights
    kernel_room := ?_ }
  · rcases C.lengths with hshort | hlong
    · rcases lt_or_ge (ulmLength p (G := G) hG : Ordinal.{0}) (ω * α) with hlt | hge
      · exact Or.inl ⟨hshort.1, hlt⟩
      · exact Or.inr ⟨by rw [← hshort.1]; exact hge, by
          rw [← hshort.1]
          exact min_le_left _ _⟩
    · exact Or.inr ⟨le_self_add.trans hlong.2,
        (min_le_right _ _).trans hlong.1⟩
  · intro β hbase hcap
    have hinj : Function.Injective
        (jumpMap p C.iso.equiv.toAddMonoidHom
          (heightFloorAt_of_heights p C.iso hoddHeights (Order.succ β)
            (Order.succ_le_of_lt hcap))
          (heightFloorAt_of_heights p C.iso hoddHeights β (le_of_lt hcap))) := by
      apply jumpMap_injective_of_equiv_of_reflectsAt p C.iso.equiv
      intro x hx
      exact (C.heightPresBelowCap p hG hH β hcap x).mpr hx
    have hker : jumpKernelInvariant p C.iso.equiv.toAddMonoidHom
          (heightFloorAt_of_heights p C.iso hoddHeights (Order.succ β)
            (Order.succ_le_of_lt hcap))
          (heightFloorAt_of_heights p C.iso hoddHeights β (le_of_lt hcap)) = 0 :=
      (jumpKernelInvariant_eq_zero_iff p C.iso.equiv.toAddMonoidHom _ _).2 hinj
    rw [hker, add_zero]
    exact hroom β hbase hcap

/-- Even data restricts to odd data once Kaplansky's long-socle theorem is
supplied.  All tail summation, countability, finite-mark removal, and induced
jump-kernel work is internal to the preceding lemmas. -/
noncomputable def toOddData_of_kaplanskyLongSocles
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hGkap : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) →
      ∀ β : Ordinal.{0}, β < ω * α + ω →
        Set.Infinite (pSocleAt p β (G := G) : Set G))
    (hHkap : ω * α + ω ≤ (ulmLength p (G := H) hH : Ordinal.{0}) →
      ∀ β : Ordinal.{0}, β < ω * α + ω →
        Set.Infinite (pSocleAt p β (G := H) : Set H)) :
    AlgBFOddCondData p hG hH α a b :=
  C.toOddData_of_roomDom p hG hH
    (C.roomDomination_of_kaplanskyLongSocles p hG hH hGkap hHkap)

/-- **Unconditional even-to-odd conversion.**  Countability, finite tuple
marks, the one-step room exact sequence, and the finite-socle theorem discharge
all room and jump-kernel obligations internally. -/
noncomputable def toOddData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    AlgBFOddCondData p hG hH α a b :=
  C.toOddData_of_roomDom p hG hH (C.roomDomination p hG hH)

/-- Existing even data also restricts to odd data in the reversed orientation. -/
noncomputable def toOddDataSymm
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    AlgBFOddCondData p hH hG α b a :=
  (C.symm p hG hH).toOddData p hH hG

end AlgBFEvenCondData
