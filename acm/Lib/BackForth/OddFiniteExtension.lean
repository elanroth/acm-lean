import Lib.BackForth.Algebraic
import Lib.BackForth.LocalFiniteEmbedding
import Lib.BackForth.OddLongCountdown

/-!
# Plugging the corrected odd condition into finite challenges

The odd algebraic condition supplies `K_β` only in its active window and a
height floor only through the cap.  This file first records the explicit band
seams, then closes bounded Case 1(c) by reordering the finite challenge: exact
high-tail reaches consume only the active-window budget, and a separate low
Kaplansky climb uses absolute Ulm equality below the cutoff.
-/

noncomputable section

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

namespace AlgebraicBFConditions

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

/-- Clause (d) of the corrected odd condition is definitionally the survival
layer's room--kernel budget at every height in the active window. -/
theorem AlgBFOddCondData.kernelRoomBudgetAt
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (β : Ordinal.{0}) (hβ : Survival.InWindow α β) :
    Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β
      (heightFloorAt_of_heights p C.iso C.heights (Order.succ β)
        (Order.succ_le_of_lt hβ.2))
      (heightFloorAt_of_heights p C.iso C.heights β
        (le_of_lt hβ.2)) := by
  exact C.kernel_room β hβ.1 hβ.2

/-! ### The bounded-tail band assembly -/

/-- In the bounded-target branch of the odd length clause, the source length is
bounded by the same cap.  This is the length-theoretic reason that no genuine
upper band remains in ACM Case 1(c). -/
theorem AlgBFOddCondData.sourceLength_lt_cap_of_targetLength_lt_cap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) :
    (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω := by
  rcases C.lengths with hshort | hlong
  · calc
      (ulmLength p (G := H) hH : Ordinal.{0}) =
          (ulmLength p (G := G) hG : Ordinal.{0}) := hshort.1.symm
      _ < ω * α := hshort.2
      _ ≤ ω * α + ω := le_self_add
  · by_contra hHcap
    have hcapH : ω * α + ω ≤
        (ulmLength p (G := H) hH : Ordinal.{0}) := le_of_not_gt hHcap
    have hcapG : ω * α + ω ≤
        (ulmLength p (G := G) hG : Ordinal.{0}) := by
      simpa [min_eq_right hcapH] using hlong.2
    exact (not_le_of_gt hGcap) hcapG

/-- A bounded target length makes the source filtration vanish at the odd cap.
The proof uses only the recorded odd length clause and the definition of Ulm
length; no height or room hypothesis is added. -/
theorem AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) :
    ulmSubgroup p (ω * α + ω) (G := H) = ⊥ := by
  apply le_bot_iff.mp
  calc
    ulmSubgroup p (ω * α + ω) (G := H) ≤
        ulmSubgroup p (ulmLength p (G := H) hH) (G := H) :=
      ulmSubgroup_antitone p (le_of_lt
        (AlgBFOddCondData.sourceLength_lt_cap_of_targetLength_lt_cap
          p hG hH C hGcap))
    _ = ⊥ := ulmLength.at_ulmLength (p := p) (hred := hH)

/-- Once the source has no tail at the cap, clause (e)'s capped floor is a
genuine all-height floor.  Above the cap every source element in the relevant
filtration subgroup is zero. -/
theorem AlgBFOddCondData.heightFloorOn_of_sourceTail_eq_bot
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (htail : ulmSubgroup p (ω * α + ω) (G := H) = ⊥) :
    IsHeightFloorOn p C.iso.equiv.toAddMonoidHom := by
  intro γ
  by_cases hγ : γ ≤ ω * α + ω
  · exact heightFloorAt_of_heights p C.iso C.heights γ hγ
  · intro x hx
    have hcapγ : ω * α + ω ≤ γ := le_of_not_ge hγ
    have hxcap : (x : H) ∈ ulmSubgroup p (ω * α + ω) (G := H) :=
      ulmSubgroup_antitone p hcapγ hx
    rw [htail] at hxcap
    have hxzero : x = 0 := Subtype.ext (by simpa using hxcap)
    subst x
    simp

/-- In the bounded-target branch, the odd clauses themselves provide the full
marked height floor. -/
theorem AlgBFOddCondData.heightFloorOn_of_targetLength_lt_cap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) :
    IsHeightFloorOn p C.iso.equiv.toAddMonoidHom :=
  AlgBFOddCondData.heightFloorOn_of_sourceTail_eq_bot p hG hH C
    (AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
      p hG hH C hGcap)

/-- The exact low-height half of clause (e), expressed at the filtration level
used by extension arguments. -/
theorem AlgBFOddCondData.heightPresBelowOn
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b) :
    IsHeightPresBelowOn p C.iso.equiv.toAddMonoidHom (ω * α) :=
  heightPresBelowOn_of_heights p C.iso C.heights

/-- **Bounded-tail finite-challenge integration.**

Assume the target length is below the odd cap.  The odd length clause then
kills the source tail at the cap, so clause (e) becomes a global floor and every
upper-band budget is automatic.  Clause (d) supplies the window.  Consequently
only the below-base budgets remain as an explicit input to the already-proved
finite-challenge theorem.

This theorem is retained as the direct all-height-budget decomposition.  The
stronger high-tail-first construction below removes its below-base input and
also supplies exact cutoff behavior. -/
theorem exists_finiteChallenge_embedding_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H))
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor) :
    ∃ f : D →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), hFD x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  have htail : ulmSubgroup p (ω * α + ω) (G := H) = ⊥ :=
    AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
      p hG hH C hGcap
  have hfloor : IsHeightFloorOn p C.iso.equiv.toAddMonoidHom :=
    AlgBFOddCondData.heightFloorOn_of_sourceTail_eq_bot p hG hH C htail
  apply LocalFiniteEmbedding.exists_finiteChallenge_embedding_of_kernelRoomBudget
    p hH (tupleSubgroup b) D hFD hD (tupleSubgroup a)
    C.iso.equiv.toAddMonoidHom C.iso.equiv.injective hfloor
  intro β
  by_cases hlow : β < ω * α
  · exact hbelow β hlow (hfloor (Order.succ β)) (hfloor β)
  · have hbase : ω * α ≤ β := le_of_not_gt hlow
    by_cases hwindow : β < ω * α + ω
    · simpa using AlgBFOddCondData.kernelRoomBudgetAt
        p hG hH C β ⟨hbase, hwindow⟩
    · have hcap : ω * α + ω ≤ β := le_of_not_gt hwindow
      apply Survival.KernelRoomBudgetAt.of_ulmSubgroup_le p
      exact le_trans (ulmSubgroup_antitone p hcap) (by simp [htail])

/-- **High-tail-first ACM integration.**

Before the low Kaplansky climb, enlarge the marked subgroup only by challenge
elements already in the source tail `H_(ω·α)`.  The bounded-tail finite
embedding theorem makes their images stay in the target tail.  Since it fixes
the original odd map, adding those high elements cannot disturb any exact
height below the base.  Thus the resulting map has precisely the cutoff
height behavior required by the predecessor relation: filtration equivalence
below the base and a global height floor.

The `hbelow` input is kept explicit in this decomposition theorem.  The
exact-reach variant immediately below removes it. -/
theorem exists_highChallenge_embedding_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H))
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor) :
    let Dhi : AddSubgroup H :=
      tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
    ∃ f : Dhi →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      IsHeightPresBelowOn p f (ω * α) ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  dsimp only
  let Dhi : AddSubgroup H :=
    tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
  have hDhiD : Dhi ≤ D := sup_le hFD inf_le_left
  have hDhi : Set.Finite (Dhi : Set H) := hD.subset hDhiD
  obtain ⟨f, hfinj, hffloor, hfmark⟩ :=
    exists_finiteChallenge_embedding_of_oddData_of_boundedTarget
      p hG hH C hGcap Dhi le_sup_left hDhi hbelow
  refine ⟨f, hfinj, hffloor, ?_, hfmark⟩
  intro γ hγ z
  constructor
  · exact hffloor γ z
  · intro hfz
    obtain ⟨e, heF, x, hxTail, hex⟩ := AddSubgroup.mem_sup.mp z.property
    let eF : tupleSubgroup b := ⟨e, heF⟩
    let eDhi : Dhi := ⟨e, AddSubgroup.mem_sup_left heF⟩
    let xDhi : Dhi := ⟨x, AddSubgroup.mem_sup_right hxTail⟩
    have hγbase : γ ≤ ω * α := le_of_lt hγ
    have hxγ : x ∈ ulmSubgroup p γ (G := H) :=
      ulmSubgroup_antitone p hγbase hxTail.2
    have hfxbase : (f xDhi : G) ∈
        ulmSubgroup p (ω * α) (G := G) :=
      hffloor (ω * α) xDhi hxTail.2
    have hfxγ : (f xDhi : G) ∈ ulmSubgroup p γ (G := G) :=
      ulmSubgroup_antitone p hγbase hfxbase
    have hze : z - xDhi = eDhi := by
      apply Subtype.ext
      change (z : H) - x = e
      rw [show (z : H) = e + x by exact hex.symm]
      simp
    have hfeγ : (f eDhi : G) ∈ ulmSubgroup p γ (G := G) := by
      rw [← hze, map_sub]
      exact (ulmSubgroup p γ).sub_mem hfz hfxγ
    have hφeγ : (C.iso.equiv eF : G) ∈
        ulmSubgroup p γ (G := G) := by
      have hfe : (f eDhi : G) = (C.iso.equiv eF : G) := by
        simpa [eF, eDhi, Dhi] using hfmark eF
      rw [← hfe]
      exact hfeγ
    have heγ : e ∈ ulmSubgroup p γ (G := H) :=
      (AlgBFOddCondData.heightPresBelowOn p hG hH C γ hγ eF).mpr hφeγ
    rw [show (z : H) = e + x by exact hex.symm]
    exact (ulmSubgroup p γ).add_mem heγ hxγ

/-- The high-tail phase needs `K_β` only at the exact reaches of the new
finite challenge directions.  Every such reach is at least the base because
the new directions have representatives in `H_(ω·α)`.  Hence clause (d)
handles reaches in the active window and the bounded tail handles all later
reaches; no below-base budget is needed. -/
theorem exists_highChallenge_embedding_of_oddData_of_boundedTarget_from_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H)) :
    let Dhi : AddSubgroup H :=
      tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
    ∃ f : Dhi →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      IsHeightPresBelowOn p f (ω * α) ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  dsimp only
  let Dhi : AddSubgroup H :=
    tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
  have hDhiD : Dhi ≤ D := sup_le hFD inf_le_left
  have hDhi : Set.Finite (Dhi : Set H) := hD.subset hDhiD
  have htail : ulmSubgroup p (ω * α + ω) (G := H) = ⊥ :=
    AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
      p hG hH C hGcap
  have hfloor : IsHeightFloorOn p C.iso.equiv.toAddMonoidHom :=
    AlgBFOddCondData.heightFloorOn_of_sourceTail_eq_bot p hG hH C htail
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) := by
    exact Ordinal.isSuccLimit_omega0
  have hbaseLimit : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  obtain ⟨f, hfinj, hffloor, hfmark⟩ :=
    LocalFiniteEmbedding.exists_finiteChallenge_embedding_of_reachableKernelRoomBudget
      p hH (tupleSubgroup b) Dhi le_sup_left hDhi (tupleSubgroup a)
      C.iso.equiv.toAddMonoidHom C.iso.equiv.injective hfloor (by
        intro β hexact
        obtain ⟨q, _hq0, hqβ, hqSucc⟩ := hexact
        have hqbase : q ∈
            FiniteChallenge.challengeReach p (tupleSubgroup b) Dhi (ω * α) := by
          obtain ⟨x, rfl⟩ :=
            FiniteChallenge.challengeQuotientMap_surjective
              p (tupleSubgroup b) Dhi q
          rw [FiniteChallenge.mem_challengeReach_iff]
          obtain ⟨e, he, y, hy, hey⟩ := AddSubgroup.mem_sup.mp x.property
          let eF : tupleSubgroup b := ⟨e, he⟩
          refine ⟨eF, ?_⟩
          have hdiff : (x : H) - (eF : H) = y := by
            change (x : H) - e = y
            rw [show (x : H) = e + y by exact hey.symm]
            simp
          rw [hdiff]
          exact hy.2
        have hbase : ω * α ≤ β := by
          by_contra hnot
          have hsuccBase : Order.succ β ≤ ω * α :=
            le_of_lt (hbaseLimit.succ_lt (lt_of_not_ge hnot))
          exact hqSucc
            (FiniteChallenge.challengeReach_antitone
              p (tupleSubgroup b) Dhi hsuccBase hqbase)
        by_cases hwindow : β < ω * α + ω
        · simpa using AlgBFOddCondData.kernelRoomBudgetAt
            p hG hH C β ⟨hbase, hwindow⟩
        · have hcap : ω * α + ω ≤ β := le_of_not_gt hwindow
          apply Survival.KernelRoomBudgetAt.of_ulmSubgroup_le p
          exact le_trans (ulmSubgroup_antitone p hcap) (by simp [htail]))
  refine ⟨f, hfinj, hffloor, ?_, hfmark⟩
  intro γ hγ z
  constructor
  · exact hffloor γ z
  · intro hfz
    obtain ⟨e, heF, x, hxTail, hex⟩ := AddSubgroup.mem_sup.mp z.property
    let eF : tupleSubgroup b := ⟨e, heF⟩
    let eDhi : Dhi := ⟨e, AddSubgroup.mem_sup_left heF⟩
    let xDhi : Dhi := ⟨x, AddSubgroup.mem_sup_right hxTail⟩
    have hγbase : γ ≤ ω * α := le_of_lt hγ
    have hxγ : x ∈ ulmSubgroup p γ (G := H) :=
      ulmSubgroup_antitone p hγbase hxTail.2
    have hfxbase : (f xDhi : G) ∈
        ulmSubgroup p (ω * α) (G := G) :=
      hffloor (ω * α) xDhi hxTail.2
    have hfxγ : (f xDhi : G) ∈ ulmSubgroup p γ (G := G) :=
      ulmSubgroup_antitone p hγbase hfxbase
    have hze : z - xDhi = eDhi := by
      apply Subtype.ext
      change (z : H) - x = e
      rw [show (z : H) = e + x by exact hex.symm]
      simp
    have hfeγ : (f eDhi : G) ∈ ulmSubgroup p γ (G := G) := by
      rw [← hze, map_sub]
      exact (ulmSubgroup p γ).sub_mem hfz hfxγ
    have hφeγ : (C.iso.equiv eF : G) ∈
        ulmSubgroup p γ (G := G) := by
      have hfe : (f eDhi : G) = (C.iso.equiv eF : G) := by
        simpa [eF, eDhi, Dhi] using hfmark eF
      rw [← hfe]
      exact hfeγ
    have heγ : e ∈ ulmSubgroup p γ (G := H) :=
      (AlgBFOddCondData.heightPresBelowOn p hG hH C γ hγ eF).mpr hφeγ
    rw [show (z : H) = e + x by exact hex.symm]
    exact (ulmSubgroup p γ).add_mem heγ hxγ

/-- **Bounded Case 1(c), assembled through the two-phase finite climb.**

First absorb the part of the finite challenge already in `H_(ω·α)` using
the room--kernel construction.  Then the cutoff Kaplansky climb absorbs every
remaining element.  Tail containment forces every genuinely new normalized
representative into an exact height below `ω·α`, where clause (c) supplies
the one Ulm-invariant equality used by target selection.

The result is the actual cutoff height conclusion, not merely a one-sided
floor.  This budget-parameterized version is followed by the odd-only theorem
that restricts the high phase to exact reaches and removes `hbelow`. -/
theorem exists_finiteChallenge_cutoffEmbedding_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H))
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor) :
    ∃ f : D →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      IsHeightPresBelowOn p f (ω * α) ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), hFD x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  let Dhi : AddSubgroup H :=
    tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
  obtain ⟨fhi, hfhiinj, hfhifloor, hfhipres, hfhimark⟩ :=
    exists_highChallenge_embedding_of_oddData_of_boundedTarget
      p hG hH C hGcap D hFD hD hbelow
  have hDhiD : Dhi ≤ D := sup_le hFD inf_le_left
  have hDhifinite : Set.Finite (Dhi : Set H) := hD.subset hDhiD
  let s : LocalFiniteEmbedding.LocalCutoffClimbStage
      p (A := G) D (ω * α) :=
    { source := Dhi
      source_le := hDhiD
      source_finite := hDhifinite
      map := fhi
      map_injective := hfhiinj
      floor := hfhifloor
      presBelow := hfhipres
      tail_le := fun x hx ↦ AddSubgroup.mem_sup_right hx }
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) := by
    exact Ordinal.isSuccLimit_omega0
  have hbase : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  obtain ⟨f, hfinj, hffloor, hfpres, hfhi⟩ :=
    LocalFiniteEmbedding.finite_cutoff_climb_within
      p hH hD hbase C.ulm_below s
  refine ⟨f, hfinj, hffloor, hfpres, ?_⟩
  intro x
  let xhi : Dhi := ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩
  calc
    (f ⟨(x : H), hFD x.property⟩ : G) = (fhi xhi : G) := hfhi xhi
    _ = (C.iso.equiv x : G) := by simpa [xhi, Dhi] using hfhimark x

/-- **Bounded Case 1(c) from the odd clauses alone.**

This removes the provisional below-base budget from the preceding theorem.
Only exact reaches of the reordered high challenge are charged, and those
reaches lie in the odd window or above the bounded cap.  The low phase uses
clause (c) height by height. -/
theorem exists_finiteChallenge_cutoffEmbedding_of_oddData_of_boundedTarget_from_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H)) :
    ∃ f : D →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      IsHeightPresBelowOn p f (ω * α) ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), hFD x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  let Dhi : AddSubgroup H :=
    tupleSubgroup b ⊔ (D ⊓ ulmSubgroup p (ω * α) (G := H))
  obtain ⟨fhi, hfhiinj, hfhifloor, hfhipres, hfhimark⟩ :=
    exists_highChallenge_embedding_of_oddData_of_boundedTarget_from_odd
      p hG hH C hGcap D hFD hD
  have hDhiD : Dhi ≤ D := sup_le hFD inf_le_left
  have hDhifinite : Set.Finite (Dhi : Set H) := hD.subset hDhiD
  let s : LocalFiniteEmbedding.LocalCutoffClimbStage
      p (A := G) D (ω * α) :=
    { source := Dhi
      source_le := hDhiD
      source_finite := hDhifinite
      map := fhi
      map_injective := hfhiinj
      floor := hfhifloor
      presBelow := hfhipres
      tail_le := fun x hx ↦ AddSubgroup.mem_sup_right hx }
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) := by
    exact Ordinal.isSuccLimit_omega0
  have hbase : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  obtain ⟨f, hfinj, hffloor, hfpres, hfhi⟩ :=
    LocalFiniteEmbedding.finite_cutoff_climb_within
      p hH hD hbase C.ulm_below s
  refine ⟨f, hfinj, hffloor, hfpres, ?_⟩
  intro x
  let xhi : Dhi := ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩
  calc
    (f ⟨(x : H), hFD x.property⟩ : G) = (fhi xhi : G) := hfhi xhi
    _ = (C.iso.equiv x : G) := by simpa [xhi, Dhi] using hfhimark x

/-- **The exact finite-challenge seam for the odd characterization.**

The corrected odd clause supplies the active-window part of the budget.
Supplying a full ambient floor and the complementary lower/upper-band budgets
then invokes the local finite embedding theorem verbatim.  These two explicit
inputs are precisely what the still-open band assembly must construct; they
are not consequences claimed here from the odd data alone.
-/
theorem exists_finiteChallenge_embedding_of_oddData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (D : AddSubgroup H) (hFD : tupleSubgroup b ≤ D)
    (hD : Set.Finite (D : Set H))
    (hfloor : IsHeightFloorOn p C.iso.equiv.toAddMonoidHom)
    (hoffWindow : ∀ β : Ordinal.{0}, ¬ Survival.InWindow α β →
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ f : D →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), hFD x.property⟩ : G) =
          (C.iso.equiv x : G) := by
  apply LocalFiniteEmbedding.exists_finiteChallenge_embedding_of_kernelRoomBudget
    p hH (tupleSubgroup b) D hFD hD (tupleSubgroup a)
    C.iso.equiv.toAddMonoidHom C.iso.equiv.injective hfloor
  intro β
  by_cases hβ : Survival.InWindow α β
  · simpa using AlgBFOddCondData.kernelRoomBudgetAt
      p hG hH C β hβ
  · exact hoffWindow β hβ

/-! ### From subgroup embeddings to ACM finite-tuple responses -/

/-- **Finite-tuple wrapper for the proved challenge theorem.**

Let `d` be an arbitrary finite source challenge.  Its tuple-generated subgroup
is finite because the ambient source is primary.  Under the explicit global
floor and off-window budgets of `exists_finiteChallenge_embedding_of_oddData`,
the resulting subgroup embedding sends `d` to a target tuple `c` and
corestricts to an isomorphism of the enlarged tuple-generated subgroups.

This is the finite-challenge object consumed by the arbitrary finite-tuple
quantifier in `BFRel_succ`.  A height floor on the enlarged tuple map is still
weaker than the exact-below-base height condition required at the next
even/limit relation. -/
theorem exists_finiteTuple_heightFloorResponse_of_oddData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    {m : ℕ} (d : Fin m → H)
    (hfloor : IsHeightFloorOn p C.iso.equiv.toAddMonoidHom)
    (hoffWindow : ∀ β : Ordinal.{0}, ¬ Survival.InWindow α β →
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom := by
  let D : AddSubgroup H := tupleSubgroup (Fin.append b d)
  have hFD : tupleSubgroup b ≤ D := by
    apply AddSubgroup.closure_mono
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by simp⟩
  have hD : Set.Finite (D : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  obtain ⟨f, hfinj, hffloor, hfmark⟩ :=
    exists_finiteChallenge_embedding_of_oddData
      p hG hH C D hFD hD hfloor hoffWindow
  let fG : D →+ G := (AddSubgroup.subtype (⊤ : AddSubgroup G)).comp f
  have hfGinj : Function.Injective fG := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext hxy
  let c : Fin m → G := fun i ↦
    fG ⟨d i, AddSubgroup.subset_closure
      ⟨Fin.natAdd n i, by simp⟩⟩
  have hgen : ∀ i : Fin (n + m),
      fG ⟨Fin.append b d i,
        AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
          Fin.append a c i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      calc
        fG _ =
            (C.iso.equiv
              ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩ : G) := by
                simpa [fG] using hfmark
                  ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩
        _ = a j := congrArg Subtype.val (C.iso.map_gen j)
    · simp only [Fin.append_right]
      rfl
  let C' : TupleIsoMap (Fin.append a c) (Fin.append b d) :=
    TupleIsoMap.ofInjectiveOnGenerators fG hfGinj hgen
  refine ⟨c, C', ?_⟩
  intro β x hx
  change ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
    ulmSubgroup p β (G := G)
  rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
    exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
  exact hffloor β x hx

/-- **Finite-tuple ACM response with the predecessor height condition.**

This is the tuple wrapper around the two-phase bounded Case 1(c) theorem.  It
returns one shared isomorphism on the enlarged tuples that has a global height
floor and preserves every filtration level below `ω·α` in both directions. -/
theorem exists_finiteTuple_cutoffResponse_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom ∧
      IsHeightPresBelowOn p C'.equiv.toAddMonoidHom (ω * α) := by
  let D : AddSubgroup H := tupleSubgroup (Fin.append b d)
  have hFD : tupleSubgroup b ≤ D := by
    apply AddSubgroup.closure_mono
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by simp⟩
  have hD : Set.Finite (D : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  obtain ⟨f, hfinj, hffloor, hfpres, hfmark⟩ :=
    exists_finiteChallenge_cutoffEmbedding_of_oddData_of_boundedTarget
      p hG hH C hGcap D hFD hD hbelow
  let fG : D →+ G := (AddSubgroup.subtype (⊤ : AddSubgroup G)).comp f
  have hfGinj : Function.Injective fG := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext hxy
  let c : Fin m → G := fun i ↦
    fG ⟨d i, AddSubgroup.subset_closure
      ⟨Fin.natAdd n i, by simp⟩⟩
  have hgen : ∀ i : Fin (n + m),
      fG ⟨Fin.append b d i,
        AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
          Fin.append a c i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      calc
        fG _ =
            (C.iso.equiv
              ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩ : G) := by
                simpa [fG] using hfmark
                  ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩
        _ = a j := congrArg Subtype.val (C.iso.map_gen j)
    · simp only [Fin.append_right]
      rfl
  let C' : TupleIsoMap (Fin.append a c) (Fin.append b d) :=
    TupleIsoMap.ofInjectiveOnGenerators fG hfGinj hgen
  refine ⟨c, C', ?_, ?_⟩
  · intro β x hx
    change ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
      ulmSubgroup p β (G := G)
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hffloor β x hx
  · intro β hβ x
    change ((x : H) ∈ ulmSubgroup p β (G := H) ↔
      ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
        ulmSubgroup p β (G := G))
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hfpres β hβ x

/-- **Bounded Case 1(c) finite-tuple response from the odd clauses alone.**

This is the finite-tuple wrapper around
`exists_finiteChallenge_cutoffEmbedding_of_oddData_of_boundedTarget_from_odd`.
Unlike the provisional theorem above, it assumes no below-base room budget:
the high phase charges only exact challenge reaches, while the low phase is the
cutoff Kaplansky climb. -/
theorem exists_finiteTuple_cutoffResponse_of_oddData_of_boundedTarget_from_odd
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom ∧
      IsHeightPresBelowOn p C'.equiv.toAddMonoidHom (ω * α) := by
  let D : AddSubgroup H := tupleSubgroup (Fin.append b d)
  have hFD : tupleSubgroup b ≤ D := by
    apply AddSubgroup.closure_mono
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by simp⟩
  have hD : Set.Finite (D : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  obtain ⟨f, hfinj, hffloor, hfpres, hfmark⟩ :=
    exists_finiteChallenge_cutoffEmbedding_of_oddData_of_boundedTarget_from_odd
      p hG hH C hGcap D hFD hD
  let fG : D →+ G := (AddSubgroup.subtype (⊤ : AddSubgroup G)).comp f
  have hfGinj : Function.Injective fG := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext hxy
  let c : Fin m → G := fun i ↦
    fG ⟨d i, AddSubgroup.subset_closure
      ⟨Fin.natAdd n i, by simp⟩⟩
  have hgen : ∀ i : Fin (n + m),
      fG ⟨Fin.append b d i,
        AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
          Fin.append a c i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      calc
        fG _ =
            (C.iso.equiv
              ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩ : G) := by
                simpa [fG] using hfmark
                  ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩
        _ = a j := congrArg Subtype.val (C.iso.map_gen j)
    · simp only [Fin.append_right]
      rfl
  let C' : TupleIsoMap (Fin.append a c) (Fin.append b d) :=
    TupleIsoMap.ofInjectiveOnGenerators fG hfGinj hgen
  refine ⟨c, C', ?_, ?_⟩
  · intro β x hx
    change ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
      ulmSubgroup p β (G := G)
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hffloor β x hx
  · intro β hβ x
    change ((x : H) ∈ ulmSubgroup p β (G := H) ↔
      ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
        ulmSubgroup p β (G := G))
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hfpres β hβ x

/-! ### The cap-truncated long-target response -/

/-- **Long-target finite-tuple response.**

The finite odd countdown reserves one cap level per remaining root extension
and finishes at the fixed base.  This packages its finite-subgroup map as the
enlarged tuple isomorphism used by ACM. -/
theorem exists_finiteTuple_cutoffResponse_of_oddData_of_longTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorAt p C'.equiv.toAddMonoidHom (ω * α) ∧
      IsHeightPresBelowOn p C'.equiv.toAddMonoidHom (ω * α) := by
  let D : AddSubgroup H := tupleSubgroup (Fin.append b d)
  have hFD : tupleSubgroup b ≤ D := by
    apply AddSubgroup.closure_mono
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by simp⟩
  have hD : Set.Finite (D : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  obtain ⟨f, hfinj, hfpres, hffloor, hfmark⟩ :=
    OddLongCountdown.finite_countdown_within
      p hG hH C hlong D hD hFD
  let fG : D →+ G := (AddSubgroup.subtype (⊤ : AddSubgroup G)).comp f
  have hfGinj : Function.Injective fG := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext hxy
  let c : Fin m → G := fun i ↦
    fG ⟨d i, AddSubgroup.subset_closure
      ⟨Fin.natAdd n i, by simp⟩⟩
  have hgen : ∀ i : Fin (n + m),
      fG ⟨Fin.append b d i,
        AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
          Fin.append a c i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      calc
        fG _ =
            (C.iso.equiv
              ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩ : G) := by
                simpa [fG] using hfmark
                  ⟨b j, AddSubgroup.subset_closure (Set.mem_range_self j)⟩
        _ = a j := congrArg Subtype.val (C.iso.map_gen j)
    · simp only [Fin.append_right]
      rfl
  let C' : TupleIsoMap (Fin.append a c) (Fin.append b d) :=
    TupleIsoMap.ofInjectiveOnGenerators fG hfGinj hgen
  refine ⟨c, C', ?_, ?_⟩
  · intro x hx
    change ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
      ulmSubgroup p (ω * α) (G := G)
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hffloor x hx
  · intro β hβ x
    change ((x : H) ∈ ulmSubgroup p β (G := H) ↔
      ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) ∈
        ulmSubgroup p β (G := G))
    rw [show ((C'.equiv x : tupleSubgroup (Fin.append a c)) : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hfpres β hβ x

/-- The long countdown in the literal height language consumed by the
successor and limit predecessor packages. -/
theorem exists_finiteTuple_predecessorHeightResponse_of_oddData_of_longTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      ∀ x : tupleSubgroup (Fin.append b d),
        (ulmHeight p (x : H) = ulmHeight p (C'.equiv x : G) ∧
          ulmHeight p (x : H) < ω * α) ∨
        (ω * α ≤ ulmHeight p (x : H) ∧
          ω * α ≤ ulmHeight p (C'.equiv x : G)) := by
  obtain ⟨c, C', _hfloor, hpres⟩ :=
    exists_finiteTuple_cutoffResponse_of_oddData_of_longTarget
      p hG hH C hlong d
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) :=
    Ordinal.isSuccLimit_omega0
  have hbase : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  exact ⟨c, C',
    heightsMatchBelow_of_heightPresBelowOn p hG hH hbase C' hpres⟩

/-- **Bounded Case 1(c) finite-tuple response in ACM's height language.**

The preceding map-level cutoff theorem implies the literal disjunction used by
the even/limit predecessor clauses.  The conversion is valid because
`omega * alpha` is a successor prelimit, so exact heights below the cutoff are
visible at two filtration levels that are themselves below the cutoff. -/
theorem exists_finiteTuple_predecessorHeightResponse_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom ∧
      ∀ x : tupleSubgroup (Fin.append b d),
        (ulmHeight p (x : H) = ulmHeight p (C'.equiv x : G) ∧
          ulmHeight p (x : H) < ω * α) ∨
        (ω * α ≤ ulmHeight p (x : H) ∧
          ω * α ≤ ulmHeight p (C'.equiv x : G)) := by
  obtain ⟨c, C', hfloor, hpres⟩ :=
    exists_finiteTuple_cutoffResponse_of_oddData_of_boundedTarget_from_odd
      p hG hH C hGcap d
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) :=
    Ordinal.isSuccLimit_omega0
  have hbase : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  exact ⟨c, C', hfloor,
    heightsMatchBelow_of_heightPresBelowOn p hG hH hbase C' hpres⟩

/-! ### Limit predecessors: assemble the reversed limit data -/

/-- **Bounded odd response packaged as limit predecessor data.**

The finite response preserves every filtration level below `ω * α`.  Together
with the odd ambient clauses, this gives the full limit condition in the
reversed orientation on the enlarged tuples.  This theorem is data-only: the
fact that a limit parameter satisfies `2 * α = α` is used later, at the
relation wrapper. -/
theorem exists_finiteTuple_limitPredecessorData_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G),
      Nonempty
        (AlgBFLimitCondData p hH hG α
          (Fin.append b d) (Fin.append a c)) := by
  obtain ⟨c, C', _hfloor, hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_boundedTarget
      p hG hH C hGcap d
  refine ⟨c, ⟨{
    iso := C'.symm
    lengths := ?_
    ulm_below := ?_
    heights := ?_ }⟩⟩
  · rcases C.lengths with hshort | hlong
    · exact Or.inl ⟨hshort.1.symm, by
        simpa [← hshort.1] using hshort.2⟩
    · have hbaseCap : ω * α ≤ ω * α + ω := le_self_add
      have hbaseMin : ω * α ≤
          min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * α + ω) :=
        le_min hlong.1 hbaseCap
      exact Or.inr ⟨hlong.1, hbaseMin.trans hlong.2⟩
  · intro β hβ
    exact (C.ulm_below β hβ).symm
  · intro x
    let y : tupleSubgroup (Fin.append b d) := C'.equiv.symm x
    have hy : C'.equiv y = x := C'.equiv.apply_symm_apply x
    rcases hheight y with hlow | hhigh
    · exact Or.inl ⟨by
        simpa [TupleIsoMap.symm, y, hy] using hlow.1.symm,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [TupleIsoMap.symm, y] using hhigh.1⟩

/-- **Long odd response packaged as limit predecessor data.** -/
theorem exists_finiteTuple_limitPredecessorData_of_oddData_of_longTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlongTarget : ω * α + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G),
      Nonempty
        (AlgBFLimitCondData p hH hG α
          (Fin.append b d) (Fin.append a c)) := by
  obtain ⟨c, C', hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_longTarget
      p hG hH C hlongTarget d
  refine ⟨c, ⟨{
    iso := C'.symm
    lengths := ?_
    ulm_below := ?_
    heights := ?_ }⟩⟩
  · rcases C.lengths with hshort | hlong
    · exact Or.inl ⟨hshort.1.symm, by
        simpa [← hshort.1] using hshort.2⟩
    · have hbaseCap : ω * α ≤ ω * α + ω := le_self_add
      have hbaseMin : ω * α ≤
          min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * α + ω) :=
        le_min hlong.1 hbaseCap
      exact Or.inr ⟨hlong.1, hbaseMin.trans hlong.2⟩
  · intro β hβ
    exact (C.ulm_below β hβ).symm
  · intro x
    let y : tupleSubgroup (Fin.append b d) := C'.equiv.symm x
    have hy : C'.equiv y = x := C'.equiv.apply_symm_apply x
    rcases hheight y with hlow | hhigh
    · exact Or.inl ⟨by
        simpa [TupleIsoMap.symm, y, hy] using hlow.1.symm,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [TupleIsoMap.symm, y] using hhigh.1⟩

/-- **Conditional bounded odd integration at a limit parameter.**

For limit `α`, ordinal arithmetic identifies the odd predecessor
`2 * α` with `α`.  The theorem above constructs limit algebraic data after
each challenge, and this wrapper consumes only the limit sufficiency direction
at `α`. -/
theorem bf_odd_limit_of_oddData_of_boundedTarget_of_limitSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (hLimit : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFLimitCond p hH hG α u v → BFRel p α k u v) :
    BFRel p (2 * α + 1) n a b := by
  rw [show 2 * α + 1 = Order.succ α by
    rw [Ordinal.two_mul_eq_self_of_isSuccLimit hα]
    rfl, BFRel_succ]
  intro m d
  obtain ⟨c, hpred⟩ :=
    exists_finiteTuple_limitPredecessorData_of_oddData_of_boundedTarget
      p hG hH C hGcap d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_iff_BFRel_swap]
  exact hLimit (Fin.append b d) (Fin.append a c) hpred

/-- Conditional long-target odd integration at a limit parameter. -/
theorem bf_odd_limit_of_oddData_of_longTarget_of_limitSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlongTarget : ω * α + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    (hLimit : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFLimitCond p hH hG α u v → BFRel p α k u v) :
    BFRel p (2 * α + 1) n a b := by
  rw [show 2 * α + 1 = Order.succ α by
    rw [Ordinal.two_mul_eq_self_of_isSuccLimit hα]
    rfl, BFRel_succ]
  intro m d
  obtain ⟨c, hpred⟩ :=
    exists_finiteTuple_limitPredecessorData_of_oddData_of_longTarget
      p hG hH C hlongTarget d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_iff_BFRel_swap]
  exact hLimit (Fin.append b d) (Fin.append a c) hpred

/-! ### Successor predecessors: assemble the corrected even data first -/

/-- **Bounded odd response packaged as corrected even predecessor data.**

When `α = succ δ`, the predecessor of the odd level is even.  This theorem is
purely algebraic: it constructs the response and the full *crossed* even
condition with the ambient groups reversed, but makes no appeal to an even
back-and-forth characterization.

The absolute predecessor window comes from the odd `ulm_below` equality.  The
oppositely oriented marked-graded comparison comes from the finite-mark
transfer lemma and the response's exact filtration behavior below
`ω * succ δ`.  Keeping this theorem free of `BFRel` isolates every semantic
field before the relation-level induction is attempted. -/
theorem exists_finiteTuple_evenPredecessorData_of_oddData_of_boundedTarget
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) <
      ω * Order.succ δ + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G),
      Nonempty
        (AlgBFEvenCondData p hH hG δ (Fin.append b d) (Fin.append a c)) := by
  obtain ⟨c, C', _hfloor, hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_boundedTarget
      p hG hH C hGcap d
  have hcut : ω * Order.succ δ = ω * δ + ω := by
    rw [Ordinal.mul_succ]
  have hleftFinite : Set.Finite
      (tupleSubgroup (Fin.append b d) : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  have hrightFinite : Set.Finite
      (tupleSubgroup (Fin.append a c) : Set G) :=
    tupleSubgroup_finite p hG.primary (Fin.append a c)
  refine ⟨c, ⟨{
    iso := C'.symm
    lengths := ?_
    ulm_below := ?_
    window := ?_
    heights := ?_ }⟩⟩
  · rcases C.lengths with hshort | hlong
    · have hshortlt := hshort.2
      rw [hcut] at hshortlt
      exact Or.inl ⟨hshort.1.symm, hshort.1.symm ▸ hshortlt⟩
    · refine Or.inr ⟨?_, ?_⟩
      · have hlongBase := hlong.1
        rw [hcut] at hlongBase
        exact hlongBase
      · have hbaseCap : ω * Order.succ δ ≤ ω * Order.succ δ + ω :=
          le_self_add
        have hbaseMin : ω * Order.succ δ ≤
            min (ulmLength p (G := H) hH : Ordinal.{0})
              (ω * Order.succ δ + ω) :=
          le_min hlong.1 hbaseCap
        have htargetBase := hbaseMin.trans hlong.2
        rw [hcut] at htargetBase
        exact htargetBase
  · intro β hβ
    have hβ' : β < ω * Order.succ δ :=
      hβ.trans_le (by rw [hcut]; exact le_self_add)
    exact (C.ulm_below β hβ').symm
  · apply EvenWindowCrossed.of_eq
    · intro β _hbase hβ
      have hβ' : β < ω * Order.succ δ := by
        rw [hcut]
        exact hβ
      exact (C.ulm_below β hβ').symm
    · intro β _hbase hβ
      have hβ' : β < ω * Order.succ δ := by
        rw [hcut]
        exact hβ
      have hmarkHeight : ∀ x : tupleSubgroup (Fin.append b d),
          (ulmHeight p (C'.equiv x : G) = ulmHeight p (x : H) ∧
            ulmHeight p (x : H) < ω * Order.succ δ) ∨
          (ω * Order.succ δ ≤ ulmHeight p (x : H) ∧
            ω * Order.succ δ ≤ ulmHeight p (C'.equiv x : G)) := by
        intro x
        rcases hheight x with hlow | hhigh
        · exact Or.inl ⟨hlow.1.symm, hlow.2⟩
        · exact Or.inr hhigh
      exact (markedGradedInvariant_eq_iff_of_heightPres
        p hH hG
        (tupleSubgroup (Fin.append b d))
        (tupleSubgroup (Fin.append a c))
        hleftFinite hrightFinite C'.equiv
        (ω * Order.succ δ) hmarkHeight β hβ').mp
          (C.ulm_below β hβ')
  · intro x
    let y : tupleSubgroup (Fin.append b d) := C'.equiv.symm x
    have hy : C'.equiv y = x := C'.equiv.apply_symm_apply x
    have hheightAtCut := hheight y
    have hcutTop :
        ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) =
          ((ω * δ + ω : Ordinal.{0}) : WithTop Ordinal.{0}) :=
      congrArg (fun z : Ordinal.{0} ↦ (z : WithTop Ordinal.{0})) hcut
    change
      (ulmHeight p (y : H) = ulmHeight p (C'.equiv y : G) ∧
        ulmHeight p (y : H) <
          ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
      (((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (y : H) ∧
        ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (C'.equiv y : G)) at hheightAtCut
    rw [hcutTop] at hheightAtCut
    rcases hheightAtCut with hlow | hhigh
    · exact Or.inl ⟨by
        simpa [TupleIsoMap.symm, y, hy] using hlow.1.symm,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * δ + ω : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [TupleIsoMap.symm, y] using hhigh.1⟩

/-- **Long odd response packaged as corrected even predecessor data.** -/
theorem exists_finiteTuple_evenPredecessorData_of_oddData_of_longTarget
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hlongTarget : ω * Order.succ δ + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G),
      Nonempty
        (AlgBFEvenCondData p hH hG δ (Fin.append b d) (Fin.append a c)) := by
  obtain ⟨c, C', hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_longTarget
      p hG hH C hlongTarget d
  have hcut : ω * Order.succ δ = ω * δ + ω := by
    rw [Ordinal.mul_succ]
  have hleftFinite : Set.Finite
      (tupleSubgroup (Fin.append b d) : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b d)
  have hrightFinite : Set.Finite
      (tupleSubgroup (Fin.append a c) : Set G) :=
    tupleSubgroup_finite p hG.primary (Fin.append a c)
  refine ⟨c, ⟨{
    iso := C'.symm
    lengths := ?_
    ulm_below := ?_
    window := ?_
    heights := ?_ }⟩⟩
  · rcases C.lengths with hshort | hlong
    · have hshortlt := hshort.2
      rw [hcut] at hshortlt
      exact Or.inl ⟨hshort.1.symm, hshort.1.symm ▸ hshortlt⟩
    · refine Or.inr ⟨?_, ?_⟩
      · have hlongBase := hlong.1
        rw [hcut] at hlongBase
        exact hlongBase
      · have hbaseCap : ω * Order.succ δ ≤ ω * Order.succ δ + ω :=
          le_self_add
        have hbaseMin : ω * Order.succ δ ≤
            min (ulmLength p (G := H) hH : Ordinal.{0})
              (ω * Order.succ δ + ω) :=
          le_min hlong.1 hbaseCap
        have htargetBase := hbaseMin.trans hlong.2
        rw [hcut] at htargetBase
        exact htargetBase
  · intro β hβ
    have hβ' : β < ω * Order.succ δ :=
      hβ.trans_le (by rw [hcut]; exact le_self_add)
    exact (C.ulm_below β hβ').symm
  · apply EvenWindowCrossed.of_eq
    · intro β _hbase hβ
      have hβ' : β < ω * Order.succ δ := by
        rw [hcut]
        exact hβ
      exact (C.ulm_below β hβ').symm
    · intro β _hbase hβ
      have hβ' : β < ω * Order.succ δ := by
        rw [hcut]
        exact hβ
      have hmarkHeight : ∀ x : tupleSubgroup (Fin.append b d),
          (ulmHeight p (C'.equiv x : G) = ulmHeight p (x : H) ∧
            ulmHeight p (x : H) < ω * Order.succ δ) ∨
          (ω * Order.succ δ ≤ ulmHeight p (x : H) ∧
            ω * Order.succ δ ≤ ulmHeight p (C'.equiv x : G)) := by
        intro x
        rcases hheight x with hlow | hhigh
        · exact Or.inl ⟨hlow.1.symm, hlow.2⟩
        · exact Or.inr hhigh
      exact (markedGradedInvariant_eq_iff_of_heightPres
        p hH hG
        (tupleSubgroup (Fin.append b d))
        (tupleSubgroup (Fin.append a c))
        hleftFinite hrightFinite C'.equiv
        (ω * Order.succ δ) hmarkHeight β hβ').mp
          (C.ulm_below β hβ')
  · intro x
    let y : tupleSubgroup (Fin.append b d) := C'.equiv.symm x
    have hy : C'.equiv y = x := C'.equiv.apply_symm_apply x
    have hheightAtCut := hheight y
    have hcutTop :
        ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) =
          ((ω * δ + ω : Ordinal.{0}) : WithTop Ordinal.{0}) :=
      congrArg (fun z : Ordinal.{0} ↦ (z : WithTop Ordinal.{0})) hcut
    change
      (ulmHeight p (y : H) = ulmHeight p (C'.equiv y : G) ∧
        ulmHeight p (y : H) <
          ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
      (((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (y : H) ∧
        ((ω * Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (C'.equiv y : G)) at hheightAtCut
    rw [hcutTop] at hheightAtCut
    rcases hheightAtCut with hlow | hhigh
    · exact Or.inl ⟨by
        simpa [TupleIsoMap.symm, y, hy] using hlow.1.symm,
        by
          calc
            ulmHeight p (x : G) = ulmHeight p (y : H) := by
              simpa [hy] using hlow.1.symm
            _ < ((ω * δ + ω : Ordinal.{0}) : WithTop Ordinal.{0}) := hlow.2⟩
    · exact Or.inr ⟨by simpa [hy] using hhigh.2,
        by simpa [TupleIsoMap.symm, y] using hhigh.1⟩

/-- **Conditional relation wrapper for the bounded successor branch.**

This is the only relation-level theorem in the successor-predecessor module.
It takes the even sufficiency direction at `δ` as an explicit induction
hypothesis, uses the data-only theorem above for the response, and handles only
the ordinal and orientation bookkeeping.  In particular it does not depend on
the unfinished global even biconditional. -/
theorem bf_odd_succ_of_oddData_of_boundedTarget_of_evenSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) <
      ω * Order.succ δ + ω)
    (hEven : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFEvenCond p hH hG δ u v →
        BFRel p (2 * δ + 2) k u v) :
    BFRel p (2 * Order.succ δ + 1) n a b := by
  rw [show 2 * Order.succ δ + 1 = Order.succ (2 * δ + 2) by
    rw [Ordinal.mul_succ]
    rfl, BFRel_succ]
  intro m d
  obtain ⟨c, hpred⟩ :=
    exists_finiteTuple_evenPredecessorData_of_oddData_of_boundedTarget
      p hG hH C hGcap d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_iff_BFRel_swap]
  exact hEven (Fin.append b d) (Fin.append a c) hpred

/-- Conditional long-target odd integration at a successor parameter. -/
theorem bf_odd_succ_of_oddData_of_longTarget_of_evenSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hlongTarget : ω * Order.succ δ + ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}))
    (hEven : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFEvenCond p hH hG δ u v →
        BFRel p (2 * δ + 2) k u v) :
    BFRel p (2 * Order.succ δ + 1) n a b := by
  rw [show 2 * Order.succ δ + 1 = Order.succ (2 * δ + 2) by
    rw [Ordinal.mul_succ]
    rfl, BFRel_succ]
  intro m d
  obtain ⟨c, hpred⟩ :=
    exists_finiteTuple_evenPredecessorData_of_oddData_of_longTarget
      p hG hH C hlongTarget d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_iff_BFRel_swap]
  exact hEven (Fin.append b d) (Fin.append a c) hpred

/-- **Actual relation-level bounded Case 1(c) integration at `alpha = 0`.**

At predecessor level zero, the enlarged tuple isomorphism is the whole
back-and-forth obligation.  This theorem verifies that the finite response
construction plugs directly into `BFRel_succ`; higher successor predecessors
add the corrected crossed even-window package and consume the even sufficiency
direction explicitly, as in the conditional wrapper immediately above. -/
theorem bf_one_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH 0 a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω) :
    BFRel p 1 n a b := by
  rw [show (1 : Ordinal.{0}) = Order.succ 0 by simp, BFRel_succ]
  intro m d
  obtain ⟨c, C', _hfloor, _hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_boundedTarget
      p hG hH C (by simpa using hGcap) d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_zero]
  exact ⟨C'.equiv, C'.map_gen⟩

/-- Relation-level long-target odd integration at parameter zero. -/
theorem bf_one_of_oddData_of_longTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH 0 a b)
    (hlongTarget : ω ≤ (ulmLength p (G := G) hG : Ordinal.{0})) :
    BFRel p 1 n a b := by
  rw [show (1 : Ordinal.{0}) = Order.succ 0 by simp, BFRel_succ]
  intro m d
  obtain ⟨c, C', _hheight⟩ :=
    exists_finiteTuple_predecessorHeightResponse_of_oddData_of_longTarget
      p hG hH C (by simpa using hlongTarget) d
  refine ⟨c, ?_⟩
  rw [BFRelReverse_zero]
  exact ⟨C'.equiv, C'.map_gen⟩

/-- **Bounded-tail finite-tuple response.**

This combines the bounded-tail band assembly with the finite-tuple wrapper.
The odd clauses discharge the marked floor, active window, and upper band;
the only budget still assumed is below `ω·α`. -/
theorem exists_finiteTuple_heightFloorResponse_of_oddData_of_boundedTarget
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom := by
  have htail : ulmSubgroup p (ω * α + ω) (G := H) = ⊥ :=
    AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
      p hG hH C hGcap
  have hfloor : IsHeightFloorOn p C.iso.equiv.toAddMonoidHom :=
    AlgBFOddCondData.heightFloorOn_of_sourceTail_eq_bot p hG hH C htail
  apply exists_finiteTuple_heightFloorResponse_of_oddData
    p hG hH C d hfloor
  intro β hout
  by_cases hlow : β < ω * α
  · exact hbelow β hlow (hfloor (Order.succ β)) (hfloor β)
  · have hbase : ω * α ≤ β := le_of_not_gt hlow
    have hcap : ω * α + ω ≤ β := by
      apply le_of_not_gt
      intro hwindow
      exact hout ⟨hbase, hwindow⟩
    apply Survival.KernelRoomBudgetAt.of_ulmSubgroup_le p
    exact le_trans (ulmSubgroup_antitone p hcap) (by simp [htail])

end AlgebraicBFConditions
