import Lib.BackForth.EvenToOdd
import Lib.BackForth.EvenHighCountdown
import Lib.BackForth.LocalFiniteEmbedding

/-!
# The exact finite-response seam for even sufficiency

At level `2 * α + 2`, the successor definition challenges the right ambient
group and reverses orientation at predecessor level `2 * α + 1`.  Thus the
algebraic response needed from current even data is not merely odd data on the
current tuple: after adjoining a finite tuple `c`, one must choose a matching
tuple `d` and obtain odd data in the reversed orientation on the enlarged
tuples.

This module names that response property and proves the relation-level wrapper
which consumes it.  Constructing the responses remains a separate algebraic
extension theorem; keeping that obligation explicit prevents it from being
hidden inside a global biconditional.
-/

noncomputable section

open Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]

namespace AlgebraicBFConditions

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

/-- The response, enlarged inverse tuple map, and height clause for one finite
even challenge.  This is the map-theoretic core of the required odd predecessor;
the room--kernel budget is kept separate below. -/
structure EvenFiniteTupleOddCoreData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H) : Type u where
  /-- The response to the prescribed right-side challenge. -/
  response : Fin m → G
  /-- The predecessor odd map points from the enlarged `G` mark back to the
  enlarged `H` mark. -/
  iso : TupleIsoMap (Fin.append b c) (Fin.append a response)
  /-- The reverse-orientation odd height clause on the enlarged marks. -/
  heights : ∀ x : tupleSubgroup (Fin.append a response),
    (ulmHeight p (x : G) = ulmHeight p (iso.equiv x : H) ∧
      ulmHeight p (x : G) < ω * α) ∨
    (ω * α ≤ ulmHeight p (x : G) ∧
      min (ulmHeight p (x : G))
          ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (iso.equiv x : H))
  /-- In the bounded-length branch the constructed enlarged map is exact
  throughout the whole finite omega window. -/
  short_presBelowCap :
    (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω →
      IsHeightPresBelowOn p iso.equiv.toAddMonoidHom (ω * α + ω)

/-- The genuinely map-sensitive data needed for one even challenge response.

The ambient length and below-base Ulm clauses do not mention the enlarged
marks and are inherited from the current even package.  What must actually be
constructed is a response element, the extended reverse-orientation tuple
isomorphism, its directional height control, and its enlarged `K_β` budget. -/
structure EvenFiniteTupleOddMapData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H) : Type u
    extends EvenFiniteTupleOddCoreData p hG hH C c where
  /-- The enlarged reverse map retains the exact room--kernel budget. -/
  kernel_room :
    ∀ (β : Ordinal.{0}) (_hβ : ω * α ≤ β) (hβ' : β < ω * α + ω),
      roomInvariant p (tupleSubgroup (Fin.append a response)) β +
        jumpKernelInvariant p (iso.equiv.toAddMonoidHom)
          (heightFloorAt_of_heights p iso heights (Order.succ β)
            (Order.succ_le_of_lt hβ'))
          (heightFloorAt_of_heights p iso heights β (le_of_lt hβ')) ≤
        roomInvariant p (tupleSubgroup (Fin.append b c)) β

/-- The finite subgroup generated after prescribing `c`. -/
abbrev evenFiniteTupleChallengeSubgroup
    (b : Fin n → H) {m : ℕ} (c : Fin m → H) : AddSubgroup H :=
  tupleSubgroup (Fin.append b c)

/-- The marked subgroup together with the part of the finite challenge already
at the odd base.  Case 2 first handles these high directions with its finite
countdown; the floor-free cutoff climb can then absorb every remaining
direction strictly below the base. -/
abbrev evenFiniteTupleHighSubgroup
    (α : Ordinal.{0}) (b : Fin n → H)
    {m : ℕ} (c : Fin m → H) : AddSubgroup H :=
  tupleSubgroup b ⊔
    (evenFiniteTupleChallengeSubgroup b c ⊓
      ulmSubgroup p (ω * α) (G := H))

/-- The map package needed from the high-tail phase of the even proof.

There is deliberately no global height floor.  The high phase preserves
filtration exactly below the odd base and retains only the directional
truncated-height inequality above it, matching the countdown invariant in
Case 2 of the paper. -/
structure EvenFiniteTupleHighMapData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H) : Type u where
  map : evenFiniteTupleHighSubgroup p α b c →+ (⊤ : AddSubgroup G)
  map_injective : Function.Injective map
  presBelow : IsHeightPresBelowOn p map (ω * α)
  short_presBelowCap :
    (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω →
      IsHeightPresBelowOn p map (ω * α + ω)
  reverse_floor : ∀ x : evenFiniteTupleHighSubgroup p α b c,
    min (ulmHeight p (map x : G))
        ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
      ulmHeight p (x : H)
  mark : ∀ x : tupleSubgroup b,
    (map ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩ : G) =
      (C.iso.equiv x : G)

/-- The finite high countdown constructs the complete high-phase map package
for every finite-tuple challenge.  No embedding hypothesis on a larger ambient
group is used: finiteness belongs only to the subgroup generated by the old
tuple and the prescribed challenge. -/
theorem exists_evenFiniteTupleHighMapData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleHighMapData p hG hH C c) := by
  let D : AddSubgroup H := evenFiniteTupleHighSubgroup p α b c
  let Dall : AddSubgroup H := evenFiniteTupleChallengeSubgroup b c
  have hmarkD : tupleSubgroup b ≤ D := le_sup_left
  have hmarkAll : tupleSubgroup b ≤ Dall := by
    change AddSubgroup.closure (Set.range b) ≤
      AddSubgroup.closure (Set.range (Fin.append b c))
    apply AddSubgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castAdd m, by simp⟩
  have hDAll : D ≤ Dall := sup_le hmarkAll inf_le_left
  have hDallFinite : Set.Finite (Dall : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b c)
  have hDfinite : Set.Finite (D : Set H) := hDallFinite.subset hDAll
  obtain ⟨f, hfinj, hpres, hshortPres, hreverse, hmark⟩ :=
    EvenHighCountdown.finite_countdown_within
      p hG hH C D hDfinite hmarkD
  exact ⟨{
    map := f
    map_injective := hfinj
    presBelow := hpres
    short_presBelowCap := hshortPres
    reverse_floor := hreverse
    mark := hmark }⟩

/-- A high-tail countdown map is enough to construct the response, enlarged
inverse tuple isomorphism, and the complete odd height clause.  The only field
of `EvenFiniteTupleOddMapData` not produced here is its enlarged room--kernel budget.

The construction first completes the finite challenged subgroup in the
forward `H → G` orientation using the floor-free cutoff climb, then inverts the
resulting tuple isomorphism to obtain the odd predecessor orientation. -/
theorem exists_evenFiniteTupleOddCoreData_of_highMap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H)
    (M : EvenFiniteTupleHighMapData p hG hH C c) :
    Nonempty (EvenFiniteTupleOddCoreData p hG hH C c) := by
  let D : AddSubgroup H := evenFiniteTupleChallengeSubgroup b c
  let Dhi : AddSubgroup H := evenFiniteTupleHighSubgroup p α b c
  have hFD : tupleSubgroup b ≤ D := by
    change AddSubgroup.closure (Set.range b) ≤
      AddSubgroup.closure (Set.range (Fin.append b c))
    apply AddSubgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castAdd m, by simp⟩
  have hD : Set.Finite (D : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b c)
  have hDhiD : Dhi ≤ D := sup_le hFD inf_le_left
  have hDhifinite : Set.Finite (Dhi : Set H) := hD.subset hDhiD
  let s : LocalFiniteEmbedding.LocalCutoffPresStage
      p (A := G) D (ω * α) :=
    { source := Dhi
      source_le := hDhiD
      source_finite := hDhifinite
      map := M.map
      map_injective := M.map_injective
      presBelow := M.presBelow
      tail_le := fun x hx ↦ AddSubgroup.mem_sup_right hx }
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) :=
    Ordinal.isSuccLimit_omega0
  have hbase : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  obtain ⟨f, hfinj, hfpres, hfhi⟩ :=
    LocalFiniteEmbedding.finite_cutoff_pres_climb_within
      p hH hD hbase C.ulm_below s
  let fG : D →+ G := (AddSubgroup.subtype (⊤ : AddSubgroup G)).comp f
  have hfGinj : Function.Injective fG := by
    intro x y hxy
    apply hfinj
    exact Subtype.ext hxy
  have hmemD (i : Fin (n + m)) :
      (Fin.append b c : Fin (n + m) → H) i ∈ D := by
    change (Fin.append b c : Fin (n + m) → H) i ∈
      AddSubgroup.closure (Set.range (Fin.append b c))
    exact AddSubgroup.subset_closure (Set.mem_range_self i)
  let cD (j : Fin m) : D :=
    ⟨c j, by simpa using hmemD (Fin.natAdd n j)⟩
  let d : Fin m → G := fun j ↦ fG (cD j)
  have hfmark : ∀ x : tupleSubgroup b,
      fG ⟨(x : H), hFD x.property⟩ = (C.iso.equiv x : G) := by
    intro x
    let xhi : Dhi := ⟨(x : H), AddSubgroup.mem_sup_left x.property⟩
    calc
      fG ⟨(x : H), hFD x.property⟩ = (M.map xhi : G) := by
        simpa [fG, xhi, s, Dhi] using hfhi xhi
      _ = (C.iso.equiv x : G) := by
        simpa [xhi, Dhi] using M.mark x
  have hgen : ∀ i : Fin (n + m),
      fG (⟨(Fin.append b c : Fin (n + m) → H) i, hmemD i⟩ : D) =
          (Fin.append a d : Fin (n + m) → G) i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      calc
        fG _ =
            (C.iso.equiv
              ⟨b j, AddSubgroup.subset_closure
                (Set.mem_range_self j)⟩ : G) := by
          simpa [D, evenFiniteTupleChallengeSubgroup] using
            hfmark ⟨b j, AddSubgroup.subset_closure
              (Set.mem_range_self j)⟩
        _ = a j := congrArg Subtype.val (C.iso.map_gen j)
    · simp only [Fin.append_right]
      rfl
  let forward : TupleIsoMap (Fin.append a d) (Fin.append b c) :=
    TupleIsoMap.ofInjectiveOnGenerators fG hfGinj hgen
  have hforwardPres :
      IsHeightPresBelowOn p forward.equiv.toAddMonoidHom (ω * α) := by
    intro β hβ x
    change ((x : H) ∈ ulmSubgroup p β (G := H) ↔
      (forward.equiv x : G) ∈ ulmSubgroup p β (G := G))
    rw [show (forward.equiv x : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hfpres β hβ x
  have hfPresCap :
      (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω →
        IsHeightPresBelowOn p f (ω * α + ω) := by
    intro hshort β hβ y
    by_cases hybase : (y : H) ∈ ulmSubgroup p (ω * α) (G := H)
    · let yhi : Dhi :=
        ⟨(y : H), AddSubgroup.mem_sup_right ⟨y.property, hybase⟩⟩
      have hM := M.short_presBelowCap hshort β hβ yhi
      have hfy : (f y : G) = (M.map yhi : G) := by
        simpa [s, yhi, Dhi] using hfhi yhi
      simpa [hfy, yhi] using hM
    · have hy0 : (y : H) ≠ 0 := by
        intro hy0
        apply hybase
        simp [hy0]
      obtain ⟨γ, hyγ, hySucc⟩ :=
        exists_ulmHeight_eq_of_ne_zero (p := p) hH hy0
      have hγbase : γ < ω * α := by
        by_contra hnot
        exact hybase (ulmSubgroup_antitone p (le_of_not_gt hnot) hyγ)
      have hbasePre : Order.IsSuccPrelimit (ω * α) :=
        Ordinal.isSuccPrelimit_mul_left Ordinal.isSuccLimit_omega0
      have hsuccγbase : Order.succ γ < ω * α :=
        hbasePre.succ_lt hγbase
      have hfγ : (f y : G) ∈ ulmSubgroup p γ (G := G) :=
        (hfpres γ hγbase y).mp hyγ
      have hfSucc : (f y : G) ∉
          ulmSubgroup p (Order.succ γ) (G := G) := by
        intro hf
        exact hySucc ((hfpres (Order.succ γ) hsuccγbase y).mpr hf)
      have hyheight : ulmHeight p (y : H) =
          (γ : WithTop Ordinal.{0}) :=
        ulmHeight_eq_of_mem_not_mem_succ p (y : H) γ hyγ hySucc
      have hfheight : ulmHeight p (f y : G) =
          (γ : WithTop Ordinal.{0}) :=
        ulmHeight_eq_of_mem_not_mem_succ p (f y : G) γ hfγ hfSucc
      rw [mem_ulmSubgroup_iff_le_ulmHeight,
        mem_ulmSubgroup_iff_le_ulmHeight, hfheight, hyheight]
  have hforwardPresCap :
      (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω →
        IsHeightPresBelowOn p forward.equiv.toAddMonoidHom
          (ω * α + ω) := by
    intro hshort β hβ x
    change ((x : H) ∈ ulmSubgroup p β (G := H) ↔
      (forward.equiv x : G) ∈ ulmSubgroup p β (G := G))
    rw [show (forward.equiv x : G) = fG x by
      exact TupleIsoMap.ofInjectiveOnGenerators_apply fG hfGinj hgen x]
    exact hfPresCap hshort β hβ x
  let reverse : TupleIsoMap (Fin.append b c) (Fin.append a d) := forward.symm
  have hreversePres :
      IsHeightPresBelowOn p reverse.equiv.toAddMonoidHom (ω * α) := by
    intro β hβ x
    let y : tupleSubgroup (Fin.append b c) := forward.equiv.symm x
    have hy : forward.equiv y = x := forward.equiv.apply_symm_apply x
    simpa [reverse, TupleIsoMap.symm, y, hy] using
      (hforwardPres β hβ y).symm
  have hreversePresCap :
      (ulmLength p (G := H) hH : Ordinal.{0}) < ω * α + ω →
        IsHeightPresBelowOn p reverse.equiv.toAddMonoidHom
          (ω * α + ω) := by
    intro hshort β hβ x
    let y : tupleSubgroup (Fin.append b c) := forward.equiv.symm x
    have hy : forward.equiv y = x := forward.equiv.apply_symm_apply x
    simpa [reverse, TupleIsoMap.symm, y, hy] using
      (hforwardPresCap hshort β hβ y).symm
  have hmatch :=
    heightsMatchBelow_of_heightPresBelowOn p hH hG hbase reverse hreversePres
  have hheights : ∀ x : tupleSubgroup (Fin.append a d),
      (ulmHeight p (x : G) = ulmHeight p (reverse.equiv x : H) ∧
        ulmHeight p (x : G) < ω * α) ∨
      (ω * α ≤ ulmHeight p (x : G) ∧
        min (ulmHeight p (x : G))
            ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (reverse.equiv x : H)) := by
    intro x
    rcases hmatch x with hlow | hhigh
    · exact Or.inl hlow
    · refine Or.inr ⟨hhigh.1, ?_⟩
      let y : D := forward.equiv.symm x
      have hybase : (y : H) ∈ ulmSubgroup p (ω * α) (G := H) := by
        rw [mem_ulmSubgroup_iff_le_ulmHeight]
        simpa [reverse, TupleIsoMap.symm, y] using hhigh.2
      let yhi : Dhi :=
        ⟨(y : H), AddSubgroup.mem_sup_right ⟨y.property, hybase⟩⟩
      have hmap : (M.map yhi : G) = (x : G) := by
        calc
          (M.map yhi : G) = (f ⟨(y : H), hDhiD yhi.property⟩ : G) := by
            symm
            simpa [s, yhi, Dhi] using hfhi yhi
          _ = fG y := rfl
          _ = (forward.equiv y : G) := by
            symm
            exact TupleIsoMap.ofInjectiveOnGenerators_apply
              fG hfGinj hgen y
          _ = (x : G) := congrArg Subtype.val
            (forward.equiv.apply_symm_apply x)
      simpa [hmap, reverse, TupleIsoMap.symm, yhi, y] using
        M.reverse_floor yhi
  exact ⟨{
    response := d
    iso := reverse
    heights := hheights
    short_presBelowCap := hreversePresCap }⟩

/-- The response element, enlarged inverse tuple isomorphism, and full odd
height clause are unconditional consequences of current even data.  The
enlarged room--kernel budget remains the separate map-sensitive obligation. -/
theorem exists_evenFiniteTupleOddCoreData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleOddCoreData p hG hH C c) := by
  obtain ⟨M⟩ := exists_evenFiniteTupleHighMapData p hG hH C c
  exact exists_evenFiniteTupleOddCoreData_of_highMap p hG hH C c M

/-- The enlarged inverse map constructed from the countdown satisfies the
exact room--kernel budget.  In the bounded branch it is filtration-exact up to
the cap, so the jump kernel vanishes and the room sequences telescope.  In the
long branch both finite-mark rooms are countably infinite, while the new jump
kernel is finite-dimensional. -/
theorem EvenFiniteTupleOddCoreData.kernel_room_of_countable
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : EvenHighCountdown.Context p hG hH α a b}
    {m : ℕ} {c : Fin m → H}
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β ≤
        roomInvariant p (tupleSubgroup b) β)
    (R : EvenFiniteTupleOddCoreData p hG hH C c) :
    ∀ (β : Ordinal.{0}) (_hβ : ω * α ≤ β) (hβ' : β < ω * α + ω),
      roomInvariant p (tupleSubgroup (Fin.append a R.response)) β +
        jumpKernelInvariant p (R.iso.equiv.toAddMonoidHom)
          (heightFloorAt_of_heights p R.iso R.heights (Order.succ β)
            (Order.succ_le_of_lt hβ'))
          (heightFloorAt_of_heights p R.iso R.heights β (le_of_lt hβ')) ≤
        roomInvariant p (tupleSubgroup (Fin.append b c)) β := by
  intro β hbase hcap
  let F : AddSubgroup G := tupleSubgroup (Fin.append a R.response)
  let E : AddSubgroup H := tupleSubgroup (Fin.append b c)
  let φ : F →+ E := R.iso.equiv.toAddMonoidHom
  let hsucc : IsHeightFloorAt p φ (Order.succ β) :=
    heightFloorAt_of_heights p R.iso R.heights (Order.succ β)
      (Order.succ_le_of_lt hcap)
  let hβfloor : IsHeightFloorAt p φ β :=
    heightFloorAt_of_heights p R.iso R.heights β (le_of_lt hcap)
  have hFfinite : Set.Finite (F : Set G) :=
    tupleSubgroup_finite p hG.primary (Fin.append a R.response)
  have hEfinite : Set.Finite (E : Set H) :=
    tupleSubgroup_finite p hH.primary (Fin.append b c)
  rcases C.lengths with hshort | hlong
  · have hHshort : (ulmLength p (G := H) hH : Ordinal.{0}) <
        ω * α + ω := by
      simpa [← hshort.1] using hshort.2
    have hpres := R.short_presBelowCap hHshort
    have hinj : Function.Injective (jumpMap p φ hsucc hβfloor) := by
      apply jumpMap_injective_of_equiv_of_reflectsAt p R.iso.equiv
      intro x hx
      exact (hpres β hcap x).mpr hx
    have hker : jumpKernelInvariant p φ hsucc hβfloor = 0 :=
      (jumpKernelInvariant_eq_zero_iff p φ hsucc hβfloor).2 hinj
    have hsuccCap : Order.succ β < ω * α + ω :=
      (Ordinal.isSuccLimit_add (ω * α) Ordinal.isSuccLimit_omega0).succ_lt hcap
    let initial : UlmStageAt p (G := H) (H := G) β :=
      { A := tupleSubgroup b
        B := tupleSubgroup a
        hAfinite := tupleSubgroup_finite p hH.primary b
        hBfinite := tupleSubgroup_finite p hG.primary a
        e := C.iso.equiv
        hφ_at := fun z ↦ C.presBelowCap β hcap z
        hφ_succ := fun z ↦ C.presBelowCap (Order.succ β) hsuccCap z
        hφ_succSucc := fun z ↦ C.presBelowCap
          (Order.succ (Order.succ β))
          ((Ordinal.isSuccLimit_add (ω * α)
            Ordinal.isSuccLimit_omega0).succ_lt hsuccCap) z }
    have hforwardPres : IsHeightPresBelowOn p
        R.iso.equiv.symm.toAddMonoidHom (ω * α + ω) :=
      ExactStageTransfer.heightPresBelowOn_symm p R.iso.equiv hpres
    let current : UlmStageAt p (G := H) (H := G) β :=
      { A := E
        B := F
        hAfinite := hEfinite
        hBfinite := hFfinite
        e := R.iso.equiv.symm
        hφ_at := fun z ↦ hforwardPres β hcap z
        hφ_succ := fun z ↦ hforwardPres (Order.succ β) hsuccCap z
        hφ_succSucc := fun z ↦ hforwardPres
          (Order.succ (Order.succ β))
          ((Ordinal.isSuccLimit_add (ω * α)
            Ordinal.isSuccLimit_omega0).succ_lt hsuccCap) z }
    have hrooms : roomInvariant p F β ≤ roomInvariant p E β :=
      ExactStageTransfer.roomInvariant_reverse_of_initial
        p initial current (by simpa [initial] using hroom β hbase hcap)
    change roomInvariant p F β + jumpKernelInvariant p φ hsucc hβfloor ≤
      roomInvariant p E β
    rw [hker, add_zero]
    exact hrooms
  · have hGinf : Set.Infinite (pSocleAt p β (G := G) : Set G) :=
      AlgBFEvenCondData.infinite_pSocleAt_of_longWindow
        p hG hlong.1 hbase hcap
    have hHinf : Set.Infinite (pSocleAt p β (G := H) : Set H) :=
      AlgBFEvenCondData.infinite_pSocleAt_of_longWindow
        p hH hlong.2 hbase hcap
    have hroomG : roomInvariant p F β = Cardinal.aleph0 :=
      roomInvariant_eq_aleph0_of_infinite p F hFfinite β hGinf
    have hroomH : roomInvariant p E β = Cardinal.aleph0 :=
      roomInvariant_eq_aleph0_of_infinite p E hEfinite β hHinf
    have hkerfin : jumpKernelInvariant p φ hsucc hβfloor < Cardinal.aleph0 :=
      jumpKernelInvariant_lt_aleph0_of_finite_source
        p hFfinite φ hsucc hβfloor
    change roomInvariant p F β + jumpKernelInvariant p φ hsucc hβfloor ≤
      roomInvariant p E β
    rw [hroomG, hroomH]
    exact Cardinal.add_le_aleph0.2 ⟨le_rfl, hkerfin.le⟩

/-- The complete map-sensitive odd response data now follows without an
additional response hypothesis. -/
theorem exists_evenFiniteTupleOddMapData_of_context
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β ≤
        roomInvariant p (tupleSubgroup b) β)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleOddMapData p hG hH C c) := by
  obtain ⟨R⟩ := exists_evenFiniteTupleOddCoreData p hG hH C c
  exact ⟨{
    response := R.response
    iso := R.iso
    heights := R.heights
    short_presBelowCap := R.short_presBelowCap
    kernel_room := R.kernel_room_of_countable p hG hH hroom }⟩

/-- Compatibility wrapper for the established crossed even package. -/
theorem exists_evenFiniteTupleOddMapData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleOddMapData p hG hH
      (EvenHighCountdown.Context.ofStrong p hG hH C) c) := by
  let exact := C.toExactData p hG hH
  exact exists_evenFiniteTupleOddMapData_of_context p hG hH
    (EvenHighCountdown.Context.ofStrong p hG hH C)
    exact.window.room_reverse c

/-- Once the map-sensitive response fields are built, current even data supplies
the unchanged ambient fields and packages the complete enlarged odd data. -/
noncomputable def EvenFiniteTupleOddMapData.toOddData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : EvenHighCountdown.Context p hG hH α a b}
    {m : ℕ} {c : Fin m → H}
    (R : EvenFiniteTupleOddMapData p hG hH C c) :
    AlgBFOddCondData p hH hG α
      (Fin.append b c) (Fin.append a R.response) := by
  exact {
    iso := R.iso
    lengths := by
      rcases C.lengths with hshort | hlong
      · rcases lt_or_ge (ulmLength p (G := H) hH : Ordinal.{0}) (ω * α) with hlt | hge
        · exact Or.inl ⟨hshort.1.symm, hlt⟩
        · exact Or.inr ⟨by simpa [hshort.1] using hge, by
            rw [← hshort.1]
            exact min_le_left _ _⟩
      · exact Or.inr ⟨le_self_add.trans hlong.1,
          (min_le_right _ _).trans hlong.2⟩
    ulm_below := fun β hβ ↦ (C.ulm_below β hβ).symm
    heights := R.heights
    kernel_room := R.kernel_room }

/-- The exact finite-tuple algebraic response required for even sufficiency.

The outer challenge lies in `H`, while the predecessor relation is oriented
from `H` back to `G`; consequently the enlarged odd data has ambient groups and
tuples swapped. -/
def EvenFiniteTupleOddResponses
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  ∀ (m : ℕ) (c : Fin m → H), ∃ d : Fin m → G,
    AlgBFOddCond p hH hG α (Fin.append b c) (Fin.append a d)

/-- Constructing the map-sensitive response data for every challenge is enough
for the exact proposition-level response seam. -/
theorem evenFiniteTupleOddResponses_of_mapData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    (hmap : ∀ (m : ℕ) (c : Fin m → H),
      Nonempty (EvenFiniteTupleOddMapData p hG hH C c)) :
    EvenFiniteTupleOddResponses p hG hH α a b := by
  intro m c
  obtain ⟨R⟩ := hmap m c
  exact ⟨R.response, ⟨R.toOddData p hG hH⟩⟩

/-- Every current even package has the exact enlarged odd response required by
the successor definition. -/
theorem evenFiniteTupleOddResponses_of_context
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : EvenHighCountdown.Context p hG hH α a b)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β ≤
        roomInvariant p (tupleSubgroup b) β) :
    EvenFiniteTupleOddResponses p hG hH α a b :=
  evenFiniteTupleOddResponses_of_mapData p hG hH C
    (fun _m c ↦ exists_evenFiniteTupleOddMapData_of_context
      p hG hH C hroom c)

/-- The established crossed even package has every finite odd response. -/
theorem evenFiniteTupleOddResponses
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    EvenFiniteTupleOddResponses p hG hH α a b := by
  let exact := C.toExactData p hG hH
  exact evenFiniteTupleOddResponses_of_context p hG hH
    (EvenHighCountdown.Context.ofStrong p hG hH C)
    exact.window.room_reverse

/-- The exact Hill--room even package has every finite odd response. -/
theorem evenFiniteTupleOddResponses_of_exactData
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b) :
    EvenFiniteTupleOddResponses p hG hH α a b :=
  evenFiniteTupleOddResponses_of_context p hG hH
    (EvenHighCountdown.Context.ofExact p hG hH C)
    C.window.room_reverse

/-- The even successor relation follows from the exact algebraic response seam
and the odd sufficiency direction at the predecessor level.

This theorem performs only ordinal, finite-tuple, and orientation
bookkeeping.  It assumes neither global biconditional. -/
theorem bf_even_of_evenFiniteTupleOddResponses_of_oddSufficiency
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (hresponse : EvenFiniteTupleOddResponses p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v →
        BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b := by
  rw [show 2 * α + 2 = Order.succ (2 * α + 1) by
    rw [Order.succ_eq_add_one, ← one_add_one_eq_two, ← add_assoc],
    BFRel_succ]
  intro m c
  obtain ⟨d, hdata⟩ := hresponse m c
  refine ⟨d, ?_⟩
  rw [BFRelReverse_iff_BFRel_swap]
  exact hOdd (Fin.append b c) (Fin.append a d) hdata

/-- The even sufficiency step is now fully reduced to the predecessor odd
sufficiency theorem; all finite response algebra is discharged internally. -/
theorem bf_even_of_evenData_of_oddSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v →
        BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b :=
  bf_even_of_evenFiniteTupleOddResponses_of_oddSufficiency
    p hG hH (evenFiniteTupleOddResponses p hG hH C) hOdd

/-- Exact Hill--room even data implies the successor relation once odd
sufficiency is known at the predecessor level. -/
theorem bf_even_of_exactEvenData_of_oddSufficiency
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v →
        BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b :=
  bf_even_of_evenFiniteTupleOddResponses_of_oddSufficiency
    p hG hH (evenFiniteTupleOddResponses_of_exactData p hG hH C) hOdd

end AlgebraicBFConditions
