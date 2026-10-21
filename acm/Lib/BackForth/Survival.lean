import Lib.BackForth.InducedMap

/-!
# The extension stage and the survival lemma

This file states the finite-core obligation that odd sufficiency rests on, so
that it is a single named `Prop` and everything else can be proved around it.

The former construction attempted to build a chain of isomorphisms
`g_i : B_i → A_i` one source socle line at a time, maintaining the four invariants
in `Stage`.  `OneLineSurvival` names the required one-line assertion.  D-20 records
that this assertion is **false** for the current stage predicate; the definition is
retained so the failed route remains explicit and downstream implications can still
be stated conditionally.

## Why the invariants are shaped this way

`(I2)` is a genuine **height floor** `h(g z) ≥ h(z)`, not the two-sided height
condition of the `≤_{2α}` clause.  The floor is what makes `jumpMap` well defined
at every level, which is what lets `(I4)` be stated at all.  At `α = 0` the
two-sided condition degenerates to something vacuous, so the floor is the only
usable form.

`(I3)` retains unused target socle room for later unanchored demands, and `(I4)`
retains the high-root classes for later anchored ones.  Neither alone suffices:
the ledger records a legal move that is nevertheless unsafe because it hands an
existing anchor a high target root and kills an old jump class.  That is why
`(I4)` is quantified over the whole window and not only over levels newly
exhausted by the move.

## Main definitions

- `Stage`           : the invariants (I1)-(I4) at one stage
- `Stage.Extends`   : one stage extends another
- `OneLineSurvival` : **the refuted one-line statement**
- `SocleCaptured`   : Phase I's goal, the whole source socle inside the domain
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace Survival

/-- The window `[ω·α, ω·α+ω)` the odd clauses are measured on. -/
def InWindow (α β : Ordinal.{0}) : Prop :=
  ω * α ≤ β ∧ β < ω * α + ω

/-- A stage of the extension construction: a partial isomorphism from `B` to `A`
carrying the four invariants (I1)-(I4). -/
structure Stage (α : Ordinal.{0}) where
  /-- (I1) the current source subgroup. -/
  src : AddSubgroup B
  /-- (I1) the current target subgroup. -/
  tgt : AddSubgroup A
  /-- (I1) the current partial isomorphism. -/
  iso : src ≃+ tgt
  /-- (I2) the height floor `h(g z) ≥ h(z)`. -/
  floor : IsHeightFloorOn p (iso.toAddMonoidHom)
  /-- (I3) remaining-room domination across the window. -/
  room_dom : ∀ β : Ordinal.{0}, InWindow α β →
    roomInvariant p src β ≤ roomInvariant p tgt β
  /-- (I4) guarded jump-map injectivity.  This must hold at levels exhausted
  *before* the current move as well as at newly exhausted ones. -/
  jump_inj : ∀ β : Ordinal.{0}, InWindow α β →
    roomInvariant p tgt β = 0 →
    Function.Injective (jumpMap p (iso.toAddMonoidHom)
      (floor (Order.succ β)) (floor β))

/-- One stage extends another when its source contains the earlier source and its
isomorphism agrees with the earlier one there. -/
def Stage.Extends {α : Ordinal.{0}} (S T : Stage p (A := A) (B := B) α) : Prop :=
  ∃ hsrc : S.src ≤ T.src,
    ∀ x : S.src, (T.iso ⟨(x : B), hsrc x.2⟩ : A) = (S.iso x : A)

lemma Stage.Extends.rfl' {α : Ordinal.{0}} (S : Stage p (A := A) (B := B) α) :
    Stage.Extends p S S :=
  ⟨le_rfl, fun _ => by simp⟩

/-! ### The refuted one-line statement -/

/-- **The former survival lemma (false).**

From any stage whose source socle is not yet inside the domain, there is an
extension of that stage capturing at least one more socle element.

The 64-element activation counterexample in D-20 is a stage with source socle
remaining and no preserving one-line extension for its top source line.  Both legal
responses are proper, but each uses the last target room line and thereby activates
an old unguarded kernel. -/
def OneLineSurvival (α : Ordinal.{0}) : Prop :=
  ∀ (S : Stage p (A := A) (B := B) α) (x : B),
    x ∈ pSocle p (G := B) → x ∉ S.src →
      ∃ T : Stage p (A := A) (B := B) α, Stage.Extends p S T ∧ x ∈ T.src

/-- Phase I's goal: the whole source socle lies inside the domain. -/
def SocleCaptured {α : Ordinal.{0}} (S : Stage p (A := A) (B := B) α) : Prop :=
  pSocle p (G := B) ≤ S.src

/-- A stage already containing every socle element has captured the socle. -/
lemma socleCaptured_of_forall {α : Ordinal.{0}} (S : Stage p (A := A) (B := B) α)
    (h : ∀ x : B, x ∈ pSocle p (G := B) → x ∈ S.src) :
    SocleCaptured p S := h



/-! ### Survival implies Phase I

The point of isolating `OneLineSurvival` is that everything downstream of it is
ordinary finite bookkeeping.  Here is that bookkeeping: in the finite core, one
application of survival per uncaptured socle element drives Phase I to
completion. -/

lemma Stage.Extends.trans {α : Ordinal.{0}} {S T U : Stage p (A := A) (B := B) α}
    (hST : Stage.Extends p S T) (hTU : Stage.Extends p T U) :
    Stage.Extends p S U := by
  obtain ⟨h1, e1⟩ := hST
  obtain ⟨h2, e2⟩ := hTU
  refine ⟨le_trans h1 h2, fun x => ?_⟩
  have := e2 ⟨(x : B), h1 x.2⟩
  rw [← e1 x, ← this]

variable [Fintype B] [DecidableEq B]

open scoped Classical in
/-- The socle elements not yet inside the domain. -/
private noncomputable def uncaptured {α : Ordinal.{0}}
    (S : Stage p (A := A) (B := B) α) : Finset B :=
  Finset.univ.filter (fun x : B => x ∈ pSocle p (G := B) ∧ x ∉ S.src)

open scoped Classical in
private lemma uncaptured_empty_iff {α : Ordinal.{0}}
    (S : Stage p (A := A) (B := B) α) :
    uncaptured p S = ∅ ↔ SocleCaptured p S := by
  constructor
  · intro h x hx
    by_contra hxs
    have : x ∈ uncaptured p S := by
      simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx, hxs⟩
    rw [h] at this
    simp at this
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.2 (h hx.1)

open scoped Classical in
/-- **Survival drives Phase I to completion.**

Given the survival lemma, every stage extends to one whose domain contains the
entire source socle.  The induction is on the number of uncaptured socle
elements, which strictly drops at each step because the captured element `x` was
outside the old domain and is inside the new one.

So the *whole* of Phase I reduces to `OneLineSurvival`; nothing else is owed. -/
theorem socleCaptured_of_survival {α : Ordinal.{0}}
    (hsurv : OneLineSurvival p (A := A) (B := B) α) :
    ∀ (S : Stage p (A := A) (B := B) α),
      ∃ T : Stage p (A := A) (B := B) α,
        Stage.Extends p S T ∧ SocleCaptured p T := by
  have key : ∀ (n : ℕ) (S : Stage p (A := A) (B := B) α),
      (uncaptured p S).card ≤ n →
      ∃ T : Stage p (A := A) (B := B) α,
        Stage.Extends p S T ∧ SocleCaptured p T := by
    intro n
    induction n with
    | zero =>
        intro S hcard
        refine ⟨S, Stage.Extends.rfl' p S, ?_⟩
        rw [← uncaptured_empty_iff]
        exact Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    | succ n ih =>
        intro S hcard
        by_cases hall : SocleCaptured p S
        · exact ⟨S, Stage.Extends.rfl' p S, hall⟩
        · -- some socle element is still outside the domain
          have hne : uncaptured p S ≠ ∅ := fun h =>
            hall ((uncaptured_empty_iff p S).mp h)
          obtain ⟨x, hxmem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and] at hxmem
          obtain ⟨T, hST, hxT⟩ := hsurv S x hxmem.1 hxmem.2
          obtain ⟨hsrc, _⟩ := id hST
          -- the uncaptured set strictly shrinks: it loses `x` and gains nothing
          have hsub : uncaptured p T ⊆ (uncaptured p S).erase x := by
            intro y hy
            simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and] at hy
            refine Finset.mem_erase.mpr ⟨fun h => hy.2 (h ▸ hxT), ?_⟩
            simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hy.1, fun hmem => hy.2 (hsrc hmem)⟩
          have hlt : (uncaptured p T).card ≤ n := by
            have h1 := Finset.card_le_card hsub
            have h2 : ((uncaptured p S).erase x).card = (uncaptured p S).card - 1 :=
              Finset.card_erase_of_mem (by
                simp only [uncaptured, Finset.mem_filter, Finset.mem_univ, true_and]
                exact hxmem)
            omega
          obtain ⟨U, hTU, hU⟩ := ih T hlt
          exact ⟨U, Stage.Extends.trans p hST hTU, hU⟩
  intro S
  exact key (uncaptured p S).card S le_rfl


/-! ### The existence half of a survival step

A legal *response* always exists.  This is the part of the survival lemma that
(I3) already pays for, and isolating it narrows the open statement to the
preservation obligations.

If a source socle element of height at least `β` sits outside the domain, then
the source room at `β` is nonzero; (I3) transports that to the target room, and a
nonzero target room is exactly a target socle element of height at least `β`
outside the image.  So `(O1)` — a fresh, high-enough response — is never the
obstruction. -/

/-- Nonzero room is exactly a socle element of the right height outside the
subgroup. -/
lemma roomInvariant_ne_zero_iff {G : Type u} [AddCommGroup G]
    (E : AddSubgroup G) (β : Ordinal.{0}) :
    roomInvariant p E β ≠ 0 ↔ ¬ (pSocleAt p β (G := G) ≤ E) := by
  rw [← room_nontrivial_iff]
  constructor
  · intro h
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact h (rank_zero_iff.mpr hcon)
  · intro h
    intro hz
    exact absurd (rank_zero_iff.mp hz) (not_subsingleton_iff_nontrivial.mpr h)

/-- **The response always exists.**  Given a stage and a source socle element of
height at least `β` outside the domain, there is a target socle element of height
at least `β` outside the image.

This is `(O1)`, and it costs nothing beyond `(I3)`.  What the survival lemma
still owes is that some such response also preserves `(I3)` and `(I4)`. -/
theorem exists_response {α : Ordinal.{0}} (S : Stage p (A := A) (B := B) α)
    (β : Ordinal.{0}) (hw : InWindow α β)
    (x : B) (hx : x ∈ pSocleAt p β (G := B)) (hxn : x ∉ S.src) :
    ∃ w : A, w ∈ pSocleAt p β (G := A) ∧ w ∉ S.tgt := by
  have hsrc : ¬ (pSocleAt p β (G := B) ≤ S.src) := fun h => hxn (h hx)
  have h1 : roomInvariant p S.src β ≠ 0 :=
    (roomInvariant_ne_zero_iff p S.src β).mpr hsrc
  have h2 : roomInvariant p S.tgt β ≠ 0 := by
    intro hz
    exact h1 (le_antisymm (hz ▸ S.room_dom β hw) (zero_le _))
  have := (roomInvariant_ne_zero_iff p S.tgt β).mp h2
  rw [SetLike.not_le_iff_exists] at this
  obtain ⟨w, hw1, hw2⟩ := this
  exact ⟨w, hw1, hw2⟩


/-! ### (O2): the whole line is height-legal

Given a **proper** socle challenge `x` and any response `w` that is fresh and high
enough, the extended map respects the height floor on the *entire* new line
`b + r·x`, not merely on the old domain and the new generator separately.

This is the second of the three one-line obligations, and properness is exactly
what pays for it: `x` having maximal height in its coset caps `h(b + r·x)` at
`h(x)`, so the only levels that need checking are those the response already
reaches. -/

/-- **(O2), height legality of the whole new line.**

If `x` is a socle element of height at least `β`, proper with respect to the
current domain, and `w` is a socle element of height at least `β`, then the
extension sending `b + r·x` to `g b + r·w` respects the height floor everywhere.

The two cases are: at levels `γ ≤ β` the response is high enough on its own and
`(I2)` covers `b`; at levels `γ > β` properness makes the hypothesis unsatisfiable
whenever `r` contributes, so there is nothing to check. -/
theorem line_height_legal {α : Ordinal.{0}} (S : Stage p (A := A) (B := B) α)
    (hprimB : IsPrimaryPGroup p B)
    {β : Ordinal.{0}} {x : B}
    (hxsoc : p • x = 0)
    (hxβ : x ∈ ulmSubgroup p β (G := B))
    (hxprop : ∀ s ∈ S.src, x + s ∉ ulmSubgroup p (Order.succ β) (G := B))
    {w : A} (hwsoc : p • w = 0) (hwβ : w ∈ ulmSubgroup p β (G := A))
    (b : S.src) (r : ℤ) (γ : Ordinal.{0})
    (hmem : (b : B) + r • x ∈ ulmSubgroup p γ (G := B)) :
    (S.iso b : A) + r • w ∈ ulmSubgroup p γ (G := A) := by
  by_cases hdvd : (p : ℤ) ∣ r
  · -- `r` kills both socle elements, so this is just `(I2)`
    obtain ⟨m, rfl⟩ := hdvd
    have hzB : (p * m : ℤ) • x = 0 := by
      rw [mul_comm, mul_zsmul]
      simp [show ((p : ℤ)) • x = (p : ℕ) • x from (natCast_zsmul _ _), hxsoc]
    have hzA : (p * m : ℤ) • w = 0 := by
      rw [mul_comm, mul_zsmul]
      have : ((p : ℤ)) • w = (p : ℕ) • w := natCast_zsmul _ _
      rw [this]
      simp [hwsoc]
    rw [hzA, add_zero]
    rw [hzB, add_zero] at hmem
    exact S.floor γ b hmem
  · by_cases hγ : γ ≤ β
    · -- low levels: the response is already high enough, and `(I2)` covers `b`
      have hrx : r • x ∈ ulmSubgroup p γ (G := B) :=
        (ulmSubgroup p γ).zsmul_mem (ulmSubgroup_antitone p hγ hxβ) r
      have hb : (b : B) ∈ ulmSubgroup p γ (G := B) := by
        have := (ulmSubgroup p γ).sub_mem hmem hrx
        simpa using this
      exact (ulmSubgroup p γ).add_mem (S.floor γ b hb)
        ((ulmSubgroup p γ).zsmul_mem (ulmSubgroup_antitone p hγ hwβ) r)
    · -- high levels: properness makes the hypothesis impossible
      exfalso
      push_neg at hγ
      have hsucc : Order.succ β ≤ γ := Order.succ_le_of_lt hγ
      have hmem' : (b : B) + r • x ∈ ulmSubgroup p (Order.succ β) (G := B) :=
        ulmSubgroup_antitone p hsucc hmem
      -- rescale by the inverse of `r` to land on `x + s`
      obtain ⟨a, c, hac⟩ : IsCoprime (r : ℤ) (p : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        show r.natAbs.gcd p = 1
        rw [Nat.gcd_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
          (fun h => hdvd (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
      have hax : a • (r • x) = x := by
        have : (a * r) • x = x := by
          have h1 : (a * r + c * (p : ℤ)) • x = x := by rw [hac, one_zsmul]
          rw [add_zsmul, mul_zsmul, mul_zsmul] at h1
          have hpx : ((p : ℤ)) • x = 0 := by
            rw [natCast_zsmul]; exact hxsoc
          rw [hpx, smul_zero, add_zero] at h1
          rw [mul_zsmul]; exact h1
        rw [mul_zsmul] at this; exact this
      have := (ulmSubgroup p (Order.succ β)).zsmul_mem hmem' a
      rw [zsmul_add, hax] at this
      exact hxprop (a • (b : B)) ((S.src).zsmul_mem b.2 a) (by
        rw [add_comm] at this; exact this)

/-! ### (O3): a proper response stabilizes the jump map

Adjoining a proper socle element changes neither the numerator nor the denominator
of the jump space at any level, so the underlying jump map is unchanged.  This does
**not** imply that `(I4)` transfers: the response may change target room from one to
zero and activate the guard on an old noninjective map.  The D-20 counterexample has
two proper legal responses and both fail by exactly this activation mechanism. -/

/-- Adjoining a socle element does not change the jump-space numerator: it
contributes nothing to `pE`, because `p • w = 0`. -/
theorem jumpNum_sup_zmultiples {G : Type u} [AddCommGroup G]
    (E : AddSubgroup G) {w : G} (hwsoc : p • w = 0) (γ : Ordinal.{0}) :
    jumpNum p (E ⊔ AddSubgroup.zmultiples w) γ = jumpNum p E γ := by
  unfold jumpNum
  congr 1
  ext y
  simp only [mem_pImage]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [AddSubgroup.mem_sup] at hu
    obtain ⟨e, he, z, ⟨r, rfl⟩, rfl⟩ := hu
    simp only []
    refine ⟨e, he, ?_⟩
    rw [smul_add, show p • (r • w) = r • (p • w) by rw [smul_comm], hwsoc, smul_zero,
      add_zero]
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, AddSubgroup.mem_sup_left he, rfl⟩

/-- Adjoining a **proper** socle element does not change the jump-space
denominator either.

At levels `γ ≤ β` the new generator is already high enough, so the intersection
grows only by `⟨w⟩`, which `p` kills.  At levels `γ > β` properness makes the
intersection not grow at all: rescaling by the inverse of `r` turns `e + r·w`
into `w + e'` with `e'` in `E`, which properness keeps out of `G_{β+1}`. -/
theorem jumpDen_sup_zmultiples {G : Type u} [AddCommGroup G]
    (hprim : IsPrimaryPGroup p G)
    (E : AddSubgroup G) {w : G} {β : Ordinal.{0}}
    (hwsoc : p • w = 0) (hwβ : w ∈ ulmSubgroup p β (G := G))
    (hwprop : ∀ e ∈ E, w + e ∉ ulmSubgroup p (Order.succ β) (G := G))
    (γ : Ordinal.{0}) :
    jumpDen p (E ⊔ AddSubgroup.zmultiples w) γ = jumpDen p E γ := by
  apply le_antisymm
  · rintro y ⟨u, ⟨hu, huγ⟩, rfl⟩
    have hu2 : u ∈ E ⊔ AddSubgroup.zmultiples w := hu
    rw [AddSubgroup.mem_sup] at hu2
    obtain ⟨e, he, z, ⟨r, rfl⟩, rfl⟩ := hu2
    simp only [] at huγ ⊢
    -- the `w` part is killed by `p`, so it suffices that `e` is high enough
    have hpe : p • (e + r • w) = p • e := by
      rw [smul_add, show p • (r • w) = r • (p • w) by rw [smul_comm], hwsoc,
        smul_zero, add_zero]
    rw [hpe]
    refine ⟨e, ⟨he, ?_⟩, rfl⟩
    by_cases hdvd : (p : ℤ) ∣ r
    · obtain ⟨m, rfl⟩ := hdvd
      have hz : (p * m : ℤ) • w = 0 := by
        rw [mul_comm, mul_zsmul, natCast_zsmul, hwsoc, zsmul_zero]
      rw [hz, add_zero] at huγ
      exact huγ
    · by_cases hγ : γ ≤ β
      · have hrw : r • w ∈ ulmSubgroup p γ (G := G) :=
          (ulmSubgroup p γ).zsmul_mem (ulmSubgroup_antitone p hγ hwβ) r
        simpa using (ulmSubgroup p γ).sub_mem huγ hrw
      · exfalso
        push_neg at hγ
        have hmem' : e + r • w ∈ ulmSubgroup p (Order.succ β) (G := G) :=
          ulmSubgroup_antitone p (Order.succ_le_of_lt hγ) huγ
        obtain ⟨a, c, hac⟩ : IsCoprime (r : ℤ) (p : ℤ) := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          show r.natAbs.gcd p = 1
          rw [Nat.gcd_comm]
          exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
            (fun h => hdvd (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
        have haw : a • (r • w) = w := by
          have h1 : (a * r + c * (p : ℤ)) • w = w := by rw [hac, one_zsmul]
          rw [add_zsmul, mul_zsmul, mul_zsmul,
            show ((p : ℤ)) • w = (0 : G) by rw [natCast_zsmul, hwsoc],
            smul_zero, add_zero] at h1
          exact h1
        have := (ulmSubgroup p (Order.succ β)).zsmul_mem hmem' a
        rw [zsmul_add, haw] at this
        exact hwprop (a • e) (E.zsmul_mem he a) (by rw [add_comm] at this; exact this)
  · rintro y ⟨u, ⟨hu, huγ⟩, rfl⟩
    exact ⟨u, ⟨AddSubgroup.mem_sup_left hu, huγ⟩, rfl⟩

/-- **(O3) for proper responses.** Adjoining a proper socle element leaves the
jump space unchanged at every level, numerator and denominator alike. This is a
denominator-stability result only; guarded safety additionally requires the old map
to be injective at every level newly exhausted by the response. -/
theorem jumpSpace_unchanged_of_proper {G : Type u} [AddCommGroup G]
    (hprim : IsPrimaryPGroup p G)
    (E : AddSubgroup G) {w : G} {β : Ordinal.{0}}
    (hwsoc : p • w = 0) (hwβ : w ∈ ulmSubgroup p β (G := G))
    (hwprop : ∀ e ∈ E, w + e ∉ ulmSubgroup p (Order.succ β) (G := G))
    (γ : Ordinal.{0}) :
    jumpNum p (E ⊔ AddSubgroup.zmultiples w) γ = jumpNum p E γ ∧
      jumpDen p (E ⊔ AddSubgroup.zmultiples w) γ = jumpDen p E γ :=
  ⟨jumpNum_sup_zmultiples p E hwsoc γ,
   jumpDen_sup_zmultiples p hprim E hwsoc hwβ hwprop γ⟩

/-! ### (C): the improper-challenge mechanism, corrected

`jumpSpace_unchanged_of_proper` handles a **proper** response by leaving the
target jump space alone.  The other escape route was supposed to be an **improper
challenge**, collapsing the *source* jump space instead, after which
`jumpMap_injective_of_source_subsingleton` gives (I4) for free.

**That collapse does not happen.**  The previous form of this statement — same
hypotheses, conclusion `Subsingleton (jumpSpace p (E ⊔ zmultiples x) γ)` for
every `γ` — is false.  Exhaustive over every `p = 2` type of total exponent `≤ 8`
with `E = ⟨P_{β+1}, at most two further generators⟩`, the refutations are 6 and
all of one type:

    G = Z/2 ⊕ Z/2 ⊕ Z/8 ⊕ Z/8,  β = 0,  x = (1,0,0,0),
    E = ⟨(1,0,2,0), (0,1,0,2), (0,0,4,0), (0,0,0,4)⟩   (order 16)

Every hypothesis holds and `dim S_{G,E}(1) = 2`, `dim S_{G,E'}(1) = 1`, not `0`.

What is true is a **dimension formula**, proved in `knowledge/engine/jump_transfer.py`
and recorded in `knowledge/STATE.md`.  Writing `P` for the socle, `Q = P ∩ (E+G_γ)`
and `D = P ∩ E`:

* (L1) if `P_γ ⊆ E` then `S_{G,E}(γ) ≅ Q / D`, by `[p·e] ↦ [e − v]` for any root
  `v ∈ G_γ` of `p·e`;
* (T1) if `γ ≤ h(x)` then numerator and denominator are literally unchanged;
* (T2) if `P_γ ⊆ E` and `x ∈ E + G_γ` then `dim S_{G,E'}(γ) = dim S_{G,E}(γ) − 1`;
* (T3) if `P_γ ⊆ E` and `x ∉ E + G_γ` then the dimension is unchanged.

So an improper challenge removes **exactly one** dimension, never more.  Hence the
collapse holds iff `dim S_{G,E}(β+1) ≤ 1`, which is the hypothesis added below.

Two further corrections carried by that hypothesis set:

* The old `∀ γ` was too strong for the application.  At `γ ≤ β` nothing changes at
  all, by (T1); and the levels that matter are those where the *target* is
  exhausted, where room domination (I3) forces `P^B_γ ⊆ B_i` and so `γ > β`.  The
  quantifier is therefore restricted to `γ` with `P_γ ⊆ E`.
* The top-live-level hypothesis stays **essential**: without it the statement fails
  even in the one-dimensional regime — among 908 triples `(G, E, x)` with `E`
  two-generated and `x` an improper socle element, 4 are counterexamples, the first
  being `G = Z/2 ⊕ Z/4 ⊕ Z/16`, `E = {(0,0,0), (0,0,8), (1,0,4), (1,0,12)}`,
  `x = (1,2,0)`, failing at `γ = 2`.  With it, 252 triples and no failure.

Why the corpus evidence never saw this.  Breaking (C) needs BOTH a marked tuple of
length `≥ 2` and a source group of total exponent `≥ 8`, and no searched scope has
both.  Length is needed because `dim S_{G,E}(γ) ≤ rank (pE)`: the numerator is a
subgroup of `pE` and the quotient is killed by `p`, and adjoining socle lines does not
change `pE`, so `rank (pE_i)` stays bounded by the tuple length throughout Phase I.  At
`ngens = 1` that bound reads `dim ≤ 1` and the rank hypothesis below is automatic, so
(C) is a **theorem for one-generator marked tuples**.  The binding constraint, though,
is group size: the scopes are `maxtot=6 maxk=3 ngens=1`, `maxtot=5 maxk=2 ngens=1` and
`maxtot=4 maxk=2 ngens=2` — the two-generator scope exists but stops at total exponent
4, and an independent sweep of every `p = 2` type of total exponent `≤ 6` found no
counterexample.

**D-20 correction.** Survival is false under the current `Stage` predicate.  The
matching argument above controls one class lost by the source; it does not remove an
old unguarded kernel when the response newly exhausts the target level.  In the
64-element activation counterexample, the old map at level one is noninjective and
unguarded, and every legal response activates its guard.  The proposition below is a
true rank-bounded source statement, but it does not imply one-line survival. -/
def ImproperChallengeCollapses (G : Type u) [AddCommGroup G] : Prop :=
  ∀ (E : AddSubgroup G) (x : G) (β : Ordinal.{0}),
    p • x = 0 →
    x ∈ ulmSubgroup p β (G := G) →
    x ∉ E →
    (∃ e ∈ E, x + e ∈ ulmSubgroup p (Order.succ β) (G := G)) →   -- `x` is improper
    (∀ γ : Ordinal.{0}, β < γ → pSocleAt p γ (G := G) ≤ E) →      -- `β` is the top live level
    Module.rank (ZMod p) (jumpSpace p E (Order.succ β)) ≤ 1 →     -- **required**: see above
    ∀ γ : Ordinal.{0}, pSocleAt p γ (G := G) ≤ E →                -- the levels that matter
      Subsingleton (jumpSpace p (E ⊔ AddSubgroup.zmultiples x) γ)

/-- **An improperness witness is never a socle element.**

If `x` is a socle element at the top live level and `b ∈ E` lifts it — `x + b`
has height above `β` — then `p • b ≠ 0`.

Otherwise `x + b` would itself be a socle element of height above `β`, hence in
`P_{β+1} ⊆ E` by the top-live-level hypothesis, forcing `x = (x + b) - b ∈ E`
and contradicting the choice of `x`.

This is why the improper case cannot be waved away: the element that spoils
properness necessarily has `p·b ≠ 0`, so it contributes to `pE` and moves the
jump-space denominator.  It is also what makes `x + b` a genuine *root* of `p·b`
lying above `β`. -/
theorem improperness_witness_not_socle {G : Type u} [AddCommGroup G]
    (E : AddSubgroup G) {x : G} {β : Ordinal.{0}}
    (hxsoc : p • x = 0)
    (hxnot : x ∉ E)
    (htop : ∀ γ : Ordinal.{0}, β < γ → pSocleAt p γ (G := G) ≤ E)
    {b : G} (hb : b ∈ E)
    (hlift : x + b ∈ ulmSubgroup p (Order.succ β) (G := G)) :
    p • b ≠ 0 := by
  intro hbsoc
  have hsoc : p • (x + b) = 0 := by rw [smul_add, hxsoc, hbsoc, add_zero]
  have hmem : x + b ∈ pSocleAt p (Order.succ β) (G := G) := ⟨hsoc, hlift⟩
  have : x + b ∈ E := htop (Order.succ β) (Order.lt_succ β) hmem
  exact hxnot (by simpa using E.sub_mem this hb)

end Survival
