import Lib.BackForth.JumpSpace
import Lib.BackForth.MarkedCorrection
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The one-step filtration of room

For a marked subgroup `E ≤ G`, room at height `β` has a canonical next-height
subspace.  Its quotient is the marked-graded layer at `β`:

`0 → R_{G,E}(β+1) → R_{G,E}(β) → V_{G,E}(β) → 0`.

This file constructs the two maps, identifies image with kernel, and records
the resulting cardinal rank equation.  Iteration across a finite tail and the
countable long-tail argument are kept separate from this local exact sequence.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [AddCommGroup G]

/-- Inclusion of a later filtered socle into an earlier one. -/
noncomputable def pSocleRestriction {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    pSocleAt p γ (G := G) →ₗ[ZMod p] pSocleAt p β (G := G) :=
  ({
    toFun := fun x => ⟨(x : G), pSocleAt_antitone p hβγ x.property⟩
    map_zero' := Subtype.ext rfl
    map_add' := fun _ _ => Subtype.ext rfl
  } : pSocleAt p γ (G := G) →+ pSocleAt p β (G := G)).toZModLinearMap p

/-- The room denominator is respected by filtered-socle restriction. -/
lemma roomSubmodule_maps_restriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    roomSubmodule p E γ ≤
      (roomSubmodule p E β).comap (pSocleRestriction p hβγ) := by
  intro x hx
  exact ⟨hx.1, pSocleAt_antitone p hβγ x.property⟩

/-- A later room maps canonically into every earlier room. -/
noncomputable def roomRestriction (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    room p E γ →ₗ[ZMod p] room p E β :=
  (roomSubmodule p E γ).mapQ (roomSubmodule p E β)
    (pSocleRestriction p hβγ)
    (roomSubmodule_maps_restriction p E hβγ)

@[simp] theorem roomRestriction_mk (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (x : pSocleAt p γ (G := G)) :
    roomRestriction p E hβγ ((roomSubmodule p E γ).mkQ x) =
      (roomSubmodule p E β).mkQ (pSocleRestriction p hβγ x) :=
  Submodule.mapQ_apply _ _ _ x

/-- Restriction does not collapse a later room class: its representative is
already in the later socle, so membership in the earlier mark denominator is
the same membership in the later denominator. -/
theorem roomRestriction_injective (E : AddSubgroup G)
    {β γ : Ordinal.{0}} (hβγ : β ≤ γ) :
    Function.Injective (roomRestriction p E hβγ) := by
  intro q₁ q₂ hq
  obtain ⟨x, rfl⟩ := (roomSubmodule p E γ).mkQ_surjective q₁
  obtain ⟨y, rfl⟩ := (roomSubmodule p E γ).mkQ_surjective q₂
  rw [roomRestriction_mk, roomRestriction_mk] at hq
  apply (Submodule.Quotient.eq _).mpr
  have hdiff := (Submodule.Quotient.eq _).mp hq
  exact ⟨hdiff.1, (pSocleAt p γ).sub_mem x.property y.property⟩

/-- The room denominator is contained in the marked-graded denominator. -/
lemma roomSubmodule_le_markedGradedSubmodule (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    roomSubmodule p E β ≤ markedGradedSubmodule p E β := by
  intro x hx
  change (x : G) ∈ pSocleAt p (Order.succ β) ⊔
    (E ⊓ pSocleAt p β)
  exact AddSubgroup.mem_sup_right ⟨hx.1, x.property⟩

/-- Forgetting every class surviving to `β+1` projects room onto the
marked-graded layer at `β`. -/
noncomputable def roomToMarkedGraded (E : AddSubgroup G) (β : Ordinal.{0}) :
    room p E β →ₗ[ZMod p] markedGradedQuotient p E β :=
  (roomSubmodule p E β).mapQ (markedGradedSubmodule p E β)
    LinearMap.id (roomSubmodule_le_markedGradedSubmodule p E β)

@[simp] theorem roomToMarkedGraded_mk (E : AddSubgroup G)
    (β : Ordinal.{0}) (x : pSocleAt p β (G := G)) :
    roomToMarkedGraded p E β ((roomSubmodule p E β).mkQ x) =
      (markedGradedSubmodule p E β).mkQ x :=
  Submodule.mapQ_apply _ _ _ x

theorem roomToMarkedGraded_surjective (E : AddSubgroup G) (β : Ordinal.{0}) :
    Function.Surjective (roomToMarkedGraded p E β) := by
  intro q
  obtain ⟨x, rfl⟩ := (markedGradedSubmodule p E β).mkQ_surjective q
  exact ⟨(roomSubmodule p E β).mkQ x, roomToMarkedGraded_mk p E β x⟩

/-- The next-height room is exactly the kernel of the projection to the local
marked-graded layer. -/
theorem range_roomRestriction_succ_eq_ker_roomToMarkedGraded
    (E : AddSubgroup G) (β : Ordinal.{0}) :
    LinearMap.range (roomRestriction p E (Order.le_succ β)) =
      LinearMap.ker (roomToMarkedGraded p E β) := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨x, rfl⟩ := (roomSubmodule p E (Order.succ β)).mkQ_surjective r
    rw [LinearMap.mem_ker, roomRestriction_mk, roomToMarkedGraded_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact AddSubgroup.mem_sup_left x.property
  · intro hq
    obtain ⟨x, rfl⟩ := (roomSubmodule p E β).mkQ_surjective q
    rw [LinearMap.mem_ker, roomToMarkedGraded_mk] at hq
    have hx : (x : G) ∈ pSocleAt p (Order.succ β) ⊔
        (E ⊓ pSocleAt p β) :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hx
    let y' : pSocleAt p (Order.succ β) (G := G) := ⟨y, hy⟩
    refine ⟨(roomSubmodule p E (Order.succ β)).mkQ y', ?_⟩
    rw [roomRestriction_mk]
    apply (Submodule.Quotient.eq _).mpr
    change y - (x : G) ∈ E ⊓ pSocleAt p β
    rw [← hyz]
    simpa using hz

/-- **One-step room decomposition.**  Room is the next-height room plus the
marked-graded layer at the current height. -/
theorem markedGradedInvariant_add_roomInvariant_succ
    (E : AddSubgroup G) (β : Ordinal.{0}) :
    markedGradedInvariant p E β + roomInvariant p E (Order.succ β) =
      roomInvariant p E β := by
  have hrank := LinearMap.rank_eq_of_surjective
    (roomToMarkedGraded_surjective p E β)
  rw [← range_roomRestriction_succ_eq_ker_roomToMarkedGraded p E β] at hrank
  rw [← (LinearEquiv.ofInjective
    (roomRestriction p E (Order.le_succ β))
    (roomRestriction_injective p E (Order.le_succ β))).rank_eq] at hrank
  exact hrank.symm

/-! ### Finite telescoping -/

/-- If two marked groups have the same marked-graded layers for `n` successive
heights and the same room at the endpoint, then their rooms agree at the
starting height.  This is the finite-tail form of the cumulative identity; it
does not use countability or reducedness. -/
theorem roomInvariant_eq_of_markedGraded_eq_to_add_nat
    {H : Type u} [AddCommGroup H]
    (E : AddSubgroup G) (F : AddSubgroup H)
    (β : Ordinal.{0}) (n : ℕ)
    (hgraded : ∀ k : ℕ, k < n →
      markedGradedInvariant p E (β + k) =
        markedGradedInvariant p F (β + k))
    (hend : roomInvariant p E (β + n) = roomInvariant p F (β + n)) :
    roomInvariant p E β = roomInvariant p F β := by
  induction n generalizing β with
  | zero => simpa using hend
  | succ n ih =>
      have htail :
          roomInvariant p E (Order.succ β) =
            roomInvariant p F (Order.succ β) := by
        apply ih (β := Order.succ β)
        · intro k hk
          simpa [Order.succ_eq_add_one, add_assoc] using hgraded (k + 1) (Nat.succ_lt_succ hk)
        · simpa [Order.succ_eq_add_one, add_assoc] using hend
      calc
        roomInvariant p E β =
            markedGradedInvariant p E β +
              roomInvariant p E (Order.succ β) :=
          (markedGradedInvariant_add_roomInvariant_succ p E β).symm
        _ = markedGradedInvariant p F β +
              roomInvariant p F (Order.succ β) := by
          have hzero : markedGradedInvariant p E β =
              markedGradedInvariant p F β := by
            simpa using hgraded 0 (Nat.zero_lt_succ n)
          rw [hzero, htail]
        _ = roomInvariant p F β :=
          markedGradedInvariant_add_roomInvariant_succ p F β

/-! ### Infinite room in the countable case -/

/-- An infinite filtered socle minus a finite mark has countably infinite
dimension in a countable group. -/
theorem roomInvariant_eq_aleph0_of_infinite
    [Countable G] (E : AddSubgroup G) (hE : Set.Finite (E : Set G))
    (β : Ordinal.{0})
    (hP : Set.Infinite (pSocleAt p β (G := G) : Set G)) :
    roomInvariant p E β = ℵ₀ := by
  letI : Finite E := Set.finite_coe_iff.mp hE
  let toE : roomSubmodule p E β → E := fun x => ⟨(x : G), x.property.1⟩
  have htoE : Function.Injective toE := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) hxy
  letI : Finite (roomSubmodule p E β) := Finite.of_injective toE htoE
  have hroomInfinite : Infinite (room p E β) := by
    apply not_finite_iff_infinite.mp
    intro hfinite
    letI : Finite (room p E β) := hfinite
    letI : Module.Finite (ZMod p) (room p E β) := Module.Finite.of_finite
    have hroomRank : Module.rank (ZMod p) (room p E β) < ℵ₀ :=
      Module.rank_lt_aleph0 (ZMod p) (room p E β)
    have hdenRank : Module.rank (ZMod p) (roomSubmodule p E β) < ℵ₀ :=
      Module.rank_lt_aleph0 (ZMod p) (roomSubmodule p E β)
    have hPfiniteRank : Module.rank (ZMod p) (pSocleAt p β (G := G)) < ℵ₀ := by
      rw [← Submodule.rank_quotient_add_rank (roomSubmodule p E β)]
      exact Cardinal.add_lt_aleph0 hroomRank hdenRank
    letI : Module.Finite (ZMod p) (pSocleAt p β (G := G)) :=
      Module.rank_lt_aleph0_iff.mp hPfiniteRank
    letI : Finite (pSocleAt p β (G := G)) := Module.finite_of_finite (ZMod p)
    letI : Infinite (pSocleAt p β (G := G)) := Set.infinite_coe_iff.mpr hP
    exact not_finite (pSocleAt p β (G := G))
  apply le_antisymm
  · exact (rank_le_card (R := ZMod p) (M := room p E β)).trans
      ((Cardinal.mk_le_of_surjective
        (roomSubmodule p E β).mkQ_surjective).trans Cardinal.mk_le_aleph0)
  · rw [← not_lt]
    intro hrank
    letI : Module.Finite (ZMod p) (room p E β) :=
      Module.rank_lt_aleph0_iff.mp hrank
    letI : Finite (room p E β) := Module.finite_of_finite (ZMod p)
    exact hroomInfinite.not_finite inferInstance

/-- Once the ambient Ulm filtration has vanished, every marked room vanishes. -/
theorem roomInvariant_eq_zero_of_ulmSubgroup_eq_bot
    (E : AddSubgroup G) (β : Ordinal.{0})
    (hbot : ulmSubgroup p β (G := G) = ⊥) :
    roomInvariant p E β = 0 := by
  apply rank_zero_iff.mpr
  apply (room_subsingleton_iff p E β).mpr
  intro x hx
  have hxzero : (x : G) = 0 := by
    have : (x : G) ∈ (⊥ : AddSubgroup G) := by
      rw [← hbot]
      exact hx.2
    simpa using this
  simp [hxzero]
