import Lib.BackForth.InducedMap

/-!
# The D-5 Example, machine-checked

`AUTHORITATIVE.md` D-5 records the configuration that forces the injectivity half
of odd clause (d) to exist at all:

* `A = ZMod 4 × ZMod 32` with `ā = (2,4)`;
* `B = ZMod 4 × ZMod 16` with `b̄ = (1,2)`;
* the exhausted level `β = 2`.

There every earlier clause holds, the guard `R_{A,⟨ā⟩}(2) = 0` is active, and yet
`ḡ_2` kills the class of the anchor `c = (0,8)`.  This file checks the two facts
that make the example decisive, so that a formalization of clause (d) which does
*not* fail here would be caught.

Both marked subgroups are cyclic of order 8.  Note that the argument never needs
the isomorphism `⟨b̄⟩ → ⟨ā⟩` to be constructed: `(0,8) = 4·b̄`, so **additivity
alone** forces its image to be `4·ā = (0,16)`, which is already in the target
denominator.
-/

open Ordinal

namespace D5Example

abbrev B := ZMod 4 × ZMod 16
abbrev A := ZMod 4 × ZMod 32

/-- The marked element of `B`. -/
def bbar : B := (1, 2)
/-- The marked element of `A`. -/
def abar : A := (2, 4)

/-- `⟨b̄⟩ ≤ B`, cyclic of order 8. -/
def Fb : AddSubgroup B := AddSubgroup.zmultiples bbar
/-- `⟨ā⟩ ≤ A`, cyclic of order 8. -/
def Ea : AddSubgroup A := AddSubgroup.zmultiples abar

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma two_eq : ((2 : Ordinal)) = ((2 : ℕ) : Ordinal) := by simp
private lemma succ_two : Order.succ (2 : Ordinal) = ((3 : ℕ) : Ordinal) := by
  rw [show ((3 : ℕ) : Ordinal) = (3 : Ordinal) by simp]
  rfl

/-! ### The guard is active: `R_{A,⟨ā⟩}(2) = 0` -/

set_option maxRecDepth 8000 in
/-- `P^A_2 = {(0,0), (0,16)}` lies inside `⟨ā⟩`, so the room vanishes and clause
(d)'s injectivity demand is switched on at `β = 2`. -/
theorem guard_active : Subsingleton (room 2 Ea (2 : Ordinal)) := by
  rw [room_subsingleton_iff]
  rintro x ⟨hx2, hxU⟩
  rw [two_eq, ulmSubgroup_nat] at hxU
  obtain ⟨y, hy⟩ := hxU
  have hx : x = ((0 : ZMod 4), (0 : ZMod 32)) ∨ x = ((0 : ZMod 4), (16 : ZMod 32)) := by
    have key : ∀ w : A, (2 : ℕ) • ((2 ^ 2 : ℕ) • w) = 0 →
        ((2 ^ 2 : ℕ) • w = ((0 : ZMod 4), (0 : ZMod 32)) ∨
          (2 ^ 2 : ℕ) • w = ((0 : ZMod 4), (16 : ZMod 32))) := by decide
    have h2 : (2 : ℕ) • ((2 ^ 2 : ℕ) • y) = 0 := by rw [hy]; exact hx2
    rw [← hy]
    exact key y h2
  rcases hx with h | h
  · exact ⟨0, by simp [h]; decide⟩
  · exact ⟨4, by rw [h]; decide⟩

/-! ### The source class is nonzero -/

lemma mem_num : ((0, 8) : B) ∈ jumpNum 2 Fb (2 : Ordinal) := by
  constructor
  · exact ⟨(2, 4), ⟨2, by decide⟩, by decide⟩
  · rw [succ_two, ulmSubgroup_nat]
    exact ⟨((0 : ZMod 4), (1 : ZMod 16)), by decide⟩

lemma not_mem_den : ((0, 8) : B) ∉ jumpDen 2 Fb (2 : Ordinal) := by
  rintro ⟨y, ⟨hyF, hy2⟩, hy⟩
  obtain ⟨k, rfl⟩ := hyF
  rw [two_eq, ulmSubgroup_nat] at hy2
  obtain ⟨z, hz⟩ := hy2
  -- First coordinate: `G^B_2 = 4·B` kills the `ZMod 4` factor, so `4 ∣ k`.
  have hfst : ((k : ZMod 4)) = 0 := by
    have h1 := congrArg Prod.fst hz
    simp only [Prod.smul_fst] at h1
    rw [show (bbar.1 : ZMod 4) = 1 from rfl, zsmul_eq_mul, mul_one] at h1
    have hkill : ∀ w : ZMod 4, (2 ^ 2 : ℕ) • w = 0 := by decide
    rw [← h1, hkill]
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = 4 * m := by
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 4).mp hfst
    exact ⟨m, hm⟩
  -- Second coordinate: `k = 4m` makes the image `16m = 0`, never `8`.
  have hsnd := congrArg Prod.snd hy
  simp only [Prod.smul_snd, bbar] at hsnd
  rw [zsmul_eq_mul] at hsnd
  push_cast at hsnd
  have : (0 : ZMod 16) = 8 := by
    rw [← hsnd]; ring_nf
    rw [show ((16 : ZMod 16)) = 0 by decide]
    ring
  exact absurd this (by decide)

/-! ### The conclusion -/

/-- **The D-5 Example, machine-checked.**  For every additive `φ : Fb →+ Ea`
sending `b̄` to `ā` and respecting the height floor, the induced map on jump
spaces at `β = 2` is **not** injective.

The class of `(0,8)` is nonzero in `S_{B,⟨b̄⟩}(2)` while its image
`φ(0,8) = 4·ā = (0,16)` lies in the target denominator.  Since the guard
`R_{A,⟨ā⟩}(2) = 0` is active (`guard_active`), this is exactly the configuration
clause (d) rules out — and exactly what a dimension comparison cannot see, since
both jump spaces here are one-dimensional. -/
theorem jumpMap_not_injective
    (φ : Fb →+ Ea)
    (hφb : (φ ⟨bbar, AddSubgroup.mem_zmultiples bbar⟩ : A) = abar)
    (hsucc : IsHeightFloorAt 2 φ (Order.succ (2 : Ordinal)))
    (hβ : IsHeightFloorAt 2 φ (2 : Ordinal)) :
    ¬ Function.Injective (jumpMap 2 φ hsucc hβ) := by
  rw [jumpMap_injective_iff]
  push_neg
  refine ⟨⟨((0, 8) : B), mem_num⟩, ?_, not_mem_den⟩
  -- `(0,8) = 4·b̄`, so additivity pins the image at `4·ā = (0,16)`
  have h4 : (⟨((0, 8) : B), jumpNum_le_self 2 Fb 2 mem_num⟩ : Fb)
      = (4 : ℕ) • (⟨bbar, AddSubgroup.mem_zmultiples bbar⟩ : Fb) := by
    apply Subtype.ext
    simp [bbar]
    decide
  rw [h4, map_nsmul]
  show ((4 : ℕ) • (φ ⟨bbar, _⟩ : Ea) : A) ∈ jumpDen 2 Ea (2 : Ordinal)
  rw [show ((4 : ℕ) • (φ ⟨bbar, AddSubgroup.mem_zmultiples bbar⟩ : Ea) : A)
      = (4 : ℕ) • abar by rw [← hφb]]
  -- `(0,16) = 2·(0,8)` with `(0,8) ∈ ⟨ā⟩ ∩ G^A_2`
  refine ⟨((0 : ZMod 4), (8 : ZMod 32)), ⟨⟨2, by decide⟩, ?_⟩, by decide⟩
  rw [two_eq, ulmSubgroup_nat]
  exact ⟨((0 : ZMod 4), (2 : ZMod 32)), by decide⟩

end D5Example
