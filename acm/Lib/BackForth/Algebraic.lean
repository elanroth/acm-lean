import Lib.BackForth.Relations
import Lib.BackForth.EvenWindow
import Lib.BackForth.MarkedGradedTransfer
import Lib.Scott.Tuples
import Lib.BackForth.InducedMap

/-!
# Algebraic reformulation of the back-and-forth relations

We formalize the algebraic characterization of n-back-and-forth equivalence
for tuples in countable reduced abelian p-groups, following Theorem 1.2 of
the ACM algebraic characterization (Updated Alg 4/10).

## Key definitions

- `markedGradedInvariant p F β` : the marked-graded invariant used in the
  Updated Alg 4/10 draft =
    dim_{ℤ/pℤ} [ P_β A / (P_{β+1} A + (F ∩ P_β A)) ]
  When F = ⊥, this reduces to the ordinary Ulm invariant f_A(β). It is
  distinct from the standard Fuchs/Walker Hill invariant for general F.

## Exact algebraic packages

The three exact packages have the following shapes:
- **Odd** (γ = 2α+1): Ulm equality below ω·α, tuple isomorphism, height/length
  conditions with subcases by length and finiteness of P^A_{ω·α+k}.
- **Even** (γ = 2α+2): Ulm equality below ω·α, marked-graded invariant ordering
  from ω·α to ω·α+ω, height matching below ω·α+ω.
- **Limit/zero** (γ limit or 0): Ulm equality below ω·α, height matching
  below ω·α.

All three packages are proved necessary and sufficient.  The exact even
package uses forward standard-Hill domination and reverse cumulative-room
domination.  The older crossed marked/ambient window remains available only
as a stronger sufficient interface: the infinite-reserve counterexample in
`Necessity.lean` refutes its necessity already at parameter zero.

## References
- Alvir–Csima–MacLean, "Scott complexity of countable reduced abelian p-groups"
- Barker, "Back and forth relations for reduced abelian p-groups"
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

section Lengths

variable {G : Type u} [AddCommGroup G]

/- The Ulm length `λ_A` of a reduced p-group: least ordinal α with p^α·G = 0. -/
-- (Already defined in PGroups.UlmInvariants as ulmLength; we use it here.)

/-- The filtered `p`-socle `P_(ω·α+k)` is infinite. -/
def InfiniteAtLevel (α : Ordinal) (k : ℕ) : Prop :=
  Set.Infinite (pSocleAt p (ω * α + k) (G := G) : Set G)

/-- The filtered `p`-socle `P_(ω·α+k)` is finite. -/
def FiniteAtLevel (α : Ordinal) (k : ℕ) : Prop :=
  Set.Finite (pSocleAt p (ω * α + k) (G := G) : Set G)

/-- The critical index: the least k such that P^A_{ω·α+k+1} is finite,
    or ⊤ if no such k exists. Used in the odd-case subcases (iii)(A)/(B)/(C). -/
noncomputable def criticalIndex (α : Ordinal) : ℕ∞ :=
  by
    classical
    exact if h : ∃ k : ℕ, FiniteAtLevel p (G := G) α (k + 1)
      then Nat.find h
      else ⊤

end Lengths

section AlgebraicBFConditions

variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
variable {n : ℕ}

/-! ### Height conditions on generated subgroups -/

/-- Heights agree for every element under a tuple-induced generated-subgroup
isomorphism. -/
def GeneratedHeightsExact (a : Fin n → G) (b : Fin n → H) : Prop :=
  ∃ g : TupleIsoMap a b, ∀ x : tupleSubgroup b,
      ulmHeight p (x : H) = ulmHeight p (g.equiv x : G)

/-- Heights agree below `θ`; above `θ`, both corresponding elements have height
at least `θ`. This is imposed on every element of the generated subgroup, not
only on the displayed tuple coordinates. -/
def GeneratedHeightsMatchBelow
    (θ : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  ∃ g : TupleIsoMap a b, ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < θ) ∨
      (θ ≤ ulmHeight p (x : H) ∧ θ ≤ ulmHeight p (g.equiv x : G))

/-- The directional high-tail condition from Updated Alg 4/10:
below `base` heights agree; above it, the image in `G` reaches at least the
minimum of the source height and `cap`. -/
def GeneratedHeightsDirectional
    (base cap : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  ∃ g : TupleIsoMap a b, ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < base) ∨
      (base ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H)) (cap : WithTop Ordinal.{0}) ≤
          ulmHeight p (g.equiv x : G))

/-- The three-band directional condition in odd subcase (iii)(B). -/
def GeneratedHeightsThreeBand
    (base cap : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  ∃ g : TupleIsoMap a b, ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < base) ∨
      (base ≤ ulmHeight p (x : H) ∧
        ulmHeight p (x : H) ≤ ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (g.equiv x : G) ≤ cap) ∨
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        cap < ulmHeight p (x : H))

/-! ### The tuple isomorphism condition -/

-- `TupleIsoMap a b` is defined in Scott/Tuples.lean: it is the chosen map
-- `⟨b̄⟩ ≃+ ⟨ā⟩` used by all directional conditions below.

/-! ### Odd case conditions (Theorem 1.2, part 1) -/

/-! ### Legacy strong even case -/

/-- **The legacy crossed-window sufficient strengthening.**

This keeps the source-facing crossed window package: absolute Ulm domination
runs from the right ambient group to the left, while marked-graded domination
runs from the left marked pair to the right.  Under finite marks and exact
marked heights this can be repackaged as standard-Hill equality; one-sided
standard-Hill domination is not an equivalent replacement.

The isomorphism is shared.  Previously `tuple_iso` and `heights` each
  existentially bound their own map, so nothing forced the heights condition to
  be about the isomorphism clause (a) provides.  The paper says "`g` extends to
  an isomorphism" and then "for every `b ∈ ⟨b̄⟩` and `a = g(b)`" — one `g`.

No induced map appears here, so unlike the odd case this carries no injectivity
clause; the data is nonetheless kept as data so that clause (e) can name `iso`. -/
structure AlgBFEvenCondData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Type u where
  /-- (a) `g` extends to an isomorphism `⟨b̄⟩ → ⟨ā⟩`. -/
  iso : TupleIsoMap a b
  /-- (b) the length condition, at the cap `ω·α + ω`. -/
  lengths :
    ((ulmLength p (G := G) hG : Ordinal.{0}) = (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) ∨
    (ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) ∧
      ω * α + ω ≤ (ulmLength p (G := H) hH : Ordinal.{0}))
  /-- (c) the absolute Ulm invariants agree below the base. -/
  ulm_below : ∀ β : Ordinal.{0}, β < ω * α →
    ulmInvariant p β (G := H) = ulmInvariant p β (G := G)
  /-- (d) the two oppositely oriented comparisons across the active window. -/
  window : EvenWindowCrossed p (ω * α) (ω * α + ω)
    (tupleSubgroup a) (tupleSubgroup b)
  /-- (e) heights agree below the cap; above it both are at least the cap. -/
  heights : ∀ x : tupleSubgroup b,
    (ulmHeight p (x : H) = ulmHeight p (iso.equiv x : G) ∧
      ulmHeight p (x : H) < ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
    (((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (x : H) ∧
      ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (iso.equiv x : G))

/-- Compatibility proposition for the legacy crossed-window strengthening.
New public statements should use `AlgBFEvenExactCond`. -/
def AlgBFEvenCond
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  Nonempty (AlgBFEvenCondData p hG hH α a b)

/-- Explicit name for the legacy crossed-window sufficient strengthening.
The shorter `AlgBFEvenCondData` name remains as an implementation compatibility
alias for the established construction modules; it is not the exact public
even condition. -/
abbrev AlgBFEvenStrongCondData := AlgBFEvenCondData

/-- Proposition form of the legacy crossed-window sufficient strengthening. -/
abbrev AlgBFEvenStrongCond := AlgBFEvenCond

/-- The exact-even condition.  It deliberately duplicates the
non-window fields of `AlgBFEvenCondData` while replacing only its crossed
marked/ambient window by `EvenWindowHillRoom`.  The old data remains the input
to the established sufficiency development. -/
structure AlgBFEvenExactCondData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Type u where
  iso : TupleIsoMap a b
  lengths :
    ((ulmLength p (G := G) hG : Ordinal.{0}) = (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) ∨
    (ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) ∧
      ω * α + ω ≤ (ulmLength p (G := H) hH : Ordinal.{0}))
  ulm_below : ∀ β : Ordinal.{0}, β < ω * α →
    ulmInvariant p β (G := H) = ulmInvariant p β (G := G)
  window : EvenWindowHillRoom p (ω * α) (ω * α + ω)
    (tupleSubgroup a) (tupleSubgroup b)
  heights : ∀ x : tupleSubgroup b,
    (ulmHeight p (x : H) = ulmHeight p (iso.equiv x : G) ∧
      ulmHeight p (x : H) < ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
    (((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (x : H) ∧
      ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (iso.equiv x : G))

/-- Proposition form of the exact-even condition. -/
def AlgBFEvenExactCond
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  Nonempty (AlgBFEvenExactCondData p hG hH α a b)

namespace AlgBFEvenExactCondData

/-- Exact-even height data gives filtration equivalence below the cap. -/
theorem heightPresBelowCap
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b) :
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

end AlgBFEvenExactCondData

namespace AlgBFEvenCondData

/-- Convert the established crossed data to exact-even data once the two
window equalities have been supplied.  This deliberately makes the missing
overhang theorem an explicit hypothesis: `window_eq` alone is only
marked-graded equality and is insufficient for `hill_eq`. -/
noncomputable def toExactData_of_windowEq
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hhill : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      hillInvariant p (tupleSubgroup b) β = hillInvariant p (tupleSubgroup a) β)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β = roomInvariant p (tupleSubgroup b) β) :
    AlgBFEvenExactCondData p hG hH α a b where
  iso := C.iso
  lengths := C.lengths
  ulm_below := C.ulm_below
  window := EvenWindowHillRoom.of_eq p hhill hroom
  heights := C.heights

end AlgBFEvenCondData

/-! ### Limit/zero case (Theorem 1.2, part 3) -/

/-- **The limit/zero condition, clauses (a)-(d) of the theorem of record.**

This is `latex/main_july_29.tex` part 3.  There is no window at a limit, so there
is neither a domination clause nor an injectivity clause: everything is measured
at the base `ω·α`.  The isomorphism is shared, as in the other two cases. -/
structure AlgBFLimitCondData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Type u where
  /-- (a) `g` extends to an isomorphism `⟨b̄⟩ → ⟨ā⟩`. -/
  iso : TupleIsoMap a b
  /-- (b) the length condition, at the base. -/
  lengths :
    ((ulmLength p (G := G) hG : Ordinal.{0}) = (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α) ∨
    (ω * α ≤ (ulmLength p (G := G) hG : Ordinal.{0}) ∧
      ω * α ≤ (ulmLength p (G := H) hH : Ordinal.{0}))
  /-- (c) the absolute Ulm invariants agree below the base. -/
  ulm_below : ∀ β : Ordinal.{0}, β < ω * α →
    ulmInvariant p β (G := H) = ulmInvariant p β (G := G)
  /-- (d) heights agree below the base; above it both are at least the base. -/
  heights : ∀ x : tupleSubgroup b,
    (ulmHeight p (x : H) = ulmHeight p (iso.equiv x : G) ∧
      ulmHeight p (x : H) < ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0})) ∨
    (((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (x : H) ∧
      ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤ ulmHeight p (iso.equiv x : G))

/-- The limit/zero condition as a proposition. -/
def AlgBFLimitCond
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  Nonempty (AlgBFLimitCondData p hG hH α a b)

/-! ### Odd case assembled (Theorem 1.2, part 1) -/

/-- **Clause (e) implies the height floor across the window.**

The directional height condition is stated with `ulmHeight`, but the jump-space
construction consumes filtration membership.  `mem_ulmSubgroup_iff_le_ulmHeight`
is what connects them.

The cap matters: clause (e) gives the floor only up to `ω·α + ω`, because above
the cap the `min` stops tracking the source height.  That is exactly enough,
since the jump space at a window level `β` mentions only `β` and `succ β`, both
of which stay inside the window. -/
lemma heightFloorAt_of_heights {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (g : TupleIsoMap a b)
    (hh : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < ω * α) ∨
      (ω * α ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H)) ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
          ulmHeight p (g.equiv x : G)))
    (γ : Ordinal.{0}) (hγ : γ ≤ ω * α + ω) :
    IsHeightFloorAt p (G := H) (H := G) (g.equiv.toAddMonoidHom) γ := by
  intro x hx
  rw [mem_ulmSubgroup_iff_le_ulmHeight] at hx
  rw [mem_ulmSubgroup_iff_le_ulmHeight]
  show (γ : WithTop Ordinal.{0}) ≤ ulmHeight p ((g.equiv x : tupleSubgroup a) : G)
  rcases hh x with ⟨heq, _⟩ | ⟨_, hmin⟩
  · rw [← heq]; exact hx
  · exact le_trans (le_min hx (WithTop.coe_le_coe.mpr hγ)) hmin

/-- Clause (e) of the odd condition preserves the filtration in both
directions strictly below its base.  Unlike `heightFloorAt_of_heights`, this
uses the exact low-height disjunct and intentionally says nothing at or above
the base. -/
lemma heightPresBelowOn_of_heights
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (g : TupleIsoMap a b)
    (hh : ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < ω * α) ∨
      (ω * α ≤ ulmHeight p (x : H) ∧
        min (ulmHeight p (x : H))
          (((ω * α + ω : Ordinal.{0})) : WithTop Ordinal.{0}) ≤
            ulmHeight p (g.equiv x : G))) :
    IsHeightPresBelowOn p g.equiv.toAddMonoidHom (ω * α) := by
  intro γ hγ x
  change ((x : H) ∈ ulmSubgroup p γ (G := H) ↔
    (g.equiv x : G) ∈ ulmSubgroup p γ (G := G))
  rw [mem_ulmSubgroup_iff_le_ulmHeight,
    mem_ulmSubgroup_iff_le_ulmHeight]
  rcases hh x with hlow | hhigh
  · rw [hlow.1]
  · have hγbase :
        (γ : WithTop Ordinal.{0}) ≤
          ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) :=
      WithTop.coe_le_coe.mpr (le_of_lt hγ)
    constructor
    · intro _
      have hbaseCap :
          ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            (((ω * α + ω : Ordinal.{0})) : WithTop Ordinal.{0}) :=
        WithTop.coe_le_coe.mpr le_self_add
      exact hγbase.trans ((le_min hhigh.1 hbaseCap).trans hhigh.2)
    · intro _
      exact hγbase.trans hhigh.1

/-- Filtration equivalence below a successor-prelimit cutoff is exactly the
elementwise height disjunction used in the ACM even/limit clauses.

Successor-prelimitness is the point that makes this conversion exact: if an
element has height `β < θ`, then both levels `β` and `succ β` still lie
strictly below `θ`, so filtration equivalence detects both membership at
`β` and nonmembership at `succ β`. -/
lemma heightsMatchBelow_of_heightPresBelowOn
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {θ : Ordinal.{0}} (hθ : Order.IsSuccPrelimit θ)
    {a : Fin n → G} {b : Fin n → H}
    (g : TupleIsoMap a b)
    (hpres : IsHeightPresBelowOn p g.equiv.toAddMonoidHom θ) :
    ∀ x : tupleSubgroup b,
      (ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) ∧
        ulmHeight p (x : H) < θ) ∨
      (θ ≤ ulmHeight p (x : H) ∧
        θ ≤ ulmHeight p (g.equiv x : G)) := by
  intro x
  have source_exact_of_lt
      (hxlt : ulmHeight p (x : H) <
        ((θ : Ordinal.{0}) : WithTop Ordinal.{0})) :
      ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) := by
    have hx0 : (x : H) ≠ 0 := by
      intro hxzero
      have hxsub : x = 0 := Subtype.ext hxzero
      subst x
      exact (not_lt_of_ge
        (coe_le_ulmHeight_of_mem p (0 : H) θ (by simp))) hxlt
    obtain ⟨β, hxβ, hxSucc⟩ :=
      exists_ulmHeight_eq_of_ne_zero (p := p) hH hx0
    have hxheight : ulmHeight p (x : H) =
        (β : WithTop Ordinal.{0}) :=
      ulmHeight_eq_of_mem_not_mem_succ p (x : H) β hxβ hxSucc
    have hβ : β < θ := by
      rw [hxheight] at hxlt
      exact WithTop.coe_lt_coe.mp hxlt
    have hβSucc : Order.succ β < θ := hθ.succ_lt hβ
    have hgβ : (g.equiv x : G) ∈ ulmSubgroup p β (G := G) :=
      (hpres β hβ x).mp hxβ
    have hgSucc : (g.equiv x : G) ∉
        ulmSubgroup p (Order.succ β) (G := G) := by
      intro hg
      exact hxSucc ((hpres (Order.succ β) hβSucc x).mpr hg)
    rw [hxheight,
      ulmHeight_eq_of_mem_not_mem_succ p (g.equiv x : G) β hgβ hgSucc]
  have target_exact_of_lt
      (hglt : ulmHeight p (g.equiv x : G) <
        ((θ : Ordinal.{0}) : WithTop Ordinal.{0})) :
      ulmHeight p (x : H) = ulmHeight p (g.equiv x : G) := by
    have hg0 : (g.equiv x : G) ≠ 0 := by
      intro hgzero
      have hgeq : g.equiv x = 0 := Subtype.ext hgzero
      have hxzero : x = 0 := g.equiv.injective (by simpa using hgeq)
      subst x
      have hglt0 : ulmHeight p (0 : G) <
          ((θ : Ordinal.{0}) : WithTop Ordinal.{0}) := by
        simpa using hglt
      exact (not_lt_of_ge
        (coe_le_ulmHeight_of_mem p (0 : G) θ (by simp))) hglt0
    obtain ⟨β, hgβ, hgSucc⟩ :=
      exists_ulmHeight_eq_of_ne_zero (p := p) hG hg0
    have hgheight : ulmHeight p (g.equiv x : G) =
        (β : WithTop Ordinal.{0}) :=
      ulmHeight_eq_of_mem_not_mem_succ p (g.equiv x : G) β hgβ hgSucc
    have hβ : β < θ := by
      rw [hgheight] at hglt
      exact WithTop.coe_lt_coe.mp hglt
    have hβSucc : Order.succ β < θ := hθ.succ_lt hβ
    have hxβ : (x : H) ∈ ulmSubgroup p β (G := H) :=
      (hpres β hβ x).mpr hgβ
    have hxSucc : (x : H) ∉
        ulmSubgroup p (Order.succ β) (G := H) := by
      intro hx
      exact hgSucc ((hpres (Order.succ β) hβSucc x).mp hx)
    rw [hgheight,
      ulmHeight_eq_of_mem_not_mem_succ p (x : H) β hxβ hxSucc]
  by_cases hxlt : ulmHeight p (x : H) <
      ((θ : Ordinal.{0}) : WithTop Ordinal.{0})
  · exact Or.inl ⟨source_exact_of_lt hxlt, hxlt⟩
  · refine Or.inr ⟨le_of_not_gt hxlt, ?_⟩
    by_contra htarget
    have hglt : ulmHeight p (g.equiv x : G) <
        ((θ : Ordinal.{0}) : WithTop Ordinal.{0}) := lt_of_not_ge htarget
    exact hxlt (by rw [target_exact_of_lt hglt]; exact hglt)

/-- Package `heightsMatchBelow_of_heightPresBelowOn` as the tuple-level ACM
height predicate, keeping the same chosen tuple isomorphism. -/
lemma generatedHeightsMatchBelow_of_heightPresBelowOn
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {θ : Ordinal.{0}} (hθ : Order.IsSuccPrelimit θ)
    {a : Fin n → G} {b : Fin n → H}
    (g : TupleIsoMap a b)
    (hpres : IsHeightPresBelowOn p g.equiv.toAddMonoidHom θ) :
    GeneratedHeightsMatchBelow p θ a b :=
  ⟨g, heightsMatchBelow_of_heightPresBelowOn p hG hH hθ g hpres⟩

/-- **The odd condition, clauses (a)-(e) of the theorem of record.**

This is the corrected D-23 form of the odd condition.  Clause (d) is the single
room--kernel inequality

`R_{H,F}(β) + dim ker(ḡ_β) ≤ R_{G,E}(β)`.

It replaces the strictly weaker pair consisting of room domination and a
zero-target-room injectivity guard.  The arithmetic is stated inline here so
the characterization layer depends only on the group-theoretic induced map,
not on the finite Rado implementation which consumes the same inequality.

There are no extra floor fields in the package.  The proof arguments needed to
form `g_bar_beta` are derived from clause (e) at the two levels mentioned by the
jump space, using `mem_ulmSubgroup_iff_le_ulmHeight`. -/
structure AlgBFOddCondData
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Type u where
  /-- (a) `g` extends to an isomorphism `⟨b̄⟩ → ⟨ā⟩`. -/
  iso : TupleIsoMap a b
  /-- (b) the length condition. -/
  lengths :
    ((ulmLength p (G := G) hG : Ordinal.{0}) = (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α) ∨
    (ω * α ≤ (ulmLength p (G := H) hH : Ordinal.{0}) ∧
      min (ulmLength p (G := H) hH : Ordinal.{0}) (ω * α + ω) ≤
        (ulmLength p (G := G) hG : Ordinal.{0}))
  /-- (c) the absolute Ulm invariants agree below the base. -/
  ulm_below : ∀ β : Ordinal.{0}, β < ω * α →
    ulmInvariant p β (G := H) = ulmInvariant p β (G := G)
  /-- (e) the directional height condition. -/
  heights : ∀ x : tupleSubgroup b,
    (ulmHeight p (x : H) = ulmHeight p (iso.equiv x : G) ∧
      ulmHeight p (x : H) < ω * α) ∨
    (ω * α ≤ ulmHeight p (x : H) ∧
      min (ulmHeight p (x : H)) ((ω * α + ω : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
        ulmHeight p (iso.equiv x : G))
  /-- (d): the exact `K_β` room--kernel budget throughout the active window.

  The two height-floor arguments are derived from clause (e); no global height
  floor is smuggled into the algebraic characterization. -/
  kernel_room :
    ∀ (β : Ordinal.{0}) (_hβ : ω * α ≤ β) (hβ' : β < ω * α + ω),
      roomInvariant p (tupleSubgroup b) β +
        jumpKernelInvariant p (iso.equiv.toAddMonoidHom)
          (heightFloorAt_of_heights p iso heights (Order.succ β)
            (Order.succ_le_of_lt hβ'))
          (heightFloorAt_of_heights p iso heights β (le_of_lt hβ')) ≤
        roomInvariant p (tupleSubgroup a) β

/-- The odd condition as a proposition: the data of clauses (a)-(e) exists.

Carrying the isomorphism as data is forced — clause (d) is a statement *about*
`g_bar_beta`, which is built from that isomorphism.  This mirrors
`TuplesIso = Nonempty (TupleIsoMap a b)`. -/
def AlgBFOddCond
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) : Prop :=
  Nonempty (AlgBFOddCondData p hG hH α a b)

end AlgebraicBFConditions

section MainTheorem

variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
variable {n : ℕ}
variable [Countable G] [Countable H]

/-! ### Lemma 1.3: Height-preserving invariant equivalence -/

/-- Lemma 1.3: below a height threshold, a height-preserving isomorphism
between finite marked subgroups converts equality of the absolute Ulm
invariants into equality of the marked-graded invariants, and conversely.

The finiteness, bijectivity, and explicit threshold are hypotheses of the
source lemma; dropping any of them is not a harmless strengthening. -/
theorem markedGradedInvariant_eq_iff_of_heightPres
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (F : AddSubgroup G) (E : AddSubgroup H)
    (hF : Set.Finite (F : Set G)) (hE : Set.Finite (E : Set H))
    (φ : F ≃+ E) (θ : Ordinal)
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal) (hγ : γ < θ) :
    ulmInvariant p γ (G := G) = ulmInvariant p γ (G := H) ↔
      markedGradedInvariant p F γ = markedGradedInvariant p E γ := by
  exact markedGradedInvariant_eq_iff_of_finiteHeightEquiv
    p F E hF φ θ hφ γ hγ

/-! ### The proved level-zero characterization -/

/-- **The level-`0` case, proved.**

At `α = 0` every clause of the limit condition except (a) is degenerate: the
length disjunction's second branch and the height disjunction's second branch are
both trivially satisfied, and the Ulm clause quantifies over no `β`.  What is left
is exactly the base relation, in the opposite orientation. -/
theorem bf_limit_iff_algebraic_zero
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p 0 n a b ↔ AlgBFLimitCond p hG hH 0 a b := by
  rw [BFRel_zero]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨{
      iso := TupleIsoMap.ofBase φ hφ
      lengths := Or.inr ⟨by simp, by simp⟩
      ulm_below := by intro β hβ; simp at hβ
      heights := by
        intro x
        exact Or.inr ⟨by simp, by simp⟩ }⟩
  · rintro ⟨cond⟩
    obtain ⟨φ, hφ⟩ := cond.iso.toBase
    exact ⟨φ, hφ⟩

end MainTheorem
