import Lib.BackForth.JumpSpace

/-!
# The crossed invariant package at an even back-and-forth window

The theorem of record has two comparisons on a half-open interval.  They run
in opposite directions:

* the absolute Ulm invariant of the right-hand ambient group is at most that
  of the left-hand ambient group;
* the marked-graded invariant of the left-hand marked subgroup is at most that
  of the right-hand marked subgroup.

This source-facing package is intentionally separate from any standard-Hill
reformulation.  With finite marks and exact marked heights the crossed package
can be converted to Hill equality, but one-sided Hill domination alone is not
an equivalent replacement.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]

/-- The two oppositely oriented comparisons in an even window `[base, cap)`.

`G` is the left side of the relation, marked by `E`; `H` is the right side,
marked by `F`.  Naming both fields explicitly prevents an orientation error
from being hidden inside a larger algebraic condition. -/
structure EvenWindowCrossed
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (base cap : Ordinal.{0}) (E : AddSubgroup G) (F : AddSubgroup H) : Prop where
  /-- Absolute comparison: right ambient Ulm is bounded by left ambient Ulm. -/
  absolute : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
    ulmInvariant p β (G := H) ≤ ulmInvariant p β (G := G)
  /-- Relative comparison: left marked-graded is bounded by right marked-graded. -/
  marked : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
    markedGradedInvariant p E β ≤ markedGradedInvariant p F β

namespace EvenWindowCrossed

/-- Pointwise equality of both invariant families is stronger than, and
packages directly into, the crossed window. -/
theorem of_eq
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {base cap : Ordinal.{0}} {E : AddSubgroup G} {F : AddSubgroup H}
    (hulm : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
      ulmInvariant p β (G := H) = ulmInvariant p β (G := G))
    (hmarked : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
      markedGradedInvariant p E β = markedGradedInvariant p F β) :
    EvenWindowCrossed p base cap E F where
  absolute β hbase hcap := (hulm β hbase hcap).le
  marked β hbase hcap := (hmarked β hbase hcap).le

end EvenWindowCrossed

/-- The exact-even window: standard Hill domination in the response direction,
together with reverse cumulative-room domination.  This remains separate from
`EvenWindowCrossed`, whose converse is false in countable ambient groups. -/
structure EvenWindowHillRoom
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (base cap : Ordinal.{0}) (E : AddSubgroup G) (F : AddSubgroup H) : Prop where
  /-- Standard Hill of the right marked pair is bounded by that of the left. -/
  hill_forward : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
    hillInvariant p F β ≤ hillInvariant p E β
  /-- Remaining room of the left marked pair is bounded by that of the right. -/
  room_reverse : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
    roomInvariant p E β ≤ roomInvariant p F β

namespace EvenWindowHillRoom

/-- Pointwise equality of both exact-even invariant families packages into the
exact window. -/
theorem of_eq
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {base cap : Ordinal.{0}} {E : AddSubgroup G} {F : AddSubgroup H}
    (hhill : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
      hillInvariant p F β = hillInvariant p E β)
    (hroom : ∀ β : Ordinal.{0}, base ≤ β → β < cap →
      roomInvariant p E β = roomInvariant p F β) :
    EvenWindowHillRoom p base cap E F where
  hill_forward β hbase hcap := (hhill β hbase hcap).le
  room_reverse β hbase hcap := (hroom β hbase hcap).le

end EvenWindowHillRoom
