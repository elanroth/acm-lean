import Lib.BackForth.JumpSpace

/-!
# Section 1 specification regressions

These checks protect the distinctions that are easiest to collapse in the
definitions layer:

* room, the marked-graded space, and the Hill space are three *different*
  quotients of `P_β`, with denominators ordered
  `E ∩ P_β ≤ P_{β+1} + (E ∩ P_β) ≤ (E + G_{β+1}) ∩ P_β`;
* the jump space is a `ZMod p`-vector space even though its numerator
  `pE ∩ G_{β+1}` need not consist of elements of order `p`;
* Lemma 1.8 reads its first disjunct off the Hill space, that is, off the room
  of `E + G_{β+1}` — not off the room of `E`.
-/

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [AddCommGroup G]

/-- The room denominator `E ∩ P_β` is contained in the marked-graded
denominator `P_{β+1} + (E ∩ P_β)`.  Together with the upstream
`markedGradedSubmodule_le_hillSubmodule` this orders all three denominators,
so the three invariants cannot be silently identified. -/
example (E : AddSubgroup G) (β : Ordinal.{0}) :
    roomSubmodule p E β ≤ markedGradedSubmodule p E β := by
  intro x hx
  exact AddSubgroup.mem_sup_right hx

example (E : AddSubgroup G) (β : Ordinal.{0}) :
    roomSubmodule p E β ≤ hillSubmodule p E β := by
  intro x hx
  exact markedGradedSubmodule_le_hillSubmodule p E β (AddSubgroup.mem_sup_right hx)

/-- One multiplication by `p` carries the jump-space numerator into its
denominator.  This is the check that makes `jumpSpace` a `ZMod p`-vector
space, and it is the step that fails if the numerator is mistaken for a
subgroup of the socle. -/
example (E : AddSubgroup G) (β : Ordinal.{0}) {c : G}
    (hc : c ∈ pImage p E) (hc' : c ∈ ulmSubgroup p (Order.succ β)) :
    p • c ∈ pImage p (E ⊓ ulmSubgroup p β) :=
  smul_mem_jumpDen p E β ⟨hc, hc'⟩

/-- Proposition 1.2 is about `E`; the Hill-side reading of it is about
`E + G_{β+1}`.  Pinning both shapes keeps the two from being conflated when
Lemma 1.8 is applied. -/
example (E : AddSubgroup G) (β : Ordinal.{0}) :
    (roomSubmodule p E β = ⊤ ↔ pSocleAt p β (G := G) ≤ E) ∧
      (hillSubmodule p E β = ⊤ ↔
        pSocleAt p β (G := G) ≤ E ⊔ ulmSubgroup p (Order.succ β)) :=
  ⟨roomSubmodule_eq_top_iff p E β, hillSubmodule_eq_top_iff p E β⟩

/-- Properness is stated against `E + G_{β+1}`, at exact height `β`.  The
hypothesis `w ∉ G_{β+1}` is not decorative: it is what turns "height at least
`β`" into "height exactly `β`" in Lemma 1.8. -/
example (E : AddSubgroup G) (w : G) (β : Ordinal.{0})
    (hw : w ∈ ulmSubgroup p β (G := G))
    (hws : w ∉ ulmSubgroup p (Order.succ β) (G := G))
    (hprop : IsProper p E w) :
    w ∉ E ⊔ ulmSubgroup p (Order.succ β) (G := G) :=
  (isProper_iff_notMem_sup p E w β hw hws).mp hprop
