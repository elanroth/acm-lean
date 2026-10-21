import Lib.BackForth.OddFiniteExtension
import Lib.BackForth.EvenFiniteExtension
import Lib.BackForth.EvenToOdd
import Lib.BackForth.LimitRestriction
import Lib.BackForth.Necessity

/-!
# Even-window specification regressions

These examples pin the two source-facing comparison orientations separately.
They are intentionally type-level regressions: swapping either ambient group
or either marked subgroup changes the proposition being asserted.
-/

open Ordinal Cardinal

universe u

example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {base cap : Ordinal.{0}} {E : AddSubgroup G} {F : AddSubgroup H}
    (C : EvenWindowCrossed p base cap E F)
    (β : Ordinal.{0}) (hbase : base ≤ β) (hcap : β < cap) :
    ulmInvariant p β (G := H) ≤ ulmInvariant p β (G := G) :=
  C.absolute β hbase hcap

example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {base cap : Ordinal.{0}} {E : AddSubgroup G} {F : AddSubgroup H}
    (C : EvenWindowCrossed p base cap E F)
    (β : Ordinal.{0}) (hbase : base ≤ β) (hcap : β < cap) :
    markedGradedInvariant p E β ≤ markedGradedInvariant p F β :=
  C.marked β hbase hcap

/-- The exact candidate keeps its two orientations explicit and independent of
the historical crossed package. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {base cap : Ordinal.{0}} {E : AddSubgroup G} {F : AddSubgroup H}
    (C : EvenWindowHillRoom p base cap E F)
    (β : Ordinal.{0}) (hbase : base ≤ β) (hcap : β < cap) :
    hillInvariant p F β ≤ hillInvariant p E β ∧
      roomInvariant p E β ≤ roomInvariant p F β :=
  ⟨C.hill_forward β hbase hcap, C.room_reverse β hbase hcap⟩

/-- Exact-even data exposes the same cutoff filtration equivalence as the
strong package, but makes no unproved conversion claim between the packages. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b) :
    IsHeightPresBelowOn p C.iso.equiv.toAddMonoidHom (ω * α + ω) :=
  C.heightPresBelowCap p hG hH

/-- Exact-even data answers every finite outer challenge with the reversed odd
predecessor package required by the successor relation. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b) :
    AlgebraicBFConditions.EvenFiniteTupleOddResponses p hG hH α a b :=
  AlgebraicBFConditions.evenFiniteTupleOddResponses_of_exactData
    p hG hH C

/-- Exact-even data implies the even successor once odd sufficiency is known
at the predecessor rank. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenExactCondData p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v → BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b :=
  AlgebraicBFConditions.bf_even_of_exactEvenData_of_oddSufficiency
    p hG hH C hOdd

/-- The old package has a single guarded adapter to the exact package; callers
must provide genuine Hill and room equalities rather than treating
marked-graded equality as a substitute. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hhill : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      hillInvariant p (tupleSubgroup b) β = hillInvariant p (tupleSubgroup a) β)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup a) β = roomInvariant p (tupleSubgroup b) β) :
    AlgBFEvenExactCondData p hG hH α a b :=
  C.toExactData_of_windowEq p hG hH hhill hroom

/-- The compiled overhang bridge discharges both equality hypotheses for the
established crossed package in countable reduced ambient groups. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    AlgBFEvenExactCondData p hG hH α a b :=
  C.toExactData p hG hH

/-- Rank two now supplies the exact-even candidate at the base without the
rejected opposite marked-graded hypothesis. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) :
    AlgBFEvenExactCond p hG hH 0 a b :=
  ACMNecessity.even_zero_exact_of_BFRel_two p hG hH h

/-- The finite-mark transfer is independent of reducedness, countability, and
the back-and-forth relation. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H)
    (hF : Set.Finite (F : Set G)) (φ : F ≃+ E) (θ : Ordinal.{0})
    (hφ : ∀ x : F,
      (ulmHeight p (φ x : H) = ulmHeight p (x : G) ∧
        ulmHeight p (x : G) < θ) ∨
      (θ ≤ ulmHeight p (x : G) ∧ θ ≤ ulmHeight p (φ x : H)))
    (γ : Ordinal.{0}) (hγ : γ < θ) :
    ulmInvariant p γ (G := G) = ulmInvariant p γ (G := H) ↔
      markedGradedInvariant p F γ = markedGradedInvariant p E γ :=
  markedGradedInvariant_eq_iff_of_finiteHeightEquiv
    p F E hF φ θ hφ γ hγ

/-- Limit algebraic data restricts independently of the unfinished global
limit biconditional. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α β : Ordinal.{0}} (hβα : β ≤ α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFLimitCond p hG hH α a b) :
    AlgBFLimitCond p hG hH β a b :=
  C.antitone p hG hH hβα

/-- Once room domination is supplied, even data yields odd data with no
remaining jump-kernel hypothesis. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hroom : ∀ β : Ordinal.{0}, ω * α ≤ β → β < ω * α + ω →
      roomInvariant p (tupleSubgroup b) β ≤ roomInvariant p (tupleSubgroup a) β) :
    Nonempty (AlgBFOddCondData p hG hH α a b) :=
  ⟨C.toOddData_of_roomDom p hG hH hroom⟩

/-- For finite tuple marks, the crossed inequalities themselves collapse to
pointwise equalities on the even window. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (β : Ordinal.{0}) (hbase : ω * α ≤ β) (hcap : β < ω * α + ω) :
    ulmInvariant p β (G := G) = ulmInvariant p β (G := H) ∧
      markedGradedInvariant p (tupleSubgroup a) β =
        markedGradedInvariant p (tupleSubgroup b) β :=
  C.window_eq p hG hH β hbase hcap

/-- The local room calculation is an exact one-step decomposition, independent
of countability, reducedness, and the global back-and-forth relation. -/
example {p : ℕ} [Fact p.Prime]
    {G : Type u} [AddCommGroup G]
    (E : AddSubgroup G) (β : Ordinal.{0}) :
    markedGradedInvariant p E β + roomInvariant p E (Order.succ β) =
      roomInvariant p E β :=
  markedGradedInvariant_add_roomInvariant_succ p E β

/-- The short-length branch closes internally: common bounded length plus the
even-window data already forces equality of the two rooms. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hshort :
      (ulmLength p (G := G) hG : Ordinal.{0}) =
          (ulmLength p (G := H) hH : Ordinal.{0}) ∧
        (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (β : Ordinal.{0}) (hbase : ω * α ≤ β) (hcap : β < ω * α + ω) :
    roomInvariant p (tupleSubgroup b) β =
      roomInvariant p (tupleSubgroup a) β :=
  C.roomInvariant_eq_of_shortLengths p hG hH hshort β hbase hcap

/-- The finite-socle compactness lemma now closes the long branch internally,
so even data converts to odd data without an external room hypothesis. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    Nonempty (AlgBFOddCondData p hG hH α a b) :=
  ⟨C.toOddData p hG hH⟩

/-- The crossed presentation does not make even data directional after finite
mark cancellation: it also yields odd data with the ambient groups swapped. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    Nonempty (AlgBFOddCondData p hH hG α b a) :=
  ⟨C.toOddDataSymm p hG hH⟩

/-- The bounded successor response is packaged as corrected crossed even data
before any back-and-forth characterization theorem is invoked. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n m : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) <
      ω * Order.succ δ + ω)
    (d : Fin m → H) :
    ∃ c : Fin m → G,
      Nonempty
        (AlgBFEvenCondData p hH hG δ (Fin.append b d) (Fin.append a c)) :=
  AlgebraicBFConditions.exists_finiteTuple_evenPredecessorData_of_oddData_of_boundedTarget
    p hG hH C hGcap d

/-- The successor relation wrapper consumes only a one-directional even
induction hypothesis; no global biconditional is smuggled into the assembly. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {δ : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH (Order.succ δ) a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) <
      ω * Order.succ δ + ω)
    (hEven : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFEvenCond p hH hG δ u v → BFRel p (2 * δ + 2) k u v) :
    BFRel p (2 * Order.succ δ + 1) n a b :=
  AlgebraicBFConditions.bf_odd_succ_of_oddData_of_boundedTarget_of_evenSufficiency
    p hG hH C hGcap hEven
