import Lib.BackForth.EvenFiniteExtension

/-!
# Even-extension assembly regressions

These type-level checks pin the exact algebraic response seam and the
relation-level orientation independently of the global characterization
biconditionals.
-/

open Ordinal

universe u

open AlgebraicBFConditions

/-- The finite high-tail countdown is constructed from current even data alone;
in particular, neither ambient group is assumed finite or countable here. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleHighMapData p hG hH
      (EvenHighCountdown.Context.ofStrong p hG hH C) c) :=
  exists_evenFiniteTupleHighMapData p hG hH
    (EvenHighCountdown.Context.ofStrong p hG hH C) c

/-- The constructed high-tail countdown plus the floor-free low climb produces
the response, enlarged inverse tuple isomorphism, and odd height clause. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    {m : ℕ} (c : Fin m → H)
    (M : EvenFiniteTupleHighMapData p hG hH
      (EvenHighCountdown.Context.ofStrong p hG hH C) c) :
    Nonempty (EvenFiniteTupleOddCoreData p hG hH
      (EvenHighCountdown.Context.ofStrong p hG hH C) c) :=
  exists_evenFiniteTupleOddCoreData_of_highMap p hG hH
    (EvenHighCountdown.Context.ofStrong p hG hH C) c M

/-- Countability closes the enlarged room--kernel budget for each challenge. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    {m : ℕ} (c : Fin m → H) :
    Nonempty (EvenFiniteTupleOddMapData p hG hH
      (EvenHighCountdown.Context.ofStrong p hG hH C) c) :=
  exists_evenFiniteTupleOddMapData p hG hH C c

/-- The exact enlarged odd response now follows unconditionally from current
even data in the countable ambient setting. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b) :
    EvenFiniteTupleOddResponses p hG hH α a b :=
  evenFiniteTupleOddResponses p hG hH C

/-- Map-sensitive responses still expose a useful intermediate seam and package
the unchanged ambient clauses automatically. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hmap : ∀ (m : ℕ) (c : Fin m → H),
      Nonempty (EvenFiniteTupleOddMapData p hG hH
        (EvenHighCountdown.Context.ofStrong p hG hH C) c)) :
    EvenFiniteTupleOddResponses p hG hH α a b :=
  evenFiniteTupleOddResponses_of_mapData p hG hH
    (EvenHighCountdown.Context.ofStrong p hG hH C) hmap

/-- The exact response seam and odd sufficiency have the successor orientation
required by `BFRel`. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (hresponse : EvenFiniteTupleOddResponses p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v → BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b :=
  bf_even_of_evenFiniteTupleOddResponses_of_oddSufficiency
    p hG hH hresponse hOdd

/-- All finite even-response algebra is internal; the only remaining input to
this relation-level theorem is odd sufficiency at the predecessor level. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFEvenCondData p hG hH α a b)
    (hOdd : ∀ {k : ℕ} (u : Fin k → H) (v : Fin k → G),
      AlgBFOddCond p hH hG α u v → BFRel p (2 * α + 1) k u v) :
    BFRel p (2 * α + 2) n a b :=
  bf_even_of_evenData_of_oddSufficiency p hG hH C hOdd
