import Lib.PGroups.FiniteSocle

/-!
# Finite-socle regressions

These type-level checks pin the two classical interfaces used by the even
window's long branch, separately from the room and back-and-forth assembly.
-/

open Ordinal

universe u

/-- The compactness theorem has exactly the reduced-primary and finite-socle
hypotheses; countability is not needed. -/
example {p : ℕ} [Fact p.Prime]
    {G : Type u} [AddCommGroup G]
    (hG : IsReducedPGroup p G)
    (hP : Set.Finite (pSocle p (G := G) : Set G)) :
    Finite G :=
  finite_of_finite_pSocle p hG hP

/-- Its Ulm-tail consequence is the precise omega-boundary statement consumed
by `EvenToOdd.lean`. -/
example {p : ℕ} [Fact p.Prime]
    {G : Type u} [AddCommGroup G]
    (hG : IsReducedPGroup p G) (β : Ordinal.{0})
    (hlong : β + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0})) :
    Set.Infinite (pSocleAt p β (G := G) : Set G) :=
  infinite_pSocleAt_of_add_omega_le_ulmLength p hG β hlong
