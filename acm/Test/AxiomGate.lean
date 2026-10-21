import Lib.BackForth.Characterization
import Lib.Ulm.Theorem

/-!
# Axiom gate for the three public characterization theorems

A `sorry`-free source tree is not the same claim as a `sorry`-free proof: a hole
anywhere in the transitive proof term shows up as `sorryAx` in the kernel's axiom
list, whatever the source text says. Grepping cannot see that.

(The frozen proof-search run records that used to sit at `formal/acm/.rambam/`,
carrying 69 `sorry`s and superseded variants of `Lib/BackForth/Relations.lean`,
now live under `archive/rambam-2026-08-18/`. They were never on the build path.)

These are the checks that settle the question. `#guard_msgs` compares the printed
axiom list against the expected one, so if a hole, a new axiom, or a dependency on
the sorry-carrying sibling package `../infinitary-logic` ever enters the proof of
any of these theorems, **this file fails to compile**.

The expected list is Lean's three standard axioms. `sorryAx` must never appear.
-/

/-- info: 'bf_odd_iff_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bf_odd_iff_algebraic

/-- info: 'bf_even_iff_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bf_even_iff_algebraic

/-- info: 'bf_limit_iff_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bf_limit_iff_algebraic

/-- info: 'acmCharacterizationAtRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms acmCharacterizationAtRank

/-- info: 'acmNecessityAtRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms acmNecessityAtRank

/-- info: 'acmSufficiencyAtRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms acmSufficiencyAtRank

/-! ### Ulm's theorem

The characterization is stated relative to the Ulm invariants, so the classical
theorem underneath it carries the same burden and gets the same gate. Both
directions are pinned separately, since only their conjunction is the theorem. -/

/-- info: 'ulm_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ulm_theorem

/-- info: 'ulm_invariants_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ulm_invariants_of_iso

/-- info: 'iso_of_ulm_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iso_of_ulm_invariants
