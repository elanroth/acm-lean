import Lib.Scott.Classification

/-!
# Scott-classification boundary regressions

These checks pin the honest formal boundary: the five draft templates are
computable data, and the Scott layer consumes the exact algebraic
back-and-forth characterization without an axiomatized complexity oracle.
-/

open Ordinal

/-- The public Scott entry point carries all three exact rank cases. -/
example {p : ℕ} [Fact p.Prime] (ξ : Ordinal.{0}) :
    ACMCharacterizationAtRank p ξ :=
  scottClassification_backAndForth p ξ

/-- The target catalog preserves the recorded limit class. -/
example (γ : Ordinal) (n : ℕ) :
    (scottClassificationTargets γ n).limit = scottSentence_limit γ :=
  rfl

/-- The target catalog preserves the two-infinite draft class. -/
example (γ : Ordinal) (n : ℕ) :
    (scottClassificationTargets γ n).twoInfinite =
      scottSentence_twoInfinite γ n :=
  rfl
