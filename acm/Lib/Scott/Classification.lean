import Lib.Scott.UpperBounds
import Lib.Scott.LowerBounds

/-!
# Scott-classification foundation

The formal result currently available for Scott analysis is the exact
algebraic back-and-forth characterization. The separate template catalog is
statement-level bookkeeping; optimal Scott-sentence upper and lower bounds
remain outside the formal surface until infinitary formula syntax and
satisfaction are implemented.
-/

open Ordinal

variable (p : ℕ) [Fact p.Prime]

/-- Public Scott-side entry point to the exact odd/even/limit characterization
at every literal relation rank. -/
theorem scottClassification_backAndForth (ξ : Ordinal.{0}) :
    ACMCharacterizationAtRank p ξ :=
  scottBackAndForth_characterization p ξ
