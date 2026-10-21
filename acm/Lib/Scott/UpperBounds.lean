import Lib.Scott.Complexity

/-!
# Scott-sentence upper-bound boundary

`Complexity.lean` records the five sentence-template targets. This module does
not promote them to upper-bound theorems: the repository does not yet contain
infinitary formulas, satisfaction, or a theorem constructing a Scott sentence
of a given template. Once that logic layer exists, its construction theorems
belong here and may use `scottBackAndForth_characterization` as their algebraic
input.
-/
