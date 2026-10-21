import Lib.BackForth.Characterization

/-!
# Non-vacuity witnesses

The three public biconditionals are stated for an abstract countable reduced
abelian `p`-group. Until this file, **every** occurrence of `IsReducedPGroup` in
`Lib/` and `Test/` was a bound hypothesis and none was ever discharged, and
nothing anywhere proved `BFRel` either holds or fails at a concrete
configuration. Both sides were only ever related to each other.

That leaves two ways the theorems could have been true but empty, neither of
which grep or a green build can rule out:

* the hypothesis set could be unsatisfiable, so the theorems apply to nothing;
* `BFRel` could be identically `True`, so the left side carries no information.

These witnesses close both. They are deliberately small — the point is that they
are concrete, not that they are interesting.

`D5Example.lean` and `JumpWitness.lean` supply the complementary fact that the
jump kernel can be nonzero, which is what stops odd clause (d) collapsing to
plain room domination.
-/

namespace NonVacuityRegression

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The ambient hypotheses are satisfiable at a nontrivial group. -/
example : IsReducedPGroup 2 (ZMod 4) where
  primary := fun x => ⟨2, by revert x; decide⟩
  reduced := by
    refine ⟨((2 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

/-- And at one of the two groups the D-5 example is built on, so that example is
known to live inside the theorems' hypothesis class. -/
example : IsReducedPGroup 2 (ZMod 4 × ZMod 16) where
  primary := fun x => ⟨4, by revert x; decide⟩
  reduced := by
    refine ⟨((4 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_setOf_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

/-- `BFRel` is not identically `True`.  `1 : ZMod 2` generates a group of order
two and `1 : ZMod 4` one of order four, so no `AddEquiv` matches the generators
and the two tuples cannot share a quantifier-free type. -/
example : ¬ BFRel 2 0 1 ![(1 : ZMod 2)] ![(1 : ZMod 4)] := by
  rw [BFRel_zero]
  rintro ⟨φ, hφ⟩
  set x : AddSubgroup.closure (Set.range ![(1 : ZMod 2)]) :=
    ⟨(1 : ZMod 2), AddSubgroup.subset_closure ⟨0, rfl⟩⟩ with hx
  have hxz : (2 : ℕ) • x = 0 := by
    apply Subtype.ext
    rw [hx]
    decide
  have himg : (2 : ℕ) • φ x = 0 := by
    rw [← map_nsmul, hxz, map_zero]
  have hval : φ x = ⟨(1 : ZMod 4), AddSubgroup.subset_closure ⟨0, rfl⟩⟩ := by
    simpa [hx] using hφ 0
  rw [hval] at himg
  have hcontra : ((2 : ℕ) • (1 : ZMod 4)) = 0 := congrArg Subtype.val himg
  revert hcontra
  decide

end NonVacuityRegression
