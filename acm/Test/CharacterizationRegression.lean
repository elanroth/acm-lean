import Lib.BackForth.Characterization

/-!
# Characterization-induction regressions

These type-level checks pin the transfinite construction architecture and the
exact global biconditionals.
-/

open Ordinal
open AlgebraicBFConditions

universe u

/-- The recursive relation exposes exactly the all-smaller-challenges clause
used in the paper at every positive rank. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (α : Ordinal.{0}) (hα : α ≠ 0)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p α n a b ↔
      ∀ β (_hβ : β < α) (m : ℕ) (c : Fin m → H),
        ∃ d : Fin m → G,
          BFRelReverse p β (n + m) (Fin.append b c) (Fin.append a d) :=
  BFRel_positive_iff p α hα a b

/-- Every literal relation rank has one of the four shapes used by the
well-founded characterization induction. -/
example (γ : Ordinal.{0}) :
    γ = 0 ∨
      (∃ α : Ordinal.{0}, γ = 2 * α + 1) ∨
      (∃ α : Ordinal.{0}, γ = 2 * α + 2) ∨
      Order.IsSuccLimit γ :=
  Ordinal.zero_odd_even_limit_cases γ

/-- At a nonzero limit parameter, the predecessor of the associated odd rank
is literally the limit parameter itself. -/
example {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) : 2 * α = α :=
  Ordinal.two_mul_eq_self_of_isSuccLimit hα

/-- Limit data at a larger cutoff supplies the complete even package at every
smaller successor cutoff. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α δ : Ordinal.{0}} (hδα : Order.succ δ ≤ α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFLimitCondData p hG hH α a b) :
    AlgBFEvenCondData p hG hH δ a b :=
  C.toEven p hG hH hδα

/-- The bounded odd response at a limit parameter produces the reversed
limit predecessor package before any relation-level induction is invoked. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ c : Fin m → G,
      Nonempty (AlgBFLimitCondData p hH hG α
        (Fin.append b d) (Fin.append a c)) :=
  exists_finiteTuple_limitPredecessorData_of_oddData_of_boundedTarget
    p hG hH C hGcap d

/-- The corrected long-target construction embeds any finite challenged
subgroup with the exact predecessor invariant needed by the outer induction. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (D : AddSubgroup H) (hD : Set.Finite (D : Set H))
    (hmarkD : tupleSubgroup b ≤ D) :
    ∃ f : D →+ (⊤ : AddSubgroup G),
      Function.Injective f ∧
      IsHeightPresBelowOn p f (ω * α) ∧
      IsHeightFloorAt p f (ω * α) ∧
      ∀ x : tupleSubgroup b,
        (f ⟨(x : H), hmarkD x.property⟩ : G) =
          (C.iso.equiv x : G) :=
  AlgebraicBFConditions.OddLongCountdown.finite_countdown_within
    p hG hH C hlong D hD hmarkD

/-- The zero/successor/limit split closes the long odd branch from the same
strictly lower claims used by the bounded branch. -/
example {p : ℕ} [Fact p.Prime]
    {α : Ordinal.{0}}
    (hSucc : ∀ δ : Ordinal.{0}, α = Order.succ δ →
      AlgBFEvenSufficiencyAt.{u} p δ)
    (hLimit : Order.IsSuccLimit α →
      AlgBFLimitSufficiencyAt.{u} p α) :
    AlgBFOddLongSufficiencyAt.{u} p α :=
  AlgBFOddLongSufficiencyAt.of_parameter_cases p hSucc hLimit

/-- The older parameterized induction seam remains available: supplying a
long-target theorem at every parameter yields the complete rank package. -/
example {p : ℕ} [Fact p.Prime]
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (γ : Ordinal.{0}) : ACMSufficiencyAtRank.{u} p γ :=
  acmSufficiencyAtRank_of_oddLong p hLong γ

/-- The induction output plugs directly into each of the three algebraic
sufficiency directions. -/
example {p : ℕ} [Fact p.Prime]
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (α : Ordinal.{0}) :
    AlgBFOddSufficiencyAt.{u} p α ∧
      AlgBFEvenSufficiencyAt.{u} p α ∧
      AlgBFLimitSufficiencyAt.{u} p α :=
  ⟨acmOddSufficiency_of_oddLong p hLong α,
    acmEvenSufficiency_of_oddLong p hLong α,
    acmLimitSufficiency_of_oddLong p hLong α⟩

/-- With the long countdown proved locally, the literal-rank induction has no
external hypotheses. -/
example {p : ℕ} [Fact p.Prime] (γ : Ordinal.{0}) :
    ACMSufficiencyAtRank.{u} p γ :=
  acmSufficiencyAtRank p γ

/-- The unconditional induction plugs directly into all three algebraic
sufficiency directions. -/
example {p : ℕ} [Fact p.Prime] (α : Ordinal.{0}) :
    AlgBFOddSufficiencyAt.{u} p α ∧
      AlgBFEvenSufficiencyAt.{u} p α ∧
      AlgBFLimitSufficiencyAt.{u} p α :=
  ⟨acmOddSufficiency p α,
    acmEvenSufficiency p α,
    acmLimitSufficiency p α⟩

/-- A positive relation answers an arbitrary finite challenge already at
atomic rank, producing a concrete enlarged tuple isomorphism. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {α : Ordinal.{0}} (hα : α ≠ 0)
    {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p α n a b) {m : ℕ} (d : Fin m → H) :
    ∃ c : Fin m → G,
      Nonempty (TupleIsoMap (Fin.append a c) (Fin.append b d)) :=
  exists_finiteTuple_baseResponse_of_BFRel p hα h d

/-- Rank one already forces every natural Ulm-height floor for the marked
tuple map, without any finiteness assumption on the ambient groups. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    ∃ C : TupleIsoMap a b,
      ∀ k : ℕ,
        IsHeightFloorAt p C.equiv.toAddMonoidHom (k : Ordinal.{0}) :=
  ACMNecessity.exists_tupleIsoMap_natFloor_of_BFRel_one p h

/-- Consequently the complete directional height clause at odd parameter
zero holds in arbitrary ambient groups. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    GeneratedHeightsDirectional p 0 ω a b :=
  ACMNecessity.generatedHeightsDirectional_zero_of_BFRel_one p h

/-- Rank one also forces the capped Ulm-length inequality required by the
odd algebraic condition at parameter zero in arbitrary reduced groups. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    min (ulmLength p (G := H) hH : Ordinal.{0}) ω ≤
      (ulmLength p (G := G) hG : Ordinal.{0}) :=
  ACMNecessity.length_min_omega_le_of_BFRel_one p hG hH h

/-- At an infinite target-socle level, the room--kernel part of necessity is
automatic; only finite target-socle levels require a finite witness. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H} (C : TupleIsoMap a b)
    (β : Ordinal.{0})
    (hsucc : IsHeightFloorAt p C.equiv.toAddMonoidHom (Order.succ β))
    (hβ : IsHeightFloorAt p C.equiv.toAddMonoidHom β)
    (hinfinite : Set.Infinite (pSocleAt p β (G := G) : Set G)) :
    Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β hsucc hβ :=
  ACMNecessity.kernelRoomBudgetAt_of_infinite_targetSocle
    p hG hH C β hsucc hβ hinfinite

/-- In finite ambient groups, rank one forces the exact room--kernel budget
for one marked tuple map at every ordinal. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H]
    {n : ℕ} (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 1 n a b) :
    ∃ (C : TupleIsoMap a b) (hfloor : IsHeightFloorOn p C.equiv.toAddMonoidHom),
      ∀ β : Ordinal.{0},
        Survival.KernelRoomBudgetAt p C.equiv.toAddMonoidHom β
          (hfloor (Order.succ β)) (hfloor β) :=
  ACMNecessity.exists_kernelRoomBudget_of_finite_BFRel_one p hH h

/-- The odd biconditional is completely closed at parameter zero for finite
ambient groups. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p 1 n a b ↔ AlgBFOddCond p hG hH 0 a b :=
  bf_one_iff_algebraic_odd_zero_finite p hG hH a b

/-- The finite selector-kernel challenge closes the odd base biconditional in
arbitrary countable reduced ambient groups, not only finite ones. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p 1 n a b ↔ AlgBFOddCond p hG hH 0 a b :=
  bf_one_iff_algebraic_odd_zero p hG hH a b

/-- The forward-Hill/reverse-room package is the exact even characterization
at every ordinal block, including countable groups with infinite reserve. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    BFRel p (2 * α + 2) n a b ↔
      AlgBFEvenExactCond p hG hH α a b :=
  bf_even_iff_algebraic p hG hH α a b

/-- Rank two transfers every finite independent family in a natural Ulm
quotient from the challenged ambient group to the response ambient group. -/
noncomputable example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n m k : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b)
    (v : Fin m → ulmQuotient p (k : Ordinal.{0}) (G := H))
    (hv : LinearIndependent (ZMod p) v) :
    ∃ w : Fin m → ulmQuotient p (k : Ordinal.{0}) (G := G),
      LinearIndependent (ZMod p) w :=
  ACMNecessity.exists_ulmQuotient_linearIndependent_response_nat p h v hv

/-- Countability upgrades the finite-family transfer to the genuine absolute
half of the first even window. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel p 2 n a b) (k : ℕ) :
    ulmInvariant p (k : Ordinal.{0}) (G := H) ≤
      ulmInvariant p (k : Ordinal.{0}) (G := G) :=
  ACMNecessity.ulmInvariant_nat_le_of_BFRel_two p h k

/-- The crossed even package remains a proved sufficient strengthening under
an explicitly strong compatibility name. -/
example {p : ℕ} [Fact p.Prime]
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    {n : ℕ} (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    AlgBFEvenStrongCond p hG hH α a b → BFRel p (2 * α + 2) n a b :=
  bf_even_of_strong_algebraic p hG hH α a b

/-- The literal-rank assembly exposes the three exact public biconditionals
through one downstream interface. -/
example {p : ℕ} [Fact p.Prime] (γ : Ordinal.{0}) :
    ACMCharacterizationAtRank p γ :=
  acmCharacterizationAtRank p γ

/-- Necessity has a parallel exact literal-rank interface. -/
example {p : ℕ} [Fact p.Prime] (γ : Ordinal.{0}) :
    ACMNecessityAtRank p γ :=
  acmNecessityAtRank p γ
