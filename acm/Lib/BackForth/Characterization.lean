import Lib.BackForth.EvenFiniteExtension
import Lib.BackForth.LimitRestriction
import Lib.BackForth.Necessity
import Lib.BackForth.OddFiniteExtension

/-!
# Assembly of the ACM algebraic packages

The algebraic data structures and their local consequences live in
`Algebraic.lean`.  Finite challenge responses, even-to-odd restriction, and
limit restriction live in separate lower modules.  The exact odd, even, and
limit necessity and sufficiency directions are assembled here.  The former
crossed-even converse is excluded because it is false for countable ambient
groups with an infinite fresh-coordinate reserve.
-/

open Ordinal Cardinal
open AlgebraicBFConditions

universe u

variable (p : ℕ) [Fact p.Prime]

/-! ### The transfinite sufficiency package

The proof of the three characterization statements is one induction on the
relation rank, not three independent arguments.  These predicates name the
three sufficiency hypotheses used by that induction without appealing to any
global biconditional. -/

/-- Odd sufficiency at parameter `α`, uniformly in both ambient groups and all
finite tuple arities. -/
def AlgBFOddSufficiencyAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    AlgBFOddCond p hG hH α a b → BFRel p (2 * α + 1) n a b

/-- Even sufficiency at parameter `α`. -/
def AlgBFEvenSufficiencyAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    AlgBFEvenCond p hG hH α a b → BFRel p (2 * α + 2) n a b

/-- Limit/zero sufficiency at the literal relation rank `α`. -/
def AlgBFLimitSufficiencyAt (α : Ordinal.{0}) : Prop :=
  (Order.IsSuccLimit α ∨ α = 0) →
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      [Countable G] [Countable H]
      (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      AlgBFLimitCond p hG hH α a b → BFRel p α n a b

/-- The three sufficiency statements available at one induction parameter. -/
structure ACMSufficiencyAt (α : Ordinal.{0}) : Prop where
  odd : AlgBFOddSufficiencyAt.{u} p α
  even : AlgBFEvenSufficiencyAt.{u} p α
  limit : AlgBFLimitSufficiencyAt.{u} p α

/-- The completed finite even-response construction turns odd sufficiency at
`α` into even sufficiency at the same parameter. -/
theorem AlgBFEvenSufficiencyAt.of_odd
    {α : Ordinal.{0}} (hOdd : AlgBFOddSufficiencyAt.{u} p α) :
    AlgBFEvenSufficiencyAt.{u} p α := by
  intro G H _ _ _ _ hG hH n a b hEven
  obtain ⟨C⟩ := hEven
  exact bf_even_of_evenData_of_oddSufficiency p hG hH C (by
    intro k u v h
    exact hOdd hH hG u v h)

/-- The limit/zero sufficiency package is closed at rank zero. -/
theorem AlgBFLimitSufficiencyAt.zero : AlgBFLimitSufficiencyAt.{u} p 0 := by
  intro _hzero G H _ _ _ _ hG hH n a b h
  exact (bf_limit_iff_algebraic_zero p hG hH a b).2 h

/-- A nonzero limit sufficiency statement is assembled entirely from
sufficiency at lower relation ranks.

Limit data restricts directly to smaller limit ranks.  At an odd or even
lower rank, it first restricts to the corresponding successor cutoff; that is
the full even algebraic package, and even-to-odd restriction supplies the odd
package when needed. -/
theorem AlgBFLimitSufficiencyAt.of_lower
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (hOdd : ∀ δ : Ordinal.{0}, 2 * δ + 1 < α →
      AlgBFOddSufficiencyAt.{u} p δ)
    (hEven : ∀ δ : Ordinal.{0}, 2 * δ + 2 < α →
      AlgBFEvenSufficiencyAt.{u} p δ)
    (hLimit : ∀ β : Ordinal.{0}, β < α →
      AlgBFLimitSufficiencyAt.{u} p β) :
    AlgBFLimitSufficiencyAt.{u} p α := by
  intro _hrank G H _ _ _ _ hG hH n a b hCond
  obtain ⟨C⟩ := hCond
  rw [BFRel_limit p α hα]
  intro β hβα
  rcases Ordinal.zero_odd_even_limit_cases β with
    hzero | hodd | heven | hlimit
  · subst β
    exact AlgBFLimitSufficiencyAt.zero p (Or.inr rfl)
      hG hH a b ⟨C.restrict p hG hH (zero_le α)⟩
  · obtain ⟨δ, rfl⟩ := hodd
    have hsucc : Order.succ δ ≤ α :=
      (Ordinal.succ_le_two_mul_add_one δ).trans hβα.le
    let E : AlgBFEvenCondData p hG hH δ a b :=
      C.toEven p hG hH hsucc
    exact hOdd δ hβα hG hH a b ⟨E.toOddData p hG hH⟩
  · obtain ⟨δ, rfl⟩ := heven
    have hoddEven : 2 * δ + 1 < 2 * δ + 2 := by
      simpa [Order.succ_eq_add_one, ← one_add_one_eq_two, add_assoc] using
        (Order.lt_succ (2 * δ + 1))
    have hsucc : Order.succ δ ≤ α :=
      (Ordinal.succ_le_two_mul_add_one δ).trans
        (hoddEven.trans hβα).le
    exact hEven δ hβα hG hH a b ⟨C.toEven p hG hH hsucc⟩
  · exact hLimit β hβα (Or.inl hlimit) hG hH a b
      ⟨C.restrict p hG hH hβα.le⟩

/-- The bounded-target portion of odd sufficiency.  Naming it separately keeps
the Case 1(c) construction available as a reusable local theorem. -/
def AlgBFOddBoundedSufficiencyAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    AlgBFOddCond p hG hH α a b →
      (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω →
      BFRel p (2 * α + 1) n a b

/-- The bounded odd base branch is the already-proved level-one response. -/
theorem AlgBFOddBoundedSufficiencyAt.zero :
    AlgBFOddBoundedSufficiencyAt.{u} p 0 := by
  intro G H _ _ _ _ hG hH n a b hOdd hGcap
  obtain ⟨C⟩ := hOdd
  simpa using bf_one_of_oddData_of_boundedTarget p hG hH C (by
    simpa using hGcap)

/-- At a successor parameter, the bounded odd branch consumes precisely the
even sufficiency hypothesis at the predecessor parameter. -/
theorem AlgBFOddBoundedSufficiencyAt.succ_of_even
    {δ : Ordinal.{0}} (hEven : AlgBFEvenSufficiencyAt.{u} p δ) :
    AlgBFOddBoundedSufficiencyAt.{u} p (Order.succ δ) := by
  intro G H _ _ _ _ hG hH n a b hOdd hGcap
  obtain ⟨C⟩ := hOdd
  apply bf_odd_succ_of_oddData_of_boundedTarget_of_evenSufficiency
    p hG hH C hGcap
  intro k u v h
  exact hEven hH hG u v h

/-- At a limit parameter, the bounded odd branch consumes the limit
sufficiency statement at the (strictly smaller) predecessor relation rank
`α = 2 * α`. -/
theorem AlgBFOddBoundedSufficiencyAt.limit_of_limit
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (hLimit : AlgBFLimitSufficiencyAt.{u} p α) :
    AlgBFOddBoundedSufficiencyAt.{u} p α := by
  intro G H _ _ _ _ hG hH n a b hOdd hGcap
  obtain ⟨C⟩ := hOdd
  apply bf_odd_limit_of_oddData_of_boundedTarget_of_limitSufficiency
    p hG hH hα C hGcap
  intro k u v h
  exact hLimit (Or.inl hα) hH hG u v h

/-- The three parameter shapes assemble the complete bounded odd branch. -/
theorem AlgBFOddBoundedSufficiencyAt.of_parameter_cases
    {α : Ordinal.{0}}
    (hSucc : ∀ δ : Ordinal.{0}, α = Order.succ δ →
      AlgBFEvenSufficiencyAt.{u} p δ)
    (hLimit : Order.IsSuccLimit α →
      AlgBFLimitSufficiencyAt.{u} p α) :
    AlgBFOddBoundedSufficiencyAt.{u} p α := by
  rcases Order.isMin_or_mem_range_succ_or_isSuccLimit α with
    hzero | hsucc | hlimit
  · have hαzero : α = 0 := isMin_iff_eq_bot.mp hzero
    subst α
    intro G H _ _ _ _ hG hH n a b hOdd hcap
    exact AlgBFOddBoundedSufficiencyAt.zero p hG hH a b hOdd hcap
  · obtain ⟨δ, rfl⟩ := hsucc
    exact AlgBFOddBoundedSufficiencyAt.succ_of_even p (hSucc δ rfl)
  · exact AlgBFOddBoundedSufficiencyAt.limit_of_limit p hlimit
      (hLimit hlimit)

/-- The only odd sufficiency branch not covered by the bounded finite
embedding theorem: the target Ulm length reaches the odd cap. -/
def AlgBFOddLongSufficiencyAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    AlgBFOddCond p hG hH α a b →
      ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}) →
      BFRel p (2 * α + 1) n a b

/-- The long odd base branch is the cap-truncated level-one response. -/
theorem AlgBFOddLongSufficiencyAt.zero :
    AlgBFOddLongSufficiencyAt.{u} p 0 := by
  intro G H _ _ _ _ hG hH n a b hOdd hlong
  obtain ⟨C⟩ := hOdd
  simpa using
    (bf_one_of_oddData_of_longTarget p hG hH C (by simpa using hlong))

/-- At a successor parameter, the long countdown constructs the complete
even predecessor package and consumes even sufficiency one rank lower. -/
theorem AlgBFOddLongSufficiencyAt.succ_of_even
    {δ : Ordinal.{0}} (hEven : AlgBFEvenSufficiencyAt.{u} p δ) :
    AlgBFOddLongSufficiencyAt.{u} p (Order.succ δ) := by
  intro G H _ _ _ _ hG hH n a b hOdd hlong
  obtain ⟨C⟩ := hOdd
  apply bf_odd_succ_of_oddData_of_longTarget_of_evenSufficiency
    p hG hH C hlong
  intro k u v h
  exact hEven hH hG u v h

/-- At a limit parameter, the long countdown constructs the reversed limit
predecessor package and consumes limit sufficiency at the lower literal rank. -/
theorem AlgBFOddLongSufficiencyAt.limit_of_limit
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (hLimit : AlgBFLimitSufficiencyAt.{u} p α) :
    AlgBFOddLongSufficiencyAt.{u} p α := by
  intro G H _ _ _ _ hG hH n a b hOdd hlong
  obtain ⟨C⟩ := hOdd
  apply bf_odd_limit_of_oddData_of_longTarget_of_limitSufficiency
    p hG hH hα C hlong
  intro k u v h
  exact hLimit (Or.inl hα) hH hG u v h

/-- The zero/successor/limit split assembles every long odd branch from the
same strictly lower claims used by the bounded branch. -/
theorem AlgBFOddLongSufficiencyAt.of_parameter_cases
    {α : Ordinal.{0}}
    (hSucc : ∀ δ : Ordinal.{0}, α = Order.succ δ →
      AlgBFEvenSufficiencyAt.{u} p δ)
    (hLimit : Order.IsSuccLimit α →
      AlgBFLimitSufficiencyAt.{u} p α) :
    AlgBFOddLongSufficiencyAt.{u} p α := by
  rcases Order.isMin_or_mem_range_succ_or_isSuccLimit α with
    hzero | hsucc | hlimit
  · have hαzero : α = 0 := isMin_iff_eq_bot.mp hzero
    subst α
    intro G H _ _ _ _ hG hH n a b hOdd hlong
    exact AlgBFOddLongSufficiencyAt.zero p hG hH a b hOdd hlong
  · obtain ⟨δ, rfl⟩ := hsucc
    exact AlgBFOddLongSufficiencyAt.succ_of_even p (hSucc δ rfl)
  · exact AlgBFOddLongSufficiencyAt.limit_of_limit p hlimit
      (hLimit hlimit)

/-- Bounded and long target branches exhaust the odd sufficiency direction. -/
theorem AlgBFOddSufficiencyAt.of_bounded_and_long
    {α : Ordinal.{0}}
    (hBounded : AlgBFOddBoundedSufficiencyAt.{u} p α)
    (hLong : AlgBFOddLongSufficiencyAt.{u} p α) :
    AlgBFOddSufficiencyAt.{u} p α := by
  intro G H _ _ _ _ hG hH n a b hOdd
  rcases lt_or_ge (ulmLength p (G := G) hG : Ordinal.{0})
      (ω * α + ω) with hshort | hlong
  · exact hBounded hG hH a b hOdd hshort
  · exact hLong hG hH a b hOdd hlong

/-- The three algebraic sufficiency claims whose literal relation rank is
`γ`.  Most fields are vacuous at any fixed `γ`; this packaging lets one
well-founded induction expose exactly the predecessor claim needed by each
parity case. -/
structure ACMSufficiencyAtRank (γ : Ordinal.{0}) : Prop where
  odd : ∀ α : Ordinal.{0}, γ = 2 * α + 1 →
    AlgBFOddSufficiencyAt.{u} p α
  even : ∀ α : Ordinal.{0}, γ = 2 * α + 2 →
    AlgBFEvenSufficiencyAt.{u} p α
  limit : AlgBFLimitSufficiencyAt.{u} p γ

/-- **The transfinite sufficiency induction.**

Once the long-target odd response is available at every parameter, all three
algebraic sufficiency directions follow by one well-founded induction on the
literal back-and-forth rank.  The induction dependencies are:

* odd at `0`: the proved level-one finite response;
* odd at `succ δ`: even at the predecessor rank `2 * δ + 2`;
* odd at limit `α`: limit at the predecessor rank `α = 2 * α`;
* even at `α`: odd at the predecessor rank `2 * α + 1`;
* limit at `γ`: the appropriate odd/even/limit claim at every `β < γ`.
-/
theorem acmSufficiencyAtRank_of_oddLong
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (γ : Ordinal.{0}) : ACMSufficiencyAtRank.{u} p γ := by
  refine Ordinal.lt_wf.induction γ ?_
  intro γ ih
  refine {
    odd := ?_
    even := ?_
    limit := ?_ }
  · intro α hγα
    have hBounded : AlgBFOddBoundedSufficiencyAt.{u} p α :=
      AlgBFOddBoundedSufficiencyAt.of_parameter_cases.{u} p
        (fun δ hαsucc ↦ by
          have hrank : 2 * δ + 2 < γ := by
            rw [hγα, hαsucc]
            rw [show 2 * Order.succ δ + 1 =
                Order.succ (2 * δ + 2) by
              rw [Ordinal.mul_succ]
              rfl]
            exact Order.lt_succ _
          intro G H _ _ _ _ hG hH n a b hEven
          exact (ih (2 * δ + 2) hrank).even δ rfl
            hG hH a b hEven)
        (fun hαlimit ↦ by
          have hrank : α < γ := by
            rw [hγα]
            exact (Order.lt_succ α).trans_le
              (Ordinal.succ_le_two_mul_add_one α)
          exact (show AlgBFLimitSufficiencyAt.{u} p α from
            (ih α hrank).limit))
    intro G H _ _ _ _ hG hH n a b hOdd
    rcases lt_or_ge (ulmLength p (G := G) hG : Ordinal.{0})
        (ω * α + ω) with hshort | hlong
    · exact hBounded hG hH a b hOdd hshort
    · exact hLong α hG hH a b hOdd hlong
  · intro α hγα
    have hrank : 2 * α + 1 < γ := by
      rw [hγα]
      simpa [Order.succ_eq_add_one, ← one_add_one_eq_two, add_assoc] using
        (Order.lt_succ (2 * α + 1))
    intro G H _ _ _ _ hG hH n a b hEven
    obtain ⟨C⟩ := hEven
    exact bf_even_of_evenData_of_oddSufficiency p hG hH C (by
      intro k u v hOdd
      exact (ih (2 * α + 1) hrank).odd α rfl hH hG u v hOdd)
  · intro hrank
    rcases hrank with hγlimit | hγzero
    · refine (AlgBFLimitSufficiencyAt.of_lower p hγlimit ?_ ?_ ?_)
        (Or.inl hγlimit)
      · intro δ hδ
        exact (ih (2 * δ + 1) hδ).odd δ rfl
      · intro δ hδ
        exact (ih (2 * δ + 2) hδ).even δ rfl
      · intro β hβ
        exact (ih β hβ).limit
    · subst γ
      exact AlgBFLimitSufficiencyAt.zero p (Or.inr rfl)

/-- Global odd sufficiency, conditional only on the isolated long-target
response theorem. -/
theorem acmOddSufficiency_of_oddLong
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (α : Ordinal.{0}) : AlgBFOddSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank_of_oddLong p hLong (2 * α + 1)).odd α rfl

/-- Global even sufficiency under the same isolated long-target hypothesis. -/
theorem acmEvenSufficiency_of_oddLong
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (α : Ordinal.{0}) : AlgBFEvenSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank_of_oddLong p hLong (2 * α + 2)).even α rfl

/-- Global limit/zero sufficiency under the same isolated long-target
hypothesis. -/
theorem acmLimitSufficiency_of_oddLong
    (hLong : ∀ α : Ordinal.{0}, AlgBFOddLongSufficiencyAt.{u} p α)
    (α : Ordinal.{0}) : AlgBFLimitSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank_of_oddLong p hLong α).limit

/-- **The unconditional transfinite sufficiency induction.**

Both target-length branches are now local theorems.  Consequently the same
well-founded induction on the literal relation rank proves the full odd,
even, and limit sufficiency package without an external response hypothesis.
The only recursive calls are at the predecessor ranks listed above. -/
theorem acmSufficiencyAtRank
    (γ : Ordinal.{0}) : ACMSufficiencyAtRank.{u} p γ := by
  refine Ordinal.lt_wf.induction γ ?_
  intro γ ih
  refine {
    odd := ?_
    even := ?_
    limit := ?_ }
  · intro α hγα
    have hSucc : ∀ δ : Ordinal.{0}, α = Order.succ δ →
        AlgBFEvenSufficiencyAt.{u} p δ := fun δ hαsucc ↦ by
      have hrank : 2 * δ + 2 < γ := by
        rw [hγα, hαsucc]
        rw [show 2 * Order.succ δ + 1 =
            Order.succ (2 * δ + 2) by
          rw [Ordinal.mul_succ]
          rfl]
        exact Order.lt_succ _
      intro G H _ _ _ _ hG hH n a b hEven
      exact (ih (2 * δ + 2) hrank).even δ rfl
        hG hH a b hEven
    have hLimit : Order.IsSuccLimit α →
        AlgBFLimitSufficiencyAt.{u} p α := fun _hαlimit ↦ by
      have hrank : α < γ := by
        rw [hγα]
        exact (Order.lt_succ α).trans_le
          (Ordinal.succ_le_two_mul_add_one α)
      exact (ih α hrank).limit
    have hBounded : AlgBFOddBoundedSufficiencyAt.{u} p α :=
      AlgBFOddBoundedSufficiencyAt.of_parameter_cases.{u} p hSucc hLimit
    have hLong : AlgBFOddLongSufficiencyAt.{u} p α :=
      AlgBFOddLongSufficiencyAt.of_parameter_cases.{u} p hSucc hLimit
    intro G H _ _ _ _ hG hH n a b hOdd
    rcases lt_or_ge (ulmLength p (G := G) hG : Ordinal.{0})
        (ω * α + ω) with hshort | hlong
    · exact hBounded hG hH a b hOdd hshort
    · exact hLong hG hH a b hOdd hlong
  · intro α hγα
    have hrank : 2 * α + 1 < γ := by
      rw [hγα]
      simpa [Order.succ_eq_add_one, ← one_add_one_eq_two, add_assoc] using
        (Order.lt_succ (2 * α + 1))
    intro G H _ _ _ _ hG hH n a b hEven
    obtain ⟨C⟩ := hEven
    exact bf_even_of_evenData_of_oddSufficiency p hG hH C (by
      intro k u v hOdd
      exact (ih (2 * α + 1) hrank).odd α rfl hH hG u v hOdd)
  · intro hrank
    rcases hrank with hγlimit | hγzero
    · refine (AlgBFLimitSufficiencyAt.of_lower p hγlimit ?_ ?_ ?_)
        (Or.inl hγlimit)
      · intro δ hδ
        exact (ih (2 * δ + 1) hδ).odd δ rfl
      · intro δ hδ
        exact (ih (2 * δ + 2) hδ).even δ rfl
      · intro β hβ
        exact (ih β hβ).limit
    · subst γ
      exact AlgBFLimitSufficiencyAt.zero p (Or.inr rfl)

/-- The full odd algebraic condition implies the odd back-and-forth relation. -/
theorem acmOddSufficiency
    (α : Ordinal.{0}) : AlgBFOddSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank p (2 * α + 1)).odd α rfl

/-- The full even algebraic condition implies the even relation. -/
theorem acmEvenSufficiency
    (α : Ordinal.{0}) : AlgBFEvenSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank p (2 * α + 2)).even α rfl

/-- The full limit/zero algebraic condition implies the relation. -/
theorem acmLimitSufficiency
    (α : Ordinal.{0}) : AlgBFLimitSufficiencyAt.{u} p α :=
  (acmSufficiencyAtRank p α).limit

/-! ### The transfinite necessity spine

Necessity is organized on the same literal relation-rank spine as
sufficiency.  This is important for the successor reversal: odd parameter
`α` lives at rank `2α+1`, even parameter `α` at rank `2α+2`, and the
limit package at its literal rank.

All three exact fields are now proved.  The even node uses the Hill--room
condition, not the refuted crossed-window sufficient strengthening. -/

/-- Odd necessity at parameter `α`. -/
def AlgBFOddNecessityAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    BFRel p (2 * α + 1) n a b → AlgBFOddCond p hG hH α a b

/-- Exact-even necessity at parameter `α`. -/
def AlgBFEvenNecessityAt (α : Ordinal.{0}) : Prop :=
  ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H),
    BFRel p (2 * α + 2) n a b → AlgBFEvenExactCond p hG hH α a b

/-- Limit/zero necessity at the literal relation rank `α`. -/
def AlgBFLimitNecessityAt (α : Ordinal.{0}) : Prop :=
  (Order.IsSuccLimit α ∨ α = 0) →
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      [Countable G] [Countable H]
      (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      BFRel p α n a b → AlgBFLimitCond p hG hH α a b

/-- The three exact necessity claims at literal back-and-forth rank `γ`.
At a fixed rank the parity fields not matching `γ` are vacuous. -/
structure ACMNecessityAtRank (γ : Ordinal.{0}) : Prop where
  odd : ∀ α : Ordinal.{0}, γ = 2 * α + 1 →
    AlgBFOddNecessityAt.{u} p α
  even : ∀ α : Ordinal.{0}, γ = 2 * α + 2 →
    AlgBFEvenNecessityAt.{u} p α
  limit : AlgBFLimitNecessityAt.{u} p γ

/-- Every literal rank has the complete exact necessity package. -/
theorem acmNecessityAtRank (γ : Ordinal.{0}) :
    ACMNecessityAtRank.{u} p γ := by
  refine {
    odd := ?_
    even := ?_
    limit := ?_ }
  · intro α hγ
    subst γ
    intro G H _ _ _ _ hG hH n a b h
    exact ACMNecessity.odd_necessity_of_BFRel p hG hH h
  · intro α hγ
    subst γ
    intro G H _ _ _ _ hG hH n a b h
    exact ACMNecessity.even_exact_of_BFRel_even p hG hH h
  · intro hrank G H _ _ _ _ hG hH n a b h
    rcases hrank with hlimit | hzero
    · exact ACMNecessity.limit_necessity_of_BFRel p hG hH hlimit h
    · subst γ
      exact (bf_limit_iff_algebraic_zero p hG hH a b).mp h

/-- The complete odd base biconditional for countable reduced ambient groups. -/
theorem bf_one_iff_algebraic_odd_zero
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {n : ℕ} (a : Fin n → G) (b : Fin n → H) :
    BFRel p 1 n a b ↔ AlgBFOddCond p hG hH 0 a b := by
  constructor
  · exact ACMNecessity.odd_zero_necessity_of_BFRel_one p hG hH
  · intro h
    simpa using acmOddSufficiency p 0 hG hH a b h

section FiniteOddBaseCharacterization

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable [Fintype G] [Fintype H]
variable {n : ℕ}

/-- The complete odd biconditional at parameter zero for finite ambient
groups.  This is the first necessity theorem to meet the unconditional
transfinite sufficiency theorem: the forward direction is the finite
whole-source/room--kernel argument, and the reverse direction is the global
ACM induction specialized to rank one. -/
theorem bf_one_iff_algebraic_odd_zero_finite
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p 1 n a b ↔ AlgBFOddCond p hG hH 0 a b := by
  constructor
  · exact ACMNecessity.odd_zero_necessity_of_finite_BFRel_one p hG hH
  · intro hOdd
    simpa using acmOddSufficiency p 0 hG hH a b hOdd

end FiniteOddBaseCharacterization

section MainCharacterization

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}
variable [Countable G] [Countable H]

/-- Theorem 1.2, odd case: `(A, ā) ≤_{2α+1} (B, b̄)` iff the algebraic
odd conditions hold. -/
theorem bf_odd_iff_algebraic
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    BFRel p (2 * α + 1) n a b ↔
      AlgBFOddCond p hG hH α a b := by
  constructor
  · intro hbf
    exact ACMNecessity.odd_necessity_of_BFRel p hG hH hbf
  · exact acmOddSufficiency p α hG hH a b

/-- The exact even Hill--room package characterizes the even successor
relation for arbitrary countable reduced ambient groups. -/
theorem bf_even_iff_algebraic
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    BFRel p (2 * α + 2) n a b ↔
      AlgBFEvenExactCond p hG hH α a b := by
  constructor
  · exact ACMNecessity.even_exact_of_BFRel_even p hG hH
  · rintro ⟨C⟩
    exact bf_even_of_exactEvenData_of_oddSufficiency p hG hH C
      (fun u v hOdd ↦ acmOddSufficiency p α hH hG u v hOdd)

/-- Compatibility name retained for code written during packets E1--E4.
New code should use `bf_even_iff_algebraic`. -/
theorem bf_even_exact_iff_algebraic
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    BFRel p (2 * α + 2) n a b ↔
      AlgBFEvenExactCond p hG hH α a b :=
  bf_even_iff_algebraic p hG hH α a b

/-- The legacy crossed algebraic package is a strong sufficient condition.

The converse is false for arbitrary countable ambient groups: an infinite
direct sum of `Z/p²` absorbs one additional `Z/p` direction in every finite
rank-two game while changing the height-zero marked-graded invariant. -/
theorem bf_even_of_strong_algebraic
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (a : Fin n → G) (b : Fin n → H) :
    AlgBFEvenStrongCond p hG hH α a b →
      BFRel p (2 * α + 2) n a b :=
  acmEvenSufficiency p α hG hH a b

/-- Theorem 1.2, limit/zero case: `(A, ā) ≤_α (B, b̄)` iff the algebraic
limit/zero conditions hold. -/
theorem bf_limit_iff_algebraic
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    (α : Ordinal.{0}) (hα : Order.IsSuccLimit α ∨ α = 0)
    (a : Fin n → G) (b : Fin n → H) :
    BFRel p α n a b ↔
      AlgBFLimitCond p hG hH α a b := by
  constructor
  · intro hbf
    rcases hα with hlimit | hzero
    · exact ACMNecessity.limit_necessity_of_BFRel p hG hH hlimit hbf
    · subst α
      exact (bf_limit_iff_algebraic_zero p hG hH a b).mp hbf
  · exact acmLimitSufficiency p α hα hG hH a b

/-- The three exact biconditionals at one literal relation rank.  Fields whose
parity does not match the rank are vacuous, just as in the sufficiency and
necessity spine structures. -/
structure ACMCharacterizationAtRank (γ : Ordinal.{0}) : Prop where
  odd : ∀ α : Ordinal.{0}, γ = 2 * α + 1 →
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      [Countable G] [Countable H]
      (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      BFRel p γ n a b ↔ AlgBFOddCond p hG hH α a b
  even : ∀ α : Ordinal.{0}, γ = 2 * α + 2 →
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      [Countable G] [Countable H]
      (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      BFRel p γ n a b ↔ AlgBFEvenExactCond p hG hH α a b
  limit : (Order.IsSuccLimit γ ∨ γ = 0) →
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      [Countable G] [Countable H]
      (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      BFRel p γ n a b ↔ AlgBFLimitCond p hG hH γ a b

/-- Every literal rank carries the complete exact characterization package. -/
theorem acmCharacterizationAtRank (γ : Ordinal.{0}) :
    ACMCharacterizationAtRank.{u} p γ := by
  refine {
    odd := ?_
    even := ?_
    limit := ?_ }
  · intro α hγ G H _ _ _ _ hG hH n a b
    subst γ
    exact bf_odd_iff_algebraic p hG hH α a b
  · intro α hγ G H _ _ _ _ hG hH n a b
    subst γ
    exact bf_even_iff_algebraic p hG hH α a b
  · intro hγ G H _ _ _ _ hG hH n a b
    exact bf_limit_iff_algebraic p hG hH γ hγ a b

end MainCharacterization
