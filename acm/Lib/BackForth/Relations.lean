import Lib.PGroups.UlmInvariants
import Lib.Ulm.Pure
import Lib.Scott.Tuples

/-!
# Back-and-forth relations for abelian p-groups

We formalize the back-and-forth relations from Alvir–Csima–MacLean (ACM),
which characterize when two tuples in reduced abelian p-groups are
ordinal-indexed back-and-forth equivalent.

## The back-and-forth relations

Fix countable reduced abelian p-groups G and H, and a prime p.
For tuples ā = (a₁,…,aₖ) in G and b̄ = (b₁,…,bₖ) in H:

  (G, ā) ≤_α (H, b̄)  ("ā is α-back-and-forth below b̄")

is defined by ordinal recursion:
- (G, ā) ≤_0 (H, b̄) iff the map aᵢ ↦ bᵢ extends to an isomorphism
  of generated subgroups (equivalently, the tuples have the same atomic diagram).
- (G, ā) ≤_{α+1} (H, b̄) iff for every finite tuple c̄ from H there is a
  matching tuple d̄ from G with (H, b̄c̄) ≤_α (G, ād̄). The structures reverse
  at every successor.
- At a nonzero limit λ, the relation holds iff it holds at every α < λ.

## References
- Alvir–Csima–MacLean, "Scott complexity of countable reduced abelian p-groups"
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

section BFRelDef

variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-! ### Base relation -/

/-- The base back-and-forth relation: the tuples have the same atomic diagram,
equivalently the map `aᵢ ↦ bᵢ` extends to an isomorphism of their generated
subgroups. Ambient heights are not atomic data and enter only at later stages. -/
def BFBase (_q : ℕ) (k : ℕ) (a : Fin k → G) (b : Fin k → H) : Prop :=
  ∃ φ : AddSubgroup.closure (Set.range a) ≃+ AddSubgroup.closure (Set.range b),
    ∀ i : Fin k,
      φ ⟨a i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩ =
        ⟨b i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩

/-- The atomic-diagram relation is symmetric. -/
theorem BFBase.symm {q k : ℕ} {a : Fin k → G} {b : Fin k → H} :
    BFBase q k a b → BFBase q k b a := by
  rintro ⟨φ, hφ⟩
  refine ⟨φ.symm, ?_⟩
  intro i
  rw [← hφ i]
  simp

/-- Atomic diagrams restrict to any selected list of tuple coordinates. -/
theorem BFBase.reindex
    {q n m : ℕ} {a : Fin n → G} {b : Fin n → H}
    (e : Fin m → Fin n) :
    BFBase q n a b → BFBase q m (a ∘ e) (b ∘ e) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨φ', hφ'⟩ := (TupleIsoMap.ofBase φ hφ).reindex e |>.toBase
  exact ⟨φ', hφ'⟩

/-! ### The directional back-and-forth system -/

/-- A family of tuple relations from `G` to `H`, simultaneously for every arity. -/
private abbrev BFRelation (G H : Type u) :=
  (k : ℕ) → (Fin k → G) → (Fin k → H) → Prop

/-- The two orientations are defined together so that a successor can reverse them.
The first component is `G → H`; the second is `H → G`. -/
private noncomputable def bfRelPair (q : ℕ) :
    (α : Ordinal.{0}) → BFRelation G H × BFRelation H G :=
  fun α =>
    Ordinal.limitRecOn α
      ⟨(fun k a b => BFBase q k a b),
        (fun k b a => BFBase q k b a)⟩
      (fun _ prev =>
        ⟨(fun k a b =>
            ∀ (m : ℕ) (c : Fin m → H), ∃ d : Fin m → G,
              prev.2 (k + m) (Fin.append b c) (Fin.append a d)),
          (fun k b a =>
            ∀ (m : ℕ) (d : Fin m → G), ∃ c : Fin m → H,
              prev.1 (k + m) (Fin.append a d) (Fin.append b c))⟩)
      (fun α _ prev =>
        ⟨(fun k a b => ∀ β (hβ : β < α), (prev β hβ).1 k a b),
          (fun k b a => ∀ β (hβ : β < α), (prev β hβ).2 k b a)⟩)

/-- The ordinal-indexed directional back-and-forth preorder on tuples.
At successors the structures reverse; at nonzero limits it is the intersection
of all earlier relations in the same orientation. -/
noncomputable def BFRel (q : ℕ) (α : Ordinal.{0}) : BFRelation G H :=
  (bfRelPair (G := G) (H := H) q α).1

/-- The reverse orientation paired with `BFRel`. It is exposed so the successor
equation states, and regression-tests, the required structure reversal directly. -/
noncomputable def BFRelReverse (q : ℕ) (α : Ordinal.{0}) : BFRelation H G :=
  (bfRelPair (G := G) (H := H) q α).2

@[simp] theorem BFRel_zero (q : ℕ) (k : ℕ) (a : Fin k → G) (b : Fin k → H) :
    BFRel q 0 k a b ↔ BFBase q k a b := by
  simp [BFRel, bfRelPair]

@[simp] theorem BFRelReverse_zero
    (q : ℕ) (k : ℕ) (b : Fin k → H) (a : Fin k → G) :
    BFRelReverse q 0 k b a ↔ BFBase q k b a := by
  simp [BFRelReverse, bfRelPair]

@[simp] theorem BFRel_succ
    (q : ℕ) (α : Ordinal.{0}) (k : ℕ) (a : Fin k → G) (b : Fin k → H) :
    BFRel q (Order.succ α) k a b ↔
      ∀ (m : ℕ) (c : Fin m → H), ∃ d : Fin m → G,
        BFRelReverse q α (k + m) (Fin.append b c) (Fin.append a d) := by
  unfold BFRel BFRelReverse bfRelPair
  rw [Ordinal.limitRecOn_succ]

@[simp] theorem BFRelReverse_succ
    (q : ℕ) (α : Ordinal.{0}) (k : ℕ) (b : Fin k → H) (a : Fin k → G) :
    BFRelReverse q (Order.succ α) k b a ↔
      ∀ (m : ℕ) (d : Fin m → G), ∃ c : Fin m → H,
        BFRel q α (k + m) (Fin.append a d) (Fin.append b c) := by
  unfold BFRel BFRelReverse bfRelPair
  rw [Ordinal.limitRecOn_succ]

@[simp] theorem BFRel_limit
    (q : ℕ) (o : Ordinal.{0}) (ho : Order.IsSuccLimit o)
    (k : ℕ) (a : Fin k → G) (b : Fin k → H) :
    BFRel q o k a b ↔
      ∀ β (_hβ : β < o), BFRel q β k a b := by
  unfold BFRel bfRelPair
  rw [Ordinal.limitRecOn_limit _ _ _ _ ho]

@[simp] theorem BFRelReverse_limit
    (q : ℕ) (o : Ordinal.{0}) (ho : Order.IsSuccLimit o)
    (k : ℕ) (b : Fin k → H) (a : Fin k → G) :
    BFRelReverse q o k b a ↔
      ∀ β (_hβ : β < o), BFRelReverse q β k b a := by
  unfold BFRelReverse bfRelPair
  rw [Ordinal.limitRecOn_limit _ _ _ _ ho]

/-- The second component of the mutually recursive definition is extensionally
the ordinary relation with the ambient types swapped.  This is deliberately an
explicit theorem, rather than a definitional reduction: successor recursion
uses the opposite component of the pair. -/
theorem BFRelReverse_iff_BFRel_swap (q : ℕ) (α : Ordinal.{0}) :
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      (k : ℕ) (b : Fin k → H) (a : Fin k → G),
      BFRelReverse q α k b a ↔
        BFRel (G := H) (H := G) q α k b a := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro G H _ _ k b a
      rw [BFRelReverse_zero, BFRel_zero]
  | succ α ih =>
      intro G H _ _ k b a
      rw [BFRelReverse_succ, BFRel_succ]
      constructor
      · intro h m d
        obtain ⟨c, hc⟩ := h m d
        exact ⟨c, (ih (G := H) (H := G) (k + m)
          (Fin.append a d) (Fin.append b c)).mpr hc⟩
      · intro h m d
        obtain ⟨c, hc⟩ := h m d
        exact ⟨c, (ih (G := H) (H := G) (k + m)
          (Fin.append a d) (Fin.append b c)).mp hc⟩
  | limit o ho ih =>
      intro G H _ _ k b a
      rw [BFRelReverse_limit q o ho, BFRel_limit q o ho]
      constructor
      · intro h β hβ
        exact (ih β hβ (G := G) (H := H) k b a).mp (h β hβ)
      · intro h β hβ
        exact (ih β hβ (G := G) (H := H) k b a).mpr (h β hβ)

/-- Back-and-forth relations weaken along any selection of tuple coordinates.

This is the formal operation used to discard challenge coordinates.  The
selector need not be injective. -/
theorem BFRel_reindex (q : ℕ) (α : Ordinal.{0}) :
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      {n m : ℕ} (a : Fin n → G) (b : Fin n → H) (e : Fin m → Fin n),
      BFRel q α n a b → BFRel q α m (a ∘ e) (b ∘ e) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro G H _ _ n m a b e h
      rw [BFRel_zero] at h ⊢
      exact BFBase.reindex e h
  | succ α ih =>
      intro G H _ _ n m a b e h
      rw [BFRel_succ] at h ⊢
      intro r c
      obtain ⟨d, hd⟩ := h r c
      refine ⟨d, ?_⟩
      rw [BFRelReverse_iff_BFRel_swap] at hd ⊢
      let e' : Fin (m + r) → Fin (n + r) :=
        Fin.append (fun i ↦ (e i).castAdd r) (fun j ↦ Fin.natAdd n j)
      have hreindex := ih (G := H) (H := G)
        (Fin.append b c) (Fin.append a d) e' hd
      have hb : (Fin.append b c) ∘ e' = Fin.append (b ∘ e) c := by
        funext i
        refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
          simp [e', Function.comp_def]
      have ha : (Fin.append a d) ∘ e' = Fin.append (a ∘ e) d := by
        funext i
        refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
          simp [e', Function.comp_def]
      rwa [hb, ha] at hreindex
  | limit o ho ih =>
      intro G H _ _ n m a b e h
      rw [BFRel_limit q o ho] at h ⊢
      intro β hβ
      exact ih β hβ a b e (h β hβ)

/-- One successor rank implies the preceding rank in the same orientation.

This is not definitional for the directional relation: the successor response
is oriented backwards.  The proof descends through that response and, at a
limit predecessor, reconstructs every lower rank. -/
theorem BFRel_succ_self (q : ℕ) (α : Ordinal.{0}) :
    ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
      {n : ℕ} (a : Fin n → G) (b : Fin n → H),
      BFRel q (Order.succ α) n a b → BFRel q α n a b := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro G H _ _ n a b h
      rw [BFRel_succ] at h
      let zH : Fin 0 → H := Fin.elim0
      obtain ⟨d, hd⟩ := h 0 zH
      rw [BFRelReverse_iff_BFRel_swap] at hd
      rw [BFRel_zero] at hd ⊢
      have hd0 : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
      subst d
      exact BFBase.symm (by simpa [zH] using hd)
  | succ α ih =>
      intro G H _ _ n a b h
      rw [BFRel_succ] at h ⊢
      intro m c
      obtain ⟨d, hd⟩ := h m c
      refine ⟨d, ?_⟩
      rw [BFRelReverse_iff_BFRel_swap] at hd ⊢
      exact ih (G := H) (H := G) (Fin.append b c) (Fin.append a d) hd
  | limit o ho ih =>
      intro G H _ _ n a b h
      rw [BFRel_succ] at h
      rw [BFRel_limit q o ho]
      intro β hβ
      apply ih β hβ a b
      rw [BFRel_succ]
      intro m c
      obtain ⟨d, hd⟩ := h m c
      refine ⟨d, ?_⟩
      rw [BFRelReverse_iff_BFRel_swap] at hd ⊢
      rw [BFRel_limit q o ho] at hd
      exact hd β hβ

/-- Higher ranks imply lower ranks in the same orientation. -/
theorem BFRel_antitone (q : ℕ) :
    ∀ {α β : Ordinal.{0}}, β ≤ α →
      ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H]
        {n : ℕ} (a : Fin n → G) (b : Fin n → H),
        BFRel q α n a b → BFRel q β n a b := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro β hβ G H _ _ n a b h
      have hβ0 : β = 0 := nonpos_iff_eq_zero.mp hβ
      simpa [hβ0] using h
  | succ α ih =>
      intro β hβ G H _ _ n a b h
      rcases hβ.eq_or_lt with rfl | hβlt
      · exact h
      · have hβα : β ≤ α := by
          exact Order.lt_succ_iff.mp hβlt
        exact ih hβα a b (BFRel_succ_self q α a b h)
  | limit o ho ih =>
      intro β hβ G H _ _ n a b h
      rcases hβ.eq_or_lt with rfl | hβlt
      · exact h
      · rw [BFRel_limit q o ho] at h
        exact h β hβlt

/-- At a nonzero limit rank the directional relation is symmetric.

For each lower rank `β`, use the original limit relation at `succ β` and
answer the empty challenge.  The successor reversal supplies the desired
opposite orientation at `β`, and the limit equation reassembles those lower
ranks. -/
theorem BFRel_symm_of_isSuccLimit (q : ℕ)
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (a : Fin n → G) (b : Fin n → H) :
    BFRel q α n a b → BFRel q α n b a := by
  intro h
  rw [BFRel_limit q α hα] at h ⊢
  intro β hβ
  have hsucc : Order.succ β < α := hα.succ_lt hβ
  have hs := h (Order.succ β) hsucc
  rw [BFRel_succ] at hs
  obtain ⟨d, hd⟩ := hs 0 Fin.elim0
  have hd0 : d = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst d
  have hd' : BFRelReverse q β n b a := by
    simpa using hd
  exact (BFRelReverse_iff_BFRel_swap q β n b a).mp hd'

/-- The recursive relation agrees with the paper's positive-rank definition.

For every `α > 0`, `(G,a) ≤_α (H,b)` holds exactly when every finite tuple
challenge from `H` can be answered at every rank `β < α` in the reversed
orientation.  This is the induction interface used in ACM Definition 1.1 and
in the proof of the limit case of Theorem 4.4. -/
theorem BFRel_positive_iff
    (q : ℕ) (α : Ordinal.{0}) (hα : α ≠ 0)
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} (a : Fin n → G) (b : Fin n → H) :
    BFRel q α n a b ↔
      ∀ β (_hβ : β < α) (m : ℕ) (c : Fin m → H), ∃ d : Fin m → G,
        BFRelReverse q β (n + m) (Fin.append b c) (Fin.append a d) := by
  constructor
  · intro h β hβ m c
    have hsucc : BFRel q (Order.succ β) n a b :=
      BFRel_antitone q (Order.succ_le_of_lt hβ) a b h
    rw [BFRel_succ] at hsucc
    exact hsucc m c
  · intro h
    rcases Order.isMin_or_mem_range_succ_or_isSuccLimit α with hzero | hsucc | hlimit
    · have : α = 0 := isMin_iff_eq_bot.mp hzero
      exact (hα this).elim
    · obtain ⟨β, rfl⟩ := hsucc
      rw [BFRel_succ]
      exact h β (Order.lt_succ β)
    · rw [BFRel_limit q α hlimit]
      intro β hβ
      apply BFRel_succ_self q β a b
      rw [BFRel_succ]
      exact h β hβ

/-- Every back-and-forth relation carries the current atomic tuple map.

This is the common necessity proof of the tuple-isomorphism clause in all
three algebraic packages. -/
theorem tupleIsoMap_of_BFRel
    (q : ℕ) (α : Ordinal.{0})
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel q α n a b) : Nonempty (TupleIsoMap a b) := by
  have hzero : BFRel q 0 n a b :=
    BFRel_antitone q (zero_le α) a b h
  rw [BFRel_zero] at hzero
  obtain ⟨φ, hφ⟩ := hzero
  exact ⟨TupleIsoMap.ofBase φ hφ⟩

/-- A positive-rank relation answers an arbitrary finite challenge already at
atomic rank, producing one concrete isomorphism of the enlarged generated
subgroups.  This is the finite local object used by algebraic necessity. -/
theorem exists_finiteTuple_baseResponse_of_BFRel
    (q : ℕ) {α : Ordinal.{0}} (hα : α ≠ 0)
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    {n : ℕ} {a : Fin n → G} {b : Fin n → H}
    (h : BFRel q α n a b) {m : ℕ} (d : Fin m → H) :
    ∃ c : Fin m → G, Nonempty
      (TupleIsoMap (Fin.append a c) (Fin.append b d)) := by
  obtain ⟨c, hbase⟩ :=
    (BFRel_positive_iff q α hα a b).mp h 0 (pos_iff_ne_zero.mpr hα) m d
  rw [BFRelReverse_zero] at hbase
  obtain ⟨φ, hφ⟩ := BFBase.symm hbase
  exact ⟨c, ⟨TupleIsoMap.ofBase φ hφ⟩⟩

end BFRelDef

namespace Ordinal

/-- Multiplication on the left by `2` fixes every nonzero limit ordinal.

This is the ordinal-arithmetic normalization behind the limit-parameter odd
case: if `α` is a limit then the predecessor of rank `2 * α + 1` is literally
rank `α`. -/
theorem two_mul_eq_self_of_isSuccLimit {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) : 2 * α = α := by
  apply mul_omega0_dvd (a := (2 : Ordinal.{0})) (by norm_num)
    (natCast_lt_omega0 2)
  exact isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit

/-- A successor parameter lies below its associated odd relation rank. -/
theorem succ_le_two_mul_add_one (α : Ordinal.{0}) :
    Order.succ α ≤ 2 * α + 1 := by
  have hα : α ≤ 2 * α := le_mul_right α (by norm_num)
  simpa [Order.succ_eq_add_one] using
    (Ordinal.add_le_add_iff_right (a := α) (b := 2 * α) 1).2 hα

/-- Every ordinal below `2` is `0` or `1`. -/
theorem lt_two_cases {r : Ordinal.{0}} (hr : r < 2) : r = 0 ∨ r = 1 := by
  rcases Order.isMin_or_mem_range_succ_or_isSuccLimit r with hzero | hsucc | hlimit
  · exact Or.inl (isMin_iff_eq_bot.mp hzero)
  · obtain ⟨a, rfl⟩ := hsucc
    right
    have ha : a < 1 := Order.succ_lt_succ_iff.mp (by simpa using hr)
    have ha0 : a = 0 := Order.lt_one_iff.mp ha
    simp [ha0]
  · have hone : (1 : Ordinal.{0}) < r := one_lt_of_isSuccLimit hlimit
    have htwo : 2 < r := by
      rw [← one_add_one_eq_two, ← Order.succ_eq_add_one]
      exact hlimit.succ_lt hone
    exact (not_lt_of_ge hr.le htwo).elim

/-- Every relation rank is zero, odd, positive even, or a nonzero limit.

This is the exhaustive partition used in the ACM induction.  Ordinal division
is on the left: `2 * (γ / 2) + γ % 2 = γ`. -/
theorem zero_odd_even_limit_cases (γ : Ordinal.{0}) :
    γ = 0 ∨
      (∃ α : Ordinal.{0}, γ = 2 * α + 1) ∨
      (∃ α : Ordinal.{0}, γ = 2 * α + 2) ∨
      Order.IsSuccLimit γ := by
  have hr : γ % 2 = 0 ∨ γ % 2 = 1 :=
    lt_two_cases (mod_lt γ (by norm_num))
  have hdecomp := div_add_mod γ 2
  rcases hr with hr | hr
  · rw [hr, add_zero] at hdecomp
    rcases Order.isMin_or_mem_range_succ_or_isSuccLimit (γ / 2) with
      hzero | hsucc | hlimit
    · left
      rw [isMin_iff_eq_bot.mp hzero] at hdecomp
      simpa using hdecomp.symm
    · obtain ⟨α, hα⟩ := hsucc
      right
      right
      left
      refine ⟨α, ?_⟩
      rw [← hα, mul_succ] at hdecomp
      simpa using hdecomp.symm
    · right
      right
      right
      rw [← hdecomp]
      exact isSuccLimit_mul_right (by norm_num) hlimit
  · right
    left
    refine ⟨γ / 2, ?_⟩
    simpa [hr] using hdecomp.symm

end Ordinal
