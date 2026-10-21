import Lib.PGroups.Heights
import Lib.PGroups.Socle
import Lib.PGroups.UlmInvariants
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Order.KonigLemma

/-!
# Finite socles in reduced primary groups

This file formalizes the classical compactness argument used in the long
branch of the ACM room comparison.  A finite `p`-socle makes every bounded
exponent layer finite.  If the primary group were infinite, finite
pigeonhole plus Koenig's lemma would produce a coherent infinite root chain.
Transfinite induction puts that chain in every Ulm subgroup, contradicting
reducedness.
-/

open Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [AddCommGroup G]

set_option linter.unusedSectionVars false

/-- Elements killed by `p^n`. -/
def pPowerTorsion (n : ℕ) : AddSubgroup G where
  carrier := {x | p ^ n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change p ^ n • (x + y) = 0
    change p ^ n • x = 0 at hx
    change p ^ n • y = 0 at hy
    rw [smul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    simpa [smul_neg, hx]

@[simp] theorem mem_pPowerTorsion (n : ℕ) (x : G) :
    x ∈ pPowerTorsion p n ↔ p ^ n • x = 0 :=
  Iff.rfl

/-- Multiplication by `p` lowers the exponent bound by one. -/
def pPowerTorsionStep (n : ℕ) :
    pPowerTorsion p (n + 1) (G := G) →+
      pPowerTorsion p n (G := G) where
  toFun x := ⟨p • (x : G), by
    change p ^ n • (p • (x : G)) = 0
    rw [← mul_smul, ← pow_succ]
    exact x.property⟩
  map_zero' := Subtype.ext (smul_zero p)
  map_add' x y := Subtype.ext (smul_add p (x : G) (y : G))

/-- The kernel of one exponent-lowering step embeds in the `p`-socle. -/
def pPowerTorsionStepKerToSocle (n : ℕ) :
    (pPowerTorsionStep p n (G := G)).ker → pSocle p (G := G) :=
  fun x => ⟨(x : pPowerTorsion p (n + 1) (G := G)), by
    have hx := x.property
    exact congrArg (fun y : pPowerTorsion p n (G := G) => (y : G)) hx⟩

theorem pPowerTorsionStepKerToSocle_injective (n : ℕ) :
    Function.Injective (pPowerTorsionStepKerToSocle p n (G := G)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : pSocle p (G := G) => (z : G)) hxy

/-- A finite socle makes every bounded-exponent layer finite. -/
theorem finite_pPowerTorsion
    (hP : Set.Finite (pSocle p (G := G) : Set G)) :
    ∀ n : ℕ, Finite (pPowerTorsion p n (G := G)) := by
  intro n
  induction n with
  | zero =>
      apply Set.finite_coe_iff.mp
      have hsingleton : (pPowerTorsion p 0 (G := G) : Set G) = {0} := by
        ext x
        simp [pPowerTorsion]
      rw [hsingleton]
      exact Set.finite_singleton 0
  | succ n ih =>
      letI : Finite (pSocle p (G := G)) := Set.finite_coe_iff.mp hP
      letI : Finite (pPowerTorsionStep p n (G := G)).ker :=
        Finite.of_injective (pPowerTorsionStepKerToSocle p n (G := G))
          (pPowerTorsionStepKerToSocle_injective p n (G := G))
      letI : Fintype (pPowerTorsion p n (G := G)) := Fintype.ofFinite _
      letI : Fintype (pPowerTorsionStep p n (G := G)).ker := Fintype.ofFinite _
      letI : Fintype (pPowerTorsion p (n + 1) (G := G)) :=
        AddGroup.fintypeOfKerOfCodom (pPowerTorsionStep p n (G := G))
      infer_instance

/-- Once a power of `p` kills an element, every larger power does too. -/
theorem pPow_nsmul_eq_zero_mono {m n : ℕ} {x : G} (hmn : m ≤ n)
    (hx : p ^ m • x = 0) :
    p ^ n • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [show m + k = k + m by omega, pow_add, mul_smul, hx, smul_zero]

/-- In an infinite primary group with finite socle, arbitrarily deep roots of
some nonzero socle element exist (the element may still depend on the depth). -/
theorem exists_nonzero_pSocle_with_root
    [Infinite G]
    (hprimary : IsPrimaryPGroup p G)
    (hP : Set.Finite (pSocle p (G := G) : Set G))
    (n : ℕ) :
    ∃ c : pSocle p (G := G), (c : G) ≠ 0 ∧
      ∃ x : G, p ^ n • x = (c : G) := by
  classical
  have hbounded : Set.Finite (pPowerTorsion p (n + 1) (G := G) : Set G) :=
    Set.finite_coe_iff.mpr (finite_pPowerTorsion p hP (n + 1))
  obtain ⟨x, hx⟩ : ∃ x : G, x ∉ pPowerTorsion p (n + 1) := by
    by_contra h
    push Not at h
    have huniv : (Set.univ : Set G).Finite := hbounded.subset (fun x _ => h x)
    exact Set.infinite_univ huniv
  have hxpow : p ^ (n + 1) • x ≠ 0 := by
    simpa [pPowerTorsion] using hx
  let m : ℕ := Nat.find (hprimary x)
  have hmzero : p ^ m • x = 0 := Nat.find_spec (hprimary x)
  have hmn : n + 1 < m := by
    apply lt_of_not_ge
    intro hmle
    exact hxpow (pPow_nsmul_eq_zero_mono p hmle hmzero)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by omega)
  have hnk : n ≤ k := by omega
  let y : G := p ^ (k - n) • x
  let c : G := p ^ k • x
  have hcroot : p ^ n • y = c := by
    simp only [y, c, ← mul_smul, ← pow_add]
    rw [Nat.add_sub_of_le hnk]
  have hcne : c ≠ 0 := by
    exact Nat.find_min (hprimary x) (by omega)
  have hcsocle : c ∈ pSocle p (G := G) := by
    change p • c = 0
    simp only [c, ← mul_smul]
    rw [mul_comm, ← pow_succ, ← hk]
    exact hmzero
  exact ⟨⟨c, hcsocle⟩, hcne, y, hcroot⟩

/-- Finite pigeonhole makes the nonzero socle element independent of the
requested root depth. -/
theorem exists_nonzero_pSocle_with_all_roots
    [Infinite G]
    (hprimary : IsPrimaryPGroup p G)
    (hP : Set.Finite (pSocle p (G := G) : Set G)) :
    ∃ c : pSocle p (G := G), (c : G) ≠ 0 ∧
      ∀ n : ℕ, ∃ x : G, p ^ n • x = (c : G) := by
  classical
  let C := {c : pSocle p (G := G) // (c : G) ≠ 0}
  letI : Finite (pSocle p (G := G)) := Set.finite_coe_iff.mp hP
  letI : Finite C := Finite.of_injective (fun c : C => (c : pSocle p (G := G)))
    (fun _ _ h => Subtype.ext h)
  let cAt : ℕ → C := fun n =>
    ⟨Classical.choose (exists_nonzero_pSocle_with_root p hprimary hP n),
      (Classical.choose_spec
        (exists_nonzero_pSocle_with_root p hprimary hP n)).1⟩
  have hcAtRoot : ∀ n : ℕ, ∃ x : G, p ^ n • x = (cAt n : G) := by
    intro n
    exact (Classical.choose_spec
      (exists_nonzero_pSocle_with_root p hprimary hP n)).2
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber cAt
  refine ⟨(c : pSocle p (G := G)), c.property, ?_⟩
  intro n
  have hfiber : (cAt ⁻¹' {c}).Infinite := Set.infinite_coe_iff.mp hc
  obtain ⟨m, hm, hnm⟩ := hfiber.exists_gt n
  obtain ⟨y, hy⟩ := hcAtRoot m
  refine ⟨p ^ (m - n) • y, ?_⟩
  simp only [← mul_smul, ← pow_add]
  rw [Nat.add_sub_of_le (le_of_lt hnm), hy]
  exact congrArg (fun z : C => (z : G)) hm

/-! ### Koenig compactness -/

/-- The type of `n`-fold roots of a fixed element. -/
def pRoot (c : G) (n : ℕ) :=
  {x : G // p ^ n • x = c}

/-- A root of a socle element is killed by the next power of `p`. -/
def pRootToPowerTorsion (c : pSocle p (G := G)) (n : ℕ) :
    pRoot p (c : G) n → pPowerTorsion p (n + 1) (G := G) :=
  fun x => ⟨x.1, by
    calc
      p ^ (n + 1) • x.1 = p • (p ^ n • x.1) := by
        rw [pow_succ, mul_smul, smul_comm]
      _ = p • (c : G) := congrArg (fun y : G => p • y) x.property
      _ = 0 := c.property⟩

theorem pRootToPowerTorsion_injective (c : pSocle p (G := G)) (n : ℕ) :
    Function.Injective (pRootToPowerTorsion p c n) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : pPowerTorsion p (n + 1) (G := G) => (z : G)) hxy

/-- Root sets of a socle element are finite when the whole socle is finite. -/
theorem finite_pRoot
    (hP : Set.Finite (pSocle p (G := G) : Set G))
    (c : pSocle p (G := G)) (n : ℕ) :
    Finite (pRoot p (c : G) n) := by
  letI : Finite (pPowerTorsion p (n + 1) (G := G)) :=
    finite_pPowerTorsion p hP (n + 1)
  exact Finite.of_injective (pRootToPowerTorsion p c n)
    (pRootToPowerTorsion_injective p c n)

/-- Projection from deeper roots to shallower roots. -/
def pRootProjection (c : G) {i j : ℕ} (hij : i ≤ j) :
    pRoot p c j → pRoot p c i :=
  fun x => ⟨p ^ (j - i) • x.1, by
    calc
      p ^ i • (p ^ (j - i) • x.1) = p ^ j • x.1 := by
        simp only [← mul_smul, ← pow_add]
        rw [Nat.add_sub_of_le hij]
      _ = c := x.property⟩

@[simp] theorem pRootProjection_refl (c : G) (i : ℕ)
    (x : pRoot p c i) :
    pRootProjection p c (le_refl i) x = x := by
  apply Subtype.ext
  change p ^ (i - i) • x.1 = x.1
  simp

theorem pRootProjection_trans (c : G) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (x : pRoot p c k) :
    pRootProjection p c hij (pRootProjection p c hjk x) =
      pRootProjection p c (hij.trans hjk) x := by
  apply Subtype.ext
  change p ^ (j - i) • (p ^ (k - j) • x.1) =
    p ^ (k - i) • x.1
  simp only [← mul_smul, ← pow_add]
  rw [add_comm, Nat.sub_add_sub_cancel hjk hij]

/-- Nonempty finite root sets admit a coherent infinite root chain. -/
theorem exists_coherent_root_chain
    (hP : Set.Finite (pSocle p (G := G) : Set G))
    (c : pSocle p (G := G))
    (hroots : ∀ n : ℕ, ∃ x : G, p ^ n • x = (c : G)) :
    ∃ f : ℕ → G, f 0 = (c : G) ∧
      ∀ n : ℕ, p • f (n + 1) = f n := by
  letI : ∀ n : ℕ, Finite (pRoot p (c : G) n) := fun n =>
    finite_pRoot p hP c n
  letI : ∀ n : ℕ, Nonempty (pRoot p (c : G) n) := fun n => by
    obtain ⟨x, hx⟩ := hroots n
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨r, hr⟩ := exists_seq_forall_proj_of_forall_finite
    (fun {_i _j} hij => pRootProjection p (c : G) hij)
    (fun {_i} x => pRootProjection_refl p (c : G) _i x)
    (fun {_i _j _k} hij hjk x =>
      pRootProjection_trans p (c : G) hij hjk x)
    (fun i a => Set.toFinite _)
  refine ⟨fun n => (r n).1, ?_, ?_⟩
  · simpa [pRoot] using (r 0).property
  · intro n
    have h := congrArg (fun z : pRoot p (c : G) n => z.1)
      (hr (Nat.le_succ n))
    simpa [pRootProjection] using h

/-- A coherent root chain lies in every transfinite Ulm subgroup. -/
theorem coherent_root_chain_mem_ulmSubgroup
    (f : ℕ → G) (hstep : ∀ n : ℕ, p • f (n + 1) = f n) :
    ∀ (α : Ordinal.{0}) (n : ℕ), f n ∈ ulmSubgroup p α (G := G) := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro n
      simp [ulmSubgroup]
  | succ α ih =>
      intro n
      rw [mem_ulmSubgroup_succ_iff (p := p) (G := G)]
      exact ⟨f (n + 1), ih (n + 1), hstep n⟩
  | limit o ho IH =>
      intro n
      rw [mem_ulmSubgroup_limit_iff (p := p) (G := G) ho]
      intro β hβ
      exact IH β hβ n

/-- **Finite socle theorem.** A reduced primary abelian `p`-group with finite
`p`-socle is finite. -/
theorem finite_of_finite_pSocle
    (hred : IsReducedPGroup p G)
    (hP : Set.Finite (pSocle p (G := G) : Set G)) :
    Finite G := by
  apply not_infinite_iff_finite.mp
  intro hInfinite
  letI : Infinite G := hInfinite
  obtain ⟨c, hcne, hroots⟩ :=
    exists_nonzero_pSocle_with_all_roots p hred.primary hP
  obtain ⟨f, hfzero, hfstep⟩ :=
    exists_coherent_root_chain p hP c hroots
  obtain ⟨α, hα⟩ := hred.reduced
  have hcα := coherent_root_chain_mem_ulmSubgroup p f hfstep α 0
  rw [hfzero, hα] at hcα
  exact hcne (AddSubgroup.mem_bot.mp hcα)

/-! ### Ulm tails -/

/-- Every Ulm subgroup of a reduced primary group is itself reduced primary. -/
theorem ulmSubgroup_isReducedPGroup
    (hG : IsReducedPGroup p G) (β : Ordinal.{0}) :
    IsReducedPGroup p (ulmSubgroup p β (G := G)) := by
  constructor
  · intro x
    obtain ⟨n, hn⟩ := hG.primary (x : G)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  · obtain ⟨α, hα⟩ := hG.reduced
    refine ⟨α, ?_⟩
    apply le_bot_iff.mp
    intro x hx
    apply AddSubgroup.mem_bot.mpr
    apply Subtype.ext
    have hmap : ((x : ulmSubgroup p β (G := G)) : G) ∈
        (ulmSubgroup p α (G := ulmSubgroup p β (G := G))).map
          (ulmSubgroup p β (G := G)).subtype :=
      ⟨x, hx, rfl⟩
    have hambient := map_ulmSubgroup_le p
      (ulmSubgroup p β (G := G)).subtype α hmap
    rw [hα] at hambient
    exact AddSubgroup.mem_bot.mp hambient

/-- The socle of an Ulm subgroup embeds into the corresponding filtered
ambient socle. -/
def pSocleUlmToFilteredSocle (β : Ordinal.{0}) :
    pSocle p (G := ulmSubgroup p β (G := G)) →
      pSocleAt p β (G := G) :=
  fun x => ⟨((x : ulmSubgroup p β (G := G)) : G), by
    constructor
    · exact congrArg
        (fun y : ulmSubgroup p β (G := G) => (y : G)) x.property
    · exact (x : ulmSubgroup p β (G := G)).property⟩

theorem pSocleUlmToFilteredSocle_injective (β : Ordinal.{0}) :
    Function.Injective (pSocleUlmToFilteredSocle p (G := G) β) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : pSocleAt p β (G := G) => (z : G)) hxy

/-- A finite filtered socle makes the whole corresponding Ulm tail finite. -/
theorem finite_ulmSubgroup_of_finite_pSocleAt
    (hG : IsReducedPGroup p G) (β : Ordinal.{0})
    (hP : Set.Finite (pSocleAt p β (G := G) : Set G)) :
    Finite (ulmSubgroup p β (G := G)) := by
  letI : Finite (pSocleAt p β (G := G)) := Set.finite_coe_iff.mpr hP
  letI : Finite (pSocle p (G := ulmSubgroup p β (G := G))) :=
    Finite.of_injective (pSocleUlmToFilteredSocle p (G := G) β)
      (pSocleUlmToFilteredSocle_injective p (G := G) β)
  exact finite_of_finite_pSocle p (ulmSubgroup_isReducedPGroup p hG β)
    (Set.finite_coe_iff.mp inferInstance)

/-- A finite primary group has a uniform `p`-power exponent. -/
theorem finite_primary_bounded_exponent
    {K : Type u} [AddCommGroup K] [Finite K]
    (hK : IsPrimaryPGroup p K) :
    ∃ n : ℕ, ∀ x : K, p ^ n • x = 0 := by
  classical
  letI := Fintype.ofFinite K
  let e : K → ℕ := fun x => Classical.choose (hK x)
  have he : ∀ x : K, p ^ e x • x = 0 := fun x =>
    Classical.choose_spec (hK x)
  let N : ℕ := ∑ x : K, e x
  refine ⟨N, fun x => ?_⟩
  have hex : e x ≤ N :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  exact pPow_nsmul_eq_zero_mono p hex (he x)

/-- A finite filtered socle forces its Ulm tail to vanish after finitely many
successor steps. -/
theorem exists_ulmSubgroup_add_nat_eq_bot_of_finite_pSocleAt
    (hG : IsReducedPGroup p G) (β : Ordinal.{0})
    (hP : Set.Finite (pSocleAt p β (G := G) : Set G)) :
    ∃ n : ℕ, ulmSubgroup p (β + n) (G := G) = ⊥ := by
  letI : Finite (ulmSubgroup p β (G := G)) :=
    finite_ulmSubgroup_of_finite_pSocleAt p hG β hP
  obtain ⟨n, hn⟩ := finite_primary_bounded_exponent p
    (ulmSubgroup_isReducedPGroup p hG β).primary
  refine ⟨n, ?_⟩
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    (mem_ulmSubgroup_add_nat_iff (p := p) (G := G) β n x).mp hx
  apply AddSubgroup.mem_bot.mpr
  calc
    x = p ^ n • y := hxy.symm
    _ = 0 := congrArg
      (fun z : ulmSubgroup p β (G := G) => (z : G)) (hn ⟨y, hy⟩)

/-- Finite filtered socle implies that the global Ulm length is strictly below
the next omega boundary. -/
theorem ulmLength_lt_add_omega_of_finite_pSocleAt
    (hG : IsReducedPGroup p G) (β : Ordinal.{0})
    (hP : Set.Finite (pSocleAt p β (G := G) : Set G)) :
    (ulmLength p (G := G) hG : Ordinal.{0}) < β + ω := by
  obtain ⟨n, hn⟩ :=
    exists_ulmSubgroup_add_nat_eq_bot_of_finite_pSocleAt p hG β hP
  have hlength : (ulmLength p (G := G) hG : Ordinal.{0}) ≤ β + n := by
    unfold ulmLength
    exact csInf_le ⟨0, fun _ _ => bot_le⟩ hn
  exact hlength.trans_lt (by
    rw [add_lt_add_iff_left]
    exact Ordinal.natCast_lt_omega0 n)

/-- **Kaplansky long-socle consequence.** If the Ulm length reaches the omega
boundary above `β`, then the filtered socle at `β` is infinite. -/
theorem infinite_pSocleAt_of_add_omega_le_ulmLength
    (hG : IsReducedPGroup p G) (β : Ordinal.{0})
    (hlong : β + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0})) :
    Set.Infinite (pSocleAt p β (G := G) : Set G) := by
  intro hfinite
  exact (not_lt_of_ge hlong)
    (ulmLength_lt_add_omega_of_finite_pSocleAt p hG β hfinite)
