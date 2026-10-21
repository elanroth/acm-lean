import Lib.BackForth.SocleLift
import Lib.BackForth.FilteredBasis
import Lib.Ulm.Extension

/-!
# The exact finite marked-embedding criterion

This file assembles the finite-source theorem behind the D-23 room--kernel
budget.  The finiteness hypotheses here are deliberately hypotheses on the
ambient source group.  They must not later be reused for a finite subgroup of
an infinite source, whose intrinsic Ulm filtration need not agree with the
ambient filtration.
-/

noncomputable section

open Module Ordinal

universe u v

variable (p : ℕ) [hp : Fact p.Prime]

namespace FiniteEmbedding

section FiniteFilteredBasis

variable {K : Type u} {V : Type v}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A finite-dimensional ordinal filtration which starts at the whole space and
is zero by a natural stage admits a basis with an exact ordinal reach assigned
to every basis vector.

This is the wrapper missing from `FilteredBasis`: reverse the finite natural
part of the antitone filtration, choose a simultaneously adapted basis, and
label each basis vector by the last natural level at which it occurs.  Levels
beyond the terminal natural stage are automatically zero.
-/
theorem exists_basis_compatibleWithReach
    [FiniteDimensional K V]
    (X : Ordinal.{0} → Submodule K V) (hX : Antitone X)
    (N : ℕ) (hzero : X 0 = ⊤) (hN : X (N : Ordinal) = ⊥) :
    ∃ (s : Set V) (b : Basis s K V),
      Finite s ∧ ∃ r : s → Ordinal.{0},
        HeightRado.CompatibleWithReach b r X := by
  classical
  let Y : ℕ → Submodule K V := fun k ↦ X (N - k : ℕ)
  have hY : Monotone Y := by
    intro k l hkl
    apply hX
    exact_mod_cast Nat.sub_le_sub_left hkl N
  have hYtop : Y N = ⊤ := by
    simpa [Y] using hzero
  obtain ⟨s, b, hsfinite, hb⟩ :=
    FilteredBasis.exists_compatible_basis Y hY N hYtop
  let reachNat : s → ℕ := fun i ↦
    Nat.findGreatest (fun k ↦ b i ∈ X (k : Ordinal)) N
  have hreach_mem : ∀ i : s, b i ∈ X (reachNat i : Ordinal) := by
    intro i
    change b i ∈ X (Nat.findGreatest
      (fun k ↦ b i ∈ X (k : Ordinal)) N : ℕ)
    exact Nat.findGreatest_spec
      (P := fun k ↦ b i ∈ X (k : Ordinal))
      (m := 0) (Nat.zero_le N) (by
      change b i ∈ X (0 : Ordinal)
      rw [hzero]
      exact Submodule.mem_top)
  have hreach_le : ∀ i : s, reachNat i ≤ N := fun i ↦
    Nat.findGreatest_le N
  have hnat : ∀ k ≤ N,
      X (k : Ordinal) =
        Submodule.span K (b '' {i : s | k ≤ reachNat i}) := by
    intro k hkN
    obtain ⟨I, hI⟩ := hb (N - k) (Nat.sub_le N k)
    have hNk : N - (N - k) = k := Nat.sub_sub_self hkN
    have hI' : Submodule.span K (b '' I) = X (k : Ordinal) := by
      change Submodule.span K (b '' I) = X (N - (N - k) : ℕ) at hI
      rwa [hNk] at hI
    apply le_antisymm
    · rw [← hI']
      apply Submodule.span_mono
      rintro x ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      apply Nat.le_findGreatest hkN
      rw [← hI']
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · apply Submodule.span_le.2
      rintro x ⟨i, hi, rfl⟩
      exact hX (by exact_mod_cast hi) (hreach_mem i)
  let r : s → Ordinal.{0} := fun i ↦ (reachNat i : Ordinal)
  refine ⟨s, b, hsfinite, r, ?_⟩
  intro β
  rcases le_total β (N : Ordinal) with hβN | hNβ
  · have hβω : β < ω := hβN.trans_lt (natCast_lt_omega0 N)
    obtain ⟨k, rfl⟩ := lt_omega0.1 hβω
    have hkN : k ≤ N := by exact_mod_cast hβN
    simpa [r] using hnat k hkN
  · have hXβ : X β = ⊥ := by
      apply le_antisymm
      · rw [← hN]
        exact hX hNβ
      · exact bot_le
    rw [hXβ]
    apply le_antisymm
    · exact bot_le
    · apply Submodule.span_le.2
      rintro x ⟨i, hi, rfl⟩
      change β ≤ (reachNat i : Ordinal) at hi
      have hNreach : N ≤ reachNat i := by
        exact_mod_cast hNβ.trans hi
      have hreach_eq : reachNat i = N :=
        le_antisymm (hreach_le i) hNreach
      have hmem := hreach_mem i
      rw [hreach_eq, hN] at hmem
      exact hmem

end FiniteFilteredBasis

section FiniteReach

variable {B : Type u} [AddCommGroup B] [Finite B]

omit hp in
/-- A finite primary `p`-group is killed by one uniform power of `p`.

The proof takes the sum of elementwise primary exponents.  This elementary
form is more useful here than the abstract finite-group exponent because it
records directly that the uniform annihilator is a power of the fixed prime.
-/
theorem exists_pPow_eq_bot (hB : IsPrimaryPGroup p B) :
    ∃ n : ℕ, pPow p (G := B) n = ⊥ := by
  classical
  letI := Fintype.ofFinite B
  let e : B → ℕ := fun x ↦ Classical.choose (hB x)
  have he : ∀ x : B, p ^ e x • x = 0 := fun x ↦
    Classical.choose_spec (hB x)
  let N : ℕ := ∑ x : B, e x
  refine ⟨N, ?_⟩
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    have hey : e y ≤ N := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ y)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hey
    rw [hk, Nat.add_comm, pow_add, mul_smul, he]
    simp
  · exact bot_le

/-- Consequently the transfinite Ulm filtration of a finite primary source is
already zero at a natural-number stage. -/
theorem exists_ulmSubgroup_nat_eq_bot (hB : IsPrimaryPGroup p B) :
    ∃ n : ℕ, ulmSubgroup p (n : Ordinal) (G := B) = ⊥ := by
  obtain ⟨n, hn⟩ := exists_pPow_eq_bot p hB
  exact ⟨n, (ulmSubgroup_nat p n).trans hn⟩

omit [Finite B] in
/-- At height zero every global socle class is reachable. -/
theorem reachableSubspace_zero_eq_top (F : AddSubgroup B) :
    reachableSubspace p F 0 = ⊤ := by
  apply top_unique
  intro q _hq
  obtain ⟨x, rfl⟩ := (roomSubmodule p F 0).mkQ_surjective q
  let u : reachableNum p F 0 0 :=
    ⟨(x : B), ⟨x.property, by simp [ulmSubgroup_zero]⟩⟩
  refine ⟨(reachableDenSubmodule p F 0 0).mkQ u, ?_⟩
  rw [reachableToRoomZeroLinearMap_mk]
  rfl

omit [Finite B] in
/-- Once the ambient tail lies in the marked subgroup, the corresponding
reachable subspace of the global room is zero. -/
theorem reachableSubspace_eq_bot_of_ulmSubgroup_le
    (F : AddSubgroup B) (β : Ordinal.{0})
    (htail : ulmSubgroup p β (G := B) ≤ F) :
    reachableSubspace p F β = ⊥ := by
  apply bot_unique
  rintro q ⟨c, rfl⟩
  obtain ⟨u, rfl⟩ := (reachableDenSubmodule p F 0 β).mkQ_surjective c
  rw [reachableToRoomZeroLinearMap_mk]
  apply (Submodule.Quotient.mk_eq_zero _).2
  constructor
  · change (u : B) ∈ F
    obtain ⟨e, he, z, hz, hez⟩ := (AddSubgroup.mem_sup).1 u.property.2
    rw [← hez]
    exact F.add_mem he (htail hz)
  · exact u.property.1

/-- The global height-zero room of a finite source is finite-dimensional over
`ZMod p`. -/
theorem room_finiteDimensional (F : AddSubgroup B) :
    FiniteDimensional (ZMod p) (room p F 0) := by
  letI : Finite (room p F 0) :=
    Finite.of_surjective (roomSubmodule p F 0).mkQ
      (roomSubmodule p F 0).mkQ_surjective
  let b := Basis.ofVectorSpace (ZMod p) (room p F 0)
  letI : Finite (Basis.ofVectorSpaceIndex (ZMod p) (room p F 0)) :=
    Finite.of_injective b b.injective
  exact b.finiteDimensional_of_finite

/-- A finite primary source supplies the exact compatible reach basis required
by the height--Rado construction; the basis and all reaches refer to the
ambient finite source filtration. -/
theorem exists_reachable_basis_compatibleWithReach
    (hB : IsPrimaryPGroup p B) (F : AddSubgroup B) :
    ∃ (s : Set (room p F 0)) (b : Basis s (ZMod p) (room p F 0)),
      Finite s ∧ ∃ r : s → Ordinal.{0},
        HeightRado.CompatibleWithReach b r (reachableSubspace p F) := by
  letI : FiniteDimensional (ZMod p) (room p F 0) :=
    room_finiteDimensional p F
  obtain ⟨N, hN⟩ := exists_ulmSubgroup_nat_eq_bot p hB
  apply exists_basis_compatibleWithReach
    (X := reachableSubspace p F)
    (fun _ _ h ↦ reachableSubspace_antitone p F h) N
    (reachableSubspace_zero_eq_top p F)
  apply reachableSubspace_eq_bot_of_ulmSubgroup_le p F (N : Ordinal)
  rw [hN]
  exact bot_le

end FiniteReach

section MarkedSocleExtension

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A}

/-- The first domain in the finite climb: the marked source subgroup together
with the complete source `p`-socle. -/
abbrev markedSocleDomain (F : AddSubgroup B) : AddSubgroup B :=
  F ⊔ pSocleAt p (0 : Ordinal.{0})

/-- A socle map agreeing with the marked map on `F ∩ P(B)` glues to an
additive extension on `F + P(B)`. -/
theorem exists_markedSocleExtension
    (φ : F →+ E)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (hmark : Φ.comp (roomSubmodule p F 0).subtype =
      SocleLift.markedSocleMap p φ) :
    ∃ g₁ : markedSocleDomain p F →+ (⊤ : AddSubgroup A),
      (∀ e : F, (g₁ ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ : A) =
        (φ e : A)) ∧
      (∀ x : pSocleAt p 0 (G := B),
        (g₁ ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ : A) =
          (Φ x : A)) := by
  let ψ : F × pSocleAt p 0 (G := B) →+ markedSocleDomain p F :=
    { toFun := fun z ↦
        ⟨(z.1 : B) + (z.2 : B), AddSubgroup.add_mem_sup z.1.property z.2.property⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := by intro x y; apply Subtype.ext; simp; abel }
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).1 z.property
    refine ⟨(⟨e, he⟩, ⟨x, hx⟩), ?_⟩
    apply Subtype.ext
    exact hex
  let χ : F × pSocleAt p 0 (G := B) →+ A :=
    { toFun := fun z ↦ (φ z.1 : A) + (Φ z.2 : A)
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  have hker : ψ.ker ≤ χ.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz0 : (z.1 : B) + (z.2 : B) = 0 :=
      congrArg (fun t : markedSocleDomain p F ↦ (t : B)) hz
    have hxF : (z.2 : B) ∈ F := by
      have hx : (z.2 : B) = -(z.1 : B) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using hz0
      rw [hx]
      exact F.neg_mem z.1.property
    let u : roomSubmodule p F 0 :=
      ⟨z.2, ⟨hxF, z.2.property⟩⟩
    have hΦx : (Φ z.2 : A) =
        (φ ⟨(z.2 : B), hxF⟩ : A) := by
      have hm := LinearMap.ext_iff.mp hmark u
      exact congrArg Subtype.val hm
    change (φ z.1 : A) + (Φ z.2 : A) = 0
    rw [hΦx]
    have hsumF : z.1 + ⟨(z.2 : B), hxF⟩ = 0 := by
      apply Subtype.ext
      exact hz0
    have himage := congrArg φ hsumF
    simpa [map_add] using congrArg Subtype.val himage
  let g : markedSocleDomain p F →+ A :=
    ψ.liftOfSurjective hψ ⟨χ, hker⟩
  refine ⟨g.codRestrict ⊤ (by intro x; simp), ?_, ?_⟩
  · intro e
    have hψe : ψ (e, 0) =
        ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ := by
      apply Subtype.ext
      simp [ψ]
    change g ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ = (φ e : A)
    rw [← hψe]
    simpa [g, χ] using
      (AddMonoidHom.liftOfRightInverse_comp_apply
        (f := ψ) (f_inv := Function.surjInv hψ)
        (hf := Function.rightInverse_surjInv hψ) (g := ⟨χ, hker⟩) (x := (e, 0)))
  · intro x
    have hψx : ψ (0, x) =
        ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ := by
      apply Subtype.ext
      simp [ψ]
    change g ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ = (Φ x : A)
    rw [← hψx]
    simpa [g, χ] using
      (AddMonoidHom.liftOfRightInverse_comp_apply
        (f := ψ) (f_inv := Function.surjInv hψ)
        (hf := Function.rightInverse_surjInv hψ) (g := ⟨χ, hker⟩) (x := (0, x)))

/-- The glued map is injective and height-nondecreasing when the marked map
and the full-socle map have those properties. -/
theorem exists_injective_heightFloor_markedSocleExtension
    (φ : F →+ E) (hφ : Function.Injective φ)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (hΦ : Function.Injective Φ)
    (hmark : Φ.comp (roomSubmodule p F 0).subtype =
      SocleLift.markedSocleMap p φ)
    (hheight : SocleLift.IsMarkedHeightFloor p φ Φ) :
    ∃ g₁ : markedSocleDomain p F →+ (⊤ : AddSubgroup A),
      Function.Injective g₁ ∧ IsHeightFloorOn p g₁ ∧
      (∀ e : F,
        (g₁ ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ : A) =
          (φ e : A)) ∧
      (∀ x : pSocleAt p 0 (G := B),
        (g₁ ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ : A) =
          (Φ x : A)) := by
  obtain ⟨g₁, hgF, hgP⟩ := exists_markedSocleExtension p φ Φ hmark
  have hg₁inj : Function.Injective g₁ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).1 z.property
    let eF : F := ⟨e, he⟩
    let xP : pSocleAt p 0 (G := B) := ⟨x, hx⟩
    let eD : markedSocleDomain p F :=
      ⟨e, AddSubgroup.mem_sup_left he⟩
    let xD : markedSocleDomain p F :=
      ⟨x, AddSubgroup.mem_sup_right hx⟩
    have hzx : z = eD + xD := by
      apply Subtype.ext
      exact hex.symm
    have htarget : (φ eF : A) + (Φ xP : A) = 0 := by
      have hzA := congrArg (fun t : (⊤ : AddSubgroup A) ↦ (t : A)) hz
      rw [hzx, map_add] at hzA
      change (g₁ eD : A) + (g₁ xD : A) = 0 at hzA
      rw [show (g₁ eD : A) = (φ eF : A) by exact hgF eF,
        show (g₁ xD : A) = (Φ xP : A) by exact hgP xP] at hzA
      exact hzA
    have hpφe : p • (φ eF : A) = 0 := by
      have hp := congrArg (fun y : A ↦ p • y) htarget
      have hpΦ : p • (Φ xP : A) = 0 := (Φ xP).property.1
      simpa [smul_add, hpΦ] using hp
    have hpeF : p • eF = 0 := by
      apply hφ
      rw [map_nsmul, map_zero]
      apply Subtype.ext
      exact hpφe
    have hpe : p • (eF : B) = 0 := congrArg Subtype.val hpeF
    let eP : pSocleAt p 0 (G := B) :=
      ⟨(eF : B), by
        rw [mem_pSocleAt]
        exact ⟨hpe, by simp [ulmSubgroup_zero]⟩⟩
    let u : roomSubmodule p F 0 :=
      ⟨eP, ⟨eF.property, eP.property⟩⟩
    have hΦe : (Φ eP : A) = (φ eF : A) := by
      have hm := LinearMap.ext_iff.mp hmark u
      have hmA : (Φ eP : A) =
          (SocleLift.markedSocleMap p φ u : A) := congrArg Subtype.val hm
      change (Φ eP : A) = (SocleLift.markedSocleValue p φ u : A) at hmA
      rw [SocleLift.markedSocleValue_coe] at hmA
      simpa [u, eP, eF] using hmA
    have hΦsum : Φ (eP + xP) = 0 := by
      rw [map_add]
      apply Subtype.ext
      change (Φ eP : A) + (Φ xP : A) = 0
      rw [hΦe]
      exact htarget
    have hsource : eP + xP = 0 := by
      apply hΦ
      simpa using hΦsum
    apply Subtype.ext
    change (z : B) = 0
    rw [hzx]
    exact congrArg (fun t : pSocleAt p 0 (G := B) ↦ (t : B)) hsource
  have hg₁floor : IsHeightFloorOn p g₁ := by
    intro β z hz
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).1 z.property
    let eF : F := ⟨e, he⟩
    let xP : pSocleAt p 0 (G := B) := ⟨x, hx⟩
    let eD : markedSocleDomain p F :=
      ⟨e, AddSubgroup.mem_sup_left he⟩
    let xD : markedSocleDomain p F :=
      ⟨x, AddSubgroup.mem_sup_right hx⟩
    have hsrc : (xP : B) + (eF : B) ∈ ulmSubgroup p β := by
      rw [add_comm, hex]
      exact hz
    have ht := SocleLift.IsMarkedHeightFloor.add_mem p hheight β xP eF hsrc
    change (g₁ z : A) ∈ ulmSubgroup p β
    have hzx : z = eD + xD := by
      apply Subtype.ext
      exact hex.symm
    rw [hzx, map_add]
    change (g₁ eD : A) + (g₁ xD : A) ∈ ulmSubgroup p β
    rw [show (g₁ eD : A) = (φ eF : A) by exact hgF eF,
      show (g₁ xD : A) = (Φ xP : A) by exact hgP xP]
    simpa [add_comm] using ht
  exact ⟨g₁, hg₁inj, hg₁floor, hgF, hgP⟩

end MarkedSocleExtension

section FreeClimb

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- Package an injective finite marked map as the three-level partial
isomorphism consumed by Kaplansky target selection.  A cutoff-preserving map
supplies this package whenever `α`, `α+1`, and `α+2` all lie below the
cutoff. -/
noncomputable def ulmStageAtOfInjectiveMap
    {H : AddSubgroup B} (hHfinite : Set.Finite (H : Set B))
    (φ : H →+ (⊤ : AddSubgroup A)) (hφinj : Function.Injective φ)
    {θ α : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    (hα : α < θ) (hαsucc : Order.succ α < θ)
    (hαsuccSucc : Order.succ (Order.succ α) < θ) :
    UlmStageAt p (G := B) (H := A) α := by
  let raw : H →+ A := (⊤ : AddSubgroup A).subtype.comp φ
  let R : AddSubgroup A := AddMonoidHom.range raw
  have hrawinj : Function.Injective raw := by
    intro x y hxy
    apply hφinj
    apply Subtype.ext
    exact hxy
  have hrangeInj : Function.Injective raw.rangeRestrict := by
    intro x y hxy
    have hraw : raw x = raw y :=
      congrArg (fun z : R ↦ (z : A)) hxy
    apply hφinj
    apply Subtype.ext
    exact hraw
  let e : H ≃+ R := AddEquiv.ofBijective raw.rangeRestrict
    ⟨hrangeInj, AddMonoidHom.rangeRestrict_surjective raw⟩
  letI : Finite H := hHfinite.to_subtype
  have hRfinite : Set.Finite (R : Set A) := by
    change Set.Finite (Set.range raw)
    exact Set.finite_range raw
  refine
    { A := H
      B := R
      hAfinite := hHfinite
      hBfinite := hRfinite
      e := e
      hφ_at := ?_
      hφ_succ := ?_
      hφ_succSucc := ?_ }
  · intro x
    simpa [e, raw, R] using hpres α hα x
  · intro x
    simpa [e, raw, R] using hpres (Order.succ α) hαsucc x
  · intro x
    simpa [e, raw, R] using
      hpres (Order.succ (Order.succ α)) hαsuccSucc x

/-- Kaplansky target selection for an injective finite map that preserves
heights only below a cutoff.  At a low exact height `α`, the old map is
packaged as `UlmStageAt`; the Case I/II split therefore uses invariant equality
only at `α` and no global height-preservation assumption. -/
theorem exists_kaplanskyTarget_of_heightPresBelow
    {H : AddSubgroup B} (hHfinite : Set.Finite (H : Set B))
    (φ : H →+ (⊤ : AddSubgroup A)) (hφinj : Function.Injective φ)
    {θ α : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    (hα : α < θ) (hαsucc : Order.succ α < θ)
    (hαsuccSucc : Order.succ (Order.succ α) < θ)
    (hinv : ulmInvariant p α (G := B) = ulmInvariant p α (G := A))
    {x : B} (hpxH : p • x ∈ H)
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hxProper : IsProper p H x)
    (hpxMax : ∀ y : B, y - x ∈ H → IsProper p H y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x)) :
    ∃ w : A,
      p • w = (φ ⟨p • x, hpxH⟩ : A) ∧
      w ∈ ulmSubgroup p α (G := A) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := A) ∧
      IsProper p
        (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) w := by
  let s := ulmStageAtOfInjectiveMap p hHfinite φ hφinj hpres
    hα hαsucc hαsuccSucc
  by_cases hcaseII :
      p • x ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := B)
  · simpa [s, ulmStageAtOfInjectiveMap] using
      (exists_kaplanskyTarget_caseII p s hinv hpxH
        hxα hxSucc hxProper hcaseII)
  · simpa [s, ulmStageAtOfInjectiveMap] using
      (exists_kaplanskyTarget_caseI p s hpxH hxα hxSucc hxProper
        hpxMax hcaseII)

/-- Kaplansky target selection with standard-Hill supply in place of ambient
Ulm equality.  The no-gap branch is unchanged.  In the gap branch, subtracting
a higher root from the normalized source element gives a nonzero source Hill
class; Hill domination therefore makes the target Hill quotient nontrivial,
and the exact relative-root lemma supplies the required proper root directly.

This is the selection seam used by the exact-even countdown. -/
theorem exists_kaplanskyTarget_of_heightPresBelow_of_hill
    {H : AddSubgroup B} (hHfinite : Set.Finite (H : Set B))
    (φ : H →+ (⊤ : AddSubgroup A)) (hφinj : Function.Injective φ)
    {θ α : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    (hα : α < θ) (hαsucc : Order.succ α < θ)
    (hαsuccSucc : Order.succ (Order.succ α) < θ)
    (hhill : hillInvariant p H α ≤
      hillInvariant p
        (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) α)
    {x : B} (hpxH : p • x ∈ H)
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hxProper : IsProper p H x)
    (hpxMax : ∀ y : B, y - x ∈ H → IsProper p H y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x)) :
    ∃ w : A,
      p • w = (φ ⟨p • x, hpxH⟩ : A) ∧
      w ∈ ulmSubgroup p α (G := A) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := A) ∧
      IsProper p
        (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) w := by
  let s := ulmStageAtOfInjectiveMap p hHfinite φ hφinj hpres
    hα hαsucc hαsuccSucc
  by_cases hcaseII :
      p • x ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := B)
  · have hroot := hcaseII
    rw [ulmSubgroup_succ] at hroot
    obtain ⟨v, hvSucc, hpv⟩ := hroot
    let q : B := x - v
    have hpq : p • q = 0 := by
      simp [q, smul_sub, hpv]
    have hqα : q ∈ ulmSubgroup p α (G := B) :=
      (ulmSubgroup p α).sub_mem hxα
        (ulmSubgroup_antitone p (Order.le_succ α) hvSucc)
    have hqSucc : q ∉ ulmSubgroup p (Order.succ α) (G := B) := by
      intro hq
      apply hxSucc
      have hxqv : x = q + v := by simp [q]
      rw [hxqv]
      exact (ulmSubgroup p (Order.succ α)).add_mem hq hvSucc
    have hqProper : IsProper p H q := by
      have hqHeight : ulmHeight p q = (α : WithTop Ordinal.{0}) :=
        ulmHeight_eq_of_mem_not_mem_succ p q α hqα hqSucc
      intro a
      rw [hqHeight]
      apply ulmHeight_le_of_not_mem_succ p (q + (a : B)) α
      intro hqa
      have hxaSucc :
          x + (a : B) ∈ ulmSubgroup p (Order.succ α) (G := B) := by
        have hdecomp : x + (a : B) = (q + (a : B)) + v := by
          simp [q]
          abel
        rw [hdecomp]
        exact (ulmSubgroup p (Order.succ α)).add_mem hqa hvSucc
      have hlower :
          ((Order.succ α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            ulmHeight p (x + (a : B)) :=
        coe_le_ulmHeight_of_mem p _ _ hxaSucc
      have hupper := hxProper a
      have hxHeight :=
        ulmHeight_eq_of_mem_not_mem_succ p x α hxα hxSucc
      have hbad :
          ((Order.succ α : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            (α : WithTop Ordinal.{0}) := by
        rw [← hxHeight]
        exact hlower.trans hupper
      exact (not_le_of_gt
        (WithTop.coe_lt_coe.mpr (Order.lt_succ α))) hbad
    have hqP : q ∈ pSocleAt p α (G := B) :=
      (mem_pSocleAt p α q).2 ⟨hpq, hqα⟩
    have hsourceNontrivial : Nontrivial (hillQuotient p H α) :=
      (hillQuotient_nontrivial_iff p H α).2 (by
        intro hle
        have hqmem := hle hqP
        exact ((isProper_iff_notMem_sup p H q α hqα hqSucc).1 hqProper) hqmem)
    have hsourcePos : 0 < hillInvariant p H α :=
      (rank_pos_iff_nontrivial (R := ZMod p)).2 hsourceNontrivial
    have htargetPos : 0 < hillInvariant p s.B α := hsourcePos.trans_le hhill
    have hySuccSucc : (φ ⟨p • x, hpxH⟩ : A) ∈
        ulmSubgroup p (Order.succ (Order.succ α)) (G := A) := by
      simpa [s, ulmStageAtOfInjectiveMap] using
        (s.hφ_succSucc ⟨p • x, hpxH⟩).mp hcaseII
    have hySucc : (φ ⟨p • x, hpxH⟩ : A) ∈
        ulmSubgroup p (Order.succ α) (G := A) :=
      ulmSubgroup_antitone p (Order.le_succ (Order.succ α)) hySuccSucc
    simpa [s, ulmStageAtOfInjectiveMap] using
      (exists_proper_root_of_hillInvariant_pos p s.B
        (φ ⟨p • x, hpxH⟩ : A) α hySucc htargetPos)
  · simpa [s, ulmStageAtOfInjectiveMap] using
      (exists_kaplanskyTarget_caseI p s hpxH hxα hxSucc hxProper
        hpxMax hcaseII)

/-- The one-sided normal-form height calculation at one specified filtration
level.  Only the height floor at the queried level is used.  This local form
is what a finite truncated countdown needs; the all-height wrapper immediately
below remains the convenient interface for the free climb. -/
theorem proper_adjoin_rep_mem_imp_at
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    {x : B} {w : A} {α β : Ordinal.{0}}
    (hfloor : IsHeightFloorAt p φ β)
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hxProper : IsProper p H x)
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (a : H) (n : ℤ)
    (hmem : (a : B) + n • x ∈ ulmSubgroup p β (G := B)) :
    (φ a : A) + n • w ∈ ulmSubgroup p β (G := A) := by
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    let a' : H := a + k • ⟨p • x, hpxH⟩
    have hxrepr :
        (a : B) + ((p : ℤ) * k) • x = (a' : B) := by
      change (a : B) + ((p : ℤ) * k) • x =
        (a : B) + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hwrepr :
        (φ a : A) + ((p : ℤ) * k) • w = (φ a' : A) := by
      change (φ a : A) + ((p : ℤ) * k) • w =
        (φ (a + k • ⟨p • x, hpxH⟩) : A)
      rw [map_add, map_zsmul]
      change (φ a : A) + ((p : ℤ) * k) • w =
        (φ a : A) + k • (φ ⟨p • x, hpxH⟩ : A)
      rw [← hpw]
      simp [mul_zsmul, Int.mul_comm]
    rw [hxrepr] at hmem
    rw [hwrepr]
    exact hfloor a' hmem
  · by_cases hβα : β ≤ α
    · have hxβ : x ∈ ulmSubgroup p β (G := B) :=
        ulmSubgroup_antitone p hβα hxα
      have hwβ : w ∈ ulmSubgroup p β (G := A) :=
        ulmSubgroup_antitone p hβα hwα
      have haβ : (a : B) ∈ ulmSubgroup p β (G := B) := by
        have := (ulmSubgroup p β (G := B)).sub_mem hmem
          ((ulmSubgroup p β (G := B)).zsmul_mem hxβ n)
        simpa using this
      exact (ulmSubgroup p β (G := A)).add_mem
        (hfloor a haβ)
        ((ulmSubgroup p β (G := A)).zsmul_mem hwβ n)
    · have hsuccβ : Order.succ α ≤ β :=
        Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      exact False.elim ((not_mem_succ_add_zsmul_of_proper p
        hxα hxSucc hxProper hpxH a n hn)
          (ulmSubgroup_antitone p hsuccβ hmem))

/-- The one-sided normal-form height calculation used by the finite free
climb.  Target properness and exact target height are unnecessary: a lower
bound for the chosen target root is enough. -/
theorem proper_adjoin_rep_mem_imp
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    (hfloor : IsHeightFloorOn p φ)
    {x : B} {w : A} {α β : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hxProper : IsProper p H x)
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (a : H) (n : ℤ)
    (hmem : (a : B) + n • x ∈ ulmSubgroup p β (G := B)) :
    (φ a : A) + n • w ∈ ulmSubgroup p β (G := A) :=
  proper_adjoin_rep_mem_imp_at p φ (hfloor β) hxα hxSucc hwα
    hxProper hpxH hpw a n hmem

/-- The two-sided version of `proper_adjoin_rep_mem_imp` below a cutoff.
Only preservation of the old map at the queried level `β < θ` is used.
Thus adjoining source and target representatives of the same exact height
preserves the ACM cutoff invariant without requiring global height equality. -/
theorem proper_adjoin_rep_mem_iff_of_below
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    {x : B} {w : A} {α β θ : Ordinal.{0}}
    (hpres : IsHeightPresBelowOn p φ θ) (hβ : β < θ)
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := A))
    (hxProper : IsProper p H x)
    (hwProper : IsProper p (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) w)
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (a : H) (n : ℤ) :
    ((a : B) + n • x ∈ ulmSubgroup p β (G := B)) ↔
      ((φ a : A) + n • w ∈ ulmSubgroup p β (G := A)) := by
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    let a' : H := a + k • ⟨p • x, hpxH⟩
    have hxrepr :
        (a : B) + ((p : ℤ) * k) • x = (a' : B) := by
      change (a : B) + ((p : ℤ) * k) • x =
        (a : B) + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hwrepr :
        (φ a : A) + ((p : ℤ) * k) • w = (φ a' : A) := by
      change (φ a : A) + ((p : ℤ) * k) • w =
        (φ (a + k • ⟨p • x, hpxH⟩) : A)
      rw [map_add, map_zsmul]
      change (φ a : A) + ((p : ℤ) * k) • w =
        (φ a : A) + k • (φ ⟨p • x, hpxH⟩ : A)
      rw [← hpw]
      simp [mul_zsmul, Int.mul_comm]
    rw [hxrepr, hwrepr]
    exact hpres β hβ a'
  · by_cases hβα : β ≤ α
    · have hxβ : x ∈ ulmSubgroup p β (G := B) :=
        ulmSubgroup_antitone p hβα hxα
      have hwβ : w ∈ ulmSubgroup p β (G := A) :=
        ulmSubgroup_antitone p hβα hwα
      have hsource :
          ((a : B) + n • x ∈ ulmSubgroup p β (G := B)) ↔
            (a : B) ∈ ulmSubgroup p β (G := B) := by
        constructor
        · intro hsum
          have hsub := (ulmSubgroup p β (G := B)).sub_mem hsum
            ((ulmSubgroup p β (G := B)).zsmul_mem hxβ n)
          simpa using hsub
        · intro ha
          exact (ulmSubgroup p β (G := B)).add_mem ha
            ((ulmSubgroup p β (G := B)).zsmul_mem hxβ n)
      have htarget :
          ((φ a : A) + n • w ∈ ulmSubgroup p β (G := A)) ↔
            (φ a : A) ∈ ulmSubgroup p β (G := A) := by
        constructor
        · intro hsum
          have hsub := (ulmSubgroup p β (G := A)).sub_mem hsum
            ((ulmSubgroup p β (G := A)).zsmul_mem hwβ n)
          simpa using hsub
        · intro ha
          exact (ulmSubgroup p β (G := A)).add_mem ha
            ((ulmSubgroup p β (G := A)).zsmul_mem hwβ n)
      exact hsource.trans ((hpres β hβ a).trans htarget.symm)
    · have hsuccβ : Order.succ α ≤ β :=
        Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      have hsource :
          (a : B) + n • x ∉ ulmSubgroup p β (G := B) := by
        intro hmem
        exact (not_mem_succ_add_zsmul_of_proper p
          hxα hxSucc hxProper hpxH a n hn)
            (ulmSubgroup_antitone p hsuccβ hmem)
      have htarget :
          (φ a : A) + n • w ∉ ulmSubgroup p β (G := A) := by
        intro hmem
        let raw : H →+ A := (⊤ : AddSubgroup A).subtype.comp φ
        let aR : AddMonoidHom.range raw := ⟨(φ a : A), ⟨a, rfl⟩⟩
        have hpwR : p • w ∈ AddMonoidHom.range raw := by
          rw [hpw]
          exact ⟨⟨p • x, hpxH⟩, rfl⟩
        exact (not_mem_succ_add_zsmul_of_proper p
          hwα hwSucc hwProper hpwR aR n hn)
            (ulmSubgroup_antitone p hsuccβ hmem)
      exact iff_of_false hsource htarget

/-- Build the one-generator extension while preserving only a height floor. -/
theorem socle_extend_build_map_heightFloor
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    (hfloor : IsHeightFloorOn p φ)
    {x : B} (hxH : x ∉ H) {w : A} {α : Ordinal.{0}}
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hxProper : IsProper p H x) :
    ∃ φ' : adjoinElem H x →+ (⊤ : AddSubgroup A),
      (∀ a : H,
        (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) ∧
      (φ' ⟨x, mem_adjoinElem_right H x⟩ : A) = w ∧
      IsHeightFloorOn p φ' := by
  obtain ⟨φ', hφH, hφx⟩ :=
    socle_extend_build_map (p := p) φ hxH hpxH hpw
  refine ⟨φ', hφH, hφx, ?_⟩
  intro β z hz
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  let aH : H := ⟨a, ha⟩
  let a' : adjoinElem H x := ⟨a, le_adjoinElem H x ha⟩
  let x' : adjoinElem H x := ⟨x, mem_adjoinElem_right H x⟩
  have hzrepr : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : A) = (φ aH : A) + n • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : A) + n • (φ' x' : A) =
      (φ aH : A) + n • w
    rw [show (φ' a' : A) = (φ aH : A) by
      simpa [a', aH] using hφH aH]
    rw [show (φ' x' : A) = w by simpa [x'] using hφx]
  change (φ' z : A) ∈ ulmSubgroup p β
  rw [hmap]
  apply proper_adjoin_rep_mem_imp p φ hfloor hxα hxSucc hwα
    hxProper hpxH hpw aH n
  rw [hzrepr] at hz
  exact hz

/-- Build a one-generator extension preserving filtration membership below a
cutoff, without assuming or producing a global height floor.

For the even challenge construction the current tuple map is exact below the
cap but may be directional above it, so a global floor is not available.  The
quotient-built extension itself only needs matching exact heights and
properness of the new representatives to retain the below-cutoff equivalence. -/
theorem socle_extend_build_map_heightPresBelow
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    {θ : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    {x : B} (hxH : x ∉ H) {w : A} {α : Ordinal.{0}}
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := A))
    (hxProper : IsProper p H x)
    (hwProper : IsProper p
      (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) w) :
    ∃ φ' : adjoinElem H x →+ (⊤ : AddSubgroup A),
      (∀ a : H,
        (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) ∧
      (φ' ⟨x, mem_adjoinElem_right H x⟩ : A) = w ∧
      IsHeightPresBelowOn p φ' θ := by
  obtain ⟨φ', hφH, hφx⟩ :=
    socle_extend_build_map (p := p) φ hxH hpxH hpw
  refine ⟨φ', hφH, hφx, ?_⟩
  intro β hβ z
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  let aH : H := ⟨a, ha⟩
  let a' : adjoinElem H x := ⟨a, le_adjoinElem H x ha⟩
  let x' : adjoinElem H x := ⟨x, mem_adjoinElem_right H x⟩
  have hzrepr : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : A) = (φ aH : A) + n • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : A) + n • (φ' x' : A) =
      (φ aH : A) + n • w
    rw [show (φ' a' : A) = (φ aH : A) by
      simpa [a', aH] using hφH aH]
    rw [show (φ' x' : A) = w by simpa [x'] using hφx]
  change ((z : B) ∈ ulmSubgroup p β (G := B) ↔
    (φ' z : A) ∈ ulmSubgroup p β (G := A))
  rw [hmap, hzrepr]
  change ((aH : B) + n • x ∈ ulmSubgroup p β (G := B) ↔
    (φ aH : A) + n • w ∈ ulmSubgroup p β (G := A))
  exact proper_adjoin_rep_mem_iff_of_below p φ hpres hβ
    hxα hxSucc hwα hwSucc hxProper hwProper hpxH hpw aH n

/-- Build a one-generator extension below a cutoff when both the new source
and target representatives already lie in the cutoff subgroup.

At every strictly lower queried level, adding a multiple of either
representative does not change membership.  Thus the old filtration
equivalence alone is enough; no exact-height or properness hypothesis enters.
This is the high branch companion to
`socle_extend_build_map_heightPresBelow`. -/
theorem socle_extend_build_map_heightPresBelow_of_mem
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    {θ : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    {x : B} (hxH : x ∉ H) {w : A}
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (hxθ : x ∈ ulmSubgroup p θ (G := B))
    (hwθ : w ∈ ulmSubgroup p θ (G := A)) :
    ∃ φ' : adjoinElem H x →+ (⊤ : AddSubgroup A),
      (∀ a : H,
        (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) ∧
      (φ' ⟨x, mem_adjoinElem_right H x⟩ : A) = w ∧
      IsHeightPresBelowOn p φ' θ := by
  obtain ⟨φ', hφH, hφx⟩ :=
    socle_extend_build_map (p := p) φ hxH hpxH hpw
  refine ⟨φ', hφH, hφx, ?_⟩
  intro β hβ z
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  let aH : H := ⟨a, ha⟩
  let a' : adjoinElem H x := ⟨a, le_adjoinElem H x ha⟩
  let x' : adjoinElem H x := ⟨x, mem_adjoinElem_right H x⟩
  have hzrepr : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : A) = (φ aH : A) + n • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : A) + n • (φ' x' : A) =
      (φ aH : A) + n • w
    rw [show (φ' a' : A) = (φ aH : A) by
      simpa [a', aH] using hφH aH]
    rw [show (φ' x' : A) = w by simpa [x'] using hφx]
  have hxβ : x ∈ ulmSubgroup p β (G := B) :=
    ulmSubgroup_antitone p (le_of_lt hβ) hxθ
  have hwβ : w ∈ ulmSubgroup p β (G := A) :=
    ulmSubgroup_antitone p (le_of_lt hβ) hwθ
  have hsource :
      ((aH : B) + n • x ∈ ulmSubgroup p β (G := B)) ↔
        (aH : B) ∈ ulmSubgroup p β (G := B) := by
    constructor
    · intro hsum
      have := (ulmSubgroup p β (G := B)).sub_mem hsum
        ((ulmSubgroup p β (G := B)).zsmul_mem hxβ n)
      simpa using this
    · intro haβ
      exact (ulmSubgroup p β (G := B)).add_mem haβ
        ((ulmSubgroup p β (G := B)).zsmul_mem hxβ n)
  have htarget :
      ((φ aH : A) + n • w ∈ ulmSubgroup p β (G := A)) ↔
        (φ aH : A) ∈ ulmSubgroup p β (G := A) := by
    constructor
    · intro hsum
      have := (ulmSubgroup p β (G := A)).sub_mem hsum
        ((ulmSubgroup p β (G := A)).zsmul_mem hwβ n)
      simpa using this
    · intro haβ
      exact (ulmSubgroup p β (G := A)).add_mem haβ
        ((ulmSubgroup p β (G := A)).zsmul_mem hwβ n)
  change ((z : B) ∈ ulmSubgroup p β (G := B) ↔
    (φ' z : A) ∈ ulmSubgroup p β (G := A))
  rw [hmap, hzrepr]
  exact hsource.trans ((hpres β hβ aH).trans htarget.symm)

/-- Build a one-generator extension that retains both the global height floor
and exact filtration membership below `θ`.  The new source and target
representatives must have the same exact height; the old map need only be
two-sided below `θ`. -/
theorem socle_extend_build_map_heightFloor_heightPresBelow
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    (hfloor : IsHeightFloorOn p φ)
    {θ : Ordinal.{0}} (hpres : IsHeightPresBelowOn p φ θ)
    {x : B} (hxH : x ∉ H) {w : A} {α : Ordinal.{0}}
    (hpxH : p • x ∈ H)
    (hpw : p • w = (φ ⟨p • x, hpxH⟩ : A))
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hwα : w ∈ ulmSubgroup p α (G := A))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := A))
    (hxProper : IsProper p H x)
    (hwProper : IsProper p
      (AddMonoidHom.range ((⊤ : AddSubgroup A).subtype.comp φ)) w) :
    ∃ φ' : adjoinElem H x →+ (⊤ : AddSubgroup A),
      (∀ a : H,
        (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) ∧
      (φ' ⟨x, mem_adjoinElem_right H x⟩ : A) = w ∧
      IsHeightFloorOn p φ' ∧ IsHeightPresBelowOn p φ' θ := by
  obtain ⟨φ', hφH, hφx, hφfloor⟩ :=
    socle_extend_build_map_heightFloor p φ hfloor hxH hpxH hpw
      hxα hxSucc hwα hxProper
  refine ⟨φ', hφH, hφx, hφfloor, ?_⟩
  intro β hβ z
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  let aH : H := ⟨a, ha⟩
  let a' : adjoinElem H x := ⟨a, le_adjoinElem H x ha⟩
  let x' : adjoinElem H x := ⟨x, mem_adjoinElem_right H x⟩
  have hzrepr : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : A) = (φ aH : A) + n • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : A) + n • (φ' x' : A) =
      (φ aH : A) + n • w
    rw [show (φ' a' : A) = (φ aH : A) by
      simpa [a', aH] using hφH aH]
    rw [show (φ' x' : A) = w by simpa [x'] using hφx]
  change ((z : B) ∈ ulmSubgroup p β (G := B) ↔
    (φ' z : A) ∈ ulmSubgroup p β (G := A))
  rw [hmap, hzrepr]
  change ((aH : B) + n • x ∈ ulmSubgroup p β (G := B) ↔
    (φ aH : A) + n • w ∈ ulmSubgroup p β (G := A))
  exact proper_adjoin_rep_mem_iff_of_below p φ hpres hβ
    hxα hxSucc hwα hwSucc hxProper hwProper hpxH hpw aH n

/-- A cutoff-preserving one-generator extension at a height strictly below
the cutoff is injective.  In the nontrivial coefficient case, properness makes
the source normal form leave `G_(α+1)`, while cutoff preservation would force it
back into that subgroup if its image vanished. -/
theorem socle_extend_build_map_injective_of_heightPresBelow
    {H : AddSubgroup B} (φ : H →+ (⊤ : AddSubgroup A))
    (hφinj : Function.Injective φ)
    {θ α : Ordinal.{0}} {x : B}
    (hxα : x ∈ ulmSubgroup p α (G := B))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := B))
    (hxProper : IsProper p H x) (hpxH : p • x ∈ H)
    (φ' : adjoinElem H x →+ (⊤ : AddSubgroup A))
    (hφH : ∀ a : H,
      (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A))
    (hpres' : IsHeightPresBelowOn p φ' θ)
    (hαsucc : Order.succ α < θ) : Function.Injective φ' := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    let a' : H := ⟨a + k • (p • x), H.add_mem ha (H.zsmul_mem hpxH k)⟩
    have hzrepr : z = ⟨(a' : B), le_adjoinElem H x a'.property⟩ := by
      apply Subtype.ext
      rw [← hrepr]
      change a + ((p : ℤ) * k) • x = a + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hφa' : φ a' = 0 := by
      apply Subtype.ext
      rw [← hφH a', ← hzrepr, hz]
    have ha' : a' = 0 := hφinj (by simpa using hφa')
    rw [hzrepr, ha']
    rfl
  · have hznot : (z : B) ∉
        ulmSubgroup p (Order.succ α) (G := B) := by
      rw [← hrepr]
      exact not_mem_succ_add_zsmul_of_proper p hxα hxSucc hxProper
        hpxH ⟨a, ha⟩ n hn
    have hφz : (φ' z : A) ∈
        ulmSubgroup p (Order.succ α) (G := A) := by
      rw [hz]
      simp
    exact False.elim (hznot ((hpres' (Order.succ α) hαsucc z).mpr hφz))

/-- The quotient-built one-generator extension is injective when the chosen
new image lies outside the old range.

This is the algebraic injectivity criterion needed by the high countdown
branch.  There, the new source and target representatives need not have the
same exact height, so injectivity cannot be recovered from cutoff
preservation.  Instead the quotient by the old source has order `p`; if a
prime-to-`p` multiple of the new image lay in the old range, Bezout would put
the image itself in that range. -/
theorem socle_extend_build_map_injective_of_not_mem_range
    {S : AddSubgroup B} (φ : S →+ (⊤ : AddSubgroup A))
    (hφ : Function.Injective φ)
    {x : B} (hpxS : p • x ∈ S)
    {w : A}
    (hpw : p • w = (φ ⟨p • x, hpxS⟩ : A))
    (hw : w ∉ AddMonoidHom.range
      ((⊤ : AddSubgroup A).subtype.comp φ))
    (φ' : adjoinElem S x →+ (⊤ : AddSubgroup A))
    (hφS : ∀ a : S,
      (φ' ⟨a, le_adjoinElem S x a.property⟩ : A) = (φ a : A))
    (hφx : (φ' ⟨x, mem_adjoinElem_right S x⟩ : A) = w) :
    Function.Injective φ' := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := S) (g := x)).1 z.property
  let aS : S := ⟨a, ha⟩
  let a' : adjoinElem S x := ⟨a, le_adjoinElem S x ha⟩
  let x' : adjoinElem S x := ⟨x, mem_adjoinElem_right S x⟩
  have hzrepr : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : A) = (φ aS : A) + n • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : A) + n • (φ' x' : A) =
      (φ aS : A) + n • w
    rw [show (φ' a' : A) = (φ aS : A) by
      simpa [a', aS] using hφS aS]
    rw [show (φ' x' : A) = w by simpa [x'] using hφx]
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    let bS : S := aS + k • ⟨p • x, hpxS⟩
    have hzold : z =
        ⟨(bS : B), le_adjoinElem S x bS.property⟩ := by
      apply Subtype.ext
      rw [hzrepr]
      change a + ((p : ℤ) * k) • x = a + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hφb : φ bS = 0 := by
      apply Subtype.ext
      rw [← hφS bS, ← hzold, hz]
    have hb : bS = 0 := hφ (by simpa using hφb)
    rw [hzold, hb]
    rfl
  · let raw : S →+ A := (⊤ : AddSubgroup A).subtype.comp φ
    let R : AddSubgroup A := AddMonoidHom.range raw
    have hpwR : p • w ∈ R := by
      refine ⟨⟨p • x, hpxS⟩, ?_⟩
      exact hpw.symm
    have hnR : n • w ∈ R := by
      refine ⟨-aS, ?_⟩
      have hzero : (φ aS : A) + n • w = 0 := by
        rw [← hmap, hz]
        rfl
      change raw (-aS) = n • w
      calc
        raw (-aS) = -(φ aS : A) := by simp [raw]
        _ = -((φ aS : A) + n • w) + n • w := by abel
        _ = n • w := by rw [hzero]; simp
    exact False.elim (hn (dvd_of_zsmul_mem_of_not_mem
      (p := p) (A := R) hw hpwR n hnR))

/-- Full source-socle containment makes the one-generator height-floor map
injective.  If an extended element dies, its `p`-multiple dies in the old
domain; injectivity there puts the element itself in the full socle, hence back
in the old domain. -/
theorem socle_extend_build_map_injective
    {H : AddSubgroup B} (hSocle : pSocleAt p 0 (G := B) ≤ H)
    (φ : H →+ (⊤ : AddSubgroup A)) (hφ : Function.Injective φ)
    {x : B} (hpxH : p • x ∈ H)
    (φ' : adjoinElem H x →+ (⊤ : AddSubgroup A))
    (hφH : ∀ a : H,
      (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) :
    Function.Injective φ' := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).1 z.property
  have hpzH : p • (z : B) ∈ H := by
    rw [← hrepr]
    rw [nsmul_add, smul_comm p n x]
    exact H.add_mem (H.nsmul_mem ha p) (H.zsmul_mem hpxH n)
  let pz : H := ⟨p • (z : B), hpzH⟩
  have hφpz : φ pz = 0 := by
    apply Subtype.ext
    rw [← hφH pz]
    have hincl :
        (⟨(pz : B), le_adjoinElem H x pz.property⟩ : adjoinElem H x) =
          p • z := Subtype.ext rfl
    rw [hincl, map_nsmul, hz]
    simp
  have hpz : p • (z : B) = 0 := by
    have hpz0 : pz = 0 := by
      apply hφ
      simpa using hφpz
    exact congrArg Subtype.val hpz0
  have hzSocle : (z : B) ∈ pSocleAt p 0 := by
    rw [mem_pSocleAt]
    exact ⟨hpz, by simp [ulmSubgroup_zero]⟩
  let zH : H := ⟨(z : B), hSocle hzSocle⟩
  have hφz : φ zH = 0 := by
    apply Subtype.ext
    rw [← hφH zH]
    have hincl :
        (⟨(zH : B), le_adjoinElem H x zH.property⟩ : adjoinElem H x) = z :=
      Subtype.ext rfl
    rw [hincl, hz]
  have hzH : zH = 0 := by
    apply hφ
    simpa using hφz
  have hzB : (z : B) = 0 := by
    simpa [zH] using congrArg Subtype.val hzH
  exact Subtype.ext hzB

/-- A finite free-climb stage retains precisely the data needed by the
one-sided construction. -/
structure FreeClimbStage (p : ℕ) [Fact p.Prime]
    (B A : Type u) [AddCommGroup B] [AddCommGroup A] where
  source : AddSubgroup B
  source_finite : Set.Finite (source : Set B)
  map : source →+ (⊤ : AddSubgroup A)
  map_injective : Function.Injective map
  floor : IsHeightFloorOn p map
  socle_le : pSocleAt p (0 : Ordinal.{0}) (G := B) ≤ source

/-- Extension of free-climb stages, including literal agreement of the maps. -/
structure FreeClimbStage.Extends
    (s t : FreeClimbStage p B A) : Prop where
  source_le : s.source ≤ t.source
  map_eq : ∀ x : s.source,
    (t.map ⟨(x : B), source_le x.property⟩ : A) = (s.map x : A)

namespace FreeClimbStage.Extends

theorem refl (s : FreeClimbStage p B A) : FreeClimbStage.Extends p s s :=
  ⟨le_rfl, fun _ ↦ rfl⟩

theorem trans {s t u : FreeClimbStage p B A}
    (hst : FreeClimbStage.Extends p s t)
    (htu : FreeClimbStage.Extends p t u) :
    FreeClimbStage.Extends p s u := by
  refine ⟨hst.source_le.trans htu.source_le, ?_⟩
  intro x
  calc
    (u.map ⟨(x : B), htu.source_le (hst.source_le x.property)⟩ : A) =
        (t.map ⟨(x : B), hst.source_le x.property⟩ : A) :=
      htu.map_eq ⟨(x : B), hst.source_le x.property⟩
    _ = (s.map x : A) := hst.map_eq x

end FreeClimbStage.Extends

/-- One free-climb step when the prescribed element has its `p`-multiple in
the current domain. -/
theorem FreeClimbStage.extend_one
    (hB : IsReducedPGroup p B)
    (s : FreeClimbStage p B A) (g : B)
    (hpg : p • g ∈ s.source) :
    ∃ t : FreeClimbStage p B A,
      FreeClimbStage.Extends p s t ∧ g ∈ t.source := by
  by_cases hg : g ∈ s.source
  · exact ⟨s, FreeClimbStage.Extends.refl p s, hg⟩
  obtain ⟨x, hxg, hxProper, _hpxMax⟩ :=
    exists_kaplanskyNormalized (p := p) s.source_finite g
  have hx : x ∉ s.source := by
    intro hxH
    apply hg
    have hrepr : g = x - (x - g) := by abel
    rw [hrepr]
    exact s.source.sub_mem hxH hxg
  have hpx : p • x ∈ s.source := by
    have hrepr : p • x = p • g + p • (x - g) := by
      rw [smul_sub]
      abel
    rw [hrepr]
    exact s.source.add_mem hpg (s.source.nsmul_mem hxg p)
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply hx
    simpa [hxzero] using hxg
  obtain ⟨α, hxα, hxSucc⟩ :=
    exists_ulmHeight_eq_of_ne_zero (p := p) hB hx0
  have hpxSucc : p • x ∈ ulmSubgroup p (Order.succ α) (G := B) := by
    rw [ulmSubgroup_succ]
    exact ⟨x, hxα, rfl⟩
  have hySucc : (s.map ⟨p • x, hpx⟩ : A) ∈
      ulmSubgroup p (Order.succ α) (G := A) :=
    s.floor (Order.succ α) ⟨p • x, hpx⟩ hpxSucc
  rw [ulmSubgroup_succ] at hySucc
  obtain ⟨w, hwα, hpw⟩ := hySucc
  obtain ⟨φ', hφH, _hφx, hφfloor⟩ :=
    socle_extend_build_map_heightFloor p s.map s.floor hx hpx
      hpw hxα hxSucc hwα hxProper
  have hφinj : Function.Injective φ' :=
    socle_extend_build_map_injective p s.socle_le s.map s.map_injective
      hpx φ' hφH
  let H' := adjoinElem s.source x
  have hH'finite : Set.Finite (H' : Set B) :=
    adjoinElem_finite (p := p) hB.primary s.source_finite x
  let t : FreeClimbStage p B A :=
    { source := H'
      source_finite := hH'finite
      map := φ'
      map_injective := hφinj
      floor := hφfloor
      socle_le := s.socle_le.trans (le_adjoinElem s.source x) }
  have hst : FreeClimbStage.Extends p s t := by
    refine ⟨le_adjoinElem s.source x, ?_⟩
    exact hφH
  refine ⟨t, hst, ?_⟩
  have hxg' : x - g ∈ t.source := hst.source_le hxg
  have hx' : x ∈ t.source := mem_adjoinElem_right s.source x
  have hrepr : g = x - (x - g) := by abel
  rw [hrepr]
  exact t.source.sub_mem hx' hxg'

/-- Primaryness reduces an arbitrary prescribed element to repeated one-step
extensions along its finite `p`-power chain. -/
theorem FreeClimbStage.extend_to_mem
    (hB : IsReducedPGroup p B)
    (s : FreeClimbStage p B A) (g : B) :
    ∃ t : FreeClimbStage p B A,
      FreeClimbStage.Extends p s t ∧ g ∈ t.source := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : FreeClimbStage p B A,
        p ^ n • g ∈ t.source →
        ∃ u : FreeClimbStage p B A,
          FreeClimbStage.Extends p t u ∧ g ∈ u.source := by
    intro n
    induction n with
    | zero =>
        intro t hg
        have hg' : g ∈ t.source := by simpa using hg
        exact ⟨t, FreeClimbStage.Extends.refl p t, hg'⟩
    | succ n ih =>
        intro t hpow
        let y : B := p ^ n • g
        have hpy : p • y ∈ t.source := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, htt₁, hy₁⟩ := t.extend_one p hB y hpy
        obtain ⟨t₂, ht₁t₂, hg₂⟩ := ih t₁ hy₁
        exact ⟨t₂, FreeClimbStage.Extends.trans p htt₁ ht₁t₂, hg₂⟩
  obtain ⟨n, hn⟩ := hB.primary g
  exact extend_pow n s (by simpa [hn])

/-- Absorb every member of a finite list while retaining agreement with the
initial stage. -/
theorem FreeClimbStage.extend_list
    (hB : IsReducedPGroup p B)
    (s : FreeClimbStage p B A) (l : List B) :
    ∃ t : FreeClimbStage p B A,
      FreeClimbStage.Extends p s t ∧
      ∀ g ∈ l, g ∈ t.source := by
  induction l generalizing s with
  | nil =>
      exact ⟨s, FreeClimbStage.Extends.refl p s, by simp⟩
  | cons g l ih =>
      obtain ⟨t₁, hst₁, hg₁⟩ := s.extend_to_mem p hB g
      obtain ⟨t₂, ht₁t₂, hlt₂⟩ := ih t₁
      refine ⟨t₂, FreeClimbStage.Extends.trans p hst₁ ht₁t₂, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact ht₁t₂.source_le hg₁
      · exact hlt₂ x hxl

/-- **Finite free climb above a full source socle.**  An injective
height-nondecreasing homomorphism whose domain contains `P(B)` extends to an
injective height-nondecreasing homomorphism on all of a finite reduced primary
source group. -/
theorem finite_free_climb
    [Finite B] (hB : IsReducedPGroup p B)
    (H : AddSubgroup B)
    (hSocle : pSocleAt p (0 : Ordinal.{0}) (G := B) ≤ H)
    (φ : H →+ (⊤ : AddSubgroup A))
    (hφ : Function.Injective φ) (hfloor : IsHeightFloorOn p φ) :
    ∃ f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : H, (f ⟨(x : B), trivial⟩ : A) = (φ x : A) := by
  let s : FreeClimbStage p B A :=
    { source := H
      source_finite := Set.toFinite (H : Set B)
      map := φ
      map_injective := hφ
      floor := hfloor
      socle_le := hSocle }
  letI := Fintype.ofFinite B
  obtain ⟨t, hst, hall⟩ :=
    s.extend_list p hB (Finset.univ.toList)
  have htall : ∀ x : B, x ∈ t.source := by
    intro x
    exact hall x (by simp)
  let ι : (⊤ : AddSubgroup B) →+ t.source :=
    { toFun := fun x ↦ ⟨x, htall x⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A) := t.map.comp ι
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : t.source ↦ (z : B)) hxy)
  have hfinj : Function.Injective f := t.map_injective.comp hι
  have hffloor : IsHeightFloorOn p f := by
    intro β x hx
    exact t.floor β (ι x) hx
  refine ⟨f, hfinj, hffloor, ?_⟩
  intro x
  change (t.map (ι ⟨(x : B), trivial⟩) : A) = (φ x : A)
  have hιx : ι ⟨(x : B), trivial⟩ =
      ⟨(x : B), hst.source_le x.property⟩ := Subtype.ext rfl
  rw [hιx]
  exact hst.map_eq x

end FreeClimb

section ReverseSocleSelector

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A}

/-- A height-compatible socle map inducing `L` on the room quotient is already
a legal point of every affine height cell.  This is the reverse bridge needed
for finite necessity: it extracts a Rado realization from an existing group
embedding instead of constructing the socle map from a Rado realization. -/
theorem affineAccess_of_heightCompatible_socle_map
    (φ : F →+ E) (hfloor : IsHeightFloorOn p φ)
    {I : Type v}
    (b : Basis I (ZMod p) (room p F 0)) (r : I → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hquot : (roomSubmodule p E 0).mkQ.comp Φ =
      L.comp (roomSubmodule p F 0).mkQ)
    (hheight : SocleLift.IsMarkedHeightFloor p φ Φ) :
    ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i := by
  intro i
  let x := SocleLift.sourceBasisSocle p b r hcompat i
  let e := SocleLift.sourceBasisAnchor p b r hcompat i
  have hxe : (x : B) - (e : B) ∈ ulmSubgroup p (r i) :=
    SocleLift.sourceBasisSocle_sub_anchor_mem p b r hcompat i
  have hy : (Φ x : A) - (φ e : A) ∈ ulmSubgroup p (r i) :=
    hheight (r i) x e hxe
  let y : reachableNum p E 0 (r i) :=
    ⟨(Φ x : A), ⟨(Φ x).property,
      (AddSubgroup.mem_sup).2
        ⟨(φ e : A), (φ e).property,
          (Φ x : A) - (φ e : A), hy, by abel⟩⟩⟩
  let q : reachableSpace p E 0 (r i) :=
    (reachableDenSubmodule p E 0 (r i)).mkQ y
  have hqroom : reachableToRoomZeroLinearMap p E (r i) q = L (b i) := by
    change (roomSubmodule p E 0).mkQ (Φ x) = L (b i)
    calc
      (roomSubmodule p E 0).mkQ (Φ x) =
          L ((roomSubmodule p F 0).mkQ x) :=
        LinearMap.ext_iff.mp hquot x
      _ = L (b i) := by
        rw [SocleLift.sourceBasisSocle_mkQ p b r hcompat]
  have hqjump : reachableToJumpLinearMap p E (r i) q =
      HeightCell.basisJumpTarget p φ hfloor b r hcompat i := by
    rw [show q = (reachableDenSubmodule p E 0 (r i)).mkQ y by rfl]
    rw [reachableToJumpLinearMap_mk_of_anchor p E (r i) y
      (φ e : A) (φ e).property hy]
    rw [HeightCell.basisJumpTarget,
      ← SocleLift.sourceBasisNum_mk p b r hcompat i]
    rw [reachableToJumpLinearMap_mk_of_anchor p F (r i)
      (SocleLift.sourceBasisNum p b r hcompat i)
      (e : B) e.property hxe]
    change QuotientAddGroup.mk
        (reachableAnchorMultipleOf p E (r i) y
          (φ e : A) (φ e).property hy) =
      jumpMap p φ (hfloor (Order.succ (r i))) (hfloor (r i))
        (QuotientAddGroup.mk
          (reachableAnchorMultipleOf p F (r i)
            (SocleLift.sourceBasisNum p b r hcompat i)
            (e : B) e.property hxe))
    rw [jumpMap_mk]
    apply congrArg QuotientAddGroup.mk
    apply Subtype.ext
    change p • (φ e : A) = (φ (p • e) : A)
    rw [map_nsmul]
    rfl
  let q₀ := HeightCell.targetAtReach p φ hfloor b r hcompat i
  have hdiffjump :
      reachableToJumpLinearMap p E (r i) (q - q₀) = 0 := by
    rw [map_sub, hqjump,
      HeightCell.targetAtReach_residue p φ hfloor b r hcompat]
    simp
  have hdiffroom :=
    (reachableToRoomZero_mem_roomSubspace_iff p E (r i) (q - q₀)).2
      hdiffjump
  change L (b i) -
      HeightCell.heightCellBaseMap p φ hfloor b r hcompat (b i) ∈
        roomSubspace p E (r i)
  simpa [map_sub, hqroom, q₀, HeightCell.heightCellBaseMap_basis] using
    hdiffroom

/-- Restrict a homomorphism on the whole source to the source `p`-socle. -/
noncomputable def wholeSocleMap
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A)) :
    pSocleAt p (0 : Ordinal.{0}) (G := B) →ₗ[ZMod p]
      pSocleAt p (0 : Ordinal.{0}) (G := A) :=
  ({
    toFun := fun x ↦ ⟨(f ⟨(x : B), trivial⟩ : A), by
      rw [mem_pSocleAt]
      constructor
      · change p • (f ⟨(x : B), trivial⟩ : A) = 0
        have hx0 : p • (x : B) = 0 :=
          (mem_pSocleAt p 0 (x : B)).1 x.property |>.1
        have hxTop : p • (⟨(x : B), trivial⟩ : (⊤ : AddSubgroup B)) = 0 :=
          Subtype.ext hx0
        have hf0 := congrArg (fun z : (⊤ : AddSubgroup A) ↦ (z : A))
          (congrArg f hxTop)
        simpa using hf0
      · simp [ulmSubgroup_zero]⟩
    map_zero' := by
      apply Subtype.ext
      change (f (0 : (⊤ : AddSubgroup B)) : A) = 0
      rw [map_zero]
      rfl
    map_add' := by
      intro x y
      apply Subtype.ext
      change (f (⟨(x : B), trivial⟩ + ⟨(y : B), trivial⟩) : A) =
        (f ⟨(x : B), trivial⟩ : A) + (f ⟨(y : B), trivial⟩ : A)
      rw [map_add]
      rfl
  } : pSocleAt p (0 : Ordinal.{0}) (G := B) →+
      pSocleAt p (0 : Ordinal.{0}) (G := A)).toZModLinearMap p

@[simp] theorem wholeSocleMap_coe
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (x : pSocleAt p (0 : Ordinal.{0}) (G := B)) :
    (wholeSocleMap p f x : A) = (f ⟨(x : B), trivial⟩ : A) := rfl

theorem wholeSocleMap_injective
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hf : Function.Injective f) : Function.Injective (wholeSocleMap p f) := by
  intro x y hxy
  apply Subtype.ext
  have hfxy : f ⟨(x : B), trivial⟩ = f ⟨(y : B), trivial⟩ := by
    apply Subtype.ext
    exact congrArg
      (fun z : pSocleAt p (0 : Ordinal.{0}) (G := A) ↦ (z : A)) hxy
  exact congrArg (fun z : (⊤ : AddSubgroup B) ↦ (z : B)) (hf hfxy)

/-- An extension with a height floor satisfies all marked socle height
equations. -/
theorem wholeSocleMap_isMarkedHeightFloor
    (φ : F →+ E)
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hffloor : IsHeightFloorOn p f)
    (hext : ∀ e : F, (f ⟨(e : B), trivial⟩ : A) = (φ e : A)) :
    SocleLift.IsMarkedHeightFloor p φ (wholeSocleMap p f) := by
  intro β x e hxe
  let xb : (⊤ : AddSubgroup B) := ⟨(x : B), trivial⟩
  let eb : (⊤ : AddSubgroup B) := ⟨(e : B), trivial⟩
  have hsrc : (xb - eb : B) ∈ ulmSubgroup p β := by
    simpa using hxe
  have ht := hffloor β (xb - eb) hsrc
  change (wholeSocleMap p f x : A) - (φ e : A) ∈ ulmSubgroup p β
  rw [wholeSocleMap_coe, ← hext e]
  simpa [xb, eb] using ht

/-- The room-quotient map induced by a whole-group extension. -/
noncomputable def wholeRoomMap
    (φ : F →+ E)
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hext : ∀ e : F, (f ⟨(e : B), trivial⟩ : A) = (φ e : A)) :
    room p F 0 →ₗ[ZMod p] room p E 0 :=
  (roomSubmodule p F 0).mapQ (roomSubmodule p E 0)
    (wholeSocleMap p f) (by
      intro x hx
      constructor
      · change (wholeSocleMap p f x : A) ∈ E
        let e : F := ⟨(x : B), hx.1⟩
        rw [wholeSocleMap_coe, hext e]
        exact (φ e).property
      · exact (wholeSocleMap p f x).property)

theorem wholeRoomMap_quotient
    (φ : F →+ E)
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hext : ∀ e : F, (f ⟨(e : B), trivial⟩ : A) = (φ e : A)) :
    (roomSubmodule p E 0).mkQ.comp (wholeSocleMap p f) =
      (wholeRoomMap p φ f hext).comp (roomSubmodule p F 0).mkQ := by
  exact (Submodule.mapQ_mkQ (roomSubmodule p F 0) (roomSubmodule p E 0)
    (wholeSocleMap p f)).symm

/-- If the marked target subgroup is exactly the image of the marked source,
then an injective whole-group extension induces an injective room map.  This
surjectivity condition is essential for necessity: enlarging `E` artificially
shrinks target room. -/
theorem wholeRoomMap_injective
    (φ : F →+ E) (hφsurj : Function.Surjective φ)
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hf : Function.Injective f)
    (hext : ∀ e : F, (f ⟨(e : B), trivial⟩ : A) = (φ e : A)) :
    Function.Injective (wholeRoomMap p φ f hext) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  refine Quotient.inductionOn q ?_ hq
  intro x hx
  change wholeRoomMap p φ f hext ((roomSubmodule p F 0).mkQ x) = 0 at hx
  have hmapQ :
      wholeRoomMap p φ f hext ((roomSubmodule p F 0).mkQ x) =
        (roomSubmodule p E 0).mkQ (wholeSocleMap p f x) :=
    (LinearMap.ext_iff.mp (wholeRoomMap_quotient p φ f hext) x).symm
  rw [hmapQ] at hx
  have hdenA := (Submodule.Quotient.mk_eq_zero (roomSubmodule p E 0)).1 hx
  have hmemE : (wholeSocleMap p f x : A) ∈ E := hdenA.1
  let yE : E := ⟨(wholeSocleMap p f x : A), hmemE⟩
  obtain ⟨e, he⟩ := hφsurj yE
  have hfval : f ⟨(x : B), trivial⟩ = f ⟨(e : B), trivial⟩ := by
    apply Subtype.ext
    rw [← wholeSocleMap_coe p f x, hext e]
    exact (congrArg Subtype.val he).symm
  have hxe : (x : B) = (e : B) :=
    congrArg (fun z : (⊤ : AddSubgroup B) ↦ (z : B)) (hf hfval)
  apply (Submodule.Quotient.mk_eq_zero (roomSubmodule p F 0)).2
  constructor
  · change (x : B) ∈ F
    rw [hxe]
    exact e.property
  · exact x.property

end ReverseSocleSelector

section FiniteSufficiency

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- **Finite D-23 sufficiency.**  For finite reduced `p`-primary source and
finite target groups, the room--kernel budget constructs an injective
height-nondecreasing homomorphism on the whole source, extending the marked
map literally.

The target-finiteness hypothesis is explicit because the current finite Rado
selector API asks for finite-dimensional target room.  Removing that
implementation restriction is a separate step from this theorem. -/
theorem exists_finite_embedding_of_kernelRoomBudget
    [Finite A] [Finite B]
    (hB : IsReducedPGroup p B)
    (F : AddSubgroup B) (E : AddSubgroup A)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : F, (f ⟨(x : B), trivial⟩ : A) = (φ x : A) := by
  letI : FiniteDimensional (ZMod p) (room p F 0) :=
    room_finiteDimensional p F
  letI : FiniteDimensional (ZMod p) (room p E 0) :=
    room_finiteDimensional p E
  obtain ⟨s, b, hs, r, hcompat⟩ :=
    exists_reachable_basis_compatibleWithReach p hB.primary F
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  obtain ⟨L, Φ, hL, haccess, hΦ, hmark, hquot, hheight⟩ :=
    SocleLift.exists_injective_heightCompatible_socle_lift_of_budget
      p φ hφ hfloor b r hcompat hbudget
  obtain ⟨g₁, hg₁inj, hg₁floor, hgF, hgP⟩ :=
    exists_injective_heightFloor_markedSocleExtension
      p φ hφ Φ hΦ hmark hheight
  have hsocle :
      pSocleAt p (0 : Ordinal.{0}) (G := B) ≤ markedSocleDomain p F := by
    intro x hx
    exact AddSubgroup.mem_sup_right hx
  obtain ⟨f, hfinj, hffloor, hfD⟩ :=
    finite_free_climb p hB (markedSocleDomain p F) hsocle
      g₁ hg₁inj hg₁floor
  refine ⟨f, hfinj, hffloor, ?_⟩
  intro x
  let xD : markedSocleDomain p F :=
    ⟨(x : B), AddSubgroup.mem_sup_left x.property⟩
  calc
    (f ⟨(x : B), trivial⟩ : A) = (g₁ xD : A) := hfD xD
    _ = (φ x : A) := hgF x

/-- **Finite D-23 necessity.**  If the marked target `E` is exactly the image
of `F`, every injective height-nondecreasing whole-group extension forces the
room--kernel budget at every height. -/
theorem kernelRoomBudget_of_finite_embedding
    [Finite A] [Finite B]
    (hB : IsReducedPGroup p B)
    (F : AddSubgroup B) (E : AddSubgroup A)
    (φ : F →+ E) (hφsurj : Function.Surjective φ)
    (hfloor : IsHeightFloorOn p φ)
    (f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A))
    (hf : Function.Injective f) (hffloor : IsHeightFloorOn p f)
    (hext : ∀ x : F, (f ⟨(x : B), trivial⟩ : A) = (φ x : A)) :
    ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β) := by
  letI : FiniteDimensional (ZMod p) (room p F 0) :=
    room_finiteDimensional p F
  letI : FiniteDimensional (ZMod p) (room p E 0) :=
    room_finiteDimensional p E
  obtain ⟨s, b, hs, r, hcompat⟩ :=
    exists_reachable_basis_compatibleWithReach p hB.primary F
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  let Φ := wholeSocleMap p f
  let L := wholeRoomMap p φ f hext
  have hL : Function.Injective L :=
    wholeRoomMap_injective p φ hφsurj f hf hext
  have hheight : SocleLift.IsMarkedHeightFloor p φ Φ :=
    wholeSocleMap_isMarkedHeightFloor p φ f hffloor hext
  have haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i :=
    affineAccess_of_heightCompatible_socle_map p φ hfloor b r hcompat
      Φ L (wholeRoomMap_quotient p φ f hext) hheight
  have hreal : FiniteRado.HasInjectiveRealization b
      (HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r) := ⟨L, hL, haccess⟩
  have hfin := HeightRado.kernel_budget_of_hasInjectiveRealization
    (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
    (reachableSubspace p F) (roomSubspace p E) b r hcompat
    (fun _ _ h ↦ roomSubspace_antitone p E h) hreal
  intro β
  apply (Survival.KernelRoomBudgetAt.iff_selectorKernelRank_le
    p φ β (hfloor (Order.succ β)) (hfloor β)).2
  rw [← HeightCell.heightCellBaseMap_residueKernel_rank
    p φ hfloor b r hcompat β, ← roomSubspace_rank]
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank]
  exact_mod_cast hfin β

/-- **Exact finite marked-embedding criterion (finite target form).**  When
`E` is precisely the image of the marked subgroup, a full injective
height-nondecreasing extension exists exactly when D-23 holds at every
ordinal. -/
theorem finite_embedding_iff_kernelRoomBudget
    [Finite A] [Finite B]
    (hB : IsReducedPGroup p B)
    (F : AddSubgroup B) (E : AddSubgroup A)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hφsurj : Function.Surjective φ)
    (hfloor : IsHeightFloorOn p φ) :
    (∃ f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : F, (f ⟨(x : B), trivial⟩ : A) = (φ x : A)) ↔
    ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β) := by
  constructor
  · rintro ⟨f, hf, hffloor, hext⟩
    exact kernelRoomBudget_of_finite_embedding
      p hB F E φ hφsurj hfloor f hf hffloor hext
  · exact exists_finite_embedding_of_kernelRoomBudget
      p hB F E φ hφ hfloor

end FiniteSufficiency

end FiniteEmbedding
