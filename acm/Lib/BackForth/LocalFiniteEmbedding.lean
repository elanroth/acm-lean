import Lib.BackForth.LocalSocleLift

/-!
# Finite marked embeddings inside an ambient source group

The challenge subgroup `D` is finite, but all Ulm heights are computed in the
possibly infinite ambient group `B`.  The initial domain contains precisely
`F + (D ∩ P₀(B))`; the subsequent free climb is constrained to remain inside
`D`.
-/

noncomputable section

open Module Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

namespace LocalFiniteEmbedding

/-- The actual additive subgroup `D ∩ P₀(B)` corresponding to the local
challenge socle. -/
abbrev challengeSocleSubgroup (D : AddSubgroup B) : AddSubgroup B :=
  D ⊓ pSocleAt p (0 : Ordinal.{0}) (G := B)

/-- The initial local climb domain. -/
abbrev challengeSocleDomain (F D : AddSubgroup B) : AddSubgroup B :=
  F ⊔ challengeSocleSubgroup p D

variable {F D : AddSubgroup B} {E : AddSubgroup A}

/-- Convert an element of `D ∩ P₀(B)` to the linear challenge-socle type. -/
noncomputable def toChallengeSocle
    (x : challengeSocleSubgroup p D) :
    FiniteChallenge.challengeSocle p D :=
  ⟨⟨(x : B), x.property.2⟩, x.property.1⟩

@[simp] theorem toChallengeSocle_coe
    (x : challengeSocleSubgroup p D) :
    (toChallengeSocle p x : B) = (x : B) := rfl

/-- Glue the marked map on `F` to a compatible map on `D ∩ P₀(B)`. -/
theorem exists_challengeSocleExtension
    (φ : F →+ E)
    (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
      pSocleAt p 0 (G := A))
    (hmark : Φ.comp
      (LocalSocleLift.challengeDenominator p (F := F) (D := D)).subtype =
        LocalSocleLift.challengeMarkedSocleMap p φ) :
    ∃ g₁ : challengeSocleDomain p F D →+ (⊤ : AddSubgroup A),
      (∀ e : F,
        (g₁ ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ : A) =
          (φ e : A)) ∧
      (∀ x : challengeSocleSubgroup p D,
        (g₁ ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ : A) =
          (Φ (toChallengeSocle p x) : A)) := by
  let ψ : F × FiniteChallenge.challengeSocle p D →+
      challengeSocleDomain p F D :=
    { toFun := fun z ↦
        ⟨(z.1 : B) + (z.2 : B), AddSubgroup.add_mem_sup z.1.property
          ⟨z.2.property, (z.2 : pSocleAt p 0 (G := B)).property⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := by intro x y; apply Subtype.ext; simp; abel }
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).mp z.property
    let xs : FiniteChallenge.challengeSocle p D :=
      ⟨⟨x, hx.2⟩, hx.1⟩
    refine ⟨(⟨e, he⟩, xs), ?_⟩
    apply Subtype.ext
    exact hex
  let χ : F × FiniteChallenge.challengeSocle p D →+ A :=
    { toFun := fun z ↦ (φ z.1 : A) + (Φ z.2 : A)
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  have hker : ψ.ker ≤ χ.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz0 : (z.1 : B) + (z.2 : B) = 0 :=
      congrArg (fun t : challengeSocleDomain p F D ↦ (t : B)) hz
    have hxF : (z.2 : B) ∈ F := by
      have hx : (z.2 : B) = -(z.1 : B) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using hz0
      rw [hx]
      exact F.neg_mem z.1.property
    let u : LocalSocleLift.challengeDenominator p (F := F) (D := D) :=
      ⟨z.2, ⟨hxF, (z.2 : pSocleAt p 0 (G := B)).property⟩⟩
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
  let g : challengeSocleDomain p F D →+ A :=
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
        (hf := Function.rightInverse_surjInv hψ)
        (g := ⟨χ, hker⟩) (x := (e, 0)))
  · intro x
    let xs := toChallengeSocle p x
    have hψx : ψ (0, xs) =
        ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ := by
      apply Subtype.ext
      simp [ψ, xs]
    change g ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ =
      (Φ xs : A)
    rw [← hψx]
    simpa [g, χ] using
      (AddMonoidHom.liftOfRightInverse_comp_apply
        (f := ψ) (f_inv := Function.surjInv hψ)
        (hf := Function.rightInverse_surjInv hψ)
        (g := ⟨χ, hker⟩) (x := (0, xs)))

/-- The glued local socle map is injective and height-nondecreasing. -/
theorem exists_injective_heightFloor_challengeSocleExtension
    (hFD : F ≤ D)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (Φ : FiniteChallenge.challengeSocle p D →ₗ[ZMod p]
      pSocleAt p 0 (G := A))
    (hΦ : Function.Injective Φ)
    (hmark : Φ.comp
      (LocalSocleLift.challengeDenominator p (F := F) (D := D)).subtype =
        LocalSocleLift.challengeMarkedSocleMap p φ)
    (hheight : LocalSocleLift.IsChallengeMarkedHeightFloor p φ Φ) :
    ∃ g₁ : challengeSocleDomain p F D →+ (⊤ : AddSubgroup A),
      Function.Injective g₁ ∧ IsHeightFloorOn p g₁ ∧
      (∀ e : F,
        (g₁ ⟨(e : B), AddSubgroup.mem_sup_left e.property⟩ : A) =
          (φ e : A)) ∧
      (∀ x : challengeSocleSubgroup p D,
        (g₁ ⟨(x : B), AddSubgroup.mem_sup_right x.property⟩ : A) =
          (Φ (toChallengeSocle p x) : A)) := by
  obtain ⟨g₁, hgF, hgP⟩ :=
    exists_challengeSocleExtension p φ Φ hmark
  have hg₁inj : Function.Injective g₁ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).mp z.property
    let eF : F := ⟨e, he⟩
    let xS : challengeSocleSubgroup p D := ⟨x, hx⟩
    let xP := toChallengeSocle p xS
    let eDom : challengeSocleDomain p F D :=
      ⟨e, AddSubgroup.mem_sup_left he⟩
    let xDom : challengeSocleDomain p F D :=
      ⟨x, AddSubgroup.mem_sup_right hx⟩
    have hzx : z = eDom + xDom := by
      apply Subtype.ext
      exact hex.symm
    have htarget : (φ eF : A) + (Φ xP : A) = 0 := by
      have hzA := congrArg (fun t : (⊤ : AddSubgroup A) ↦ (t : A)) hz
      rw [hzx, map_add] at hzA
      change (g₁ eDom : A) + (g₁ xDom : A) = 0 at hzA
      rw [show (g₁ eDom : A) = (φ eF : A) by exact hgF eF,
        show (g₁ xDom : A) = (Φ xP : A) by exact hgP xS] at hzA
      exact hzA
    have hpφe : p • (φ eF : A) = 0 := by
      have hpzero := congrArg (fun y : A ↦ p • y) htarget
      have hpΦ : p • (Φ xP : A) = 0 := (Φ xP).property.1
      simpa [smul_add, hpΦ] using hpzero
    have hpeF : p • eF = 0 := by
      apply hφ
      rw [map_nsmul, map_zero]
      apply Subtype.ext
      exact hpφe
    have hpe : p • (eF : B) = 0 := congrArg Subtype.val hpeF
    let eS : challengeSocleSubgroup p D :=
      ⟨(eF : B), hFD eF.property, by
        change p • (eF : B) = 0 ∧
          (eF : B) ∈ ulmSubgroup p (0 : Ordinal.{0})
        exact ⟨hpe, by simp [ulmSubgroup_zero]⟩⟩
    let eP := toChallengeSocle p eS
    let u : LocalSocleLift.challengeDenominator p (F := F) (D := D) :=
      ⟨eP, ⟨eF.property, (eP : pSocleAt p 0 (G := B)).property⟩⟩
    have hΦe : (Φ eP : A) = (φ eF : A) := by
      have hm := LinearMap.ext_iff.mp hmark u
      exact congrArg Subtype.val hm
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
    exact congrArg (fun t : FiniteChallenge.challengeSocle p D ↦ (t : B))
      hsource
  have hg₁floor : IsHeightFloorOn p g₁ := by
    intro β z hz
    obtain ⟨e, he, x, hx, hex⟩ := (AddSubgroup.mem_sup).mp z.property
    let eF : F := ⟨e, he⟩
    let xS : challengeSocleSubgroup p D := ⟨x, hx⟩
    let xP := toChallengeSocle p xS
    let eDom : challengeSocleDomain p F D :=
      ⟨e, AddSubgroup.mem_sup_left he⟩
    let xDom : challengeSocleDomain p F D :=
      ⟨x, AddSubgroup.mem_sup_right hx⟩
    have hsrc : (xP : B) + (eF : B) ∈ ulmSubgroup p β := by
      change x + e ∈ ulmSubgroup p β
      rw [add_comm, hex]
      exact hz
    have ht : (Φ xP : A) + (φ eF : A) ∈ ulmSubgroup p β := by
      have hmain := hheight β xP (-eF) (by simpa using hsrc)
      simpa using hmain
    change (g₁ z : A) ∈ ulmSubgroup p β
    have hzx : z = eDom + xDom := by
      apply Subtype.ext
      exact hex.symm
    rw [hzx, map_add]
    change (g₁ eDom : A) + (g₁ xDom : A) ∈ ulmSubgroup p β
    rw [show (g₁ eDom : A) = (φ eF : A) by exact hgF eF,
      show (g₁ xDom : A) = (Φ xP : A) by exact hgP xS]
    simpa [add_comm] using ht
  exact ⟨g₁, hg₁inj, hg₁floor, hgF, hgP⟩

/-! ### Free climb constrained to the finite challenge -/

/-- Local-socle containment suffices for injectivity when both the old domain
and the adjoined generator remain inside `D`. -/
theorem socle_extend_build_map_injective_within
    {H : AddSubgroup B} (hHD : H ≤ D)
    (hSocle : challengeSocleSubgroup p D ≤ H)
    (φ : H →+ (⊤ : AddSubgroup A)) (hφ : Function.Injective φ)
    {x : B} (hxD : x ∈ D) (hpxH : p • x ∈ H)
    (φ' : adjoinElem H x →+ (⊤ : AddSubgroup A))
    (hφH : ∀ a : H,
      (φ' ⟨a, le_adjoinElem H x a.property⟩ : A) = (φ a : A)) :
    Function.Injective φ' := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, ha, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := H) (g := x)).mp z.property
  have hpzH : p • (z : B) ∈ H := by
    rw [← hrepr, nsmul_add, smul_comm p n x]
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
  have hzD : (z : B) ∈ D := by
    rw [← hrepr]
    exact D.add_mem (hHD ha) (D.zsmul_mem hxD n)
  have hzSocle : (z : B) ∈ pSocleAt p 0 := by
    rw [mem_pSocleAt]
    exact ⟨hpz, by simp [ulmSubgroup_zero]⟩
  let zH : H := ⟨(z : B), hSocle ⟨hzD, hzSocle⟩⟩
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
  have hzB : (z : B) = 0 :=
    congrArg (fun t : H ↦ (t : B)) hzH
  exact Subtype.ext hzB

/-- State carried by the climb inside one finite challenge subgroup. -/
structure LocalFreeClimbStage (D : AddSubgroup B) where
  source : AddSubgroup B
  source_le : source ≤ D
  source_finite : Set.Finite (source : Set B)
  map : source →+ (⊤ : AddSubgroup A)
  map_injective : Function.Injective map
  floor : IsHeightFloorOn p map
  challengeSocle_le : challengeSocleSubgroup p D ≤ source

/-- Literal extension relation between local climb stages. -/
structure LocalFreeClimbStage.Extends
    (s t : LocalFreeClimbStage p (A := A) D) : Prop where
  source_le : s.source ≤ t.source
  map_eq : ∀ x : s.source,
    (t.map ⟨(x : B), source_le x.property⟩ : A) = (s.map x : A)

namespace LocalFreeClimbStage.Extends

omit hp in
theorem refl (s : LocalFreeClimbStage p (A := A) D) :
    LocalFreeClimbStage.Extends p s s :=
  ⟨le_rfl, fun _ ↦ rfl⟩

omit hp in
theorem trans {s t u : LocalFreeClimbStage p (A := A) D}
    (hst : LocalFreeClimbStage.Extends p s t)
    (htu : LocalFreeClimbStage.Extends p t u) :
    LocalFreeClimbStage.Extends p s u := by
  refine ⟨hst.source_le.trans htu.source_le, ?_⟩
  intro x
  calc
    (u.map ⟨(x : B), htu.source_le (hst.source_le x.property)⟩ : A) =
        (t.map ⟨(x : B), hst.source_le x.property⟩ : A) :=
      htu.map_eq ⟨(x : B), hst.source_le x.property⟩
    _ = (s.map x : A) := hst.map_eq x

end LocalFreeClimbStage.Extends

/-- One Kaplansky-normalized extension step, with the new source proved to
remain a subgroup of `D`. -/
theorem LocalFreeClimbStage.extend_one
    (hB : IsReducedPGroup p B)
    (s : LocalFreeClimbStage p (A := A) D) (g : D)
    (hpg : p • (g : B) ∈ s.source) :
    ∃ t : LocalFreeClimbStage p (A := A) D,
      LocalFreeClimbStage.Extends p s t ∧ (g : B) ∈ t.source := by
  by_cases hg : (g : B) ∈ s.source
  · exact ⟨s, LocalFreeClimbStage.Extends.refl p s, hg⟩
  obtain ⟨x, hxg, hxProper, _hpxMax⟩ :=
    exists_kaplanskyNormalized (p := p) s.source_finite (g : B)
  have hxD : x ∈ D := by
    have hrepr : x = (g : B) + (x - (g : B)) := by abel
    rw [hrepr]
    exact D.add_mem g.property (s.source_le hxg)
  have hx : x ∉ s.source := by
    intro hxH
    apply hg
    have hrepr : (g : B) = x - (x - (g : B)) := by abel
    rw [hrepr]
    exact s.source.sub_mem hxH hxg
  have hpx : p • x ∈ s.source := by
    have hrepr : p • x = p • (g : B) + p • (x - (g : B)) := by
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
    FiniteEmbedding.socle_extend_build_map_heightFloor
      p s.map s.floor hx hpx hpw hxα hxSucc hwα hxProper
  have hφinj : Function.Injective φ' :=
    socle_extend_build_map_injective_within p s.source_le
      s.challengeSocle_le s.map s.map_injective hxD hpx φ' hφH
  let H' := adjoinElem s.source x
  have hH'D : H' ≤ D := by
    intro z hz
    obtain ⟨a, ha, n, hrepr⟩ :=
      (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
    rw [← hrepr]
    exact D.add_mem (s.source_le ha) (D.zsmul_mem hxD n)
  have hH'finite : Set.Finite (H' : Set B) :=
    adjoinElem_finite (p := p) hB.primary s.source_finite x
  let t : LocalFreeClimbStage p (A := A) D :=
    { source := H'
      source_le := hH'D
      source_finite := hH'finite
      map := φ'
      map_injective := hφinj
      floor := hφfloor
      challengeSocle_le := s.challengeSocle_le.trans
        (le_adjoinElem s.source x) }
  have hst : LocalFreeClimbStage.Extends p s t := by
    refine ⟨le_adjoinElem s.source x, ?_⟩
    exact hφH
  refine ⟨t, hst, ?_⟩
  have hxg' : x - (g : B) ∈ t.source := hst.source_le hxg
  have hx' : x ∈ t.source := mem_adjoinElem_right s.source x
  have hrepr : (g : B) = x - (x - (g : B)) := by abel
  rw [hrepr]
  exact t.source.sub_mem hx' hxg'

/-- Primaryness reduces one prescribed element of `D` to finitely many local
one-step extensions. -/
theorem LocalFreeClimbStage.extend_to_mem
    (hB : IsReducedPGroup p B)
    (s : LocalFreeClimbStage p (A := A) D) (g : D) :
    ∃ t : LocalFreeClimbStage p (A := A) D,
      LocalFreeClimbStage.Extends p s t ∧ (g : B) ∈ t.source := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : LocalFreeClimbStage p (A := A) D,
        p ^ n • (g : B) ∈ t.source →
        ∃ u : LocalFreeClimbStage p (A := A) D,
          LocalFreeClimbStage.Extends p t u ∧ (g : B) ∈ u.source := by
    intro n
    induction n with
    | zero =>
        intro t hg
        have hg' : (g : B) ∈ t.source := by simpa using hg
        exact ⟨t, LocalFreeClimbStage.Extends.refl p t, hg'⟩
    | succ n ih =>
        intro t hpow
        let y : D := ⟨p ^ n • (g : B), D.nsmul_mem g.property (p ^ n)⟩
        have hpy : p • (y : B) ∈ t.source := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, htt₁, hy₁⟩ := t.extend_one p hB y hpy
        obtain ⟨t₂, ht₁t₂, hg₂⟩ := ih t₁ hy₁
        exact ⟨t₂, LocalFreeClimbStage.Extends.trans p htt₁ ht₁t₂, hg₂⟩
  obtain ⟨n, hn⟩ := hB.primary (g : B)
  exact extend_pow n s (by simpa [hn])

/-- Absorb a finite list of elements of `D` while retaining literal agreement
with the initial map. -/
theorem LocalFreeClimbStage.extend_list
    (hB : IsReducedPGroup p B)
    (s : LocalFreeClimbStage p (A := A) D) (l : List D) :
    ∃ t : LocalFreeClimbStage p (A := A) D,
      LocalFreeClimbStage.Extends p s t ∧
      ∀ g ∈ l, (g : B) ∈ t.source := by
  induction l generalizing s with
  | nil =>
      exact ⟨s, LocalFreeClimbStage.Extends.refl p s, by simp⟩
  | cons g l ih =>
      obtain ⟨t₁, hst₁, hg₁⟩ := s.extend_to_mem p hB g
      obtain ⟨t₂, ht₁t₂, hlt₂⟩ := ih t₁
      refine ⟨t₂, LocalFreeClimbStage.Extends.trans p hst₁ ht₁t₂, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact ht₁t₂.source_le hg₁
      · exact hlt₂ x hxl

/-- **Finite free climb inside `D`.**  The initial domain need contain only
`D ∩ P₀(B)`, not the full ambient socle. -/
theorem finite_free_climb_within
    (hB : IsReducedPGroup p B) (hD : Set.Finite (D : Set B))
    (H : AddSubgroup B) (hHD : H ≤ D)
    (hSocle : challengeSocleSubgroup p D ≤ H)
    (φ : H →+ (⊤ : AddSubgroup A))
    (hφ : Function.Injective φ) (hfloor : IsHeightFloorOn p φ) :
    ∃ f : D →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : H, (f ⟨(x : B), hHD x.property⟩ : A) = (φ x : A) := by
  let s : LocalFreeClimbStage p (A := A) D :=
    { source := H
      source_le := hHD
      source_finite := hD.subset hHD
      map := φ
      map_injective := hφ
      floor := hfloor
      challengeSocle_le := hSocle }
  letI : Fintype D := hD.fintype
  obtain ⟨t, hst, hall⟩ :=
    s.extend_list p hB (Finset.univ.toList)
  have htall : ∀ x : D, (x : B) ∈ t.source := by
    intro x
    exact hall x (by simp)
  let ι : D →+ t.source :=
    { toFun := fun x ↦ ⟨(x : B), htall x⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let f : D →+ (⊤ : AddSubgroup A) := t.map.comp ι
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : t.source ↦ (z : B)) hxy)
  have hfinj : Function.Injective f := t.map_injective.comp hι
  have hffloor : IsHeightFloorOn p f := by
    intro β x hx
    exact t.floor β (ι x) hx
  refine ⟨f, hfinj, hffloor, ?_⟩
  intro x
  change (t.map (ι ⟨(x : B), hHD x.property⟩) : A) = (φ x : A)
  have hιx : ι ⟨(x : B), hHD x.property⟩ =
      ⟨(x : B), hst.source_le x.property⟩ := Subtype.ext rfl
  rw [hιx]
  exact hst.map_eq x

/-! ### End-to-end local sufficiency -/

/-- Finite challenge sufficiency when `K_β` is available only at nonzero
levels of the actual finite challenge reach filtration.  This is the precise
finite-range interface needed after the ACM high-tail reordering. -/
theorem exists_finiteChallenge_embedding_of_reachableKernelRoomBudget
    (hB : IsReducedPGroup p B)
    (F D : AddSubgroup B) (hFD : F ≤ D)
    (hD : Set.Finite (D : Set B))
    (E : AddSubgroup A)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (hbudget : ∀ β : Ordinal.{0},
      (∃ q : FiniteChallenge.challengeRoom p F D,
        q ≠ 0 ∧ q ∈ FiniteChallenge.challengeReach p F D β ∧
          q ∉ FiniteChallenge.challengeReach p F D (Order.succ β)) →
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ f : D →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : F,
        (f ⟨(x : B), hFD x.property⟩ : A) = (φ x : A) := by
  letI : FiniteDimensional (ZMod p)
      (FiniteChallenge.challengeRoom p F D) :=
    FiniteChallenge.challengeRoom_finiteDimensional p hD
  obtain ⟨s, b, hs, r, hcompat⟩ :=
    FiniteChallenge.exists_challenge_basis_compatibleWithReach
      p hB hD hFD
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  have hreachBudget : ∀ i : s,
      Survival.KernelRoomBudgetAt p φ (r i)
        (hfloor (Order.succ (r i))) (hfloor (r i)) := by
    intro i
    apply hbudget (r i)
    refine ⟨b i, b.ne_zero i,
      FiniteChallenge.challengeBasis_mem_reach p b r hcompat i, ?_⟩
    intro hsucc
    rw [hcompat (Order.succ (r i))] at hsucc
    have hi : Order.succ (r i) ≤ r i :=
      b.self_mem_span_image.mp hsucc
    exact (not_le_of_gt (Order.lt_succ (r i))) hi
  obtain ⟨L, Φ, hL, haccess, hΦ, hmark, hquot, hheight⟩ :=
    LocalSocleLift.exists_injective_heightCompatible_challengeSocle_lift_of_reach_budget
      p φ hφ hfloor b r hcompat hreachBudget
  obtain ⟨g₁, hg₁inj, hg₁floor, hgF, _hgP⟩ :=
    exists_injective_heightFloor_challengeSocleExtension
      p hFD φ hφ Φ hΦ hmark hheight
  have hdomD : challengeSocleDomain p F D ≤ D :=
    sup_le hFD inf_le_left
  have hsocle : challengeSocleSubgroup p D ≤
      challengeSocleDomain p F D := by
    intro x hx
    exact AddSubgroup.mem_sup_right hx
  obtain ⟨f, hfinj, hffloor, hfdom⟩ :=
    finite_free_climb_within p hB hD (challengeSocleDomain p F D)
      hdomD hsocle g₁ hg₁inj hg₁floor
  refine ⟨f, hfinj, hffloor, ?_⟩
  intro x
  let xDom : challengeSocleDomain p F D :=
    ⟨(x : B), AddSubgroup.mem_sup_left x.property⟩
  calc
    (f ⟨(x : B), hFD x.property⟩ : A) = (g₁ xDom : A) := hfdom xDom
    _ = (φ x : A) := hgF x

/-- **Finite challenge sufficiency from the ambient room--kernel budget.**

Let `F ≤ D ≤ B`, with `D` finite but ambient `B` arbitrary and reduced
`p`-primary.  An injective marked map `φ : F → E` satisfying the ambient
height floor extends injectively and height-nondecreasingly to `D` whenever
the global `K_β` budget holds at every ordinal.  The target ambient group is
arbitrary; in particular it need not be finite or reduced.
-/
theorem exists_finiteChallenge_embedding_of_kernelRoomBudget
    (hB : IsReducedPGroup p B)
    (F D : AddSubgroup B) (hFD : F ≤ D)
    (hD : Set.Finite (D : Set B))
    (E : AddSubgroup A)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ f : D →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : F,
        (f ⟨(x : B), hFD x.property⟩ : A) = (φ x : A) := by
  letI : FiniteDimensional (ZMod p)
      (FiniteChallenge.challengeRoom p F D) :=
    FiniteChallenge.challengeRoom_finiteDimensional p hD
  obtain ⟨s, b, hs, r, hcompat⟩ :=
    FiniteChallenge.exists_challenge_basis_compatibleWithReach
      p hB hD hFD
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  obtain ⟨L, Φ, hL, haccess, hΦ, hmark, hquot, hheight⟩ :=
    LocalSocleLift.exists_injective_heightCompatible_challengeSocle_lift_of_budget
      p φ hφ hfloor b r hcompat hbudget
  obtain ⟨g₁, hg₁inj, hg₁floor, hgF, _hgP⟩ :=
    exists_injective_heightFloor_challengeSocleExtension
      p hFD φ hφ Φ hΦ hmark hheight
  have hdomD : challengeSocleDomain p F D ≤ D :=
    sup_le hFD inf_le_left
  have hsocle : challengeSocleSubgroup p D ≤
      challengeSocleDomain p F D := by
    intro x hx
    exact AddSubgroup.mem_sup_right hx
  obtain ⟨f, hfinj, hffloor, hfdom⟩ :=
    finite_free_climb_within p hB hD (challengeSocleDomain p F D)
      hdomD hsocle g₁ hg₁inj hg₁floor
  refine ⟨f, hfinj, hffloor, ?_⟩
  intro x
  let xDom : challengeSocleDomain p F D :=
    ⟨(x : B), AddSubgroup.mem_sup_left x.property⟩
  calc
    (f ⟨(x : B), hFD x.property⟩ : A) = (g₁ xDom : A) := hfdom xDom
    _ = (φ x : A) := hgF x

/-! ### Exact-below-cutoff climb without a global floor -/

/-- A finite local stage which preserves filtration membership exactly below
`θ`, without imposing any condition above `θ`.

The tail-containment hypothesis is used only to ensure that every genuinely
new normalized representative has height below `θ`.  This is the low-part
extension package needed by the even ACM response, whose current tuple map
need not have a global height floor. -/
structure LocalCutoffPresStage (D : AddSubgroup B) (θ : Ordinal.{0}) where
  source : AddSubgroup B
  source_le : source ≤ D
  source_finite : Set.Finite (source : Set B)
  map : source →+ (⊤ : AddSubgroup A)
  map_injective : Function.Injective map
  presBelow : IsHeightPresBelowOn p map θ
  tail_le : D ⊓ ulmSubgroup p θ (G := B) ≤ source

/-- Literal extension of cutoff-preservation stages. -/
structure LocalCutoffPresStage.Extends
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (s t : LocalCutoffPresStage p (A := A) D θ) : Prop where
  source_le : s.source ≤ t.source
  map_eq : ∀ x : s.source,
    (t.map ⟨(x : B), source_le x.property⟩ : A) = (s.map x : A)

namespace LocalCutoffPresStage.Extends

theorem refl {D : AddSubgroup B} {θ : Ordinal.{0}}
    (s : LocalCutoffPresStage p (A := A) D θ) :
    LocalCutoffPresStage.Extends p s s :=
  ⟨le_rfl, fun _ ↦ rfl⟩

theorem trans {D : AddSubgroup B} {θ : Ordinal.{0}}
    {s t u : LocalCutoffPresStage p (A := A) D θ}
    (hst : LocalCutoffPresStage.Extends p s t)
    (htu : LocalCutoffPresStage.Extends p t u) :
    LocalCutoffPresStage.Extends p s u := by
  refine ⟨hst.source_le.trans htu.source_le, ?_⟩
  intro x
  calc
    (u.map ⟨(x : B), htu.source_le (hst.source_le x.property)⟩ : A) =
        (t.map ⟨(x : B), hst.source_le x.property⟩ : A) :=
      htu.map_eq ⟨(x : B), hst.source_le x.property⟩
    _ = (s.map x : A) := hst.map_eq x

end LocalCutoffPresStage.Extends

/-- Adjoin one prescribed element while retaining exact filtration membership
below `θ`.  No global height-floor hypothesis is used or produced. -/
theorem LocalCutoffPresStage.extend_one
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffPresStage p (A := A) D θ) (g : D)
    (hpg : p • (g : B) ∈ s.source) :
    ∃ t : LocalCutoffPresStage p (A := A) D θ,
      LocalCutoffPresStage.Extends p s t ∧ (g : B) ∈ t.source := by
  by_cases hg : (g : B) ∈ s.source
  · exact ⟨s, LocalCutoffPresStage.Extends.refl p s, hg⟩
  obtain ⟨x, hxg, hxProper, hpxMax'⟩ :=
    exists_kaplanskyNormalized (p := p) s.source_finite (g : B)
  have hxD : x ∈ D := by
    have hrepr : x = (g : B) + (x - (g : B)) := by abel
    rw [hrepr]
    exact D.add_mem g.property (s.source_le hxg)
  have hx : x ∉ s.source := by
    intro hxH
    apply hg
    have hrepr : (g : B) = x - (x - (g : B)) := by abel
    rw [hrepr]
    exact s.source.sub_mem hxH hxg
  have hpx : p • x ∈ s.source := by
    have hrepr : p • x = p • (g : B) + p • (x - (g : B)) := by
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
  have hx_not_tail : x ∉ ulmSubgroup p θ (G := B) := by
    intro hxθ
    exact hx (s.tail_le ⟨hxD, hxθ⟩)
  have hα : α < θ := by
    by_contra hnot
    exact hx_not_tail (ulmSubgroup_antitone p (le_of_not_gt hnot) hxα)
  have hαsucc : Order.succ α < θ := hθ.succ_lt hα
  have hαsuccSucc : Order.succ (Order.succ α) < θ :=
    hθ.succ_lt hαsucc
  have hpxMax : ∀ y : B, y - x ∈ s.source → IsProper p s.source y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
    intro y hyx hyProper
    apply hpxMax' y
    · have : y - (g : B) = (y - x) + (x - (g : B)) := by abel
      rw [this]
      exact s.source.add_mem hyx hxg
    · exact hyProper
  obtain ⟨w, hpw, hwα, hwSucc, hwProper⟩ :=
    FiniteEmbedding.exists_kaplanskyTarget_of_heightPresBelow
      p s.source_finite s.map s.map_injective s.presBelow
      hα hαsucc hαsuccSucc (hinv α hα) hpx
      hxα hxSucc hxProper hpxMax
  obtain ⟨φ', hφH, _hφx, hφpres⟩ :=
    FiniteEmbedding.socle_extend_build_map_heightPresBelow
      p s.map s.presBelow hx hpx hpw hxα hxSucc hwα hwSucc
      hxProper hwProper
  have hφinj : Function.Injective φ' :=
    FiniteEmbedding.socle_extend_build_map_injective_of_heightPresBelow
      p s.map s.map_injective hxα hxSucc hxProper hpx φ' hφH
      hφpres hαsucc
  let H' : AddSubgroup B := adjoinElem s.source x
  have hH'D : H' ≤ D := by
    intro z hz
    obtain ⟨a, ha, n, hrepr⟩ :=
      (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
    rw [← hrepr]
    exact D.add_mem (s.source_le ha) (D.zsmul_mem hxD n)
  have hH'finite : Set.Finite (H' : Set B) :=
    adjoinElem_finite (p := p) hB.primary s.source_finite x
  let t : LocalCutoffPresStage p (A := A) D θ :=
    { source := H'
      source_le := hH'D
      source_finite := hH'finite
      map := φ'
      map_injective := hφinj
      presBelow := hφpres
      tail_le := s.tail_le.trans (le_adjoinElem s.source x) }
  have hst : LocalCutoffPresStage.Extends p s t := by
    refine ⟨le_adjoinElem s.source x, ?_⟩
    exact hφH
  refine ⟨t, hst, ?_⟩
  have hxg' : x - (g : B) ∈ t.source := hst.source_le hxg
  have hx' : x ∈ t.source := mem_adjoinElem_right s.source x
  have hrepr : (g : B) = x - (x - (g : B)) := by abel
  rw [hrepr]
  exact t.source.sub_mem hx' hxg'

/-- Absorb one prescribed element by descending its finite `p`-power tower. -/
theorem LocalCutoffPresStage.extend_to_mem
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffPresStage p (A := A) D θ) (g : D) :
    ∃ t : LocalCutoffPresStage p (A := A) D θ,
      LocalCutoffPresStage.Extends p s t ∧ (g : B) ∈ t.source := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : LocalCutoffPresStage p (A := A) D θ,
        p ^ n • (g : B) ∈ t.source →
        ∃ u : LocalCutoffPresStage p (A := A) D θ,
          LocalCutoffPresStage.Extends p t u ∧ (g : B) ∈ u.source := by
    intro n
    induction n with
    | zero =>
        intro t hg
        have hg' : (g : B) ∈ t.source := by simpa using hg
        exact ⟨t, LocalCutoffPresStage.Extends.refl p t, hg'⟩
    | succ n ih =>
        intro t hpow
        let y : D := ⟨p ^ n • (g : B), D.nsmul_mem g.property (p ^ n)⟩
        have hpy : p • (y : B) ∈ t.source := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, htt₁, hy₁⟩ := t.extend_one p hB hθ hinv y hpy
        obtain ⟨t₂, ht₁t₂, hg₂⟩ := ih t₁ hy₁
        exact ⟨t₂, LocalCutoffPresStage.Extends.trans p htt₁ ht₁t₂, hg₂⟩
  obtain ⟨n, hn⟩ := hB.primary (g : B)
  exact extend_pow n s (by simpa [hn])

/-- Iterate the cutoff-preserving climb over a finite list. -/
theorem LocalCutoffPresStage.extend_list
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffPresStage p (A := A) D θ) (l : List D) :
    ∃ t : LocalCutoffPresStage p (A := A) D θ,
      LocalCutoffPresStage.Extends p s t ∧
      ∀ g ∈ l, (g : B) ∈ t.source := by
  induction l generalizing s with
  | nil =>
      exact ⟨s, LocalCutoffPresStage.Extends.refl p s, by simp⟩
  | cons g l ih =>
      obtain ⟨t₁, hst₁, hg₁⟩ := s.extend_to_mem p hB hθ hinv g
      obtain ⟨t₂, ht₁t₂, hlt₂⟩ := ih t₁
      refine ⟨t₂, LocalCutoffPresStage.Extends.trans p hst₁ ht₁t₂, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact ht₁t₂.source_le hg₁
      · exact hlt₂ x hxl

/-- Complete a finite challenge from a stage containing its cutoff tail,
retaining injectivity and exact filtration membership below `θ` only. -/
theorem finite_cutoff_pres_climb_within
    (hB : IsReducedPGroup p B) {D : AddSubgroup B}
    (hD : Set.Finite (D : Set B)) {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffPresStage p (A := A) D θ) :
    ∃ f : D →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightPresBelowOn p f θ ∧
      ∀ x : s.source,
        (f ⟨(x : B), s.source_le x.property⟩ : A) = (s.map x : A) := by
  letI : Fintype D := hD.fintype
  obtain ⟨t, hst, hall⟩ :=
    s.extend_list p hB hθ hinv Finset.univ.toList
  have htall : ∀ x : D, (x : B) ∈ t.source := by
    intro x
    exact hall x (by simp)
  let ι : D →+ t.source :=
    { toFun := fun x ↦ ⟨(x : B), htall x⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let f : D →+ (⊤ : AddSubgroup A) := t.map.comp ι
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : t.source ↦ (z : B)) hxy)
  refine ⟨f, t.map_injective.comp hι, ?_, ?_⟩
  · intro β hβ x
    exact t.presBelow β hβ (ι x)
  · intro x
    change (t.map (ι ⟨(x : B), s.source_le x.property⟩) : A) =
      (s.map x : A)
    have hιx : ι ⟨(x : B), s.source_le x.property⟩ =
        ⟨(x : B), hst.source_le x.property⟩ := Subtype.ext rfl
    rw [hιx]
    exact hst.map_eq x

/-! ### Exact-below-cutoff climb after the high tail -/

/-- A finite local stage for the second half of the ACM reordering argument.
The whole challenge tail at `θ` has already been absorbed, the map has a
global height floor, and it preserves filtration membership exactly below
`θ`. -/
structure LocalCutoffClimbStage (D : AddSubgroup B) (θ : Ordinal.{0}) where
  source : AddSubgroup B
  source_le : source ≤ D
  source_finite : Set.Finite (source : Set B)
  map : source →+ (⊤ : AddSubgroup A)
  map_injective : Function.Injective map
  floor : IsHeightFloorOn p map
  presBelow : IsHeightPresBelowOn p map θ
  tail_le : D ⊓ ulmSubgroup p θ (G := B) ≤ source

/-- Literal extension of cutoff-climb stages. -/
structure LocalCutoffClimbStage.Extends
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (s t : LocalCutoffClimbStage p (A := A) D θ) : Prop where
  source_le : s.source ≤ t.source
  map_eq : ∀ x : s.source,
    (t.map ⟨(x : B), source_le x.property⟩ : A) = (s.map x : A)

namespace LocalCutoffClimbStage.Extends

theorem refl {D : AddSubgroup B} {θ : Ordinal.{0}}
    (s : LocalCutoffClimbStage p (A := A) D θ) :
    LocalCutoffClimbStage.Extends p s s :=
  ⟨le_rfl, fun _ ↦ rfl⟩

theorem trans {D : AddSubgroup B} {θ : Ordinal.{0}}
    {s t u : LocalCutoffClimbStage p (A := A) D θ}
    (hst : LocalCutoffClimbStage.Extends p s t)
    (htu : LocalCutoffClimbStage.Extends p t u) :
    LocalCutoffClimbStage.Extends p s u := by
  refine ⟨hst.source_le.trans htu.source_le, ?_⟩
  intro x
  calc
    (u.map ⟨(x : B), htu.source_le (hst.source_le x.property)⟩ : A) =
        (t.map ⟨(x : B), hst.source_le x.property⟩ : A) :=
      htu.map_eq ⟨(x : B), hst.source_le x.property⟩
    _ = (s.map x : A) := hst.map_eq x

end LocalCutoffClimbStage.Extends

/-- One normalized low-height Kaplansky extension.  The tail-containment field
forces every genuinely new normalized representative below `θ`; successor
pre-limitness keeps the three levels used by target selection below the same
cutoff. -/
theorem LocalCutoffClimbStage.extend_one
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffClimbStage p (A := A) D θ) (g : D)
    (hpg : p • (g : B) ∈ s.source) :
    ∃ t : LocalCutoffClimbStage p (A := A) D θ,
      LocalCutoffClimbStage.Extends p s t ∧ (g : B) ∈ t.source := by
  by_cases hg : (g : B) ∈ s.source
  · exact ⟨s, LocalCutoffClimbStage.Extends.refl p s, hg⟩
  obtain ⟨x, hxg, hxProper, hpxMax'⟩ :=
    exists_kaplanskyNormalized (p := p) s.source_finite (g : B)
  have hxD : x ∈ D := by
    have hrepr : x = (g : B) + (x - (g : B)) := by abel
    rw [hrepr]
    exact D.add_mem g.property (s.source_le hxg)
  have hx : x ∉ s.source := by
    intro hxH
    apply hg
    have hrepr : (g : B) = x - (x - (g : B)) := by abel
    rw [hrepr]
    exact s.source.sub_mem hxH hxg
  have hpx : p • x ∈ s.source := by
    have hrepr : p • x = p • (g : B) + p • (x - (g : B)) := by
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
  have hx_not_tail : x ∉ ulmSubgroup p θ (G := B) := by
    intro hxθ
    exact hx (s.tail_le ⟨hxD, hxθ⟩)
  have hα : α < θ := by
    by_contra hnot
    exact hx_not_tail (ulmSubgroup_antitone p (le_of_not_gt hnot) hxα)
  have hαsucc : Order.succ α < θ := hθ.succ_lt hα
  have hαsuccSucc : Order.succ (Order.succ α) < θ :=
    hθ.succ_lt hαsucc
  have hpxMax : ∀ y : B, y - x ∈ s.source → IsProper p s.source y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
    intro y hyx hyProper
    apply hpxMax' y
    · have : y - (g : B) = (y - x) + (x - (g : B)) := by abel
      rw [this]
      exact s.source.add_mem hyx hxg
    · exact hyProper
  obtain ⟨w, hpw, hwα, hwSucc, hwProper⟩ :=
    FiniteEmbedding.exists_kaplanskyTarget_of_heightPresBelow
      p s.source_finite s.map s.map_injective s.presBelow
      hα hαsucc hαsuccSucc (hinv α hα) hpx
      hxα hxSucc hxProper hpxMax
  obtain ⟨φ', hφH, _hφx, hφfloor, hφpres⟩ :=
    FiniteEmbedding.socle_extend_build_map_heightFloor_heightPresBelow
      p s.map s.floor s.presBelow hx hpx hpw hxα hxSucc hwα hwSucc
      hxProper hwProper
  have hφinj : Function.Injective φ' :=
    FiniteEmbedding.socle_extend_build_map_injective_of_heightPresBelow
      p s.map s.map_injective hxα hxSucc hxProper hpx φ' hφH
      hφpres hαsucc
  let H' : AddSubgroup B := adjoinElem s.source x
  have hH'D : H' ≤ D := by
    intro z hz
    obtain ⟨a, ha, n, hrepr⟩ :=
      (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
    rw [← hrepr]
    exact D.add_mem (s.source_le ha) (D.zsmul_mem hxD n)
  have hH'finite : Set.Finite (H' : Set B) :=
    adjoinElem_finite (p := p) hB.primary s.source_finite x
  let t : LocalCutoffClimbStage p (A := A) D θ :=
    { source := H'
      source_le := hH'D
      source_finite := hH'finite
      map := φ'
      map_injective := hφinj
      floor := hφfloor
      presBelow := hφpres
      tail_le := s.tail_le.trans (le_adjoinElem s.source x) }
  have hst : LocalCutoffClimbStage.Extends p s t := by
    refine ⟨le_adjoinElem s.source x, ?_⟩
    exact hφH
  refine ⟨t, hst, ?_⟩
  have hxg' : x - (g : B) ∈ t.source := hst.source_le hxg
  have hx' : x ∈ t.source := mem_adjoinElem_right s.source x
  have hrepr : (g : B) = x - (x - (g : B)) := by abel
  rw [hrepr]
  exact t.source.sub_mem hx' hxg'

/-- Absorb one prescribed element by descending a finite `p`-power tower. -/
theorem LocalCutoffClimbStage.extend_to_mem
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffClimbStage p (A := A) D θ) (g : D) :
    ∃ t : LocalCutoffClimbStage p (A := A) D θ,
      LocalCutoffClimbStage.Extends p s t ∧ (g : B) ∈ t.source := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : LocalCutoffClimbStage p (A := A) D θ,
        p ^ n • (g : B) ∈ t.source →
        ∃ u : LocalCutoffClimbStage p (A := A) D θ,
          LocalCutoffClimbStage.Extends p t u ∧ (g : B) ∈ u.source := by
    intro n
    induction n with
    | zero =>
        intro t hg
        have hg' : (g : B) ∈ t.source := by simpa using hg
        exact ⟨t, LocalCutoffClimbStage.Extends.refl p t, hg'⟩
    | succ n ih =>
        intro t hpow
        let y : D := ⟨p ^ n • (g : B), D.nsmul_mem g.property (p ^ n)⟩
        have hpy : p • (y : B) ∈ t.source := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, htt₁, hy₁⟩ := t.extend_one p hB hθ hinv y hpy
        obtain ⟨t₂, ht₁t₂, hg₂⟩ := ih t₁ hy₁
        exact ⟨t₂, LocalCutoffClimbStage.Extends.trans p htt₁ ht₁t₂, hg₂⟩
  obtain ⟨n, hn⟩ := hB.primary (g : B)
  exact extend_pow n s (by simpa [hn])

/-- Iterate the cutoff climb over a finite list. -/
theorem LocalCutoffClimbStage.extend_list
    (hB : IsReducedPGroup p B)
    {D : AddSubgroup B} {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffClimbStage p (A := A) D θ) (l : List D) :
    ∃ t : LocalCutoffClimbStage p (A := A) D θ,
      LocalCutoffClimbStage.Extends p s t ∧
      ∀ g ∈ l, (g : B) ∈ t.source := by
  induction l generalizing s with
  | nil =>
      exact ⟨s, LocalCutoffClimbStage.Extends.refl p s, by simp⟩
  | cons g l ih =>
      obtain ⟨t₁, hst₁, hg₁⟩ := s.extend_to_mem p hB hθ hinv g
      obtain ⟨t₂, ht₁t₂, hlt₂⟩ := ih t₁
      refine ⟨t₂, LocalCutoffClimbStage.Extends.trans p hst₁ ht₁t₂, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact ht₁t₂.source_le hg₁
      · exact hlt₂ x hxl

/-- Complete a finite challenge from any stage that already contains the
entire cutoff tail. -/
theorem finite_cutoff_climb_within
    (hB : IsReducedPGroup p B) {D : AddSubgroup B}
    (hD : Set.Finite (D : Set B)) {θ : Ordinal.{0}}
    (hθ : Order.IsSuccPrelimit θ)
    (hinv : ∀ β : Ordinal.{0}, β < θ →
      ulmInvariant p β (G := B) = ulmInvariant p β (G := A))
    (s : LocalCutoffClimbStage p (A := A) D θ) :
    ∃ f : D →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      IsHeightPresBelowOn p f θ ∧
      ∀ x : s.source,
        (f ⟨(x : B), s.source_le x.property⟩ : A) = (s.map x : A) := by
  letI : Fintype D := hD.fintype
  obtain ⟨t, hst, hall⟩ :=
    s.extend_list p hB hθ hinv Finset.univ.toList
  have htall : ∀ x : D, (x : B) ∈ t.source := by
    intro x
    exact hall x (by simp)
  let ι : D →+ t.source :=
    { toFun := fun x ↦ ⟨(x : B), htall x⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let f : D →+ (⊤ : AddSubgroup A) := t.map.comp ι
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : t.source ↦ (z : B)) hxy)
  refine ⟨f, t.map_injective.comp hι, ?_, ?_, ?_⟩
  · intro β x hx
    exact t.floor β (ι x) hx
  · intro β hβ x
    exact t.presBelow β hβ (ι x)
  · intro x
    change (t.map (ι ⟨(x : B), s.source_le x.property⟩) : A) =
      (s.map x : A)
    have hιx : ι ⟨(x : B), s.source_le x.property⟩ =
        ⟨(x : B), hst.source_le x.property⟩ := Subtype.ext rfl
    rw [hιx]
    exact hst.map_eq x

end LocalFiniteEmbedding
