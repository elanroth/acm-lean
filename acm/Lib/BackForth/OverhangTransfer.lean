import Lib.BackForth.InducedMap

/-!
# Mark-only presentation of the overhang

For a marked subgroup `E`, the BCM overhang at `β` has a presentation using
only the filtered pieces of `E`:
`(p (E ∩ G_β) ∩ G_(β+2)) / p (E ∩ G_(β+1))`.

This file first exposes that quotient as a typed `ZMod p` vector space.  The
subsequent equivalence with `overhangSubmodule` is deliberately kept here,
where its transport along a finite height equivalence can be reviewed without
touching the even back-and-forth development.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [AddCommGroup G]

/-- The mark-only numerator for the BCM overhang. -/
noncomputable def overhangMarkOnlyNum (E : AddSubgroup G) (β : Ordinal.{0}) :
    AddSubgroup G :=
  pImage p (E ⊓ ulmSubgroup p β) ⊓
    ulmSubgroup p (Order.succ (Order.succ β))

/-- The mark-only denominator for the BCM overhang. -/
noncomputable def overhangMarkOnlyDen (E : AddSubgroup G) (β : Ordinal.{0}) :
    AddSubgroup G :=
  pImage p (E ⊓ ulmSubgroup p (Order.succ β))

lemma overhangMarkOnlyDen_le_num (E : AddSubgroup G) (β : Ordinal.{0}) :
    overhangMarkOnlyDen p E β ≤ overhangMarkOnlyNum p E β := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨⟨y, ⟨hy.1, ulmSubgroup_antitone p (Order.le_succ β) hy.2⟩, rfl⟩, ?_⟩
  rw [ulmSubgroup_succ]
  exact ⟨y, hy.2, rfl⟩

/-- The denominator as a subgroup of the mark-only numerator. -/
noncomputable def overhangMarkOnlyDenIn (E : AddSubgroup G) (β : Ordinal.{0}) :
    AddSubgroup (overhangMarkOnlyNum p E β) :=
  (overhangMarkOnlyDen p E β).comap (overhangMarkOnlyNum p E β).subtype

/-- The mark-only overhang quotient. -/
abbrev overhangMarkOnlyQuotient (E : AddSubgroup G) (β : Ordinal.{0}) : Type u :=
  (overhangMarkOnlyNum p E β) ⧸ overhangMarkOnlyDenIn p E β

/-- Multiplication by `p` lands in the mark-only denominator. -/
lemma smul_mem_overhangMarkOnlyDen (E : AddSubgroup G) (β : Ordinal.{0})
    {x : G} (hx : x ∈ overhangMarkOnlyNum p E β) :
    p • x ∈ overhangMarkOnlyDen p E β := by
  rcases hx.1 with ⟨y, hy, hpy⟩
  have hpyHigh : p • y ∈ ulmSubgroup p (Order.succ (Order.succ β)) := by
    simpa [hpy] using hx.2
  refine ⟨p • y, ?_, ?_⟩
  · exact ⟨E.nsmul_mem hy.1 p,
      ulmSubgroup_antitone p (Order.le_succ (Order.succ β)) hpyHigh⟩
  · simpa [hpy]

/-- The mark-only quotient is naturally an `F_p`-vector space. -/
noncomputable instance overhangMarkOnlyQuotient_module (E : AddSubgroup G)
    (β : Ordinal.{0}) : Module (ZMod p) (overhangMarkOnlyQuotient p E β) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := overhangMarkOnlyNum p E β) (H := overhangMarkOnlyDenIn p E β) ?_
  intro x
  change ((p • (x : G) : G)) ∈ overhangMarkOnlyDen p E β
  exact smul_mem_overhangMarkOnlyDen p E β x.property

/-- The canonical map whose range is the already-defined overhang submodule. -/
noncomputable def hillDenToMarkedQuotient (E : AddSubgroup G) (β : Ordinal.{0}) :
    hillSubmodule p E β →ₗ[ZMod p] markedGradedQuotient p E β :=
  (markedGradedSubmodule p E β).mkQ.domRestrict (hillSubmodule p E β)

/-- The quotient of the Hill denominator by the marked denominator.  It is
written as the kernel quotient of its canonical map; the later mark-only
equivalence identifies this kernel with the displayed marked denominator. -/
abbrev overhangDenominatorQuotient (E : AddSubgroup G) (β : Ordinal.{0}) : Type u :=
  (hillSubmodule p E β) ⧸ LinearMap.ker (hillDenToMarkedQuotient p E β)

/-- The Hill-denominator quotient is canonically the BCM overhang submodule. -/
noncomputable def overhangDenominatorQuotientEquiv (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    overhangDenominatorQuotient p E β ≃ₗ[ZMod p] overhangSubmodule p E β := by
  let f := hillDenToMarkedQuotient p E β
  exact (LinearMap.quotKerEquivRange f).trans
    (LinearEquiv.ofEq f.range (overhangSubmodule p E β) (by
      simp only [f, hillDenToMarkedQuotient, LinearMap.range_domRestrict,
        overhangSubmodule]))

/-! ### The mark-only boundary map -/

/-- A chosen decomposition `s = e + t` of an element of the Hill denominator,
with `e ∈ E` and `t ∈ G_(β+1)`.  Only its class modulo the marked denominator
will be used. -/
private noncomputable def overhangDecomposition (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) :
    { et : G × G // et.1 ∈ E ∧
      et.2 ∈ ulmSubgroup p (Order.succ β) ∧ et.1 + et.2 = (s : G) } := by
  classical
  have hs : (s : G) ∈ E ⊔ ulmSubgroup p (Order.succ β) := by
    exact s.property.2
  let e := Classical.choose (AddSubgroup.mem_sup.mp hs)
  have heRest := Classical.choose_spec (AddSubgroup.mem_sup.mp hs)
  have he : e ∈ E := heRest.1
  let t := Classical.choose heRest.2
  have htRest := Classical.choose_spec heRest.2
  have ht : t ∈ ulmSubgroup p (Order.succ β) := htRest.1
  have het : e + t = (s : G) := htRest.2
  exact ⟨(e, t), he, ht, het⟩

private lemma overhangDecomposition_mark_mem (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) :
    (overhangDecomposition p E β s).1.1 ∈ E :=
  (overhangDecomposition p E β s).2.1

private lemma overhangDecomposition_high_mem (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) :
    (overhangDecomposition p E β s).1.2 ∈ ulmSubgroup p (Order.succ β) :=
  (overhangDecomposition p E β s).2.2.1

private lemma overhangDecomposition_add (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) :
    (overhangDecomposition p E β s).1.1 +
        (overhangDecomposition p E β s).1.2 = (s : G) :=
  (overhangDecomposition p E β s).2.2.2

/-- The numerator representative `p e` attached to a Hill-denominator element
`s = e + t`. -/
private noncomputable def overhangBoundaryNum (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) : overhangMarkOnlyNum p E β := by
  let e := (overhangDecomposition p E β s).1.1
  let t := (overhangDecomposition p E β s).1.2
  have heE : e ∈ E := overhangDecomposition_mark_mem p E β s
  have htHigh : t ∈ ulmSubgroup p (Order.succ β) :=
    overhangDecomposition_high_mem p E β s
  have hsum : e + t = (s : G) := overhangDecomposition_add p E β s
  have hsβ : (s : G) ∈ ulmSubgroup p β := s.1.property.2
  have htβ : t ∈ ulmSubgroup p β :=
    ulmSubgroup_antitone p (Order.le_succ β) htHigh
  have heβ : e ∈ ulmSubgroup p β := by
    have heq : e = (s : G) - t := by rw [← hsum]; abel
    rw [heq]
    exact (ulmSubgroup p β).sub_mem hsβ htβ
  have hptHigh : p • t ∈ ulmSubgroup p (Order.succ (Order.succ β)) := by
    rw [ulmSubgroup_succ]
    exact ⟨t, htHigh, rfl⟩
  have hps : p • (s : G) = 0 := (mem_pSocleAt p β (s : G)).1 s.1.property |>.1
  have hpe : p • e = -(p • t) := by
    have hadd := congrArg (fun z : G ↦ p • z) hsum
    change p • (e + t) = p • (s : G) at hadd
    rw [smul_add, hps] at hadd
    exact eq_neg_of_add_eq_zero_left hadd
  refine ⟨p • e, ?_, ?_⟩
  · exact ⟨e, ⟨heE, heβ⟩, rfl⟩
  · rw [hpe]
    exact (ulmSubgroup p (Order.succ (Order.succ β))).neg_mem hptHigh

/-- The boundary homomorphism from the Hill denominator to the mark-only
overhang quotient.  Different choices of `s = e + t` differ by an element of
`E ∩ G_(β+1)`, so the class of `p e` is additive. -/
private noncomputable def overhangBoundaryHom (E : AddSubgroup G) (β : Ordinal.{0}) :
    hillSubmodule p E β →+ overhangMarkOnlyQuotient p E β where
  toFun s := QuotientAddGroup.mk (overhangBoundaryNum p E β s)
  map_zero' := by
    let e := (overhangDecomposition p E β (0 : hillSubmodule p E β)).1.1
    let t := (overhangDecomposition p E β (0 : hillSubmodule p E β)).1.2
    have heE : e ∈ E := overhangDecomposition_mark_mem p E β 0
    have htHigh : t ∈ ulmSubgroup p (Order.succ β) :=
      overhangDecomposition_high_mem p E β 0
    have hsum : e + t = 0 := by
      simpa using overhangDecomposition_add p E β (0 : hillSubmodule p E β)
    have heHigh : e ∈ ulmSubgroup p (Order.succ β) := by
      have heq : e = -t := eq_neg_of_add_eq_zero_left hsum
      rw [heq]
      exact (ulmSubgroup p (Order.succ β)).neg_mem htHigh
    apply QuotientAddGroup.eq.mpr
    change (-((overhangBoundaryNum p E β 0 : overhangMarkOnlyNum p E β) : G) + 0) ∈
      overhangMarkOnlyDen p E β
    refine ⟨-e, ⟨E.neg_mem heE,
      (ulmSubgroup p (Order.succ β)).neg_mem heHigh⟩, ?_⟩
    change p • (-e) = -(p • e) + 0
    simp
  map_add' s r := by
    let es := (overhangDecomposition p E β s).1.1
    let ts := (overhangDecomposition p E β s).1.2
    let er := (overhangDecomposition p E β r).1.1
    let tr := (overhangDecomposition p E β r).1.2
    let esr := (overhangDecomposition p E β (s + r)).1.1
    let tsr := (overhangDecomposition p E β (s + r)).1.2
    have hesE : es ∈ E := overhangDecomposition_mark_mem p E β s
    have herE : er ∈ E := overhangDecomposition_mark_mem p E β r
    have hesrE : esr ∈ E := overhangDecomposition_mark_mem p E β (s + r)
    have htsHigh : ts ∈ ulmSubgroup p (Order.succ β) :=
      overhangDecomposition_high_mem p E β s
    have htrHigh : tr ∈ ulmSubgroup p (Order.succ β) :=
      overhangDecomposition_high_mem p E β r
    have htsrHigh : tsr ∈ ulmSubgroup p (Order.succ β) :=
      overhangDecomposition_high_mem p E β (s + r)
    have hs : es + ts = (s : G) := overhangDecomposition_add p E β s
    have hr : er + tr = (r : G) := overhangDecomposition_add p E β r
    have hsr : esr + tsr = (s + r : hillSubmodule p E β) :=
      overhangDecomposition_add p E β (s + r)
    let z := (es + er) - esr
    have hzE : z ∈ E := E.sub_mem (E.add_mem hesE herE) hesrE
    have hzEq : z = tsr - (ts + tr) := by
      have hsr' : esr = (s + r : hillSubmodule p E β) - tsr := by
        rw [← hsr]
        abel
      change (es + er) - esr = tsr - (ts + tr)
      rw [hsr']
      change (es + er) - (((s : G) + (r : G)) - tsr) = tsr - (ts + tr)
      rw [← hs, ← hr]
      abel
    have hzHigh : z ∈ ulmSubgroup p (Order.succ β) := by
      rw [hzEq]
      exact (ulmSubgroup p (Order.succ β)).sub_mem htsrHigh
        ((ulmSubgroup p (Order.succ β)).add_mem htsHigh htrHigh)
    apply QuotientAddGroup.eq.mpr
    change (-((overhangBoundaryNum p E β (s + r) :
        overhangMarkOnlyNum p E β) : G) +
      (((overhangBoundaryNum p E β s : overhangMarkOnlyNum p E β) : G) +
        ((overhangBoundaryNum p E β r : overhangMarkOnlyNum p E β) : G))) ∈
      overhangMarkOnlyDen p E β
    refine ⟨z, ⟨hzE, hzHigh⟩, ?_⟩
    change p • z = -(p • esr) + (p • es + p • er)
    simp only [z, smul_sub, smul_add]
    abel

/-- The boundary map as a `ZMod p`-linear map. -/
private noncomputable def overhangBoundary (E : AddSubgroup G) (β : Ordinal.{0}) :
    hillSubmodule p E β →ₗ[ZMod p] overhangMarkOnlyQuotient p E β :=
  (overhangBoundaryHom p E β).toZModLinearMap p

private theorem overhangBoundary_eq_zero_iff (E : AddSubgroup G) (β : Ordinal.{0})
    (s : hillSubmodule p E β) :
    overhangBoundary p E β s = 0 ↔ hillDenToMarkedQuotient p E β s = 0 := by
  let e := (overhangDecomposition p E β s).1.1
  let t := (overhangDecomposition p E β s).1.2
  have heE : e ∈ E := overhangDecomposition_mark_mem p E β s
  have htHigh : t ∈ ulmSubgroup p (Order.succ β) :=
    overhangDecomposition_high_mem p E β s
  have hsum : e + t = (s : G) := overhangDecomposition_add p E β s
  have hsP : p • (s : G) = 0 := (mem_pSocleAt p β (s : G)).1 s.1.property |>.1
  have hsβ : (s : G) ∈ ulmSubgroup p β := s.1.property.2
  constructor
  · intro hboundary
    change QuotientAddGroup.mk (overhangBoundaryNum p E β s) = 0 at hboundary
    have hpeDenIn : overhangBoundaryNum p E β s ∈ overhangMarkOnlyDenIn p E β :=
      (QuotientAddGroup.eq_zero_iff (overhangBoundaryNum p E β s)).1 hboundary
    have hpeDen : ((overhangBoundaryNum p E β s :
        overhangMarkOnlyNum p E β) : G) ∈ overhangMarkOnlyDen p E β := hpeDenIn
    obtain ⟨e', he', hpe'⟩ := hpeDen
    have hpe : p • e' = p • e := by simpa using hpe'
    let y := e' + t
    let z := e - e'
    have hyHigh : y ∈ ulmSubgroup p (Order.succ β) :=
      (ulmSubgroup p (Order.succ β)).add_mem he'.2 htHigh
    have hpy : p • y = 0 := by
      simp only [y, smul_add, hpe]
      have hpadd := congrArg (fun w : G ↦ p • w) hsum
      change p • (e + t) = p • (s : G) at hpadd
      rw [smul_add, hsP] at hpadd
      exact hpadd
    have hyP : y ∈ pSocleAt p (Order.succ β) :=
      (mem_pSocleAt p (Order.succ β) y).2 ⟨hpy, hyHigh⟩
    have hzE : z ∈ E := E.sub_mem heE he'.1
    have hpz : p • z = 0 := by
      simp only [z, smul_sub, hpe]
      exact sub_self (p • e)
    have hzβ : z ∈ ulmSubgroup p β := by
      have heβ : e ∈ ulmSubgroup p β := by
        have heq : e = (s : G) - t := by rw [← hsum]; abel
        rw [heq]
        exact (ulmSubgroup p β).sub_mem hsβ
          (ulmSubgroup_antitone p (Order.le_succ β) htHigh)
      exact (ulmSubgroup p β).sub_mem heβ
        (ulmSubgroup_antitone p (Order.le_succ β) he'.2)
    have hzP : z ∈ pSocleAt p β := (mem_pSocleAt p β z).2 ⟨hpz, hzβ⟩
    have hsMarked : (s.1 : pSocleAt p β) ∈ markedGradedSubmodule p E β := by
      change (s : G) ∈ pSocleAt p (Order.succ β) ⊔ (E ⊓ pSocleAt p β)
      refine AddSubgroup.mem_sup.mpr ⟨y, hyP, z, ⟨hzE, hzP⟩, ?_⟩
      simp only [y, z]
      rw [← hsum]
      abel
    change (markedGradedSubmodule p E β).mkQ s.1 = 0
    exact (Submodule.Quotient.mk_eq_zero (markedGradedSubmodule p E β)).2 hsMarked
  · intro hmarked
    change (markedGradedSubmodule p E β).mkQ s.1 = 0 at hmarked
    have hsMarked : (s.1 : pSocleAt p β) ∈ markedGradedSubmodule p E β :=
      (Submodule.Quotient.mk_eq_zero (markedGradedSubmodule p E β)).1 hmarked
    change (s : G) ∈ pSocleAt p (Order.succ β) ⊔ (E ⊓ pSocleAt p β) at hsMarked
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hsMarked
    let d := e - z
    have hdE : d ∈ E := E.sub_mem heE hz.1
    have hdEq : d = y - t := by
      change e - z = y - t
      have heq : e + t = y + z := hsum.trans hyz.symm
      have he : e = y + z - t := by
        calc
          e = e + t - t := by abel
          _ = y + z - t := by rw [heq]
      rw [he]
      abel
    have hdHigh : d ∈ ulmSubgroup p (Order.succ β) := by
      rw [hdEq]
      exact (ulmSubgroup p (Order.succ β)).sub_mem hy.2 htHigh
    have hpz : p • z = 0 := (mem_pSocleAt p β z).1 hz.2 |>.1
    apply QuotientAddGroup.eq.mpr
    change (-((overhangBoundaryNum p E β s : overhangMarkOnlyNum p E β) : G) + 0) ∈
      overhangMarkOnlyDen p E β
    refine ⟨-d, ⟨E.neg_mem hdE,
      (ulmSubgroup p (Order.succ β)).neg_mem hdHigh⟩, ?_⟩
    change p • (-d) = -(p • e) + 0
    simp only [d, smul_neg, smul_sub, hpz, add_zero]
    rw [_root_.sub_zero]

private theorem overhangBoundary_ker (E : AddSubgroup G) (β : Ordinal.{0}) :
    LinearMap.ker (overhangBoundary p E β) =
      LinearMap.ker (hillDenToMarkedQuotient p E β) := by
  ext s
  simp only [LinearMap.mem_ker]
  exact overhangBoundary_eq_zero_iff p E β s

private theorem overhangBoundary_surjective (E : AddSubgroup G) (β : Ordinal.{0}) :
    Function.Surjective (overhangBoundary p E β) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H c =>
      obtain ⟨e, he, hpe⟩ := c.property.1
      obtain ⟨u, huHigh, hpu⟩ :=
        (mem_ulmSubgroup_succ_iff p (Order.succ β) (c : G)).1 c.property.2
      let t := -u
      let x : G := e + t
      have htHigh : t ∈ ulmSubgroup p (Order.succ β) :=
        (ulmSubgroup p (Order.succ β)).neg_mem huHigh
      have hxβ : x ∈ ulmSubgroup p β :=
        (ulmSubgroup p β).add_mem he.2
          (ulmSubgroup_antitone p (Order.le_succ β) htHigh)
      have hpx : p • x = 0 := by
        simp only [x, t, smul_add, smul_neg, hpe, hpu]
        exact add_neg_cancel (c : G)
      have hxP : x ∈ pSocleAt p β := (mem_pSocleAt p β x).2 ⟨hpx, hxβ⟩
      let s : hillSubmodule p E β :=
        ⟨⟨x, hxP⟩, by
          change x ∈ pSocleAt p β ⊓ (E ⊔ ulmSubgroup p (Order.succ β))
          exact ⟨hxP, AddSubgroup.mem_sup.mpr ⟨e, he.1, t, htHigh, rfl⟩⟩⟩
      refine ⟨s, ?_⟩
      let e' := (overhangDecomposition p E β s).1.1
      let t' := (overhangDecomposition p E β s).1.2
      have he'E : e' ∈ E := overhangDecomposition_mark_mem p E β s
      have ht'High : t' ∈ ulmSubgroup p (Order.succ β) :=
        overhangDecomposition_high_mem p E β s
      have hsum' : e' + t' = (s : G) := overhangDecomposition_add p E β s
      let z := e - e'
      have hzE : z ∈ E := E.sub_mem he.1 he'E
      have hzEq : z = t' + u := by
        change e - e' = t' + u
        have hsx : (s : G) = e - u := by
          change x = e - u
          simp only [x, t, sub_eq_add_neg]
        have heq : e' + t' = e - u := hsum'.trans hsx
        have he' : e' = e - u - t' := by
          calc
            e' = e' + t' - t' := by abel
            _ = e - u - t' := by rw [heq]
        rw [he']
        abel
      have hzHigh : z ∈ ulmSubgroup p (Order.succ β) := by
        rw [hzEq]
        exact (ulmSubgroup p (Order.succ β)).add_mem ht'High huHigh
      apply QuotientAddGroup.eq.mpr
      change (-((overhangBoundaryNum p E β s : overhangMarkOnlyNum p E β) : G) +
        (c : G)) ∈ overhangMarkOnlyDen p E β
      refine ⟨z, ⟨hzE, hzHigh⟩, ?_⟩
      change p • z = -(p • e') + (c : G)
      simp only [z, smul_sub, hpe]
      abel

/-- **Lemma 3.1 (mark-only presentation).** The quotient built only from the
filtered pieces of the mark is linearly equivalent to the Hill denominator
modulo the marked denominator. -/
noncomputable def overhangMarkOnlyQuotientEquiv (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    overhangMarkOnlyQuotient p E β ≃ₗ[ZMod p]
      overhangDenominatorQuotient p E β :=
  ((overhangBoundary p E β).quotKerEquivOfSurjective
      (overhangBoundary_surjective p E β)).symm.trans
    (Submodule.quotEquivOfEq
      (LinearMap.ker (overhangBoundary p E β))
      (LinearMap.ker (hillDenToMarkedQuotient p E β))
      (overhangBoundary_ker p E β))

/-- The mark-only quotient is the existing BCM overhang submodule. -/
noncomputable def overhangMarkOnlyEquivOverhang (E : AddSubgroup G)
    (β : Ordinal.{0}) :
    overhangMarkOnlyQuotient p E β ≃ₗ[ZMod p] overhangSubmodule p E β :=
  (overhangMarkOnlyQuotientEquiv p E β).trans
    (overhangDenominatorQuotientEquiv p E β)

/-! ### Transport through a height equivalence -/

/-- A height-preserving equivalence of marks carries the mark-only numerator
through `β+2`. -/
private noncomputable def overhangMarkOnlyNumMap
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    overhangMarkOnlyNum p F β →+ overhangMarkOnlyNum p E β where
  toFun c := by
    classical
    have hcF : (c : G) ∈ F :=
      ((pImage_le p (F ⊓ ulmSubgroup p β)) c.property.1).1
    let cF : F := ⟨(c : G), hcF⟩
    let x := Classical.choose c.property.1
    have hxRest := Classical.choose_spec c.property.1
    have hx : x ∈ F ⊓ ulmSubgroup p β := hxRest.1
    have hpx : p • x = (c : G) := hxRest.2
    let xF : F := ⟨x, hx.1⟩
    have hxfil : (φ xF : H) ∈ ulmSubgroup p β :=
      (hφ β hβ xF).mp hx.2
    have hcfil : (φ cF : H) ∈ ulmSubgroup p (Order.succ (Order.succ β)) :=
      (hφ (Order.succ (Order.succ β)) hβ₂ cF).mp c.property.2
    refine ⟨(φ cF : H), ?_, hcfil⟩
    refine ⟨(φ xF : H), ⟨(φ xF).property, hxfil⟩, ?_⟩
    change p • (φ xF : H) = (φ cF : H)
    change ((p • φ xF : E) : H) = (φ cF : H)
    rw [← map_nsmul]
    apply congrArg (fun z : F ↦ (φ z : H))
    apply Subtype.ext
    exact hpx
  map_zero' := by
    apply Subtype.ext
    change (φ ⟨(0 : G), _⟩ : H) = 0
    rw [show (⟨(0 : G), _⟩ : F) = 0 by rfl, map_zero]
    rfl
  map_add' c d := by
    apply Subtype.ext
    have hcF : (c : G) ∈ F :=
      ((pImage_le p (F ⊓ ulmSubgroup p β)) c.property.1).1
    have hdF : (d : G) ∈ F :=
      ((pImage_le p (F ⊓ ulmSubgroup p β)) d.property.1).1
    change (φ ⟨(c : G) + (d : G), F.add_mem hcF hdF⟩ : H) =
      (φ ⟨(c : G), hcF⟩ : H) + (φ ⟨(d : G), hdF⟩ : H)
    have hcdF : (⟨(c : G) + (d : G), F.add_mem hcF hdF⟩ : F) =
        (⟨(c : G), hcF⟩ : F) + ⟨(d : G), hdF⟩ := rfl
    rw [hcdF, map_add]
    rfl

private theorem overhangMarkOnlyNumMap_coe
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ)
    (c : overhangMarkOnlyNum p F β) :
    ((overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂ c :
        overhangMarkOnlyNum p E β) : H) =
      (φ ⟨(c : G), ((pImage_le p (F ⊓ ulmSubgroup p β)) c.property.1).1⟩ : H) :=
  rfl

private theorem overhangMarkOnlyNumMap_bijective
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    Function.Bijective (overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂) := by
  constructor
  · intro c d hcd
    have hunder :
        ((overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂ c :
            overhangMarkOnlyNum p E β) : H) =
          ((overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂ d :
            overhangMarkOnlyNum p E β) : H) :=
      congrArg (fun z : overhangMarkOnlyNum p E β ↦ (z : H)) hcd
    have hφcd :
        φ ⟨(c : G), ((pImage_le p (F ⊓ ulmSubgroup p β)) c.property.1).1⟩ =
          φ ⟨(d : G), ((pImage_le p (F ⊓ ulmSubgroup p β)) d.property.1).1⟩ := by
      apply Subtype.ext
      simpa only [overhangMarkOnlyNumMap_coe] using hunder
    have hcdF := φ.injective hφcd
    apply Subtype.ext
    exact congrArg (fun z : F ↦ (z : G)) hcdF
  · intro y
    have hyE : (y : H) ∈ E :=
      ((pImage_le p (E ⊓ ulmSubgroup p β)) y.property.1).1
    let yE : E := ⟨(y : H), hyE⟩
    let cF : F := φ.symm yE
    obtain ⟨v, hv, hpv⟩ := y.property.1
    let vE : E := ⟨v, hv.1⟩
    let uF : F := φ.symm vE
    have huβ : (uF : G) ∈ ulmSubgroup p β := by
      apply (hφ β hβ uF).mpr
      simpa [uF, vE] using hv.2
    have hcβ₂ : (cF : G) ∈ ulmSubgroup p (Order.succ (Order.succ β)) := by
      apply (hφ (Order.succ (Order.succ β)) hβ₂ cF).mpr
      simpa [cF, yE] using y.property.2
    have hpc : p • uF = cF := by
      apply φ.injective
      rw [map_nsmul]
      apply Subtype.ext
      simpa [uF, vE, cF, yE] using hpv
    let c : overhangMarkOnlyNum p F β :=
      ⟨(cF : G), ⟨⟨(uF : G), ⟨uF.property, huβ⟩,
        congrArg (fun z : F ↦ (z : G)) hpc⟩, hcβ₂⟩⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [overhangMarkOnlyNumMap_coe p F E φ θ hφ β hβ hβ₂]
    change (φ cF : H) = (y : H)
    simp [cF, yE]

private noncomputable def overhangMarkOnlyNumEquiv
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    overhangMarkOnlyNum p F β ≃+ overhangMarkOnlyNum p E β :=
  AddEquiv.ofBijective (overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂)
    (overhangMarkOnlyNumMap_bijective p F E φ θ hφ β hβ hβ₂)

private theorem overhangMarkOnlyNumEquiv_map_den
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    (overhangMarkOnlyDenIn p F β).map
        (overhangMarkOnlyNumEquiv p F E φ θ hφ β hβ hβ₂).toAddMonoidHom =
      overhangMarkOnlyDenIn p E β := by
  let eNum := overhangMarkOnlyNumEquiv p F E φ θ hφ β hβ hβ₂
  have hβ₁ : Order.succ β < θ :=
    (Order.lt_succ (Order.succ β)).trans hβ₂
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change ((eNum x : overhangMarkOnlyNum p E β) : H) ∈ overhangMarkOnlyDen p E β
    change (x : G) ∈ overhangMarkOnlyDen p F β at hx
    obtain ⟨u, hu, hpu⟩ := hx
    let uF : F := ⟨u, hu.1⟩
    have huHigh : (φ uF : H) ∈ ulmSubgroup p (Order.succ β) :=
      (hφ (Order.succ β) hβ₁ uF).mp hu.2
    refine ⟨(φ uF : H), ⟨(φ uF).property, huHigh⟩, ?_⟩
    change p • (φ uF : H) =
      ((overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂ x :
        overhangMarkOnlyNum p E β) : H)
    rw [overhangMarkOnlyNumMap_coe]
    change ((p • φ uF : E) : H) =
      (φ ⟨(x : G), ((pImage_le p (F ⊓ ulmSubgroup p β)) x.property.1).1⟩ : H)
    rw [← map_nsmul]
    apply congrArg (fun z : F ↦ (φ z : H))
    apply Subtype.ext
    exact hpu
  · intro y hy
    change (y : H) ∈ overhangMarkOnlyDen p E β at hy
    obtain ⟨v, hv, hpv⟩ := hy
    let vE : E := ⟨v, hv.1⟩
    let uF : F := φ.symm vE
    have huHigh : (uF : G) ∈ ulmSubgroup p (Order.succ β) := by
      apply (hφ (Order.succ β) hβ₁ uF).mpr
      simpa [uF, vE] using hv.2
    obtain ⟨x, hx⟩ :=
      (overhangMarkOnlyNumMap_bijective p F E φ θ hφ β hβ hβ₂).2 y
    have hxu : (x : G) = p • (uF : G) := by
      let xF : F :=
        ⟨(x : G), ((pImage_le p (F ⊓ ulmSubgroup p β)) x.property.1).1⟩
      have hxuF : xF = p • uF := by
        apply φ.injective
        apply Subtype.ext
        have hxy :
            ((overhangMarkOnlyNumMap p F E φ θ hφ β hβ hβ₂ x :
              overhangMarkOnlyNum p E β) : H) = (y : H) :=
          congrArg (fun z : overhangMarkOnlyNum p E β ↦ (z : H)) hx
        rw [overhangMarkOnlyNumMap_coe] at hxy
        change (φ xF : H) = (y : H) at hxy
        calc
          (φ xF : H) = (y : H) := hxy
          _ = p • v := hpv.symm
          _ = ((p • vE : E) : H) := rfl
          _ = ((p • φ uF : E) : H) := by simp [uF, vE]
          _ = (φ (p • uF) : H) := by rw [map_nsmul]
      exact congrArg (fun z : F ↦ (z : G)) hxuF
    refine ⟨x, ?_, ?_⟩
    · change (x : G) ∈ overhangMarkOnlyDen p F β
      refine ⟨(uF : G), ⟨uF.property, huHigh⟩, ?_⟩
      exact hxu.symm
    · exact hx

/-- A height equivalence through `β+2` transports the mark-only overhang
quotient. -/
noncomputable def overhangMarkOnlyTransport
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    overhangMarkOnlyQuotient p F β ≃ₗ[ZMod p]
      overhangMarkOnlyQuotient p E β := by
  let eNum := overhangMarkOnlyNumEquiv p F E φ θ hφ β hβ hβ₂
  let eQuot := QuotientAddGroup.congr
    (overhangMarkOnlyDenIn p F β) (overhangMarkOnlyDenIn p E β) eNum
    (overhangMarkOnlyNumEquiv_map_den p F E φ θ hφ β hβ hβ₂)
  exact LinearEquiv.ofBijective (eQuot.toAddMonoidHom.toZModLinearMap p)
    eQuot.bijective

/-- Transport of the existing overhang submodules, obtained by passing through
the mark-only presentation on both sides. -/
noncomputable def overhangTransport
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    overhangSubmodule p F β ≃ₗ[ZMod p] overhangSubmodule p E β :=
  (overhangMarkOnlyEquivOverhang p F β).symm.trans
    ((overhangMarkOnlyTransport p F E φ θ hφ β hβ hβ₂).trans
      (overhangMarkOnlyEquivOverhang p E β))

/-- Height equivalence through `β+2` identifies the overhang ranks. -/
theorem overhangInvariant_eq_of_heightPresBelow
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (φ : F ≃+ E)
    (θ : Ordinal.{0}) (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ) :
    overhangInvariant p F β = overhangInvariant p E β :=
  (overhangTransport p F E φ θ hφ β hβ hβ₂).rank_eq

/-- A finite mark has finite overhang rank. -/
theorem overhangInvariant_lt_aleph0
    (E : AddSubgroup G) (hE : Set.Finite (E : Set G)) (β : Ordinal.{0}) :
    overhangInvariant p E β < ℵ₀ := by
  unfold overhangInvariant
  rw [← (overhangMarkOnlyEquivOverhang p E β).rank_eq]
  letI : Finite E := Set.finite_coe_iff.mp hE
  let toE : overhangMarkOnlyNum p E β → E := fun x ↦
    ⟨(x : G), ((pImage_le p (E ⊓ ulmSubgroup p β)) x.property.1).1⟩
  have htoE : Function.Injective toE := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : E ↦ (z : G)) hxy
  letI : Finite (overhangMarkOnlyNum p E β) := Finite.of_injective toE htoE
  letI : Finite (overhangMarkOnlyQuotient p E β) :=
    Finite.of_surjective (QuotientAddGroup.mk (s := overhangMarkOnlyDenIn p E β))
      QuotientAddGroup.mk_surjective
  exact Module.rank_lt_aleph0 (ZMod p) (overhangMarkOnlyQuotient p E β)

/-- Finite overhang cancellation converts marked-graded equality into standard
Hill equality once the mark is height-equivalent through `β+2`. -/
theorem hillInvariant_eq_of_markedGraded_eq_of_heightPresBelow
    {H : Type u} [AddCommGroup H]
    (F : AddSubgroup G) (E : AddSubgroup H) (hF : Set.Finite (F : Set G))
    (φ : F ≃+ E) (θ : Ordinal.{0})
    (hφ : IsHeightPresBelowOn p φ.toAddMonoidHom θ)
    (β : Ordinal.{0}) (hβ : β < θ)
    (hβ₂ : Order.succ (Order.succ β) < θ)
    (hmarked : markedGradedInvariant p F β = markedGradedInvariant p E β) :
    hillInvariant p F β = hillInvariant p E β := by
  have hover : overhangInvariant p F β = overhangInvariant p E β :=
    overhangInvariant_eq_of_heightPresBelow p F E φ θ hφ β hβ hβ₂
  have hfinite : overhangInvariant p F β < ℵ₀ :=
    overhangInvariant_lt_aleph0 p F hF β
  apply (Cardinal.add_right_inj_of_lt_aleph0 hfinite).1
  calc
    hillInvariant p F β + overhangInvariant p F β =
        markedGradedInvariant p F β := hillInvariant_add_overhangInvariant p F β
    _ = markedGradedInvariant p E β := hmarked
    _ = hillInvariant p E β + overhangInvariant p E β :=
      (hillInvariant_add_overhangInvariant p E β).symm
    _ = hillInvariant p E β + overhangInvariant p F β := by rw [hover]
