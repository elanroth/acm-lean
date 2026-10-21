import Lib.BackForth.EvenHighCountdown

/-!
# The cap-truncated finite countdown for the long odd response

The printed long odd construction asks the target to follow the full source
height.  The corrected odd condition only supplies a height floor through
`ω * α + ω`, so that step is not available.  The finite challenge needs less:
reserve one finite unit of height for every remaining root extension, decrease
that reserve after each extension, and finish with a floor at `ω * α`.

Throughout the countdown the map preserves filtration membership exactly
below `ω * α`.  This is the predecessor invariant consumed by the outer
transfinite induction.
-/

noncomputable section

open Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]

namespace AlgebraicBFConditions.OddLongCountdown

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

/-- A finite stage of the corrected long odd countdown.  At fuel `N`, the
current map has a height floor through `ω * α + N`; only the fixed base is
preserved in both directions. -/
structure Stage
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (D : AddSubgroup H) (N : ℕ) : Type u where
  source : AddSubgroup H
  source_le : source ≤ D
  source_finite : Set.Finite (source : Set H)
  map : source →+ (⊤ : AddSubgroup G)
  map_injective : Function.Injective map
  presBelow : IsHeightPresBelowOn p map (ω * α)
  floorThrough : ∀ β : Ordinal.{0}, β ≤ ω * α + N →
    IsHeightFloorAt p map β
  mark_le : tupleSubgroup b ≤ source
  mark : ∀ x : tupleSubgroup b,
    (map ⟨(x : H), mark_le x.property⟩ : G) =
      (C.iso.equiv x : G)

/-- Literal extension of countdown stages. -/
structure Stage.Extends
    {hG : IsReducedPGroup p G} {hH : IsReducedPGroup p H}
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : AlgBFOddCondData p hG hH α a b}
    {D : AddSubgroup H} {N N' : ℕ}
    (s : Stage p hG hH C D N) (t : Stage p hG hH C D N') : Prop where
  source_le : s.source ≤ t.source
  map_eq : ∀ x : s.source,
    (t.map ⟨(x : H), source_le x.property⟩ : G) = (s.map x : G)

namespace Stage.Extends

theorem refl
    {hG : IsReducedPGroup p G} {hH : IsReducedPGroup p H}
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : AlgBFOddCondData p hG hH α a b}
    {D : AddSubgroup H} {N : ℕ}
    (s : Stage p hG hH C D N) : Stage.Extends p s s :=
  ⟨le_rfl, fun _ ↦ rfl⟩

theorem trans
    {hG : IsReducedPGroup p G} {hH : IsReducedPGroup p H}
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : AlgBFOddCondData p hG hH α a b}
    {D : AddSubgroup H} {N₁ N₂ N₃ : ℕ}
    {s : Stage p hG hH C D N₁}
    {t : Stage p hG hH C D N₂}
    {u : Stage p hG hH C D N₃}
    (hst : Stage.Extends p s t) (htu : Stage.Extends p t u) :
    Stage.Extends p s u := by
  refine ⟨hst.source_le.trans htu.source_le, ?_⟩
  intro x
  calc
    (u.map ⟨(x : H), htu.source_le (hst.source_le x.property)⟩ : G) =
        (t.map ⟨(x : H), hst.source_le x.property⟩ : G) :=
      htu.map_eq ⟨(x : H), hst.source_le x.property⟩
    _ = (s.map x : G) := hst.map_eq x

theorem cast
    {hG : IsReducedPGroup p G} {hH : IsReducedPGroup p H}
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    {C : AlgBFOddCondData p hG hH α a b}
    {D : AddSubgroup H} {N N' : ℕ}
    (s : Stage p hG hH C D N) (h : N = N') :
    Stage.Extends p s (h ▸ s) := by
  subst N'
  exact refl p s

end Stage.Extends

/-- The old odd tuple map starts the countdown at every finite reserve below
the cap. -/
noncomputable def Stage.initial
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (D : AddSubgroup H) (hmarkD : tupleSubgroup b ≤ D)
    (N : ℕ) (hNcap : ω * α + N < ω * α + ω) :
    Stage p hG hH C D N := by
  let raw : tupleSubgroup b →+ G :=
    (tupleSubgroup a).subtype.comp C.iso.equiv.toAddMonoidHom
  let f : tupleSubgroup b →+ (⊤ : AddSubgroup G) :=
    raw.codRestrict ⊤ (fun _ ↦ by simp)
  refine
    { source := tupleSubgroup b
      source_le := hmarkD
      source_finite := tupleSubgroup_finite p hH.primary b
      map := f
      map_injective := ?_
      presBelow := ?_
      floorThrough := ?_
      mark_le := le_rfl
      mark := ?_ }
  · intro x y hxy
    apply C.iso.equiv.injective
    apply Subtype.ext
    exact congrArg (fun z : (⊤ : AddSubgroup G) ↦ (z : G)) hxy
  · intro β hβ x
    simpa [f, raw] using
      (heightPresBelowOn_of_heights p C.iso C.heights β hβ x)
  · intro β hβ
    intro x hx
    have hβcap : β ≤ ω * α + ω := hβ.trans (le_of_lt hNcap)
    simpa [f, raw] using
      (heightFloorAt_of_heights p C.iso C.heights β hβcap x hx)
  · intro x
    rfl

/-- Spend one unit of reserve without changing the map. -/
noncomputable def Stage.lower
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (D : AddSubgroup H) (N : ℕ)
    (s : Stage p hG hH C D (N + 1)) :
    Stage p hG hH C D N := by
  have hnewOld : ω * α + N < ω * α + (N + 1) := by
    rw [add_lt_add_iff_left]
    exact_mod_cast Nat.lt_succ_self N
  exact
    { source := s.source
      source_le := s.source_le
      source_finite := s.source_finite
      map := s.map
      map_injective := s.map_injective
      presBelow := s.presBelow
      floorThrough := fun β hβ ↦ s.floorThrough β (hβ.trans (le_of_lt hnewOld))
      mark_le := s.mark_le
      mark := s.mark }

/-- At any level in the long window, a root can be perturbed by a fresh
filtered socle direction so that it avoids a prescribed finite range. -/
theorem exists_target_root_outside_range
    (hG : IsReducedPGroup p G)
    {α ρ : Ordinal.{0}}
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (hbase : ω * α ≤ ρ) (hcap : ρ < ω * α + ω)
    {S : AddSubgroup H} (hSfinite : Set.Finite (S : Set H))
    (φ : S →+ (⊤ : AddSubgroup G))
    (y : G) (hy : y ∈ ulmSubgroup p (Order.succ ρ) (G := G)) :
    ∃ w : G,
      p • w = y ∧ w ∈ ulmSubgroup p ρ (G := G) ∧
      w ∉ AddMonoidHom.range ((⊤ : AddSubgroup G).subtype.comp φ) := by
  classical
  let raw : S →+ G := (⊤ : AddSubgroup G).subtype.comp φ
  let R : AddSubgroup G := AddMonoidHom.range raw
  rw [mem_ulmSubgroup_succ_iff] at hy
  obtain ⟨w₁, hw₁, hpw₁⟩ := hy
  have hPinf : Set.Infinite (pSocleAt p ρ (G := G) : Set G) :=
    AlgBFEvenCondData.infinite_pSocleAt_of_longWindow
      p hG hlong hbase hcap
  have hRfinite : Set.Finite (R : Set G) := by
    letI : Finite S := hSfinite.to_subtype
    change Set.Finite (Set.range raw)
    exact Set.finite_range raw
  have hR₁finite : Set.Finite (adjoinElem R w₁ : Set G) :=
    adjoinElem_finite (p := p) hG.primary hRfinite w₁
  have hex : ∃ w₂ : G,
      w₂ ∈ pSocleAt p ρ (G := G) ∧ w₂ ∉ adjoinElem R w₁ := by
    by_contra hnone
    push Not at hnone
    apply hPinf
    exact hR₁finite.subset (fun z hz ↦ hnone z hz)
  obtain ⟨w₂, hw₂P, hw₂out⟩ := hex
  have hpw₂ : p • w₂ = 0 := (mem_pSocleAt p _ w₂).1 hw₂P |>.1
  have hw₂ : w₂ ∈ ulmSubgroup p ρ (G := G) :=
    (mem_pSocleAt p _ w₂).1 hw₂P |>.2
  let w : G := w₁ + w₂
  refine ⟨w, by simp [w, smul_add, hpw₁, hpw₂],
    (ulmSubgroup p ρ).add_mem hw₁ hw₂, ?_⟩
  intro hwR
  apply hw₂out
  have hwR' : w ∈ R := hwR
  have hw₁adj : w₁ ∈ adjoinElem R w₁ := mem_adjoinElem_right R w₁
  have hwadj : w ∈ adjoinElem R w₁ := le_adjoinElem R w₁ hwR'
  have hw₂eq : w₂ = w - w₁ := by simp [w]
  rw [hw₂eq]
  exact (adjoinElem R w₁).sub_mem hwadj hw₁adj

/-- A literal one-generator extension inherits every queried floor through a
cutoff when the chosen image reaches the source representative's exact
height. -/
theorem floorThrough_of_exact_extension
    {S : AddSubgroup H} (φ : S →+ (⊤ : AddSubgroup G))
    {x : H} {w : G} {ρ θ : Ordinal.{0}}
    (hfloor : ∀ β : Ordinal.{0}, β ≤ θ → IsHeightFloorAt p φ β)
    (hxρ : x ∈ ulmSubgroup p ρ (G := H))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ ρ) (G := H))
    (hwρ : w ∈ ulmSubgroup p ρ (G := G))
    (hxProper : IsProper p S x) (hpx : p • x ∈ S)
    (hpw : p • w = (φ ⟨p • x, hpx⟩ : G))
    (φ' : adjoinElem S x →+ (⊤ : AddSubgroup G))
    (hφS : ∀ z : S,
      (φ' ⟨(z : H), le_adjoinElem S x z.property⟩ : G) = (φ z : G))
    (hφx : (φ' ⟨x, mem_adjoinElem_right S x⟩ : G) = w) :
    ∀ β : Ordinal.{0}, β ≤ θ → IsHeightFloorAt p φ' β := by
  intro β hβ z hz
  obtain ⟨a, ha, k, hrepr⟩ :=
    (mem_adjoinElem_iff (A := S) (g := x)).mp z.property
  let aS : S := ⟨a, ha⟩
  let a' : adjoinElem S x := ⟨a, le_adjoinElem S x ha⟩
  let x' : adjoinElem S x := ⟨x, mem_adjoinElem_right S x⟩
  have hzrepr : z = a' + k • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap : (φ' z : G) = (φ aS : G) + k • w := by
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : G) + k • (φ' x' : G) =
      (φ aS : G) + k • w
    rw [show (φ' a' : G) = (φ aS : G) by
      simpa [a', aS] using hφS aS]
    rw [show (φ' x' : G) = w by simpa [x'] using hφx]
  change (φ' z : G) ∈ ulmSubgroup p β (G := G)
  rw [hmap]
  apply FiniteEmbedding.proper_adjoin_rep_mem_imp_at p φ
    (hfloor β hβ) hxρ hxSucc hwρ hxProper hpx hpw aS k
  rw [hzrepr] at hz
  exact hz

/-- If both the new source representative and its chosen image lie in the
cutoff subgroup, then a literal extension inherits every old floor through
that cutoff. -/
theorem floorThrough_of_mem_extension
    {S : AddSubgroup H} (φ : S →+ (⊤ : AddSubgroup G))
    {x : H} {w : G} {θ : Ordinal.{0}}
    (hfloor : ∀ β : Ordinal.{0}, β ≤ θ → IsHeightFloorAt p φ β)
    (hxθ : x ∈ ulmSubgroup p θ (G := H))
    (hwθ : w ∈ ulmSubgroup p θ (G := G))
    (φ' : adjoinElem S x →+ (⊤ : AddSubgroup G))
    (hφS : ∀ z : S,
      (φ' ⟨(z : H), le_adjoinElem S x z.property⟩ : G) = (φ z : G))
    (hφx : (φ' ⟨x, mem_adjoinElem_right S x⟩ : G) = w) :
    ∀ β : Ordinal.{0}, β ≤ θ → IsHeightFloorAt p φ' β := by
  intro β hβ z hz
  obtain ⟨a, ha, k, hrepr⟩ :=
    (mem_adjoinElem_iff (A := S) (g := x)).mp z.property
  let aS : S := ⟨a, ha⟩
  let a' : adjoinElem S x := ⟨a, le_adjoinElem S x ha⟩
  let x' : adjoinElem S x := ⟨x, mem_adjoinElem_right S x⟩
  have hxβ : x ∈ ulmSubgroup p β (G := H) :=
    ulmSubgroup_antitone p hβ hxθ
  have hwβ : w ∈ ulmSubgroup p β (G := G) :=
    ulmSubgroup_antitone p hβ hwθ
  have haβ : a ∈ ulmSubgroup p β (G := H) := by
    have hkx := (ulmSubgroup p β (G := H)).zsmul_mem hxβ k
    have := (ulmSubgroup p β (G := H)).sub_mem hz hkx
    rw [← hrepr] at this
    simpa using this
  have hmap : (φ' z : G) = (φ aS : G) + k • w := by
    have hzrepr : z = a' + k • x' := by
      apply Subtype.ext
      simpa [a', x'] using hrepr.symm
    rw [hzrepr, map_add, map_zsmul]
    change (φ' a' : G) + k • (φ' x' : G) =
      (φ aS : G) + k • w
    rw [show (φ' a' : G) = (φ aS : G) by
      simpa [a', aS] using hφS aS]
    rw [show (φ' x' : G) = w by simpa [x'] using hφx]
  change (φ' z : G) ∈ ulmSubgroup p β (G := G)
  rw [hmap]
  exact (ulmSubgroup p β (G := G)).add_mem
    (hfloor β hβ aS haβ)
    ((ulmSubgroup p β (G := G)).zsmul_mem hwβ k)

/-- The exact-height branch of one countdown step.  It is used only below the
fixed base, where the odd condition supplies equality of Ulm invariants. -/
theorem Stage.extend_low
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (D : AddSubgroup H) (N : ℕ)
    (s : Stage p hG hH C D (N + 1))
    {x : H} (hxD : x ∈ D) (hx : x ∉ s.source)
    (hpx : p • x ∈ s.source)
    (hxProper : IsProper p s.source x)
    (hpxMax : ∀ y : H, y - x ∈ s.source → IsProper p s.source y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x))
    {ρ : Ordinal.{0}}
    (hxρ : x ∈ ulmSubgroup p ρ (G := H))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ ρ) (G := H))
    (hρbase : ρ < ω * α) :
    ∃ t : Stage p hG hH C D N,
      Stage.Extends p s t ∧ x ∈ t.source := by
  have hω : Order.IsSuccLimit (ω : Ordinal.{0}) :=
    Ordinal.isSuccLimit_omega0
  have hbasePre : Order.IsSuccPrelimit (ω * α) :=
    Ordinal.isSuccPrelimit_mul_left hω
  have hρsucc : Order.succ ρ < ω * α := hbasePre.succ_lt hρbase
  have hρsuccSucc : Order.succ (Order.succ ρ) < ω * α :=
    hbasePre.succ_lt hρsucc
  obtain ⟨w, hpw, hwρ, hwSucc, hwProper⟩ :=
    FiniteEmbedding.exists_kaplanskyTarget_of_heightPresBelow
      p s.source_finite s.map s.map_injective s.presBelow
      hρbase hρsucc hρsuccSucc (C.ulm_below ρ hρbase)
      hpx hxρ hxSucc hxProper hpxMax
  obtain ⟨φ', hφS, hφx, hφpres⟩ :=
    FiniteEmbedding.socle_extend_build_map_heightPresBelow
      p s.map s.presBelow hx hpx hpw hxρ hxSucc hwρ hwSucc
      hxProper hwProper
  have hφinj : Function.Injective φ' :=
    FiniteEmbedding.socle_extend_build_map_injective_of_heightPresBelow
      p s.map s.map_injective hxρ hxSucc hxProper hpx φ' hφS
      hφpres hρsucc
  have hnewOld : ω * α + N < ω * α + (N + 1) := by
    rw [add_lt_add_iff_left]
    exact_mod_cast Nat.lt_succ_self N
  have hφfloor : ∀ β : Ordinal.{0}, β ≤ ω * α + N →
      IsHeightFloorAt p φ' β :=
    floorThrough_of_exact_extension p s.map
      (fun β hβ ↦ s.floorThrough β (hβ.trans (le_of_lt hnewOld)))
      hxρ hxSucc hwρ hxProper hpx hpw φ' hφS hφx
  let S' : AddSubgroup H := adjoinElem s.source x
  have hS'D : S' ≤ D := by
    intro z hz
    obtain ⟨y, hy, k, hrepr⟩ :=
      (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
    rw [← hrepr]
    exact D.add_mem (s.source_le hy) (D.zsmul_mem hxD k)
  have hS'finite : Set.Finite (S' : Set H) :=
    adjoinElem_finite (p := p) hH.primary s.source_finite x
  let t : Stage p hG hH C D N :=
    { source := S'
      source_le := hS'D
      source_finite := hS'finite
      map := φ'
      map_injective := hφinj
      presBelow := hφpres
      floorThrough := hφfloor
      mark_le := s.mark_le.trans (le_adjoinElem s.source x)
      mark := fun z ↦ by
        simpa using (hφS ⟨(z : H), s.mark_le z.property⟩).trans (s.mark z) }
  refine ⟨t, ⟨le_adjoinElem s.source x, ?_⟩,
    mem_adjoinElem_right s.source x⟩
  exact hφS

/-- The high branch of one countdown step.  If the normalized source height
is below the new finite cutoff, the target follows that exact source level;
otherwise both representatives are kept at the new cutoff.  Freshness, not a
claim about the full source height, supplies injectivity. -/
theorem Stage.extend_high
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (D : AddSubgroup H) (N : ℕ)
    (s : Stage p hG hH C D (N + 1))
    {x : H} (hxD : x ∈ D) (hx : x ∉ s.source)
    (hpx : p • x ∈ s.source)
    (hxProper : IsProper p s.source x)
    {ρ : Ordinal.{0}}
    (hxρ : x ∈ ulmSubgroup p ρ (G := H))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ ρ) (G := H))
    (hbaseρ : ω * α ≤ ρ) :
    ∃ t : Stage p hG hH C D N,
      Stage.Extends p s t ∧ x ∈ t.source := by
  let cutoff : Ordinal.{0} := ω * α + N
  let oldCutoff : Ordinal.{0} := ω * α + (N + 1)
  have hcutOld : cutoff < oldCutoff := by
    dsimp only [cutoff, oldCutoff]
    rw [add_lt_add_iff_left]
    exact_mod_cast Nat.lt_succ_self N
  have hcutCap : cutoff < ω * α + ω := by
    dsimp only [cutoff]
    rw [add_lt_add_iff_left]
    exact Ordinal.natCast_lt_omega0 N
  by_cases hρcut : ρ ≤ cutoff
  · have hxSuccMem : p • x ∈
        ulmSubgroup p (Order.succ ρ) (G := H) := by
      rw [ulmSubgroup_succ]
      exact ⟨x, hxρ, rfl⟩
    have hsuccOld : Order.succ ρ ≤ oldCutoff := by
      exact (Order.succ_le_succ hρcut).trans_eq (by
        dsimp only [cutoff, oldCutoff]
        rw [show Order.succ (ω * α + N) = ω * α + (N + 1) by
          simp [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
            ← add_assoc]])
    have hy : (s.map ⟨p • x, hpx⟩ : G) ∈
        ulmSubgroup p (Order.succ ρ) (G := G) :=
      s.floorThrough (Order.succ ρ) hsuccOld ⟨p • x, hpx⟩ hxSuccMem
    obtain ⟨w, hpw, hwρ, hwout⟩ :=
      exists_target_root_outside_range p hG hlong hbaseρ
        (hρcut.trans_lt hcutCap) s.source_finite s.map
        (s.map ⟨p • x, hpx⟩ : G) hy
    obtain ⟨φ', hφS, hφx, hφpres⟩ :=
      FiniteEmbedding.socle_extend_build_map_heightPresBelow_of_mem
        p s.map s.presBelow hx hpx hpw
        (ulmSubgroup_antitone p hbaseρ hxρ)
        (ulmSubgroup_antitone p hbaseρ hwρ)
    have hφinj : Function.Injective φ' :=
      FiniteEmbedding.socle_extend_build_map_injective_of_not_mem_range
        p s.map s.map_injective hpx hpw hwout φ' hφS hφx
    have hφfloor : ∀ β : Ordinal.{0}, β ≤ cutoff →
        IsHeightFloorAt p φ' β :=
      floorThrough_of_exact_extension p s.map
        (fun β hβ ↦ s.floorThrough β (hβ.trans (le_of_lt hcutOld)))
        hxρ hxSucc hwρ hxProper hpx hpw φ' hφS hφx
    let S' : AddSubgroup H := adjoinElem s.source x
    have hS'D : S' ≤ D := by
      intro z hz
      obtain ⟨y, hyS, k, hrepr⟩ :=
        (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
      rw [← hrepr]
      exact D.add_mem (s.source_le hyS) (D.zsmul_mem hxD k)
    have hS'finite : Set.Finite (S' : Set H) :=
      adjoinElem_finite (p := p) hH.primary s.source_finite x
    let t : Stage p hG hH C D N :=
      { source := S'
        source_le := hS'D
        source_finite := hS'finite
        map := φ'
        map_injective := hφinj
        presBelow := hφpres
        floorThrough := by simpa [cutoff] using hφfloor
        mark_le := s.mark_le.trans (le_adjoinElem s.source x)
        mark := fun z ↦ by
          simpa using (hφS ⟨(z : H), s.mark_le z.property⟩).trans (s.mark z) }
    refine ⟨t, ⟨le_adjoinElem s.source x, ?_⟩,
      mem_adjoinElem_right s.source x⟩
    exact hφS
  · have hcutρ : cutoff ≤ ρ := le_of_not_ge hρcut
    have hxCut : x ∈ ulmSubgroup p cutoff (G := H) :=
      ulmSubgroup_antitone p hcutρ hxρ
    have hxOld : p • x ∈ ulmSubgroup p oldCutoff (G := H) := by
      have hsuccCut : Order.succ cutoff = oldCutoff := by
        dsimp only [cutoff, oldCutoff]
        simp [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ← add_assoc]
      rw [← hsuccCut, ulmSubgroup_succ]
      exact ⟨x, hxCut, rfl⟩
    have hy : (s.map ⟨p • x, hpx⟩ : G) ∈
        ulmSubgroup p oldCutoff (G := G) :=
      s.floorThrough oldCutoff le_rfl ⟨p • x, hpx⟩ hxOld
    have hySucc : (s.map ⟨p • x, hpx⟩ : G) ∈
        ulmSubgroup p (Order.succ cutoff) (G := G) := by
      simpa [cutoff, oldCutoff, Order.succ_eq_add_one, Nat.cast_add,
        Nat.cast_one, ← add_assoc] using hy
    obtain ⟨w, hpw, hwCut, hwout⟩ :=
      exists_target_root_outside_range p hG hlong
        (le_self_add : ω * α ≤ cutoff) hcutCap
        s.source_finite s.map (s.map ⟨p • x, hpx⟩ : G) hySucc
    obtain ⟨φ', hφS, hφx, hφpres⟩ :=
      FiniteEmbedding.socle_extend_build_map_heightPresBelow_of_mem
        p s.map s.presBelow hx hpx hpw
        (ulmSubgroup_antitone p (le_self_add : ω * α ≤ cutoff) hxCut)
        (ulmSubgroup_antitone p (le_self_add : ω * α ≤ cutoff) hwCut)
    have hφinj : Function.Injective φ' :=
      FiniteEmbedding.socle_extend_build_map_injective_of_not_mem_range
        p s.map s.map_injective hpx hpw hwout φ' hφS hφx
    have hφfloor : ∀ β : Ordinal.{0}, β ≤ cutoff →
        IsHeightFloorAt p φ' β :=
      floorThrough_of_mem_extension p s.map
        (fun β hβ ↦ s.floorThrough β (hβ.trans (le_of_lt hcutOld)))
        hxCut hwCut φ' hφS hφx
    let S' : AddSubgroup H := adjoinElem s.source x
    have hS'D : S' ≤ D := by
      intro z hz
      obtain ⟨y, hyS, k, hrepr⟩ :=
        (mem_adjoinElem_iff (A := s.source) (g := x)).mp hz
      rw [← hrepr]
      exact D.add_mem (s.source_le hyS) (D.zsmul_mem hxD k)
    have hS'finite : Set.Finite (S' : Set H) :=
      adjoinElem_finite (p := p) hH.primary s.source_finite x
    let t : Stage p hG hH C D N :=
      { source := S'
        source_le := hS'D
        source_finite := hS'finite
        map := φ'
        map_injective := hφinj
        presBelow := hφpres
        floorThrough := by simpa [cutoff] using hφfloor
        mark_le := s.mark_le.trans (le_adjoinElem s.source x)
        mark := fun z ↦ by
          simpa using (hφS ⟨(z : H), s.mark_le z.property⟩).trans (s.mark z) }
    refine ⟨t, ⟨le_adjoinElem s.source x, ?_⟩,
      mem_adjoinElem_right s.source x⟩
    exact hφS

/-- One prescribed-root step: normalize once, then use exact low selection or
the finite long-window margin according to the attained source height. -/
theorem Stage.extend_one
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (D : AddSubgroup H) (N : ℕ)
    (s : Stage p hG hH C D (N + 1)) (g : D)
    (hpg : p • (g : H) ∈ s.source) :
    ∃ t : Stage p hG hH C D N,
      Stage.Extends p s t ∧ (g : H) ∈ t.source := by
  by_cases hg : (g : H) ∈ s.source
  · let t := s.lower p hG hH C D N
    exact ⟨t, ⟨le_rfl, fun _ ↦ rfl⟩, hg⟩
  obtain ⟨x, hxg, hxProper, hpxMax'⟩ :=
    exists_kaplanskyNormalized (p := p) s.source_finite (g : H)
  have hxD : x ∈ D := by
    have hrepr : x = (g : H) + (x - (g : H)) := by abel
    rw [hrepr]
    exact D.add_mem g.property (s.source_le hxg)
  have hx : x ∉ s.source := by
    intro hxS
    apply hg
    have hrepr : (g : H) = x - (x - (g : H)) := by abel
    rw [hrepr]
    exact s.source.sub_mem hxS hxg
  have hpx : p • x ∈ s.source := by
    have hrepr : p • x = p • (g : H) + p • (x - (g : H)) := by
      rw [smul_sub]
      abel
    rw [hrepr]
    exact s.source.add_mem hpg (s.source.nsmul_mem hxg p)
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hx
    simpa [hx0]
  obtain ⟨ρ, hxρ, hxSucc⟩ :=
    exists_ulmHeight_eq_of_ne_zero (p := p) hH hx0
  have hpxMax : ∀ y : H, y - x ∈ s.source → IsProper p s.source y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
    intro y hyx hyProper
    apply hpxMax' y
    · have : y - (g : H) = (y - x) + (x - (g : H)) := by abel
      rw [this]
      exact s.source.add_mem hyx hxg
    · exact hyProper
  have finish : ∀ (t : Stage p hG hH C D N),
      Stage.Extends p s t → x ∈ t.source →
      ∃ u : Stage p hG hH C D N,
        Stage.Extends p s u ∧ (g : H) ∈ u.source := by
    intro t hst hxt
    refine ⟨t, hst, ?_⟩
    have hxg' : x - (g : H) ∈ t.source := hst.source_le hxg
    have hrepr : (g : H) = x - (x - (g : H)) := by abel
    rw [hrepr]
    exact t.source.sub_mem hxt hxg'
  by_cases hρbase : ρ < ω * α
  · obtain ⟨t, hst, hxt⟩ :=
      s.extend_low p hG hH C D N hxD hx hpx hxProper hpxMax
        hxρ hxSucc hρbase
    exact finish t hst hxt
  · obtain ⟨t, hst, hxt⟩ :=
      s.extend_high p hG hH C hlong D N hxD hx hpx hxProper
        hxρ hxSucc (le_of_not_gt hρbase)
    exact finish t hst hxt

/-- Absorb one prescribed element using exactly `k` countdown steps, starting
from a stage containing its `p^k` multiple. -/
theorem Stage.extend_pow_to_mem
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (D : AddSubgroup H) (N k : ℕ)
    (s : Stage p hG hH C D (N + k)) (g : D)
    (hpow : p ^ k • (g : H) ∈ s.source) :
    ∃ t : Stage p hG hH C D N,
      Stage.Extends p s t ∧ (g : H) ∈ t.source := by
  induction k with
  | zero =>
      have hg : (g : H) ∈ s.source := by simpa using hpow
      exact ⟨s, Stage.Extends.refl p s, hg⟩
  | succ k ih =>
      let y : D := ⟨p ^ k • (g : H), D.nsmul_mem g.property (p ^ k)⟩
      have hpy : p • (y : H) ∈ s.source := by
        simpa [y, pow_succ, mul_smul, Nat.mul_comm, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using hpow
      let s' : Stage p hG hH C D ((N + k) + 1) := by
        simpa only [Nat.add_succ] using s
      obtain ⟨t₁, hst₁, hy₁⟩ :=
        s'.extend_one p hG hH C hlong D (N + k) y
          (by simpa [s'] using hpy)
      obtain ⟨t₂, ht₁t₂, hg₂⟩ := ih t₁ hy₁
      have hst₁' : Stage.Extends p s t₁ := by
        simpa [s', Nat.add_assoc] using hst₁
      exact ⟨t₂, Stage.Extends.trans p hst₁' ht₁t₂, hg₂⟩

/-- Iterate uniform-exponent absorption over a finite list. -/
theorem Stage.extend_list
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hlong : ω * α + ω ≤ (ulmLength p (G := G) hG : Ordinal.{0}))
    (D : AddSubgroup H) (N k : ℕ)
    (hkill : ∀ g : D, p ^ k • (g : H) = 0)
    (l : List D) (s : Stage p hG hH C D (N + k * l.length)) :
    ∃ t : Stage p hG hH C D N,
      Stage.Extends p s t ∧ ∀ g ∈ l, (g : H) ∈ t.source := by
  induction l with
  | nil =>
      exact ⟨s, Stage.Extends.refl p s, by simp⟩
  | cons g l ih =>
      have hsFuel : N + k * (g :: l).length =
          (N + k * l.length) + k := by simp [Nat.mul_add, Nat.add_assoc]
      let s' : Stage p hG hH C D ((N + k * l.length) + k) := hsFuel ▸ s
      have hss' : Stage.Extends p s s' := Stage.Extends.cast p s hsFuel
      obtain ⟨t₁, hst₁, hg₁⟩ :=
        s'.extend_pow_to_mem p hG hH C hlong D
          (N + k * l.length) k g (by simp [hkill g])
      obtain ⟨t₂, ht₁t₂, hlt₂⟩ := ih t₁
      have hst₁' : Stage.Extends p s t₁ :=
        Stage.Extends.trans p hss' hst₁
      refine ⟨t₂, Stage.Extends.trans p hst₁' ht₁t₂, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ht₁t₂.source_le hg₁
      · exact hlt₂ z hz

/-- Complete the long odd countdown on an arbitrary finite challenged
subgroup.  The result has exactly the two map properties needed by the odd
predecessor: two-sided preservation below the base and a one-sided floor at
the base itself. -/
theorem finite_countdown_within
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
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
          (C.iso.equiv x : G) := by
  classical
  letI : Fintype D := hD.fintype
  have hDprimary : IsPrimaryPGroup p D := by
    intro x
    obtain ⟨k, hk⟩ := hH.primary (x : H)
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨k, hkill⟩ := finite_primary_bounded_exponent p hDprimary
  let l : List D := Finset.univ.toList
  let fuel : ℕ := k * l.length
  have hfuelCap : ω * α + fuel < ω * α + ω := by
    rw [add_lt_add_iff_left]
    exact Ordinal.natCast_lt_omega0 fuel
  let s₀ : Stage p hG hH C D (0 + k * l.length) :=
    Stage.initial p hG hH C D hmarkD (0 + k * l.length) (by
      simpa [fuel] using hfuelCap)
  obtain ⟨t, hs₀t, hall⟩ :=
    s₀.extend_list p hG hH C hlong D 0 k
      (fun g ↦ congrArg Subtype.val (hkill g)) l
  have htall : ∀ x : D, (x : H) ∈ t.source := by
    intro x
    exact hall x (by simp [l])
  let ι : D →+ t.source :=
    { toFun := fun x ↦ ⟨(x : H), htall x⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl }
  let f : D →+ (⊤ : AddSubgroup G) := t.map.comp ι
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : t.source ↦ (z : H)) hxy)
  have hpres : IsHeightPresBelowOn p f (ω * α) := by
    intro β hβ x
    exact t.presBelow β hβ (ι x)
  have hfloor : IsHeightFloorAt p f (ω * α) := by
    intro x hx
    exact t.floorThrough (ω * α) (by simp) (ι x) hx
  have hmark : ∀ x : tupleSubgroup b,
      (f ⟨(x : H), hmarkD x.property⟩ : G) =
        (C.iso.equiv x : G) := by
    intro x
    change (t.map (ι ⟨(x : H), hmarkD x.property⟩) : G) =
      (C.iso.equiv x : G)
    have hιx : ι ⟨(x : H), hmarkD x.property⟩ =
        ⟨(x : H), hs₀t.source_le x.property⟩ := Subtype.ext rfl
    rw [hιx, hs₀t.map_eq]
    exact s₀.mark x
  exact ⟨f, t.map_injective.comp hι, hpres, hfloor, hmark⟩

end AlgebraicBFConditions.OddLongCountdown
