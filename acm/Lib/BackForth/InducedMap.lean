import Lib.BackForth.JumpSpace

/-!
# The induced map on jump spaces

This file formalizes Definition 1.9 of the paper *An Algebraic Characterization of
the Back and Forth Relations on Reduced Abelian `p`-Groups*: given subgroups
`F ≤ B` and `E ≤ A` and a homomorphism `φ : F →+ E`, the induced map

  `jumpMap : S_{B,F}(β) →+ S_{A,E}(β)`,   `[c] ↦ [φ c]`.

The paper leaves well-definedness as an open TODO at `def:inducedmap`.  It is
discharged here, and the hypotheses it actually needs are exactly two:
`φ` is additive, and `φ` satisfies the **height floor** `h(φ a) ≥ h(a)`.  No
height *preservation* (the two-sided `IsHeightPresOn`) is required.

## Why this is a map and not an equivalence

The construction deliberately produces an `AddMonoidHom`, never an `AddEquiv`.
The numerator condition and the denominator condition are asymmetric: the floor
pushes the numerator forward, but the *target* denominator `p(E ∩ G^A_β)` can be
strictly larger than the image of the source denominator, so classes can die.
`jumpMap_injective_iff` isolates exactly that, and `Test/InducedMapRegression`
exhibits a pair where the kernel is nonzero.  This matters: clause (d) of the odd
characterization asks for injectivity of this map at exhausted levels, and any
construction that made it an equivalence would render that clause vacuous.

## Main definitions

- `IsHeightFloorOn p φ` : `h(φ a) ≥ h(a)`, the one-sided weakening of `IsHeightPresOn`
- `jumpNumMap`          : the map on numerators `pF ∩ G^B_{β+1} →+ pE ∩ G^A_{β+1}`
- `jumpMap`             : the induced map on jump spaces

## Main results

- `jumpMap_mk`             : the induced map sends `[c]` to `[φ c]` (well-definedness)
- `jumpMap_injective_iff`  : injectivity is exactly a denominator-reflection condition
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]

/-! ### The height floor -/

/-- `φ` satisfies the **height floor** if `h(φ a) ≥ h(a)` for every `a` in its
domain, stated by filtration membership as elsewhere in this development.

This is the hypothesis (H2)/(I2) of the extension construction.  It is strictly
weaker than `IsHeightPresOn`, which is the two-sided `↔`. -/
def IsHeightFloorAt {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    (γ : Ordinal.{0}) : Prop :=
  ∀ a : F, (a : G) ∈ ulmSubgroup p γ (G := G) → (φ a : H) ∈ ulmSubgroup p γ (G := H)

/-- The height floor at every level. -/
def IsHeightFloorOn {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E) : Prop :=
  ∀ γ : Ordinal.{0}, IsHeightFloorAt p φ γ

/-- `φ` preserves the filtration strictly below `θ`.  This is the map-level
form of the cutoff height condition in the ACM even/limit clauses: elements
below `θ` keep their exact height, while an element on either side of the
cutoff stays above every level `< θ` on both sides. -/
def IsHeightPresBelowOn {F : AddSubgroup G} {E : AddSubgroup H}
    (φ : F →+ E) (θ : Ordinal.{0}) : Prop :=
  ∀ γ : Ordinal.{0}, γ < θ → ∀ a : F,
    ((a : G) ∈ ulmSubgroup p γ (G := G) ↔
      (φ a : H) ∈ ulmSubgroup p γ (G := H))

omit hp in
/-- Height preservation implies the height floor. -/
lemma IsHeightPresOn.isHeightFloorOn {F : AddSubgroup G} {E : AddSubgroup H}
    {φ : F →+ E} (hφ : IsHeightPresOn p φ) : IsHeightFloorOn p φ :=
  fun γ a h => (hφ a γ).mp h

omit hp in
/-- Global height preservation restricts to every cutoff. -/
lemma IsHeightPresOn.isHeightPresBelowOn
    {F : AddSubgroup G} {E : AddSubgroup H} {φ : F →+ E}
    (hφ : IsHeightPresOn p φ) (θ : Ordinal.{0}) :
    IsHeightPresBelowOn p φ θ :=
  fun γ _ a ↦ hφ a γ

/-! ### The numerator map -/

omit hp in
/-- The jump numerator sits inside its subgroup: `pF ∩ G_{β+1} ≤ F`. -/
lemma jumpNum_le_self (F : AddSubgroup G) (β : Ordinal.{0}) :
    jumpNum p F β ≤ F :=
  fun _ hx => pImage_le p F hx.1

/-- The induced map on jump-space **numerators**.

Both components of membership survive: `c ∈ pF` gives `φ c ∈ pE` because `φ` is
additive, and `c ∈ G^B_{β+1}` gives `φ c ∈ G^A_{β+1}` by the height floor. -/
noncomputable def jumpNumMap {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hφ : IsHeightFloorAt p φ (Order.succ β)) :
    jumpNum p F β →+ jumpNum p E β where
  toFun c :=
    ⟨(φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H), by
      obtain ⟨⟨y, hyF, hyc⟩, hcU⟩ := c.2
      refine ⟨⟨(φ ⟨y, hyF⟩ : H), (φ ⟨y, hyF⟩).2, ?_⟩, ?_⟩
      · have hy : (⟨(c : G), jumpNum_le_self p F β c.2⟩ : F) = p • (⟨y, hyF⟩ : F) := by
          apply Subtype.ext
          simpa using hyc.symm
        rw [hy, map_nsmul]
        simp
      · exact hφ _ hcU⟩
  map_zero' := by
    apply Subtype.ext
    have h0 : (⟨((0 : jumpNum p F β) : G), jumpNum_le_self p F β (0 : jumpNum p F β).2⟩ : F)
        = 0 := Subtype.ext rfl
    show ((φ ⟨((0 : jumpNum p F β) : G), _⟩ : E) : H) = ((0 : jumpNum p E β) : H)
    rw [h0, map_zero]
    rfl
  map_add' x y := by
    apply Subtype.ext
    have hxy : (⟨((x + y : jumpNum p F β) : G), jumpNum_le_self p F β (x + y).2⟩ : F)
        = ⟨(x : G), jumpNum_le_self p F β x.2⟩ + ⟨(y : G), jumpNum_le_self p F β y.2⟩ :=
      Subtype.ext rfl
    show ((φ ⟨((x + y : jumpNum p F β) : G), _⟩ : E) : H) = _
    rw [hxy, map_add]
    rfl

@[simp] lemma jumpNumMap_coe {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hφ : IsHeightFloorAt p φ (Order.succ β)) (c : jumpNum p F β) :
    ((jumpNumMap p φ hφ c : jumpNum p E β) : H)
      = (φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H) := rfl

/-! ### The induced map on jump spaces -/

/-- The denominator condition: `φ` carries `p(F ∩ G^B_β)` into `p(E ∩ G^A_β)`.

This is the second half of well-definedness, and it is where the height floor is
used a second time: a source denominator element is `p y` with `y ∈ F` of height
at least `β`, and the floor puts `φ y` at height at least `β` as well. -/
lemma jumpDen_maps {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    jumpDenIn p F β ≤ (jumpDenIn p E β).comap (jumpNumMap p φ hsucc) := by
  rintro x hx
  obtain ⟨y, ⟨hyF, hyU⟩, hyx⟩ := hx
  show ((jumpNumMap p φ hsucc x : jumpNum p E β) : H) ∈ jumpDen p E β
  rw [jumpNumMap_coe]
  refine ⟨(φ ⟨y, hyF⟩ : H), ⟨(φ ⟨y, hyF⟩).2, hβ _ hyU⟩, ?_⟩
  have hy : (⟨(x : G), jumpNum_le_self p F β x.2⟩ : F) = p • (⟨y, hyF⟩ : F) := by
    apply Subtype.ext
    simpa using hyx.symm
  rw [hy, map_nsmul]
  simp

/-- **Definition 1.9 (induced map).** For `φ : F →+ E` satisfying the height
floor, the induced map on jump spaces `S_{B,F}(β) →+ S_{A,E}(β)`, `[c] ↦ [φ c]`.

This is an `AddMonoidHom`, not an `AddEquiv`; see the module docstring. -/
noncomputable def jumpMap {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    jumpSpace p F β →+ jumpSpace p E β :=
  QuotientAddGroup.map (jumpDenIn p F β) (jumpDenIn p E β)
    (jumpNumMap p φ hsucc) (jumpDen_maps p φ hsucc hβ)

/-- The induced jump map as a `ZMod p`-linear map.

The additive map is automatically linear because both jump spaces are killed by
`p`.  Keeping this wrapper next to `jumpMap` makes its kernel available to the
quantitative room--kernel invariant. -/
noncomputable def jumpLinearMap {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    jumpSpace p F β →ₗ[ZMod p] jumpSpace p E β :=
  (jumpMap p φ hsucc hβ).toZModLinearMap p

/-- The induced jump map is natural under restriction to an earlier height. -/
theorem jumpRestriction_jumpLinearMap
    {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    (hfloor : IsHeightFloorOn p φ) {β γ : Ordinal.{0}} (hβγ : β ≤ γ)
    (q : jumpSpace p F γ) :
    jumpRestriction p E hβγ
        (jumpLinearMap p φ (hfloor (Order.succ γ)) (hfloor γ) q) =
      jumpLinearMap p φ (hfloor (Order.succ β)) (hfloor β)
        (jumpRestriction p F hβγ q) := by
  refine Quotient.inductionOn q ?_
  intro c
  rfl

/-- The `ZMod p`-dimension of the kernel of the induced jump map. -/
noncomputable def jumpKernelInvariant {F : AddSubgroup G} {E : AddSubgroup H}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) : Cardinal :=
  Module.rank (ZMod p) (LinearMap.ker (jumpLinearMap p φ hsucc hβ))

/-- A finite marked source has a finite-dimensional induced jump kernel. -/
theorem jumpKernelInvariant_lt_aleph0_of_finite_source
    {F : AddSubgroup G} {E : AddSubgroup H}
    (hF : Set.Finite (F : Set G)) (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    jumpKernelInvariant p φ hsucc hβ < Cardinal.aleph0 := by
  letI : Finite F := hF.to_subtype
  let toF : jumpNum p F β → F := fun x ↦
    ⟨(x : G), pImage_le p F x.property.1⟩
  letI : Finite (jumpNum p F β) :=
    Finite.of_injective toF (by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : F ↦ (z : G)) hxy))
  letI : Finite (jumpSpace p F β) := inferInstance
  letI : Finite (LinearMap.ker (jumpLinearMap p φ hsucc hβ)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Module.rank_lt_aleph0 (ZMod p)
    (LinearMap.ker (jumpLinearMap p φ hsucc hβ))

/-- `jumpKernelInvariant` does not depend on which proofs of the height floor
were supplied to the quotient construction. -/
theorem jumpKernelInvariant_proof_irrel {F : AddSubgroup G} {E : AddSubgroup H}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc hsucc' : IsHeightFloorAt p φ (Order.succ β))
    (hβ hβ' : IsHeightFloorAt p φ β) :
    jumpKernelInvariant p φ hsucc hβ =
      jumpKernelInvariant p φ hsucc' hβ' := by
  congr

/-- The jump-kernel dimension is zero exactly when the induced jump map is
injective. -/
theorem jumpKernelInvariant_eq_zero_iff {F : AddSubgroup G} {E : AddSubgroup H}
    (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    jumpKernelInvariant p φ hsucc hβ = 0 ↔
      Function.Injective (jumpMap p φ hsucc hβ) := by
  rw [jumpKernelInvariant, rank_zero_iff, Submodule.subsingleton_iff_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

/-- **Well-definedness**, in the usable form: the induced map really does send the
class of `c` to the class of `φ c`. -/
@[simp] lemma jumpMap_mk {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) (c : jumpNum p F β) :
    jumpMap p φ hsucc hβ (QuotientAddGroup.mk c)
      = QuotientAddGroup.mk (jumpNumMap p φ hsucc c) := rfl

/-! ### Injectivity is a real condition -/

/-- Injectivity of the induced map is exactly the statement that `φ` **reflects**
the jump denominator: a numerator class can only die if it was already zero.

Nothing in the construction forces this.  The target denominator
`p(E ∩ G^A_β)` may strictly contain the image of the source denominator, and then
the map kills a class.  This is the content clause (d) of the odd characterization
asks for at exhausted levels. -/
theorem jumpMap_injective_iff {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β) :
    Function.Injective (jumpMap p φ hsucc hβ) ↔
      ∀ c : jumpNum p F β,
        (φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H) ∈ jumpDen p E β →
          (c : G) ∈ jumpDen p F β := by
  have hmem : ∀ (c : jumpNum p F β),
      (jumpNumMap p φ hsucc c ∈ jumpDenIn p E β) ↔
        (φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H) ∈ jumpDen p E β := by
    intro c; exact Iff.rfl
  have hsrc : ∀ (c : jumpNum p F β),
      (c ∈ jumpDenIn p F β) ↔ (c : G) ∈ jumpDen p F β := by
    intro c; exact Iff.rfl
  constructor
  · intro hinj c hc
    have h0 : jumpMap p φ hsucc hβ (QuotientAddGroup.mk c) = 0 := by
      rw [jumpMap_mk]
      exact (QuotientAddGroup.eq_zero_iff _).mpr ((hmem c).mpr hc)
    have hz : (QuotientAddGroup.mk c : jumpSpace p F β) = 0 := by
      have := hinj (by simpa using h0 : jumpMap p φ hsucc hβ (QuotientAddGroup.mk c)
        = jumpMap p φ hsucc hβ 0)
      simpa using this
    exact (hsrc c).mp ((QuotientAddGroup.eq_zero_iff _).mp hz)
  · intro hrefl
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      rw [jumpMap_mk] at hx
      have hc := (hmem c).mp ((QuotientAddGroup.eq_zero_iff _).mp hx)
      exact (QuotientAddGroup.eq_zero_iff _).mpr ((hsrc c).mpr (hrefl c hc))

/-- A subgroup equivalence which reflects the filtration at `β` induces an
injective jump map at `β`.

The proof is local.  A target denominator witness is pulled back through the
equivalence; filtration reflection puts that root in the source denominator,
and injectivity identifies its `p`-multiple with the original numerator. -/
theorem jumpMap_injective_of_equiv_of_reflectsAt
    {F : AddSubgroup G} {E : AddSubgroup H} (φ : F ≃+ E)
    {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ.toAddMonoidHom (Order.succ β))
    (hβ : IsHeightFloorAt p φ.toAddMonoidHom β)
    (hreflect : ∀ x : F,
      (φ x : H) ∈ ulmSubgroup p β (G := H) →
        (x : G) ∈ ulmSubgroup p β (G := G)) :
    Function.Injective (jumpMap p φ.toAddMonoidHom hsucc hβ) := by
  apply (jumpMap_injective_iff p φ.toAddMonoidHom hsucc hβ).2
  intro c hc
  change (φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H) ∈
    pImage p (E ⊓ ulmSubgroup p β) at hc
  rcases hc with ⟨y, ⟨hyE, hyβ⟩, hpy⟩
  let yE : E := ⟨y, hyE⟩
  let xF : F := φ.symm yE
  let cF : F := ⟨(c : G), jumpNum_le_self p F β c.2⟩
  have hxβ : (xF : G) ∈ ulmSubgroup p β := by
    apply hreflect xF
    simpa [xF, yE] using hyβ
  refine ⟨(xF : G), ⟨xF.property, hxβ⟩, ?_⟩
  have heq : p • xF = cF := by
    apply φ.injective
    rw [map_nsmul]
    apply Subtype.ext
    simpa [xF, yE, cF] using hpy
  exact congrArg (fun z : F ↦ (z : G)) heq

/-- Below a cutoff, filtration preservation by a subgroup equivalence makes
the jump-kernel invariant vanish.  Requiring `succ β < θ` exposes exactly the
two filtration levels consumed by the quotient construction. -/
theorem jumpKernelInvariant_eq_zero_of_equiv_of_heightPresBelow
    {F : AddSubgroup G} {E : AddSubgroup H} (φ : F ≃+ E)
    {β θ : Ordinal.{0}} (hβθ : Order.succ β < θ)
    (hpres : IsHeightPresBelowOn p φ.toAddMonoidHom θ) :
    jumpKernelInvariant p φ.toAddMonoidHom
        (fun x hx ↦ (hpres (Order.succ β) hβθ x).mp hx)
        (fun x hx ↦ (hpres β ((Order.lt_succ β).trans hβθ) x).mp hx) = 0 := by
  apply (jumpKernelInvariant_eq_zero_iff p φ.toAddMonoidHom _ _).2
  apply jumpMap_injective_of_equiv_of_reflectsAt p φ
  intro x hx
  exact (hpres β ((Order.lt_succ β).trans hβθ) x).mpr hx

/-! ### The induced map is genuinely not an equivalence -/

/-- **The construction does not produce an equivalence.**  If the target jump
space collapses while the source does not, the induced map cannot be injective —
whatever `φ` is, and however well it respects heights.

This is the configuration the odd characterization cares about: at a level where
the target is exhausted, injectivity of `jumpMap` is an extra demand on `φ`, not a
consequence of the construction.  Any formalization that built the induced map as
an `AddEquiv` would make this theorem unprovable. -/
theorem jumpMap_not_injective_of_target_subsingleton
    {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β)
    (htarget : Subsingleton (jumpSpace p E β))
    (hsource : ¬ Subsingleton (jumpSpace p F β)) :
    ¬ Function.Injective (jumpMap p φ hsucc hβ) := by
  intro hinj
  exact hsource ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

/-- The zero map into the trivial subgroup always satisfies the height floor:
`0` lies in every `G_γ`.  Together with
`jumpMap_not_injective_of_target_subsingleton` this shows the height floor alone
never implies injectivity. -/
lemma isHeightFloorOn_zero {F : AddSubgroup G} {E : AddSubgroup H} :
    IsHeightFloorOn p (0 : F →+ E) :=
  fun _ _ _ => by simpa using (ulmSubgroup p _ (G := H)).zero_mem

/-- A map out of a trivial jump space is injective for free.

This is the second of the two mechanisms by which `(I4)` survives an extension
step.  The first is that the jump space does not change at all
(`Survival.jumpSpace_unchanged_of_proper`); this one is that there was nothing
there to preserve.  Together they cover every safe move observed in the engine
corpora. -/
theorem jumpMap_injective_of_source_subsingleton
    {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E)
    {β : Ordinal.{0}} (hsucc : IsHeightFloorAt p φ (Order.succ β))
    (hβ : IsHeightFloorAt p φ β)
    (hsource : Subsingleton (jumpSpace p F β)) :
    Function.Injective (jumpMap p φ hsucc hβ) :=
  fun x y _ => Subsingleton.elim x y

/-!
### A concrete non-injective instance

The abstract theorem above is instantiated by the following data, computed by hand
and independently by `knowledge/engine/delta_probe.py`; formalizing the two
`Subsingleton` facts for it is the remaining step (they are finite `pPow`
computations, reachable through `mem_ulmSubgroup_nat_iff`).

Take `p = 2`, `β = 1`, and

* `B = ZMod 2 × ZMod 8`, `F = ⟨(1, 2)⟩ = {(0,0), (1,2), (0,4), (1,6)} ≅ ZMod 4`;
* `A = ZMod 8`, `E = ⟨2⟩ = {0, 2, 4, 6} ≅ ZMod 4`;
* `φ : F ≃+ E` determined by `(1,2) ↦ 2`.

Then `φ` is injective and satisfies the height floor — `h(1,2) = 0 ≤ 1 = h(2)`,
`h(0,4) = 2 = h(4)`, `h(1,6) = 0 ≤ 1 = h(6)` — while

* `pF ∩ G^B_2 = {(0,0), (0,4)}` and `p(F ∩ G^B_1) = {(0,0)}`, so `S_{B,F}(1) ≅ ZMod 2`;
* `pE ∩ G^A_2 = {0, 4}` and `p(E ∩ G^A_1) = {0, 4}`, so `S_{A,E}(1) = 0`.

The height jump `h(1,2) = 0` but `h(2 · (1,2)) = h(0,4) = 2` is what makes the
source nonzero, and the target's denominator swallowing its numerator is what
kills the class.  This is the same mechanism as the Example of D-5.
-/
