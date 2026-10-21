import Lib.BackForth.FiniteRado

/-!
# Height-filtered affine Rado matching

This file proves the linear-algebra assembly step in D-22.  A compatible
source basis has a reach `r i`; the legal target values of its `i`th vector
form the affine set

`Φ (b i) + Z (r i)`.

For every filtration level `β`, quotient the feasible base map `Φ` by the
target direction `Z β` and restrict it to the source reach space `X β`.  If
the kernel of this residue map fits inside `Z β`, then every subfamily of the
affine access sets satisfies Rado's rank inequality.  The finite linear Rado
theorem therefore produces an independent transversal, equivalently an
injective linear realization on the source basis.

The proof is deliberately abstract.  The group-specific remaining bridge is
to instantiate `X`, `Z`, and `Φ` with the reachable source filtration, target
room filtration, and height-equation solution.
-/

noncomputable section

open Function Module Set Submodule

universe u v w x y

namespace HeightRado

variable {K : Type u} {Q : Type v} {V : Type w}
variable {ι : Type x} {Λ : Type y}
variable [DivisionRing K]
variable [AddCommGroup Q] [Module K Q]
variable [AddCommGroup V] [Module K V]

/-- The legal values for one basis vector: an affine translate of the target
direction available at that vector's reach. -/
def affineAccess (Φ : Q →ₗ[K] V) (Z : Λ → Submodule K V)
    (b : Basis ι K Q) (r : ι → Λ) (i : ι) : Set V :=
  {z | z - Φ (b i) ∈ Z (r i)}

/-- The forced residue map at level `β`: restrict the feasible base map to
the source reach space and then quotient out the target room at `β`. -/
def residueMap (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (β : Λ) :
    X β →ₗ[K] V ⧸ Z β :=
  (Z β).mkQ.comp (Φ.domRestrict (X β))

/-- Inclusion of the kernel of a residue map restricted to `Y` into the
kernel of the same residue map on a larger source space `X`. -/
noncomputable def residueKernelInclusion (Φ : Q →ₗ[K] V)
    (Z : Submodule K V) {Y X : Submodule K Q} (hYX : Y ≤ X) :
    LinearMap.ker (Z.mkQ.comp (Φ.domRestrict Y)) →ₗ[K]
      LinearMap.ker (Z.mkQ.comp (Φ.domRestrict X)) where
  toFun x :=
    ⟨⟨(x : Y), hYX x.1.2⟩, by
      change Z.mkQ (Φ ((x : Y) : Q)) = 0
      exact x.property⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The kernel inclusion above is injective. -/
theorem residueKernelInclusion_injective (Φ : Q →ₗ[K] V)
    (Z : Submodule K V) {Y X : Submodule K Q} (hYX : Y ≤ X) :
    Function.Injective (residueKernelInclusion Φ Z hYX) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : LinearMap.ker (Z.mkQ.comp (Φ.domRestrict X)) =>
      (((z : X) : Q))) hab

/-- **Finite-dimensional kernel-versus-direction estimate.**  If `Y ≤ X`
and the residue kernel on `X` fits inside the target direction `Z`, then the
span of `Z` together with the image of `Y` has dimension at least `dim Y`.

This is equation (6.11) stripped to its linear-algebra core. -/
theorem finrank_le_finrank_sup_map_of_kernel_le
    [FiniteDimensional K Q] [FiniteDimensional K V]
    (Φ : Q →ₗ[K] V) (Z : Submodule K V) {Y X : Submodule K Q}
    (hYX : Y ≤ X)
    (hbudget : Module.finrank K
        (LinearMap.ker (Z.mkQ.comp (Φ.domRestrict X))) ≤
      Module.finrank K Z) :
    Module.finrank K Y ≤
      Module.finrank K (Z ⊔ Submodule.map Φ Y : Submodule K V) := by
  let fY : Y →ₗ[K] V ⧸ Z := Z.mkQ.comp (Φ.domRestrict Y)
  let fX : X →ₗ[K] V ⧸ Z := Z.mkQ.comp (Φ.domRestrict X)
  have hker : Module.finrank K (LinearMap.ker fY) ≤ Module.finrank K Z := by
    have hinj : Function.Injective (residueKernelInclusion Φ Z hYX) :=
      residueKernelInclusion_injective Φ Z hYX
    exact ((residueKernelInclusion Φ Z hYX).finrank_le_finrank_of_injective hinj).trans
      hbudget
  let S : Submodule K V := Z ⊔ Submodule.map Φ Y
  have hmap : S.map Z.mkQ = LinearMap.range fY := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨⟨y, hy⟩, ?_⟩
      change Z.mkQ (Φ y) = Z.mkQ (z + Φ y)
      rw [map_add, show Z.mkQ z = 0 by exact (Submodule.Quotient.mk_eq_zero Z).2 hz,
        zero_add]
    · rintro ⟨y, rfl⟩
      refine ⟨Φ (y : Q), ?_, rfl⟩
      exact (le_sup_right : Submodule.map Φ Y ≤ S) ⟨y, y.2, rfl⟩
  have hdimS := FiniteRado.finrank_map_mkQ_add_finrank_inf Z S
  have hZS : Z ≤ S := le_sup_left
  rw [hmap, inf_eq_right.mpr hZS] at hdimS
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker fY
  change Module.finrank K Y ≤ Module.finrank K S
  omega

/-- A basis is compatible with a reach filtration when the vectors of reach
at least `β` span exactly the source space `X β`. -/
def CompatibleWithReach [LinearOrder Λ] (b : Basis ι K Q) (r : ι → Λ)
    (X : Λ → Submodule K Q) : Prop :=
  ∀ β, X β = span K (b '' {i | β ≤ r i})

/-- **D-22, finite-range affine Height--Rado step.**  The theorem only uses
the kernel budget at heights
which actually occur as reaches of basis vectors.  This finite-range form is
the useful interface when the ambient target is not finite-dimensional: only
those finitely many target directions need to be localized. -/
theorem hasIndependentTransversal_affineAccess_of_reach_budget
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ i, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z (r i))) ≤
          Module.finrank K (Z (r i))) :
    FiniteRado.HasIndependentTransversal (K := K)
      (affineAccess Φ Z b r) := by
  apply (FiniteRado.finite_linear_rado (affineAccess Φ Z b r)).2
  intro t _
  by_cases ht : t = ∅
  · subst t
    simp [FiniteRado.familySpan]
  have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
  obtain ⟨i₀, hi₀, hmin⟩ := t.exists_min_image r htne
  let β : Λ := r i₀
  let Y : Submodule K Q := span K (b '' (t : Set ι))
  have hYX : Y ≤ X β := by
    rw [hcompat β]
    apply span_mono
    rintro q ⟨i, hi, rfl⟩
    exact ⟨i, hmin i hi, rfl⟩
  have hdimY : Module.finrank K Y = t.card := by
    let bt : {i // i ∈ t} → Q := fun i => b i
    have hli : LinearIndependent K bt :=
      b.linearIndependent.comp (fun i : {i // i ∈ t} => (i : ι))
        Subtype.val_injective
    have hrange : Set.range bt = b '' (t : Set ι) := by
      ext q
      simp [bt]
    change Module.finrank K (span K (b '' (t : Set ι))) = t.card
    rw [← hrange, finrank_span_eq_card hli]
    simp
  have hdim : Module.finrank K Y ≤
      Module.finrank K (Z β ⊔ Submodule.map Φ Y : Submodule K V) := by
    apply finrank_le_finrank_sup_map_of_kernel_le Φ (Z β) hYX
    exact hbudget i₀
  have hdir : Z β ≤
      FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t := by
    intro z hz
    have ha : Φ (b i₀) ∈
        FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t :=
      subset_span (FiniteRado.mem_familyUnion_of_mem hi₀ (by
        simp [affineAccess]))
    have haz : Φ (b i₀) + z ∈
        FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t :=
      subset_span (FiniteRado.mem_familyUnion_of_mem hi₀ (by
        change Φ (b i₀) + z - Φ (b i₀) ∈ Z (r i₀)
        simpa [β] using hz))
    simpa using
      (FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t).sub_mem haz ha
  have himage : Submodule.map Φ Y ≤
      FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t := by
    rw [map_le_iff_le_comap]
    change span K (b '' (t : Set ι)) ≤
      (FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t).comap Φ
    apply span_le.mpr
    rintro q ⟨i, hi, rfl⟩
    exact subset_span (FiniteRado.mem_familyUnion_of_mem hi (by
      simp [affineAccess]))
  calc
    t.card = Module.finrank K Y := hdimY.symm
    _ ≤ Module.finrank K
        (Z β ⊔ Submodule.map Φ Y : Submodule K V) := hdim
    _ ≤ Module.finrank K
        (FiniteRado.familySpan (K := K) (affineAccess Φ Z b r) t) :=
      Submodule.finrank_mono (sup_le hdir himage)

/-- All-height wrapper for the finite-range affine Height--Rado theorem. -/
theorem hasIndependentTransversal_affineAccess
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ β, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z β)) ≤ Module.finrank K (Z β)) :
    FiniteRado.HasIndependentTransversal (K := K)
      (affineAccess Φ Z b r) := by
  exact hasIndependentTransversal_affineAccess_of_reach_budget
    Φ X Z b r hcompat (fun i ↦ hbudget (r i))

/-- The same criterion packaged as an injective linear realization on the
source basis. -/
theorem hasInjectiveRealization_affineAccess
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    [SMulCommClass K K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ β, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z β)) ≤ Module.finrank K (Z β)) :
    FiniteRado.HasInjectiveRealization b (affineAccess Φ Z b r) := by
  apply (FiniteRado.hasInjectiveRealization_iff b (affineAccess Φ Z b r)).2
  exact (FiniteRado.finite_linear_rado (affineAccess Φ Z b r)).1
    (hasIndependentTransversal_affineAccess Φ X Z b r hcompat hbudget)

/-- Reach-only budget form of the injective-realization theorem. -/
theorem hasInjectiveRealization_affineAccess_of_reach_budget
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    [SMulCommClass K K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ i, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z (r i))) ≤
          Module.finrank K (Z (r i))) :
    FiniteRado.HasInjectiveRealization b (affineAccess Φ Z b r) := by
  apply (FiniteRado.hasInjectiveRealization_iff b (affineAccess Φ Z b r)).2
  exact (FiniteRado.finite_linear_rado (affineAccess Φ Z b r)).1
    (hasIndependentTransversal_affineAccess_of_reach_budget
      Φ X Z b r hcompat hbudget)

/-- **Target-local affine Height--Rado.**  A finite source basis only uses
finitely many target directions, even when the ambient target space is
infinite-dimensional.  At each realized reach choose a finite-dimensional
piece of the corresponding direction large enough for that reach's residue
kernel.  The span of those pieces together with `range Φ` is a common
finite-dimensional target in which the ordinary finite Rado theorem applies.

The hypothesis is cardinal-valued, so this theorem composes directly with
ambient room invariants.  No finite-dimensionality assumption is made on `V`.
-/
theorem hasInjectiveRealization_affineAccess_of_rank_reach_budget
    {Q₀ V₀ : Type v}
    [AddCommGroup Q₀] [Module K Q₀]
    [AddCommGroup V₀] [Module K V₀]
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q₀]
    [SMulCommClass K K V₀]
    (Φ : Q₀ →ₗ[K] V₀) (X : Λ → Submodule K Q₀)
    (Z : Λ → Submodule K V₀) (b : Basis ι K Q₀) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ i, Module.rank K
        (LinearMap.ker (residueMap Φ X Z (r i))) ≤
          Module.rank K (Z (r i))) :
    FiniteRado.HasInjectiveRealization b (affineAccess Φ Z b r) := by
  classical
  let n : ι → ℕ := fun i ↦
    Module.finrank K (LinearMap.ker (residueMap Φ X Z (r i)))
  have hn : ∀ i, (n i : Cardinal) ≤ Module.rank K (Z (r i)) := by
    intro i
    simpa only [n, Module.finrank_eq_rank] using hbudget i
  let f : ∀ i, (Fin (n i) → K) →ₗ[K] Z (r i) := fun i ↦
    Classical.choose (Module.le_rank_iff_exists_linearMap.mp (hn i))
  have hf : ∀ i, Function.Injective (f i) := fun i ↦
    Classical.choose_spec (Module.le_rank_iff_exists_linearMap.mp (hn i))
  let fV : ∀ i, (Fin (n i) → K) →ₗ[K] V₀ := fun i ↦
    (Z (r i)).subtype.comp (f i)
  have hfV : ∀ i, Function.Injective (fV i) := fun i ↦
    Subtype.val_injective.comp (hf i)
  let W : ι → Submodule K V₀ := fun i ↦ LinearMap.range (fV i)
  have hWZ : ∀ i, W i ≤ Z (r i) := by
    intro i _ hx
    obtain ⟨x, rfl⟩ := hx
    exact (f i x).property
  have hWfin : ∀ i, FiniteDimensional K (W i) := by
    intro i
    dsimp only [W]
    infer_instance
  have hWrank : ∀ i, Module.finrank K (W i) = n i := by
    intro i
    rw [show W i = LinearMap.range (fV i) by rfl,
      LinearMap.finrank_range_of_inj (hfV i)]
    simp
  let Z₀ : Λ → Submodule K V₀ := fun β ↦
    ⨆ i : ι, if r i = β then W i else ⊥
  have hZ₀Z : ∀ β, Z₀ β ≤ Z β := by
    intro β
    apply iSup_le
    intro i
    by_cases hi : r i = β
    · simp only [hi, if_pos]
      simpa [hi] using hWZ i
    · simp [hi]
  have hWZ₀ : ∀ i, W i ≤ Z₀ (r i) := by
    intro i
    have hi := le_iSup (fun j : ι ↦ if r j = r i then W j else ⊥) i
    simpa [Z₀] using hi
  let V' : Submodule K V₀ := LinearMap.range Φ ⊔ ⨆ i : ι, W i
  let Φ₀ : Q₀ →ₗ[K] V' :=
    Φ.codRestrict V' (fun q ↦
      (le_sup_left : LinearMap.range Φ ≤ V') ⟨q, rfl⟩)
  let Z₁ : Λ → Submodule K V' := fun β ↦ (Z₀ β).comap V'.subtype
  let W₁ : ι → Submodule K V' := fun i ↦ (W i).comap V'.subtype
  have hWV' : ∀ i, W i ≤ V' := by
    intro i x hx
    exact (le_sup_right : (⨆ j : ι, W j) ≤ V')
      ((le_iSup (fun j : ι ↦ W j) i) hx)
  have hW₁Z₁ : ∀ i, W₁ i ≤ Z₁ (r i) := by
    intro i x hx
    exact hWZ₀ i hx
  have hW₁rank : ∀ i, Module.finrank K (W₁ i) = n i := by
    intro i
    have hmap : (W₁ i).map V'.subtype = W i := by
      change ((W i).comap V'.subtype).map V'.subtype = W i
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hWV' i)]
    calc
      Module.finrank K (W₁ i) =
          Module.finrank K ((W₁ i).map V'.subtype) :=
        (Submodule.finrank_map_subtype_eq V' (W₁ i)).symm
      _ = Module.finrank K (W i) := by rw [hmap]
      _ = n i := hWrank i
  let kerInclusion : ∀ i,
      LinearMap.ker (residueMap Φ₀ X Z₁ (r i)) →ₗ[K]
        LinearMap.ker (residueMap Φ X Z (r i)) := fun i ↦
    { toFun := fun q ↦ by
        refine ⟨(q : X (r i)), ?_⟩
        have hq₁ : Φ₀ ((q : X (r i)) : Q₀) ∈ Z₁ (r i) := by
          apply (Submodule.Quotient.mk_eq_zero (Z₁ (r i))).mp
          exact q.property
        apply (Submodule.Quotient.mk_eq_zero (Z (r i))).mpr
        exact hZ₀Z (r i) hq₁
      map_add' := by intro x y; apply Subtype.ext; apply Subtype.ext; rfl
      map_smul' := by intro a x; apply Subtype.ext; apply Subtype.ext; rfl }
  have hkerInclusion : ∀ i, Function.Injective (kerInclusion i) := by
    intro i x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun q : LinearMap.ker (residueMap Φ X Z (r i)) ↦
        (((q : X (r i)) : Q₀))) hxy
  have hlocalBudget : ∀ i, Module.finrank K
      (LinearMap.ker (residueMap Φ₀ X Z₁ (r i))) ≤
        Module.finrank K (Z₁ (r i)) := by
    intro i
    calc
      Module.finrank K (LinearMap.ker (residueMap Φ₀ X Z₁ (r i))) ≤
          Module.finrank K (LinearMap.ker (residueMap Φ X Z (r i))) :=
        (kerInclusion i).finrank_le_finrank_of_injective (hkerInclusion i)
      _ = n i := rfl
      _ = Module.finrank K (W₁ i) := (hW₁rank i).symm
      _ ≤ Module.finrank K (Z₁ (r i)) :=
        Submodule.finrank_mono (hW₁Z₁ i)
  letI : FiniteDimensional K V' := by
    dsimp only [V']
    infer_instance
  obtain ⟨L₀, hL₀, hL₀access⟩ :=
    hasInjectiveRealization_affineAccess_of_reach_budget
      Φ₀ X Z₁ b r hcompat hlocalBudget
  let L : Q₀ →ₗ[K] V₀ := V'.subtype.comp L₀
  refine ⟨L, Subtype.val_injective.comp hL₀, ?_⟩
  intro i
  have hi := hL₀access i
  change (L₀ (b i) : V₀) - Φ (b i) ∈ Z (r i)
  apply hZ₀Z (r i)
  exact hi

/-- Cardinal-rank form of the affine Height--Rado theorem.  This is the form
which composes directly with the room--kernel invariant. -/
theorem hasInjectiveRealization_affineAccess_of_rank_budget
    {Q₀ V₀ : Type v}
    [AddCommGroup Q₀] [Module K Q₀]
    [AddCommGroup V₀] [Module K V₀]
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q₀] [FiniteDimensional K V₀]
    [SMulCommClass K K V₀]
    (Φ : Q₀ →ₗ[K] V₀) (X : Λ → Submodule K Q₀)
    (Z : Λ → Submodule K V₀) (b : Basis ι K Q₀) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X)
    (hbudget : ∀ β, Module.rank K
        (LinearMap.ker (residueMap Φ X Z β)) ≤ Module.rank K (Z β)) :
    FiniteRado.HasInjectiveRealization b (affineAccess Φ Z b r) := by
  apply hasInjectiveRealization_affineAccess Φ X Z b r hcompat
  intro β
  have h := hbudget β
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

/-- A linear realization of all basis access sets differs from the feasible
base map by an element of `Z β` on the whole compatible reach space `X β`.
This is the all-vector height rewrite: it upgrades basiswise access to every
linear combination in the filtration level. -/
theorem sub_mem_direction_of_compatible
    [LinearOrder Λ]
    (Φ L : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X) (hZ : Antitone Z)
    (haccess : ∀ i, L (b i) ∈ affineAccess Φ Z b r i)
    (β : Λ) (q : Q) (hq : q ∈ X β) :
    L q - Φ q ∈ Z β := by
  rw [hcompat β] at hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro q ⟨i, hi, rfl⟩
    exact hZ hi (haccess i)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add, add_sub_add_comm] using (Z β).add_mem hx hy
  · intro a x _ hx
    simpa only [map_smul, smul_sub] using (Z β).smul_mem a hx

/-- Basiswise membership in a nested target filtration extends to every vector
in the corresponding compatible source filtration.  This is the linear-span
bridge used to turn basiswise height-cell choices into a genuinely feasible
base map on all of `X β`. -/
theorem map_mem_of_compatible
    [LinearOrder Λ]
    (L : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Y : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X) (hY : Antitone Y)
    (hbasis : ∀ i, L (b i) ∈ Y (r i))
    (β : Λ) (q : Q) (hq : q ∈ X β) :
    L q ∈ Y β := by
  rw [hcompat β] at hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro q ⟨i, hi, rfl⟩
    exact hY hi (hbasis i)
  · rw [map_zero]
    exact (Y β).zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using (Y β).add_mem hx hy
  · intro a x _ hx
    simpa only [map_smul] using (Y β).smul_mem a hx

/-- Necessity in the abstract Height--Rado theorem.  An injective realization
embeds every forced-residue kernel into the corresponding target direction. -/
theorem kernel_budget_of_hasInjectiveRealization
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X) (hZ : Antitone Z)
    (hreal : FiniteRado.HasInjectiveRealization b
      (affineAccess Φ Z b r)) :
    ∀ β, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z β)) ≤ Module.finrank K (Z β) := by
  obtain ⟨L, hL, haccess⟩ := hreal
  intro β
  let toZ : LinearMap.ker (residueMap Φ X Z β) →ₗ[K] Z β := {
    toFun x :=
      ⟨L (((x : X β) : Q)), by
        have hdiff : L (((x : X β) : Q)) - Φ (((x : X β) : Q)) ∈ Z β :=
          sub_mem_direction_of_compatible Φ L X Z b r hcompat hZ haccess β
            (((x : X β) : Q)) x.1.2
        have hphi : Φ (((x : X β) : Q)) ∈ Z β := by
          apply (Submodule.Quotient.mk_eq_zero (Z β)).1
          change residueMap Φ X Z β x = 0
          exact x.property
        simpa only [sub_add_cancel] using (Z β).add_mem hdiff hphi⟩
    map_add' x y := by
      apply Subtype.ext
      simp
    map_smul' a x := by
      apply Subtype.ext
      simp
  }
  have htoZ : Function.Injective toZ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply hL
    exact congrArg Subtype.val hxy
  exact toZ.finrank_le_finrank_of_injective htoZ

/-- **Finite-dimensional affine Height--Rado criterion.**  For a compatible
reach basis and nested target directions, the room bound on every residue
kernel is necessary and sufficient for an injective realization of all legal
height access sets. -/
theorem hasInjectiveRealization_affineAccess_iff
    [LinearOrder Λ] [Fintype ι]
    [FiniteDimensional K Q] [FiniteDimensional K V]
    [SMulCommClass K K V]
    (Φ : Q →ₗ[K] V) (X : Λ → Submodule K Q)
    (Z : Λ → Submodule K V) (b : Basis ι K Q) (r : ι → Λ)
    (hcompat : CompatibleWithReach b r X) (hZ : Antitone Z) :
    FiniteRado.HasInjectiveRealization b (affineAccess Φ Z b r) ↔
      ∀ β, Module.finrank K
        (LinearMap.ker (residueMap Φ X Z β)) ≤ Module.finrank K (Z β) := by
  constructor
  · exact kernel_budget_of_hasInjectiveRealization Φ X Z b r hcompat hZ
  · exact hasInjectiveRealization_affineAccess Φ X Z b r hcompat

end HeightRado
