import Lib.BackForth.OddFiniteExtension

/-!
# Ambient-height finite challenge regression tests

These compile-time checks pin the local sufficiency theorem with arbitrary
ambient source and target groups, plus the exact active-window bridge from the
corrected odd algebraic condition.
-/

noncomputable section

open Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- A finite challenge uses ambient heights and needs no ambient finiteness. -/
example (hB : IsReducedPGroup p B)
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
      ∀ x : F, (f ⟨(x : B), hFD x.property⟩ : A) = (φ x : A) :=
  LocalFiniteEmbedding.exists_finiteChallenge_embedding_of_kernelRoomBudget
    p hB F D hFD hD E φ hφ hfloor hbudget

namespace AlgebraicBFConditions

variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

/-- Corrected odd clause (d) is literally `K_β` inside its window. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (β : Ordinal.{0}) (hβ : Survival.InWindow α β) :
    Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β
      (heightFloorAt_of_heights p C.iso C.heights (Order.succ β)
        (Order.succ_le_of_lt hβ.2))
      (heightFloorAt_of_heights p C.iso C.heights β
        (le_of_lt hβ.2)) :=
  AlgBFOddCondData.kernelRoomBudgetAt p hG hH C β hβ

/-- A finite tuple really does generate a finite challenge subgroup in an
arbitrary ambient primary group. -/
example (hH : IsReducedPGroup p H) {m : ℕ} (d : Fin m → H) :
    Set.Finite (tupleSubgroup d : Set H) :=
  tupleSubgroup_finite p hH.primary d

/-- In the bounded-target branch the odd length clause kills the source tail
at the cap and upgrades the capped marked floor to a global floor. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω) :
    ulmSubgroup p (ω * α + ω) (G := H) = ⊥ ∧
      IsHeightFloorOn p C.iso.equiv.toAddMonoidHom := by
  constructor
  · exact AlgBFOddCondData.sourceTail_eq_bot_of_targetLength_lt_cap
      p hG hH C hGcap
  · exact AlgBFOddCondData.heightFloorOn_of_targetLength_lt_cap
      p hG hH C hGcap

/-- The bounded-tail integration consumes only the below-base budgets and
returns a response to an arbitrary finite tuple challenge. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    (hbelow : ∀ (β : Ordinal.{0}) (_hβ : β < ω * α)
      (hsucc : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom (Order.succ β))
      (hβfloor : IsHeightFloorAt p C.iso.equiv.toAddMonoidHom β),
      Survival.KernelRoomBudgetAt p C.iso.equiv.toAddMonoidHom β hsucc hβfloor)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom :=
  exists_finiteTuple_heightFloorResponse_of_oddData_of_boundedTarget
    p hG hH C hGcap hbelow d

/-- The completed bounded Case 1(c) construction needs no below-base
room--kernel hypothesis: the odd clauses alone answer every finite tuple
challenge with filtration equivalence below the predecessor cutoff. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom ∧
      IsHeightPresBelowOn p C'.equiv.toAddMonoidHom (ω * α) :=
  exists_finiteTuple_cutoffResponse_of_oddData_of_boundedTarget_from_odd
    p hG hH C hGcap d

/-- The map-level cutoff conclusion converts to the literal elementwise
height disjunction in ACM's even/limit predecessor clauses. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α : Ordinal.{0}} {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH α a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω * α + ω)
    {m : ℕ} (d : Fin m → H) :
    ∃ (c : Fin m → G)
      (C' : TupleIsoMap (Fin.append a c) (Fin.append b d)),
      IsHeightFloorOn p C'.equiv.toAddMonoidHom ∧
      ∀ x : tupleSubgroup (Fin.append b d),
        (ulmHeight p (x : H) = ulmHeight p (C'.equiv x : G) ∧
          ulmHeight p (x : H) < ω * α) ∨
        (ω * α ≤ ulmHeight p (x : H) ∧
          ω * α ≤ ulmHeight p (C'.equiv x : G)) :=
  exists_finiteTuple_predecessorHeightResponse_of_oddData_of_boundedTarget
    p hG hH C hGcap d

/-- At `alpha = 0`, the bounded response reaches Lean's actual successor
relation because its predecessor obligation is just the base tuple
isomorphism. -/
example (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFOddCondData p hG hH 0 a b)
    (hGcap : (ulmLength p (G := G) hG : Ordinal.{0}) < ω) :
    BFRel p 1 n a b :=
  bf_one_of_oddData_of_boundedTarget p hG hH C hGcap

end AlgebraicBFConditions
