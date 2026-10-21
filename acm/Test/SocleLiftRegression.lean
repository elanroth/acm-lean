import Lib.BackForth.SocleLift

/-!
# Socle-lift regression tests

These compile-time checks pin the algebraic bridge from the room selector to
the actual `p`-socles.
-/

noncomputable section

open Module Ordinal

universe u v w

section Abstract

variable {K : Type u} {V : Type v} {W : Type w}
variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

example (U : Submodule K V) (T : Submodule K W)
    (g : U →ₗ[K] W) (hg : ∀ u, g u ∈ T)
    (L : (V ⧸ U) →ₗ[K] (W ⧸ T)) :
    ∃ Φ : V →ₗ[K] W,
      Φ.comp U.subtype = g ∧ T.mkQ.comp Φ = L.comp U.mkQ :=
  SocleLift.exists_compatible_quotient_lift U T g hg L

end Abstract

section Concrete

variable (p : ℕ) [Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
variable {F : AddSubgroup B} {E : AddSubgroup A}

/-- Injectivity of the marked map and room selector lifts to the full source
socle. -/
example (φ : F →+ E) (hφ : Function.Injective φ)
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = SocleLift.markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ :=
  SocleLift.exists_injective_socle_lift p φ hφ L hL

variable {ι : Type v} [Fintype ι]
variable [FiniteDimensional (ZMod p) (room p F 0)]
variable [FiniteDimensional (ZMod p) (room p E 0)]

example (φ : F →+ E)
    (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A))
    (hΦ : SocleLift.IsMarkedHeightFloor p φ Φ)
    (β : Ordinal.{0}) (x : pSocleAt p 0 (G := B)) (e : F)
    (hxe : (x : B) + (e : B) ∈ ulmSubgroup p β) :
    (Φ x : A) + (φ e : A) ∈ ulmSubgroup p β :=
  SocleLift.IsMarkedHeightFloor.add_mem p hΦ β x e hxe

/-- D-23's budget reaches an injective algebraic map on the actual socle. -/
example (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (L : room p F 0 →ₗ[ZMod p] room p E 0)
      (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = SocleLift.markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ :=
  SocleLift.exists_injective_socle_lift_of_budget
    p φ hφ hfloor b r hcompat hbudget

/-- The selected quotient map lifts injectively while preserving every marked
height equation. -/
example (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (L : room p F 0 →ₗ[ZMod p] room p E 0)
    (hL : Function.Injective L)
    (haccess : ∀ i, L (b i) ∈ HeightRado.affineAccess
      (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
      (roomSubspace p E) b r i) :
    ∃ Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A),
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = SocleLift.markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ ∧
      SocleLift.IsMarkedHeightFloor p φ Φ :=
  SocleLift.exists_injective_heightCompatible_socle_lift
    p φ hφ hfloor b r hcompat L hL haccess

/-- D-23's budget reaches the full injective height-compatible socle lift. -/
example (φ : F →+ E) (hφ : Function.Injective φ)
    (hfloor : IsHeightFloorOn p φ)
    (b : Basis ι (ZMod p) (room p F 0))
    (r : ι → Ordinal.{0})
    (hcompat : HeightRado.CompatibleWithReach b r (reachableSubspace p F))
    (hbudget : ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β)) :
    ∃ (L : room p F 0 →ₗ[ZMod p] room p E 0)
      (Φ : pSocleAt p 0 (G := B) →ₗ[ZMod p] pSocleAt p 0 (G := A)),
      Function.Injective L ∧
      (∀ i, L (b i) ∈ HeightRado.affineAccess
        (HeightCell.heightCellBaseMap p φ hfloor b r hcompat)
        (roomSubspace p E) b r i) ∧
      Function.Injective Φ ∧
      Φ.comp (roomSubmodule p F 0).subtype = SocleLift.markedSocleMap p φ ∧
      (roomSubmodule p E 0).mkQ.comp Φ =
        L.comp (roomSubmodule p F 0).mkQ ∧
      SocleLift.IsMarkedHeightFloor p φ Φ :=
  SocleLift.exists_injective_heightCompatible_socle_lift_of_budget
    p φ hφ hfloor b r hcompat hbudget

end Concrete
