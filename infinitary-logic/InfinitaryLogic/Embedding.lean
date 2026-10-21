/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Embedding of Finitary Formulas into the Infinitary Core

This file defines the canonical embedding of Mathlib's finitary `BoundedFormula` into
the project's generic infinitary core syntax, and proves it preserves semantics.

## Main Definitions

- `BoundedFormula.toInf` — embedding of finitary formulas into the infinitary core.
- `BoundedFormula.realize_toInf` — the embedding preserves realization.
- `BoundedFormula.toInf_isFinitary` — the image is always finitary.
- `BoundedFormula.toInf_cardBounded` — the image is `CardBounded κ` for any `κ`.

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6.
-/

import InfinitaryLogic.Semantics

universe u v u' w

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type u'}

open InfBoundedFormula

/-- Canonical embedding of a finitary bounded formula into an infinitary bounded formula.
Every finitary formula is naturally an infinitary formula that uses no `iSup` or `iInf`. -/
def BoundedFormula.toInf : {n : ℕ} → L.BoundedFormula α n →
    @InfBoundedFormula.{u, v, u', w} L α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => .imp φ.toInf ψ.toInf
  | _, .all φ => .all φ.toInf

/-- The embedding of a finitary formula produces a finitary infinitary formula. -/
theorem BoundedFormula.toInf_isFinitary {n : ℕ} (φ : L.BoundedFormula α n) :
    (φ.toInf : @InfBoundedFormula.{u, v, u', w} L α n).IsFinitary := by
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | all φ ih => exact .all ih

/-- Finitary formulas embedded into infinitary formulas are `CardBounded κ` for any `κ`. -/
theorem BoundedFormula.toInf_cardBounded {n : ℕ} (φ : L.BoundedFormula α n)
    (κ : Cardinal.{w}) :
    (φ.toInf : @InfBoundedFormula.{u, v, u', w} L α n).CardBounded κ :=
  φ.toInf_isFinitary.cardBounded κ

/-- The embedding preserves realization: a finitary formula and its infinitary image
are satisfied by exactly the same tuples in every structure. -/
theorem BoundedFormula.realize_toInf {n : ℕ} (φ : L.BoundedFormula α n)
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (φ.toInf : @InfBoundedFormula.{u, v, u', w} L α n).Realize v xs ↔
    φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    simpa [BoundedFormula.toInf, InfBoundedFormula.Realize, BoundedFormula.Realize] using
      imp_congr (ihφ xs) (ihψ xs)
  | all φ ih =>
    simpa [BoundedFormula.toInf, InfBoundedFormula.Realize, BoundedFormula.Realize] using
      forall_congr' fun x => ih (Fin.snoc xs x)

end FirstOrder.Language
