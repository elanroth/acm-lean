/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Infinitary Logic: Semantics for the Infinitary Core

This file defines the satisfaction relation for infinitary formulas, extending
Mathlib's first-order semantics with infinitary conjunction and disjunction.

The core definitions are generic, but downstream files in this project primarily use the
`L_{ω₁,ω}` aliases from `Syntax.lean`.

## Main Definitions

- `InfBoundedFormula.Realize` — realization of a bounded formula in a structure M.
- `InfFormula.Realize` — realization of a formula (no bound variables).
- `InfSentence.Realize` — realization of a sentence in a structure.
- `InfTheory.IsModel` — a structure is a model of a theory.
- `InfBoundedFormula.SemEquiv` — semantic equivalence of formulas.
- `infElementarilyEquivalent` — M ≡_{∞,ω} N.

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Section 6.1.
-/

import InfinitaryLogic.Syntax
import Mathlib.ModelTheory.Semantics

universe u v u' w

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type u'} {M : Type*} [L.Structure M]

open Structure

namespace InfBoundedFormula

/-- Realize an infinitary bounded formula in a structure `M`.

  - `falsum` is false.
  - `equal t₁ t₂` holds when the terms evaluate to the same element.
  - `rel R ts` holds when `R` holds of the evaluated terms.
  - `imp φ ψ` is the usual implication.
  - `all φ` universally quantifies over elements of `M`.
  - `iSup ι φ` (infinitary disjunction) holds when some `φ i` holds.
  - `iInf ι φ` (infinitary conjunction) holds when all `φ i` hold.
-/
def Realize : {n : ℕ} → @InfBoundedFormula.{u, v, u', w} L α n →
    (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs =>
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs =>
      RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ x : M, Realize φ v (Fin.snoc xs x)
  | _, .iSup _ι φ, v, xs => ∃ i, Realize (φ i) v xs
  | _, .iInf _ι φ, v, xs => ∀ i, Realize (φ i) v xs

variable {n : ℕ} {φ ψ : @InfBoundedFormula.{u, v, u', w} L α n}
variable {v : α → M} {xs : Fin n → M}

/-! ### Simp lemmas for `Realize` -/

@[simp]
theorem realize_falsum :
  (.falsum : @InfBoundedFormula.{u, v, u', w} L α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_imp :
  (φ.imp ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  Iff.rfl

@[simp]
theorem realize_all {φ : @InfBoundedFormula.{u, v, u', w} L α (n + 1)} :
  φ.all.Realize v xs ↔ ∀ x : M, φ.Realize v (Fin.snoc xs x) :=
  Iff.rfl

@[simp]
theorem realize_iSup {ι : Type w}
    {φ : ι → @InfBoundedFormula.{u, v, u', w} L α n} :
  (InfBoundedFormula.iSup ι φ).Realize v xs ↔ ∃ i, (φ i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_iInf {ι : Type w}
    {φ : ι → @InfBoundedFormula.{u, v, u', w} L α n} :
  (InfBoundedFormula.iInf ι φ).Realize v xs ↔ ∀ i, (φ i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_not :
  φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

/-- The empty disjunction is false. -/
theorem realize_iSup_pempty {φ : PEmpty → @InfBoundedFormula.{u, v, u', w} L α n} :
  (InfBoundedFormula.iSup PEmpty φ).Realize v xs ↔ False := by
  simp only [realize_iSup]
  exact ⟨fun ⟨i, _⟩ => i.elim, False.elim⟩

/-- The empty conjunction is true. -/
theorem realize_iInf_pempty {φ : PEmpty → @InfBoundedFormula.{u, v, u', w} L α n} :
  (InfBoundedFormula.iInf PEmpty φ).Realize v xs ↔ True := by
  simp only [realize_iInf]
  exact ⟨fun _ => trivial, fun _ i => i.elim⟩

end InfBoundedFormula

/-! ### Formula and Sentence realization -/

namespace InfFormula

/-- Realize a formula (no bound variables in scope) at a given variable assignment. -/
nonrec def Realize (φ : @InfFormula.{u, v, u', w} L α) (v : α → M) : Prop :=
  φ.Realize v Fin.elim0

end InfFormula

namespace InfSentence

/-- Realize a sentence in a structure `M`. A sentence has no free or bound variables. -/
nonrec def Realize (φ : @InfSentence.{u, v, w} L) (M : Type*) [L.Structure M] : Prop :=
  InfFormula.Realize φ (PEmpty.elim : PEmpty → M)

end InfSentence

/-! ### Theories and models -/

namespace InfTheory

variable (T : @InfTheory.{u, v, w} L)

/-- A structure `M` is a model of an infinitary theory if it satisfies every sentence
in the theory. -/
def IsModel (M : Type*) [L.Structure M] : Prop :=
  ∀ φ ∈ T, InfSentence.Realize φ M

end InfTheory

/-! ### Semantic equivalence -/

/-- Two infinitary bounded formulas are semantically equivalent if they are realized by the
same tuples in all structures. -/
def InfBoundedFormula.SemEquiv {n : ℕ}
    (φ ψ : @InfBoundedFormula.{u, v, u', w} L α n) : Prop :=
  ∀ (M : Type (max u (max v (max u' w)))) [L.Structure M] (v : α → M) (xs : Fin n → M),
    φ.Realize v xs ↔ ψ.Realize v xs

/-! ### Elementary equivalence -/

/-- Two structures are infinitarily elementarily equivalent (M ≡_{∞,ω} N) if they
satisfy exactly the same infinitary sentences. -/
def infElementarilyEquivalent (M N : Type*) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : @InfSentence.{u, v, w} L, InfSentence.Realize φ M ↔ InfSentence.Realize φ N

end FirstOrder.Language
