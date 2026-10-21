/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth

# Infinitary Logic: Core Syntax with an L_{ω₁,ω} Interface

This file defines the generic infinitary syntax underlying the project, building on Mathlib's
first-order language and term infrastructure. The key extension is the addition of
infinitary conjunction (`iInf`) and disjunction (`iSup`) constructors.

The project itself is aimed at `L_{ω₁,ω}`. Concretely, the intended public interface is:

- `LOmegaOneBoundedFormula`, `LOmegaOneFormula`, `LOmegaOneSentence`, `LOmegaOneTheory`
- `IsLOmegaOne`

The more general `InfBoundedFormula` type remains as a reusable core syntax layer.

## Main Definitions

- `InfBoundedFormula L α n` — generic infinitary bounded formulas with free variables in `α`
  and bound variables in `Fin n`.
- `InfFormula`, `InfSentence`, `InfTheory` — formulas, sentences, and theories.
- `CardBounded κ φ` — predicate asserting all infinitary connectives use index types
  of cardinality < κ, restricting to L_{κ,ω}.
- Derived connectives: `not`, `top`, `ex`, `inf`, `sup`, `iff`.
- `IsFinitary` — predicate for formulas using no infinitary connectives.

## References

- C.J. Ash and J. Knight, *Computable Structures and the Hyperarithmetical Hierarchy*,
  Chapter 6, Sections 6.1, 6.3.
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Aleph

universe u v u' w

namespace FirstOrder.Language

variable (L : Language.{u, v})

/-- `InfBoundedFormula L α n` is the generic ambient type of infinitary formulas with free variables
indexed by `α` and `n` bound variables in scope (indexed by `Fin n`).

This extends Mathlib's `BoundedFormula` with infinitary conjunction (`iInf`) and
disjunction (`iSup`). The constructors `iSup` and `iInf` take an indexed family
of formulas over an arbitrary type `ι : Type w`. To restrict to the `L_{ω₁,ω}` fragment used by
this project, use `LOmegaOneBoundedFormula` together with `IsLOmegaOne`.

The universe parameter `w` controls the ambient size of index types for infinitary
connectives. In this project, the `L_{ω₁,ω}` interface fixes `w = 0` and then imposes the
actual countability restriction via `IsLOmegaOne`. -/
inductive InfBoundedFormula (α : Type u') : ℕ → Type max u v u' (w + 1)
  /-- The false formula ⊥. -/
  | falsum {n} : InfBoundedFormula α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : InfBoundedFormula α n
  /-- A relation symbol applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      InfBoundedFormula α n
  /-- Implication φ → ψ. -/
  | imp {n} (φ ψ : InfBoundedFormula α n) : InfBoundedFormula α n
  /-- Universal quantification ∀x. φ. Binds the variable indexed by `n`. -/
  | all {n} (φ : InfBoundedFormula α (n + 1)) : InfBoundedFormula α n
  /-- Infinitary disjunction ⋁_{i : ι} φ_i. -/
  | iSup {n} (ι : Type w) (φ : ι → InfBoundedFormula α n) : InfBoundedFormula α n
  /-- Infinitary conjunction ⋀_{i : ι} φ_i. -/
  | iInf {n} (ι : Type w) (φ : ι → InfBoundedFormula α n) : InfBoundedFormula α n

variable {L}

/-- `InfFormula L α` is the type of infinitary formulas with free variables indexed by `α`
and no bound variables in scope. -/
abbrev InfFormula (L : Language.{u, v}) (α : Type u') : Type _ :=
  @InfBoundedFormula.{u, v, u', w} L α 0

/-- `InfSentence L` is the type of infinitary sentences (no free or bound variables). -/
abbrev InfSentence (L : Language.{u, v}) : Type _ :=
  @InfFormula.{u, v, 0, w} L PEmpty

/-- `InfTheory L` is the type of infinitary theories (sets of sentences). -/
abbrev InfTheory (L : Language.{u, v}) : Type _ :=
  Set (@InfSentence.{u, v, w} L)

/-- The first uncountable cardinal, used to state the `L_{ω₁,ω}` bound. -/
noncomputable abbrev alephOne : Cardinal := Cardinal.aleph 1

/-- The first uncountable ordinal. -/
noncomputable abbrev omegaOne : Ordinal := Ordinal.omega 1

/-- Bounded formulas intended for the `L_{ω₁,ω}` fragment. The infinitary indices live in
`Type 0`; countability is still imposed separately via `CardBounded alephOne`. -/
abbrev LOmegaOneBoundedFormula (L : Language.{u, v}) (α : Type u') (n : ℕ) : Type _ :=
  @InfBoundedFormula.{u, v, u', 0} L α n

/-- Formulas intended for the `L_{ω₁,ω}` fragment. -/
abbrev LOmegaOneFormula (L : Language.{u, v}) (α : Type u') : Type _ :=
  @LOmegaOneBoundedFormula.{u, v, u'} L α 0

/-- Sentences intended for the `L_{ω₁,ω}` fragment. -/
abbrev LOmegaOneSentence (L : Language.{u, v}) : Type _ :=
  @LOmegaOneFormula.{u, v, 0} L PEmpty

/-- Theories intended for the `L_{ω₁,ω}` fragment. -/
abbrev LOmegaOneTheory (L : Language.{u, v}) : Type _ :=
  Set (@LOmegaOneSentence.{u, v} L)

namespace InfBoundedFormula

variable {α : Type u'} {n : ℕ}

/-- Negation: ¬φ := φ → ⊥ -/
protected def not (φ : @InfBoundedFormula.{u, v, u', w} L α n) :
    @InfBoundedFormula.{u, v, u', w} L α n :=
  φ.imp falsum

/-- Verum: ⊤ := ¬⊥ -/
protected def top : @InfBoundedFormula.{u, v, u', w} L α n :=
  InfBoundedFormula.falsum.not

/-- Existential quantifier: ∃x. φ := ¬(∀x. ¬φ) -/
protected def ex (φ : @InfBoundedFormula.{u, v, u', w} L α (n + 1)) :
    @InfBoundedFormula.{u, v, u', w} L α n :=
  φ.not.all.not

/-- Disjunction of two formulas: φ ∨ ψ := ¬φ → ψ -/
protected def sup (φ ψ : @InfBoundedFormula.{u, v, u', w} L α n) :
    @InfBoundedFormula.{u, v, u', w} L α n :=
  φ.not.imp ψ

/-- Conjunction of two formulas: φ ∧ ψ := ¬(φ → ¬ψ) -/
protected def inf (φ ψ : @InfBoundedFormula.{u, v, u', w} L α n) :
    @InfBoundedFormula.{u, v, u', w} L α n :=
  (φ.imp ψ.not).not

/-- Biconditional: φ ↔ ψ := (φ → ψ) ∧ (ψ → φ) -/
protected def iff (φ ψ : @InfBoundedFormula.{u, v, u', w} L α n) :
    @InfBoundedFormula.{u, v, u', w} L α n :=
  (φ.imp ψ).inf (ψ.imp φ)

/-- Close a formula with `k` universal quantifiers. -/
def forallClosure : (k : ℕ) → @InfBoundedFormula.{u, v, u', w} L α (n + k) →
    @InfBoundedFormula.{u, v, u', w} L α n
  | 0, φ => φ
  | k + 1, φ => forallClosure k φ.all

/-- Close a formula with `k` existential quantifiers. -/
def existsClosure : (k : ℕ) → @InfBoundedFormula.{u, v, u', w} L α (n + k) →
    @InfBoundedFormula.{u, v, u', w} L α n
  | 0, φ => φ
  | k + 1, φ => existsClosure k φ.ex

section CardBounded

/-- A formula is `CardBounded κ` if every infinitary connective (`iSup`, `iInf`) uses an
index type of cardinality strictly less than `κ`. This restricts formulas to L_{κ,ω}.

For example, `CardBounded ℵ₁` gives L_{ω₁,ω} formulas (countable conjunctions/disjunctions).
Finitary formulas (using no `iSup`/`iInf`) are `CardBounded κ` for any `κ`. -/
inductive CardBounded (κ : Cardinal.{w}) :
    {n : ℕ} → @InfBoundedFormula.{u, v, u', w} L α n → Prop where
  | falsum {n} : CardBounded κ (.falsum : @InfBoundedFormula L α n)
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
      CardBounded κ (.equal t₁ t₂ : @InfBoundedFormula L α n)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      CardBounded κ (.rel R ts : @InfBoundedFormula L α n)
  | imp {n} {φ ψ : @InfBoundedFormula.{u, v, u', w} L α n} :
      CardBounded κ φ → CardBounded κ ψ → CardBounded κ (φ.imp ψ)
  | all {n} {φ : @InfBoundedFormula.{u, v, u', w} L α (n + 1)} :
      CardBounded κ φ → CardBounded κ φ.all
  | iSup {n} {ι : Type w} {φ : ι → @InfBoundedFormula.{u, v, u', w} L α n} :
      Cardinal.mk ι < κ → (∀ i, CardBounded κ (φ i)) → CardBounded κ (.iSup ι φ)
  | iInf {n} {ι : Type w} {φ : ι → @InfBoundedFormula.{u, v, u', w} L α n} :
      Cardinal.mk ι < κ → (∀ i, CardBounded κ (φ i)) → CardBounded κ (.iInf ι φ)

variable {κ : Cardinal.{w}}

/-- Predicate asserting an infinitary formula lies in the `L_{ω₁,ω}` fragment. -/
abbrev IsLOmegaOne {n : ℕ} (φ : @InfBoundedFormula.{u, v, u', 0} L α n) : Prop :=
  CardBounded alephOne φ

theorem CardBounded.not {φ : @InfBoundedFormula.{u, v, u', w} L α n}
    (h : CardBounded κ φ) : CardBounded κ φ.not :=
  .imp h .falsum

theorem CardBounded.top' :
    CardBounded κ (InfBoundedFormula.top : @InfBoundedFormula.{u, v, u', w} L α n) :=
  CardBounded.falsum.not

theorem CardBounded.ex {φ : @InfBoundedFormula.{u, v, u', w} L α (n + 1)}
    (h : CardBounded κ φ) : CardBounded κ φ.ex :=
  (h.not.all).not

theorem CardBounded.sup {φ ψ : @InfBoundedFormula.{u, v, u', w} L α n}
    (hφ : CardBounded κ φ) (hψ : CardBounded κ ψ) : CardBounded κ (φ.sup ψ) :=
  hφ.not.imp hψ

theorem CardBounded.inf' {φ ψ : @InfBoundedFormula.{u, v, u', w} L α n}
    (hφ : CardBounded κ φ) (hψ : CardBounded κ ψ) : CardBounded κ (φ.inf ψ) :=
  (hφ.imp hψ.not).not

/-- A `CardBounded κ` formula is also `CardBounded κ'` for any `κ' ≥ κ`. -/
theorem CardBounded.mono {κ' : Cardinal.{w}} (hle : κ ≤ κ')
    {φ : @InfBoundedFormula.{u, v, u', w} L α n} (h : CardBounded κ φ) :
    CardBounded κ' φ := by
  induction h with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ ih => exact .all ih
  | iSup hlt _ ih => exact .iSup (lt_of_lt_of_le hlt hle) ih
  | iInf hlt _ ih => exact .iInf (lt_of_lt_of_le hlt hle) ih

end CardBounded

section IsFinitary

/-- A formula is finitary if it uses no infinitary connectives (`iSup` or `iInf`). -/
inductive IsFinitary : {n : ℕ} → @InfBoundedFormula.{u, v, u', w} L α n → Prop where
  | falsum {n} : IsFinitary (.falsum : @InfBoundedFormula L α n)
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
      IsFinitary (.equal t₁ t₂ : @InfBoundedFormula L α n)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      IsFinitary (.rel R ts : @InfBoundedFormula L α n)
  | imp {n} {φ ψ : @InfBoundedFormula.{u, v, u', w} L α n} :
      IsFinitary φ → IsFinitary ψ → IsFinitary (φ.imp ψ)
  | all {n} {φ : @InfBoundedFormula.{u, v, u', w} L α (n + 1)} :
      IsFinitary φ → IsFinitary φ.all

/-- Finitary formulas are `CardBounded κ` for any cardinal `κ`. -/
theorem IsFinitary.cardBounded (κ : Cardinal.{w})
    {φ : @InfBoundedFormula.{u, v, u', w} L α n} (h : IsFinitary φ) :
    CardBounded κ φ := by
  induction h with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ ih => exact .all ih

end IsFinitary

section FreeVariables

/-- The set of free variables occurring in an infinitary bounded formula.
For infinitary connectives, this is the union over all index values. -/
noncomputable def freeVarSet [DecidableEq α] :
    {n : ℕ} → @InfBoundedFormula.{u, v, u', w} L α n → Set α
  | _, .falsum => ∅
  | _, .equal t₁ t₂ =>
      {a | Sum.inl a ∈ t₁.varFinset} ∪ {a | Sum.inl a ∈ t₂.varFinset}
  | _, .rel _R ts =>
      ⋃ i, {a | Sum.inl a ∈ (ts i).varFinset}
  | _, .imp φ ψ => freeVarSet φ ∪ freeVarSet ψ
  | _, .all φ => freeVarSet φ
  | _, .iSup _ι φ => ⋃ i, freeVarSet (φ i)
  | _, .iInf _ι φ => ⋃ i, freeVarSet (φ i)

end FreeVariables

end InfBoundedFormula

end FirstOrder.Language
