import Lib.BackForth.Algebraic

/-!
# Restricting limit algebraic data to a smaller cutoff

This module isolates the monotonicity step needed by the limit back-and-forth
assembly.  Limit data at `α` yields limit data at every `β ≤ α`: the Ulm and
height clauses restrict directly, while the length dichotomy is re-split at the
smaller cutoff.

No back-and-forth characterization theorem is used here.
-/

open Ordinal Cardinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]
variable {n : ℕ}

/-- Restrict limit-condition data from `α` to a smaller index `β`. -/
noncomputable def AlgBFLimitCondData.restrict
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α β : Ordinal.{0}} (hβα : β ≤ α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFLimitCondData p hG hH α a b) :
    AlgBFLimitCondData p hG hH β a b := by
  have hbase : ω * β ≤ ω * α := mul_le_mul_right hβα ω
  refine {
    iso := C.iso
    lengths := ?_
    ulm_below := ?_
    heights := ?_ }
  · rcases C.lengths with hshort | hlong
    · rcases lt_or_ge (ulmLength p (G := G) hG : Ordinal.{0}) (ω * β) with hlt | hge
      · exact Or.inl ⟨hshort.1, hlt⟩
      · exact Or.inr ⟨hge, by rw [← hshort.1]; exact hge⟩
    · exact Or.inr ⟨hbase.trans hlong.1, hbase.trans hlong.2⟩
  · intro γ hγ
    exact C.ulm_below γ (hγ.trans_le hbase)
  · intro x
    rcases C.heights x with hlow | hhigh
    · rcases lt_or_ge (ulmHeight p (x : H))
        (((ω * β : Ordinal.{0})) : WithTop Ordinal.{0}) with hxlt | hxge
      · exact Or.inl ⟨hlow.1, hxlt⟩
      · exact Or.inr ⟨hxge, by rw [← hlow.1]; exact hxge⟩
    · have hbase' :
          ((ω * β : Ordinal.{0}) : WithTop Ordinal.{0}) ≤
            ((ω * α : Ordinal.{0}) : WithTop Ordinal.{0}) :=
        WithTop.coe_le_coe.mpr hbase
      exact Or.inr ⟨hbase'.trans hhigh.1, hbase'.trans hhigh.2⟩

/-- Proposition-level monotonicity of the limit algebraic condition. -/
theorem AlgBFLimitCond.antitone
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α β : Ordinal.{0}} (hβα : β ≤ α)
    {a : Fin n → G} {b : Fin n → H} :
    AlgBFLimitCond p hG hH α a b → AlgBFLimitCond p hG hH β a b := by
  rintro ⟨C⟩
  exact ⟨C.restrict p hG hH hβα⟩

/-- Limit data at `α` restricts to the complete even package at every
successor cutoff `succ δ ≤ α`.

After restricting the limit cutoff to `succ δ`, its base is
`ω * succ δ = ω * δ + ω`, exactly the cap in the even condition.  Absolute
Ulm equality below that cap and the marked height equivalence turn the crossed
even window into pointwise equality. -/
noncomputable def AlgBFLimitCondData.toEven
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α δ : Ordinal.{0}} (hδα : Order.succ δ ≤ α)
    {a : Fin n → G} {b : Fin n → H}
    (C : AlgBFLimitCondData p hG hH α a b) :
    AlgBFEvenCondData p hG hH δ a b := by
  let L : AlgBFLimitCondData p hG hH (Order.succ δ) a b :=
    C.restrict p hG hH hδα
  have hcut : ω * Order.succ δ = ω * δ + ω := by
    rw [Ordinal.mul_succ]
  refine {
    iso := L.iso
    lengths := ?_
    ulm_below := ?_
    window := ?_
    heights := ?_ }
  · exact hcut ▸ L.lengths
  · intro β hβ
    exact L.ulm_below β (hβ.trans_le (by rw [hcut]; exact le_self_add))
  · apply EvenWindowCrossed.of_eq
    · intro β _hbase hβ
      exact L.ulm_below β (hcut.symm ▸ hβ)
    · intro β _hbase hβ
      have hleftFinite : Set.Finite (tupleSubgroup a : Set G) :=
        tupleSubgroup_finite p hG.primary a
      have hrightFinite : Set.Finite (tupleSubgroup b : Set H) :=
        tupleSubgroup_finite p hH.primary b
      have hsymm : ∀ x : tupleSubgroup a,
          (ulmHeight p (L.iso.equiv.symm x : H) = ulmHeight p (x : G) ∧
            ulmHeight p (x : G) < ω * Order.succ δ) ∨
          (ω * Order.succ δ ≤ ulmHeight p (x : G) ∧
            ω * Order.succ δ ≤ ulmHeight p (L.iso.equiv.symm x : H)) := by
        intro x
        let y : tupleSubgroup b := L.iso.equiv.symm x
        have hy : L.iso.equiv y = x := L.iso.equiv.apply_symm_apply x
        rcases L.heights y with hlow | hhigh
        · exact Or.inl ⟨by simpa [y, hy] using hlow.1,
            by
              calc
                ulmHeight p (x : G) = ulmHeight p (y : H) := by
                  simpa [hy] using hlow.1.symm
                _ < ((ω * Order.succ δ : Ordinal.{0}) :
                    WithTop Ordinal.{0}) := hlow.2⟩
        · exact Or.inr ⟨by simpa [hy] using hhigh.2,
            by simpa [y] using hhigh.1⟩
      exact (markedGradedInvariant_eq_iff_of_heightPres
        p hG hH
        (tupleSubgroup a) (tupleSubgroup b)
        hleftFinite hrightFinite L.iso.equiv.symm
        (ω * Order.succ δ) hsymm β (hcut.symm ▸ hβ)).mp
          (L.ulm_below β (hcut.symm ▸ hβ)).symm
  · exact hcut ▸ L.heights

/-- Proposition-level limit-to-even restriction. -/
theorem AlgBFLimitCond.toEven
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G) (hH : IsReducedPGroup p H)
    {α δ : Ordinal.{0}} (hδα : Order.succ δ ≤ α)
    {a : Fin n → G} {b : Fin n → H} :
    AlgBFLimitCond p hG hH α a b → AlgBFEvenCond p hG hH δ a b := by
  rintro ⟨C⟩
  exact ⟨C.toEven p hG hH hδα⟩
