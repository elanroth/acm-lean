import Lib.BackForth.FiniteEmbedding

/-!
# Finite marked-embedding regression tests

These compile-time checks pin the finite free climb and the exact finite D-23
criterion, including the essential requirement that the marked target be the
image of the marked source in the necessity direction.
-/

noncomputable section

open Module Ordinal

universe u

variable (p : ℕ) [Fact p.Prime]
variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- Once the full source socle is mapped injectively with a height floor, a
finite reduced primary source can be climbed completely. -/
example [Finite B] (hB : IsReducedPGroup p B)
    (H : AddSubgroup B)
    (hSocle : pSocleAt p (0 : Ordinal.{0}) (G := B) ≤ H)
    (φ : H →+ (⊤ : AddSubgroup A))
    (hφ : Function.Injective φ) (hfloor : IsHeightFloorOn p φ) :
    ∃ f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : H, (f ⟨(x : B), trivial⟩ : A) = (φ x : A) :=
  FiniteEmbedding.finite_free_climb p hB H hSocle φ hφ hfloor

/-- For finite source and target, D-23 is exactly equivalent to a full marked
embedding when `E` is the marked image. -/
example [Finite A] [Finite B]
    (hB : IsReducedPGroup p B)
    (F : AddSubgroup B) (E : AddSubgroup A)
    (φ : F →+ E) (hφ : Function.Injective φ)
    (hφsurj : Function.Surjective φ)
    (hfloor : IsHeightFloorOn p φ) :
    (∃ f : (⊤ : AddSubgroup B) →+ (⊤ : AddSubgroup A),
      Function.Injective f ∧ IsHeightFloorOn p f ∧
      ∀ x : F, (f ⟨(x : B), trivial⟩ : A) = (φ x : A)) ↔
    ∀ β : Ordinal.{0},
      Survival.KernelRoomBudgetAt p φ β
        (hfloor (Order.succ β)) (hfloor β) :=
  FiniteEmbedding.finite_embedding_iff_kernelRoomBudget
    p hB F E φ hφ hφsurj hfloor

