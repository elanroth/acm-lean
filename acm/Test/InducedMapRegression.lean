import Lib.BackForth.InducedMap

/-!
# Specification regressions for the induced map on jump spaces

These pin the two properties that the odd characterization depends on and that a
careless reconstruction would silently break:

1. the induced map is an `AddMonoidHom`, **not** an `AddEquiv`, and
2. injectivity is an extra hypothesis on `φ`, not a consequence of the construction.
-/

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G H : Type u} [AddCommGroup G] [AddCommGroup H]

/-- The induced map is well defined on classes: this is the paper's
`def:inducedmap` equation `ḡ_β([c]) = [g(c)]`. -/
example {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β)) (hβ : IsHeightFloorAt p φ β)
    (c : jumpNum p F β) :
    jumpMap p φ hsucc hβ (QuotientAddGroup.mk c)
      = QuotientAddGroup.mk (jumpNumMap p φ hsucc c) :=
  jumpMap_mk p φ hsucc hβ c

/-- The height floor, not height preservation, is what the construction consumes,
and only at the two levels the jump space at `β` mentions. -/
example {F : AddSubgroup G} {E : AddSubgroup H} {φ : F →+ E}
    (hφ : IsHeightPresOn p φ) : IsHeightFloorOn p φ :=
  hφ.isHeightFloorOn p

example {F : AddSubgroup G} {E : AddSubgroup H} {φ : F →+ E}
    (hφ : IsHeightFloorOn p φ) (γ : Ordinal.{0}) : IsHeightFloorAt p φ γ :=
  hφ γ

/-- Injectivity is equivalent to denominator reflection — in particular it is a
condition *on `φ`*, not a theorem about the construction. -/
example {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β)) (hβ : IsHeightFloorAt p φ β) :
    Function.Injective (jumpMap p φ hsucc hβ) ↔
      ∀ c : jumpNum p F β,
        (φ ⟨(c : G), jumpNum_le_self p F β c.2⟩ : H) ∈ jumpDen p E β →
          (c : G) ∈ jumpDen p F β :=
  jumpMap_injective_iff p φ hsucc hβ

/-- **The anti-equivalence regression.**  The induced map is non-injective
whenever the target jump space collapses and the source does not.  If `jumpMap`
were ever rebuilt as an `AddEquiv` (for instance by imitating
`kaplanskyDomainEquiv`, which *is* an equivalence), this statement would become
unprovable and this test would fail. -/
example {F : AddSubgroup G} {E : AddSubgroup H} (φ : F →+ E) {β : Ordinal.{0}}
    (hsucc : IsHeightFloorAt p φ (Order.succ β)) (hβ : IsHeightFloorAt p φ β)
    (htarget : Subsingleton (jumpSpace p E β))
    (hsource : ¬ Subsingleton (jumpSpace p F β)) :
    ¬ Function.Injective (jumpMap p φ hsucc hβ) :=
  jumpMap_not_injective_of_target_subsingleton p φ hsucc hβ htarget hsource
