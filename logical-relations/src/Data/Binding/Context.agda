open import Data.Binding

module Data.Binding.Context {{_ : NomPa}} where

open import Data.Sum
open import Data.Bool
open import Data.Empty
import Function

record Weaken (F : World → Set) : Set where
  field
    weaken : ∀{α β} → α ⊆ β → F α → F β

Ctx' : ∀ (F : World → Set) → World → Set
Ctx' F w = Name w → F w

Ctx : Set → World → Set
Ctx T = Ctx' (Function.const T)

nil : ∀{F : World → Set} → Ctx' F ∅
nil n = ⊥-elim (¬Name∅ n)

cons : ∀{F : World → Set} {w : World} ⦃ wkF : Weaken F ⦄ →
  Ctx' F w → (b : Binder) → F w → Ctx' F (b ◃ w)
cons ⦃ wkF ⦄ Γ b v n with exportᴺ {_} {b} n
... | inj₁ _ = Weaken.weaken wkF {!!} v
... | inj₂ n' = {! Γ(n') !}
