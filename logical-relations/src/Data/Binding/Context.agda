open import Data.Binding

module Data.Binding.Context {{_ : NomPa}} where

open import Data.Sum
open import Data.Bool
open import Data.Empty
open import Function

open import Data.Binding.Operations

Ctx' : ∀ (F : World → Set) → World → Set
Ctx' F w = Name w → F w

Ctx : Set → World → Set
Ctx = Ctx' ∘ const

nil : ∀{F : World → Set} → Ctx' F ∅
nil n = ⊥-elim (¬Name∅ n)

record Weaken (F : World → Set) : Set where
  field
    weaken : ∀{α β} → α ⊆ β → F α → F β

cons' : ∀{F : World → Set} {w : World} ⦃ wkF : Weaken F ⦄ →
  Ctx' F w → (b : Binder) → b # w → F w → Ctx' F (b ◃ w)
cons' ⦃ wkF ⦄ Γ b b#w v = Weaken.weaken wkF (⊆-# b#w) ∘ exportWith v Γ

cons : ∀{T : Set} {w : World} → Ctx T w → (b : Binder) → T → Ctx T (b ◃ w)
cons Γ b v n with exportᴺ {_} {b} n
... | inj₁ _ = v
... | inj₂ n' = Γ(n')

infix 21 _&_~_
_&_~_ = cons
