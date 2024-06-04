module Data.Binding where

open import Data.Bool
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary using (Reflexive; Transitive)

record NomPa : Set₁ where
  field
    World  : Set
    Name   : World → Set
    Binder : Set
    _◃_    : Binder → World → World

    zeroᴮ  : Binder
    sucᴮ   : Binder → Binder

    nameᴮ   : ∀ {α} b → Name (b ◃ α)
    binderᴺ : ∀ {α} → Name α → Binder

    ∅      : World
    ¬Name∅ : ¬ (Name ∅)

    _==ᴺ_   : ∀ {α} (x y : Name α) → Bool
    exportᴺ : ∀ {α b} → Name (b ◃ α)
            → Name (b ◃ ∅) ⊎ Name α

    _#_  : Binder → World → Set
    _#∅  : ∀ b → b # ∅
    suc# : ∀ {α b} → b # α → (sucᴮ b) # (b ◃ α)

    _⊆_     : World → World → Set
    coerceᴺ : ∀ {α b} → α ⊆ b → Name α → Name b
    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-∅     : ∀ {α} → ∅ ⊆ α
    ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)

open NomPa {{...}} public
