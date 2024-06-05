open import Data.Binding

module STLC.Typing {{_ : NomPa}} where

open import Relation.Binary.PropositionalEquality
open import Data.Binding.Context

open import STLC.Syntax

infix 4 _⊢_∈_

Context : World → Set
Context = Ctx Type

data _⊢_∈_ {w} (Γ : Context w) : Term w → Type → Set where
  typ-var : ∀{x τ} → Γ(x) ≡ τ → Γ ⊢ V x ∈ τ
  typ-true : Γ ⊢ True ∈ TBool
  typ-false : Γ ⊢ False ∈ TBool
  typ-if : ∀{e e₁ e₂ τ} →
    Γ ⊢ e ∈ TBool → Γ ⊢ e₁ ∈ τ → Γ ⊢ e₂ ∈ τ →
    Γ ⊢ if e then e₁ else e₂ ∈ τ
  typ-prod : ∀{e₁ e₂ τ₁ τ₂} → Γ ⊢ e₁ ∈ τ₁ → Γ ⊢ e₂ ∈ τ₂ → Γ ⊢ (Pair e₁ e₂) ∈ TProd τ₁ τ₂
  typ-prj₁ : ∀{e τ₁ τ₂} → Γ ⊢ e ∈ TProd τ₁ τ₂ → Γ ⊢ prj₁ e ∈ τ₁
  typ-prj₂ : ∀{e τ₁ τ₂} → Γ ⊢ e ∈ TProd τ₁ τ₂ → Γ ⊢ prj₂ e ∈ τ₂
  typ-abs : ∀{x τ τ' e} → Γ & x ~ τ ⊢ e ∈ τ' → Γ ⊢ ƛ x τ e ∈ τ ⇒ τ'
  typ-app : ∀{e₁ e₂ τ τ'} → Γ ⊢ e₁ ∈ τ ⇒ τ' → Γ ⊢ e₂ ∈ τ → Γ ⊢ e₁ ∙ e₂ ∈ τ'
