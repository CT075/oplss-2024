module STLC.Soundness where

open import Data.List using ([]; _∷_)
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Context
open import Relation.Binary.PropositionalEquality

open import STLC.Syntax
open import STLC.Typing
open import STLC.Eval

Substs = Ctx Term

mutual
  _∈V'⟦_⟧ : Term → Type → Set
  True ∈V'⟦ TBool ⟧ = ⊤
  False ∈V'⟦ TBool ⟧ = ⊤
  (Pair e₁ e₂) ∈V'⟦ TProd τ₁ τ₂ ⟧ = e₁ ∈V'⟦ τ₁ ⟧ × e₂ ∈V'⟦ τ₂ ⟧
  (ƛ τ e) ∈V'⟦ τ₁ ⇒ τ₂ ⟧ = τ ≡ τ₁ × (∀ v → v ∈V'⟦ τ₁ ⟧ → bindTerm v e ∈E'⟦ τ₂ ⟧)
  _ ∈V'⟦ _ ⟧ = ⊥

  _∈E'⟦_⟧ : Term → Type → Set
  e ∈E'⟦ τ ⟧ = ∃[ e' ](e ~>* e' × e' ∈V'⟦ τ ⟧)

mutual
  data _∈V⟦_⟧ : Term → Type → Set where
    v-bool-true : True ∈V⟦ TBool ⟧
    v-bool-false : False ∈V⟦ TBool ⟧
    v-pair : ∀{e₁ e₂ τ₁ τ₂} → e₁ ∈V⟦ τ₁ ⟧ → e₂ ∈V⟦ τ₂ ⟧ → Pair e₁ e₂ ∈V⟦ TProd τ₁ τ₂ ⟧
    v-abs : ∀{τ e τ'} → (∀ v → v ∈V'⟦ τ ⟧ → bindTerm v e ∈E⟦ τ' ⟧) → ƛ τ e ∈V⟦ τ ⇒ τ' ⟧

  record _∈E⟦_⟧ (e : Term) (τ : Type) : Set where
    inductive
    constructor E-fold
    field
      value : Term
      evals : e ~>* value
      denot : value ∈V⟦ τ ⟧

mutual
  v-fold : ∀{e τ} → e ∈V'⟦ τ ⟧ → e ∈V⟦ τ ⟧
  v-fold {True} {TBool} tt = v-bool-true
  v-fold {False} {TBool} tt = v-bool-false
  v-fold {Pair e₁ e₂} {TProd τ₁ τ₂} (e₁∈V' , e₂∈V') = v-pair (v-fold e₁∈V') (v-fold e₂∈V')
  v-fold {ƛ ττ e} {τ ⇒ τ'} (τ≡ττ , body-valid) rewrite τ≡ττ =
    v-abs (λ v v∈V' → e-fold (body-valid v v∈V'))

  e-fold : ∀{e τ} → e ∈E'⟦ τ ⟧ → e ∈E⟦ τ ⟧
  e-fold (e' , e~>*e' , e'∈V') = E-fold e' e~>*e' (v-fold e'∈V')

mutual
  v-unfold : ∀{e τ} → e ∈V⟦ τ ⟧ → e ∈V'⟦ τ ⟧
  v-unfold v-bool-true = tt
  v-unfold v-bool-false = tt
  v-unfold (v-pair e₁∈V e₂∈V) = v-unfold e₁∈V , v-unfold e₂∈V
  v-unfold (v-abs body-valid) = refl , (λ v v∈V' → e-unfold (body-valid v v∈V'))

  e-unfold : ∀{e τ} → e ∈E⟦ τ ⟧ → e ∈E'⟦ τ ⟧
  e-unfold (E-fold e' e~>*e' e'∈V) = e' , e~>*e' , v-unfold e'∈V

data _∈G⟦_⟧ : Substs → Context → Set where
  g-emp : [] ∈G⟦ [] ⟧
  g-cons : ∀{γ Γ x v τ γ' Γ'} → γ' ≡ γ & x ~ v → Γ' ≡ Γ & x ~ τ →
    v ∈V'⟦ τ ⟧ → γ ∈G⟦ Γ ⟧ →
    γ' ∈G⟦ Γ' ⟧
