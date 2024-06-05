open import Data.Binding

module STLC.Soundness {{_ : NomPa}} where

open import Data.List using ([]; _∷_)
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Function

open import Data.Binding.Context

open import STLC.Syntax
open import STLC.Typing
open import STLC.Eval

Substs = Ctx (Term ∅)

mutual
  _∈V'⟦_⟧ : Term ∅ → Type → Set
  True ∈V'⟦ TBool ⟧ = ⊤
  False ∈V'⟦ TBool ⟧ = ⊤
  (Pair e₁ e₂) ∈V'⟦ TProd τ₁ τ₂ ⟧ = e₁ ∈V'⟦ τ₁ ⟧ × e₂ ∈V'⟦ τ₂ ⟧
  (ƛ x τ e) ∈V'⟦ τ₁ ⇒ τ₂ ⟧ = τ ≡ τ₁ × (∀ v → v ∈V'⟦ τ₁ ⟧ → plug∅ v e ∈E'⟦ τ₂ ⟧)
  _ ∈V'⟦ _ ⟧ = ⊥

  _∈E'⟦_⟧ : Term ∅ → Type → Set
  e ∈E'⟦ τ ⟧ = ∃[ e' ](e ~>* e' × e' ∈V'⟦ τ ⟧)

mutual
  data _∈V⟦_⟧ : Term ∅ → Type → Set where
    v-bool-true : True ∈V⟦ TBool ⟧
    v-bool-false : False ∈V⟦ TBool ⟧
    v-pair : ∀{e₁ e₂ τ₁ τ₂} → e₁ ∈V⟦ τ₁ ⟧ → e₂ ∈V⟦ τ₂ ⟧ → Pair e₁ e₂ ∈V⟦ TProd τ₁ τ₂ ⟧
    v-abs : ∀{τ x e τ'} → (∀ v → v ∈V'⟦ τ ⟧ → plug∅ v e ∈E⟦ τ' ⟧) → ƛ x τ e ∈V⟦ τ ⇒ τ' ⟧

  record _∈E⟦_⟧ (e : Term ∅) (τ : Type) : Set where
    inductive
    constructor E-fold
    field
      v : Term ∅
      e~>*final-value : e ~>* v
      v∈V⟦τ⟧ : v ∈V⟦ τ ⟧

mutual
  v-fold : ∀{e τ} → e ∈V'⟦ τ ⟧ → e ∈V⟦ τ ⟧
  v-fold {True} {TBool} tt = v-bool-true
  v-fold {False} {TBool} tt = v-bool-false
  v-fold {Pair e₁ e₂} {TProd τ₁ τ₂} (e₁∈V' , e₂∈V') = v-pair (v-fold e₁∈V') (v-fold e₂∈V')
  v-fold {ƛ x ττ e} {τ ⇒ τ'} (τ≡ττ , body-valid) rewrite τ≡ττ =
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

V-val : ∀ {e τ} → e ∈V⟦ τ ⟧ → e val
V-val v-bool-true = true-val
V-val v-bool-false = false-val
V-val (v-pair p₁ p₂) = prod-val (V-val p₁) (V-val p₂)
V-val (v-abs _) = abs-val

V⇒E : ∀ e {τ} → e ∈V⟦ τ ⟧ → e ∈E⟦ τ ⟧
V⇒E e e∈V⟦τ⟧ = E-fold e kleene-z e∈V⟦τ⟧

record _∈G⟦_⟧ {w} (γ : Substs w) (Γ : Context w) : Set where
  field
    apply-defn-G : ∀ x → γ(x) ∈V⟦ Γ(x) ⟧

open _∈G⟦_⟧

infix 4 _⊨_∈_

_⊨_∈_ : ∀ {w} → Context w → Term w → Type → Set
Γ ⊨ e ∈ τ = ∀ γ → γ ∈G⟦ Γ ⟧ → subst∅ γ e ∈E⟦ τ ⟧

apply-defn-⊨ : ∀{w Γ e τ} →
  Γ ⊨ e ∈ τ →
  (γ : Substs w) → γ ∈G⟦ Γ ⟧ → subst∅ γ e ∈E⟦ τ ⟧
apply-defn-⊨ = id

basic-thm : ∀{w} {Γ : Context w} {e τ} → Γ ⊢ e ∈ τ → Γ ⊨ e ∈ τ
basic-thm {_} {Γ} {V x} {τ} (typ-var Γ[x]≡τ) γ γ∈G⟦Γ⟧ = V⇒E v v∈V⟦τ⟧
  where
    v = γ(x)

    -- not really sure why this needs to be its own function
    rewrite-Γ[x]≡τ : ∀ v → v ∈V⟦ Γ x ⟧ → v ∈V⟦ τ ⟧
    rewrite-Γ[x]≡τ v t rewrite Γ[x]≡τ = t

    v∈V⟦τ⟧ : v ∈V⟦ τ ⟧
    v∈V⟦τ⟧ = rewrite-Γ[x]≡τ v (apply-defn-G γ∈G⟦Γ⟧ x)
basic-thm typ-true γ γ∈G⟦Γ⟧ = V⇒E True v-bool-true
basic-thm typ-false γ γ∈G⟦Γ⟧ = V⇒E False v-bool-false
basic-thm {_} {Γ} {if e then e₁ else e₂} {τ}
  (typ-if Γ⊢e∈Bool Γ⊢e₁∈τ Γ⊢e₂∈τ) γ γ∈G⟦Γ⟧ = {! !}
  where
    Γ⊨e∈Bool : Γ ⊨ e ∈ TBool
    Γ⊨e∈Bool = basic-thm Γ⊢e∈Bool

    --e-final = .value apply-defn-⊨
basic-thm (typ-prod Γ⊢e∈τ Γ⊢e∈τ₁) γ γ∈G⟦Γ⟧ = {! !}
basic-thm (typ-prj₁ Γ⊢e∈τ) γ γ∈G⟦Γ⟧ = {! !}
basic-thm (typ-prj₂ Γ⊢e∈τ) γ γ∈G⟦Γ⟧ = {! !}
basic-thm (typ-abs Γ⊢e∈τ) γ γ∈G⟦Γ⟧ = {! !}
basic-thm (typ-app Γ⊢e∈τ Γ⊢e∈τ₁) γ γ∈G⟦Γ⟧ = {! !}

push-subst-if : ∀ {w} (γ : Substs w) {e e₁ e₂} →
  subst∅ γ (if e then e₁ else e₂) ≡
  if subst∅ γ e then subst∅ γ e₁ else subst∅ γ e₂
push-subst-if γ = refl
