module STLC.Eval where

open import STLC.Syntax

infix 5 _val

data _val : Term → Set where
  true-val : True val
  false-val : False val
  prod-val : ∀{e₁ e₂} → e₁ val → e₂ val → (e₁ , e₂) val
  abs-val : ∀{τ e} → ƛ τ e val

infix 4 _~>_

data _~>_ : Term → Term → Set where
  step-if : ∀{e e' e₁ e₂} →
    e ~> e' →
    if e then e₁ else e₂ ~> if e' then e₁ else e₂
  step-then : ∀{e₁ e₂} → if True then e₁ else e₂ ~> e₁
  step-else : ∀{e₁ e₂} → if False then e₁ else e₂ ~> e₂
  step-prod₁ : ∀{e₁ e₁' e₂} → e₁ ~> e₁' → (e₁ , e₂) ~> (e₁' , e₂)
  step-prod₂ : ∀{e₁ e₂ e₂'} → e₁ val → e₂ ~> e₂' → (e₁ , e₂) ~> (e₁ , e₂')
  step-abs₁ : ∀{e₁ e₁' e₂} → e₁ ~> e₁' → e₁ ∙ e₂ ~> e₁' ∙ e₂
  step-abs₂ : ∀{τ e₁ e₂ e₂'} → e₂ ~> e₂' → ƛ τ e₁ ∙ e₂ ~> ƛ τ e₁ ∙ e₂'
  step-app : ∀{τ e₁ e₂} → e₂ val → ƛ τ e₁ ∙ e₂ ~> bindTerm e₂ e₁
