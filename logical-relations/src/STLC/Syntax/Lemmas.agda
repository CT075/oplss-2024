module STLC.Syntax.Lemmas where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Function

mutual
  weakenSubst/id : ∀{n} → (γ : Fin n → Term n) →
    (∀ e → subst γ e ≡ e) →
    (∀ e → subst (weakenSubst γ) e ≡ e)
  weakenSubst/id γ f (V zero) = refl
  weakenSubst/id γ f (V (suc i)) =
    begin
      subst (weakenSubst γ) (V (suc i))
    ≡⟨⟩
      weaken (γ i)
    ≡⟨⟩
      weaken (subst γ (V i))
    ≡⟨ {! f (V i) !} ⟩
      V (suc i)
    ∎
    where
      open ≡-Reasoning
      foo : weaken (subst γ (V i)) ≡ V (suc i)
      foo = {! f (V i) !}
  weakenSubst/id γ f True = refl
  weakenSubst/id γ f False = refl
  weakenSubst/id γ f (if e then e₁ else e₂)
    rewrite weakenSubst/id γ f e
    rewrite weakenSubst/id γ f e₁
    rewrite weakenSubst/id γ f e₂ = refl
  weakenSubst/id γ f (Pair e₁ e₂)
    rewrite weakenSubst/id γ f e₁
    rewrite weakenSubst/id γ f e₂ = refl
  weakenSubst/id γ f (prj₁ e) rewrite weakenSubst/id γ f e = refl
  weakenSubst/id γ f (prj₂ e) rewrite weakenSubst/id γ f e = refl
  weakenSubst/id γ f (ƛ τ e) = result
    where
      foo : subst (weakenSubst (weakenSubst γ)) e ≡ e
      foo = weakenSubst/id (weakenSubst γ) (weakenSubst/id γ f) e

      result : ƛ τ (subst (weakenSubst (weakenSubst γ)) e) ≡ ƛ τ e
      result rewrite foo = refl
  weakenSubst/id γ f (e₁ ∙ e₂)
    rewrite weakenSubst/id γ f e₁
    rewrite weakenSubst/id γ f e₂ = refl

  subst/zero : (γ : Fin zero → Term zero) → (e : Term zero) → subst γ e ≡ e
  subst/zero γ True = refl
  subst/zero γ False = refl
  subst/zero γ (if e then e₁ else e₂)
    rewrite subst/zero γ e
    rewrite subst/zero γ e₁
    rewrite subst/zero γ e₂ = refl
  subst/zero γ (Pair e₁ e₂)
    rewrite subst/zero γ e₁
    rewrite subst/zero γ e₂ = refl
  subst/zero γ (prj₁ e) rewrite subst/zero γ e = refl
  subst/zero γ (prj₂ e) rewrite subst/zero γ e = refl
  subst/zero γ (ƛ τ e) = {! !}
  subst/zero γ (e₁ ∙ e₂)
    rewrite subst/zero γ e₁
    rewrite subst/zero γ e₂ = refl

{-
∘~/defn : ∀{n m} →
  (γ₁ : Context (Term zero) n) → (γ₂ : Context (Term zero) m) →
  (e : Term (n + m)) →
  subst (γ₁ ~∘ γ₂) e ≡ subst γ₂ (subst (weakenSubst* m γ₁) e)
∘~/defn {zero} γ₁ γ₂ e =
  begin
    subst (γ₁ ~∘ γ₂) e
  ≡⟨⟩
    subst γ₂ e
  ≡⟨ {!!} ⟩
    {!!}
  ∎
  where
    open ≡-Reasoning
-}
