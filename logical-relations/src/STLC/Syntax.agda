module STLC.Syntax where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (true; false)
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Relation.Nullary.Decidable hiding (True; False)
open import Function

infix 19 _⇒_
infix 20 if_then_else_

data Type : Set where
  TBool : Type
  TProd : Type → Type → Type
  _⇒_ : Type → Type → Type

data Term (n : ℕ) : Set where
  V : Fin n → Term n
  True : Term n
  False : Term n
  if_then_else_ : Term n → Term n → Term n → Term n
  Pair : Term n → Term n → Term n
  prj₁ : Term n → Term n
  prj₂ : Term n → Term n
  ƛ : Type → Term (suc n) → Term n
  _∙_ : Term n → Term n → Term n

-- TODO: make this work dependently
Context : Set → ℕ → Set
Context T n = Fin n → T

infix 4 _&~_

nil : ∀{T} → Context T zero
nil ()

_&~_ : ∀{T n} → Context T n → T → Context T (suc n)
_&~_ Γ c zero = c
_&~_ Γ c (suc n) = Γ(n)

weakenUnder : ∀{n} → Fin (suc n) → Term n → Term (suc n)
weakenUnder i (V x) with i ≤? x
... | true because _ = V (suc x)
... | false because _ = V (inject₁ x)
weakenUnder i True = True
weakenUnder i False = False
weakenUnder i (if e then e₁ else e₂) = if weakenUnder i e then weakenUnder i e₁ else weakenUnder i e₂
weakenUnder i (Pair e₁ e₂) = Pair (weakenUnder i e₁) (weakenUnder i e₂)
weakenUnder i (prj₁ e) = prj₁ (weakenUnder i e)
weakenUnder i (prj₂ e) = prj₂ (weakenUnder i e)
weakenUnder i (ƛ τ e) = ƛ τ (weakenUnder (suc i) e)
weakenUnder i (e₁ ∙ e₂) = weakenUnder i e₁ ∙ weakenUnder i e₂

weaken : ∀{n} → Term n → Term (suc n)
weaken = weakenUnder zero

weaken* : ∀{n} m → Term n → Term (n + m)
weaken* {n} m rewrite +-comm n m = weaken*' m
  where
    weaken*' : ∀{n} m → Term n → Term (m + n)
    weaken*' zero e = e
    weaken*' (suc i) e = weaken (weaken*' i e)

weakenSubst : ∀{n m} → (Fin n → Term m) → Fin (suc n) → Term (suc m)
weakenSubst f zero = V zero
weakenSubst f (suc j) = weaken (f j)

subst : ∀{n m} → (Fin n → Term m) → Term n → Term m
subst f (V x) = f x
subst f True = True
subst f False = False
subst f (if e then e₁ else e₂) = if subst f e then subst f e₁ else subst f e₂
subst f (Pair e₁ e₂) = Pair (subst f e₁) (subst f e₂)
subst f (prj₁ e) = prj₁ (subst f e)
subst f (prj₂ e) = prj₂ (subst f e)
subst f (ƛ τ e) = ƛ τ (subst (weakenSubst f) e)
subst f (e₁ ∙ e₂) = (subst f e₁ ∙ subst f e₂)

plug : ∀{n} → Term zero → Term (suc n) → Term n
plug {n} t = subst f
  where
    f : Fin (suc n) → Term n
    f zero = weaken* n t
    f (suc i) = V i

compose-subst : ∀{a b c} →
  (Fin a → Term c) →
  (Fin b → Term c) →
  (Fin (a + b) → Term c)
compose-subst γ₁ γ₂ = {!!}
