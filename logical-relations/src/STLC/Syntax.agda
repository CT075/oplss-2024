module STLC.Syntax where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin hiding (lift)
import Data.Vec as Vec
open import Data.Vec using (_∷_; []) public
import Data.Fin.Substitution as S
open import Data.Fin.Substitution.Lemmas

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

Ctx : ∀ {ℓ} (T : Set ℓ) → ℕ → Set ℓ
Ctx = Vec.Vec

infix 10 _[_]

_[_] : ∀{ℓ} {T : Set ℓ} {n} → Ctx T n → Fin n → T
[] [ () ]
(x ∷ _) [ zero ] = x
(_ ∷ Γ) [ suc i ] = Γ [ i ]

module TermApp {T : ℕ → Set} (l : S.Lift T Term) where
  infix 8 _/_

  open S.Lift l

  _/_ : ∀{m n} → Term m → S.Sub T m n → Term n
  V x / σ = lift (σ [ x ])
  True / σ = True
  False / σ = False
  if e then e₁ else e₂ / σ = if (e / σ) then (e₁ / σ) else (e₂ / σ)
  Pair e₁ e₂ / σ = Pair (e₁ / σ) (e₂ / σ)
  prj₁ e / σ = prj₁ (e / σ)
  prj₂ e / σ = prj₂ (e / σ)
  ƛ τ e / σ = ƛ τ (e / σ ↑)
  (e₁ ∙ e₂) / σ = (e₁ / σ) ∙ (e₂ / σ)

termSubst : S.TermSubst Term
termSubst = record {var = V; app = _/_}
  where
    open TermApp

termLift = S.TermSubst.termLift termSubst
varSubst = S.TermSubst.varLift termSubst

open S.Lift termLift using (sub ; _↑ ; weaken) public
open TermApp termLift using (_/_) public

plug : ∀{n} → Term n → Term (suc n) → Term n
plug t e = e / (sub t)
