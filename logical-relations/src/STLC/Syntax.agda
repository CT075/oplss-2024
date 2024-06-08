open import Data.Binding

module STLC.Syntax {{_ : NomPa}} where

open import Effect.Functor
open import Effect.Applicative renaming
  (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Effect.Applicative.Util
open import Function hiding (_ˢ_)

open import Data.Binding.Operations

infix 19 _⇒_
infix 20 if_then_else_

data Type : Set where
  TBool : Type
  TProd : Type → Type → Type
  _⇒_ : Type → Type → Type

data Term (w : World) : Set where
  V : Name w → Term w
  True : Term w
  False : Term w
  if_then_else_ : Term w → Term w → Term w → Term w
  Pair : Term w → Term w → Term w
  prj₁ : Term w → Term w
  prj₂ : Term w → Term w
  ƛ : (b : Binder) → Type → Term (b ◃ w) → Term w
  _∙_ : Term w → Term w → Term w

-- TODO: Pouillard can apparently generate this programmatically, which would
-- be a neat exercise for later

module TrTerm
    {E : Set → Set} (E-app : Applicative E)
    {Env : World → World → Set} (trKit : TrKit Env (E ∘ Term)) where
  open Applicative E-app
  open TrKit trKit

  tr : ∀{α β} → Env α β → Term α → E (Term β)
  tr Δ (V x) = trName Δ x
  tr Δ True = pure True
  tr Δ False = pure False
  tr Δ (if e then e₁ else e₂) = if_then_else_ <$> tr Δ e <*> tr Δ e₁ <*> tr Δ e₂
  tr Δ (Pair e₁ e₂) = Pair <$> tr Δ e₁ <*> tr Δ e₂
  tr Δ (prj₁ e) = prj₁ <$> tr Δ e
  tr Δ (prj₂ e) = prj₂ <$> tr Δ e
  tr Δ (ƛ x τ e) = ƛ _ τ <$> tr (extEnv _ Δ) e
  tr Δ (e₁ ∙ e₂) = _∙_ <$> tr Δ e₁ <*> tr Δ e₂

open TrTerm

tr' : ∀ {E : Set → Set} (E-app : Applicative E)
        {Env : World → World → Set} (trKit : TrKit Env (E ∘ Name))
        {α β} → Env α β → Term α → E (Term β)
tr' E-app trKit = tr E-app (mapKit id (E-app <$> V) trKit)
  where open Applicative

weaken : ∀{α β} → α ⊆ β → Term α → Term β
weaken = tr' id-app coerceKit

subst : ∀{α β} → Supply β → (Name α → Term β) → Term α → Term β
subst s f = tr id-app (substKit V weaken) (mk f s)

weaken∅ : Term ∅ → ∀{α} → Term α
weaken∅ t = weaken ⊆-∅ t

subst∅ : ∀{α} → (Name α → Term ∅) → Term α → Term ∅
subst∅ = subst zeroS

plug : ∀{α : World} {x : Binder} → Supply α → Term α → Term (x ◃ α) → Term α
plug s t = subst s (exportWith t V)

plug∅ : ∀{x : Binder} → Term ∅ → Term (x ◃ ∅) → Term ∅
plug∅ = plug zeroS

subst∅Under : ∀{α : World} →
  (x : Binder) → (Name α → Term ∅) → Term (x ◃ α) → Term (zeroᴮ ◃ ∅)
subst∅Under x γ e =
  TrTerm.tr id-app (substKit V weaken)
    (TrKit.extEnv (substKit V weaken) x (mk γ (mkSupply b (b #∅))))
    e
  where
    b = zeroᴮ
