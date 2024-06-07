open import Data.Binding

module STLC.Syntax.Lemmas {{_ : NomPa}} where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Effect.Applicative.Util
open import Function

open import Data.Binding.Operations

open import STLC.Syntax

subst∅Under : ∀{α : World} →
  (Name α → Term ∅) → (x : Binder) → Term (x ◃ α) → ∃[ b ] (Term (b ◃ ∅))
subst∅Under γ x e =
  b ,
  (TrTerm.tr id-app (substKit V weaken)
    (TrKit.extEnv (substKit V weaken) x (mk γ (mkSupply b (b #∅))))
    e)
  where
    b = zeroᴮ

foo : ∀{α : World} {x τ e} → (γ : Name α → Term ∅) →
  --∃[ e' ](e ~>* e' × e' ∈V'⟦ τ ⟧)
  ∃[ b ](subst∅ γ (ƛ x τ e) ≡ ƛ x τ (subst∅Under γ x e))
foo γ = zeroᴮ , refl
