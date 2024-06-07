open import Data.Binding

module STLC.Syntax.Lemmas {{_ : NomPa}} where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Effect.Applicative.Util
open import Function

open import Data.Binding.Operations

open import STLC.Syntax

subst∅Under : ∀{α : World} →
  (Name α → Term ∅) → (x : Binder) → Term (x ◃ α) → Term (x ◃ ∅)
subst∅Under γ x =
  TrTerm.tr id-app (substKit V weaken)
    (TrKit.extEnv (substKit V weaken) x (mk γ (mkSupply _ (_ #∅))))

{-
foo : ∀{α : World} {x τ e} → (γ : Name α → Term ∅) →
  --∃[ e' ](e ~>* e' × e' ∈V'⟦ τ ⟧)
  ∃[ b ](subst∅ γ (ƛ x τ e) ≡ ƛ b τ (subst∅Under γ b e))
foo γ = zeroᴮ , refl
-}
