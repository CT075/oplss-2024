open import Data.Binding

module STLC.Syntax.Lemmas {{_ : NomPa}} where

open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Effect.Applicative.Util

open import Data.Binding.Operations

open import STLC.Syntax

weakenSubst∅ : ∀{α : World} →
  (Name α → Term ∅) → (x : Binder) → (Name (x ◃ α) → Term (x ◃ ∅))
weakenSubst∅ f x n with exportᴺ n
... | inj₁ r = V r
... | inj₂ e = weaken ⊆-∅ (f e)

{-
plug∅ v (TrTerm.tr id-app (substKit V weaken) (TrKit.extEnv (substKit V weaken) x (mk γ zeroS)) e)
-}
