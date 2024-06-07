open import Data.Binding

module STLC.Syntax.Lemmas {{_ : NomPa}} where

open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Effect.Applicative.Util
open import Function

open import Data.Binding.Operations

open import STLC.Syntax

substUnder : ∀{α : World} →
  (Name α → Term ∅) → (x : Binder) → Term x
substUnder γ x =
    (exportWith (V (nameᴮ zeroS)) (weaken (⊆-# (_ᴮ 0) #∅)) ∘ trName)
  where
    open SubstEnv

{-
plug∅ v
  (TrTerm.tr id-app (substKit V weaken)
  (TrKit.extEnv (substKit V weaken) x (mk γ zeroS))
  e)

TrKit.extEnv (substKit V weaken) x (mk γ zeroS)
TrKit.extEnv (mk trName trBinder extEnv) x (mk γ zeroS)
extEnv (mk γ zeroS)
(mk (exportWith (V nameᴮ zeroS) (weaken (⊆-# (0 ̂̂̂ᴮ #∅)) ∘ trName)) (sucS zeroS))

tr id-app (substKit V weaken)
  (mk (exportWith (V nameᴮ zeroS) (weaken (⊆-# (0 ̂̂̂ᴮ #∅)) ∘ trName)) (sucS zeroS))
  e
-}
