module STLC.Soundness where

open import Data.Context

open import STLC.Syntax
open import STLC.Typing
open import STLC.Eval

record Val : Set where
  field
    t : Term
    is-val : t val

Substs = Ctx Val

data _∈G⟦_⟧ : Substs → Context → Set where
