module STLC.Syntax where

open import Data.Nat using (ℕ)
open import Data.Var

data Type : Set where
  TBool : Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type

data Term : Set where
  V : Var → Term
