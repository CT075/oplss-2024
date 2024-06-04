open import Data.Binding

module STLC.Syntax {{_ : NomPa}} where

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
  ƛ : Type → (b : Binder) → Term (b ◃ w) → Term w
  _∙_ : Term w → Term w → Term w
