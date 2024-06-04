module STLC.Syntax where

open import Data.Var

infix 19 _⇒_

infix 20 if_then_else_

infix 5 _/Term_

data Type : Set where
  TBool : Type
  TProd : Type → Type → Type
  _⇒_ : Type → Type → Type

data Term : Set where
  V : Var → Term
  True : Term
  False : Term
  if_then_else_ : Term → Term → Term → Term
  Pair : Term → Term → Term
  prj₁ : Term → Term
  prj₂ : Term → Term
  ƛ : Type → Term → Term
  _∙_ : Term → Term → Term

liftType : (Var → Var) → Type → Type
liftType _ τ = τ

liftTerm : (Var → Var) → Term → Term
liftTerm f (V v) = V (f v)
liftTerm f True = True
liftTerm f False = False
liftTerm f (if e then e₁ else e₂) =
  if (liftTerm f e) then (liftTerm f e₁) else (liftTerm f e₂)
liftTerm f (Pair e₁ e₂) = Pair (liftTerm f e₁) (liftTerm f e₂)
liftTerm f (prj₁ e) = prj₁ (liftTerm f e)
liftTerm f (prj₂ e) = prj₂ (liftTerm f e)
liftTerm f (ƛ τ e) = ƛ τ (liftTerm f e)
liftTerm f (e₁ ∙ e₂) = (liftTerm f e₁) ∙ (liftTerm f e₂)

instance
  TypeLift : Lift Type
  TypeLift = record {lift = liftType}

  TermLift : Lift Term
  TermLift = record {lift = liftTerm}

_/Term_ : (Var → Term) → Term → Term
_/Term_ f (V v) = f v
_/Term_ f True = True
_/Term_ f False = False
_/Term_ f (if e then e₁ else e₂) =
  if (f /Term e) then (f /Term e₁) else (f /Term e₂)
_/Term_ f (Pair e₁ e₂) = Pair (f /Term e₁) (f /Term e₂)
_/Term_ f (prj₁ e) = prj₁ (f /Term e)
_/Term_ f (prj₂ e) = prj₂ (f /Term e)
_/Term_ f (ƛ τ e) = ƛ τ (f /Term e)
_/Term_ f (e₁ ∙ e₂) = (f /Term e₁) ∙ (f /Term e₂)

open Subst (record {lift = TermLift; var = V; subst = _/Term_})
  using ()
  renaming
  ( openT to openTerm
  ; closeT to closeTerm
  ; wkT to wkTerm
  ; shiftT to shiftTerm
  ; renameT to renameTerm
  ; bindT to bindTerm
  )
  public
