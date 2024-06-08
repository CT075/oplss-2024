module STLC.Syntax where

open import Data.String
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

infix 19 _⇒_
infix 20 if_then_else_

World = List String

record Name (w : World) : Set where
  constructor mkName
  field
    name : String
    -- In fact, a value of type `name ∈ w` is equivalent to a member of
    -- `Fin (length w)` (this proof is the index of the given name in the list).
    -- So another way to view this technique is that we are annotating a
    -- standard De Bruijin index with a string name!
    name∈w : name ∈ w

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
  ƛ : (x : String) → Type → Term (x ∷ w) → Term w
  _∙_ : Term w → Term w → Term w

weaken : ∀{w} → (x : String) → Term w → Term (x ∷ w)
weaken _ (V (mkName n rest)) = V (mkName n (there rest))
weaken _ True = True
weaken _ False = False
weaken x (if e then e₁ else e₂) = if weaken x e then weaken x e₁ else weaken x e₂
weaken x (Pair e₁ e₂) = Pair (weaken x e₁) (weaken x e₂)
weaken x (prj₁ e) = prj₁ (weaken x e)
weaken x (prj₂ e) = prj₂ (weaken x e)
-- We need to pass some extra state parameter to know how many binders we're
-- underneath, but List.Membership is not good for this.
weaken x (ƛ x' τ e) = ƛ x' τ (weaken x e)
weaken x (e₁ ∙ e₂) = weaken x e₁ ∙ weaken x e₂

subst : ∀{w w'} → (Name w → Term w') → Term w → Term w'
subst f (V x) = f x
subst f True = True
subst f False = False
subst f (if e then e₁ else e₂) = if subst f e then subst f e₁ else subst f e₂
subst f (Pair e₁ e₂) = Pair (subst f e₁) (subst f e₂)
subst f (prj₁ e) = prj₁ (subst f e)
subst f (prj₂ e) = prj₂ (subst f e)
subst f (ƛ x τ e) = {! !}
subst f (e₁ ∙ e₂) = (subst f e₁ ∙ subst f e₂)
