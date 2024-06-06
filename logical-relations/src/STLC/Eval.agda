open import Data.Binding

module STLC.Eval {{_ : NomPa}} where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)

open import STLC.Syntax

infix 5 _val

data _val : Term ∅ → Set where
  true-val : True val
  false-val : False val
  prod-val : ∀{e₁ e₂} → e₁ val → e₂ val → (Pair e₁ e₂) val
  abs-val : ∀{τ x e} → ƛ τ x e val

val-decidable : (e : Term ∅) → Dec (e val)
val-decidable True = yes true-val
val-decidable False = yes false-val
val-decidable (Pair e₁ e₂) with val-decidable e₁ , val-decidable e₂
... | yes e₁val , yes e₂val = yes (prod-val e₁val e₂val)
... | no ¬e₁val , yes e₂val = no (λ { (prod-val e₁val _) → ¬e₁val e₁val })
... | yes e₁val , no ¬e₂val = no (λ { (prod-val _ e₂val) → ¬e₂val e₂val })
... | no ¬e₁val , no ¬e₂val = no (λ { (prod-val e₁val _) → ¬e₁val e₁val })
val-decidable (ƛ x τ e) = yes abs-val
val-decidable (V _) = no (λ ())
val-decidable (if _ then _ else _) = no (λ ())
val-decidable (prj₁ _) = no (λ ())
val-decidable (prj₂ _) = no (λ ())
val-decidable (_ ∙ _) = no (λ ())

infix 4 _~>_

data _~>_ : Term ∅ → Term ∅ → Set where
  step-if : ∀{e e' e₁ e₂} →
    e ~> e' →
    if e then e₁ else e₂ ~> if e' then e₁ else e₂
  step-then : ∀{e₁ e₂} → if True then e₁ else e₂ ~> e₁
  step-else : ∀{e₁ e₂} → if False then e₁ else e₂ ~> e₂
  step-prod₁ : ∀{e₁ e₁' e₂} → e₁ ~> e₁' → Pair e₁ e₂ ~> Pair e₁' e₂
  step-prod₂ : ∀{e₁ e₂ e₂'} → e₁ val → e₂ ~> e₂' → Pair e₁ e₂ ~> Pair e₁ e₂'
  step-prj₁-mid : ∀{e e'} → e ~> e' → prj₁ e ~> prj₁ e'
  step-prj₁-app : ∀{e₁ e₂} → (Pair e₁ e₂) val → prj₁ (Pair e₁ e₂) ~> e₁
  step-prj₂-mid : ∀{e e'} → e ~> e' → prj₂ e ~> prj₂ e'
  step-prj₂-app : ∀{e₁ e₂} → (Pair e₁ e₂) val → prj₂ (Pair e₁ e₂) ~> e₂
  step-app₁ : ∀{e₁ e₁' e₂} → e₁ ~> e₁' → e₁ ∙ e₂ ~> e₁' ∙ e₂
  step-app₂ : ∀{τ x e₁ e₂ e₂'} → e₂ ~> e₂' → ƛ x τ e₁ ∙ e₂ ~> ƛ x τ e₁ ∙ e₂'
  step-app : ∀{τ x e₁ e₂ e} → e ≡ plug∅ e₂ e₁ → e₂ val → ƛ x τ e₁ ∙ e₂ ~> e

infix 4 _~>*_

data _~>*_ : Term ∅ → Term ∅ → Set where
  kleene-z : ∀{e} → e ~>* e
  kleene-n : ∀{e e' e''} → e ~> e' → e' ~>* e'' → e ~>* e''

kleene-append : ∀{e₁ e₂ e₃} → e₁ ~>* e₂ → e₂ ~>* e₃ → e₁ ~>* e₃
kleene-append kleene-z e₂~>*e₃ = e₂~>*e₃
kleene-append (kleene-n e₁~>e e~>*e₂) e₂~>*e₃ =
  kleene-n e₁~>e (kleene-append e~>*e₂ e₂~>*e₃)

iter-step : ∀{e₁ e₃ : Term ∅} {F : Term ∅ → Term ∅} →
  (∀{e e'} → e ~> e' → F e ~> F e') →
  e₁ ~>* e₃ → F e₁ ~>* F e₃
iter-step f kleene-z = kleene-z
iter-step f (kleene-n e₁~>e₂ e₂~>*e₃) = kleene-n (f e₁~>e₂) (iter-step f e₂~>*e₃)

step-if* : ∀{e e' e₁ e₂} →
  e ~>* e' →
  if e then e₁ else e₂ ~>* if e' then e₁ else e₂
step-if* = iter-step step-if

step-prod₁* : ∀{e₁ e₁' e₂} → e₁ ~>* e₁' → Pair e₁ e₂ ~>* Pair e₁' e₂
step-prod₁* = iter-step step-prod₁

step-prod₂* : ∀{v₁ e₂ e₂'} → v₁ val → e₂ ~>* e₂' → Pair v₁ e₂ ~>* Pair v₁ e₂'
step-prod₂* v₁-val = iter-step (step-prod₂ v₁-val)

reduces : Term ∅ → Set
reduces e = ∃[ e' ](e ~> e')

irred : Term ∅ → Set
irred e = ¬ (reduces e)

val-irred : ∀{e} → e val → irred e
val-irred true-val ()
val-irred false-val ()
val-irred abs-val ()
val-irred (prod-val e₁val e₂val) (_ , step-prod₁ e₁~>e₁') = val-irred e₁val (_ , e₁~>e₁')
val-irred (prod-val e₁val e₂val) (_ , step-prod₂ _ e₂~>e₂') = val-irred e₂val (_ , e₂~>e₂')

reduces-decidable : (e : Term ∅) → Dec (reduces e)
reduces-decidable (V v) = no (λ ())
reduces-decidable True = no (λ ())
reduces-decidable False = no (λ ())
reduces-decidable (if e then e₁ else e₂) with reduces-decidable e
... | yes (e' , e~>e') = yes (if e' then e₁ else e₂ , step-if e~>e')
... | no ¬e~> with e
...   | True = yes (e₁ , step-then)
...   | False = yes (e₂ , step-else)
...   | V v = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | if _ then _ else _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | Pair _ _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | prj₁ _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | prj₂ _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | ƛ _ _ _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
...   | _ ∙ _ = no (λ { (if e' then _ else _ , step-if e~>) → ¬e~> (e' , e~>) })
reduces-decidable (Pair e₁ e₂) with reduces-decidable e₁
... | yes (e₁' , e₁~>e₁') = yes (Pair e₁' e₂ , step-prod₁ e₁~>e₁')
... | no ¬e₁~> with val-decidable e₁ , reduces-decidable e₂
...   | yes e₁val , yes (e₂' , e₂~>e₂') = yes (Pair e₁ e₂' , step-prod₂ e₁val e₂~>e₂')
...   | yes e₁val , no ¬e₂~> = no (λ
        { (Pair e₁' e₂ , step-prod₁ e₁~>) → ¬e₁~> (e₁' , e₁~>)
        ; (Pair e₁ e₂' , step-prod₂ e₁val' e₂~>) → ¬e₂~> (e₂' , e₂~>)
        })
...   | no ¬e₁val , yes (e₂' , e₂~>e₂') = no (λ
        { (Pair e₁' e₂ , step-prod₁ e₁~>) → ¬e₁~> (e₁' , e₁~>)
        ; (Pair e₁ e₂' , step-prod₂ e₁val e₂~>) → ¬e₁val e₁val
        })
...   | no ¬e₁val , no ¬e₂~> = no (λ
        { (Pair e₁' e₂ , step-prod₁ e₁~>) → ¬e₁~> (e₁' , e₁~>)
        ; (Pair e₁ e₂' , step-prod₂ e₁val e₂~>) → ¬e₂~> (e₂' , e₂~>)
        })
reduces-decidable (prj₁ e) with reduces-decidable e
... | yes (e' , e~>e') = yes (prj₁ e' , step-prj₁-mid e~>e')
... | no ¬e~> with e
...   | V v = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | True = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | False = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | if _ then _ else _ = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | prj₁ _ = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | prj₂ _ = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | ƛ _ _ _ = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | _ ∙ _ = no (λ { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)})
...   | Pair e₁ e₂ with val-decidable (Pair e₁ e₂)
...     | yes e-val = yes (e₁ , step-prj₁-app e-val)
...     | no ¬e-val = no (λ
          { (prj₁ e' , step-prj₁-mid e~>) → ¬e~> (e' , e~>)
          ; (_ , step-prj₁-app e-val) → ¬e-val e-val
          })
reduces-decidable (prj₂ e) with reduces-decidable e
... | yes (e' , e~>e') = yes (prj₂ e' , step-prj₂-mid e~>e')
... | no ¬e~> with e
...   | V v = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | True = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | False = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | if _ then _ else _ = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | prj₁ _ = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | prj₂ _ = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | ƛ _ _ _ = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | _ ∙ _ = no (λ { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)})
...   | Pair e₁ e₂ with val-decidable (Pair e₁ e₂)
...     | yes e-val = yes (e₂ , step-prj₂-app e-val)
...     | no ¬e-val = no (λ
          { (prj₂ e' , step-prj₂-mid e~>) → ¬e~> (e' , e~>)
          ; (_ , step-prj₂-app e-val) → ¬e-val e-val
          })
reduces-decidable (ƛ x τ e) = no (λ ())
reduces-decidable (e₁ ∙ e₂) with reduces-decidable e₁
... | yes (e₁' , e₁~>e₁') = yes (e₁' ∙ e₂ , step-app₁ e₁~>e₁')
... | no ¬e₁~> with e₁
...   | V _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | True = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | False = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | if _ then _ else _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | Pair _ _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | prj₁ _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | prj₂ _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | _ ∙ _ = no (λ { (e₁' ∙ e₂ , step-app₁ e₁~>) → ¬e₁~> (e₁' , e₁~>) })
...   | ƛ x τ e with reduces-decidable e₂
...     | yes (e₂' , e₂~>e₂') = yes (ƛ x τ e ∙ e₂' , step-app₂ e₂~>e₂')
...     | no ¬e₂~> with val-decidable e₂
...       | yes e₂val = yes (plug∅ e₂ e , step-app refl e₂val)
...       | no ¬e₂val = no (λ
            { (e₁ ∙ e₂' , step-app₂ e₂~>) → ¬e₂~> (e₂' , e₂~>)
            ; (e[e₂/x] , step-app _ e₂val) → ¬e₂val (e₂val)
            })
