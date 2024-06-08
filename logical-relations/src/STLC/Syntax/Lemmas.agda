module STLC.Syntax.Lemmas where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality hiding (subst)

plug-subst/extend : ∀{n} →
  (γ : Fin n → Term zero) → (t : Term zero) → (e : Term (suc n)) →
  plug t (subst (weakenSubst γ) e) ≡ subst (γ &~ t) e
plug-subst/extend γ t (V x) = {! !}
plug-subst/extend γ t True = refl
plug-subst/extend γ t False = refl
plug-subst/extend γ t (if e then e₁ else e₂)
  rewrite plug-subst/extend γ t e
  rewrite plug-subst/extend γ t e₁
  rewrite plug-subst/extend γ t e₂ = refl
plug-subst/extend γ t (Pair e₁ e₂)
  rewrite plug-subst/extend γ t e₁
  rewrite plug-subst/extend γ t e₂ = refl
plug-subst/extend γ t (prj₁ e) rewrite plug-subst/extend γ t e = refl
plug-subst/extend γ t (prj₂ e) rewrite plug-subst/extend γ t e = refl
plug-subst/extend γ t (ƛ τ e) = {!!}
plug-subst/extend γ t (e₁ ∙ e₂)
  rewrite plug-subst/extend γ t e₁
  rewrite plug-subst/extend γ t e₂ = refl
