module STLC.Syntax.Lemmas where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality
open import Function

plug/subst : ∀{n m} t (γ : Ctx (Term m) n) (e : Term (suc n)) →
  plug t (e / (γ ↑)) ≡ e / (t ∷ γ)
plug/subst t γ (V x) = {! !}
plug/subst t γ True = {! !}
plug/subst t γ False = {! !}
plug/subst t γ (if e then e₁ else e₂) = {! !}
plug/subst t γ (Pair e₁ e₂) = {! !}
plug/subst t γ (prj₁ e) = {! !}
plug/subst t γ (prj₂ e) = {! !}
plug/subst t γ (ƛ τ e) = begin
    plug t (ƛ τ e / (γ ↑))
  ≡⟨⟩
    plug t (ƛ τ (e / (γ ↑ ↑)))
  ≡⟨ {!!} ⟩
    ƛ τ (plug (weaken t) (e / (γ ↑ ↑)))
  ≡⟨ cong (ƛ τ) (plug/subst (weaken t) (γ ↑) e) ⟩
    ƛ τ (e / ((weaken t) ∷ (γ ↑)))
  ≡⟨ {!!} ⟩
    ƛ τ e / (t ∷ γ)
  ∎
  where
    open ≡-Reasoning
-- plug/subst (weaken t) (γ ↑) e
plug/subst t γ (e₁ ∙ e₂) = {! !}
