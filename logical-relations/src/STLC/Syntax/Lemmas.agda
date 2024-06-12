module STLC.Syntax.Lemmas where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Relation.Nullary.Decidable hiding (True; False)
open import Function

plugi/weakenUnder : ∀{n} i → (t : Term n) → (e : Term n) → plugi i t (weakenUnder i e) ≡ e
plugi/weakenUnder i t (V x) = {!!}
  where
    open ≡-Reasoning

    {-
    lemma : (p : Dec (i ≤ x)) → (i ≤? x) ≡ p → plugi i t (weakenUnder i (V x)) ≡ V x
    lemma p@(true because _) i≤?x≡true = begin
        plug t (weakenUnder i (V x))
      ≡⟨⟩
        plug t (V (weakenUnderV x (i ≤? x)))
      ≡⟨ cong (plug t ∘ V ∘ weakenUnderV x) i≤?x≡true ⟩
        plug t (V (weakenUnderV x p))
      ≡⟨⟩
        plug t (V (suc x))
      ≡⟨⟩
        V x
      ∎
    lemma p@(false because ¬i≤x) i≤?x≡false = begin
        plug t (weakenUnder i (V x))
      ≡⟨⟩
        plug t (V (weakenUnderV x (i ≤? x)))
      ≡⟨ cong (plug t ∘ V ∘ weakenUnderV x) i≤?x≡false ⟩
        plug t (V (weakenUnderV x p))
      ≡⟨⟩
        plug t (V (inject₁ x))
      ≡⟨ {!!} ⟩
        V x
      ∎
    -}
plugi/weakenUnder i t True = refl
plugi/weakenUnder i t False = refl
plugi/weakenUnder i t (if e then e₁ else e₂)
  rewrite plugi/weakenUnder i t e
  rewrite plugi/weakenUnder i t e₁
  rewrite plugi/weakenUnder i t e₂ = refl
plugi/weakenUnder i t (Pair e₁ e₂)
  rewrite plugi/weakenUnder i t e₁
  rewrite plugi/weakenUnder i t e₂ = refl
plugi/weakenUnder i t (prj₁ e)
  rewrite plugi/weakenUnder i t e = refl
plugi/weakenUnder i t (prj₂ e)
  rewrite plugi/weakenUnder i t e = refl
plugi/weakenUnder i t (ƛ τ e)
  rewrite plugi/weakenUnder (suc i) (weaken t) e = {! !}
plugi/weakenUnder i t (e₁ ∙ e₂)
  rewrite plugi/weakenUnder i t e₁
  rewrite plugi/weakenUnder i t e₂ = refl

plug/subst : ∀{n m} →
  (t : Term m) → (γ : Context (Term m) n) → (e : Term (suc n)) →
  plug t (subst (weakenSubst γ) e) ≡ subst (t ~& γ) e
plug/subst t γ (V zero) = refl
plug/subst t γ (V (suc i)) = begin
    plug t (subst (weakenSubst γ) (V (suc i)))
  ≡⟨⟩
    plug t (weaken (γ i))
  ≡⟨ plugi/weakenUnder zero t (γ i) ⟩
    γ i
  ∎
  where
    open ≡-Reasoning
plug/subst t γ True = refl
plug/subst t γ False = refl
plug/subst t γ (if e then e₁ else e₂)
  rewrite plug/subst t γ e
  rewrite plug/subst t γ e₁
  rewrite plug/subst t γ e₂ = refl
plug/subst t γ (Pair e₁ e₂)
  rewrite plug/subst t γ e₁
  rewrite plug/subst t γ e₂ = refl
plug/subst t γ (prj₁ e) rewrite plug/subst t γ e = refl
plug/subst t γ (prj₂ e) rewrite plug/subst t γ e = refl
plug/subst t γ (ƛ τ e) = begin
    plug t (subst (weakenSubst γ) (ƛ τ e))
  ≡⟨⟩
    plug t (ƛ τ (subst (weakenSubst (weakenSubst γ)) e))
  -- WRONG
  ≡⟨ {!!} ⟩
    ƛ τ (plug (weaken t) (subst (weakenSubst (weakenSubst γ)) e))
  ≡⟨ cong (ƛ τ) {! (plug/subst (weaken t) (weakenSubst γ) e) !} ⟩
    ƛ τ (subst (weakenSubst (t ~& γ)) e)
  ≡⟨⟩
    subst (t ~& γ) (ƛ τ e)
  ∎
  where
    open ≡-Reasoning
plug/subst t γ (e₁ ∙ e₂)
  rewrite plug/subst t γ e₁
  rewrite plug/subst t γ e₂ = refl
