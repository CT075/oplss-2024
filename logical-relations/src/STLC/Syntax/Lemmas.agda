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

plug/weakenUnder : ∀{n} i → (t : Term n) → (e : Term n) → plug t (weakenUnder i e) ≡ e
plug/weakenUnder i t (V x) = lemma (i ≤? x) refl
  where
    open ≡-Reasoning

    lemma : (p : Dec (i ≤ x)) → (i ≤? x) ≡ p → plug t (weakenUnder i (V x)) ≡ V x
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
plug/weakenUnder i t True = refl
plug/weakenUnder i t False = refl
plug/weakenUnder i t (if e then e₁ else e₂)
  rewrite plug/weakenUnder i t e
  rewrite plug/weakenUnder i t e₁
  rewrite plug/weakenUnder i t e₂ = refl
plug/weakenUnder i t (Pair e₁ e₂)
  rewrite plug/weakenUnder i t e₁
  rewrite plug/weakenUnder i t e₂ = refl
plug/weakenUnder i t (prj₁ e)
  rewrite plug/weakenUnder i t e = refl
plug/weakenUnder i t (prj₂ e)
  rewrite plug/weakenUnder i t e = refl
plug/weakenUnder i t (ƛ τ e)
  rewrite plug/weakenUnder (suc i) (weaken t) e = {! !}
plug/weakenUnder i t (e₁ ∙ e₂)
  rewrite plug/weakenUnder i t e₁
  rewrite plug/weakenUnder i t e₂ = refl

plug/subst : ∀{n m} →
  (t : Term m) → (γ : Context (Term m) n) → (e : Term (suc n)) →
  plug t (subst (weakenSubst γ) e) ≡ subst (t ~& γ) e
plug/subst t γ (V zero) = refl
plug/subst t γ (V (suc i)) = begin
    plug t (subst (weakenSubst γ) (V (suc i)))
  ≡⟨⟩
    plug t (weaken (γ i))
  ≡⟨ plug/weakenUnder _ t (γ i) ⟩
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
