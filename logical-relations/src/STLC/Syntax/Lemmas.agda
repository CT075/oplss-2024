module STLC.Syntax.Lemmas where

open import STLC.Syntax

open import Data.Product
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Fin.Util
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Relation.Nullary.Decidable hiding (True; False)
open import Relation.Nullary.Negation using (contradiction)
open import Function

subst-extensionality : ∀{n m} {f g : Fin n → Term m} →
  (∀ x → f x ≡ g x) → ∀ e → subst f e ≡ subst g e
subst-extensionality {_} {_} {f} {g} fx≡gx (V x) = fx≡gx x
subst-extensionality fx≡gx True = refl
subst-extensionality fx≡gx False = refl
subst-extensionality fx≡gx (if e then e₁ else e₂)
  rewrite subst-extensionality fx≡gx e
  rewrite subst-extensionality fx≡gx e₁
  rewrite subst-extensionality fx≡gx e₂ = refl
subst-extensionality fx≡gx (Pair e₁ e₂)
  rewrite subst-extensionality fx≡gx e₁
  rewrite subst-extensionality fx≡gx e₂ = refl
subst-extensionality fx≡gx (prj₁ e) = cong prj₁ (subst-extensionality fx≡gx e)
subst-extensionality fx≡gx (prj₂ e) = cong prj₂ (subst-extensionality fx≡gx e)
subst-extensionality {_} {_} {f} {g} fx≡gx (ƛ τ e) =
    cong (ƛ τ) (subst-extensionality wk-fx≡wk-gx e)
  where
    wk-fx≡wk-gx : ∀ x → weakenSubst f x ≡ weakenSubst g x
    wk-fx≡wk-gx zero = refl
    wk-fx≡wk-gx (suc i) = cong weaken (fx≡gx i)
subst-extensionality fx≡gx (e₁ ∙ e₂)
  rewrite subst-extensionality fx≡gx e₁
  rewrite subst-extensionality fx≡gx e₂ = refl

weakenSubst/plugVar : ∀{n} i (t : Term n) x →
  weakenSubst (plugVar i t) x ≡ plugVar (suc i) (weaken t) x
weakenSubst/plugVar i t zero = refl
weakenSubst/plugVar i t (suc j) = lemma (i ≟ j) refl
  where
    open ≡-Reasoning

    lemma : (p : Dec (i ≡ j)) → p ≡ (i ≟ j) →
      weakenSubst (plugVar i t) (suc j) ≡ plugVar (suc i) (weaken t) (suc j)
    lemma (yes i≡j) p≡i≟j = trans fw (sym bw)
      where
        fw : weakenSubst (plugVar i t) (suc j) ≡ weaken t
        fw = begin
            weakenSubst (plugVar i t) (suc j)
          ≡⟨⟩
            weaken (plugVar i t j)
          ≡⟨⟩
            weaken (plugV i t j (i ≟ j))
          ≡⟨ cong (weaken ∘ plugV i t j) (sym p≡i≟j) ⟩
            weaken (plugV i t j (yes i≡j))
          ≡⟨⟩
            weaken t
          ∎

        -- This is such a messy way to prove this, but I couldn't figure out a
        -- better way.
        sublemma : (p : Dec (suc i ≡ suc j)) →
          plugV (suc i) (weaken t) (suc j) p ≡ weaken t
        sublemma (yes si≡sj) = refl
        sublemma (no si≢sj) = contradiction (cong suc i≡j) si≢sj

        bw : plugVar (suc i) (weaken t) (suc j) ≡ weaken t
        bw = begin
            plugVar (suc i) (weaken t) (suc j)
          ≡⟨⟩
            plugV (suc i) (weaken t) (suc j) (suc i ≟ suc j)
          ≡⟨ sublemma (suc i ≟ suc j) ⟩
            weaken t
          ∎
    lemma (no i≢j) p≡i≟j = trans fw (sym bw)
      where
        fw : weakenSubst (plugVar i t) (suc j) ≡ V (suc (punchOut i≢j))
        fw = begin
            weakenSubst (plugVar i t) (suc j)
          ≡⟨⟩
            weaken (plugVar i t j)
          ≡⟨⟩
            weaken (plugV i t j (i ≟ j))
          ≡⟨ cong (weaken ∘ plugV i t j) (sym p≡i≟j) ⟩
            weaken (plugV i t j (no i≢j))
          ≡⟨⟩
            weaken (V (punchOut i≢j))
          ≡⟨⟩
            V (suc (punchOut i≢j))
          ∎

        sublemma : (p : Dec (suc i ≡ suc j)) →
          plugV (suc i) (weaken t) (suc j) p ≡ V (suc (punchOut i≢j))
        sublemma (yes si≡sj) = contradiction (suc-injective si≡sj) i≢j
        sublemma (no si≢sj) = begin
            plugV (suc i) (weaken t) (suc j) (no si≢sj)
          ≡⟨⟩
            V (punchOut si≢sj)
          ≡⟨ cong V (comm-punchOut/suc i≢j si≢sj) ⟩
            V (suc (punchOut i≢j))
          ∎

        bw : plugVar (suc i) (weaken t) (suc j) ≡ V (suc (punchOut i≢j))
        bw = begin
            plugVar (suc i) (weaken t) (suc j)
          ≡⟨⟩
            plugV (suc i) (weaken t) (suc j) (suc i ≟ suc j)
          ≡⟨ sublemma (suc i ≟ suc j) ⟩
            V (suc (punchOut i≢j))
          ∎

plugi/weakenUnder : ∀{n} i → (t : Term n) → (e : Term n) → plugi i t (weakenUnder i e) ≡ e
plugi/weakenUnder i t (V x) = begin
    plugi i t (weakenUnder i (V x))
  ≡⟨⟩
    plugi i t (V (punchIn i x))
  ≡⟨⟩
    plugV i t (punchIn i x) (i ≟ punchIn i x)
  ≡⟨ lemma (i ≟ punchIn i x) refl ⟩
    V x
  ∎
  where
    open ≡-Reasoning

    lemma : (p : Dec (i ≡ punchIn i x)) →
      (i ≟ punchIn i x) ≡ p →
      plugV i t (punchIn i x) (i ≟ punchIn i x) ≡ V x
    lemma p@(yes i≡y) p≡i≟x = contradiction i≡y (≢-sym (punchInᵢ≢i i x))
    lemma p@(no i≢y) p≡i≟x = begin
        plugV i t (punchIn i x) (i ≟ punchIn i x)
      ≡⟨ cong (plugV i t (punchIn i x)) p≡i≟x ⟩
        plugV i t (punchIn i x) p
      ≡⟨⟩
        V (punchOut i≢y)
      ≡⟨ cong V (punchOut-punchIn i) ⟩
        V x
      ∎
plugi/weakenUnder i t True = refl
plugi/weakenUnder i t False = refl
plugi/weakenUnder i t (if e then e₁ else e₂)
  rewrite plugi/weakenUnder i t e
  rewrite plugi/weakenUnder i t e₁
  rewrite plugi/weakenUnder i t e₂ = refl
plugi/weakenUnder i t (Pair e₁ e₂)
  rewrite plugi/weakenUnder i t e₁
  rewrite plugi/weakenUnder i t e₂ = refl
plugi/weakenUnder i t (prj₁ e) = cong prj₁ (plugi/weakenUnder i t e)
plugi/weakenUnder i t (prj₂ e) = cong prj₂ (plugi/weakenUnder i t e)
plugi/weakenUnder i t (ƛ τ e) = begin
    plugi i t (weakenUnder i (ƛ τ e))
  ≡⟨⟩
    plugi i t (ƛ τ (weakenUnder (suc i) e))
  ≡⟨⟩
    ƛ τ (subst (weakenSubst (plugVar i t)) (weakenUnder (suc i) e))
  ≡⟨ cong (ƛ τ) (subst-extensionality (weakenSubst/plugVar i t) (weakenUnder (suc i) e)) ⟩
    ƛ τ (plugi (suc i) (weaken t) (weakenUnder (suc i) e))
  ≡⟨ cong (ƛ τ) (plugi/weakenUnder (suc i) (weaken t) e) ⟩
    ƛ τ e
  ∎
  where
    open ≡-Reasoning
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
plug/subst t γ (prj₁ e) = cong prj₁ (plug/subst t γ e)
plug/subst t γ (prj₂ e) = cong prj₂ (plug/subst t γ e)
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
