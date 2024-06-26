module STLC.Soundness where

open import Data.List using ([]; _∷_)
open import Data.Product
open import Data.Empty
open import Data.Nat hiding (_/_)
open import Data.Fin
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Relation.Nullary using (yes; no)
open import Function

open import STLC.Syntax
open import STLC.Typing
open import STLC.Eval

Substs = Ctx (Term zero)

mutual
  _∈V'⟦_⟧ : Term zero → Type → Set
  True ∈V'⟦ TBool ⟧ = ⊤
  False ∈V'⟦ TBool ⟧ = ⊤
  (Pair e₁ e₂) ∈V'⟦ TProd τ₁ τ₂ ⟧ = e₁ ∈V'⟦ τ₁ ⟧ × e₂ ∈V'⟦ τ₂ ⟧
  (ƛ τ e) ∈V'⟦ τ₁ ⇒ τ₂ ⟧ = τ ≡ τ₁ × (∀ v → v ∈V'⟦ τ₁ ⟧ → plug v e ∈E'⟦ τ₂ ⟧)
  _ ∈V'⟦ _ ⟧ = ⊥

  -- This is actually a mistake; the true relation uses
  --   ∀ e' → e ~>* e' → irred e → e' ∈V'⟦ τ ⟧
  -- and I didn't notice until I'd done all this development with this
  -- definition. However, this definition using exists is actually stronger
  -- than the forall, provided a deterministic evaluation (which we have). See
  -- E-exists-forall below. Notably, in a total language, we also have the
  -- other direction, but we do not prove it here (because proving that this
  -- STLC is total either requires a stronger logical relation or something else
  -- quite complicated).
  _∈E'⟦_⟧ : Term zero → Type → Set
  e ∈E'⟦ τ ⟧ = ∃[ e' ](e ~>* e' × e' ∈V'⟦ τ ⟧)

mutual
  data _∈V⟦_⟧ : Term zero → Type → Set where
    v-bool-true : True ∈V⟦ TBool ⟧
    v-bool-false : False ∈V⟦ TBool ⟧
    v-pair : ∀{e₁ e₂ τ₁ τ₂} → e₁ ∈V⟦ τ₁ ⟧ → e₂ ∈V⟦ τ₂ ⟧ → Pair e₁ e₂ ∈V⟦ TProd τ₁ τ₂ ⟧
    v-abs : ∀{τ e τ'} → (∀ v → v ∈V'⟦ τ ⟧ → plug v e ∈E⟦ τ' ⟧) → ƛ τ e ∈V⟦ τ ⇒ τ' ⟧

  record _∈E⟦_⟧ (e : Term zero) (τ : Type) : Set where
    inductive
    constructor E-fold
    field
      v : Term zero
      e~>*v : e ~>* v
      v∈V⟦τ⟧ : v ∈V⟦ τ ⟧

mutual
  v-fold : ∀{e τ} → e ∈V'⟦ τ ⟧ → e ∈V⟦ τ ⟧
  v-fold {True} {TBool} tt = v-bool-true
  v-fold {False} {TBool} tt = v-bool-false
  v-fold {Pair e₁ e₂} {TProd τ₁ τ₂} (e₁∈V' , e₂∈V') = v-pair (v-fold e₁∈V') (v-fold e₂∈V')
  v-fold {ƛ ττ e} {τ ⇒ τ'} (τ≡ττ , body-valid) rewrite τ≡ττ =
    v-abs (λ v v∈V' → e-fold (body-valid v v∈V'))

  e-fold : ∀{e τ} → e ∈E'⟦ τ ⟧ → e ∈E⟦ τ ⟧
  e-fold (e' , e~>*e' , e'∈V') = E-fold e' e~>*e' (v-fold e'∈V')

mutual
  v-unfold : ∀{e τ} → e ∈V⟦ τ ⟧ → e ∈V'⟦ τ ⟧
  v-unfold v-bool-true = tt
  v-unfold v-bool-false = tt
  v-unfold (v-pair e₁∈V e₂∈V) = v-unfold e₁∈V , v-unfold e₂∈V
  v-unfold (v-abs body-valid) = refl , (λ v v∈V' → e-unfold (body-valid v v∈V'))

  e-unfold : ∀{e τ} → e ∈E⟦ τ ⟧ → e ∈E'⟦ τ ⟧
  e-unfold (E-fold e' e~>*e' e'∈V) = e' , e~>*e' , v-unfold e'∈V

V-val : ∀ {e τ} → e ∈V⟦ τ ⟧ → e val
V-val v-bool-true = true-val
V-val v-bool-false = false-val
V-val (v-pair p₁ p₂) = prod-val (V-val p₁) (V-val p₂)
V-val (v-abs _) = abs-val

V⇒E : ∀ e {τ} → e ∈V⟦ τ ⟧ → e ∈E⟦ τ ⟧
V⇒E e e∈V⟦τ⟧ = E-fold e kleene-z e∈V⟦τ⟧

record _∈G⟦_⟧ {n} (γ : Substs n) (Γ : Context n) : Set where
  field
    defn-G⟦∙⟧ : ∀ x → (γ [ x ]) ∈V⟦ Γ [ x ] ⟧

open _∈G⟦_⟧

infix 4 _⊨_∈_

_⊨_∈_ : ∀ {n} → Context n → Term n → Type → Set
Γ ⊨ e ∈ τ = ∀ γ → γ ∈G⟦ Γ ⟧ → (e / γ) ∈E⟦ τ ⟧

fundamental-thm : ∀{n} {Γ : Context n} {e τ} → Γ ⊢ e ∈ τ → Γ ⊨ e ∈ τ
fundamental-thm {_} {Γ} {V x} {τ} (typ-var Γ[x]≡τ) γ γ∈G⟦Γ⟧ = V⇒E v v∈V⟦τ⟧
  where
    v = γ [ x ]

    -- not really sure why this needs to be its own function
    rewrite-Γ[x]≡τ : ∀ v → v ∈V⟦ Γ [ x ] ⟧ → v ∈V⟦ τ ⟧
    rewrite-Γ[x]≡τ v t rewrite Γ[x]≡τ = t

    v∈V⟦τ⟧ : v ∈V⟦ τ ⟧
    v∈V⟦τ⟧ = rewrite-Γ[x]≡τ v (defn-G⟦∙⟧ γ∈G⟦Γ⟧ x)
fundamental-thm typ-true γ γ∈G⟦Γ⟧ = V⇒E True v-bool-true
fundamental-thm typ-false γ γ∈G⟦Γ⟧ = V⇒E False v-bool-false
fundamental-thm {_} {_} {if e then e₁ else e₂} {τ}
  (typ-if Γ⊢e∈Bool Γ⊢e₁∈τ Γ⊢e₂∈τ) γ γ∈G⟦Γ⟧ =
    unwrap γ[e]∈E⟦Bool⟧
  where
    γ[e]∈E⟦Bool⟧ : (e / γ) ∈E⟦ TBool ⟧
    γ[e]∈E⟦Bool⟧ = fundamental-thm Γ⊢e∈Bool γ γ∈G⟦Γ⟧

    γ[e₁]∈E⟦τ⟧ : (e₁ / γ) ∈E⟦ τ ⟧
    γ[e₁]∈E⟦τ⟧ = fundamental-thm Γ⊢e₁∈τ γ γ∈G⟦Γ⟧

    γ[e₂]∈E⟦τ⟧ : (e₂ / γ) ∈E⟦ τ ⟧
    γ[e₂]∈E⟦τ⟧ = fundamental-thm Γ⊢e₂∈τ γ γ∈G⟦Γ⟧

    unwrap : (e / γ) ∈E⟦ TBool ⟧ →
      (if (e / γ) then (e₁ / γ) else (e₂ / γ)) ∈E⟦ τ ⟧
    unwrap (E-fold True e~>*True v-bool-true) =
      E-fold
        (_∈E⟦_⟧.v γ[e₁]∈E⟦τ⟧)
        (kleene-append
          (step-if* e~>*True)
          (kleene-cons step-then (_∈E⟦_⟧.e~>*v γ[e₁]∈E⟦τ⟧)))
        (_∈E⟦_⟧.v∈V⟦τ⟧ γ[e₁]∈E⟦τ⟧)
    unwrap (E-fold False e~>*False v-bool-false) =
      E-fold
        (_∈E⟦_⟧.v γ[e₂]∈E⟦τ⟧)
        (kleene-append
          (step-if* e~>*False)
          (kleene-cons step-else (_∈E⟦_⟧.e~>*v γ[e₂]∈E⟦τ⟧)))
        (_∈E⟦_⟧.v∈V⟦τ⟧ γ[e₂]∈E⟦τ⟧)
fundamental-thm {_} {_} {Pair e₁ e₂} {TProd τ₁ τ₂}
    (typ-prod Γ⊢e₁∈τ₁ Γ⊢e₂∈τ₂) γ γ∈G⟦Γ⟧ =
  rewrap γ[e₁]∈E⟦τ₁⟧ γ[e₂]∈E⟦τ₂⟧
  where
    γ[e₁]∈E⟦τ₁⟧ : (e₁ / γ) ∈E⟦ τ₁ ⟧
    γ[e₁]∈E⟦τ₁⟧ = fundamental-thm Γ⊢e₁∈τ₁ γ γ∈G⟦Γ⟧

    γ[e₂]∈E⟦τ₂⟧ : (e₂ / γ) ∈E⟦ τ₂ ⟧
    γ[e₂]∈E⟦τ₂⟧ = fundamental-thm Γ⊢e₂∈τ₂ γ γ∈G⟦Γ⟧

    rewrap :
      (e₁ / γ) ∈E⟦ τ₁ ⟧ →
      (e₂ / γ) ∈E⟦ τ₂ ⟧ →
      (Pair e₁ e₂ / γ) ∈E⟦ TProd τ₁ τ₂ ⟧
    rewrap (E-fold v₁ e₁~>*v₁ v₁∈V⟦τ₁⟧) (E-fold v₂ e₂~>*v₂ v₂∈V⟦τ₂⟧) =
      E-fold
        (Pair v₁ v₂)
        (kleene-append
          (step-prod₁* e₁~>*v₁)
          (step-prod₂* (V-val v₁∈V⟦τ₁⟧) e₂~>*v₂))
        (v-pair v₁∈V⟦τ₁⟧ v₂∈V⟦τ₂⟧)
fundamental-thm {_} {_} {prj₁ e} (typ-prj₁ {_} {τ₁} {τ₂} Γ⊢e∈τ) γ γ∈G⟦Γ⟧ =
    unwrap γ[e]∈E⟦τ⟧
  where
    γ[e]∈E⟦τ⟧ : (e / γ) ∈E⟦ TProd τ₁ τ₂ ⟧
    γ[e]∈E⟦τ⟧ = fundamental-thm Γ⊢e∈τ γ γ∈G⟦Γ⟧

    unwrap : (e / γ) ∈E⟦ TProd τ₁ τ₂ ⟧ → prj₁ (e / γ) ∈E⟦ τ₁ ⟧
    unwrap (E-fold (Pair v₁ v₂) e~>*vs (vs∈V@(v-pair v₁∈V⟦τ₁⟧ v₂∈V⟦τ₂⟧))) =
      E-fold
        v₁
        (kleene-snoc (step-prj₁* e~>*vs) (step-prj₁-app (V-val vs∈V)))
        v₁∈V⟦τ₁⟧
fundamental-thm {_} {_} {prj₂ e} (typ-prj₂ {_} {τ₁} {τ₂} Γ⊢e∈τ) γ γ∈G⟦Γ⟧ =
    unwrap γ[e]∈E⟦τ⟧
  where
    γ[e]∈E⟦τ⟧ : (e / γ) ∈E⟦ TProd τ₁ τ₂ ⟧
    γ[e]∈E⟦τ⟧ = fundamental-thm Γ⊢e∈τ γ γ∈G⟦Γ⟧

    unwrap : (e / γ) ∈E⟦ TProd τ₁ τ₂ ⟧ → prj₂ (e / γ) ∈E⟦ τ₂ ⟧
    unwrap (E-fold (Pair v₁ v₂) e~>*vs (vs∈V@(v-pair v₁∈V⟦τ₁⟧ v₂∈V⟦τ₂⟧))) =
      E-fold
        v₂
        (kleene-snoc (step-prj₂* e~>*vs) (step-prj₂-app (V-val vs∈V)))
        v₂∈V⟦τ₂⟧
fundamental-thm {_} {_} {ƛxe@(ƛ τ e)} (typ-abs {_} {_} {τ'} Γ,x~τ⊢e∈τ') γ γ∈G⟦Γ⟧ =
  E-fold (ƛxe / γ) kleene-z {!!}
  where
    γ[ƛxe] : Term zero
    γ[ƛxe] = (ƛ τ e) / γ

    foo : Term (suc zero)
    foo = e / (γ ↑)
fundamental-thm (typ-app a b) γ γ∈G⟦Γ⟧ = {!!}

E-exists-forall : ∀ {e τ} →
  (e ∈E'⟦ τ ⟧) →
  (∀ e' → e ~>* e' → irred e' → e' ∈V'⟦ τ ⟧)
E-exists-forall (e₁ , e~>*e₁ , e₁∈V'⟦τ⟧) e₂ e~>*e₂ e₂-irred =
    convert e₁≡e₂ e₁∈V'⟦τ⟧
  where
    e₁-irred : irred e₁
    e₁-irred = (val-irred (V-val (v-fold e₁∈V'⟦τ⟧)))

    e₁≡e₂ : e₁ ≡ e₂
    e₁≡e₂ = norm-deterministic e~>*e₁ e~>*e₂ e₁-irred e₂-irred

    convert : ∀{e₁ e₂ τ} → (e₁ ≡ e₂) → e₁ ∈V'⟦ τ ⟧ → e₂ ∈V'⟦ τ ⟧
    convert e₁≡e₂ e₁∈V'⟦τ⟧ rewrite e₁≡e₂ = e₁∈V'⟦τ⟧
