module Data.Fin.Util where

open import Data.Fin
open import Data.Nat using (ℕ; s≤s; z≤n; zero; suc)
open import Data.Nat.Properties using (m<n⇒n≢0)
open import Data.Product
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

data Comparison (n : ℕ) : Fin n → Fin n → Set where
  eq : ∀ i → Comparison n i i
  lt : ∀ {i j} → i < j → Comparison n i j
  gt : ∀ {i j} → j < i → Comparison n i j

compareW : ∀{n} (i j : Fin n) → Comparison n i j
compareW zero zero = eq zero
compareW (suc i) zero = gt (s≤s z≤n)
compareW zero (suc j) = lt (s≤s z≤n)
compareW (suc i) (suc j) with compareW i j
... | eq j = eq (suc j)
... | gt (j<i) = gt (s≤s j<i)
... | lt (i<j) = lt (s≤s i<j)

<⇒≢0 : ∀{n} {i : Fin (suc n)} (j : Fin (suc n)) → i < j → j ≢ zero
<⇒≢0 {_} {i} j i<j j≡0 = contradiction j≡0ℕ j≢0ℕ
  where
    j≢0ℕ : toℕ j ≢ zero
    j≢0ℕ = m<n⇒n≢0 i<j

    j≡0ℕ : toℕ j ≡ zero
    j≡0ℕ rewrite j≡0 = refl

pred' : ∀{n} → (i : Fin (suc n)) → i ≢ zero → Fin n
pred' zero i≢zero = contradiction refl i≢zero
pred' (suc i) _ = i
