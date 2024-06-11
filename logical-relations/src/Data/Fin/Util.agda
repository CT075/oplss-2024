module Data.Fin.Util where

open import Data.Fin
open import Data.Nat using (ℕ; s≤s; z≤n; suc)
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Comparison (n : ℕ) : Fin n → Fin n → Set where
  eq : ∀ i → Comparison n i i
  lt : ∀ {i j} → i < j → Comparison n i j
  gt : ∀ {i j} → j < i → Comparison n i j

compareW : ∀ {n} (i j : Fin n) → Comparison n i j
compareW zero zero = eq zero
compareW (suc i) zero = gt (s≤s z≤n)
compareW zero (suc j) = lt (s≤s z≤n)
compareW (suc i) (suc j) with compareW i j
... | eq j = eq (suc j)
... | gt (j<i) = gt (s≤s j<i)
... | lt (i<j) = lt (s≤s i<j)

<⇒pred : ∀ {n} {i : Fin (suc n)} j → i < j → ∃[ j' ](j ≡ suc j)
<⇒pred j (s≤s {_} {j'} _) = j' , refl
