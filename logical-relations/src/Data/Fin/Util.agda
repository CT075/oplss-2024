module Data.Fin.Util where

open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Fin

data Comparison {n} : Fin n → Fin n → Set where
  eq : ∀ i → Comparison i i
  lt : ∀{i j} → i < j → Comparison i j
  gt : ∀{i j} → j < i → Comparison i j

comparePred : ∀{n} → (i : Fin n) → (j : Fin n) → Comparison i j
comparePred zero zero = eq zero
comparePred (suc i) zero = gt (s≤s z≤n)
comparePred zero (suc j) = lt (s≤s z≤n)
comparePred (suc i) (suc j) with comparePred i j
... | eq j = eq (suc j)
... | gt (j<i) = gt (s≤s j<i)
... | lt (i<j) = lt (s≤s i<j)
