module Data.Nat.Util where

open import Data.Nat

<s⇒≤ : ∀{i j} → i < suc j → i ≤ j
<s⇒≤ (s≤s i≤j) = i≤j
