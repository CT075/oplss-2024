module Data.Fin.Util where

open import Data.Fin
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

-- punchOut commutes with the successor of its arguments
comm-punchOut/suc : ∀{n} {i j : Fin (suc n)} →
  (i≢j : i ≢ j) → (si≢sj : suc i ≢ suc j) →
  punchOut si≢sj ≡ suc (punchOut i≢j)
comm-punchOut/suc {i = zero} {j = zero} 0≢0 si≢sj = contradiction refl 0≢0
comm-punchOut/suc {i = zero} {j = suc j} i≢j si≢sj = refl
comm-punchOut/suc {i = suc i} {j = zero} i≢j si≢sj = refl
comm-punchOut/suc {i = suc i} {j = suc j} i≢j si≢sj = refl
