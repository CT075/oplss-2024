module Effect.Applicative.Util where

open import Effect.Applicative
open import Effect.Functor
open import Function
open import Level renaming (suc to lsuc)

private
  variable
    ℓ : Level
    A B : Set ℓ

module MIdentity where
  _<$>_ : (A → B) → A → B
  f <$> x = f x

  rawFunctor : RawFunctor (id {lsuc ℓ})
  rawFunctor = record { _<$>_ = _<$>_ }
  pure = id
  _<*>_ = _<$>_

id-functor : RawFunctor (id {lsuc ℓ})
id-functor = record {MIdentity}

id-app : RawApplicative (id {lsuc ℓ})
id-app = record {MIdentity}
