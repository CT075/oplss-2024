open import Data.Binding

module Data.Binding.Context {{_ : NomPa}} where

Ctx : Set → World → Set
Ctx T w = Name w → T
