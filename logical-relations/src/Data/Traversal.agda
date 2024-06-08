module Data.Traversal where

open import Level renaming (zero to lzero; suc to lsuc)

private
  variable
    ℓ : Level
    T : Set ℓ

  data Seal : Set where
    S : Seal

record IsRep (F : Set ℓ → Set ℓ) : Set where
  field
    seal : Seal

record GenericPolynomial (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    Rep : Set ℓ → Set ℓ
    RWitness : IsRep Rep
    wrapP : F T → Rep T
    unwrapP : Rep T → F T

data VoidLike : Set → Set where

VoidIsRep : IsRep VoidLike
VoidIsRep = record { seal = S }

data UnitLike : Set → Set where
  U1 : UnitLike T

UnitIsRep : IsRep UnitLike
UnitIsRep = record { seal = S }

record Par1 (A : Set ℓ) (T : Set ℓ) : Set ℓ where
  constructor P1
  field
    unP1 : A

ParIsRep : ∀{ℓ} {A : Set ℓ} → IsRep (Par1 A)
ParIsRep = record { seal = S }

record _:*:_ (F : Set ℓ → Set ℓ) (G : Set ℓ → Set ℓ) (T : Set ℓ) : Set ℓ where
  constructor MkGenericProduct
  field
    L1* : F T
    R1* : G T

ProductIsRep : ∀
  (F : Set ℓ → Set ℓ) ⦃ _ : IsRep F ⦄
  (G : Set ℓ → Set ℓ) ⦃ _ : IsRep G ⦄ →
  IsRep (F :*: G)
ProductIsRep F G = record { seal = S }

data _:+:_ (F : Set ℓ → Set ℓ) (G : Set ℓ → Set ℓ) (T : Set ℓ) : Set ℓ where
  L1 : F T → (F :+: G) T
  R1 : G T → (F :+: G) T

SumIsRep : ∀
  (F : Set ℓ → Set ℓ) ⦃ _ : IsRep F ⦄
  (G : Set ℓ → Set ℓ) ⦃ _ : IsRep G ⦄ →
  IsRep (F :+: G)
SumIsRep F G = record { seal = S }

genericMap : ∀{ℓ : Level} {a b} → (F : Set ℓ → Set ℓ) →
  ⦃ FPoly : GenericPolynomial F ⦄ →
  (a → b) → F a → F b
genericMap = {!!}
