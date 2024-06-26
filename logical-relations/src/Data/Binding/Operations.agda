open import Data.Binding

module Data.Binding.Operations {{_ : NomPa}} where

open import Data.Maybe
open import Data.Nat
open import Data.Sum
open import Function

_ᴮ : ℕ → Binder
zero ᴮ = zeroᴮ
(suc n) ᴮ = sucᴮ (n ᴮ)

exportWith : ∀ {b : Binder} {α : World} {A : Set} → A → (Name α → A) → Name (b ◃ α) → A
exportWith v f n with exportᴺ n
... | inj₁ _ = v
... | inj₂ x = f x

record TrKit (Env : World → World → Set) (Res : World → Set) : Set where
  constructor mk
  field
    trName : ∀{α β} → Env α β → Name α → Res β
    trBinder : ∀{α β} → Env α β → Binder → Binder
    extEnv : ∀ {α β} b (∆ : Env α β) → Env (b ◃ α) (trBinder ∆ b ◃ β)

record Supply (α : World) : Set where
  constructor mkSupply
  field
    seedᴮ : Binder
    seed# : seedᴮ # α

zeroS : Supply ∅
zeroS = mkSupply (0 ᴮ) (0 ᴮ #∅)

sucS : ∀{α} → (s : Supply α) → Supply (Supply.seedᴮ s ◃ α)
sucS (mkSupply seedᴮ seed#) = mkSupply (sucᴮ seedᴮ) (suc# seed#)

mutual
  worldN : ℕ → World
  worldN zero = ∅
  worldN (suc n) = Supply.seedᴮ (supplyN n) ◃ worldN n

  supplyN : ∀ n → Supply (worldN n)
  supplyN zero = zeroS
  supplyN (suc n) = sucS (supplyN n)

record SubstEnv (Res : World → Set) (α : World) (β : World) : Set where
  constructor mk
  field
    trName : Name α → Res β
    supply : Supply β

  open Supply supply public

  trBinder : Binder → Binder
  trBinder _ = seedᴮ

RenameEnv : (α β : World) → Set
RenameEnv = SubstEnv Name

renameKit : TrKit RenameEnv Name
renameKit = mk trName trBinder extEnv
  where
    open SubstEnv
    extEnv : ∀{α β} b (Δ : RenameEnv α β) → RenameEnv (b ◃ α) (_ ◃ β)
    extEnv {α} {β} b (mk trName s@(mkSupply seedᴮ seed#β)) = mk trName' (sucS s)
      where
        trName' : Name (b ◃ α) → Name (_ ◃ β)
        trName' = exportWith (nameᴮ seedᴮ) (coerceᴺ (⊆-# seed#β) ∘ trName)

_⊢>|_ : ∀{A : Set} → (A → Set) → (A → Set) → Set
F ⊢>| G = ∀{i} → F i → G i

Coerce : (World → Set) → Set
Coerce F = ∀{α β} → α ⊆ β → F α → F β

coerceKit : TrKit _⊆_ Name
coerceKit = mk coerceᴺ (const id) ⊆-◃

substKit : ∀{F : World → Set} → (Name ⊢>| F) → Coerce F → TrKit (SubstEnv F) F
substKit {F} V coerceF = mk trName trBinder extEnv
  where
    open SubstEnv

    extEnv : ∀ {α β} b (∆ : SubstEnv F α β) → SubstEnv F (b ◃ α) (_ ◃ β)
    extEnv {α} {β} b (mk trName s@(mkSupply seedᴮ seed#β)) = mk trName' (sucS s)
      where
        trName' : Name (b ◃ α) → F (_ ◃ β)
        trName' = exportWith (V (nameᴮ seedᴮ)) (coerceF (⊆-# seed#β) ∘ trName)

mapKit : ∀{Env} {F} {G} → (f : Name ⊢>| Name) (g : F ⊢>| G) → TrKit Env F → TrKit Env G
mapKit f g kit = mk (λ Δ → g ∘ trName Δ ∘ f) trBinder extEnv
  where open TrKit kit
