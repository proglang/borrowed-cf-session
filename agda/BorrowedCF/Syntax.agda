{-# OPTIONS --rewriting #-}

module BorrowedCF.Syntax where

open import Data.Bool using () renaming (Bool to Flag; true to set; false to unset) public
open import Data.List.Membership.Propositional

open import BorrowedCF.Prelude
open import BorrowedCF.Kits

variable st : SortTy

data ProcKind : Set where
  ty un : ProcKind

variable pk : ProcKind

data Sort : SortTy → Set where
  𝕜 : Sort NoVar
  𝕥 : Sort NoVar
  𝕤 : Sort Var
  𝕖 : Sort Var
  𝕡 : ProcKind → Sort NoVar
  𝕗 : Sort Var

variable 𝔰 𝔰₁ 𝔰₂ 𝔰₃ 𝔰′ : Sort st

data Pol : Set where
  ‼ ⁇ : Pol

data Dir : Set where
  L R 𝟙 : Dir

data Mob : Set where
  M S : Mob

data Eff : Set where
  ℙ 𝕀 : Eff

variable ϵ ϵ₁ ϵ₂ ϵ₃ ϵ′ : Eff

data _≤ϵ_ : Rel Eff 0ℓ where
  ℙ≤ϵ : ℙ ≤ϵ ϵ
  𝕀≤𝕀 : 𝕀 ≤ϵ 𝕀

≤ϵ-refl : ϵ ≤ϵ ϵ
≤ϵ-refl {ℙ} = ℙ≤ϵ
≤ϵ-refl {𝕀} = 𝕀≤𝕀

data Lin : Set where
  𝟙 unr : Lin

record Arr : Set where
  constructor arr
  field
    lin : Lin
    dir : Dir
    mob : Mob
    eff : Eff

  Mobile = mob ≡ M
  Unr = lin ≡ unr
  Par = dir ≡ 𝟙

  field
    ω⇒M : Unr → Mobile
    ω⇒𝟙 : Unr → Par

data Const : Set where
  `unit `fork `send `recv `drop `acq : Const
  `end : Pol → Const
  `new : {- 𝕊 0 → -} Const -- TODO
  `lsplit `rsplit : Const -- TODO

Scope = List (Sort Var)

BindGroup = List ℕ

bgScope : BindGroup → Scope
bgScope = L.concatMap (flip L.replicate 𝕖)

record 𝕖⊎𝕤 (s : Sort Var) : Set where
  field ev : s ≡ 𝕖 ⊎ s ≡ 𝕤

instance
  𝕖⊎𝕤-𝕖 : 𝕖⊎𝕤 𝕖
  𝕖⊎𝕤-𝕖 = record { ev = inj₁ refl }

  𝕖⊎𝕤-𝕤 : 𝕖⊎𝕤 𝕤
  𝕖⊎𝕤-𝕤 = record { ev = inj₂ refl }

infix 4 _⊢_

data _⊢_ (S : Scope) : Sort st → Set where
  `_ : 𝔰 ∈ S → S ⊢ 𝔰

  ⋆ : S ⊢ 𝕜

  ⟨_⟩ : (s : S ⊢ 𝕤) → S ⊢ 𝕥
  `⊤  : S ⊢ 𝕥
  _⟨_⟩→_ : (t : S ⊢ 𝕥) (a : Arr) (u : S ⊢ 𝕥) → S ⊢ 𝕥
  _⊗⟨_⟩_ : (t : S ⊢ 𝕥) (d : Dir) (u : S ⊢ 𝕥) → S ⊢ 𝕥

  end : (p : Pol) → S ⊢ 𝕤
  msg : (p : Pol) (t : S ⊢ 𝕥) → S ⊢ 𝕤
  brn : (p : Pol) (s₁ s₂ : S ⊢ 𝕤) → S ⊢ 𝕤
  skip ret acq : S ⊢ 𝕤

  μ : .⦃ 𝕖⊎𝕤 𝔰 ⦄ → 𝔰 ∷ S ⊢ s → S ⊢ s
  _;_ : .⦃ 𝕖⊎𝕤 𝔰 ⦄ → (x₁ x₂ : S ⊢ s) → S ⊢ s

  K : (c : Const) → S ⊢ 𝕖
  ƛ : (e : 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖
  _⊗_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
  _·_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
  `let⊗_`in_ : (e₁ : S ⊢ 𝕖) (e₂ : 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖

  ⟪_⟫ : (e : S ⊢ 𝕖) → S ⊢ 𝕡 pk
  _∥_ : (P Q : S ⊢ 𝕡 pk) → S ⊢ 𝕡 pk

  ν[_][_] : (B₁ B₂ : List ℕ) (P : bgScope B₁ ++ bgScope B₂ ++ S ⊢ 𝕡 ty) → S ⊢ 𝕡 ty

  ν : (P : 𝕖 ∷ 𝕖 ∷ S ⊢ 𝕡 un) → S ⊢ 𝕡 un
  φ : (P : 𝕗 ∷ S ⊢ 𝕡 un) → S ⊢ 𝕡 un
  _↦_ : (x : S ⊢ 𝕗) (⁰/₁ : Flag) → S ⊢ 𝕡 un

pattern _⊗¹_ T U = T ⊗⟨ 𝟙 ⟩ U
pattern _⊗ᴸ_ T U = T ⊗⟨ L ⟩ U

variable
  s s₁ s₂ s₃ s′ : S ⊢ s

data Skips {S} : S ⊢ 𝕤 → Set where
  skip : Skips skip
--  _;_ : (S₁ : Skips s₁) (S₂ : Skips s₂) → Skips (s₁ ; s₂)
  μ : (S : Skips s) → Skips (μ s)
