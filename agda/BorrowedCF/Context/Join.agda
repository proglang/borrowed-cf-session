module BorrowedCF.Context.Join where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Substitution

open Nat.Variables
open Variables

biasedDir : ParSeq → Dir
biasedDir par = 𝟙
biasedDir seq = L

record Join (A : Set) : Set where
  field joinDir : A → Dir

  join : A → Struct n → Struct n → Struct n
  join a with joinDir a
  ... | 𝟙 = _∥_
  ... | L = _;_
  ... | R = flip _;_

  ≈-join : ∀ a → Γ ∶ α₁ ≈ α₂ → Γ ∶ β₁ ≈ β₂ → Γ ∶ join a α₁ β₁ ≈ join a α₂ β₂
  ≈-join a with joinDir a
  ... | 𝟙 = ∥-cong
  ... | L = ;-cong
  ... | R = flip ;-cong

  ≼-join : ∀ a → Γ ∶ α₁ ≼ α₂ → Γ ∶ β₁ ≼ β₂ → Γ ∶ join a α₁ β₁ ≼ join a α₂ β₂
  ≼-join a with joinDir a
  ... | 𝟙 = ≼-cong-∥
  ... | L = ≼-cong-;
  ... | R = flip ≼-cong-;

  join-[]₁ : ∀ a → Γ ∶ join a [] β ≈ β
  join-[]₁ a with joinDir a
  ... | 𝟙 = ∥-comm ◅◅ ∥-unit
  ... | L = ;-unit₁
  ... | R = ;-unit₂

  join-[]₂ : ∀ a → Γ ∶ join a α [] ≈ α
  join-[]₂ a with joinDir a
  ... | 𝟙 = ∥-unit
  ... | L = ;-unit₂
  ... | R = ;-unit₁

  join-⋯ : ∀ a (α β : Struct n) → join a α β ⋯ σ ≡ join a (α ⋯ σ) (β ⋯ σ)
  join-⋯ a α β with joinDir a
  ... | L = refl
  ... | R = refl
  ... | 𝟙 = refl

open Join ⦃ ... ⦄ public

instance
  join-dir : Join Dir
  join-dir = record { joinDir = id }

  join-p/s : Join ParSeq
  join-p/s = record { joinDir = biasedDir }
