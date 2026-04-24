module BorrowedCF.Processes where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Context
open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open Nat.Variables

Bind : ℕ → Set
Bind n = ∃[ xs ] sum xs ≡ n

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : ∀ {b₁ b₂} (B₁ : Bind b₁) (B₂ : Bind b₂) (P : Proc (b₁ + (b₂ + n))) → Proc n

variable
  A A₁ A₂ A₃ A′ : Bind n
  B B₁ B₂ B₃ B′ : Bind n
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n

infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫ ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν {b₁} {b₂} B₁ B₂ P ⋯ₚ ϕ = ν B₁ B₂ (P ⋯ₚ ϕ ↑* b₂ ↑* b₁)

bind-swap : ∀ b₁ b₂ → b₁ + (b₂ + n) →ᵣ b₂ + (b₁ + n)
bind-swap b₁ b₂ x = [ (λ y → b₂ ↑ʳ (y ↑ˡ _)) , [ (λ y → y ↑ˡ _) , (λ y → b₂ ↑ʳ b₁ ↑ʳ y) ]′ ∘ Fin.splitAt b₂ ]′ (Fin.splitAt b₁ x)

bind-comm : ∀ a₁ a₂ b₁ b₂ → a₁ + (a₂ + (b₁ + (b₂ + n))) →ᵣ b₁ + (b₂ + (a₁ + (a₂ + n)))
bind-comm = {!!}

infix 4 _≋′_

data _≋′_ {n} : Rel (Proc n) 0ℓ where
  ∥-comm′ : P ∥ Q ≋′ Q ∥ P
  ∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃
  ∥-unit′ : ⟪ K `unit ⟫ ∥ P ≋′ P
  ν-swap′ : ∀ {b₁ b₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P} → ν B₁ B₂ P ≋′ ν B₂ B₁ (P ⋯ₚ bind-swap b₁ b₂)
  ν-comm′ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Bind a₁} {A₂ : Bind a₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P} →
    ν B₁ B₂ (ν A₁ A₂ P) ≋′ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ bind-comm a₁ a₂ b₁ b₂))
  ν-ext′  : ∀ {b₁ b₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P Q} →
    P ∥ ν B₁ B₂ Q ≋′ ν B₁ B₂ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ b₂ ⋯ₚ weaken* ⦃ Kᵣ ⦄ b₁) ∥ Q)
