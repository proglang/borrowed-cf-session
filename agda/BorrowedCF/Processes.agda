module BorrowedCF.Processes where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

import BorrowedCF.Context as 𝐂
open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open Nat.Variables

Bind : ℕ → Set
Bind n = ∃[ xs ] sum xs ≡ n

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : ∀ {b₁ b₂} (B₁ : Bind b₁) (B₂ : Bind b₂) (P : Proc (b₁ + b₂ + n)) → Proc n

variable
  A A₁ A₂ A₃ A′ : Bind n
  B B₁ B₂ B₃ B′ : Bind n
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n

infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫ ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν {b₁} {b₂} B₁ B₂ P ⋯ₚ ϕ = ν B₁ B₂ (P ⋯ₚ ϕ ↑* (b₁ + b₂))

bind-swap : ∀ b₁ b₂ → b₁ + b₂ + n →ᵣ b₂ + b₁ + n
bind-swap {n} b₁ b₂ = Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁) ∘ Fin.splitAt (b₁ + b₂)
{-
  Fin.cast (Nat.+-assoc b₂ b₁ n)
    ∘ Fin.join _ _
    ∘ Sum.map₁ (Fin.join _ _ ∘ Sum.swap ∘ Fin.splitAt b₁)
    ∘ Fin.splitAt (b₁ + b₂)
    ∘ Fin.cast (sym (Nat.+-assoc b₁ b₂ n))
-}

bind-comm : ∀ a₁ a₂ b₁ b₂ → a₁ + a₂ + (b₁ + b₂ + n) →ᵣ b₁ + b₂ + (a₁ + a₂ + n)
bind-comm {n} a₁ a₂ b₁ b₂ = {!bind-swap (a₁ + a₂) (b₁ + b₂ + n)!}
{-
  let eq p₁ p₂ q₁ q₂ = cong (p₁ + p₂ +_) (Nat.+-assoc q₁ q₂ n) ■ Nat.+-assoc p₁ p₂ (q₁ + (q₂ + n)) in
  Fin.cast (eq b₁ b₂ a₁ a₂)
    ∘ bind-swap {n} (a₁ + a₂) (b₁ + b₂)
    ∘ Fin.cast (sym (eq a₁ a₂ b₁ b₂))
-}

module _ ⦃ K : Kit 𝓕 ⦄ ⦃ C : CKit K Kᵣ K ⦄ {ϕ : m –[ K ]→ n} where
  bind-swap-exchange : (b₁ b₂ : ℕ) → bind-swap {m} b₁ b₂ ·[ Cᵣ ] ϕ ↑* (b₂ + b₁) ≗ ϕ ↑* (b₁ + b₂) ·ₖ bind-swap b₁ b₂
  bind-swap-exchange = {!!}

infix 4 _≋′_

data _≋′_ {n} : Rel (Proc n) 0ℓ where
  ∥-comm′ : P ∥ Q ≋′ Q ∥ P
  ∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃
  ∥-unit′ : ⟪ K `unit ⟫ ∥ P ≋′ P
  ν-swap′ : ∀ {b₁ b₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P} → ν B₁ B₂ P ≋′ ν B₂ B₁ (P ⋯ₚ bind-swap b₁ b₂)
  ν-comm′ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Bind a₁} {A₂ : Bind a₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P} →
    ν B₁ B₂ (ν A₁ A₂ P) ≋′ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ bind-comm a₁ a₂ b₁ b₂))
  ν-ext′ : ∀ {b₁ b₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P Q} →
    P ∥ ν B₁ B₂ Q ≋′ ν B₁ B₂ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ (b₁ + b₂)) ∥ Q)
  ∥-cong′ : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q
  ν-cong′ : P ≋′ Q → ν B₁ B₂ P ≋′ ν B₁ B₂ Q

module _ where
  open Eq*

  infix 4 _≋_

  _≋_ : Rel (Proc n) _
  _≋_ = EqClosure _≋′_

  ∥-comm : P ∥ Q ≋ Q ∥ P
  ∥-comm = return ∥-comm′

  ∥-unitˡ : ⟪ K `unit ⟫ ∥ P ≋ P
  ∥-unitˡ = return ∥-unit′

  ∥-unitʳ : P ∥ ⟪ K `unit ⟫ ≋ P
  ∥-unitʳ = ∥-comm ◅◅ ∥-unitˡ

  ∥-assoc : P₁ ∥ (P₂ ∥ P₃) ≋ (P₁ ∥ P₂) ∥ P₃
  ∥-assoc = return ∥-assoc′

  ∥-cong : P₁ ≋ P₂ → Q₁ ≋ Q₂ → P₁ ∥ Q₁ ≋ P₂ ∥ Q₂
  ∥-cong ps qs = gmap (_∥ _) ∥-cong′ ps ◅◅ ∥-comm ◅◅ gmap (_∥ _) ∥-cong′ qs ◅◅ ∥-comm

  ν-swap : ∀ {b₁ b₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P : Proc (b₁ + b₂ + n)} →
    ν B₁ B₂ P ≋ ν B₂ B₁ (P ⋯ₚ bind-swap b₁ b₂)
  ν-swap = return ν-swap′

  ν-comm : ∀ {a₁ a₂ b₁ b₂} {A₁ : Bind a₁} {A₂ : Bind a₂} {B₁ : Bind b₁} {B₂ : Bind b₂} {P : Proc (a₁ + a₂ + (b₁ + b₂ + n))} →
    ν B₁ B₂ (ν A₁ A₂ P) ≋ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ _))
  ν-comm = return ν-comm′

  ν-cong : P ≋ Q → ν B₁ B₂ P ≋ ν B₁ B₂ Q
  ν-cong = gmap (ν _ _) ν-cong′

  infix 5 _≋-⋯_

  ⋯-preserves-≋′ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → (_⋯ₚ ϕ) Bin.Preserves _≋′_ ⟶ _≋_
  ⋯-preserves-≋′ ∥-comm′ = {!ν-comm!}
  ⋯-preserves-≋′ ∥-assoc′ = {!!}
  ⋯-preserves-≋′ ∥-unit′ = {!!}
  ⋯-preserves-≋′ ν-swap′ = ν-swap ◅◅ ν-cong {!!}
  ⋯-preserves-≋′ ν-comm′ = {!!}
  ⋯-preserves-≋′ ν-ext′ = {!!}
  ⋯-preserves-≋′ (∥-cong′ x) = {!!}
  ⋯-preserves-≋′ (ν-cong′ x) = {!!}

  -- ⋯-preserves-≋′ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → (_⋯ₚ ϕ) Bin.Preserves _≋′_ ⟶ _≋′_
  -- ⋯-preserves-≋′ ∥-comm′ = ∥-comm′
  -- ⋯-preserves-≋′ ∥-assoc′ = ∥-assoc′
  -- ⋯-preserves-≋′ ∥-unit′ = ∥-unit′
  -- ⋯-preserves-≋′ (ν-swap′ {b₁}{b₂}{B₁}{B₂}) = subst (_ ≋′_) {!cong (λ P → ν B₁ B₂ P) !} ν-swap′
  -- ⋯-preserves-≋′ ν-comm′ = {!ν-comm′!}
  -- ⋯-preserves-≋′ ν-ext′ = {!!}
  -- ⋯-preserves-≋′ (∥-cong′ x) = {!!} --∥-cong′ (⋯-preserves-≋′ x)
  -- ⋯-preserves-≋′ (ν-cong′ x) = {!!} --ν-cong′ (⋯-preserves-≋′ x)

  -- -- _≋-⋯_ : ⦃ K : Kit 𝓕 ⦄ → P ≋ Q → (ϕ : m –[ K ]→ n) → P ⋯ₚ ϕ ≋ Q ⋯ₚ ϕ
  -- -- eq ≋-⋯ ϕ = join (gmap (_⋯ₚ ϕ) ⋯-preserves-≋′ eq)
