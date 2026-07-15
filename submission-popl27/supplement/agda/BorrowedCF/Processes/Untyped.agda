module BorrowedCF.Processes.Untyped where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open Nat.Variables

infix 14 _∥_

data Flag : Set where
  drop acq : Flag

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : (P : Proc (2 + n)) → Proc n
  φ   : Flag → (P : Proc (1 + n)) → Proc n

variable
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n


infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫   ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q   ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν P     ⋯ₚ ϕ = ν (P ⋯ₚ ϕ ↑* 2)
φ x P   ⋯ₚ ϕ = φ x (P ⋯ₚ ϕ ↑)

⋯ₚ-cong : ⦃ K : Kit 𝓕 ⦄ (P : Proc m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → P ⋯ₚ ϕ₁ ≡ P ⋯ₚ ϕ₂
⋯ₚ-cong ⟪ e ⟫   eq = cong ⟪_⟫ (⋯-cong e eq)
⋯ₚ-cong (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-cong P eq) (⋯ₚ-cong Q eq)
⋯ₚ-cong (ν P)   eq = cong ν (⋯ₚ-cong P (eq ~↑* 2))
⋯ₚ-cong (φ x P) eq = cong (φ x) (⋯ₚ-cong P (eq ~↑))

fusionₚ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ C : CKit K₁ K₂ K ⦄ ⦃ W : WkKit K₁ ⦄ →
          (P : Proc n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
          P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ (ϕ₁ ·ₖ ϕ₂)
fusionₚ ⟪ e ⟫   ϕ₁ ϕ₂ = cong ⟪_⟫ (fusion e ϕ₁ ϕ₂)
fusionₚ (P ∥ Q) ϕ₁ ϕ₂ = cong₂ _∥_ (fusionₚ P ϕ₁ ϕ₂) (fusionₚ Q ϕ₁ ϕ₂)
fusionₚ (ν P)   ϕ₁ ϕ₂ = cong ν (fusionₚ P (ϕ₁ ↑* 2) (ϕ₂ ↑* 2) ■ sym (⋯ₚ-cong P (dist-↑*-· 2 ϕ₁ ϕ₂)))
fusionₚ (φ x P) ϕ₁ ϕ₂ = cong (φ x) (fusionₚ P (ϕ₁ ↑) (ϕ₂ ↑) ■ sym (⋯ₚ-cong P (dist-↑-· ϕ₁ ϕ₂)))

≡-fusedₚ : (P : Proc m) (ρ₁ : m →ᵣ n₁) (ρ₂ : n₁ →ᵣ n) (ρ₃ : m →ᵣ n₂) (ρ₄ : n₂ →ᵣ n) →
           ρ₁ ·ₖ ρ₂ ≗ ρ₃ ·ₖ ρ₄ →
           P ⋯ₚ ρ₁ ⋯ₚ ρ₂ ≡ P ⋯ₚ ρ₃ ⋯ₚ ρ₄
≡-fusedₚ P ρ₁ ρ₂ ρ₃ ρ₄ eq = fusionₚ P ρ₁ ρ₂ ■ ⋯ₚ-cong P eq ■ sym (fusionₚ P ρ₃ ρ₄)

infix 4 _≋′_

data _≋′_ {n} : Rel (Proc n) 0ℓ where
  ∥-comm′  : P ∥ Q ≋′ Q ∥ P
  ∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃
  ∥-unit′  : ⟪ K `unit ⟫ ∥ P ≋′ P
  ν-swap′  : ν P ≋′ ν (P ⋯ₚ swapᵣ 1 1)
  ν-comm′  : ν (ν P) ≋′ ν (ν (P ⋯ₚ assocSwapᵣ 2 2))
  φ-comm′  : ∀ {x y} → φ x (φ y P) ≋′ φ y (φ x (P ⋯ₚ assocSwapᵣ 1 1))
  νφ-comm′ : ∀ {x} → ν (φ x P) ≋′ φ x (ν (P ⋯ₚ assocSwapᵣ 1 2))
  ν-ext′   : P ∥ ν Q ≋′ ν ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) ∥ Q)
  φ-ext′   : ∀ {x} → P ∥ φ x Q ≋′ φ x ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) ∥ Q)
  ∥-cong′  : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q
  ν-cong′  : P ≋′ Q → ν P ≋′ ν Q
  φ-cong′  : ∀ {x} → P ≋′ Q → φ x P ≋′ φ x Q

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

  ν-cong : P ≋ Q → ν P ≋ ν Q
  ν-cong = gmap ν ν-cong′

  φ-cong : ∀ {x} → P ≋ Q → φ x P ≋ φ x Q
  φ-cong = gmap (φ _) φ-cong′
