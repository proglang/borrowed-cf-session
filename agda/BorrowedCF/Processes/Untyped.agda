module BorrowedCF.Processes.Untyped where

open import Data.Bool using () renaming (Bool to Flag; true to set; false to unset) public
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open Nat.Variables

infix 15 _↦_
infix 14 _∥_

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : (P : Proc (2 + n)) → Proc n
  φ   : (P : Proc (1 + n)) → Proc n
  _↦_ : (x : 𝔽 n) (⁰/₁ : Flag) → Proc n

variable
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n


infixl 5 _⋯ₚ_

_⋯ₚ_ : Proc m → m →ᵣ n → Proc n
⟪ e ⟫   ⋯ₚ ρ = ⟪ e ⋯ ρ ⟫
P ∥ Q   ⋯ₚ ρ = (P ⋯ₚ ρ) ∥ (Q ⋯ₚ ρ)
ν P     ⋯ₚ ρ = ν (P ⋯ₚ ρ ↑* 2)
φ P     ⋯ₚ ρ = φ (P ⋯ₚ ρ ↑)
(x ↦ ϕ) ⋯ₚ ρ = ρ x ↦ ϕ

⋯ₚ-cong : (P : Proc m) {ρ₁ ρ₂ : m →ᵣ n} → ρ₁ ≗ ρ₂ → P ⋯ₚ ρ₁ ≡ P ⋯ₚ ρ₂
⋯ₚ-cong ⟪ e ⟫   eq = cong ⟪_⟫ (⋯-cong e eq)
⋯ₚ-cong (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-cong P eq) (⋯ₚ-cong Q eq)
⋯ₚ-cong (ν P)   eq = cong ν (⋯ₚ-cong P (eq ~↑* 2))
⋯ₚ-cong (φ P)   eq = cong φ (⋯ₚ-cong P (eq ~↑))
⋯ₚ-cong (x ↦ ϕ) eq = cong (_↦ ϕ) (eq x)

fusionₚ : (P : Proc n₁) (ρ₁ : n₁ →ᵣ n₂) (ρ₂ : n₂ →ᵣ n₃) →
          P ⋯ₚ ρ₁ ⋯ₚ ρ₂ ≡ P ⋯ₚ (ρ₁ ·ₖ ρ₂)
fusionₚ ⟪ e ⟫   ρ₁ ρ₂ = cong ⟪_⟫ (fusion e ρ₁ ρ₂)
fusionₚ (P ∥ Q) ρ₁ ρ₂ = cong₂ _∥_ (fusionₚ P ρ₁ ρ₂) (fusionₚ Q ρ₁ ρ₂)
fusionₚ (ν P)   ρ₁ ρ₂ = cong ν (fusionₚ P (ρ₁ ↑* 2) (ρ₂ ↑* 2) ■ sym (⋯ₚ-cong P (dist-↑*-· 2 ρ₁ ρ₂)))
fusionₚ (φ P)   ρ₁ ρ₂ = cong φ (fusionₚ P (ρ₁ ↑) (ρ₂ ↑) ■ sym (⋯ₚ-cong P (dist-↑-· ρ₁ ρ₂)))
fusionₚ (x ↦ ϕ) ρ₁ ρ₂ = refl

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
  φ-comm′  : φ (φ P) ≋′ φ (φ (P ⋯ₚ assocSwapᵣ 1 1))
  νφ-comm′ : ν (φ P) ≋′ φ (ν (P ⋯ₚ assocSwapᵣ 1 2))
  ν-ext′   : P ∥ ν Q ≋′ ν ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) ∥ Q)
  φ-ext′   : P ∥ φ Q ≋′ φ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) ∥ Q)
  ∥-cong′  : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q
  ν-cong′  : P ≋′ Q → ν P ≋′ ν Q
  φ-cong′  : P ≋′ Q → φ P ≋′ φ Q

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

  φ-cong : P ≋ Q → φ P ≋ φ Q
  φ-cong = gmap φ φ-cong′
