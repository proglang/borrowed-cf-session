{-# OPTIONS --rewriting #-}

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

-- ⋯ₚ-cong : ⦃ K : Kit 𝓕 ⦄ (P : Proc m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → P ⋯ₚ ϕ₁ ≡ P ⋯ₚ ϕ₂
-- ⋯ₚ-cong ⟪ e ⟫ eq = cong ⟪_⟫ (⋯-cong e eq)
-- ⋯ₚ-cong (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-cong P eq) (⋯ₚ-cong Q eq)
-- ⋯ₚ-cong (ν P) eq = cong ν (⋯ₚ-cong P (eq ~↑* _))
-- ⋯ₚ-cong (φ P) eq = {!!}
-- ⋯ₚ-cong (x ↦ ⁰/₁) eq = {!!}

-- {-
-- fusionₚ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄
--           ⦃ C : CKit K₁ K₂ K ⦄ (P : Proc n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
--           P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ ϕ₁ ·ₖ ϕ₂
-- fusionₚ ⟪ e ⟫ ϕ₁ ϕ₂ = cong ⟪_⟫ (fusion e ϕ₁ ϕ₂)
-- fusionₚ (P ∥ Q) ϕ₁ ϕ₂ = cong₂ _∥_ (fusionₚ P ϕ₁ ϕ₂) (fusionₚ Q ϕ₁ ϕ₂)
-- fusionₚ (ν P) ϕ₁ ϕ₂ = cong ν (fusionₚ P (ϕ₁ ↑* _) (ϕ₂ ↑* _) ■ sym (⋯ₚ-cong P (dist-↑*-· _ ϕ₁ ϕ₂)))
-- fusionₚ (φ P) ϕ₁ ϕ₂ = {!!}
-- fusionₚ (x ↦ ⁰/₁) ϕ₁ ϕ₂ = {!!}

-- ≡-fusedₚ : ∀ {𝓕₁ 𝓕₂ 𝓕₃ 𝓕₄ : Scoped} {a b} →
--   ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K₃ : Kit 𝓕₃ ⦄ ⦃ K₄ : Kit 𝓕₄ ⦄ ⦃ K : Kit 𝓕 ⦄ →
--   ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₃ : WkKit K₃ ⦄ ⦃ Ca : CKit K₁ K₂ K ⦄ ⦃ Cb : CKit K₃ K₄ K ⦄ →
--   (P : Proc m) (ϕ₁ : m –[ K₁ ]→ a) (ϕ₂ : a –[ K₂ ]→ n) (ϕ₃ : m –[ K₃ ]→ b) (ϕ₄ : b –[ K₄ ]→ n) →
--   ϕ₁ ·[ Ca ] ϕ₂ ≗ ϕ₃ ·[ Cb ] ϕ₄ →
--   P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ ϕ₃ ⋯ₚ ϕ₄
-- ≡-fusedₚ P ϕ₁ ϕ₂ ϕ₃ ϕ₄ eq = fusionₚ P ϕ₁ ϕ₂ ■ ⋯ₚ-cong P eq ■ sym (fusionₚ P ϕ₃ ϕ₄)
-- -}
