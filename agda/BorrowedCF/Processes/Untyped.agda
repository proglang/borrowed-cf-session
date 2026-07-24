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

-- A φ-cell now records the channel it guards (`c : Tm n`, always a variable in
-- translation images).  This is the "linked φ" design: νφ-comm is gated so a
-- cell cannot commute past the ν that binds its channel.  The reference is a
-- Tm (not a bare 𝔽) so it rides the generic `_⋯ₚ_` traversal uniformly.
data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : (P : Proc (2 + n)) → Proc n
  φ   : Flag → (c : Tm n) → (P : Proc (1 + n)) → Proc n

variable
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n


infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫   ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q   ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν P     ⋯ₚ ϕ = ν (P ⋯ₚ ϕ ↑* 2)
φ x c P ⋯ₚ ϕ = φ x (c ⋯ ϕ) (P ⋯ₚ ϕ ↑)

⋯ₚ-cong : ⦃ K : Kit 𝓕 ⦄ (P : Proc m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → P ⋯ₚ ϕ₁ ≡ P ⋯ₚ ϕ₂
⋯ₚ-cong ⟪ e ⟫   eq = cong ⟪_⟫ (⋯-cong e eq)
⋯ₚ-cong (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-cong P eq) (⋯ₚ-cong Q eq)
⋯ₚ-cong (ν P)   eq = cong ν (⋯ₚ-cong P (eq ~↑* 2))
⋯ₚ-cong (φ x c P) eq = cong₂ (φ x) (⋯-cong c eq) (⋯ₚ-cong P (eq ~↑))

fusionₚ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ C : CKit K₁ K₂ K ⦄ ⦃ W : WkKit K₁ ⦄ →
          (P : Proc n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
          P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ (ϕ₁ ·ₖ ϕ₂)
fusionₚ ⟪ e ⟫   ϕ₁ ϕ₂ = cong ⟪_⟫ (fusion e ϕ₁ ϕ₂)
fusionₚ (P ∥ Q) ϕ₁ ϕ₂ = cong₂ _∥_ (fusionₚ P ϕ₁ ϕ₂) (fusionₚ Q ϕ₁ ϕ₂)
fusionₚ (ν P)   ϕ₁ ϕ₂ = cong ν (fusionₚ P (ϕ₁ ↑* 2) (ϕ₂ ↑* 2) ■ sym (⋯ₚ-cong P (dist-↑*-· 2 ϕ₁ ϕ₂)))
fusionₚ (φ x c P) ϕ₁ ϕ₂ =
  cong₂ (φ x) (fusion c ϕ₁ ϕ₂) (fusionₚ P (ϕ₁ ↑) (ϕ₂ ↑) ■ sym (⋯ₚ-cong P (dist-↑-· ϕ₁ ϕ₂)))

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
  -- GATED: a φ-cell commutes only past binders that do NOT bind its channel.
  -- The channel points strictly outside — a `weaken*` of an ambient channel —
  -- never at the crossed binder's fresh names.  A φ guarding the ν's own pair
  -- (channel `` ` 0F ``/`` ` 1F ``) matches no rule and cannot escape.
  φ-comm′  : ∀ {x y c} {d : Tm n} →
             φ x c (φ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) P)
               ≋′ φ y d (φ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (P ⋯ₚ assocSwapᵣ 1 1))
  νφ-comm′ : ∀ {x} {c : Tm n} {P} →
             ν (φ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) P) ≋′ φ x c (ν (P ⋯ₚ assocSwapᵣ 1 2))
  ν-ext′   : P ∥ ν Q ≋′ ν ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) ∥ Q)
  φ-ext′   : ∀ {x c} → P ∥ φ x c Q ≋′ φ x c ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) ∥ Q)
  ∥-cong′  : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q
  ν-cong′  : P ≋′ Q → ν P ≋′ ν Q
  φ-cong′  : ∀ {x c} → P ≋′ Q → φ x c P ≋′ φ x c Q

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

  φ-cong : ∀ {x c} → P ≋ Q → φ x c P ≋ φ x c Q
  φ-cong = gmap (φ _ _) φ-cong′
