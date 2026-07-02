module BorrowedCF.ProcessesInv where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Terms
open import BorrowedCF.TermsInv using (⊢⋯⁻¹)
open import BorrowedCF.Processes.Typed

open Nat.Variables

⊢⋯ₚ⁻¹ : ∀ {m n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {γ} {P} {ϕ : m →ᵣ n} {σ} →
  𝐂.Inj ϕ → Γ₂ ; γ ⊢ₚ P ⋯ₚ ϕ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ₚ P
⊢⋯ₚ⁻¹ {P = ⟪ e ⟫} inj p ⊢ϕ =
  let γ′ , ≤γ , ⊢e′ = ⊢⋯⁻¹ inj (inv-⟪⟫ p) ⊢ϕ
  in γ′ , ≤γ , TP-Expr ⊢e′
⊢⋯ₚ⁻¹ {P = P ∥ Q} inj p ⊢ϕ =
  let α , β , ≤ , p₁ , p₂ = inv-∥ p
      α′ , ≤α , p₁′ = ⊢⋯ₚ⁻¹ inj p₁ ⊢ϕ
      β′ , ≤β , p₂′ = ⊢⋯ₚ⁻¹ inj p₂ ⊢ϕ
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≤α ≤β) ≤ , TP-Par p₁′ p₂′
⊢⋯ₚ⁻¹ {P = ν B₁ B₂ P} inj p ⊢ϕ = {!!}
