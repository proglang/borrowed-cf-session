module BorrowedCF.ProcessesInv where

open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import BorrowedCF.Terms
open import BorrowedCF.TermsInv using (⊢⋯⁻¹; brₛ; ϕ-any⇐; Inj-↑ᵣ; lift-disg; σ≗ϕ)
open import BorrowedCF.DescendK using (descend-absK; wk^; wk^≡weaken*; Inj-↑*; freshᵏ; rlift)
open import BorrowedCF.Processes.Typed

open Nat.Variables

Inj-↑*ₜ : (k : ℕ) {ρ : m →ᵣ n} → 𝐂.Inj ρ → 𝐂.Inj (ρ ↑* k)
Inj-↑*ₜ zero    inj = inj
Inj-↑*ₜ (suc k) inj = Inj-↑ᵣ (Inj-↑*ₜ k inj)

lift-disg* : (k : ℕ) {ρ : m →ᵣ n} {σ : m 𝐂.→ₛ n} →
  σ ≗ (λ x → CB.`_ (ρ x)) → (σ 𝐂.↑* k) ≗ (λ x → CB.`_ ((rlift k ρ) x))
lift-disg* zero    eq = eq
lift-disg* (suc k) eq = lift-disg (lift-disg* k eq)

brₛ↑* : (k : ℕ) {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (k + m)) →
  γ 𝐂.⋯ (σ 𝐂.↑* k) ≡ γ 𝐂.⋯ᵣ (rlift k ϕ)
brₛ↑* k ⊢ϕ γ = 𝐂.⋯-cong γ (lift-disg* k (σ≗ϕ ⊢ϕ)) ■ 𝐂.conv-⋯ᵣₛ γ

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
⊢⋯ₚ⁻¹ {m = m} {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {γ = γ} {P = ν B₁ B₂ P} {ϕ = ϕ} inj p ⊢ϕ =
  let Γ₁ᵥ , Γ₂ᵥ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p′ = inv-ν p
      k = sum B₁ + sum B₂
      Δ = Γ₁ᵥ ⸴* Γ₂ᵥ
      Fr  = (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ m)
          ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ m)
      Fr′ = (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
          ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      γ′ , ≤γ , p″ = ⊢⋯ₚ⁻¹ (Inj-↑*ₜ k inj) p′ (⊢↑* Δ ⊢ϕ)
      ≤γᵣ = subst (λ z → (Δ ⸴* Γ₂) ∶ z ≼ _) (brₛ↑* k ⊢ϕ γ′) ≤γ
      ≼b = subst (λ z → (Δ ⸴* Γ₂) ∶ (γ′ 𝐂.⋯ᵣ (rlift k ϕ)) ≼ join 𝟙 Fr′ z)
             (sym (wk^≡weaken* k γ)) ≤γᵣ
      Frinv = cong₂ _∥_
               (𝐂.fusion (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ m) (rlift k ϕ)
                 ■ 𝐂.⋯-cong (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ k ϕ))
               (𝐂.fusion (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ m) (rlift k ϕ)
                 ■ 𝐂.⋯-cong (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ k ϕ))
      γr , part1 , part2 = descend-absK k Δ inj (ϕ-any⇐ ⊢ϕ) 𝟙 Fr Fr′ γ′ γ Frinv {!!} ≼b
      body = subst-γₚ (cong (join 𝟙 Fr) (wk^≡weaken* k γr)) (TP-Weaken part1 p″)
  in γr
   , ≼-respˡ-≈ (≈-reflexive (sym (brₛ ⊢ϕ γr))) part2
   , TP-Res N pol ⊢B₁ ⊢B₂ C C′ body
