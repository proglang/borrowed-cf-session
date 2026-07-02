module BorrowedCF.ProcessesInv where

open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Terms
open import BorrowedCF.TermsInv using (⊢⋯⁻¹; brₛ; ϕ-any⇐)
open import BorrowedCF.DescendK using (descend-absK; wk^; wk^≡weaken*; Inj-↑*; freshᵏ)
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

{- ν-case assembly (BLOCKED on term-vs-𝐂 ↑* instance clash — needs k-ary Inj-↑*ᵣ + brₛ↑* bridge,
   analogous to the term-level Inj-↑ᵣ/brₛ↑ solution; plus Frinv via 𝐂.wkʳ-cancels-↑* and
   Frdom via dom(structBinder⋯wkʳ) ⊆ freshᵏ):

⊢⋯ₚ⁻¹ {m = m} {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {γ = γ} {P = ν B₁ B₂ P} {ϕ = ϕ} inj p ⊢ϕ =
  let Γ₁ᵥ , Γ₂ᵥ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p′ = inv-ν p
      k = sum B₁ + sum B₂
      Δ = Γ₁ᵥ ⸴* Γ₂ᵥ
      Fr  = (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ m)
          ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ m)
      Fr′ = (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
          ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      γ′ , ≤γ , p″ = ⊢⋯ₚ⁻¹ (Inj-↑* k inj) p′ (⊢↑* Δ ⊢ϕ)
      ≤γᵣ = subst (λ z → (Δ ⸴* Γ₂) ∶ z ≼ _) (brₛ (⊢↑* Δ ⊢ϕ) γ′) ≤γ
      ≼b = subst (λ z → (Δ ⸴* Γ₂) ∶ (γ′ 𝐂.⋯ (ϕ 𝐂.↑* k)) ≼ join 𝟙 Fr′ z)
             (sym (wk^≡weaken* k γ)) ≤γᵣ
      γr , part1 , part2 = descend-absK k Δ inj (ϕ-any⇐ ⊢ϕ) 𝟙 Fr Fr′ γ′ γ {!!} {!!} ≼b
      body = subst-γₚ (cong (join 𝟙 Fr) (wk^≡weaken* k γr)) (TP-Weaken part1 p″)
  in γr
   , ≼-respˡ-≈ (≈-reflexive (sym (brₛ ⊢ϕ γr))) part2
   , TP-Res N pol ⊢B₁ ⊢B₂ C C′ body
-}
