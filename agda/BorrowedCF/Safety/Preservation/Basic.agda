-- Preservation of process typing for the "basic" reductions R-Exp, R-New, R-Fork.
module BorrowedCF.Safety.Preservation.Basic where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns
open ≼-Reasoning

-- R-Exp
pres-Exp : ChanCx Γ → e₁ ⋯→ e₂ → Γ ; γ ⊢ₚ ⟪ e₁ ⟫ → Γ ; γ ⊢ₚ ⟪ e₂ ⟫
pres-Exp Γ-S x p = TP-Expr (preservation Γ-S (inv-⟪⟫ p) x)

-- R-Fork
pres-Fork : ChanCx Γ → ∀ (E : Frame* n) (V : Value e) →
  Γ ; γ ⊢ₚ ⟪ E [ K `fork ·¹ e ]* ⟫ →
  Γ ; γ ⊢ₚ ⟪ E [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫
pres-Fork {γ = γ} Γ-S E V p
  with ⟪e⟫ ← inv-⟪⟫ p
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , eq , ϵ≤ , ⊢E , ⊢fork·e ← ⊢[]*⁻¹ E _ ⟪e⟫
  with inv-·-unr ⊢fork·e (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-fork , γ-e , _ , ≤γ′ , ≤ₐ , refl , ⊢fork , ⊢e
  with _ , eq₁ `→ eq₂ , []≤γ-fork , `fork ← inv-K ⊢fork
  = TP-Weaken
      (begin  𝒫 [ [] ]𝓅 ∥ (γ-e ∥ [])  ≈⟨ 𝐂.∥-comm ⟩
              (γ-e ∥ []) ∥ 𝒫 [ [] ]𝓅  ≈⟨ pullOutMobile 𝒫 (inv-mob V (arr refl) (T-Conv (≃-sym eq₁) ≤ϵ-refl ⊢e) ∥ []) ⟨
              𝒫 [ γ-e ∥ [] ]𝓅         ≲⟨ [-]𝓅-≼ 𝒫 (≼-cong-∥ (≼-refl refl) []≤γ-fork) ⟩
              𝒫 [ γ-e ∥ γ-fork ]𝓅     ≲⟨ [-]𝓅-≼ 𝒫 ≤γ′ ⟩
              𝒫 [ γ′ ]𝓅               ≲⟨ ≤γ ⟩
              γ ∎)
      (TP-Par (TP-Expr (T-Conv eq ϵ≤ ⊢⟨ ⊢E [ T-Conv eq₂ ≤ₐ (T-Const `unit) ]*⟩))
              (TP-Expr (T-AppLin (refl , refl) 𝕀≤𝕀 (T-Conv (≃-sym eq₁) (𝕀-maximum _) ⊢e) (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)))))

private
  -- The frame typing produced by `⊢weaken*` carries the *substitution* kit,
  -- while the reduct's frame is renamed.  This bridges the two.
  ⋯𝓅-wk-conv : ∀ k (𝒫 : CxPat m) →
    𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k ≡ 𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ k
  ⋯𝓅-wk-conv k [] = refl
  ⋯𝓅-wk-conv k ((d , γ) ∷ 𝒫) =
    cong₂ _∷_
      (cong (d ,_) (𝐂.⋯-congᶜ ⦃ 𝐂.Kₛ ⦄ ⦃ 𝐂.Kᵣ ⦄ γ
        λ y → 𝐂.weaken*~wkˡ k y ■ cong `_ (sym (𝐂.weaken*~wkˡ k y))))
      (⋯𝓅-wk-conv k 𝒫)

-- R-New
pres-New : ChanCx Γ → ∀ {s} (E : Frame* n) →
  Γ ; γ ⊢ₚ ⟪ E [ K (`new s) ·¹ * ]* ⟫ →
  Γ ; γ ⊢ₚ ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) ⟪ E ⋯ᶠ* weaken* _ [ (` 0F) ⊗ (` 1F) ]* ⟫
pres-New {Γ = Γ} {γ = γ} Γ-S {s = s} E p
  with e ← inv-⟪⟫ p
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , eq , ϵ≤ , ⊢E , ⊢new·* ← ⊢[]*⁻¹ E _ e
  with inv-·-unr ⊢new·* (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-new , γ-* , _ , ≤γ′ , ≤ₐ , refl , x , y
  with _ , eq₁ `→ eq₂ , []≤γ-new , `new N ← inv-K x
  with _ , _ , []≤γ-* , _ ← inv-K y
  = let Δ : Ctx 2
        Δ = ⟨ acq ; (s ; end ⁇) ⟩ ⸴ ⟨ acq ; (dual s ; end ‼) ⟩ ⸴ []
        wk⇒ = 𝐂.⇔→⇒ ⦃ 𝐂.Kᵣ ⦄ {Γ} (𝐂.wk*-⇔ ⦃ 𝐂.Kᵣ ⦄ Δ)
    in
    TP-Res N ⁇ (_ ∷ []) (_ ∷ [])
      (cons-acq (last (cons _ _ (λ{ (() ; _) }) ≃-skipʳ (nil skip))) (_ , ≃-refl))
      (cons-acq (last (cons _ _ (λ{ (() ; _) }) ≃-skipʳ (nil skip))) (_ , ≃-refl))
      (TP-Expr $ T-Conv eq ϵ≤ $ T-Weaken
        (begin  (𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≡⟨ cong (_[ (` 0F) ∥ (` 1F) ]𝓅) (⋯𝓅-wk-conv 2 𝒫) ⟩
                (𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≲⟨ pullOut-≼ (𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ 2) (` 0F ∥ ` 1F) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ 2) [ [] ]𝓅
                  ≡⟨ cong (_ ∥_) ([-]-dist-⋯ 𝒫 [] (𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ 2)) ⟨
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ [] ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥
                        (≼-refl refl)
                        (𝐂.≼-⋯ wk⇒
                               ([-]𝓅-≼ 𝒫 (≼-trans (≼-∅ ([] ∥ [])) (≼-cong-∥ []≤γ-* []≤γ-new))))
                   ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ-* ∥ γ-new ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ wk⇒ ([-]𝓅-≼ 𝒫 ≤γ′)) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ′ ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ wk⇒ ≤γ) ⟩
                (` 0F) ∥ (` 1F) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.;-unit₂ 𝐂.;-unit₂) refl ⟨
                (` 0F) ; [] ∥ ((` 1F) ; []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₂ 𝐂.∥-unit₂) refl ⟨
                (` 0F) ; [] ∥ [] ∥ ((` 1F) ; [] ∥ []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₁ 𝐂.∥-unit₁) refl ⟨
                [] ∥ ((` 0F) ; [] ∥ []) ∥ ([] ∥ ((` 1F) ; [] ∥ [])) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2) ∎)
        ⊢⟨ ⊢E ⊢⋯ᶠ* ⊢weaken* _ Γ [ T-Conv eq₂ ≤ₐ (T-Pair par par (T-Var 0F refl) (T-Var 1F refl)) ]*⟩)
