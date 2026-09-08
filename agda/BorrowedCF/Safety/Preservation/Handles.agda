-- Preservation of process typing for the four handle-consuming reductions
-- R-Close, R-Discard, R-Drop and R-Acq.
module BorrowedCF.Safety.Preservation.Handles where

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

open import BorrowedCF.Safety.Preservation.Handles.Erase
open import BorrowedCF.Safety.Preservation.Handles.Frames
open import BorrowedCF.Safety.Preservation.Handles.BindCtx
open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (discard-handle-≃skip; drop-handle-≃ret)

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns
open ≼-Reasoning

private variable b₁ : ℕ

private
  -- the erased image of one `structBinder L.[ 1 ]` frame
  Z-≈ : {Γ : Ctx n} → Γ ∶ (([] ; []) ∥ []) ≈ []
  Z-≈ = ≈-trans 𝐂.∥-unit₂ 𝐂.;-unit₁

  isUnr : ∀ {c T U a ϵ} {Γ : Ctx n} {γ : Struct n} →
    Γ ; γ ⊢ K c ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.Unr a
  isUnr x = constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂)

-- R-Close
pres-Close : ChanCx Γ → ∀ {E₁ E₂ : Frame* n} →
  Γ ; γ ⊢ₚ ν L.[ 1 ] L.[ 1 ]
    ( ⟪ (E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) ·¹ (` 0F) ]* ⟫
    ∥ ⟪ (E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) ·¹ (` 1F) ]* ⟫ ) →
  Γ ; γ ⊢ₚ ⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ * ]* ⟫
pres-Close {Γ = Γ} {γ = γ} Γ-S {E₁} {E₂} ⊢P
  with Γ₁ , Γ₂ , _ , _ , _ , _ , _ , C , C′ , ⊢body ← inv-ν ⊢P
  with α , β , ≤αβ , ⊢th₁ , ⊢th₂ ← inv-∥ ⊢body
  with 𝒫₁ , γ₁′ , _ , _ , _ , _ , ≤α , eqT₁ , ϵ≤₁ , ⊢E₁ , ⊢app₁
    ← ⊢[]*⁻¹ (E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) _ (inv-⟪⟫ ⊢th₁)
  with 𝒫₂ , γ₂′ , _ , _ , _ , _ , ≤β , eqT₂ , ϵ≤₂ , ⊢E₂ , ⊢app₂
    ← ⊢[]*⁻¹ (E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) _ (inv-⟪⟫ ⊢th₂)
  with _ , _ , _ , _ , _ , _ , _ , ⊢fn₁ , _ ← inv-·-unr ⊢app₁ isUnr
  with _ , _ , _ , _ , _ , _ , _ , ⊢fn₂ , _ ← inv-·-unr ⊢app₂ isUnr
  with _ , _ `→ eqU₁ , _ , `end ← inv-K ⊢fn₁
  with _ , _ `→ eqU₂ , _ , `end ← inv-K ⊢fn₂
  = let ⊢wk = ⊢weaken* (Γ₁ ⸴* Γ₂) Γ
        inj = wk*-inj 2
        𝒫₁₀ , ≤𝒫₁ , ⊢E₁₀ = ⊢E₁ ⊢⋯ᶠ*⁻¹ ⊢wk / inj
        𝒫₂₀ , ≤𝒫₂ , ⊢E₂₀ = ⊢E₂ ⊢⋯ᶠ*⁻¹ ⊢wk / inj
    in TP-Weaken
        (begin
          𝒫₁₀ [ [] ]𝓅 ∥ 𝒫₂₀ [ [] ]𝓅
            ≲⟨ ≼-cong-∥ (plug-≼ 2 {𝒫 = 𝒫₁} {𝒫₀ = 𝒫₁₀} ≤𝒫₁ ≤α refl ⊢app₁)
                        (plug-≼ 2 {𝒫 = 𝒫₂} {𝒫₀ = 𝒫₂₀} ≤𝒫₂ ≤β refl ⊢app₂) ⟩
          (α 𝐂.⋯ er 2) ∥ (β 𝐂.⋯ er 2)
            ≲⟨ 𝐂.≼-⋯ (er-⇒ (Γ₁ ⸴* Γ₂)) ≤αβ ⟩
          ((([] ; []) ∥ []) ∥ (([] ; []) ∥ [])) ∥ ((γ 𝐂.⋯ᵣ 𝐂.weaken* 2) 𝐂.⋯ er 2)
            ≡⟨ cong (λ z → ((([] ; []) ∥ []) ∥ (([] ; []) ∥ [])) ∥ z) (er-wk 2 γ) ⟩
          ((([] ; []) ∥ []) ∥ (([] ; []) ∥ [])) ∥ γ
            ≈⟨ ≈-trans (𝐂.∥-cong (𝐂.∥-cong Z-≈ Z-≈) ≈-refl)
                       (≈-trans (𝐂.∥-cong 𝐂.∥-unit₁ ≈-refl) 𝐂.∥-unit₁) ⟩
          γ ∎)
        (TP-Par (TP-Expr (T-Conv eqT₁ ϵ≤₁ ⊢⟨ ⊢E₁₀ [ T-Conv eqU₁ ℙ≤ϵ (T-Const `unit) ]*⟩))
                (TP-Expr (T-Conv eqT₂ ϵ≤₂ ⊢⟨ ⊢E₂₀ [ T-Conv eqU₂ ℙ≤ϵ (T-Const `unit) ]*⟩)))


-- R-Discard
pres-Discard : ∀ {n} {Γ : Ctx n} {γ : Struct n} {b₁} → ChanCx Γ → ∀ {B₁ B₂}
  {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + n)} {P : Proc (sum (b₁ ∷ B₁) + sum B₂ + n)} →
  Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂
    (⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ)) →
  Γ ; γ ⊢ₚ ν (b₁ ∷ B₁) B₂ (⟪ E [ * ]* ⟫ ∥ P)
pres-Discard {n = n} {Γ = Γ} {γ = γ} {b₁ = b₁} Γ-S {B₁} {B₂} {E} {P} ⊢P
  with (T₁ ⸴ Γ₁) , Γ₂ , _ , pl , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with α , β , ≤αβ , ⊢th , ⊢Pw ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤α , eqT , ϵ≤ , ⊢E , ⊢app ← ⊢[]*⁻¹ (E ⋯ᶠ* weakenᵣ) _ (inv-⟪⟫ ⊢th)
  with _ , _ , _ , _ , _ , _ , _ , ⊢fn , _ ← inv-·-unr ⊢app isUnr
  with _ , _ `→ eqU , _ , `discard ← inv-K ⊢fn
  = let Δ′ = (Γ₁ ⸴* Γ₂) ⸴* Γ
        ⊢wk = ⊢weakenᵣ {T = T₁} Δ′
        𝒫₀ , ≤𝒫 , ⊢E₀ = ⊢E ⊢⋯ᶠ*⁻¹ ⊢wk / wk*-inj 1
        β₀ , ≤β , ⊢P₀ = ⊢Pw ⊢⋯ₚ⁻¹ ⊢wk / wk*-inj 1
        ⇒er = er-⇒ {k = 1} (T₁ ⸴ V.[]) {Γ = Δ′}
    in TP-Res N pl ⊢B₁ ⊢B₂ (bindCtx-discard (discard-handle-≃skip ⊢app) C) C′
        (TP-Weaken
          (≼-trans (≼-cong-∥ (plug-≼ 1 {Δ = T₁ ⸴ V.[]} {Γ = Δ′} {𝒫 = 𝒫} {𝒫₀ = 𝒫₀} ≤𝒫 ≤α refl ⊢app)
                             (≼-trans (≼-refl (≈-reflexive (sym (er-wkₛ 1 β₀)))) (𝐂.≼-⋯ ⇒er ≤β)))
          $ ≼-trans (𝐂.≼-⋯ ⇒er ≤αβ)
          $ ≼-refl (≈-trans
              (≈-reflexive (cong₂ _∥_
                (cong₂ _∥_ (cong₂ _∥_ (cong ([] ;_) (nseq-er b₁ B₁ B₂)) (tail-er b₁ B₁ B₂))
                           (grp₂-er b₁ B₁ B₂))
                (amb-er b₁ B₁ B₂ γ)))
              (𝐂.∥-cong (𝐂.∥-cong (𝐂.∥-cong 𝐂.;-unit₁ ≈-refl) ≈-refl) ≈-refl)))
          (TP-Par (TP-Expr (T-Conv eqT ϵ≤ ⊢⟨ ⊢E₀ [ T-Conv eqU ℙ≤ϵ (T-Const `unit) ]*⟩)) ⊢P₀))

-- R-Drop
pres-Drop : ∀ {n} {Γ : Ctx n} {γ : Struct n} {b₁} → ChanCx Γ → ∀ {B₁ B₂}
  {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + n)} {P : Proc (sum (b₁ ∷ B₁) + sum B₂ + n)} →
  Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂
    (⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ)) →
  Γ ; γ ⊢ₚ ν (b₁ ∷ B₁) B₂ (⟪ E [ * ]* ⟫ ∥ P)
pres-Drop {n = n} {Γ = Γ} {γ = γ} {b₁ = b₁} Γ-S {B₁} {B₂} {E} {P} ⊢P
  with (T₁ ⸴ Γ₁) , Γ₂ , _ , pl , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with α , β , ≤αβ , ⊢th , ⊢Pw ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤α , eqT , ϵ≤ , ⊢E , ⊢app ← ⊢[]*⁻¹ (E ⋯ᶠ* weakenᵣ) _ (inv-⟪⟫ ⊢th)
  with _ , _ , _ , _ , _ , _ , _ , ⊢fn , _ ← inv-·-unr ⊢app isUnr
  with _ , _ `→ eqU , _ , `drop ← inv-K ⊢fn
  = let Δ′ = (Γ₁ ⸴* Γ₂) ⸴* Γ
        ⊢wk = ⊢weakenᵣ {T = T₁} Δ′
        𝒫₀ , ≤𝒫 , ⊢E₀ = ⊢E ⊢⋯ᶠ*⁻¹ ⊢wk / wk*-inj 1
        β₀ , ≤β , ⊢P₀ = ⊢Pw ⊢⋯ₚ⁻¹ ⊢wk / wk*-inj 1
        ⇒er = er-⇒ {k = 1} (T₁ ⸴ V.[]) {Γ = Δ′}
    in TP-Res N pl ⊢B₁ ⊢B₂ (bindCtx-drop N (drop-handle-≃ret ⊢app) C) C′
        (TP-Weaken
          (≼-trans (≼-cong-∥ (plug-≼ 1 {Δ = T₁ ⸴ V.[]} {Γ = Δ′} {𝒫 = 𝒫} {𝒫₀ = 𝒫₀} ≤𝒫 ≤α refl ⊢app)
                             (≼-trans (≼-refl (≈-reflexive (sym (er-wkₛ 1 β₀)))) (𝐂.≼-⋯ ⇒er ≤β)))
          $ ≼-trans (𝐂.≼-⋯ ⇒er ≤αβ)
          $ ≼-refl (≈-trans
              (≈-reflexive (cong₂ _∥_
                (cong₂ _∥_ (cong₂ _∥_ (cong ([] ;_) (nseq-er b₁ B₁ B₂)) (tail-er b₁ B₁ B₂))
                           (grp₂-er b₁ B₁ B₂))
                (amb-er b₁ B₁ B₂ γ)))
              (𝐂.∥-cong (𝐂.∥-cong (𝐂.∥-cong 𝐂.;-unit₁ ≈-refl) ≈-refl) ≈-refl)))
          (TP-Par (TP-Expr (T-Conv eqT ϵ≤ ⊢⟨ ⊢E₀ [ T-Conv eqU ℙ≤ϵ (T-Const `unit) ]*⟩)) ⊢P₀))

------------------------------------------------------------------------
-- R-Acq.  Proved by agent P4b in `Handles/Acq.agda`; the probe that
-- justifies it (a mobile group head is alone in its group, so no
-- `∥′-tm-;` step is available at the acquired handle) is in
-- `Handles/AcqProbe.agda`.  See `Preservation/Acq-STATUS.md`.
------------------------------------------------------------------------

open import BorrowedCF.Safety.Preservation.Handles.Acq using (pres-Acq) public
