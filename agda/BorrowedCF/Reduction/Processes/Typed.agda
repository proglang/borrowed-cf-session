module BorrowedCF.Reduction.Processes.Typed where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Functional as F using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Processes.Renamings
open import BorrowedCF.Types
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns

private variable
  b b₁ b₂ q : ℕ

infix 4 _─→ₚ_

data _─→ₚ_ {n} : Proc n → Proc n → Set where
  R-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

  R-New : (E : Frame* n) →
    ⟪ E [ K (`new s) ·¹ * ]* ⟫
      ─→ₚ
    ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      ⟪ E ⋯ᶠ* weaken* _ [ (` 0F) ⊗ (` 1F) ]* ⟫

  R-Fork : (E : Frame* n) (V : Value e) →
    ⟪ E [ K `fork ·¹ e ]* ⟫
      ─→ₚ
    ⟪ E [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫

  R-Com : ∀ {E₁ E₂} → Value e →
    let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
        ∥ ⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ n (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        ∥ (P ⋯ₚ wkρ))
      ─→ₚ
    ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ e ]* ⟫) ∥ P)

  R-Choice : ∀ E₁ E₂ i →
    let x = 0F in
    let y = wkʳ n (wkˡ (suc b₁ + sum B₁) 0F) in
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ [ K (`select i) ·¹ (` x) ]* ⟫
        ∥ ⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫)
        ∥ P)
      ─→ₚ
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ [ ` 0F ]* ⟫
        ∥ ⟪ E₂ [ `inj i (` y) ]* ⟫)
        ∥ P)

  R-LSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
    ν (B₁ ++ (q + suc b₁) ∷ B₂) B (⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ ∥ (P ⋯ₚ 𝐒.lwk))

  R-RSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
    ν (B₁ ++ (q + suc b₁) ∷ B₂) B (⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ⊗ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)) ]* ⟫ ∥ (P ⋯ₚ 𝐒.rwk))

  R-Drop : ∀ {E} →
    ν (suc b₁ ∷ B₁) B₂
      (⟪ E ⋯ᶠ* weakenᵣ [ K `drop ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (b₁ ∷ B₁) B₂
      (⟪ E [ * ]* ⟫ ∥ P)

  R-Acq : ∀ {E} →
    ν (zero ∷ suc b₁ ∷ B₁) B₂
      (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P)
      ─→ₚ
    ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ]* ⟫ ∥ P)

  R-Close : ∀ {E₁ E₂} →
    ν L.[ 1 ] L.[ 1 ]
      ( ⟪ E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
      ∥ ⟪ E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫
      )
      ─→ₚ
    ⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ * ]* ⟫

  R-Discard : ∀ {E} →
    ν (suc b₁ ∷ B₁) B₂
      (⟪ E ⋯ᶠ* weakenᵣ [ K `discard ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (b₁ ∷ B₁) B₂
      (⟪ E [ * ]* ⟫ ∥ P)

  R-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  R-Bind :
    P ─→ₚ Q →
    ν B₁ B₂ P ─→ₚ ν B₁ B₂ Q

  R-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q

open ≼-Reasoning

preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q
preservationₚ {Γ = Γ} {γ} Γ-S p (R-New {s = s} E)
  with e ← inv-⟪⟫ p
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , eq , ϵ≤ , ⊢E , ⊢new·* ← ⊢[]*⁻¹ E _ e
  with inv-·-unr ⊢new·* (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-new , γ-* , _ , ≤γ′ , ≤ₐ , refl , x , y
  with _ , eq₁ `→ eq₂ , []≤γ-new , `new N ← inv-K x
  with _ , _ , []≤γ-* , _ ← inv-K y
  = TP-Res N ⁇ (_ ∷ []) (_ ∷ [])
      {const ⟨ acq ; (s      ; end ⁇) ⟩}
      {const ⟨ acq ; (dual s ; end ‼) ⟩}
      (cons-acq (last (cons _ _ (λ{ (() ; _) }) ≃-skipʳ (λ{ 0F → refl }) (nil {Γ = λ()} skip))))
      (cons-acq (last (cons _ _ (λ{ (() ; _) }) ≃-skipʳ (λ{ 0F → refl }) (nil {Γ = λ()} skip))))
      (TP-Expr $ T-Conv eq ϵ≤ $ T-Weaken
        (begin  (𝒫 ⋯𝓅 𝐂.weaken* 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≡⟨ {!!} ⟩ -- mediate between Kₛ (top) and Kᵣ (bottom)
                (𝒫 ⋯𝓅 𝐂.weaken* 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≲⟨ pullOut-≼ (𝒫 ⋯𝓅 𝐂.weaken* 2) (` 0F ∥ ` 1F) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 ⋯𝓅 𝐂.weaken* 2) [ [] ]𝓅
                  ≡⟨ cong (_ ∥_) ([-]-dist-⋯ 𝒫 [] (𝐂.weaken* 2)) ⟨
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ [] ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥
                        (≼-refl refl)
                        (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _)
                               (𝐂.wk*-preserves {m = 2} _)
                               ([-]𝓅-≼ 𝒫 (≼-trans (≼-∅ ([] ∥ [])) (≼-cong-∥ []≤γ-* []≤γ-new))))
                   ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ-* ∥ γ-new ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _) (𝐂.wk*-preserves {m = 2} _) ([-]𝓅-≼ 𝒫 ≤γ′)) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ′ ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _) (𝐂.wk*-preserves {m = 2} _) ≤γ) ⟩
                (` 0F) ∥ (` 1F) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.;-unit₂ 𝐂.;-unit₂) refl ⟨
                (` 0F) ; [] ∥ ((` 1F) ; []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₂ 𝐂.∥-unit₂) refl ⟨
                (` 0F) ; [] ∥ [] ∥ ((` 1F) ; [] ∥ []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₁ 𝐂.∥-unit₁) refl ⟨
                [] ∥ ((` 0F) ; [] ∥ []) ∥ ([] ∥ ((` 1F) ; [] ∥ [])) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2) ∎)
        ⊢⟨ ⊢E ⊢⋯ᶠ* ⊢weaken* _ Γ [ T-Conv eq₂ ≤ₐ (T-Pair par par (T-Var 0F refl) (T-Var 1F refl)) ]*⟩)
preservationₚ {γ = γ} Γ-S p (R-Fork {e = e} E V)
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
preservationₚ Γ-S ⊢p (R-Com x) = {!!}
preservationₚ Γ-S ⊢p (R-Choice E₁ E₂ i) = {!!}
preservationₚ Γ-S ⊢p (R-LSplit {E = E}) = {!⊢p!}
preservationₚ Γ-S p (R-RSplit {B₁ = B₁′}{B₂′}{B}{b₁ = b₁} {E = E})
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  with α , β , ≤γ , ⟪Ersplit⟫ , q ← inv-∥ p′
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eq , ϵ≤ , ⊢E , ⊢rsplit·c ← ⊢[]*⁻¹ E _ (inv-⟪⟫ ⟪Ersplit⟫)
  with inv-·-unr ⊢rsplit·c (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-rsplit , γ-c , _ , ≤γ″ , ≤ₐ , refl , ⊢rsplit , ⊢c
  with _ , eq₁ `→ eq₂ , []≤γ-rsplit , `rsplit {s₁} ¬S₁ s₂ ← inv-K ⊢rsplit
  with eq-` , `c≤ ← inv-` ⊢c
  = {!!}
  {-
  TP-Res N pl (⊢ᴮ-rsplit B₁′ B₁) B₂
    (bindCtx-rsplit B₁′ B₂′
      (λ y → Γ₁ (Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂′))) (y ↑ˡ (suc b₁ + sum B₂′))))
      s₁ s₂
      (λ y → Γ₁ (Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂′))) (sum B₁′ ↑ʳ (suc y ↑ˡ sum B₂′))))
      (λ y → Γ₁ (Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂′))) (sum B₁′ ↑ʳ suc b₁ ↑ʳ y)))
      (≃-⟨⟩⁻¹ (≃-trans (≃-trans {!!} (≃-sym eq-`)) (≃-sym eq₁)))
      {!!}
      Γ₁≗
      (λ y → {!!})
      C₁)
    C₂
  $ TP-Par
    (TP-Expr $ T-Conv eq {!!} $ T-Weaken {!!}
      ⊢⟨ (⊢E ⊢⋯ᶠ* ⊢wkRSplit B₁′ B₂′ (sum B) {!Γ₁!} {!!} {!!} Γ₂ {!!} {!!} {!⊢fork·e!})
         [ T-Conv eq₂ ℙ≤ϵ (T-Pair par par
             (T-Var {!!} {!!})
             (T-Var {!!} {!!})) ]*⟩)
    (TP-Weaken {!!} (q ⊢⋯ₚ {!⊢wkRSplit B₁′ B₂′ _ !}))
  where
  Γ₁≗ : ∀ y → Γ₁ y ≡ _
  Γ₁≗ y = ?
  -}
preservationₚ Γ-S p (R-Drop {E = E})
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  with α , β , ≤γ , ⟪Edrop⟫ , q ← inv-∥ p′
  with ⊢Edrop ← inv-⟪⟫ ⟪Edrop⟫
  with 𝒫 , γ′ , _ , _ , _ , _ , 𝒫[γ′]≤ , eq , ϵ≤ , ⊢E , ⊢drop·c ← ⊢[]*⁻¹ (E ⋯ᶠ* weakenᵣ) _ ⊢Edrop
  with inv-·-unr ⊢drop·c (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-drop , γ-c , _ , γ-drop∥γ-c≤ , ↔ₐ , refl , ⊢drop , ⊢c
  with _ , eq₁ `→ eq₂ , []≤γ-drop , `drop ← inv-K ⊢drop
  with eq₃ , `c≤γ-c ← inv-` ⊢c
  with refl , B₁⁺ , C₁′ ← bindCtx-drop N {!!} C₁
  = let γ″ , γ″≤ , q′ = q ⊢≗ₚ sym ∘ ⸴-cons  ⊢⋯ₚ⁻¹ ⊢weaken _ in
    TP-Res N pl B₁ B₂ C₁′ C₂ $
      TP-Par
        (TP-Expr (T-Weaken {!!} (T-Conv {!!} {!!} ⊢⟨ {!⊢E!} [ {!!} ]*⟩)))
        {!TP-Weaken ? q′ ⊢≗ ?!}
preservationₚ Γ-S ⊢p R-Acq = {!!}
preservationₚ Γ-S ⊢p R-Close = {!!}
preservationₚ Γ-S p₀ (R-Par x)
  with α , β , ≤γ , p , q ← inv-∥ p₀
  = TP-Weaken ≤γ (TP-Par (preservationₚ Γ-S p x) q)
preservationₚ Γ-S ⊢p (R-Bind x) = {!!}
preservationₚ Γ-S p (R-Exp x)
  with e ← inv-⟪⟫ p
  = TP-Expr (preservation Γ-S e x)
preservationₚ Γ-S ⊢p (R-Struct eq₁ x eq₂) = {!!}
preservationₚ Γ-S p R-Discard
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  = TP-Res N pl B₁ B₂ {!C₁!} C₂ {!p′!}
