{-# OPTIONS --allow-unsolved-metas #-}   -- WIP preservationₚ (user-owned); isolates its holes so _─→ₚ_ imports
module BorrowedCF.Reduction.Processes.Typed where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Functional as F using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.TermsInv using (_⊢⋯⁻¹_/_)
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

{-
bindCtx-drop : ∀ {b} {Γ} → New s → Γ 0F ≃ ⟨ ret ⟩ → BindCtx (s ; end p) (suc b ∷ B) Γ →
  b ≡ 0 × B ≢ [] × BindCtx (s ; end p) (0 ∷ B) λ x → Γ (suc b ↑ʳ x)
bindCtx-drop {Γ = Γ} N eq (last (cons _ _ ¬skips s≃ Γ≗ x))
  with ⟨ eq′ ⟩ ← ≃-trans (≃-reflexive (Γ≗ zero)) eq
  = let ret;s₂≃s;end = ≃-trans (≃-sym (≃-; eq′ ≃-refl)) s≃ in
    -- ret;s₂ ≃ s;end  ==> derive ∃s′.  ret;x ≃ s /\ x;end ≃ s₂  ==> conclude New (ret;x) !!!
    {!atom-;-unsnoc!}
bindCtx-drop N eq (cons-ret/acq _ s≃ Γ≗ (cons _ _ ¬skips s≃′ Γ′≗ (nil x)) C)
  with ⟨ eq′ ⟩ ← ≃-trans (≃-reflexive (Γ′≗ zero ■ Γ≗ zero)) eq
  = let foo = ≃-trans s≃′ {!≃-; {!!} {!!}!} in
    refl , (λ { refl → bindCtx-B≢[] C })
         , cons-acq (bindCtx-Γ≗ (Γ≗ ∘ suc) (bindCtx-≃ (≃-; refl (≃-trans {!!} s≃)) C))
bindCtx-drop N eq (cons-ret/acq _ s≃₁ Γ₁≗ (cons _ _ ¬skips₂ s≃₂ Γ₂≗ (cons _ _ ¬skips₃ s≃₃ Γ₃≗ x)) C)
  with ⟨ eq′ ⟩ ← ≃-trans (≃-reflexive (Γ₂≗ zero ■ Γ₁≗ zero)) eq
  = {!s≃₁!}
-}

{-
bindCtx-rsplit : ∀ (B₁ B₂ : BindGroup) (Γ₁ : Ctx (sum B₁)) (s₁ s₂ : 𝕊 0) (Γₙ : Ctx n) (Γ₂ : Ctx (sum B₂)) {Γ Γ′} →
  s′ ≃ s₁ ; s₂ →
  ¬ Skips s₂ →
  Γ ≗ (Γ₁ ⸴* ⟨ s′ ⟩ ⸴ Γₙ ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ _) →
  Γ′ ≗ (Γ₁ ⸴* ⟨ s₁ ; ret ⟩ ⸴ ⟨ acq ; s₂ ⟩ ⸴ Γₙ ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ _) →
  BindCtx s (B₁ ++ suc n ∷ B₂) Γ →
  BindCtx s (B₁ ++ 1 ∷ suc n ∷ B₂) Γ′
bindCtx-rsplit [] B₂ Γ₁ s₁ s₂ Γₙ Γ₂ s′-split ¬S₂ Γ-eq Γ′-eq (last (cons s′ s″ ¬skips s-split s′-cons x))
  with refl ← s′-cons 0F ■ Γ-eq 0F =
  cons-ret/acq s₁ {s₂ ; s″}
    (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; (≃-sym s′-split) refl) s-split))
    (λ{ 0F → sym (Γ′-eq 0F); (suc y) → sym (cong (⟨ acq ; s₂ ⟩ ⸴ (Γₙ ⸴* Γ₂)) (Fin.cast-is-id refl y)) ■ sym (Γ′-eq (suc y)) })
    (cons (s₁ ; ret) skip (λ{ (_ ; ()) }) ≃-skipʳ (λ _ → refl) (nil {Γ = F.[]} skip))
    (last (cons (acq ; s₂) s″ (λ{ (() ; _) }) ≃-assoc-; (λ{ 0F → refl; (suc y) → s′-cons (suc y) ■ Γ-eq (suc y ↑ˡ 0) ■ cong (Γₙ ⸴* Γ₂) (Fin.cast-is-id refl _) }) x))
bindCtx-rsplit {n = n} [] B₂ Γ₁ s₁ s₂ Γₙ Γ₂ s′-split ¬S₂ Γ-eq Γ′-eq
  (cons-ret/acq s-here {s-there} here;there≃s Γ≗ (cons s′ s″ _ here-split s′-cons x) C)
  with refl ← s′-cons 0F ■ Γ≗ 0F ■ Γ-eq 0F
  with atom-;-unsnoc ret here-split
... | inj₁ skips-s″ = {!!} -- should be a contradiction: Skips s″ implies s′ ends in `ret`
... | inj₂ (prfx , s′+prfx , prfx+ret) =
  cons-ret/acq s₁ {s₂ ; prfx ; s-there}
    (≃-trans (≃-sym ≃-assoc-;)
      $ ≃-trans (≃-; (≃-trans (≃-sym ≃-assoc-;) (≃-; (≃-sym s′-split) refl)) refl)
      $ ≃-trans (≃-; s′+prfx refl)
      $ here;there≃s)
    (λ{ 0F → sym (Γ′-eq 0F); 1F → sym (Γ′-eq 1F); (suc (suc y)) →
        [-,]-cong (s′-cons ∘ suc) (splitAt _ y)
          ■ sym ([,]-map (splitAt n y))
          ■ Γ≗ (suc y) ■ Γ-eq (suc y) ■ sym (Γ′-eq (suc (suc y)))
    })
    (cons (s₁ ; ret) skip (λ{ (_ ; ()) }) ≃-skipʳ (λ _ → refl) (nil {Γ = F.[]} skip))
    (cons-ret/acq (acq ; (s₂ ; prfx)) ≃-assoc-; (⸴-⸴*-assoc ⟨ acq ; s₂ ⟩ _ _)
      (cons (acq ; s₂) s″ {Γ = ⟨ (acq ; s₂) ⟩ ⸴ _} (λ{ (_ ; ()) })
        (≃-trans (≃-; refl (≃-sym prfx+ret))
          $ ≃-trans (≃-sym ≃-assoc-;)
          $ ≃-; ≃-assoc-; refl)
        (λ _ → refl)
        x)
      C)
bindCtx-rsplit (b₁ ∷ B₁) B₂ Γ₁ s₁ s₂ Γₙ Γ₂ {Γ = Γ} s′-split ¬S₂ Γ-eq Γ′-eq C
  with bindCtx-inv-cons (subst (0 Nat.<_) (sym (Nat.+-comm (L.length B₁) _) ■ sym (L.length-++ B₁)) Nat.z<s) C
... | inj₁ (_ , _ , Γ₁′ , Γ₂′ , s≃ , Γ≗ , x , C′) = cons-ret/acq _ s≃ {!!} x $
  bindCtx-rsplit B₁ B₂ (λ y → Γ₁ (b₁ ↑ʳ y)) s₁ s₂ Γₙ Γ₂ s′-split ¬S₂
    (λ y → cong [ Γ₁′ , Γ₂′ ] (sym (splitAt-↑ʳ b₁ _ y)) ■ Γ≗ (b₁ ↑ʳ y) ■ Γ-eq (b₁ ↑ʳ y) ■ {!!})
    (λ y → {!Γ′-eq (b₁ ↑ʳ y)!})
    C′
... | inj₂ (refl , C′) = cons-acq $
  bindCtx-rsplit B₁ B₂ Γ₁ s₁ s₂ Γₙ Γ₂ s′-split ¬S₂
    (λ x → cong Γ (Fin.cast-is-id refl x) ■ Γ-eq x)
    Γ′-eq
    C′
-}

open ≼-Reasoning

preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q
preservationₚ {Γ = Γ} {γ} Γ-S p (R-New {s = s} E) = {!!}
{- TINY HOLE
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
-}
preservationₚ {γ = γ} Γ-S p (R-Fork {e = e} E V) = {!!}
{- DONE
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
-}
preservationₚ {Γ = Γ} Γ-S p (R-Com {b₁ = b₁}{B₁ = B₁}{b₂ = b₂}{B₂ = B₂} {E₁ = E₁}{E₂} Vv)
  using wkρ ← wkₚ (b₁ + sum B₁) (b₂ + sum B₂)
  with Γ₁ , Γ₂ , _ , pl , N , ⊢B₁ , ⊢B₂ , C₁ , C₂ , p′ ← inv-ν p
  with αβ , γ , αβγ≤ , p″ , q ← inv-∥ p′
  with α , β , αβ≤ , p₁ , p₂ ← inv-∥ p″
  with 𝓟₁ , α′ , _ , _ , _ , _ , ≤α , eq₁ , ϵ≤₁ , ⊢E₁ , ⊢send·vc₁ ← ⊢[]*⁻¹ (E₁ ⋯ᶠ* wkρ) _ (inv-⟪⟫ p₁)
  with 𝓟₂ , β′ , _ , _ , _ , _ , ≤β , eq₂ , ϵ≤₂ , ⊢E₂ , ⊢recv·c₂  ← ⊢[]*⁻¹ (E₂ ⋯ᶠ* wkρ) _ (inv-⟪⟫ p₂)
  with a₁ , α-send , α-vc₁ , _ , ≤α′ , ≤a₁ , refl , ⊢send , ⊢vc₁
    ← inv-·-unr ⊢send·vc₁ (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with a₂ , β-recv , β-c₂ , _ , ≤β′ , ≤a₂ , refl , ⊢recv , ⊢c₂
    ← inv-·-unr ⊢recv·c₂ (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , (T≃₁ ⊗ ⟨ ‼T≃ ⟩) `→ ‵⊤≃ , []≤α-send , `send MT₁ ← inv-K ⊢send
  with _ , ⟨ ⁇T≃ ⟩ `→ T≃₂ , []≤β-recv , `recv MT₂ ← inv-K ⊢recv
  with p/s , α-v , α-c₁ , _ , _ , _ , _ , ≤α-vc₁ , vc₁≈ , ϵ≤₁′ , seq⇒p , ⊢v , ⊢c₁ ← inv-⊗ ⊢vc₁
  with eq-c₁ , `c₁≤ ← inv-` ⊢c₁
  with eq-c₂ , `c₂≤ ← inv-` ⊢c₂
  = let ⊢wkρ = ⊢wkₚ (Γ₁ ∘ suc) (Γ₂ ∘ suc) Γ {Γ₁ 0F} {Γ₂ 0F} in
    let Γ-eq = {!!} in
    let γ′ , ≤γ , q′ = q ⊢≗ₚ Γ-eq ⊢⋯ₚ⁻¹ ⊢wkρ in
    let 𝒫₁′ , 𝒫₁≡ , ⊢E₁′ = ⊢E₁ ⊢≗ᶠ* Γ-eq ⊢⋯ᶠ*⁻¹ ⊢wkρ in
    let 𝒫₂′ , 𝒫₂≡ , ⊢E₂′ = ⊢E₂ ⊢≗ᶠ* Γ-eq ⊢⋯ᶠ*⁻¹ ⊢wkρ in
    let α-v′ , α-v′≤ , ⊢v′ = ⊢v ⊢≗ Γ-eq ⊢⋯⁻¹ ⊢wkρ / wkₚ-inj (b₁ + sum B₁) (b₂ + sum B₂) _ in
    let s₁′ , ‼T;s₁′≃ , C₁′ = bindCtx-inv-msg (≃-trans (≃-sym eq-c₁) (≃-trans (≃-⊗⁻¹ vc₁≈ .proj₂ .proj₂) ⟨ ≃-sym ‼T≃ ⟩)) C₁ in
    let _ , ⁇T;s₂′≃ , C₂′ = bindCtx-inv-msg
          (≃-trans (≃-reflexive (sym (cong ([ Γ₁ , Γ₂ ] ∘ Sum.map₁ suc) (splitAt-↑ʳ (b₁ + sum B₁) _ 0F))
                                   ■ sym (cong ([ Γ₁ ⸴* Γ₂ , Γ ] ∘ Sum.map₁ suc)
                                               (splitAt-↑ˡ (b₁ + sum B₁ + (suc b₂ + sum B₂)) (b₁ + sum B₁ ↑ʳ 0F) _))))
                   (≃-trans (≃-sym eq-c₂) ⟨ ≃-sym ⁇T≃ ⟩)) C₂
    in
    TP-Res {!!} pl ⊢B₁ ⊢B₂ (bindCtx-≃ {!!} C₁′) (bindCtx-≃ {!!} C₂′)
      $ TP-Weaken {!!}
      $ TP-Par
          (TP-Par
            (TP-Expr (T-Conv eq₁ ϵ≤₁ ⊢⟨ ⊢E₁′ [ T-Conv ‵⊤≃ ℙ≤ϵ (T-Const `unit) ]*⟩))
            (TP-Expr (T-Conv eq₂ ϵ≤₂ ⊢⟨ ⊢E₂′ [
              T-Conv (≃-trans (≃-⊗⁻¹ vc₁≈ .proj₁) (≃-trans (≃-sym T≃₁) (≃-trans {!!} T≃₂))) ℙ≤ϵ
                (value⇒pure Vv ⊢v′)
            ]*⟩)))
          q′
preservationₚ Γ-S ⊢p (R-Choice E₁ E₂ i) = {!!}
preservationₚ Γ-S ⊢p (R-LSplit {E = E}) = {!⊢p!}
preservationₚ Γ-S p (R-RSplit {B₁ = B₁′}{B₂′}{B}{b₁ = b₁} {E = E}) = {!!}
{-
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  with α , β , ≤γ , ⟪Ersplit⟫ , q ← inv-∥ p′
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eq , ϵ≤ , ⊢E , ⊢rsplit·c ← ⊢[]*⁻¹ E _ (inv-⟪⟫ ⟪Ersplit⟫)
  with inv-·-unr ⊢rsplit·c (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-rsplit , γ-c , _ , ≤γ″ , ≤ₐ , refl , ⊢rsplit , ⊢c
  with _ , eq₁ `→ eq₂ , []≤γ-rsplit , `rsplit s₁ s₂ ← inv-K ⊢rsplit
  with eq-` , `c≤ ← inv-` ⊢c
  = {!!}
  -}
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
preservationₚ Γ-S p (R-Drop {E = E}) = {!!}
{-
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
    -}
preservationₚ Γ-S ⊢p R-Acq = {!!}
preservationₚ Γ-S ⊢p R-Close = {!!}
preservationₚ Γ-S p₀ (R-Par x) = {!!} -- with α , β , ≤γ , p , q ← inv-∥ p₀ = TP-Weaken ≤γ (TP-Par (preservationₚ Γ-S p x) q)
preservationₚ Γ-S ⊢p (R-Bind x) = {!!}
preservationₚ Γ-S p (R-Exp x)
  with e ← inv-⟪⟫ p
  = TP-Expr (preservation Γ-S e x)
preservationₚ Γ-S ⊢p (R-Struct eq₁ x eq₂) = {!!}
preservationₚ Γ-S p R-Discard = {!!} -- with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p = TP-Res N pl B₁ B₂ {!C₁!} C₂ {!p′!}
