{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction.Processes.Typed where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns

private variable
  b b₁ b₂ : ℕ


module SplitRenamings (B₁ B₂ B′ : BindGroup) where
  inj : 𝔽 (sum (B ++ B₂)) → 𝔽 (sum (B₁ ++ B ++ B₂) + sum B′ + n)
  inj {B} {n} z = Fin.cast (sym (sum-++ B₁ (B ++ B₂))) (sum B₁ ↑ʳ z) ↑ˡ sum B′ ↑ˡ n

  wk : sum (B₁ ++ suc b ∷ B₂) + sum B′ + n →ᵣ sum (B₁ ++ B ++ B₂) + sum B′ + n
  wk {B} {n} =
    Fin.cast (cong (λ m → m + sum B′ + n) (sym (sum-++ B₁ _)))
      ∘ {!? ↑* sum B₁!}
      ∘′ Fin.cast (cong (λ m → m + sum B′ + n) (sum-++ B₁ _))

infix 4 _─→ₚ_

data _─→ₚ_ {n} : Proc n → Proc n → Set where
  R-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

  R-New : (E : Frame n) →
    ⟪ E [ K (`new s) · K `unit ] ⟫
      ─→ₚ
    ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      ⟪ E ⋯ᶠ weaken* _ [ (` 0F) ⊗ (` 1F) ] ⟫

  R-Fork : (E : Frame n) (V : Value e) →
    ⟪ E [ K `fork · e ] ⟫
      ─→ₚ
    ⟪ E [ K `unit ] ⟫ ∥ ⟪ e · K `unit ⟫

  R-Com : ∀ {E₁ E₂} → Value e →
    let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ ⋯ᶠ wkρ [ K `send · ((` 0F) ⊗ (e ⋯ wkρ)) ] ⟫
        ∥ ⟪ E₂ ⋯ᶠ wkρ [ K `recv · (` {!weaken* ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (zero {?})!}) ] ⟫)
        ∥ (P ⋯ₚ wkρ))
      ─→ₚ
    ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((⟪ E₁ [ K `unit ] ⟫ ∥ ⟪ E₂ [ e ] ⟫) ∥ P)

  R-LSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ B in
    ν (B₁ ++ suc b₁ ∷ B₂) B (⟪ E [ K `lsplit · (` 𝐒.inj 0F) ] ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ suc (suc b₁) ∷ B₂) B (⟪ E ⋯ᶠ 𝐒.wk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ] ⟫ ∥ (P ⋯ₚ 𝐒.wk))

  R-RSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ B in
    ν (B₁ ++ suc b₁ ∷ B₂) B (⟪ E [ K `rsplit · (` 𝐒.inj 0F) ] ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B (⟪ E ⋯ᶠ 𝐒.wk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ] ⟫ ∥ (P ⋯ₚ 𝐒.wk))

  R-Drop : ∀ {E} →
    ν (suc b₁ ∷ B₁) B₂
      (⟪ E ⋯ᶠ weakenᵣ [ K `drop · (` 0F) ] ⟫ ∥ (P ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (b₁ ∷ B₁) B₂
      (⟪ E [ K `unit ] ⟫ ∥ P)

  R-Acq : ∀ {E} →
    ν (zero ∷ suc b₁ ∷ B₁) B₂
      (⟪ E [ K `acq · (` 0F) ] ⟫ ∥ P)
      ─→ₚ
    ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ] ⟫ ∥ P)

  R-Close : ∀ {E₁ E₂} →
    ν L.[ 1 ] L.[ 1 ]
      ( ⟪ E₁ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ _ [ K (`end ‼) · (` 0F) ] ⟫
      ∥ ⟪ E₂ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ _ [ K (`end ⁇) · (` 1F) ] ⟫
      )
      ─→ₚ
    ⟪ E₁ [ K `unit ] ⟫ ∥ ⟪ E₂ [ K `unit ] ⟫

  R-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  R-Bind :
    P ─→ₚ Q →
    ν B₁ B₂ P ─→ₚ ν B₁ B₂ Q

  R-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q
