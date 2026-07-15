module BorrowedCF.Reduction.Processes.Typed where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
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
