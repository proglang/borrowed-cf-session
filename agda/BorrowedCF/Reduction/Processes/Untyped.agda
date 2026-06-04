{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction.Processes.Untyped where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions

open Variables
open Fin.Patterns

infix 4 _─→ₚ_

data _─→ₚ_ {n} : Proc n → Proc n → Set where
  RU-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

  RU-Fork : (F : Frame* n) (V : Value e) →
    ⟪ F [ K `fork · e ]* ⟫
      ─→ₚ
    ⟪ F [ K `unit ]* ⟫ ∥ ⟪ e · K `unit ⟫

  RU-New : (F : Frame* n) →
    ⟪ F [ K (`new s) · K `unit ]* ⟫
      ─→ₚ
    ν (φ (φ
      ( ((1F ↦ set) ∥ (0F ↦ set))
      ∥ ⟪ (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4)
            [ (((` 1F) ⊗ (` 2F)) ⊗ K `unit) ⊗ (((` 0F) ⊗ (` 3F)) ⊗ K `unit) ]* ⟫ )))

  RU-LSplit : (F : Frame* n) {x : 𝔽 n} →
    ⟪ F [ K (`lsplit s) · (((e₁ ⊗ (` x)) ⊗ e₂)) ]* ⟫
      ─→ₚ
    ⟪ F [ (((e₁ ⊗ (` x)) ⊗ K `unit) ⊗ ((K `unit ⊗ (` x)) ⊗ e₂)) ]* ⟫

  RU-RSplit : (F : Frame* (2 + n)) {x : 𝔽 (2 + n)} →
    ν (⟪ F [ K (`rsplit s) · ((e₁ ⊗ (` x)) ⊗ e₂) ]* ⟫ ∥ P)
      ─→ₚ
    ν (φ ( (0F ↦ unset)
         ∥ ( ⟪ (F ⋯ᶠ* weakenᵣ)
                 [ (((e₁ ⋯ weakenᵣ) ⊗ (` suc x)) ⊗ (` 0F))
                 ⊗ (((` 0F) ⊗ (` suc x)) ⊗ (e₂ ⋯ weakenᵣ)) ]* ⟫
           ∥ (P ⋯ₚ weakenᵣ) ) ))

  RU-Drop : (F : Frame* (1 + n)) {x : 𝔽 (1 + n)} →
    φ ( (0F ↦ unset) ∥ (⟪ F [ K `drop · ((K `unit ⊗ (` x)) ⊗ (` 0F)) ]* ⟫ ∥ P) )
      ─→ₚ
    φ ( (0F ↦ set) ∥ (⟪ F [ K `unit ]* ⟫ ∥ P) )

  RU-Acquire : (F : Frame* (2 + n)) {x : 𝔽 (2 + n)} →
    ν (φ ( (0F ↦ set)
         ∥ ( ⟪ (F ⋯ᶠ* weakenᵣ) [ K `acq · (((` 0F) ⊗ (` suc x)) ⊗ (e ⋯ weakenᵣ)) ]* ⟫
           ∥ (P ⋯ₚ weakenᵣ) ) ))
      ─→ₚ
    ν (⟪ F [ (K `unit ⊗ (` x)) ⊗ e ]* ⟫ ∥ P)

  RU-Close : (F₁ F₂ : Frame* n) →
    ν ( ⟪ (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) · ((K `unit ⊗ (` 0F)) ⊗ K `unit) ]* ⟫
      ∥ ⟪ (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) · ((K `unit ⊗ (` 1F)) ⊗ K `unit) ]* ⟫ )
      ─→ₚ
    ⟪ F₁ [ K `unit ]* ⟫ ∥ ⟪ F₂ [ K `unit ]* ⟫

  RU-Com : (F₁ F₂ : Frame* (2 + n)) (V : Value e) →
    ν ( ⟪ F₁ [ K `send · (e ⊗ ((K `unit ⊗ (` 0F)) ⊗ e₁)) ]* ⟫
      ∥ ( ⟪ F₂ [ K `recv · ((K `unit ⊗ (` 1F)) ⊗ e₂) ]* ⟫ ∥ P ) )
      ─→ₚ
    ν ( ⟪ F₁ [ K `unit ]* ⟫ ∥ ( ⟪ F₂ [ e ]* ⟫ ∥ P ) )

  RU-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  RU-Res :
    P ─→ₚ Q →
    ν P ─→ₚ ν Q

  RU-Sync :
    P ─→ₚ Q →
    φ P ─→ₚ φ Q

  RU-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q
