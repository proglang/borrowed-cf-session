module BorrowedCF.Reduction.Processes.Untyped where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions

open Variables
open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

infix 4 _─→ₚ_

data _─→ₚ_ {n} : Proc n → Proc n → Set where
  RU-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

  RU-Fork : (F : Frame* n) (V : Value e) →
    ⟪ F [ K `fork ·¹ e ]* ⟫
      ─→ₚ
    ⟪ F [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫

  RU-New : (F : Frame* n) →
    ⟪ F [ K (`new s) ·¹ * ]* ⟫
      ─→ₚ
    ν (φ acq (φ acq ⟪
      (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [
         𝓒[ ` 0F × 3F × * ] ⊗ 𝓒[ ` 1F × 2F × * ]
      ]*
    ⟫ ))

  RU-LSplit : (F : Frame* (2 + n)) →
    ν ( ⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ] ]* ⟫ ∥ P )
      ─→ₚ
    ν ( ⟪ F [ 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ] ]* ⟫ ∥ P )

  RU-RSplit : (F : Frame* (2 + n)) →
    ν (⟪ F [ K (`rsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ] ]* ⟫ ∥ P)
      ─→ₚ
    ν (φ drop (
      ⟪ (F ⋯ᶠ* weakenᵣ) [
           𝓒[ wk e₁ × 1F × ` 0F ]
             ⊗
           𝓒[ ` 0F × 1F × wk e₂ ]
        ]*
      ⟫ ∥ (P ⋯ₚ weakenᵣ)
    ))

  RU-Drop : (F : Frame* (1 + n)) {x : 𝔽 n} →
    φ drop (⟪ F [ K `drop ·¹ 𝓒[ e × suc x × ` 0F ] ]* ⟫ ∥ P)
      ─→ₚ
    φ acq (⟪ F [ * ]* ⟫ ∥ P)

  RU-Discard : (F : Frame* n) (V : Value e) →
    ⟪ F [ K `discard ·¹ e ]* ⟫ ─→ₚ ⟪ F [ * ]* ⟫

  RU-Acquire : (F : Frame* (3 + n)) →
    ν (φ acq (
      ⟪ F [ K `acq ·¹ 𝓒[ ` 0F × 1F × e ] ]* ⟫ ∥ P
    ))
      ─→ₚ
    ν ((⟪ F [ 𝓒[ ` 0F × 1F × e ] ]* ⟫ ∥ P) ⋯ₚ ⦅ * ⦆ₛ)

  RU-Close : ∀ (F₁ F₂ : Frame* n) {e₁ e₁′ e₂ e₂′} →
    ν ( ⟪ (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) ·¹ 𝓒[ e₁ × 0F × e₁′ ] ]* ⟫
      ∥ ⟪ (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) ·¹ 𝓒[ e₂ × 1F × e₂′ ] ]* ⟫ )
      ─→ₚ
    ⟪ F₁ [ * ]* ⟫ ∥ ⟪ F₂ [ * ]* ⟫

  RU-Com : ∀ (F₁ F₂ : Frame* (2 + n)) (V : Value e) {e₁ e₁′ e₂ e₂′} →
    ν (⟪ F₁ [ K `send ·¹ (e ⊗ 𝓒[ e₁ × 0F × e₁′ ]) ]* ⟫
      ∥ ( ⟪ F₂ [ K `recv ·¹ 𝓒[ e₂ × 1F × e₂′ ] ]* ⟫ ∥ P ) )
      ─→ₚ
    ν ( ⟪ F₁ [ * ]* ⟫ ∥ ( ⟪ F₂ [ e ]* ⟫ ∥ P ) )

  RU-Choice : ∀ (F₁ F₂ : Frame* (2 + n)) k {e₁ e₁′ e₂ e₂′} →
    ν ( ⟪ F₁ [ K (`select k) ·¹ 𝓒[ e₁ × 0F × e₁′ ] ]* ⟫
      ∥ ( ⟪ F₂ [ K `branch ·¹ 𝓒[ e₂ × 1F × e₂′ ] ]* ⟫
      ∥ P
    ))
      ─→ₚ
    ν ( ⟪ F₁ [ 𝓒[ e₁ × 0F × e₁′ ] ]* ⟫
      ∥ ( ⟪ F₂ [ `inj k 𝓒[ e₂ × 1F × e₂′ ] ]* ⟫
      ∥ P
    ))

  RU-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  RU-Res :
    P ─→ₚ Q →
    ν P ─→ₚ ν Q

  RU-Sync : ∀ {x} →
    P ─→ₚ Q →
    φ x P ─→ₚ φ x Q

  RU-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q
