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

------------------------------------------------------------------------
-- φ-telescopes: the sync-cells that sit between a ν and its redex threads.
--
--   With the linked-φ design a cell cannot commute out of the ν that binds its
--   channel, so a channel operation must fire UNDER the φ-nest rather than
--   after floating it out.  Each channel rule below is quantified over an
--   arbitrary telescope `Φ`, and the ν-bound pair's channel indices are shifted
--   into the body scope by `wkΦ`.
------------------------------------------------------------------------

data Φ* : ℕ → ℕ → Set where
  []φ  : Φ* n n
  _◂_  : (Flag × Tm n) → Φ* (1 + n) k → Φ* n k

infixr 6 _◂_

plugΦ : Φ* n k → Proc k → Proc n
plugΦ []φ            P = P
plugΦ ((f , c) ◂ Φ) P = φ f c (plugΦ Φ P)

wkΦ : Φ* n k → n →ᵣ k
wkΦ []φ            = idₖ ⦃ Kᵣ ⦄
wkΦ ((f , c) ◂ Φ)  = weakenᵣ ·ₖ wkΦ Φ

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
    ν (φ acq (` 0F) (φ acq (` 2F) ⟪
      (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [
         𝓒[ ` 1F × 2F × * ] ⊗ 𝓒[ ` 0F × 3F × * ]
      ]*
    ⟫ ))

  RU-LSplit : ∀ {k} (Φ : Φ* (2 + n) k) (F : Frame* k) {e₁ e₂ : Tm k} {P : Proc k} →
    ν ( plugΦ Φ ( ⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × wkΦ Φ 0F × e₂ ] ]* ⟫ ∥ P ) )
      ─→ₚ
    ν ( plugΦ Φ ( ⟪ F [ 𝓒[ e₁ × wkΦ Φ 0F × * ] ⊗ 𝓒[ * × wkΦ Φ 0F × e₂ ] ]* ⟫ ∥ P ) )

  RU-RSplit : ∀ {k} (Φ : Φ* (2 + n) k) (F : Frame* k) {e₁ e₂ : Tm k} {P : Proc k} →
    ν ( plugΦ Φ ( ⟪ F [ K (`rsplit s) ·¹ 𝓒[ e₁ × wkΦ Φ 0F × e₂ ] ]* ⟫ ∥ P ) )
      ─→ₚ
    ν ( plugΦ Φ ( φ drop (` wkΦ Φ 0F) (
      ⟪ (F ⋯ᶠ* weakenᵣ) [
           𝓒[ wk e₁ × weakenᵣ (wkΦ Φ 0F) × ` 0F ]
             ⊗
           𝓒[ ` 0F × weakenᵣ (wkΦ Φ 0F) × wk e₂ ]
        ]*
      ⟫ ∥ (P ⋯ₚ weakenᵣ) ) ) )

  RU-Drop : ∀ {k} (Φ : Φ* (1 + n) k) (F : Frame* k) {x : 𝔽 n} {c : Tm n} {P : Proc k} →
    φ drop c ( plugΦ Φ ( ⟪ F [ K `drop ·¹ 𝓒[ * × wkΦ Φ (suc x) × ` wkΦ Φ 0F ] ]* ⟫ ∥ P ) )
      ─→ₚ
    φ acq c ( plugΦ Φ ( ⟪ F [ * ]* ⟫ ∥ P ) )

  RU-Discard : (F : Frame* n) (V : Value e) →
    ⟪ F [ K `discard ·¹ e ]* ⟫ ─→ₚ ⟪ F [ * ]* ⟫

  RU-Acquire : (F : Frame* (2 + n)) {c : Tm (2 + n)} →
    ν (φ acq c (
      ⟪ (F ⋯ᶠ* weakenᵣ) [ K `acq ·¹ 𝓒[ ` 0F × 1F × wk e ] ]* ⟫ ∥ (P ⋯ₚ weakenᵣ)
    ))
      ─→ₚ
    ν (⟪ F [ 𝓒[ * × 0F × e ] ]* ⟫ ∥ P)

  RU-Close : ∀ {k} (Φ : Φ* (2 + n) k) (F₁ F₂ : Frame* n) {e₁ e₁′ e₂ e₂′ : Tm k} →
    ν ( plugΦ Φ (
        ⟪ (F₁ ⋯ᶠ* (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ wkΦ Φ)) [ K (`end ‼) ·¹ 𝓒[ e₁ × wkΦ Φ 0F × e₁′ ] ]* ⟫
      ∥ ⟪ (F₂ ⋯ᶠ* (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ wkΦ Φ)) [ K (`end ⁇) ·¹ 𝓒[ e₂ × wkΦ Φ 1F × e₂′ ] ]* ⟫ ) )
      ─→ₚ
    ⟪ F₁ [ * ]* ⟫ ∥ ⟪ F₂ [ * ]* ⟫

  RU-Com : ∀ {k} (Φ : Φ* (2 + n) k) (F₁ F₂ : Frame* k) {e : Tm k} (V : Value e)
             {e₁ e₁′ e₂ e₂′ : Tm k} {P : Proc k} →
    ν ( plugΦ Φ ( ⟪ F₁ [ K `send ·¹ (e ⊗ 𝓒[ e₁ × wkΦ Φ 0F × e₁′ ]) ]* ⟫
      ∥ ( ⟪ F₂ [ K `recv ·¹ 𝓒[ e₂ × wkΦ Φ 1F × e₂′ ] ]* ⟫ ∥ P ) ) )
      ─→ₚ
    ν ( plugΦ Φ ( ⟪ F₁ [ * ]* ⟫ ∥ ( ⟪ F₂ [ e ]* ⟫ ∥ P ) ) )

  RU-Choice : ∀ {k′} (Φ : Φ* (2 + n) k′) (F₁ F₂ : Frame* k′) k
                {e₁ e₁′ e₂ e₂′ : Tm k′} {P : Proc k′} →
    ν ( plugΦ Φ ( ⟪ F₁ [ K (`select k) ·¹ 𝓒[ e₁ × wkΦ Φ 0F × e₁′ ] ]* ⟫
      ∥ ( ⟪ F₂ [ K `branch ·¹ 𝓒[ e₂ × wkΦ Φ 1F × e₂′ ] ]* ⟫
      ∥ P
    ) ) )
      ─→ₚ
    ν ( plugΦ Φ ( ⟪ F₁ [ 𝓒[ e₁ × wkΦ Φ 0F × e₁′ ] ]* ⟫
      ∥ ( ⟪ F₂ [ `inj k 𝓒[ e₂ × wkΦ Φ 1F × e₂′ ] ]* ⟫
      ∥ P
    ) ) )

  RU-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  RU-Par-right :
    Q ─→ₚ Q′ →
    P ∥ Q ─→ₚ P ∥ Q′

  RU-Res :
    P ─→ₚ Q →
    ν P ─→ₚ ν Q

  RU-Sync : ∀ {x c} →
    P ─→ₚ Q →
    φ x c P ─→ₚ φ x c Q

  RU-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q
