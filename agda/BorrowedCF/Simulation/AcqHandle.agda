{-# OPTIONS --rewriting #-}

-- HandleCount analogues for R-Acq: the consumed handle is 0F (position 0) of the
-- front bind group  zero @ suc b1 @ B1 , the simplest case of the split bookkeeping.

module BorrowedCF.Simulation.AcqHandle where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; cast)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed
  using (BindGroup; structBinder; structBinderWk; structBinder+²)
open import BorrowedCF.Simulation.Confine using (count)
open import BorrowedCF.Simulation.StructDom
  using (count-cast; count-structBinder-lt; count-weaken*-lo)

open import Data.Fin.Base using (_↑ʳ_)
open import Data.Fin.Properties using (toℕ-cast)

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; +-assoc; s≤s; z≤n)
open import Data.List using (_∷_)

count-handle-acq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} (γ : Struct m) →
  let C₁ = zero ∷ suc b₁ ∷ B₁ in
  count 0F
    ( structBinder+² (sum B₂) C₁
    ∥ structBinderWk (sum C₁) B₂
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B₂)) ) ≡ 1
count-handle-acq b₁ B₁ B₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = zero ∷ suc b₁ ∷ B₁
    0<C₁ : 0 < sum C₁
    0<C₁ = s≤s z≤n
    eqA : sum C₁ + (sum B₂ + m) ≡ sum C₁ + sum B₂ + m
    eqA = sym (+-assoc (sum C₁) (sum B₂) m)
    lt< : Fin.toℕ (Fin.cast (sym eqA) 0F) < sum C₁
    lt< = subst (_< sum C₁) (sym (toℕ-cast (sym eqA) 0F)) 0<C₁
    partA : count 0F (structBinder+² (sum B₂) C₁) ≡ 1
    partA = count-cast eqA (structBinder C₁) 0F
          ■ count-structBinder-lt C₁ (Fin.cast (sym eqA) 0F) lt<
    partB : count 0F (structBinderWk (sum C₁) B₂) ≡ 0
    partB = count-cast eqA (structBinder B₂ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁)) 0F
          ■ count-weaken*-lo (sum C₁) (structBinder B₂) (Fin.cast (sym eqA) 0F) lt<
    partC : count 0F (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum B₂) γ 0F (s≤s z≤n)

acqN-eq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} →
  0 + suc ((b₁ + sum B₁) + sum B₂ + m) ≡ sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m
acqN-eq b₁ B₁ B₂ = refl

mp≡handle-acq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} →
  Fin.cast (acqN-eq b₁ B₁ B₂ {m}) (0 ↑ʳ 0F) ≡ 0F
mp≡handle-acq b₁ B₁ B₂ = refl
