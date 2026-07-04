module BorrowedCF.Simulation.RevAcq where

-- Reverse RU-Acquire: an untyped acquire fires only on a SINGLE-φ telescope
-- ν (φ acq (thread ∥ rest)) whose cell is the group-1 acq marker
-- (B₁ = 0 ∷ suc c' ∷ [], B₂ = b₂ ∷ []); the mirror shape with the cell in
-- group 2 is refuted by the handle-triple's slots.  The typed step is R-Acq
-- (no renaming), and the codomain recon collapses the cell substitution
-- ⦅ * ⦆ₛ into the φ-free leaf substitution.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; close-arg-var; head⊗′)
open import BorrowedCF.Simulation.RevUCong using (U-not-φ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋; U-cong; Ub-V)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Theorems.SplitsH2 using (frame*-cong)
open import BorrowedCF.Simulation.Theorems using (frame-fusion-gen)
open import BorrowedCF.Simulation.Theorems.Acq using (U-σ⋯ₛ)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Base using (NonZero)
open T using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)
open import Data.List.Relation.Unary.All as All using (All)

open Fin.Patterns

private
  nonZero⇒suc : ∀ {c} → NonZero c → Σ[ c' ∈ ℕ ] c ≡ suc c'
  nonZero⇒suc {suc c'} _ = c' , refl

  V⦅*⦆ : ∀ {k} → VSub (⦅_⦆ₛ {n = k} *)
  V⦅*⦆ 0F      = V-K
  V⦅*⦆ (Fin.suc x) = V-`

  φ-inj : ∀ {k} {f g : U.Flag} {X Y : U.Proc (suc k)} →
          U.φ f X ≡ U.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-inj refl = refl , refl

  ν-injU : ∀ {k} {X Y : U.Proc (2 + k)} → U.ν X ≡ U.ν Y → X ≡ Y
  ν-injU refl = refl

  ∥-injU : ∀ {k} {A B C D : U.Proc k} → (A U.∥ B) ≡ (C U.∥ D) → (A ≡ C) × (B ≡ D)
  ∥-injU refl = refl , refl

------------------------------------------------------------------------
-- The single-φ acq leaf substitution (the shape U[ ν (0∷suc c'∷[]) (b₂∷[]) ]
-- reduces to) and its ⦅ * ⦆ₛ-collapse onto the φ-free reduct substitution.
------------------------------------------------------------------------

νσᵃ : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) → (suc (c' + 0) + (b₂ + 0) + m) →ₛ (3 + n)
νσᵃ c' b₂ σ =
  ((λ i → Ub[ suc (c' + 0) ] ((` 0F) , 1F , *) i ⋯ weaken* ⦃ Kᵣ ⦄ 0)
    ++ₛ Ub[ b₂ + 0 ] (* , 2F , *))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0)

νσᵃ-VSub : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) → VSub σ → VSub (νσᵃ c' b₂ σ)
νσᵃ-VSub {m} {n} c' b₂ σ Vσ i with Fin.splitAt (suc (c' + 0) + (b₂ + 0)) i
... | Sum.inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
... | Sum.inj₁ d with Fin.splitAt (suc (c' + 0)) d
...   | Sum.inj₁ v = value-⋯ (Ub-V (suc (c' + 0)) (` 0F) 1F * V-` V-K v)
                       (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
...   | Sum.inj₂ w = Ub-V (b₂ + 0) * 2F * V-K V-K w

-- per-index collapse of an acq block entry.
private
  UbC : ∀ b {k} (e₁ : Tm (3 + k)) → e₁ ⋯ ⦅_⦆ₛ {n = 2 + k} * ≡ * → (x₀ : 𝔽 (2 + k)) (v : 𝔽 b) →
        (Ub[ b ] (e₁ , Fin.suc x₀ , *) v ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ ⦅ * ⦆ₛ
        ≡ ((* ⊗ (` x₀)) ⊗ *)
  UbC (suc zero) e₁ e₁* x₀ 0F =
    cong (λ z → ((z ⊗ (` x₀)) ⊗ *))
      (cong (_⋯ ⦅ * ⦆ₛ) (⋯-id e₁ (λ _ → refl) ) ■ e₁*)
  UbC (suc (suc b)) e₁ e₁* x₀ 0F =
    cong (λ z → ((z ⊗ (` x₀)) ⊗ *))
      (cong (_⋯ ⦅ * ⦆ₛ) (⋯-id e₁ (λ _ → refl) ) ■ e₁*)
  UbC (suc (suc b)) e₁ e₁* x₀ (Fin.suc v) = UbC (suc b) * refl x₀ v

  Ub-star-const : ∀ b {N} (c : 𝔽 N) (x : 𝔽 b) →
                  Ub[ b ] (* , c , *) x ≡ ((* ⊗ (` c)) ⊗ *)
  Ub-star-const (suc zero)    c 0F      = refl
  Ub-star-const (suc (suc b)) c 0F      = refl
  Ub-star-const (suc (suc b)) c (Fin.suc x) = Ub-star-const (suc b) c x

acq-collapse : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) (i : 𝔽 (suc (c' + 0) + (b₂ + 0) + m)) →
  νσᵃ c' b₂ σ i ⋯ ⦅ * ⦆ₛ ≡ νσ (suc c') b₂ σ i
acq-collapse {m} {n} c' b₂ σ i with Fin.splitAt (suc (c' + 0) + (b₂ + 0)) i
... | Sum.inj₂ u = amb
  where
    t2 : Tm (2 + n)
    t2 = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2
    amb : ((t2 ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ ⦅ * ⦆ₛ
          ≡ (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ weaken* ⦃ Kᵣ ⦄ 0
    amb = cong (_⋯ ⦅ * ⦆ₛ) (⋯-id (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 1) (λ _ → refl))
        ■ fusion t2 (weaken* ⦃ Kᵣ ⦄ 1) ⦅ * ⦆ₛ
        ■ ⋯-id t2 (λ _ → refl)
        ■ sym (⋯-id t2 (λ _ → refl))
        ■ sym (⋯-id (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 0) (λ _ → refl))
... | Sum.inj₁ d with Fin.splitAt (suc (c' + 0)) d
...   | Sum.inj₁ v =
        UbC (suc (c' + 0)) (` 0F) refl 0F v
      ■ sym (cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) (Ub-star-const (suc c' + 0) 0F v))
...   | Sum.inj₂ w =
        cong (_⋯ ⦅ * ⦆ₛ) (Ub-star-const (b₂ + 0) 2F w)
      ■ sym (Ub-star-const (b₂ + 0) (weaken* ⦃ Kᵣ ⦄ 0 1F) w)
