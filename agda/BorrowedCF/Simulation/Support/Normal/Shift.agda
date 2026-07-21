-- | The transport-free half of the telescope calculus.
--
--   Two ingredients the remaining ≋′ cases (∥-comm′, ∥-cong′) need, both chosen
--   so that NO scope transport appears.
--
--   * `shift2` / `shift1` re-base a telescope under an extra ν / φ.  They do
--     exactly what `renTel s (2 + n)` does, but their INDEX is already
--     `Tel (2 + n) (2 + j)` instead of `Tel (2 + n) (innerOf s (2 + n))`, so
--     statements about them need no `subst`.  `shift2-renTel` is the one place
--     the two presentations are reconciled.
--   * The `liftId` laws.  `liftId` keeps the inner scope fixed, so unlike the
--     `liftRen` laws in Normal.Nat every one of these is a plain equation.
module BorrowedCF.Simulation.Support.Normal.Shift where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Nat using (subst-tν; subst-tφ)

open Nat.Variables

------------------------------------------------------------------------
-- Re-basing under an extra binder, with the index already in normal form.
------------------------------------------------------------------------

shift2 : ∀ {n j} → Tel n j → Tel (2 + n) (2 + j)
shift2 []       = []
shift2 (tν s)   = tν   (shift2 s)
shift2 (tφ f s) = tφ f (shift2 s)

shift1 : ∀ {n j} → Tel n j → Tel (1 + n) (1 + j)
shift1 []       = []
shift1 (tν s)   = tν   (shift1 s)
shift1 (tφ f s) = tφ f (shift1 s)

shift2-innerOf : ∀ {n j} (s : Tel n j) → innerOf s (2 + n) ≡ 2 + j
shift2-innerOf []       = refl
shift2-innerOf (tν s)   = shift2-innerOf s
shift2-innerOf (tφ f s) = shift2-innerOf s

shift1-innerOf : ∀ {n j} (s : Tel n j) → innerOf s (1 + n) ≡ 1 + j
shift1-innerOf []       = refl
shift1-innerOf (tν s)   = shift1-innerOf s
shift1-innerOf (tφ f s) = shift1-innerOf s

-- The reconciliation: `shift2` IS `renTel` at `2 + n`.
shift2-renTel : ∀ {n j} (s : Tel n j) →
                subst (Tel (2 + n)) (shift2-innerOf s) (renTel s (2 + n)) ≡ shift2 s
shift2-renTel []       = refl
shift2-renTel (tν s)   =
  subst-tν (shift2-innerOf s) (renTel s (2 + (2 + _))) ■ cong tν     (shift2-renTel s)
shift2-renTel (tφ f s) =
  subst-tφ (shift2-innerOf s) f (renTel s (1 + (2 + _))) ■ cong (tφ f) (shift2-renTel s)

shift1-renTel : ∀ {n j} (s : Tel n j) →
                subst (Tel (1 + n)) (shift1-innerOf s) (renTel s (1 + n)) ≡ shift1 s
shift1-renTel []       = refl
shift1-renTel (tν s)   =
  subst-tν (shift1-innerOf s) (renTel s (2 + (1 + _))) ■ cong tν     (shift1-renTel s)
shift1-renTel (tφ f s) =
  subst-tφ (shift1-innerOf s) f (renTel s (1 + (1 + _))) ■ cong (tφ f) (shift1-renTel s)

------------------------------------------------------------------------
-- The `liftId` laws — all transport-free.
------------------------------------------------------------------------

liftId-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ n} → ρ₁ ≗ ρ₂ → liftId t ρ₁ ≗ liftId t ρ₂
liftId-cong []       eq = eq
liftId-cong (tν t)   eq = liftId-cong t (eq ~↑* 2)
liftId-cong (tφ f t) eq = liftId-cong t (eq ~↑)

liftId-· : ∀ {n k} (t : Tel n k) (ρ σ : n →ᵣ n) (x : 𝔽 k) →
           liftId t σ (liftId t ρ x) ≡ liftId t (ρ ·ₖ σ) x
liftId-· []       ρ σ x = refl
liftId-· (tν t)   ρ σ x =
  liftId-· t (ρ ↑* 2) (σ ↑* 2) x ■ liftId-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-· (tφ f t) ρ σ x =
  liftId-· t (ρ ↑) (σ ↑) x ■ liftId-cong t (λ y → sym (dist-↑-· ρ σ y)) x

-- Lifting along a concatenation is lifting twice.
liftId-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (ρ : n →ᵣ n) (x : 𝔽 j) →
             liftId (t ++ᵗ s) ρ x ≡ liftId s (liftId t ρ) x
liftId-++ᵗ []       s ρ x = refl
liftId-++ᵗ (tν t)   s ρ x = liftId-++ᵗ t s (ρ ↑* 2) x
liftId-++ᵗ (tφ f t) s ρ x = liftId-++ᵗ t s (ρ ↑)    x

-- The endo counterpart of Normal.Nat's `wkTel-nat`.
liftId-wkTel : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ n) (x : 𝔽 n) →
               liftId t ρ (wkTel t x) ≡ wkTel t (ρ x)
liftId-wkTel []       ρ x = refl
liftId-wkTel (tν t)   ρ x =
  liftId-wkTel t (ρ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 x) ■ cong (wkTel t) (sym (↑*-wk ρ 2 x))
liftId-wkTel (tφ f t) ρ x =
  liftId-wkTel t (ρ ↑) (weaken* ⦃ Kᵣ ⦄ 1 x) ■ cong (wkTel t) (sym (↑*-wk ρ 1 x))
