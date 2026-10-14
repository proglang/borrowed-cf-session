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

shift2-innerOf : ∀ {n j} (s : Tel n j) → innerOf s (2 + n) ≡ 2 + j
shift2-innerOf []         = refl
shift2-innerOf (tν s)     = shift2-innerOf s
shift2-innerOf (tφ f c s) = shift2-innerOf s

shift1-innerOf : ∀ {n j} (s : Tel n j) → innerOf s (1 + n) ≡ 1 + j
shift1-innerOf []         = refl
shift1-innerOf (tν s)     = shift1-innerOf s
shift1-innerOf (tφ f c s) = shift1-innerOf s

-- LINKED-φ: `shift2` re-bases a telescope under two extra outer binders, which
-- RENAMES its φ-channels (the fresh names must be avoided) — i.e. it is exactly
-- `renTel s (weaken* 2)`, given the clean index `2 + j` by the `innerOf`
-- transport.  A structural clean-index recursion is impossible here
-- (`weaken* 2 ↑* 2 ≢ weaken* 2`), so `shift2` IS the insertion renaming.
shift2 : ∀ {n j} → Tel n j → Tel (2 + n) (2 + j)
shift2 {n} s = subst (Tel (2 + n)) (shift2-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 2))

shift1 : ∀ {n j} → Tel n j → Tel (1 + n) (1 + j)
shift1 {n} s = subst (Tel (1 + n)) (shift1-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 1))

-- The reconciliation, now definitional.
shift2-renTel : ∀ {n j} (s : Tel n j) →
                subst (Tel (2 + n)) (shift2-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 2)) ≡ shift2 s
shift2-renTel s = refl

shift1-renTel : ∀ {n j} (s : Tel n j) →
                subst (Tel (1 + n)) (shift1-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 1)) ≡ shift1 s
shift1-renTel s = refl

------------------------------------------------------------------------
-- The `liftId` laws — all transport-free.
------------------------------------------------------------------------

liftId-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ n} → ρ₁ ≗ ρ₂ → liftId t ρ₁ ≗ liftId t ρ₂
liftId-cong []         eq = eq
liftId-cong (tν t)     eq = liftId-cong t (eq ~↑* 2)
liftId-cong (tφ f c t) eq = liftId-cong t (eq ~↑)

liftId-· : ∀ {n k} (t : Tel n k) (ρ σ : n →ᵣ n) (x : 𝔽 k) →
           liftId t σ (liftId t ρ x) ≡ liftId t (ρ ·ₖ σ) x
liftId-· []         ρ σ x = refl
liftId-· (tν t)     ρ σ x =
  liftId-· t (ρ ↑* 2) (σ ↑* 2) x ■ liftId-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-· (tφ f c t) ρ σ x =
  liftId-· t (ρ ↑) (σ ↑) x ■ liftId-cong t (λ y → sym (dist-↑-· ρ σ y)) x

-- Lifting along a concatenation is lifting twice.
liftId-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (ρ : n →ᵣ n) (x : 𝔽 j) →
             liftId (t ++ᵗ s) ρ x ≡ liftId s (liftId t ρ) x
liftId-++ᵗ []         s ρ x = refl
liftId-++ᵗ (tν t)     s ρ x = liftId-++ᵗ t s (ρ ↑* 2) x
liftId-++ᵗ (tφ f c t) s ρ x = liftId-++ᵗ t s (ρ ↑)    x

-- The endo counterpart of Normal.Nat's `wkTel-nat`.
liftId-wkTel : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ n) (x : 𝔽 n) →
               liftId t ρ (wkTel t x) ≡ wkTel t (ρ x)
liftId-wkTel []         ρ x = refl
liftId-wkTel (tν t)     ρ x =
  liftId-wkTel t (ρ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 x) ■ cong (wkTel t) (sym (↑*-wk ρ 2 x))
liftId-wkTel (tφ f c t) ρ x =
  liftId-wkTel t (ρ ↑) (weaken* ⦃ Kᵣ ⦄ 1 x) ■ cong (wkTel t) (sym (↑*-wk ρ 1 x))
