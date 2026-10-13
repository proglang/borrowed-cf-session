-- | Backward simulation, RU-LSplit probe — the AMBIENT-side bridge.
--
--   Two facts the σ-escape refutation of `PinLSplit.pin-lsplit-fire` needs:
--
--     * `BσWk-wkTel` — the accumulated image weakening `BσWk` (PinConj) IS the
--       telescope weakening of the image block telescope, `wkTel (BTel t n)`.
--       Pointwise on names, so the boundary talk of `Normal.WitnessAmb`
--       (stated on `wkTel`) applies to `BσWk`-images.
--     * `σ-escape-refute` — a σ-value's `BσWk`-image cannot have a
--       NON-ambient middle: renaming reflects the pair-of-pair shape down to
--       a variable middle (`mid-var`), whose image is a `BσWk`-image, i.e.
--       ambient by the bridge.
--
--   The missing premise (`∀ z → w ≢ wkTel (BTel t n) z` for the middle `ρ 0F`)
--   is exactly the boundary-preservation of the pinning composite; its
--   witness-leg is `WitnessAmb.bound-pres`.
module BorrowedCF.Simulation.Backward.PinAmb where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Translation using (syncs)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Endo using (wkTel-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Nat using (subst-wkTel)
open import BorrowedCF.Simulation.Support.Normal.Image using (φTelᵣ; φTel; scope≡)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (BScope; BTel)
open import BorrowedCF.Simulation.Backward.PinConj using (BσWk)

import BorrowedCF.Processes.Typed as TP

open Nat.Variables

------------------------------------------------------------------------
-- Transport toolbox: `subst 𝔽` through `■`, `suc`, and `+-suc`.
------------------------------------------------------------------------

subst𝔽-■ : ∀ {a b c : ℕ} (p : a ≡ b) (q : b ≡ c) (v : 𝔽 a) →
           subst 𝔽 (p ■ q) v ≡ subst 𝔽 q (subst 𝔽 p v)
subst𝔽-■ refl q v = refl

subst𝔽-suc : ∀ {a b : ℕ} (eq : a ≡ b) (v : 𝔽 a) →
             subst 𝔽 (cong suc eq) (suc v) ≡ suc (subst 𝔽 eq v)
subst𝔽-suc refl v = refl

wk*-suc : ∀ m {k} (x : 𝔽 k) →
          subst 𝔽 (+-suc m k) (weaken* ⦃ Kᵣ ⦄ m (suc x))
            ≡ suc (weaken* ⦃ Kᵣ ⦄ m x)
wk*-suc zero        x = refl
wk*-suc (suc m) {k} x =
  subst𝔽-suc (+-suc m k) (weaken* ⦃ Kᵣ ⦄ m (suc x)) ■ cong suc (wk*-suc m x)

------------------------------------------------------------------------
-- A φ-nest weakens by its sync count.
------------------------------------------------------------------------

φ-aux : ∀ (B : TP.BindGroup) (k : ℕ) (x : 𝔽 k) →
        subst 𝔽 (scope≡ B k) (wkTel (φTelᵣ B k) x) ≡ weaken* ⦃ Kᵣ ⦄ (syncs B) x
φ-aux []              k x = refl
φ-aux (_ ∷ [])        k x = refl
φ-aux (b ∷ B@(_ ∷ _)) k x =
  subst𝔽-■ (scope≡ B (suc k)) (+-suc (syncs B) k) (wkTel (φTelᵣ B (suc k)) (suc x))
    ■ cong (subst 𝔽 (+-suc (syncs B) k)) (φ-aux B (suc k) (suc x))
    ■ wk*-suc (syncs B) x

wkTel-φTel : ∀ (B : TP.BindGroup) (k : ℕ) (x : 𝔽 k) →
             wkTel (φTel B k) x ≡ weaken* ⦃ Kᵣ ⦄ (syncs B) x
wkTel-φTel B k x = sym (subst-wkTel (scope≡ B k) (φTelᵣ B k) x) ■ φ-aux B k x

------------------------------------------------------------------------
-- The bridge: `BσWk` is the image block telescope's own weakening.
------------------------------------------------------------------------

BσWk-wkTel : ∀ {a b} (t : TTel a b) (n : ℕ) (y : 𝔽 n) →
             BσWk t n y ≡ wkTel (BTel t n) y
BσWk-wkTel []ᵗ           n y = refl
BσWk-wkTel (tνᵗ B₁ B₂ t) n y =
    BσWk-wkTel t nB (weaken* ⦃ Kᵣ ⦄ (syncs B₂)
      (weaken* ⦃ Kᵣ ⦄ (syncs B₁) (weaken* ⦃ Kᵣ ⦄ 2 y)))
  ■ cong (wkTel (BTel t nB))
      (sym ( wkTel-++ᵗ (φTel B₁ (2 + n)) (φTel B₂ s₁) (weaken* ⦃ Kᵣ ⦄ 2 y)
           ■ cong (wkTel (φTel B₂ s₁)) (wkTel-φTel B₁ (2 + n) (weaken* ⦃ Kᵣ ⦄ 2 y))
           ■ wkTel-φTel B₂ s₁ (weaken* ⦃ Kᵣ ⦄ (syncs B₁) (weaken* ⦃ Kᵣ ⦄ 2 y)) ))
  ■ sym (wkTel-++ᵗ (tν (φTel B₁ (2 + n) ++ᵗ φTel B₂ s₁)) (BTel t nB) y)
  where
    s₁ = syncs B₁ + (2 + n)
    nB = syncs B₂ + (syncs B₁ + (2 + n))

------------------------------------------------------------------------
-- Renaming reflects the redex-triple shape down to its middle variable.
------------------------------------------------------------------------

headVarᵣ : ∀ {a b} (r : a →ᵣ b) (e : Tm a) {w : 𝔽 b} →
           e ⋯ r ≡ ` w → Σ[ z ∈ 𝔽 a ] ((e ≡ ` z) × (r z ≡ w))
headVarᵣ r (` x) refl = x , refl , refl

head⊗ᵣ : ∀ {a b} (r : a →ᵣ b) (e : Tm a) {u₁ u₂ : Tm b} →
         e ⋯ r ≡ u₁ ⊗ u₂ →
         Σ[ a₀ ∈ Tm a ] Σ[ b₀ ∈ Tm a ]
           ((e ≡ a₀ ⊗ b₀) × (u₁ ≡ a₀ ⋯ r) × (u₂ ≡ b₀ ⋯ r))
head⊗ᵣ r (a₀ ⊗ b₀) refl = a₀ , b₀ , refl , refl , refl

mid-var : ∀ {a b} (r : a →ᵣ b) (v : Tm a) {u₁ u₂ : Tm b} {w : 𝔽 b} →
          v ⋯ r ≡ ((u₁ ⊗ (` w)) ⊗ u₂) → Σ[ z ∈ 𝔽 a ] (r z ≡ w)
mid-var r v eq
  with p , q , refl , eq₁ , eq₂ ← head⊗ᵣ r v eq
  with p₁ , p₂ , refl , eq₃ , eq₄ ← head⊗ᵣ r p (sym eq₁)
  with z , refl , eqz ← headVarᵣ r p₂ (sym eq₄)
  = z , eqz

------------------------------------------------------------------------
-- The σ-escape refutation, boundary premise made explicit.
------------------------------------------------------------------------

σ-escape-refute :
  ∀ {a b n} (t : TTel a b) (σ : a →ₛ n) (y : 𝔽 a)
    {u₁ u₂ : Tm (BScope t n)} {w : 𝔽 (BScope t n)} →
  (∀ z → w ≢ wkTel (BTel t n) z) →
  σ y ⋯ BσWk t n ≡ ((u₁ ⊗ (` w)) ⊗ u₂) → ⊥
σ-escape-refute {n = n} t σ y nb eq
  with z , eqz ← mid-var (BσWk t n) (σ y) eq
  = nb z (sym eqz ■ BσWk-wkTel t n z)
