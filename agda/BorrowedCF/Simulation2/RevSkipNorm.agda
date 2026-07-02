module BorrowedCF.Simulation2.RevSkipNorm where

-- Skip-normalization for the reverse simulation (shared by RU-Com / RU-Choice /
-- R-Close): the typed R-Com/R-Close/... rules fire ONLY at ν (suc b₁ ∷ …) with
-- the live handle literally ` 0F.  When leading Skips/Unr borrows push the live
-- handle to a later block-1 index, the reconstruction is R-Discard*(skips) ◅ real
-- step, absorbed by the multi-step codomain (P TR─→ₚ* P′).
--
-- Lemma 1 (translation-invariance of an R-Discard) is ALREADY proven hole-free in
-- Theorems.agda as `disc-single` — discarding a leading unused block-1 borrow is
-- invisible to U[_] up to ≋.  This module iterates it into a k-fold chain.

open import BorrowedCF.Simulation2.Base
-- disc-single lives in Theorems.agda but that module currently has open holes
-- (concurrent work), so it cannot be imported; its self-contained core
-- (block-shift / Ub-star-const / disc-single) is re-derived here from the
-- hole-free TranslationProperties primitives.
open import BorrowedCF.Simulation2.TranslationProperties using (U-⋯ₚ; U-cong; UB-cong; ≡→≋)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using ([_,_]′)

import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR

open TP using (_⋯ₚ_)

-- ── re-derived from Theorems.agda (self-contained) ─────────────────────────
Ub-star-const : ∀ b {N} (c : 𝔽 N) (x : 𝔽 b) →
                Ub[ b ] (* , c , *) x ≡ chanTriple (* , c , *)
Ub-star-const zero          c ()
Ub-star-const (suc zero)    c 0F      = refl
Ub-star-const (suc (suc b)) c 0F      = refl
Ub-star-const (suc (suc b)) c (suc x) = Ub-star-const (suc b) c x

block-shift : ∀ p {A B N} (bL : suc p →ₛ N) (bR : p →ₛ N)
              (eq : ∀ k → bL (suc k) ≡ bR k)
              (ts : A →ₛ N) (rs : B →ₛ N) (i : 𝔽 (p + A + B)) →
              ((bL ++ₛ ts) ++ₛ rs) (suc i) ≡ ((bR ++ₛ ts) ++ₛ rs) i
block-shift p {A} {B} bL bR eq ts rs i with Fin.splitAt (p + A) i
... | inj₂ k = refl
... | inj₁ j with Fin.splitAt p j
... | inj₁ k = eq k
... | inj₂ k = refl

-- disc-single (B₁ = [] single-chain R-Discard is U[_]-invariant up to ≋).
disc-single : (b : ℕ) (B₂ : TP.BindGroup)
              (P : TP.Proc (sum (b ∷ []) + sum B₂ + n))
              (σ : n →ₛ m)
            → U[ TP.ν (suc b ∷ []) B₂ (P TP.⋯ₚ weakenᵣ) ] σ
                UP.≋ U[ TP.ν (b ∷ []) B₂ P ] σ
disc-single b B₂ P σ =
  UP.ν-cong (UB-cong B₂ (* , 1F , *) (λ τ₂ →
    ≡→≋ (U-⋯ₚ P ■ U-cong P (λ i →
      block-shift (b + 0)
        (λ j → Ub[ suc b + 0 ] (* , 0F , *) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        (λ j → Ub[ b + 0 ] (* , 0F , *) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        (λ k → cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
                 (Ub-star-const (suc b + 0) 0F (suc k)
                  ■ sym (Ub-star-const (b + 0) 0F k)))
        τ₂
        (λ j → σ j ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        i))))
-- ────────────────────────────────────────────────────────────────────────────

-- k-fold weakening of a block-1 body at the head (0F), keeping the scope in the
-- ((k+b)+0)+… shape so R-Discard peels one weakenᵣ per step definitionally.
wkⁿ : ∀ (k b : ℕ) (B₂ : TP.BindGroup) {n : ℕ} → TP.Proc (b + 0 + sum B₂ + n)
    → TP.Proc (k + b + 0 + sum B₂ + n)
wkⁿ zero    b B₂ P = P
wkⁿ (suc k) b B₂ {n} P = wkⁿ k b B₂ P ⋯ₚ weakenᵣ {k + b + 0 + sum B₂ + n}

-- normalize-block1 : discard the k leading (unused) block-1 borrows, giving a
-- TR─→ₚ* chain to the k-shorter block, with U[_]-invariance (≋) at every step.
normalize-block1 : ∀ (k b : ℕ) (B₂ : TP.BindGroup) {n m} (P : TP.Proc (b + 0 + sum B₂ + n))
                   (σ : n →ₛ m)
  → Star TR._─→ₚ_ (TP.ν (k + b ∷ []) B₂ (wkⁿ k b B₂ P)) (TP.ν (b ∷ []) B₂ P)
      × (U[ TP.ν (k + b ∷ []) B₂ (wkⁿ k b B₂ P) ] σ UP.≋ U[ TP.ν (b ∷ []) B₂ P ] σ)
normalize-block1 zero    b B₂ P σ = ε , ε
normalize-block1 (suc k) b B₂ P σ =
  let chain , eqv = normalize-block1 k b B₂ P σ
  in TR.R-Discard ◅ chain , disc-single (k + b) B₂ (wkⁿ k b B₂ P) σ ◅◅ eqv
