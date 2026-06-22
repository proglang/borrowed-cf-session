{-# OPTIONS --rewriting #-}

-- Crux helper for U-acq (O1 analogue): the acq redex's channel argument.
-- leafσ 0F = canonₛ (zero ∷ suc b₁ ∷ B₁) (K`unit,0F,K`unit) 0F ⋯ weaken*(syncs B₂).
-- The leading zero chain has 0 handles, so position 0F peels into
-- canonₛ (suc b₁ ∷ B₁) ((`0F),1F,K`unit⋯weakenᵣ) 0F, whose FRONT triple
-- (via canonₛ-handle []) is `((`0F) ⊗ (`x)) ⊗ c` — the SYNC `0F` first, exactly
-- matching RU-Acquire's `((`0F) ⊗ (`suc x)) ⊗ (e ⋯ weakenᵣ)`.

module BorrowedCF.Simulation.AcqFront where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Simulation.Flatten using (Ubₛ; canonₛ; toℕ-subst𝔽)
open import BorrowedCF.Simulation.Theorems.LSplit using (canonₛ-handle; subst-⊗; subst-`)
open import BorrowedCF.Simulation.SubstLemmas using (subst-Π)
open import BorrowedCF.Simulation.Theorems.Toolkit using (toℕ-wk)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open Nat using (+-suc)
open Fin.Patterns

canonₛ-acq-front : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {n} →
  Σ[ a ∈ Tm (syncs (zero ∷ suc b₁ ∷ B₁) + (2 + n)) ]
  Σ[ x ∈ 𝔽 (syncs (zero ∷ suc b₁ ∷ B₁) + (2 + n)) ]
  Σ[ c ∈ Tm (syncs (zero ∷ suc b₁ ∷ B₁) + (2 + n)) ]
    canonₛ (zero ∷ suc b₁ ∷ B₁) (K `unit , 0F , K `unit) 0F ≡ (a ⊗ (` x)) ⊗ c
canonₛ-acq-front b₁ B₁ {n} with canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ) b₁ B₁
... | a′ , x′ , c′ , rp =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ ,
  ( subst-Π eq g 0F
  ■ cong (subst Tm eq) rp
  ■ subst-⊗ eq (a′ ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) )
  where
    sB : ℕ
    sB = syncs (suc b₁ ∷ B₁)
    eq : sB + suc (2 + n) ≡ suc sB + (2 + n)
    eq = +-suc sB (2 + n)
    g : sum (zero ∷ suc b₁ ∷ B₁) →ₛ (sB + suc (2 + n))
    g = Ubₛ 0 ( K `unit ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
              , weaken* ⦃ Kᵣ ⦄ sB (suc 0F)
              , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
        ++ₛ canonₛ (suc b₁ ∷ B₁) ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ)

-- Linkage of canonₛ-acq-front's projections to the underlying canonₛ-handle components
-- (transparent here because the `with` is in scope; opaque from outside).
acq-a-link : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {n} →
  proj₁ (canonₛ-acq-front b₁ B₁ {n})
  ≡ subst Tm (+-suc (syncs (suc b₁ ∷ B₁)) (2 + n))
      (proj₁ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁))
acq-a-link b₁ B₁ {n} with canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁
... | _ , _ , _ , _ = refl

acq-x-link : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {n} →
  proj₁ (proj₂ (canonₛ-acq-front b₁ B₁ {n}))
  ≡ subst 𝔽 (+-suc (syncs (suc b₁ ∷ B₁)) (2 + n))
      (proj₁ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁)))
acq-x-link b₁ B₁ {n} with canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁
... | _ , _ , _ , _ = refl

acq-c-link : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {n} →
  proj₁ (proj₂ (proj₂ (canonₛ-acq-front b₁ B₁ {n})))
  ≡ subst Tm (+-suc (syncs (suc b₁ ∷ B₁)) (2 + n))
      (proj₁ (proj₂ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁))))
acq-c-link b₁ B₁ {n} with canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁
... | _ , _ , _ , _ = refl

-- Positional shape of canonₛ-handle [] cc's FIRST and THIRD components when the seed
-- e₁ is a variable: the first slot is e₁ weakened to sit at sync-index syncs(suc b₁∷B₂),
-- the third slot is a value whose vars are all strictly below that index.  By case
-- analysis on (b₁, B₂) over the []-prefix cases of canonₛ-handle.
handle-a : ∀ {M} (v : 𝔽 M) (x : 𝔽 M) (e₂ : Tm M) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Σ[ va ∈ 𝔽 (syncs (suc b₁ ∷ B₂) + M) ]
    (proj₁ (canonₛ-handle [] ((` v) , x , e₂) b₁ B₂) ≡ (` va))
  × (Fin.toℕ va ≡ syncs (suc b₁ ∷ B₂) + Fin.toℕ v)
handle-a v x e₂ zero    []      = v , refl , refl
handle-a v x e₂ (suc _) []      = v , refl , refl
handle-a {M = MM} v x e₂ zero    (b ∷ B) =
  subst 𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB (suc v)) , subst-` eq (weaken* ⦃ Kᵣ ⦄ sB (suc v))
  , ( toℕ-subst𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB (suc v))
    ■ toℕ-wk sB (suc v) ■ Nat.+-suc sB (Fin.toℕ v) )
  where
    sB = syncs (b ∷ B)
    eq : sB + suc MM ≡ suc sB + MM
    eq = +-suc sB MM
handle-a {M = MM} v x e₂ (suc _) (b ∷ B) =
  subst 𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB (suc v)) , subst-` eq (weaken* ⦃ Kᵣ ⦄ sB (suc v))
  , ( toℕ-subst𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB (suc v))
    ■ toℕ-wk sB (suc v) ■ Nat.+-suc sB (Fin.toℕ v) )
  where
    sB = syncs (b ∷ B)
    eq : sB + suc MM ≡ suc sB + MM
    eq = +-suc sB MM

-- First component for a K`unit seed: always K`unit (the leading sync of the reclaimed
-- channel is consumed).  Case analysis on (b₁, B₂); the (b∷B) cases weaken K`unit.
handle-a-K : ∀ {M} (x : 𝔽 M) (e₂ : Tm M) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  proj₁ (canonₛ-handle [] (K `unit , x , e₂) b₁ B₂) ≡ K `unit
handle-a-K x e₂ zero    []      = refl
handle-a-K x e₂ (suc _) []      = refl
handle-a-K {M = MM} x e₂ zero    (b ∷ B) = subst-Kunit (+-suc (syncs (b ∷ B)) MM)
  where
    subst-Kunit : ∀ {a b} (p : a ≡ b) → subst Tm p (K `unit) ≡ K `unit
    subst-Kunit refl = refl
handle-a-K {M = MM} x e₂ (suc _) (b ∷ B) = subst-Kunit (+-suc (syncs (b ∷ B)) MM)
  where
    subst-Kunit : ∀ {a b} (p : a ≡ b) → subst Tm p (K `unit) ≡ K `unit
    subst-Kunit refl = refl

handle-c : ∀ {M} (e₁ : Tm M) (x : 𝔽 M) (e₂ : Tm M) (e₂≡ : e₂ ≡ K `unit) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  (proj₁ (proj₂ (proj₂ (canonₛ-handle [] (e₁ , x , e₂) b₁ B₂))) ≡ K `unit)
  ⊎ Σ[ vc ∈ 𝔽 (syncs (suc b₁ ∷ B₂) + M) ]
      (proj₁ (proj₂ (proj₂ (canonₛ-handle [] (e₁ , x , e₂) b₁ B₂))) ≡ (` vc))
    × (Fin.toℕ vc Nat.< syncs (suc b₁ ∷ B₂))
handle-c e₁ x e₂ e₂≡ zero    []      = inj₁ e₂≡
handle-c e₁ x e₂ e₂≡ (suc _) []      = inj₁ refl
handle-c {M = MM} e₁ x e₂ e₂≡ zero    (b ∷ B) =
  inj₂ ( subst 𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB 0F)
       , subst-` eq (weaken* ⦃ Kᵣ ⦄ sB 0F)
       , Nat.s≤s (subst (Nat._≤ sB) (sym aux) (Nat.≤-refl)) )
  where
    sB = syncs (b ∷ B)
    eq : sB + suc MM ≡ suc sB + MM
    eq = +-suc sB MM
    aux : Fin.toℕ (subst 𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {MM}))) ≡ sB
    aux = toℕ-subst𝔽 eq (weaken* ⦃ Kᵣ ⦄ sB 0F) ■ toℕ-wk sB 0F ■ Nat.+-identityʳ sB
handle-c e₁ x e₂ e₂≡ (suc _) (b ∷ B) = inj₁ (subst-Kunit (+-suc (syncs (b ∷ B)) _))
  where
    subst-Kunit : ∀ {a b} (p : a ≡ b) → subst Tm p (K `unit) ≡ K `unit
    subst-Kunit refl = refl
