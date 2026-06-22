{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.Theorems.RSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Frames
open import BorrowedCF.Simulation.TranslationProperties
open import BorrowedCF.Simulation.Flatten
open import BorrowedCF.Simulation.BlockPermutation
open import BorrowedCF.Simulation.NuExtrusion
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Simulation.Theorems.Toolkit
open import BorrowedCF.Simulation.Theorems.NuSwap
open import BorrowedCF.Simulation.Theorems.LSplit

-- ════════════════════════════════════════════════════════════════════════════
-- Data-level renaming for remote split: rwk inserts ONE fresh slot (the new chain
-- `1`) at flat position `sum B₁`, BEFORE the (suc b₁)-chain.  Mirror of the lsplit
-- `dlwk` machinery, but the insertion threshold is `sum B₁` (not `sum B₁ + 1`) and the
-- target group grows by a whole chain (B₁ ++ 1 ∷ suc b₁ ∷ B₂).
-- ════════════════════════════════════════════════════════════════════════════

drwk : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
       sum (B₁ ++ suc b₁ ∷ B₂) →ᵣ sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)
drwk []        b₁ B₂ i = weakenᵣ i
drwk (a ∷ B₁') b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) , (λ r → a ↑ʳ drwk B₁' b₁ B₂ r) ]′ (splitAt a i)

-- drwk inserts a slot at flat position `sum B₁`: below it, toℕ is preserved; above, +1.
drwk-lo : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          Fin.toℕ j Nat.< sum B₁ → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ Fin.toℕ j
drwk-lo []        b₁ B₂ j lt = ⊥-elim (Nat.n≮0 lt)
drwk-lo (a ∷ B₁') b₁ B₂ j lt with drwk-lo B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : Fin.toℕ r Nat.< sum B₁'
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁')
                   (subst (Nat._< a + sum B₁') jℕ lt)

drwk-hi : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          sum B₁ Nat.≤ Fin.toℕ j → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ suc (Fin.toℕ j)
drwk-hi []        b₁ B₂ j h = refl
drwk-hi (a ∷ B₁') b₁ B₂ j h with drwk-hi B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁'))) h))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : sum B₁' Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁') (Fin.toℕ r)
                   (subst (a + sum B₁' Nat.≤_) jℕ h)

-- 𝐒.rwk inserts a slot at the same flat position `sum B₁` (over the FULL scope).
𝐒rwk-lo : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            Fin.toℕ x Nat.< sum B₁ →
            Fin.toℕ (𝐓R.SplitRenamings.rwk B₁ B₂ B {b₁} {m} x) ≡ Fin.toℕ x
𝐒rwk-lo B₁ B₂ B {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ ↑*-lo weakenᵣ (sum B₁) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁
        lt′ = subst (Nat._< sum B₁) (sym (Fin.toℕ-cast _ x)) lt

𝐒rwk-hi : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            sum B₁ Nat.≤ Fin.toℕ x →
            Fin.toℕ (𝐓R.SplitRenamings.rwk B₁ B₂ B {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒rwk-hi B₁ B₂ B {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ ↑*-hi weakenᵣ (sum B₁) (Fin.cast _ x) h′
  ■ cong (sum B₁ +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ sum B₁) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁) (Fin.toℕ x Nat.∸ sum B₁)
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

-- The remote-split group has exactly one more data slot.
sum-rwk : ∀ (B₁ : 𝐓.BindGroup) {b₁ B₂} →
          sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂))
sum-rwk B₁ {b₁} {B₂} = sum-++ B₁ (1 ∷ suc b₁ ∷ B₂)
                     ■ +-suc (sum B₁) (sum (suc b₁ ∷ B₂))
                     ■ cong suc (sym (sum-++ B₁ (suc b₁ ∷ B₂)))

sB₁≤sumC₁r : ∀ (B₁ : 𝐓.BindGroup) {b₁ B₂} → sum B₁ Nat.≤ sum (B₁ ++ suc b₁ ∷ B₂)
sB₁≤sumC₁r B₁ {b₁} {B₂} =
  subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (Nat.m≤m+n (sum B₁) (sum (suc b₁ ∷ B₂)))

-- 𝐒.rwk vs the data-level drwk on the three regions of the leaf domain (data | B | σ).
P1r : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
     𝐓R.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
     ≡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1r B₁ B₂ B {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁
... | yes lt = Fin.toℕ-injective
      ( 𝐒rwk-lo B₁ B₂ B _ (subst (Nat._< sum B₁) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ drwk-lo B₁ b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ drwk-hi B₁ b₁ B₂ d h≤) )
  where h≤ : sum B₁ Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d) (sum B)

P2r : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (w : 𝔽 (sum B)) →
     𝐓R.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m)
     ≡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m
P2r B₁ B₂ B {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁≤sumC₁r B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-rwk B₁)

P3r : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (u : 𝔽 m) →
     𝐓R.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u)
     ≡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u
P3r B₁ B₂ B {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁≤sumC₁r B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-rwk B₁)

-- rsplit INSERTS a whole new chain, so the chain count (hence syncs and the φ-nest
-- depth) GROWS by exactly one: ϕ[1] = unset is the fresh sync's flag.
syncs-rwk : ∀ (B₁ : 𝐓.BindGroup) {b₁ : ℕ} {B₂ : 𝐓.BindGroup} →
            syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂))
syncs-rwk []            {b₁} {B₂} = refl
syncs-rwk (a ∷ [])      {b₁} {B₂} = refl
syncs-rwk (a ∷ d ∷ B₁″) {b₁} {B₂} = cong suc (syncs-rwk (d ∷ B₁″) {b₁} {B₂})

-- canonₛ uses the channel's HEAD term (e₁) only at the very first leaf position;
-- everywhere else (toℕ k ≢ 0) the head is irrelevant.  Needed to relate the rsplit
-- re-threaded channel ccR (head `0F) to mapᶜ weakenᵣ cc (head e₁⋯weakenᵣ) off-handle.
Ubₛ-head-irrel : ∀ (b : ℕ) {N} (e e' : Tm N) (x : 𝔽 N) (e₂ : Tm N) (k : 𝔽 b) →
                 Fin.toℕ k ≢ 0 → Ubₛ b (e , x , e₂) k ≡ Ubₛ b (e' , x , e₂) k
Ubₛ-head-irrel (suc zero)    e e' x e₂ 0F        k≢0 = ⊥-elim (k≢0 refl)
Ubₛ-head-irrel (suc (suc b)) e e' x e₂ 0F        k≢0 = ⊥-elim (k≢0 refl)
Ubₛ-head-irrel (suc (suc b)) e e' x e₂ (suc k')  k≢0 = refl

canonₛ-head-irrel : ∀ (B : 𝐓.BindGroup) {N} (e e' : Tm N) (x : 𝔽 N) (e₂ : Tm N) (k : 𝔽 (sum B)) →
                    Fin.toℕ k ≢ 0 → canonₛ B (e , x , e₂) k ≡ canonₛ B (e' , x , e₂) k
canonₛ-head-irrel (c ∷ [])      e e' x e₂ k k≢0 with splitAt c k in seq
... | inj₁ p = Ubₛ-head-irrel c e e' x e₂ p
                 (λ p≡0 → k≢0 (cong Fin.toℕ (sym (Fin.join-splitAt c 0 k) ■ cong (Fin.join c 0) seq) ■ Fin.toℕ-↑ˡ p 0 ■ p≡0))
... | inj₂ ()
canonₛ-head-irrel (c ∷ b ∷ B) {N} e e' x e₂ k k≢0 =
    subst-Π (+-suc sB N) (Ubₛ c (cc-i e) ++ₛ canonₛ (b ∷ B) cc-r) k
  ■ cong (subst Tm (+-suc sB N)) inner
  ■ sym (subst-Π (+-suc sB N) (Ubₛ c (cc-i e') ++ₛ canonₛ (b ∷ B) cc-r) k)
  where
    sB = syncs (b ∷ B)
    cc-i  = λ ee → ( ee ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    inner : (Ubₛ c (cc-i e) ++ₛ canonₛ (b ∷ B) cc-r) k ≡ (Ubₛ c (cc-i e') ++ₛ canonₛ (b ∷ B) cc-r) k
    inner with splitAt c k in seq
    ... | inj₁ p = Ubₛ-head-irrel c (e ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB) (e' ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) p
                     (λ p≡0 → k≢0 (cong Fin.toℕ (sym (Fin.join-splitAt c (sum (b ∷ B)) k) ■ cong (Fin.join c (sum (b ∷ B))) seq) ■ Fin.toℕ-↑ˡ p (sum (b ∷ B)) ■ p≡0))
    ... | inj₂ q = refl

-- The fresh-sync insertion renaming: inserts ONE sync at global index sT = syncs(suc b₁∷B₂)
-- (independent of B₁); the codomain grows by one (syncs C₁' = suc (syncs C₁)).  Built by
-- induction matching canonₛ's chain structure (chain a's sync stays above the inserted one).
rins : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
       (syncs (B₁ ++ suc b₁ ∷ B₂) + N) →ᵣ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N)
rins [] {N} b₁ B₂ =
  subst (λ z → (syncs (suc b₁ ∷ B₂) + N) →ᵣ z) (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂))
rins (a ∷ [])      {N} b₁ B₂ =
  subst₂ _→ᵣ_ (+-suc (syncs (suc b₁ ∷ B₂)) N) (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (rins [] {suc N} b₁ B₂)
rins (a ∷ d ∷ B₁″) {N} b₁ B₂ =
  subst₂ _→ᵣ_ (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N) (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (rins (d ∷ B₁″) {suc N} b₁ B₂)

-- Transport a renaming application across casts on both domain and codomain (free by J).
subst-⋯-both : ∀ {a a' c c'} (eqD : a ≡ a') (eqC : c ≡ c') (t : Tm a) (ρ : a →ᵣ c) →
               subst Tm eqD t ⋯ subst₂ _→ᵣ_ eqD eqC ρ ≡ subst Tm eqC (t ⋯ ρ)
subst-⋯-both refl refl t ρ = refl

subst-cod-app : ∀ {D c c'} (eq : c ≡ c') (ρ : D →ᵣ c) (w : 𝔽 D) →
                subst (λ z → D →ᵣ z) eq ρ w ≡ subst 𝔽 eq (ρ w)
subst-cod-app refl ρ w = refl

subst₂→ᵣ-app : ∀ {a a' c c'} (eqD : a ≡ a') (eqC : c ≡ c') (ρ : a →ᵣ c) (w : 𝔽 a') →
               subst₂ _→ᵣ_ eqD eqC ρ w ≡ subst 𝔽 eqC (ρ (subst 𝔽 (sym eqD) w))
subst₂→ᵣ-app refl refl ρ w = refl

-- rins shifts everything at index ≥ sT up by one (sT = syncs(suc b₁∷B₂), the fresh sync index).
rins-hi : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (w : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
          syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ w → Fin.toℕ (rins B₁ {N} b₁ B₂ w) ≡ suc (Fin.toℕ w)
rins-hi [] {N} b₁ B₂ w h =
    cong Fin.toℕ (subst-cod-app (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) w)
  ■ toℕ-subst𝔽 (+-suc (syncs (suc b₁ ∷ B₂)) N) ((weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) w)
  ■ ↑*-hi weakenᵣ (syncs (suc b₁ ∷ B₂)) w h
  ■ cong (syncs (suc b₁ ∷ B₂) +_) (cong suc (toℕ-reduce≥ w h))
  ■ Nat.+-suc (syncs (suc b₁ ∷ B₂)) (Fin.toℕ w Nat.∸ syncs (suc b₁ ∷ B₂))
  ■ cong suc (Nat.m+[n∸m]≡n h)
rins-hi (a ∷ []) {N} b₁ B₂ w h =
    cong Fin.toℕ (subst₂→ᵣ-app (+-suc (syncs (suc b₁ ∷ B₂)) N) (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (rins [] {suc N} b₁ B₂) w)
  ■ toℕ-subst𝔽 (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (rins [] {suc N} b₁ B₂ (subst 𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w))
  ■ rins-hi [] {suc N} b₁ B₂ _ (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-subst𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w)) h)
  ■ cong suc (toℕ-subst𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w)
rins-hi (a ∷ d ∷ B₁″) {N} b₁ B₂ w h =
    cong Fin.toℕ (subst₂→ᵣ-app (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N) (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (rins (d ∷ B₁″) {suc N} b₁ B₂) w)
  ■ toℕ-subst𝔽 (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (rins (d ∷ B₁″) {suc N} b₁ B₂ (subst 𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w))
  ■ rins-hi (d ∷ B₁″) {suc N} b₁ B₂ _ (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-subst𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w)) h)
  ■ cong suc (toℕ-subst𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w)

-- rins is the identity (on toℕ) below the fresh-sync index sT.
rins-lo : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (w : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
          Fin.toℕ w Nat.< syncs (suc b₁ ∷ B₂) → Fin.toℕ (rins B₁ {N} b₁ B₂ w) ≡ Fin.toℕ w
rins-lo [] {N} b₁ B₂ w h =
    cong Fin.toℕ (subst-cod-app (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) w)
  ■ toℕ-subst𝔽 (+-suc (syncs (suc b₁ ∷ B₂)) N) ((weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) w)
  ■ ↑*-lo weakenᵣ (syncs (suc b₁ ∷ B₂)) w h
rins-lo (a ∷ []) {N} b₁ B₂ w h =
    cong Fin.toℕ (subst₂→ᵣ-app (+-suc (syncs (suc b₁ ∷ B₂)) N) (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (rins [] {suc N} b₁ B₂) w)
  ■ toℕ-subst𝔽 (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (rins [] {suc N} b₁ B₂ (subst 𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w))
  ■ rins-lo [] {suc N} b₁ B₂ _ (subst (Nat._< syncs (suc b₁ ∷ B₂)) (sym (toℕ-subst𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w)) h)
  ■ toℕ-subst𝔽 (sym (+-suc (syncs (suc b₁ ∷ B₂)) N)) w
rins-lo (a ∷ d ∷ B₁″) {N} b₁ B₂ w h =
    cong Fin.toℕ (subst₂→ᵣ-app (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N) (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (rins (d ∷ B₁″) {suc N} b₁ B₂) w)
  ■ toℕ-subst𝔽 (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (rins (d ∷ B₁″) {suc N} b₁ B₂ (subst 𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w))
  ■ rins-lo (d ∷ B₁″) {suc N} b₁ B₂ _ (subst (Nat._< syncs (suc b₁ ∷ B₂)) (sym (toℕ-subst𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w)) h)
  ■ toℕ-subst𝔽 (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N)) w

-- the fresh sync sits at or below every B₁-chain junction.
sT≤syncs : ∀ (B₁ : 𝐓.BindGroup) {b₁ B₂} → syncs (suc b₁ ∷ B₂) Nat.≤ syncs (B₁ ++ suc b₁ ∷ B₂)
sT≤syncs []            = Nat.≤-refl
sT≤syncs (a ∷ [])      {b₁} {B₂} = Nat.m≤n⇒m≤1+n (sT≤syncs [] {b₁} {B₂})
sT≤syncs (a ∷ d ∷ B₁″) {b₁} {B₂} = Nat.m≤n⇒m≤1+n (sT≤syncs (d ∷ B₁″) {b₁} {B₂})

-- rins inserts BELOW the chain content (which lives above all syncs): so post-composing
-- weaken* (syncs C₁) with rins is weaken* (syncs C₁') = weaken* (suc (syncs C₁)).
rins-wk : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (v : 𝔽 N) →
          rins B₁ {N} b₁ B₂ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
          ≡ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v
rins-wk B₁ {N} b₁ B₂ v = Fin.toℕ-injective
  ( rins-hi B₁ b₁ B₂ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-wk (syncs (B₁ ++ suc b₁ ∷ B₂)) v))
        (Nat.≤-trans (sT≤syncs B₁) (Nat.m≤m+n (syncs (B₁ ++ suc b₁ ∷ B₂)) (Fin.toℕ v))))
  ■ cong suc (toℕ-wk (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
  ■ cong (Nat._+ Fin.toℕ v) (sym (syncs-rwk B₁))
  ■ sym (toℕ-wk (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v) )


-- The chain-a content (mapᶜ (weaken* (syncs rest)) cc₀) is renamed by rins to the
-- chain-a content for the grown rest (weaken* one more) — rins sits below the content.
ubRwk : ∀ (a : ℕ) {N} (cc₀ : UChan (suc N)) (B₁' : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (p : 𝔽 a) →
        Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁' ++ suc b₁ ∷ B₂))) cc₀) p ⋯ rins B₁' {suc N} b₁ B₂
        ≡ Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂))) cc₀) p
ubRwk a cc₀ B₁' b₁ B₂ p =
    cong (_⋯ rins B₁' b₁ B₂) (Ubₛ-nat a cc₀ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁' ++ suc b₁ ∷ B₂))) p)
  ■ fusion (Ubₛ a cc₀ p) (weaken* ⦃ Kᵣ ⦄ (syncs (B₁' ++ suc b₁ ∷ B₂))) (rins B₁' b₁ B₂)
  ■ ⋯-cong (Ubₛ a cc₀ p) (rins-wk B₁' b₁ B₂)
  ■ sym (Ubₛ-nat a cc₀ (weaken* ⦃ Kᵣ ⦄ (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂))) p)


-- Lift an off-handle leaf equation through one chain (chain a)'s +-suc subst, with the
-- chain renamed by the subst₂-conjugated rins.  The chainLwk analogue for the growing nest.
chainRwk : ∀ {D D' a b a' b'} (eq : a ≡ a') (eqC : b ≡ b')
           (g : 𝔽 D → Tm a) (g' : 𝔽 D' → Tm b) (ρ : a →ᵣ b) (i : 𝔽 D) (di : 𝔽 D') →
           g i ⋯ ρ ≡ g' di →
           subst (λ z → 𝔽 D → Tm z) eq g i ⋯ subst₂ _→ᵣ_ eq eqC ρ
           ≡ subst (λ z → 𝔽 D' → Tm z) eqC g' di
chainRwk eq eqC g g' ρ i di inner =
    cong (_⋯ subst₂ _→ᵣ_ eq eqC ρ) (subst-Π eq g i)
  ■ subst-⋯-both eq eqC (g i) ρ
  ■ cong (subst Tm eqC) inner
  ■ sym (subst-Π eqC g' di)


-- canonₛ is invariant under inserting the new `1`-chain (rsplit), EXCEPT at the consumed
-- handle (position sum B₁): everywhere else, canonₛ C₁ cc weakened by the fresh sync = canonₛ C₁'
-- cc at the inserted position `drwk i`.  Off-handle ⇒ the head differs harmlessly (head-irrel).
canonₛ-rwk : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup)
             (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F) →
             canonₛ (B₁ ++ suc b₁ ∷ B₂) cc i ⋯ rins B₁ b₁ B₂
             ≡ canonₛ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) cc (drwk B₁ b₁ B₂ i)
canonₛ-rwk [] {N} (e₁ , cx , e₂) b₁ B₂ i i≢ =
    subst-⋯-cod (+-suc sT N) (canonₛ (suc b₁ ∷ B₂) (e₁ , cx , e₂) i) (weakenᵣ ↑* sT)
  ■ cong (subst Tm (+-suc sT N))
      ( sym (canonₛ-nat (suc b₁ ∷ B₂) (e₁ , cx , e₂) weakenᵣ i)
      ■ canonₛ-head-irrel (suc b₁ ∷ B₂) (e₁ ⋯ weakenᵣ) (` 0F) (suc cx) (e₂ ⋯ weakenᵣ) i i≢0 )
  ■ sym (subst-Π (+-suc sT N)
           ( Ubₛ 1 ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT , weaken* ⦃ Kᵣ ⦄ sT (suc cx) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT )
             ++ₛ canonₛ (suc b₁ ∷ B₂) ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) )
           (suc i))
  where
    sT = syncs (suc b₁ ∷ B₂)
    i≢0 : Fin.toℕ i ≢ 0
    i≢0 = λ ti0 → i≢ (Fin.toℕ-injective ti0)
canonₛ-rwk (a ∷ []) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk [] {suc N} ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | rec =
  chainRwk (+-suc (syncs (suc b₁ ∷ B₂)) N) (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N)
    (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ (suc b₁ ∷ B₂) cc-r)
    (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (1 ∷ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r)
    (rins [] {suc N} b₁ B₂) i (drwk (a ∷ []) b₁ B₂ i) handle
  where
    cc₀  = (e₁ ⋯ weakenᵣ , suc x , (` 0F))
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    GL' = [ Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (1 ∷ suc b₁ ∷ B₂))) cc₀) , canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r ]′
    handle : (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ (suc b₁ ∷ B₂) cc-r) i ⋯ rins [] {suc N} b₁ B₂
             ≡ (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs (1 ∷ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r) (drwk (a ∷ []) b₁ B₂ i)
    handle with splitAt a i in seq
    ... | inj₁ p = ubRwk a cc₀ [] b₁ B₂ p
                 ■ sym (cong GL' (Fin.splitAt-↑ˡ a p (sum (1 ∷ suc b₁ ∷ B₂))))
    ... | inj₂ r = rec r r≢
                 ■ sym (cong GL' (Fin.splitAt-↑ʳ a (sum (1 ∷ suc b₁ ∷ B₂)) (drwk [] b₁ B₂ r)))
      where r≢ : r ≢ Fin.cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F)
            r≢ r≡ = i≢ ( sym (Fin.join-splitAt a (sum (suc b₁ ∷ B₂)) i) ■ cong (Fin.join a (sum (suc b₁ ∷ B₂))) seq
                       ■ cong (a ↑ʳ_) r≡ ■ sym (pos-split a [] b₁ B₂) )
canonₛ-rwk (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk (d ∷ B₁″) {suc N} ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | rec =
  chainRwk (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N) (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N)
    (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r)
    (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂) cc-r)
    (rins (d ∷ B₁″) {suc N} b₁ B₂) i (drwk (a ∷ d ∷ B₁″) b₁ B₂ i) handle
  where
    cc₀  = (e₁ ⋯ weakenᵣ , suc x , (` 0F))
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    GL' = [ Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂))) cc₀) , canonₛ ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂) cc-r ]′
    handle : (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r) i ⋯ rins (d ∷ B₁″) {suc N} b₁ B₂
             ≡ (Ubₛ a (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂))) cc₀) ++ₛ canonₛ ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂) cc-r) (drwk (a ∷ d ∷ B₁″) b₁ B₂ i)
    handle with splitAt a i in seq
    ... | inj₁ p = ubRwk a cc₀ (d ∷ B₁″) b₁ B₂ p
                 ■ sym (cong GL' (Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂))))
    ... | inj₂ r = rec r r≢
                 ■ sym (cong GL' (Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) (drwk (d ∷ B₁″) b₁ B₂ r)))
      where r≢ : r ≢ Fin.cast (sym (sum-++ (d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 0F)
            r≢ r≡ = i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) i) ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) seq
                       ■ cong (a ↑ʳ_) r≡ ■ sym (pos-split a (d ∷ B₁″) b₁ B₂) )


-- The two NEW handles of the remote-split group C₁' = B₁ ++ 1 ∷ suc b₁ ∷ B₂ at
-- positions inj 0F (the fresh `1`-chain) and inj 1F (the original suc b₁-chain, now
-- starting from the fresh sync z).  RU-RSplit's two output triples.
canonₛ-sib-r : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) ]
  Σ[ x ∈ 𝔽 (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) ]
  Σ[ z ∈ 𝔽 (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) ]
    (canonₛ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) cc
       (Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F))
       ≡ (a ⊗ (` x)) ⊗ (` z))
  × (canonₛ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) cc
       (Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 1F))
       ≡ ((` z) ⊗ (` x)) ⊗ c)
canonₛ-sib-r [] (e₁ , cx , e₂) zero    [] =
  e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ 0 , weaken* ⦃ Kᵣ ⦄ 0 (suc cx) , e₂ ⋯ weakenᵣ , weaken* ⦃ Kᵣ ⦄ 0 0F ,
  refl , refl
canonₛ-sib-r [] (e₁ , cx , e₂) (suc b₁) [] =
  e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ 0 , weaken* ⦃ Kᵣ ⦄ 0 (suc cx) , K `unit , weaken* ⦃ Kᵣ ⦄ 0 0F ,
  refl , refl
-- inj0 distribution is clean (Ubₛ 1 head of the new chain); inj1 (the suc b₁ chain
-- handle) needs a toℕ-injective reconciliation of the fresh sync between the two
-- handles, plus the +-suc transport.  See memory simlsplit-lwk-id-false for the recipe.
canonₛ-sib-r [] (e₁ , cx , e₂) zero    (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , subst Tm (eq'' ■ eq) Tt , subst 𝔽 eq Z ,
  ( subst-Π eq g 0F ■ subst-⊗ eq (A ⊗ (` X)) (` Z)
  ■ cong₂ _⊗_ (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) (subst-` eq Z) ) ,
  ( subst-Π eq g 1F
  ■ cong (subst Tm eq) (subst-Π eq'' innerg 0F)
  ■ ss eq'' eq
  ■ subst-⊗ (eq'' ■ eq) (H1 ⊗ (` Md)) Tt
  ■ cong₂ _⊗_
      ( subst-⊗ (eq'' ■ eq) H1 (` Md)
      ■ cong₂ _⊗_
          ( subst-` (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ■ cong `_ headVarEq )
          ( subst-` (eq'' ■ eq) Md ■ cong `_ midVarEq ) )
      refl )
  where
    sB   = syncs (b ∷ B)
    eq   = +-suc (syncs (suc zero ∷ b ∷ B)) _
    eq'' = +-suc sB _
    A    = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ b ∷ B))
    X    = weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ b ∷ B)) (suc cx)
    Z    = weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ b ∷ B)) 0F
    g    = Ubₛ 1 (A , X , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ b ∷ B)))
           ++ₛ canonₛ (suc zero ∷ b ∷ B) ((` 0F) , suc cx , e₂ ⋯ weakenᵣ)
    H1   = (` 0F) ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    Md    = weaken* ⦃ Kᵣ ⦄ sB (suc (suc cx))
    Tt   = (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB
    innerg = Ubₛ 1 (H1 , Md , Tt) ++ₛ canonₛ (b ∷ B) ((` 0F) , suc (suc cx) , (e₂ ⋯ weakenᵣ) ⋯ weakenᵣ)
    headVarEq : subst 𝔽 (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ≡ subst 𝔽 eq Z
    headVarEq = Fin.toℕ-injective
      ( toℕ-subst𝔽 (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ■ toℕ-wk sB 1F
      ■ Nat.+-comm sB 1 ■ sym (Nat.+-identityʳ (syncs (suc zero ∷ b ∷ B)))
      ■ sym (toℕ-wk (syncs (suc zero ∷ b ∷ B)) 0F) ■ sym (toℕ-subst𝔽 eq Z) )
    midVarEq : subst 𝔽 (eq'' ■ eq) Md ≡ subst 𝔽 eq X
    midVarEq = Fin.toℕ-injective
      ( toℕ-subst𝔽 (eq'' ■ eq) Md ■ toℕ-wk sB (suc (suc cx))
      ■ Nat.+-suc sB (suc (Fin.toℕ cx))
      ■ sym (toℕ-wk (syncs (suc zero ∷ b ∷ B)) (suc cx)) ■ sym (toℕ-subst𝔽 eq X) )
canonₛ-sib-r [] (e₁ , cx , e₂) (suc b₁) (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , K `unit , subst 𝔽 eq Z ,
  ( subst-Π eq g 0F ■ subst-⊗ eq (A ⊗ (` X)) (` Z)
  ■ cong₂ _⊗_ (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) (subst-` eq Z) ) ,
  ( subst-Π eq g 1F
  ■ cong (subst Tm eq) (subst-Π eq'' innerg 0F)
  ■ ss eq'' eq
  ■ subst-⊗ (eq'' ■ eq) (H1 ⊗ (` Md)) (K `unit)
  ■ cong₂ _⊗_
      ( subst-⊗ (eq'' ■ eq) H1 (` Md)
      ■ cong₂ _⊗_
          ( subst-` (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ■ cong `_ headVarEq )
          ( subst-` (eq'' ■ eq) Md ■ cong `_ midVarEq ) )
      (subst-Kunit (eq'' ■ eq)) )
  where
    sB   = syncs (b ∷ B)
    eq   = +-suc (syncs (suc (suc b₁) ∷ b ∷ B)) _
    eq'' = +-suc sB _
    A    = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc (suc b₁) ∷ b ∷ B))
    X    = weaken* ⦃ Kᵣ ⦄ (syncs (suc (suc b₁) ∷ b ∷ B)) (suc cx)
    Z    = weaken* ⦃ Kᵣ ⦄ (syncs (suc (suc b₁) ∷ b ∷ B)) 0F
    g    = Ubₛ 1 (A , X , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc (suc b₁) ∷ b ∷ B)))
           ++ₛ canonₛ (suc (suc b₁) ∷ b ∷ B) ((` 0F) , suc cx , e₂ ⋯ weakenᵣ)
    H1   = (` 0F) ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    Md    = weaken* ⦃ Kᵣ ⦄ sB (suc (suc cx))
    innerg = Ubₛ (suc (suc b₁)) (H1 , Md , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
             ++ₛ canonₛ (b ∷ B) ((` 0F) , suc (suc cx) , (e₂ ⋯ weakenᵣ) ⋯ weakenᵣ)
    headVarEq : subst 𝔽 (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ≡ subst 𝔽 eq Z
    headVarEq = Fin.toℕ-injective
      ( toℕ-subst𝔽 (eq'' ■ eq) (weaken* ⦃ Kᵣ ⦄ sB 1F) ■ toℕ-wk sB 1F
      ■ Nat.+-comm sB 1 ■ sym (Nat.+-identityʳ (syncs (suc (suc b₁) ∷ b ∷ B)))
      ■ sym (toℕ-wk (syncs (suc (suc b₁) ∷ b ∷ B)) 0F) ■ sym (toℕ-subst𝔽 eq Z) )
    midVarEq : subst 𝔽 (eq'' ■ eq) Md ≡ subst 𝔽 eq X
    midVarEq = Fin.toℕ-injective
      ( toℕ-subst𝔽 (eq'' ■ eq) Md ■ toℕ-wk sB (suc (suc cx))
      ■ Nat.+-suc sB (suc (Fin.toℕ cx))
      ■ sym (toℕ-wk (syncs (suc (suc b₁) ∷ b ∷ B)) (suc cx)) ■ sym (toℕ-subst𝔽 eq X) )
canonₛ-sib-r (a ∷ [])       (e₁ , cx , e₂) b₁ B₂
  with canonₛ-sib-r [] ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , z′ , rp0 , rp1 =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ , subst 𝔽 eq z′ ,
  ( subst-Π eq g (cast0 (sum (a ∷ []) ↑ʳ 0F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a [] 1 (suc b₁ ∷ B₂) 0F)
      ■ cong [ Ubₛ a cc-i , canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp0 )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) (` z′)
  ■ cong₂ _⊗_ (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) (subst-` eq z′) ) ,
  ( subst-Π eq g (cast0 (sum (a ∷ []) ↑ʳ 1F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a [] 1 (suc b₁ ∷ B₂) 1F)
      ■ cong [ Ubₛ a cc-i , canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp1 )
  ■ subst-⊗ eq ((` z′) ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq (` z′) (` x′) ■ cong₂ _⊗_ (subst-` eq z′) (subst-` eq x′)) )
  where
    sB = syncs (1 ∷ suc b₁ ∷ B₂)
    eq = +-suc sB _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc cx) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r = ((` 0F) , suc cx , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (1 ∷ suc b₁ ∷ B₂) cc-r
    cast0 = Fin.cast (sym (sum-++ (a ∷ []) (1 ∷ suc b₁ ∷ B₂)))
canonₛ-sib-r (a ∷ d ∷ B₁″)  (e₁ , cx , e₂) b₁ B₂
  with canonₛ-sib-r (d ∷ B₁″) ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , z′ , rp0 , rp1 =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ , subst 𝔽 eq z′ ,
  ( subst-Π eq g (cast0 (sum (a ∷ d ∷ B₁″) ↑ʳ 0F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a (d ∷ B₁″) 1 (suc b₁ ∷ B₂) 0F)
      ■ cong [ Ubₛ a cc-i , canonₛ (d ∷ B₁″ ++ 1 ∷ suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp0 )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) (` z′)
  ■ cong₂ _⊗_ (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) (subst-` eq z′) ) ,
  ( subst-Π eq g (cast0 (sum (a ∷ d ∷ B₁″) ↑ʳ 1F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a (d ∷ B₁″) 1 (suc b₁ ∷ B₂) 1F)
      ■ cong [ Ubₛ a cc-i , canonₛ (d ∷ B₁″ ++ 1 ∷ suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp1 )
  ■ subst-⊗ eq ((` z′) ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq (` z′) (` x′) ■ cong₂ _⊗_ (subst-` eq z′) (subst-` eq x′)) )
  where
    sB = syncs (d ∷ B₁″ ++ 1 ∷ suc b₁ ∷ B₂)
    eq = +-suc sB _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc cx) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r = ((` 0F) , suc cx , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (d ∷ B₁″ ++ 1 ∷ suc b₁ ∷ B₂) cc-r
    cast0 = Fin.cast (sym (sum-++ (a ∷ d ∷ B₁″) (1 ∷ suc b₁ ∷ B₂)))

-- A handle term `e ⋯ weakenᵣ ⋯ weaken* sB`, rebased by the base insertion, gains one
-- weaken* (the leading weakenᵣ keeps it off var 0, so the inserted slot just shifts it).
ins-head-base : ∀ {N} (e : Tm N) (sB : ℕ) →
  subst Tm (+-suc sB N) ((e ⋯ weakenᵣ) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    ⋯ subst (λ z → suc (sB + N) →ᵣ z) (cong suc (+-suc sB N)) (weakenᵣ ↑* sB ↑ᵣ)
  ≡ subst Tm (+-suc (suc sB) N) ((e ⋯ weakenᵣ) ⋯ weaken* ⦃ Kᵣ ⦄ (suc sB))
ins-head-base {N} e sB =
    subst-⋯-cod (cong suc (+-suc sB N)) (subst Tm (+-suc sB N) ((e ⋯ weakenᵣ) ⋯ weaken* ⦃ Kᵣ ⦄ sB)) (weakenᵣ ↑* sB ↑ᵣ)
  ■ cong (subst Tm (cong suc (+-suc sB N)))
      ( subst-⋯ (+-suc sB N) ((e ⋯ weakenᵣ) ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weakenᵣ ↑* sB ↑ᵣ)
      ■ fusion (e ⋯ weakenᵣ) (weaken* ⦃ Kᵣ ⦄ sB) _
      ■ fusion e weakenᵣ _
      ■ ⋯-cong e agree
      ■ sym (fusion e weakenᵣ (weaken* ⦃ Kᵣ ⦄ (suc sB))) )
  ■ cong (λ z → subst Tm z ((e ⋯ weakenᵣ) ⋯ weaken* ⦃ Kᵣ ⦄ (suc sB))) (uipℕ (cong suc (+-suc sB N)) (+-suc (suc sB) N))
  where
    agree : (weakenᵣ ·ₖ (weaken* ⦃ Kᵣ ⦄ sB ·ₖ subst (λ z → z →ᵣ suc (sB + suc N)) (sym (+-suc sB N)) ((weakenᵣ ↑* sB) ↑ᵣ)))
            ≗ (weakenᵣ ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sB))
    agree v = Fin.toℕ-injective
      ( cong Fin.toℕ (subst-→ᵣ-app (+-suc sB N) ((weakenᵣ ↑* sB) ↑ᵣ) wv)
      ■ ↑*-hi weakenᵣ (suc sB) sw hh
      ■ cong (suc sB +_) (toℕ-wk 1 (Fin.reduce≥ sw hh) ■ cong suc redv ■ sym (toℕ-wk 1 v))
      ■ sym (toℕ-wk (suc sB) (weakenᵣ v)) )
      where
        wv = weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ v)
        sw = subst 𝔽 (+-suc sB N) wv
        swℕ : Fin.toℕ sw ≡ sB + Fin.toℕ (weakenᵣ v)
        swℕ = toℕ-subst𝔽 (+-suc sB N) wv ■ toℕ-wk sB (weakenᵣ v)
        hlem : suc sB Nat.≤ sB + Fin.toℕ (weakenᵣ v)
        hlem = subst (suc sB Nat.≤_) (sym (cong (sB +_) (toℕ-wk 1 v) ■ Nat.+-suc sB (Fin.toℕ v))) (Nat.m≤m+n (suc sB) (Fin.toℕ v))
        hh : suc sB Nat.≤ Fin.toℕ sw
        hh = subst (suc sB Nat.≤_) (sym swℕ) hlem
        redv : Fin.toℕ (Fin.reduce≥ sw hh) ≡ Fin.toℕ v
        redv = toℕ-reduce≥ sw hh ■ cong (Nat._∸ suc sB) swℕ
             ■ cong (Nat._∸ suc sB) (cong (sB +_) (toℕ-wk 1 v) ■ Nat.+-suc sB (Fin.toℕ v))
             ■ Nat.m+n∸m≡n (suc sB) (Fin.toℕ v)

-- A suc-shifted variable (toℕ ≥ suc sB after weaken* sB) gains one weaken* under the base insertion.
ins-var-base : ∀ {N} (sB : ℕ) (w : 𝔽 N) →
  subst (λ z → suc (sB + N) →ᵣ z) (cong suc (+-suc sB N)) (weakenᵣ ↑* sB ↑ᵣ)
    (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (Fin.suc w)))
  ≡ subst 𝔽 (+-suc (suc sB) N) (weaken* ⦃ Kᵣ ⦄ (suc sB) (Fin.suc w))
ins-var-base {N} sB w = Fin.toℕ-injective
  ( cong Fin.toℕ (subst-ren-cod (cong suc (+-suc sB N)) (weakenᵣ ↑* sB ↑ᵣ) sw)
  ■ toℕ-subst𝔽 (cong suc (+-suc sB N)) ((weakenᵣ ↑* sB ↑ᵣ) sw)
  ■ ↑*-hi weakenᵣ (suc sB) sw hh
  ■ cong (suc sB +_) (toℕ-wk 1 (Fin.reduce≥ sw hh) ■ cong suc redv)
  ■ sym (toℕ-wk (suc sB) (Fin.suc w))
  ■ sym (toℕ-subst𝔽 (+-suc (suc sB) N) (weaken* ⦃ Kᵣ ⦄ (suc sB) (Fin.suc w))) )
  where
    sw = subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (Fin.suc w))
    swℕ : Fin.toℕ sw ≡ sB + suc (Fin.toℕ w)
    swℕ = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (Fin.suc w)) ■ toℕ-wk sB (Fin.suc w)
    hh : suc sB Nat.≤ Fin.toℕ sw
    hh = subst (suc sB Nat.≤_) (sym (swℕ ■ Nat.+-suc sB (Fin.toℕ w))) (Nat.m≤m+n (suc sB) (Fin.toℕ w))
    redv : Fin.toℕ (Fin.reduce≥ sw hh) ≡ Fin.toℕ w
    redv = toℕ-reduce≥ sw hh ■ cong (Nat._∸ suc sB) (swℕ ■ Nat.+-suc sB (Fin.toℕ w)) ■ Nat.m+n∸m≡n (suc sB) (Fin.toℕ w)

-- The insertion renaming (weakenᵣ ↑* suc sB) agrees with weaken* (suc sB) on a term that
-- avoids var 0 (its leading weakenᵣ): both shift every var by 1 (the inserted slot at
-- suc sB is above all of t⋯weakenᵣ's vars, which are ≥ suc sB after weaken* sB).
-- canonₛ-handle's triple (a,x,c) at the consumed handle, rebased by the fresh-sync
-- insertion rins, agrees with canonₛ-sib-r's (a,x,c) (the head/mid/tail of the two new
-- handles).  Joint induction mirroring hc-sib-agree (chainRwk's compT/compF in the step).
hc-sib-agree-r : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  let hc  = canonₛ-handle B₁ cc b₁ B₂
      sib = canonₛ-sib-r   B₁ cc b₁ B₂ in
  (proj₁ hc ⋯ rins B₁ b₁ B₂ ≡ proj₁ sib)
  × (rins B₁ b₁ B₂ (proj₁ (proj₂ hc)) ≡ proj₁ (proj₂ sib))
  × (proj₁ (proj₂ (proj₂ hc)) ⋯ rins B₁ b₁ B₂ ≡ proj₁ (proj₂ (proj₂ sib)))
hc-sib-agree-r []            (e₁ , x , e₂) zero     []      = sym (⋯-id _ (λ _ → refl)) , refl , refl
hc-sib-agree-r []            (e₁ , x , e₂) (suc b₁) []      = sym (⋯-id _ (λ _ → refl)) , refl , refl
hc-sib-agree-r []            {N} (e₁ , x , e₂) zero     (b ∷ B) =
  ins-head-base e₁ (syncs (b ∷ B)) , ins-var-base (syncs (b ∷ B)) x ,
  ( cong (_⋯ rins [] zero (b ∷ B)) (subst-` (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F))
  ■ cong `_ inner
  ■ sym (subst-` (+-suc sB _ ■ +-suc (suc sB) N) (weaken* ⦃ Kᵣ ⦄ sB 0F)) )
  where
    sB = syncs (b ∷ B)
    v0 = subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F)
    v0ℕ : Fin.toℕ v0 ≡ sB
    v0ℕ = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F) ■ toℕ-wk sB 0F ■ Nat.+-identityʳ sB
    inner : rins [] zero (b ∷ B) v0 ≡ subst 𝔽 (+-suc sB _ ■ +-suc (suc sB) N) (weaken* ⦃ Kᵣ ⦄ sB 0F)
    inner = Fin.toℕ-injective
      ( cong Fin.toℕ (subst-ren-cod (cong suc (+-suc sB N)) (weakenᵣ ↑* sB ↑ᵣ) v0)
      ■ toℕ-subst𝔽 (cong suc (+-suc sB N)) ((weakenᵣ ↑* sB ↑ᵣ) v0)
      ■ ↑*-lo weakenᵣ (suc sB) v0 (subst (Nat._< suc sB) (sym v0ℕ) (Nat.n<1+n sB))
      ■ v0ℕ
      ■ sym ( toℕ-subst𝔽 (+-suc sB _ ■ +-suc (suc sB) N) (weaken* ⦃ Kᵣ ⦄ sB 0F)
            ■ toℕ-wk sB 0F ■ Nat.+-identityʳ sB ) )
hc-sib-agree-r []            {N} (e₁ , x , e₂) (suc b₁) (b ∷ B) =
  ins-head-base e₁ (syncs (b ∷ B)) , ins-var-base (syncs (b ∷ B)) x ,
  cong (_⋯ rins [] (suc b₁) (b ∷ B)) (subst-Kunit (+-suc (syncs (b ∷ B)) N))
hc-sib-agree-r (a ∷ [])      {N} (e₁ , x , e₂) b₁ B₂
  with hc-sib-agree-r [] {suc N} ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | h1 , h2 , h3 =
  ( subst-⋯-both eqD eqC _ (rins [] {suc N} b₁ B₂) ■ cong (subst Tm eqC) h1 ) ,
  ( subst₂→ᵣ-app eqD eqC (rins [] {suc N} b₁ B₂) _
  ■ cong (λ z → subst 𝔽 eqC (rins [] {suc N} b₁ B₂ z)) (subst-sym-subst eqD)
  ■ cong (subst 𝔽 eqC) h2 ) ,
  ( subst-⋯-both eqD eqC _ (rins [] {suc N} b₁ B₂) ■ cong (subst Tm eqC) h3 )
  where
    eqD = +-suc (syncs (suc b₁ ∷ B₂)) N
    eqC = +-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N
hc-sib-agree-r (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂
  with hc-sib-agree-r (d ∷ B₁″) {suc N} ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | h1 , h2 , h3 =
  ( subst-⋯-both eqD eqC _ (rins (d ∷ B₁″) {suc N} b₁ B₂) ■ cong (subst Tm eqC) h1 ) ,
  ( subst₂→ᵣ-app eqD eqC (rins (d ∷ B₁″) {suc N} b₁ B₂) _
  ■ cong (λ z → subst 𝔽 eqC (rins (d ∷ B₁″) {suc N} b₁ B₂ z)) (subst-sym-subst eqD)
  ■ cong (subst 𝔽 eqC) h2 ) ,
  ( subst-⋯-both eqD eqC _ (rins (d ∷ B₁″) {suc N} b₁ B₂) ■ cong (subst Tm eqC) h3 )
  where
    eqD = +-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N
    eqC = +-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N

-- φ^ block-split (only +-assoc, NO commutation): the inner p binders stay innermost.
-- Needed to position the fresh sync φ at junction sT inside the φ^ sC₁' nest.
φ^-split : ∀ p k {n} (Y : 𝐔.Proc (p + (k + n))) →
           φ^ k (φ^ p Y) ≡ φ^ (p + k) (subst 𝐔.Proc (sym (Nat.+-assoc p k n)) Y)
φ^-split zero    k {n} Y = refl
φ^-split (suc p') k {n} Y =
    φ^-split p' k (𝐔.φ Y)
  ■ cong (φ^ (p' + k))
      ( subst-φ-commute (sym (Nat.+-assoc p' k n)) Y
      ■ cong (λ e → 𝐔.φ (subst 𝐔.Proc e Y))
             (uipℕ (cong suc (sym (Nat.+-assoc p' k n))) (sym (Nat.+-assoc (suc p') k n))) )

-- Reverse of φ^-split: peel the inner t binders off a (t + r) block.
φ^-resplit : ∀ {N} (t r : ℕ) (W : 𝐔.Proc ((t + r) + N)) →
  φ^ (t + r) W ≡ φ^ r (φ^ t (subst 𝐔.Proc (Nat.+-assoc t r N) W))
φ^-resplit {N} t r W =
  sym ( φ^-split t r (subst 𝐔.Proc (Nat.+-assoc t r N) W)
      ■ cong (φ^ (t + r)) (subst-sym-subst (Nat.+-assoc t r N)) )

-- Move a fresh φ sitting at the bottom of a (sT + r) block up to position sT
-- (sT inner binders below it), renaming the body by assocSwapᵣ 1 sT.
slide : ∀ {N} (sT r : ℕ) (Z : 𝐔.Proc (suc ((sT + r) + N))) →
  φ^ (sT + r) (𝐔.φ Z) 𝐔.≋
  φ^ r (𝐔.φ (φ^ sT (subst 𝐔.Proc (cong suc (Nat.+-assoc sT r N)) Z
                       𝐔.⋯ₚ assocSwapᵣ 1 sT {r + N})))
slide {N} sT r Z =
     ≡→≋ (φ^-resplit sT r (𝐔.φ Z))
  ◅◅ ≡→≋ (cong (λ w → φ^ r (φ^ sT w)) (subst-φ-commute (Nat.+-assoc sT r N) Z))
  ◅◅ φ^-cong r (φ^-swap sT 1 {r + N} (subst 𝐔.Proc (cong suc (Nat.+-assoc sT r N)) Z))

slide' : ∀ {N} (kk sT r : ℕ) (ek : kk ≡ sT + r) (Z : 𝐔.Proc (suc (kk + N))) →
  φ^ kk (𝐔.φ Z) 𝐔.≋
  φ^ r (𝐔.φ (φ^ sT (subst 𝐔.Proc (cong suc (cong (Nat._+ N) ek ■ Nat.+-assoc sT r N)) Z
                       𝐔.⋯ₚ assocSwapᵣ 1 sT {r + N})))
slide' .(sT + r) sT r refl Z = slide sT r Z

-- Recombine [r outer][1 fresh][sT inner] back into one (sT+1)+r block.
recombine : ∀ {N} (sT r : ℕ) (V : 𝐔.Proc (sT + (1 + (r + N)))) →
  φ^ r (𝐔.φ (φ^ sT V)) ≡
  φ^ ((sT + 1) + r)
     (subst 𝐔.Proc (sym (Nat.+-assoc (sT + 1) r N))
        (subst 𝐔.Proc (sym (Nat.+-assoc sT 1 (r + N))) V))
recombine {N} sT r V =
    cong (φ^ r) (φ^-split sT 1 {r + N} V)
  ■ φ^-split (sT + 1) r {N} (subst 𝐔.Proc (sym (Nat.+-assoc sT 1 (r + N))) V)

-- ── frame-plug / frame fusion lemmas for the renaming kit (mirrors Frames' subst versions) ──
frame-plug*ᵣ : ∀ {m n} (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []      ρ = refl
frame-plug*ᵣ (F ∷ E) ρ =
  frame-plug₁ F ρ (λ _ → V-`) ■ cong (frame-⋯ F ρ (λ _ → V-`) [_]) (frame-plug*ᵣ E ρ)

⋯ᶠ*-fusion : ∀ {m m₁ p} (E : Frame* m) (ϕ : m →ᵣ m₁) (ψ : m₁ →ᵣ p) →
             (E ⋯ᶠ* ϕ) ⋯ᶠ* ψ ≡ E ⋯ᶠ* (ϕ ·ₖ ψ)
⋯ᶠ*-fusion []      ϕ ψ = refl
⋯ᶠ*-fusion (F ∷ E) ϕ ψ =
  cong₂ _∷_ (frame-fusion-gen F (λ _ → V-`) (λ _ → V-`) (λ _ → V-`)) (⋯ᶠ*-fusion E ϕ ψ)

frame*-⋯-then-ren : ∀ {m m₁ p} (E : Frame* m) {σ : m →ₛ m₁} (Vσ : VSub σ)
                    (ρ : m₁ →ᵣ p) (Vσρ : VSub (σ ·ₖ ρ)) →
                    (frame*-⋯ E σ Vσ) ⋯ᶠ* ρ ≡ frame*-⋯ E (σ ·ₖ ρ) Vσρ
frame*-⋯-then-ren []      Vσ ρ Vσρ = refl
frame*-⋯-then-ren (F ∷ E) {σ} Vσ ρ Vσρ =
  cong₂ _∷_ (frame-fusion-gen F Vσ (λ _ → V-`) Vσρ) (frame*-⋯-then-ren E Vσ ρ Vσρ)

-- the fresh-sync variable z returned by canonₛ-sib-r sits at sync-index sT = syncs (suc b₁ ∷ B₂).
canonₛ-sib-r-zℕ : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Fin.toℕ (proj₁ (proj₂ (proj₂ (proj₂ (canonₛ-sib-r B₁ cc b₁ B₂))))) ≡ syncs (suc b₁ ∷ B₂)
canonₛ-sib-r-zℕ []            (e₁ , cx , e₂) zero     []      = refl
canonₛ-sib-r-zℕ []            (e₁ , cx , e₂) (suc b₁) []      = refl
canonₛ-sib-r-zℕ []            {N} (e₁ , cx , e₂) zero     (b ∷ B) =
    toℕ-subst𝔽 (+-suc (syncs (suc zero ∷ b ∷ B)) N) (weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ b ∷ B)) 0F)
  ■ toℕ-wk (syncs (suc zero ∷ b ∷ B)) 0F
  ■ Nat.+-identityʳ (syncs (suc zero ∷ b ∷ B))
canonₛ-sib-r-zℕ []            {N} (e₁ , cx , e₂) (suc b₁) (b ∷ B) =
    toℕ-subst𝔽 (+-suc (syncs (suc (suc b₁) ∷ b ∷ B)) N) (weaken* ⦃ Kᵣ ⦄ (syncs (suc (suc b₁) ∷ b ∷ B)) 0F)
  ■ toℕ-wk (syncs (suc (suc b₁) ∷ b ∷ B)) 0F
  ■ Nat.+-identityʳ (syncs (suc (suc b₁) ∷ b ∷ B))
canonₛ-sib-r-zℕ (a ∷ [])      {N} (e₁ , cx , e₂) b₁ B₂
  with canonₛ-sib-r    [] {suc N} ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
     | canonₛ-sib-r-zℕ [] {suc N} ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , z′ , rp0 , rp1 | ih =
  toℕ-subst𝔽 (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) _) z′ ■ ih
canonₛ-sib-r-zℕ (a ∷ d ∷ B₁″) {N} (e₁ , cx , e₂) b₁ B₂
  with canonₛ-sib-r    (d ∷ B₁″) {suc N} ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
     | canonₛ-sib-r-zℕ (d ∷ B₁″) {suc N} ((` 0F) , suc cx , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , z′ , rp0 , rp1 | ih =
  toℕ-subst𝔽 (+-suc (syncs (d ∷ B₁″ ++ 1 ∷ suc b₁ ∷ B₂)) _) z′ ■ ih

-- The fresh flag's position inside Flags (B₁ ++ 1 ∷ suc b₁ ∷ B₂): sync-index sT.
insP : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
       𝔽 (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N)
insP []            {N} b₁ B₂ =
  subst 𝔽 (+-suc (syncs (suc b₁ ∷ B₂)) N) (weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂)) 0F)
insP (a ∷ [])      {N} b₁ B₂ =
  subst 𝔽 (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (insP [] {suc N} b₁ B₂)
insP (a ∷ d ∷ B₁″) {N} b₁ B₂ =
  subst 𝔽 (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (insP (d ∷ B₁″) {suc N} b₁ B₂)

insP-ℕ : ∀ (B₁ : 𝐓.BindGroup) {N} (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
         Fin.toℕ (insP B₁ {N} b₁ B₂) ≡ syncs (suc b₁ ∷ B₂)
insP-ℕ []            {N} b₁ B₂ =
    toℕ-subst𝔽 (+-suc (syncs (suc b₁ ∷ B₂)) N) (weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂)) 0F)
  ■ toℕ-wk (syncs (suc b₁ ∷ B₂)) 0F
  ■ Nat.+-identityʳ (syncs (suc b₁ ∷ B₂))
insP-ℕ (a ∷ [])      {N} b₁ B₂ =
    toℕ-subst𝔽 (+-suc (syncs (1 ∷ suc b₁ ∷ B₂)) N) (insP [] {suc N} b₁ B₂)
  ■ insP-ℕ [] {suc N} b₁ B₂
insP-ℕ (a ∷ d ∷ B₁″) {N} b₁ B₂ =
    toℕ-subst𝔽 (+-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N) (insP (d ∷ B₁″) {suc N} b₁ B₂)
  ■ insP-ℕ (d ∷ B₁″) {suc N} b₁ B₂

-- Flags of the grown group, under any renaming ρ, equals the fresh `1`-chain flag
-- (at sync-index sT) split off in parallel from Flags of the original group rebased by rins.
flagsRenMerge : ∀ (B₁ : 𝐓.BindGroup) {N b₁ B₂} {p} (ρ : (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) →ᵣ p) →
  Flags {N} (B₁ ++ 1 ∷ suc b₁ ∷ B₂) 𝐔.⋯ₚ ρ
  𝐔.≋ (ρ (insP B₁ {N} b₁ B₂) 𝐔.↦ 𝐔.unset)
      𝐔.∥ (Flags {N} (B₁ ++ suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins B₁ b₁ B₂ ·ₖ ρ))
flagsRenMerge [] {N} {b₁} {B₂} ρ = ≡→≋
  ( subst-⋯ₚ′ (+-suc sT N) flagFlags ρ
  ■ cong₂ 𝐔._∥_ flagEq restEq )
  where
    sT = syncs (suc b₁ ∷ B₂)
    flagFlags = ((0F 𝐔.↦ ϕ[ 1 ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sT) 𝐔.∥ Flags {suc N} (suc b₁ ∷ B₂)
    flagEq : ((0F 𝐔.↦ ϕ[ 1 ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sT) 𝐔.⋯ₚ subst (λ z → z →ᵣ _) (sym (+-suc sT N)) ρ
             ≡ (ρ (insP [] {N} b₁ B₂) 𝐔.↦ 𝐔.unset)
    flagEq = cong (𝐔._↦ 𝐔.unset) (subst-→ᵣ-app (+-suc sT N) ρ (weaken* ⦃ Kᵣ ⦄ sT 0F))
    hcong : ∀ (i : 𝔽 sT) → (weakenᵣ ↑* sT) (i ↑ˡ N) ≡ idₖ (i ↑ˡ suc N)
    hcong i = Fin.toℕ-injective
      ( ↑*-lo weakenᵣ sT (i ↑ˡ N) (subst (Nat._< sT) (sym (Fin.toℕ-↑ˡ i N)) (Fin.toℕ<n i))
      ■ Fin.toℕ-↑ˡ i N ■ sym (Fin.toℕ-↑ˡ i (suc N)) )
    restEq : Flags {suc N} (suc b₁ ∷ B₂) 𝐔.⋯ₚ subst (λ z → z →ᵣ _) (sym (+-suc sT N)) ρ
             ≡ Flags {N} (suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins [] b₁ B₂ ·ₖ ρ)
    restEq =
        sym (subst-⋯ₚ′ (+-suc sT N) (Flags {suc N} (suc b₁ ∷ B₂)) ρ)
      ■ cong (𝐔._⋯ₚ ρ)
          ( cong (subst 𝐔.Proc (+-suc sT N))
              (sym (Flags-⋯-cong (suc b₁ ∷ B₂) (weakenᵣ ↑* sT) idₖ hcong
                   ■ ⋯ₚ-id (Flags {suc N} (suc b₁ ∷ B₂)) (λ _ → refl)))
          ■ sym (subst-⋯ₚ-cod (+-suc sT N) (Flags {N} (suc b₁ ∷ B₂)) (weakenᵣ ↑* sT)) )
      ■ 𝐔.fusionₚ (Flags {N} (suc b₁ ∷ B₂)) (rins [] b₁ B₂) ρ
flagsRenMerge (a ∷ []) {N} {b₁} {B₂} ρ =
    ≡→≋ (subst-⋯ₚ′ (+-suc sC' N) flagFlags' ρ)
  ◅◅ 𝐔.∥-cong ε (flagsRenMerge [] {suc N} {b₁} {B₂} ρ̃)
  ◅◅ ∥-swap-mid
  ◅◅ ≡→≋ (cong₂ 𝐔._∥_ freshEq restEq')
  where
    sC  = syncs (suc b₁ ∷ B₂)
    sC' = syncs (1 ∷ suc b₁ ∷ B₂)
    ρ̃ : (sC' + suc N) →ᵣ _
    ρ̃ = subst (λ z → z →ᵣ _) (sym (+-suc sC' N)) ρ
    rmu : (sC + suc N) →ᵣ _
    rmu = subst (λ z → z →ᵣ _) (sym (+-suc sC N)) (rins (a ∷ []) b₁ B₂ ·ₖ ρ)
    flagFlags' = ((0F 𝐔.↦ ϕ[ a ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sC') 𝐔.∥ Flags {suc N} (1 ∷ suc b₁ ∷ B₂)
    flagFlagsC = ((0F 𝐔.↦ ϕ[ a ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sC) 𝐔.∥ Flags {suc N} (suc b₁ ∷ B₂)
    freshEq : (ρ̃ (insP [] {suc N} b₁ B₂) 𝐔.↦ 𝐔.unset) ≡ (ρ (insP (a ∷ []) {N} b₁ B₂) 𝐔.↦ 𝐔.unset)
    freshEq = cong (𝐔._↦ 𝐔.unset) (subst-→ᵣ-app (+-suc sC' N) ρ (insP [] {suc N} b₁ B₂))
    sT≤ : syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F))
    sT≤ = subst (syncs (suc b₁ ∷ B₂) Nat.≤_)
            (sym (toℕ-subst𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F) ■ toℕ-wk sC 0F ■ Nat.+-identityʳ sC))
            Nat.≤-refl
    posInner : subst 𝔽 (+-suc sC' N) (weaken* ⦃ Kᵣ ⦄ sC' 0F)
               ≡ rins (a ∷ []) b₁ B₂ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F))
    posInner = Fin.toℕ-injective
      ( toℕ-subst𝔽 (+-suc sC' N) (weaken* ⦃ Kᵣ ⦄ sC' 0F) ■ toℕ-wk sC' 0F ■ Nat.+-identityʳ sC'
      ■ sym ( rins-hi (a ∷ []) b₁ B₂ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F)) sT≤
            ■ cong suc (toℕ-subst𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F) ■ toℕ-wk sC 0F ■ Nat.+-identityʳ sC) ) )
    flagAEq : ((ρ̃ (weaken* ⦃ Kᵣ ⦄ sC' 0F)) 𝐔.↦ ϕ[ a ]) ≡ ((rmu (weaken* ⦃ Kᵣ ⦄ sC 0F)) 𝐔.↦ ϕ[ a ])
    flagAEq = cong (𝐔._↦ ϕ[ a ])
      ( subst-→ᵣ-app (+-suc sC' N) ρ (weaken* ⦃ Kᵣ ⦄ sC' 0F)
      ■ cong ρ posInner
      ■ sym (subst-→ᵣ-app (+-suc sC N) (rins (a ∷ []) b₁ B₂ ·ₖ ρ) (weaken* ⦃ Kᵣ ⦄ sC 0F)) )
    ptw-ii : (rins [] b₁ B₂ ·ₖ ρ̃) ≗ rmu
    ptw-ii x =
        subst-→ᵣ-app (+-suc sC' N) ρ (rins [] b₁ B₂ x)
      ■ sym ( subst-→ᵣ-app (+-suc sC N) (rins (a ∷ []) b₁ B₂ ·ₖ ρ) x
            ■ cong ρ ( subst₂→ᵣ-app (+-suc sC N) (+-suc sC' N) (rins [] b₁ B₂) (subst 𝔽 (+-suc sC N) x)
                     ■ cong (λ z → subst 𝔽 (+-suc sC' N) (rins [] b₁ B₂ z)) (subst-sym-subst (+-suc sC N)) ) )
    restEq' : (((ρ̃ (weaken* ⦃ Kᵣ ⦄ sC' 0F)) 𝐔.↦ ϕ[ a ]) 𝐔.∥ (Flags {suc N} (suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins [] b₁ B₂ ·ₖ ρ̃)))
              ≡ (Flags {N} (a ∷ suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins (a ∷ []) b₁ B₂ ·ₖ ρ))
    restEq' =
        cong₂ 𝐔._∥_ flagAEq (𝐔.⋯ₚ-cong (Flags {suc N} (suc b₁ ∷ B₂)) ptw-ii)
      ■ sym (subst-⋯ₚ′ (+-suc sC N) flagFlagsC (rins (a ∷ []) b₁ B₂ ·ₖ ρ))
flagsRenMerge (a ∷ d ∷ B₁″) {N} {b₁} {B₂} ρ =
    ≡→≋ (subst-⋯ₚ′ (+-suc sC' N) flagFlags' ρ)
  ◅◅ 𝐔.∥-cong ε (flagsRenMerge (d ∷ B₁″) {suc N} {b₁} {B₂} ρ̃)
  ◅◅ ∥-swap-mid
  ◅◅ ≡→≋ (cong₂ 𝐔._∥_ freshEq restEq')
  where
    sC  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sC' = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    ρ̃ : (sC' + suc N) →ᵣ _
    ρ̃ = subst (λ z → z →ᵣ _) (sym (+-suc sC' N)) ρ
    rmu : (sC + suc N) →ᵣ _
    rmu = subst (λ z → z →ᵣ _) (sym (+-suc sC N)) (rins (a ∷ d ∷ B₁″) b₁ B₂ ·ₖ ρ)
    flagFlags' = ((0F 𝐔.↦ ϕ[ a ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sC') 𝐔.∥ Flags {suc N} ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    flagFlagsC = ((0F 𝐔.↦ ϕ[ a ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sC) 𝐔.∥ Flags {suc N} ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    freshEq : (ρ̃ (insP (d ∷ B₁″) {suc N} b₁ B₂) 𝐔.↦ 𝐔.unset) ≡ (ρ (insP (a ∷ d ∷ B₁″) {N} b₁ B₂) 𝐔.↦ 𝐔.unset)
    freshEq = cong (𝐔._↦ 𝐔.unset) (subst-→ᵣ-app (+-suc sC' N) ρ (insP (d ∷ B₁″) {suc N} b₁ B₂))
    sT≤ : syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F))
    sT≤ = subst (syncs (suc b₁ ∷ B₂) Nat.≤_)
            (sym (toℕ-subst𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F) ■ toℕ-wk sC 0F ■ Nat.+-identityʳ sC))
            (sT≤syncs (d ∷ B₁″))
    posInner : subst 𝔽 (+-suc sC' N) (weaken* ⦃ Kᵣ ⦄ sC' 0F)
               ≡ rins (a ∷ d ∷ B₁″) b₁ B₂ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F))
    posInner = Fin.toℕ-injective
      ( toℕ-subst𝔽 (+-suc sC' N) (weaken* ⦃ Kᵣ ⦄ sC' 0F) ■ toℕ-wk sC' 0F ■ Nat.+-identityʳ sC'
      ■ syncs-rwk (d ∷ B₁″) {b₁} {B₂}
      ■ sym ( rins-hi (a ∷ d ∷ B₁″) b₁ B₂ (subst 𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F)) sT≤
            ■ cong suc (toℕ-subst𝔽 (+-suc sC N) (weaken* ⦃ Kᵣ ⦄ sC 0F) ■ toℕ-wk sC 0F ■ Nat.+-identityʳ sC) ) )
    flagAEq : ((ρ̃ (weaken* ⦃ Kᵣ ⦄ sC' 0F)) 𝐔.↦ ϕ[ a ]) ≡ ((rmu (weaken* ⦃ Kᵣ ⦄ sC 0F)) 𝐔.↦ ϕ[ a ])
    flagAEq = cong (𝐔._↦ ϕ[ a ])
      ( subst-→ᵣ-app (+-suc sC' N) ρ (weaken* ⦃ Kᵣ ⦄ sC' 0F)
      ■ cong ρ posInner
      ■ sym (subst-→ᵣ-app (+-suc sC N) (rins (a ∷ d ∷ B₁″) b₁ B₂ ·ₖ ρ) (weaken* ⦃ Kᵣ ⦄ sC 0F)) )
    ptw-ii : (rins (d ∷ B₁″) b₁ B₂ ·ₖ ρ̃) ≗ rmu
    ptw-ii x =
        subst-→ᵣ-app (+-suc sC' N) ρ (rins (d ∷ B₁″) b₁ B₂ x)
      ■ sym ( subst-→ᵣ-app (+-suc sC N) (rins (a ∷ d ∷ B₁″) b₁ B₂ ·ₖ ρ) x
            ■ cong ρ ( subst₂→ᵣ-app (+-suc sC N) (+-suc sC' N) (rins (d ∷ B₁″) b₁ B₂) (subst 𝔽 (+-suc sC N) x)
                     ■ cong (λ z → subst 𝔽 (+-suc sC' N) (rins (d ∷ B₁″) b₁ B₂ z)) (subst-sym-subst (+-suc sC N)) ) )
    restEq' : (((ρ̃ (weaken* ⦃ Kᵣ ⦄ sC' 0F)) 𝐔.↦ ϕ[ a ]) 𝐔.∥ (Flags {suc N} ((d ∷ B₁″) ++ suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins (d ∷ B₁″) b₁ B₂ ·ₖ ρ̃)))
              ≡ (Flags {N} (a ∷ (d ∷ B₁″) ++ suc b₁ ∷ B₂) 𝐔.⋯ₚ (rins (a ∷ d ∷ B₁″) b₁ B₂ ·ₖ ρ))
    restEq' =
        cong₂ 𝐔._∥_ flagAEq (𝐔.⋯ₚ-cong (Flags {suc N} ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) ptw-ii)
      ■ sym (subst-⋯ₚ′ (+-suc sC N) flagFlagsC (rins (a ∷ d ∷ B₁″) b₁ B₂ ·ₖ ρ))

-- ════════════════════════════════════════════════════════════════════════════
-- U-rsplit: forward simulation for remote channel split.  LHS half is identical to
-- U-lsplit (same redex / bind group C₁); the firing is RU-RSplit (introduces a φ).
-- ════════════════════════════════════════════════════════════════════════════
U-rsplit : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {B₁ B₂ B : 𝐓.BindGroup} {b₁ : ℕ} {s : 𝕊 0}
           {E : Frame* (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
           {P : 𝐓.Proc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)} →
           let module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B in
           -- Well-typedness of the redex (supplied by sim→ via the confinement lemma):
           -- the consumed handle 𝐒.inj 0F is linear, so the frame E and the parallel P
           -- both factor through a renaming ρ⁻ whose image avoids it.
           {k : ℕ} (ρ⁻ : k →ᵣ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
           (∀ y → ρ⁻ y ≢ 𝐒.inj {suc b₁ ∷ []} {m} 0F) →
           {E₀ : Frame* k} → E ≡ E₀ ⋯ᶠ* ρ⁻ →
           {P₀ : 𝐓.Proc k} → P ≡ P₀ 𝐓.⋯ₚ ρ⁻ →
           U[ 𝐓.ν (B₁ ++ suc b₁ ∷ B₂) B
                (𝐓.⟪ E [ K (`rsplit s) · (` 𝐒.inj 0F) ]* ⟫ 𝐓.∥ P) ] σ
             𝐔R.─→ₚ
           U[ 𝐓.ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B
                (𝐓.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫
                 𝐓.∥ (P 𝐓.⋯ₚ 𝐒.rwk)) ] σ
U-rsplit {m} {n} σ Vσ {B₁} {B₂} {B} {b₁} {s} {E} {P} ρ⁻ ρ⁻-skip {E₀} Eeq {P₀} Peq =
  𝐔R.RU-Struct
    (Uν-flat σ C₁ B Q ◅◅ step2L ◅◅ step3L)
    (φ^-─→ sC₁ (φ^-─→ sB (𝐔R.RU-RSplit Fr)))
    (mr ◅◅ Eq*.symmetric _ reverseChain)
  where
    module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
    C₁ : 𝐓.BindGroup
    C₁ = B₁ ++ suc b₁ ∷ B₂
    Q : 𝐓.Proc (sum C₁ + sum B + m)
    Q = 𝐓.⟪ E [ K (`rsplit s) · (` 𝐒.inj 0F) ]* ⟫ 𝐓.∥ P
    sC₁ = syncs C₁
    sB  = syncs B
    cc1 : UChan (2 + n)
    cc1 = (K `unit , 0F , K `unit)
    cc2 : UChan (sC₁ + (2 + n))
    cc2 = (K `unit , weaken* ⦃ Kᵣ ⦄ sC₁ 1F , K `unit)
    Xleaf : (sum C₁ + sum B) →ₛ (sB + (sC₁ + (2 + n)))
    Xleaf = (λ i → canonₛ C₁ cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) ++ₛ canonₛ B cc2
    σpart : m →ₛ (sB + (sC₁ + (2 + n)))
    σpart = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    leafσ : (sum C₁ + sum B + m) →ₛ (sB + (sC₁ + (2 + n)))
    leafσ = Xleaf ++ₛ σpart
    Vleafσ : VSub leafσ
    Vleafσ = ++ₛ-VSub
      (++ₛ-VSub (weaken-VSub sB (VSub-canonₛ C₁ cc1 (V-K , V-K)))
                (VSub-canonₛ B cc2 (V-K , V-K)))
      (weaken-VSub sB (weaken-VSub sC₁ (weaken-VSub 2 Vσ)))
    castpos : 𝔽 (sum C₁)
    castpos = Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
    leafσ-inj0 : leafσ (𝐒.inj 0F) ≡ canonₛ C₁ cc1 castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
    leafσ-inj0 =
        cong [ Xleaf , σpart ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
      ■ cong [ (λ i → canonₛ C₁ cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2 ]′
             (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
    BODY_L : 𝐔.Proc (sB + (sC₁ + (2 + n)))
    BODY_L = (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.∥ (Flags B 𝐔.∥ U[ Q ] leafσ)
    step2L : 𝐔.ν (φ^ sC₁ (φ^ sB BODY_L)) 𝐔.≋
             φ^ sC₁ (φ^ sB (𝐔.ν (BODY_L 𝐔.⋯ₚ (assocSwapᵣ sC₁ 2 ↑* sB) 𝐔.⋯ₚ assocSwapᵣ sB 2)))
    step2L =
         ν-φ^-comm sC₁ {n} (φ^ sB BODY_L)
      ◅◅ φ^-cong sC₁ (𝐔.ν-cong (≡→≋ (φ^-⋯ₚ sB BODY_L (assocSwapᵣ sC₁ 2))))
      ◅◅ φ^-cong sC₁ (ν-φ^-comm sB {sC₁ + n} (BODY_L 𝐔.⋯ₚ (assocSwapᵣ sC₁ 2 ↑* sB)))
    ρ₁ : (sB + (sC₁ + (2 + n))) →ᵣ (sB + (2 + (sC₁ + n)))
    ρ₁ = assocSwapᵣ sC₁ 2 ↑* sB
    ρ₂ : (sB + (2 + (sC₁ + n))) →ᵣ (2 + (sB + (sC₁ + n)))
    ρ₂ = assocSwapᵣ sB 2
    ρ₁₂ : (sB + (sC₁ + (2 + n))) →ᵣ (2 + (sB + (sC₁ + n)))
    ρ₁₂ = ρ₁ ·ₖ ρ₂
    σ' : (sum C₁ + sum B + m) →ₛ (2 + (sB + (sC₁ + n)))
    σ' = leafσ ·ₖ ρ₁₂
    Vσ' : VSub σ'
    Vσ' i = value-⋯ (Vleafσ i) ρ₁₂ (λ _ → V-`)
    Fr : Frame* (2 + (sB + (sC₁ + n)))
    Fr = frame*-⋯ E σ' Vσ'
    hc = canonₛ-handle B₁ cc1 b₁ B₂
    Xch : 𝔽 (2 + (sB + (sC₁ + n)))
    Xch = ρ₁₂ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ hc)))
    redexTriple : Tm (2 + (sB + (sC₁ + n)))
    redexTriple =
      ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂) ⊗ (` Xch))
      ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂)
    σ'inj0 : σ' (𝐒.inj 0F) ≡ redexTriple
    σ'inj0 = cong (_⋯ ρ₁₂) (leafσ-inj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₂ (proj₂ (proj₂ hc))))
    RpForm : ((E [ K (`rsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ⋯ ρ₁ ⋯ ρ₂
             ≡ Fr [ K (`rsplit s) · redexTriple ]*
    RpForm =
        fusion ((E [ K (`rsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ρ₁ ρ₂
      ■ fusion (E [ K (`rsplit s) · (` 𝐒.inj 0F) ]*) leafσ ρ₁₂
      ■ frame-plug* E σ' Vσ'
      ■ cong (λ z → Fr [ K (`rsplit s) · z ]*) σ'inj0
    G1 G2 Sp RpThread Prest : 𝐔.Proc (2 + (sB + (sC₁ + n)))
    G1 = (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    G2 = Flags B 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    Sp = U[ P ] leafσ 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    RpThread = 𝐔.⟪ ((E [ K (`rsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ⋯ ρ₁ ⋯ ρ₂ ⟫
    Prest = G2 𝐔.∥ (G1 𝐔.∥ Sp)
    step3L : φ^ sC₁ (φ^ sB (𝐔.ν (BODY_L 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂))) 𝐔.≋
             φ^ sC₁ (φ^ sB (𝐔.ν (𝐔.⟪ Fr [ K (`rsplit s) · redexTriple ]* ⟫ 𝐔.∥ Prest)))
    step3L = φ^-cong sC₁ (φ^-cong sB (𝐔.ν-cong
               ( reorder-front G1 G2 RpThread Sp
               ◅◅ ≡→≋ (cong (𝐔._∥ Prest) (cong 𝐔.⟪_⟫ RpForm)) )))
    -- ── RHS side (C₁' = the grown bind group): a cast-free mirror of the lhs chain. ──
    C₁' : 𝐓.BindGroup
    C₁' = B₁ ++ 1 ∷ suc b₁ ∷ B₂
    sC₁' = syncs C₁'
    Q' : 𝐓.Proc (sum C₁' + sum B + m)
    Q' = 𝐓.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ 𝐓.∥ (P 𝐓.⋯ₚ 𝐒.rwk)
    cc2' : UChan (sC₁' + (2 + n))
    cc2' = (K `unit , weaken* ⦃ Kᵣ ⦄ sC₁' 1F , K `unit)
    Xleaf' : (sum C₁' + sum B) →ₛ (sB + (sC₁' + (2 + n)))
    Xleaf' = (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) ++ₛ canonₛ B cc2'
    σpart' : m →ₛ (sB + (sC₁' + (2 + n)))
    σpart' = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC₁' ⋯ weaken* ⦃ Kᵣ ⦄ sB
    leafσ' : (sum C₁' + sum B + m) →ₛ (sB + (sC₁' + (2 + n)))
    leafσ' = Xleaf' ++ₛ σpart'
    Vleafσ' : VSub leafσ'
    Vleafσ' = ++ₛ-VSub
      (++ₛ-VSub (weaken-VSub sB (VSub-canonₛ C₁' cc1 (V-K , V-K)))
                (VSub-canonₛ B cc2' (V-K , V-K)))
      (weaken-VSub sB (weaken-VSub sC₁' (weaken-VSub 2 Vσ)))
    BODY_R : 𝐔.Proc (sB + (sC₁' + (2 + n)))
    BODY_R = (Flags C₁' 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.∥ (Flags B 𝐔.∥ U[ Q' ] leafσ')
    ρ₁' : (sB + (sC₁' + (2 + n))) →ᵣ (sB + (2 + (sC₁' + n)))
    ρ₁' = assocSwapᵣ sC₁' 2 ↑* sB
    step2R : 𝐔.ν (φ^ sC₁' (φ^ sB BODY_R)) 𝐔.≋
             φ^ sC₁' (φ^ sB (𝐔.ν (BODY_R 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2)))
    step2R =
         ν-φ^-comm sC₁' {n} (φ^ sB BODY_R)
      ◅◅ φ^-cong sC₁' (𝐔.ν-cong (≡→≋ (φ^-⋯ₚ sB BODY_R (assocSwapᵣ sC₁' 2))))
      ◅◅ φ^-cong sC₁' (ν-φ^-comm sB {sC₁' + n} (BODY_R 𝐔.⋯ₚ ρ₁'))
    G1_R G2_R Sp_R RpThread_R Prest_R : 𝐔.Proc (2 + (sB + (sC₁' + n)))
    G1_R = (Flags C₁' 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2
    G2_R = Flags B 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2
    Sp_R = U[ P 𝐓.⋯ₚ 𝐒.rwk ] leafσ' 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2
    RpThread_R = 𝐔.⟪ (((E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]*) ⋯ leafσ') ⋯ ρ₁') ⋯ assocSwapᵣ sB 2 ⟫
    Prest_R = G2_R 𝐔.∥ (G1_R 𝐔.∥ Sp_R)
    reorderR : φ^ sC₁' (φ^ sB (𝐔.ν (BODY_R 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2))) 𝐔.≋
               φ^ sC₁' (φ^ sB (𝐔.ν (RpThread_R 𝐔.∥ Prest_R)))
    reorderR = φ^-cong sC₁' (φ^-cong sB (𝐔.ν-cong (reorder-front G1_R G2_R RpThread_R Sp_R)))
    reverseChain : U[ 𝐓.ν C₁' B Q' ] σ 𝐔.≋ φ^ sC₁' (φ^ sB (𝐔.ν (RpThread_R 𝐔.∥ Prest_R)))
    reverseChain = Uν-flat σ C₁' B Q' ◅◅ step2R ◅◅ reorderR
    sT : ℕ
    sT = syncs (suc b₁ ∷ B₂)
    r : ℕ
    r = sC₁ Nat.∸ sT
    sCsT : sT + r ≡ sC₁
    sCsT = Nat.m+[n∸m]≡n (sT≤syncs B₁ {b₁} {B₂})
    e'' : (sT + 1) + r ≡ sC₁'
    e'' = cong (Nat._+ r) (Nat.+-comm sT 1) ■ cong suc sCsT ■ sym (syncs-rwk B₁ {b₁} {B₂})
    mr = φ^-cong sC₁ (φ^-cong sB (ν-φ^-comm 1 _))
       ◅◅ φ^-cong sC₁ (φ^-swap sB 1 {sC₁ + n} _)
       ◅◅ slide' sC₁ sT r (sym sCsT) _
       ◅◅ ≡→≋ (recombine sT r _)
       ◅◅ ≡→≋ (φ^-cast e'' _)
       ◅◅ φ^-cong sC₁' dataReconcile
      where
        M1 = cong suc (cong (Nat._+ n) (sym sCsT) ■ Nat.+-assoc sT r n)
        M2 = sym (Nat.+-assoc sT 1 (r + n))
        M3 = sym (Nat.+-assoc (sT + 1) r n)
        compRec = assembled
          where
            reorder = ∥-swap-mid ◅◅ 𝐔.∥-cong ε (∥-swap-mid ◅◅ 𝐔.∥-cong ε 𝐔.∥-assoc)
            θ4 : suc (sC₁ + n) →ᵣ (sC₁' + n)
            θ4 = subst (λ z → suc (sC₁ + n) →ᵣ z) (cong (Nat._+ n) e'')
                   (subst (λ z → suc (sC₁ + n) →ᵣ z) M3
                     (subst (λ z → suc (sC₁ + n) →ᵣ z) M2
                       (subst (λ z → z →ᵣ (sT + (1 + (r + n)))) (sym M1)
                         (assocSwapᵣ 1 sT {r + n}))))
            aS12 = assocSwapᵣ 1 2 {sB + (sC₁ + n)}
            aS1sB = assocSwapᵣ 1 sB {sC₁ + n} ↑* 2
            ρB = θ4 ↑* sB ↑* 2
            -- toℕ of the full trailing composite on the (shifted) sB-block: 2+q ↦ 2+q.
            sB-trail : (q : ℕ) (y : 𝔽 (2 + (sB + (sC₁ + n)))) → Fin.toℕ y ≡ 2 + q → q Nat.< sB →
                       Fin.toℕ ((weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))) y) ≡ 2 + q
            sB-trail q y yq qlt =
                ↑*-hi (θ4 ↑* sB) 2 (aS1sB (aS12 (weakenᵣ y))) twoLE
              ■ cong (2 +_)
                  ( ↑*-lo θ4 sB (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ y))) twoLE) reduceLT
                  ■ reduceEq )
              where
                wkℕ : Fin.toℕ (weakenᵣ y) ≡ 3 + q
                wkℕ = cong suc yq
                aS12ℕ : Fin.toℕ (aS12 (weakenᵣ y)) ≡ 3 + q
                aS12ℕ = toℕ-assoc-ge 1 2 (weakenᵣ y) (subst (3 Nat.≤_) (sym wkℕ) (Nat.s≤s (Nat.s≤s (Nat.s≤s Nat.z≤n)))) ■ wkℕ
                twoLE' : 2 Nat.≤ Fin.toℕ (aS12 (weakenᵣ y))
                twoLE' = subst (2 Nat.≤_) (sym aS12ℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                reduceℕ : Fin.toℕ (Fin.reduce≥ (aS12 (weakenᵣ y)) twoLE') ≡ 1 + q
                reduceℕ = toℕ-reduce≥ (aS12 (weakenᵣ y)) twoLE' ■ cong (Nat._∸ 2) aS12ℕ
                innerℕ : Fin.toℕ (assocSwapᵣ 1 sB (Fin.reduce≥ (aS12 (weakenᵣ y)) twoLE')) ≡ q
                innerℕ = toℕ-assoc-mid 1 sB (Fin.reduce≥ (aS12 (weakenᵣ y)) twoLE')
                           (subst (1 Nat.≤_) (sym reduceℕ) (Nat.s≤s Nat.z≤n))
                           (subst (Nat._< 1 + sB) (sym reduceℕ) (Nat.s≤s qlt))
                       ■ cong (Nat._∸ 1) reduceℕ
                aS1sBℕ : Fin.toℕ (aS1sB (aS12 (weakenᵣ y))) ≡ 2 + q
                aS1sBℕ = ↑*-hi (assocSwapᵣ 1 sB) 2 (aS12 (weakenᵣ y)) twoLE' ■ cong (2 +_) innerℕ
                twoLE : 2 Nat.≤ Fin.toℕ (aS1sB (aS12 (weakenᵣ y)))
                twoLE = subst (2 Nat.≤_) (sym aS1sBℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                reduceEq : Fin.toℕ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ y))) twoLE) ≡ q
                reduceEq = toℕ-reduce≥ (aS1sB (aS12 (weakenᵣ y))) twoLE ■ cong (Nat._∸ 2) aS1sBℕ
                reduceLT : Fin.toℕ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ y))) twoLE) Nat.< sB
                reduceLT = subst (Nat._< sB) (sym reduceEq) qlt
            -- Fuse a leaf P through the full 6-renaming trailing chain into one composite.
            fuse6 : (P : 𝐔.Proc (sB + (sC₁ + (2 + n)))) →
                    P 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂ 𝐔.⋯ₚ weakenᵣ 𝐔.⋯ₚ aS12 𝐔.⋯ₚ aS1sB 𝐔.⋯ₚ ρB
                    ≡ P 𝐔.⋯ₚ (ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB)))))
            fuse6 P =
                𝐔.fusionₚ (P 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂ 𝐔.⋯ₚ weakenᵣ 𝐔.⋯ₚ aS12) aS1sB ρB
              ■ 𝐔.fusionₚ (P 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂ 𝐔.⋯ₚ weakenᵣ) aS12 (aS1sB ·ₖ ρB)
              ■ 𝐔.fusionₚ (P 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂) weakenᵣ (aS12 ·ₖ (aS1sB ·ₖ ρB))
              ■ 𝐔.fusionₚ (P 𝐔.⋯ₚ ρ₁) ρ₂ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB)))
              ■ 𝐔.fusionₚ P ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))
            hG2 : (i : 𝔽 (syncs B)) →
                  (ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))) (i ↑ˡ (sC₁ + (2 + n)))
                  ≡ (ρ₁' ·ₖ assocSwapᵣ sB 2) (i ↑ˡ (sC₁' + (2 + n)))
            hG2 i = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
              where
                x = i ↑ˡ (sC₁ + (2 + n))
                y = i ↑ˡ (sC₁' + (2 + n))
                iℕ : Fin.toℕ i Nat.< sB
                iℕ = Fin.toℕ<n i
                xℕ : Fin.toℕ x ≡ Fin.toℕ i
                xℕ = Fin.toℕ-↑ˡ i (sC₁ + (2 + n))
                yℕ : Fin.toℕ y ≡ Fin.toℕ i
                yℕ = Fin.toℕ-↑ˡ i (sC₁' + (2 + n))
                ρ₁xℕ : Fin.toℕ (ρ₁ x) ≡ Fin.toℕ i
                ρ₁xℕ = ↑*-lo (assocSwapᵣ sC₁ 2) sB x (subst (Nat._< sB) (sym xℕ) iℕ) ■ xℕ
                ρ₂ρ₁xℕ : Fin.toℕ (ρ₂ (ρ₁ x)) ≡ 2 + Fin.toℕ i
                ρ₂ρ₁xℕ = toℕ-assoc-lt sB 2 (ρ₁ x) (subst (Nat._< sB) (sym ρ₁xℕ) iℕ)
                       ■ cong (2 +_) ρ₁xℕ
                lhsℕ : Fin.toℕ ((ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))) x) ≡ 2 + Fin.toℕ i
                lhsℕ = sB-trail (Fin.toℕ i) (ρ₂ (ρ₁ x)) ρ₂ρ₁xℕ iℕ
                ρ₁'yℕ : Fin.toℕ (ρ₁' y) ≡ Fin.toℕ i
                ρ₁'yℕ = ↑*-lo (assocSwapᵣ sC₁' 2) sB y (subst (Nat._< sB) (sym yℕ) iℕ) ■ yℕ
                rhsℕ : Fin.toℕ ((ρ₁' ·ₖ assocSwapᵣ sB 2) y) ≡ 2 + Fin.toℕ i
                rhsℕ = toℕ-assoc-lt sB 2 (ρ₁' y) (subst (Nat._< sB) (sym ρ₁'yℕ) iℕ)
                     ■ cong (2 +_) ρ₁'yℕ
            G2Eq = ≡→≋
              ( fuse6 (Flags B)
              ■ Flags-⋯-cong B (ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))) (ρ₁' ·ₖ assocSwapᵣ sB 2) hG2
              ■ sym (𝐔.fusionₚ (Flags B) ρ₁' (assocSwapᵣ sB 2)) )
            -- ── the leaf identity off the consumed handle, for the rsplit insertion ──
            rinsB : (sC₁ + (2 + n)) →ᵣ (sC₁' + (2 + n))
            rinsB = rins B₁ b₁ B₂
            -- weaken* sB then insert = insert then weaken* sB.
            wkcom : (t : Tm (sC₁ + (2 + n))) →
                    (t ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ (rinsB ↑* sB) ≡ (t ⋯ rinsB) ⋯ weaken* ⦃ Kᵣ ⦄ sB
            wkcom t = fusion t (weaken* ⦃ Kᵣ ⦄ sB) (rinsB ↑* sB)
                    ■ ⋯-cong t (λ z → sym (↑*-wk rinsB sB z))
                    ■ sym (fusion t rinsB (weaken* ⦃ Kᵣ ⦄ sB))
            -- weaken into the sC₁ block, then insert below it, is weaken into sC₁'.
            wkC₁-rins : (t : Tm (2 + n)) →
                        (t ⋯ weaken* ⦃ Kᵣ ⦄ sC₁) ⋯ rinsB ≡ t ⋯ weaken* ⦃ Kᵣ ⦄ sC₁'
            wkC₁-rins t = fusion t (weaken* ⦃ Kᵣ ⦄ sC₁) rinsB
                        ■ ⋯-cong t (λ z → rins-wk B₁ b₁ B₂ z)
            -- data region: canonₛ rebased by the insertion is canonₛ on the grown group.
            data-coh-r : (d : 𝔽 (sum C₁)) → d ≢ castpos →
                         (canonₛ C₁ cc1 d ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ (rinsB ↑* sB)
                         ≡ canonₛ C₁' cc1 (drwk B₁ b₁ B₂ d) ⋯ weaken* ⦃ Kᵣ ⦄ sB
            data-coh-r d d≢ = wkcom (canonₛ C₁ cc1 d)
                            ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (canonₛ-rwk B₁ cc1 b₁ B₂ d d≢)
            -- B region: the B-channel rebased by the insertion is the B-channel for cc2'.
            cc2-rins : cc2' ≡ mapᶜ rinsB cc2
            cc2-rins = cong (λ z → (K `unit , z , K `unit)) (sym (rins-wk B₁ b₁ B₂ 1F))
            canonB-coh-r : (w : 𝔽 (sum B)) →
                           canonₛ B cc2 w ⋯ (rinsB ↑* sB) ≡ canonₛ B cc2' w
            canonB-coh-r w = sym (canonₛ-nat B cc2 rinsB w)
                           ■ cong (λ z → canonₛ B z w) (sym cc2-rins)
            -- σ region: the outer substitution part rebased by the insertion.
            σ-coh-r : (u : 𝔽 m) → σpart u ⋯ (rinsB ↑* sB) ≡ σpart' u
            σ-coh-r u = wkcom (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC₁)
                      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (wkC₁-rins (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2))
            rwk-id-off0 : (i : 𝔽 (sum C₁ + sum B + m)) → i ≢ 𝐒.inj {suc b₁ ∷ []} {m} 0F →
                          leafσ i ⋯ (rinsB ↑* sB) ≡ leafσ' (𝐒.rwk i)
            rwk-id-off0 i i≢ with splitAt (sum C₁ + sum B) i | Fin.join-splitAt (sum C₁ + sum B) m i
            ... | inj₂ u  | jeq =
                  σ-coh-r u
                ■ sym ( cong leafσ' (cong 𝐒.rwk (sym jeq) ■ P3r B₁ B₂ B u)
                      ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ʳ (sum C₁' + sum B) m u) )
            ... | inj₁ db | jeq with splitAt (sum C₁) db | Fin.join-splitAt (sum C₁) (sum B) db
            ...   | inj₂ w | jeq2 =
                    canonB-coh-r w
                  ■ sym ( cong leafσ' (cong 𝐒.rwk ieq ■ P2r B₁ B₂ B w)
                        ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (sum C₁' ↑ʳ w) m)
                        ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                               (Fin.splitAt-↑ʳ (sum C₁') (sum B) w) )
              where ieq : i ≡ (sum C₁ ↑ʳ w) ↑ˡ m
                    ieq = sym jeq ■ cong (_↑ˡ m) (sym jeq2)
            ...   | inj₁ d | jeq2 =
                    data-coh-r d d≢
                  ■ sym ( cong leafσ' (cong 𝐒.rwk ieq ■ P1r B₁ B₂ B d)
                        ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (drwk B₁ b₁ B₂ d ↑ˡ sum B) m)
                        ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                               (Fin.splitAt-↑ˡ (sum C₁') (drwk B₁ b₁ B₂ d) (sum B)) )
              where ieq : i ≡ (d ↑ˡ sum B) ↑ˡ m
                    ieq = sym jeq ■ cong (_↑ˡ m) (sym jeq2)
                    d≢ : d ≢ castpos
                    d≢ d≡ = i≢ (ieq ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡)
            -- toℕ of θ4 reduces to that of the underlying assocSwapᵣ 1 sT (substs preserve toℕ).
            θ4-toℕ-via : (x : 𝔽 (suc (sC₁ + n))) →
                         Fin.toℕ (θ4 x) ≡ Fin.toℕ (assocSwapᵣ 1 sT {r + n} (subst 𝔽 M1 x))
            θ4-toℕ-via x =
                cong Fin.toℕ (subst-cod-app (cong (Nat._+ n) e'') θ4inner x)
              ■ toℕ-subst𝔽 (cong (Nat._+ n) e'') (θ4inner x)
              ■ cong Fin.toℕ (subst-cod-app M3 θ4i2 x)
              ■ toℕ-subst𝔽 M3 (θ4i2 x)
              ■ cong Fin.toℕ (subst-cod-app M2 θ4i1 x)
              ■ toℕ-subst𝔽 M2 (θ4i1 x)
              ■ cong Fin.toℕ (subst-→ᵣ-app M1 (assocSwapᵣ 1 sT {r + n}) x)
              where
                θ4i1 = subst (λ z → z →ᵣ (sT + (1 + (r + n)))) (sym M1) (assocSwapᵣ 1 sT {r + n})
                θ4i2 = subst (λ z → suc (sC₁ + n) →ᵣ z) M2 θ4i1
                θ4inner = subst (λ z → suc (sC₁ + n) →ᵣ z) M3 θ4i2
            -- The full key renaming identity (all regions): the LHS 6-fold composite equals
            -- the structural insertion ∘ rebasing.  Proven by toℕ on the four blocks.
            target : (sB + (sC₁ + (2 + n))) →ᵣ (2 + (sB + (sC₁' + n)))
            target = rinsB ↑* sB ·ₖ (ρ₁' ·ₖ assocSwapᵣ sB 2)
            FULL : (sB + (sC₁ + (2 + n))) →ᵣ (2 + (sB + (sC₁' + n)))
            FULL = ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))
            aS_sB2 : (sB + (2 + (sC₁' + n))) →ᵣ (2 + (sB + (sC₁' + n)))
            aS_sB2 = assocSwapᵣ sB 2 {sC₁' + n}
            -- target on a position landing (after rins) at v < sC₁' in the sC₁'-block.
            tgt-sC1≤ : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) (v : ℕ) →
                       Fin.toℕ (rinsB (Fin.reduce≥ i sB≤)) ≡ v → v Nat.< sC₁' →
                       Fin.toℕ (target i) ≡ sB + (2 + v)
            tgt-sC1≤ i sB≤ v rv v<sC₁' =
                toℕ-assoc-ge sB 2 (ρ₁' (riB i)) (subst (sB + 2 Nat.≤_) (sym ρ₁ℕ) (Nat.+-monoʳ-≤ sB (Nat.m≤m+n 2 v)))
              ■ ρ₁ℕ
              where
                riB = rinsB ↑* sB
                riBℕ : Fin.toℕ (riB i) ≡ sB + v
                riBℕ = ↑*-hi rinsB sB i sB≤ ■ cong (sB +_) rv
                sB≤riB : sB Nat.≤ Fin.toℕ (riB i)
                sB≤riB = subst (sB Nat.≤_) (sym riBℕ) (Nat.m≤m+n sB v)
                red2ℕ : Fin.toℕ (Fin.reduce≥ (riB i) sB≤riB) ≡ v
                red2ℕ = toℕ-reduce≥ (riB i) sB≤riB ■ cong (Nat._∸ sB) riBℕ ■ Nat.m+n∸m≡n sB v
                ρ₁ℕ : Fin.toℕ (ρ₁' (riB i)) ≡ sB + (2 + v)
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁' 2) sB (riB i) sB≤riB
                    ■ cong (sB +_) ( toℕ-assoc-lt sC₁' 2 (Fin.reduce≥ (riB i) sB≤riB)
                                       (subst (Nat._< sC₁') (sym red2ℕ) v<sC₁')
                                   ■ cong (2 +_) red2ℕ )
            rinsℕ-lo : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                       Fin.toℕ i Nat.∸ sB Nat.< sT →
                       Fin.toℕ (rinsB (Fin.reduce≥ i sB≤)) ≡ Fin.toℕ i Nat.∸ sB
            rinsℕ-lo i sB≤ d<sT =
              rins-lo B₁ b₁ B₂ (Fin.reduce≥ i sB≤)
                (subst (Nat._< sT) (sym (toℕ-reduce≥ i sB≤)) d<sT) ■ toℕ-reduce≥ i sB≤
            rinsℕ-hi : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                       sT Nat.≤ Fin.toℕ i Nat.∸ sB →
                       Fin.toℕ (rinsB (Fin.reduce≥ i sB≤)) ≡ suc (Fin.toℕ i Nat.∸ sB)
            rinsℕ-hi i sB≤ d≥sT =
              rins-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤)
                (subst (sT Nat.≤_) (sym (toℕ-reduce≥ i sB≤)) d≥sT) ■ cong suc (toℕ-reduce≥ i sB≤)
            v<sC₁'-lo : (i : 𝔽 (sB + (sC₁ + (2 + n)))) → ¬ (Fin.toℕ i Nat.< sB) →
                        Fin.toℕ i Nat.∸ sB Nat.< sT → Fin.toℕ i Nat.∸ sB Nat.< sC₁'
            v<sC₁'-lo i _ d<sT = Nat.<-≤-trans (Nat.<-≤-trans d<sT (sT≤syncs B₁))
                                   (subst (sC₁ Nat.≤_) (sym (syncs-rwk B₁)) (Nat.n≤1+n sC₁))
            v<sC₁'-hi : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                        Fin.toℕ i Nat.< sB + sC₁ → suc (Fin.toℕ i Nat.∸ sB) Nat.< sC₁'
            v<sC₁'-hi i sB≤ p<sBsC₁ =
              subst (suc (Fin.toℕ i Nat.∸ sB) Nat.<_) (sym (syncs-rwk B₁))
                (Nat.s≤s (Nat.+-cancelˡ-< sB (Fin.toℕ i Nat.∸ sB) sC₁
                  (subst (Nat._< sB + sC₁) (sym (Nat.m+[n∸m]≡n sB≤)) p<sBsC₁)))
            bridge-lo : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                        sB + (2 + (Fin.toℕ i Nat.∸ sB)) ≡ 2 + Fin.toℕ i
            bridge-lo i sB≤ =
                arith ■ cong (2 +_) (Nat.m+[n∸m]≡n sB≤)
              where open +-*-Solver
                    arith : sB + (2 + (Fin.toℕ i Nat.∸ sB)) ≡ 2 + (sB + (Fin.toℕ i Nat.∸ sB))
                    arith = solve 2 (λ a b → a :+ (con 2 :+ b) := con 2 :+ (a :+ b)) refl sB (Fin.toℕ i Nat.∸ sB)
            bridge-hi : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                        sB + (2 + suc (Fin.toℕ i Nat.∸ sB)) ≡ 3 + Fin.toℕ i
            bridge-hi i sB≤ =
                arith ■ cong (3 +_) (Nat.m+[n∸m]≡n sB≤)
              where open +-*-Solver
                    arith : sB + (2 + suc (Fin.toℕ i Nat.∸ sB)) ≡ 3 + (sB + (Fin.toℕ i Nat.∸ sB))
                    arith = solve 2 (λ a b → a :+ (con 2 :+ (con 1 :+ b)) := con 3 :+ (a :+ b)) refl sB (Fin.toℕ i Nat.∸ sB)
            -- common to tgt-2 / tgt-n: toℕ of riB i for a position ≥ sB+sC₁ (rins-hi fires).
            riB-hiℕ : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                      sT Nat.≤ Fin.toℕ i Nat.∸ sB →
                      Fin.toℕ ((rinsB ↑* sB) i) ≡ sB + suc (Fin.toℕ i Nat.∸ sB)
            riB-hiℕ i sB≤ sT≤ = ↑*-hi rinsB sB i sB≤ ■ cong (sB +_) (rinsℕ-hi i sB≤ sT≤)
            -- shared: sC₁ ≤ (toℕ i ∸ sB), hence sT ≤ (toℕ i ∸ sB).
            sC₁≤dd : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                    sB + sC₁ Nat.≤ Fin.toℕ i → sC₁ Nat.≤ Fin.toℕ i Nat.∸ sB
            sC₁≤dd i sB≤ sBsC₁≤ = Nat.+-cancelˡ-≤ sB sC₁ (Fin.toℕ i Nat.∸ sB)
                                   (subst (sB + sC₁ Nat.≤_) (sym (Nat.m+[n∸m]≡n sB≤)) sBsC₁≤)
            tgt-2 : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i)
                    (sBsC₁≤ : sB + sC₁ Nat.≤ Fin.toℕ i) → Fin.toℕ i Nat.< sB + sC₁ + 2 →
                    Fin.toℕ (target i) ≡ Fin.toℕ i Nat.∸ (sB + sC₁)
            tgt-2 i sB≤ sBsC₁≤ p<2 =
                toℕ-assoc-mid sB 2 (ρ₁' (riB i))
                  (subst (sB Nat.≤_) (sym ρ₁ℕ) (Nat.m≤m+n sB _))
                  (subst (Nat._< sB + 2) (sym ρ₁ℕ) (Nat.+-monoʳ-< sB v∸<2))
              ■ cong (Nat._∸ sB) ρ₁ℕ ■ Nat.m+n∸m≡n sB _ ■ ∸∸
              where
                riB = rinsB ↑* sB
                v = suc (Fin.toℕ i Nat.∸ sB)
                sT≤ : sT Nat.≤ Fin.toℕ i Nat.∸ sB
                sT≤ = Nat.≤-trans (sT≤syncs B₁) (sC₁≤dd i sB≤ sBsC₁≤)
                sC₁'≤v : sC₁' Nat.≤ v
                sC₁'≤v = subst (Nat._≤ v) (sym (syncs-rwk B₁)) (Nat.s≤s (sC₁≤dd i sB≤ sBsC₁≤))
                v<sC₁'2 : v Nat.< sC₁' + 2
                v<sC₁'2 = subst (v Nat.<_) (sym (cong (Nat._+ 2) (syncs-rwk B₁)))
                            (Nat.s≤s (Nat.+-cancelˡ-< sB (Fin.toℕ i Nat.∸ sB) (sC₁ + 2)
                              (subst (Nat._< sB + (sC₁ + 2)) (sym (Nat.m+[n∸m]≡n sB≤))
                                (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc sB sC₁ 2) p<2))))
                v∸<2 : v Nat.∸ sC₁' Nat.< 2
                v∸<2 = Nat.+-cancelˡ-< sC₁' (v Nat.∸ sC₁') 2
                         (subst (Nat._< sC₁' + 2) (sym (Nat.m+[n∸m]≡n sC₁'≤v)) v<sC₁'2)
                ∸∸ : v Nat.∸ sC₁' ≡ Fin.toℕ i Nat.∸ (sB + sC₁)
                ∸∸ = cong (v Nat.∸_) (syncs-rwk B₁) ■ Nat.∸-+-assoc (Fin.toℕ i) sB sC₁
                riBℕ : Fin.toℕ (riB i) ≡ sB + v
                riBℕ = riB-hiℕ i sB≤ sT≤
                sB≤riB : sB Nat.≤ Fin.toℕ (riB i)
                sB≤riB = subst (sB Nat.≤_) (sym riBℕ) (Nat.m≤m+n sB v)
                red2ℕ : Fin.toℕ (Fin.reduce≥ (riB i) sB≤riB) ≡ v
                red2ℕ = toℕ-reduce≥ (riB i) sB≤riB ■ cong (Nat._∸ sB) riBℕ ■ Nat.m+n∸m≡n sB v
                ρ₁ℕ : Fin.toℕ (ρ₁' (riB i)) ≡ sB + (v Nat.∸ sC₁')
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁' 2) sB (riB i) sB≤riB
                    ■ cong (sB +_) ( toℕ-assoc-mid sC₁' 2 (Fin.reduce≥ (riB i) sB≤riB)
                                       (subst (sC₁' Nat.≤_) (sym red2ℕ) sC₁'≤v)
                                       (subst (Nat._< sC₁' + 2) (sym red2ℕ) v<sC₁'2)
                                   ■ cong (Nat._∸ sC₁') red2ℕ )
            tgt-n : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i)
                    (sBsC₁≤ : sB + sC₁ Nat.≤ Fin.toℕ i) → sB + sC₁ + 2 Nat.≤ Fin.toℕ i →
                    Fin.toℕ (target i) ≡ 1 + Fin.toℕ i
            tgt-n i sB≤ sBsC₁≤ p≥2 =
                toℕ-assoc-ge sB 2 (ρ₁' (riB i))
                  (subst (sB + 2 Nat.≤_) (sym ρ₁ℕ) (Nat.+-monoʳ-≤ sB 2≤v)) ■ ρ₁ℕ ■ comm
              where
                riB = rinsB ↑* sB
                v = suc (Fin.toℕ i Nat.∸ sB)
                dd = Fin.toℕ i Nat.∸ sB
                sC₁2≤d : sC₁ + 2 Nat.≤ dd
                sC₁2≤d = Nat.+-cancelˡ-≤ sB (sC₁ + 2) dd
                           (subst (sB + (sC₁ + 2) Nat.≤_) (sym (Nat.m+[n∸m]≡n sB≤))
                             (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc sB sC₁ 2) p≥2))
                sT≤ : sT Nat.≤ dd
                sT≤ = Nat.≤-trans (sT≤syncs B₁) (Nat.≤-trans (Nat.m≤m+n sC₁ 2) sC₁2≤d)
                2≤v : 2 Nat.≤ v
                2≤v = Nat.s≤s (Nat.≤-trans {1} {2} {dd} (Nat.s≤s Nat.z≤n)
                                (Nat.≤-trans (Nat.m≤n+m 2 sC₁) sC₁2≤d))
                sC₁'2≤v : sC₁' + 2 Nat.≤ v
                sC₁'2≤v = subst (Nat._≤ v) (sym (cong (Nat._+ 2) (syncs-rwk B₁))) (Nat.s≤s sC₁2≤d)
                riBℕ : Fin.toℕ (riB i) ≡ sB + v
                riBℕ = riB-hiℕ i sB≤ sT≤
                sB≤riB : sB Nat.≤ Fin.toℕ (riB i)
                sB≤riB = subst (sB Nat.≤_) (sym riBℕ) (Nat.m≤m+n sB v)
                red2ℕ : Fin.toℕ (Fin.reduce≥ (riB i) sB≤riB) ≡ v
                red2ℕ = toℕ-reduce≥ (riB i) sB≤riB ■ cong (Nat._∸ sB) riBℕ ■ Nat.m+n∸m≡n sB v
                ρ₁ℕ : Fin.toℕ (ρ₁' (riB i)) ≡ sB + v
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁' 2) sB (riB i) sB≤riB
                    ■ cong (sB +_) ( toℕ-assoc-ge sC₁' 2 (Fin.reduce≥ (riB i) sB≤riB)
                                       (subst (sC₁' + 2 Nat.≤_) (sym red2ℕ) sC₁'2≤v)
                                   ■ red2ℕ )
                comm : sB + v ≡ 1 + Fin.toℕ i
                comm = Nat.+-suc sB (Fin.toℕ i Nat.∸ sB) ■ cong suc (Nat.m+[n∸m]≡n sB≤)
            tgt-sB : (i : 𝔽 (sB + (sC₁ + (2 + n)))) → Fin.toℕ i Nat.< sB →
                     Fin.toℕ (target i) ≡ 2 + Fin.toℕ i
            tgt-sB i p<sB =
                  toℕ-assoc-lt sB 2 (ρ₁' (riB i)) (subst (Nat._< sB) (sym step1) p<sB)
                ■ cong (2 +_) step1
              where
                riB = rinsB ↑* sB
                step0 : Fin.toℕ (riB i) ≡ Fin.toℕ i
                step0 = ↑*-lo rinsB sB i p<sB
                step1 : Fin.toℕ (ρ₁' (riB i)) ≡ Fin.toℕ i
                step1 = ↑*-lo (assocSwapᵣ sC₁' 2) sB (riB i) (subst (Nat._< sB) (sym step0) p<sB) ■ step0
            -- toℕ of ρ₂(ρ₁ i): the two block-swaps bring the 2 ν-endpoints to the front,
            -- shift the sB-block up by 2, leave the sC₁/n blocks fixed.
            pref-sB : (i : 𝔽 (sB + (sC₁ + (2 + n)))) → Fin.toℕ i Nat.< sB →
                      Fin.toℕ (ρ₂ (ρ₁ i)) ≡ 2 + Fin.toℕ i
            pref-sB i p<sB =
                toℕ-assoc-lt sB 2 (ρ₁ i) (subst (Nat._< sB) (sym ρ₁ℕ) p<sB) ■ cong (2 +_) ρ₁ℕ
              where ρ₁ℕ : Fin.toℕ (ρ₁ i) ≡ Fin.toℕ i
                    ρ₁ℕ = ↑*-lo (assocSwapᵣ sC₁ 2) sB i p<sB
            pref-ge : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                      Fin.toℕ i Nat.< sB + sC₁ →
                      Fin.toℕ (ρ₂ (ρ₁ i)) ≡ 2 + Fin.toℕ i
            pref-ge i sB≤ p<sBsC₁ =
                toℕ-assoc-ge sB 2 (ρ₁ i)
                  (subst (sB + 2 Nat.≤_) (sym ρ₁ℕ)
                    (subst (sB + 2 Nat.≤_) (Nat.+-comm (Fin.toℕ i) 2) (Nat.+-monoˡ-≤ 2 sB≤))) ■ ρ₁ℕ
              where
                dd = Fin.toℕ i Nat.∸ sB
                redℕ : Fin.toℕ (Fin.reduce≥ i sB≤) ≡ dd
                redℕ = toℕ-reduce≥ i sB≤
                dd<sC₁ : dd Nat.< sC₁
                dd<sC₁ = Nat.+-cancelˡ-< sB dd sC₁ (subst (Nat._< sB + sC₁) (sym (Nat.m+[n∸m]≡n sB≤)) p<sBsC₁)
                ρ₁ℕ : Fin.toℕ (ρ₁ i) ≡ 2 + Fin.toℕ i
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁ 2) sB i sB≤
                    ■ cong (sB +_) ( toℕ-assoc-lt sC₁ 2 (Fin.reduce≥ i sB≤) (subst (Nat._< sC₁) (sym redℕ) dd<sC₁)
                                   ■ cong (2 +_) redℕ )
                    ■ arith ■ cong (2 +_) (Nat.m+[n∸m]≡n sB≤)
                  where open +-*-Solver
                        arith : sB + (2 + dd) ≡ 2 + (sB + dd)
                        arith = solve 2 (λ a b → a :+ (con 2 :+ b) := con 2 :+ (a :+ b)) refl sB dd
            full-sB : (i : 𝔽 (sB + (sC₁ + (2 + n)))) → Fin.toℕ i Nat.< sB →
                      Fin.toℕ (FULL i) ≡ 2 + Fin.toℕ i
            full-sB i p<sB = sB-trail (Fin.toℕ i) (ρ₂ (ρ₁ i)) (pref-sB i p<sB) p<sB
            full-sC1-lo : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                          Fin.toℕ i Nat.∸ sB Nat.< sT →
                          Fin.toℕ (FULL i) ≡ sB + (2 + (Fin.toℕ i Nat.∸ sB))
            -- TRAIL on a position z (≥ 2+sB): weaken/aS12/aS1sB restore it shifted, ρB then
            -- applies θ4 (≈ assocSwapᵣ 1 sT) to the (toℕ z ∸ (1+sB)) offset.  The θ4 toℕ is
            -- supplied by the caller via θ4-toℕ-via.  Returns toℕ(TRAIL z) = 2 + (sB + θv).
            -- TRAIL on z with toℕ z = 2 + (sB + g'): weaken/aS12/aS1sB carry it to 3+(sB+g'),
            -- ρB applies θ4 to the offset 1+g'.  Returns 2 + (sB + toℕ(assocSwapᵣ 1 sT (1+g'))).
            trail-hi : (z : 𝔽 (2 + (sB + (sC₁ + n)))) (g' : ℕ) → Fin.toℕ z ≡ 2 + (sB + g') →
                       (e₀ : 𝔽 (suc (sC₁ + n))) → Fin.toℕ e₀ ≡ suc g' →
                       Fin.toℕ ((weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))) z)
                       ≡ 2 + (sB + Fin.toℕ (assocSwapᵣ 1 sT {r + n} (subst 𝔽 M1 e₀)))
            trail-hi z g' zw e₀ e₀ℕ =
                ↑*-hi (θ4 ↑* sB) 2 (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB
              ■ cong (2 +_)
                  ( ↑*-hi θ4 sB (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB) sB≤red
                  ■ cong (sB +_) (θ4-toℕ-via _
                      ■ cong (λ z′ → Fin.toℕ (assocSwapᵣ 1 sT {r + n} (subst 𝔽 M1 z′)))
                             (Fin.toℕ-injective (red≡g' ■ sym e₀ℕ))) )
              where
                wkℕ : Fin.toℕ (weakenᵣ z) ≡ 3 + (sB + g')
                wkℕ = cong suc zw
                aS12ℕ : Fin.toℕ (aS12 (weakenᵣ z)) ≡ 3 + (sB + g')
                aS12ℕ = toℕ-assoc-ge 1 2 (weakenᵣ z)
                          (subst (3 Nat.≤_) (sym wkℕ) (Nat.s≤s (Nat.s≤s (Nat.s≤s Nat.z≤n)))) ■ wkℕ
                2≤aS12 : 2 Nat.≤ Fin.toℕ (aS12 (weakenᵣ z))
                2≤aS12 = subst (2 Nat.≤_) (sym aS12ℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                red1ℕ : Fin.toℕ (Fin.reduce≥ (aS12 (weakenᵣ z)) 2≤aS12) ≡ 1 + (sB + g')
                red1ℕ = toℕ-reduce≥ (aS12 (weakenᵣ z)) 2≤aS12 ■ cong (Nat._∸ 2) aS12ℕ
                aS1sBℕ : Fin.toℕ (aS1sB (aS12 (weakenᵣ z))) ≡ 3 + (sB + g')
                aS1sBℕ = ↑*-hi (assocSwapᵣ 1 sB) 2 (aS12 (weakenᵣ z)) 2≤aS12
                       ■ cong (2 +_) ( toℕ-assoc-ge 1 sB (Fin.reduce≥ (aS12 (weakenᵣ z)) 2≤aS12)
                                         (subst (1 + sB Nat.≤_) (sym red1ℕ)
                                           (Nat.s≤s (Nat.m≤m+n sB g'))) ■ red1ℕ )
                2≤aS1sB : 2 Nat.≤ Fin.toℕ (aS1sB (aS12 (weakenᵣ z)))
                2≤aS1sB = subst (2 Nat.≤_) (sym aS1sBℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                red2ℕ : Fin.toℕ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB) ≡ 1 + (sB + g')
                red2ℕ = toℕ-reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB ■ cong (Nat._∸ 2) aS1sBℕ
                sB≤red : sB Nat.≤ Fin.toℕ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB)
                sB≤red = subst (sB Nat.≤_) (sym red2ℕ) (Nat.m≤n⇒m≤1+n (Nat.m≤m+n sB g'))
                red≡g' : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB) sB≤red) ≡ suc g'
                red≡g' = toℕ-reduce≥ (Fin.reduce≥ (aS1sB (aS12 (weakenᵣ z))) 2≤aS1sB) sB≤red
                       ■ cong (Nat._∸ sB) red2ℕ ■ helper
                  where helper : 1 + (sB + g') Nat.∸ sB ≡ suc g'
                        helper = cong (Nat._∸ sB) (Nat.+-comm 1 (sB + g') ■ Nat.+-assoc sB g' 1)
                               ■ Nat.m+n∸m≡n sB (g' + 1) ■ Nat.+-comm g' 1
            full-sC1-lo i sB≤ d<sT =
                trail-hi (ρ₂ (ρ₁ i)) dd zw e₀ e₀ℕ
              ■ cong (λ z → 2 + (sB + z))
                  ( toℕ-assoc-mid 1 sT (subst 𝔽 M1 e₀)
                      (subst (1 Nat.≤_) (sym sM1ℕ) (Nat.s≤s Nat.z≤n))
                      (subst (Nat._< 1 + sT) (sym sM1ℕ) (Nat.s≤s d<sT))
                  ■ cong (Nat._∸ 1) sM1ℕ )
              ■ comm
              where
                dd = Fin.toℕ i Nat.∸ sB
                dd<sC₁ : dd Nat.< sC₁
                dd<sC₁ = Nat.<-≤-trans d<sT (sT≤syncs B₁)
                zw : Fin.toℕ (ρ₂ (ρ₁ i)) ≡ 2 + (sB + dd)
                zw = pref-ge i sB≤ (subst (Nat._< sB + sC₁) (Nat.m+[n∸m]≡n sB≤) (Nat.+-monoʳ-< sB dd<sC₁))
                   ■ cong (2 +_) (sym (Nat.m+[n∸m]≡n sB≤))
                e₀< : suc dd Nat.< suc (sC₁ + n)
                e₀< = Nat.s≤s (Nat.<-≤-trans dd<sC₁ (Nat.m≤m+n sC₁ n))
                e₀ : 𝔽 (suc (sC₁ + n))
                e₀ = Fin.fromℕ< e₀<
                e₀ℕ : Fin.toℕ e₀ ≡ suc dd
                e₀ℕ = Fin.toℕ-fromℕ< e₀<
                sM1ℕ : Fin.toℕ (subst 𝔽 M1 e₀) ≡ suc dd
                sM1ℕ = toℕ-subst𝔽 M1 e₀ ■ e₀ℕ
                comm : 2 + (sB + dd) ≡ sB + (2 + dd)
                comm = bsolve
                  where open +-*-Solver
                        bsolve : 2 + (sB + dd) ≡ sB + (2 + dd)
                        bsolve = solve 2 (λ a b → con 2 :+ (a :+ b) := a :+ (con 2 :+ b)) refl sB dd
            full-sC1-hi : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                          Fin.toℕ i Nat.< sB + sC₁ → sT Nat.≤ Fin.toℕ i Nat.∸ sB →
                          Fin.toℕ (FULL i) ≡ sB + (2 + suc (Fin.toℕ i Nat.∸ sB))
            full-sC1-hi i sB≤ p<sBsC₁ d≥sT =
                trail-hi (ρ₂ (ρ₁ i)) dd zw e₀ e₀ℕ
              ■ cong (λ z → 2 + (sB + z))
                  ( toℕ-assoc-ge 1 sT (subst 𝔽 M1 e₀)
                      (subst (1 + sT Nat.≤_) (sym sM1ℕ) (Nat.s≤s d≥sT))
                  ■ sM1ℕ )
              ■ comm
              where
                dd = Fin.toℕ i Nat.∸ sB
                dd<sC₁ : dd Nat.< sC₁
                dd<sC₁ = Nat.+-cancelˡ-< sB dd sC₁ (subst (Nat._< sB + sC₁) (sym (Nat.m+[n∸m]≡n sB≤)) p<sBsC₁)
                zw : Fin.toℕ (ρ₂ (ρ₁ i)) ≡ 2 + (sB + dd)
                zw = pref-ge i sB≤ p<sBsC₁ ■ cong (2 +_) (sym (Nat.m+[n∸m]≡n sB≤))
                e₀< : suc dd Nat.< suc (sC₁ + n)
                e₀< = Nat.s≤s (Nat.<-≤-trans dd<sC₁ (Nat.m≤m+n sC₁ n))
                e₀ : 𝔽 (suc (sC₁ + n))
                e₀ = Fin.fromℕ< e₀<
                e₀ℕ : Fin.toℕ e₀ ≡ suc dd
                e₀ℕ = Fin.toℕ-fromℕ< e₀<
                sM1ℕ : Fin.toℕ (subst 𝔽 M1 e₀) ≡ suc dd
                sM1ℕ = toℕ-subst𝔽 M1 e₀ ■ e₀ℕ
                comm : 2 + (sB + suc dd) ≡ sB + (2 + suc dd)
                comm = bsolve
                  where open +-*-Solver
                        bsolve : 2 + (sB + suc dd) ≡ sB + (2 + suc dd)
                        bsolve = solve 2 (λ a b → con 2 :+ (a :+ b) := a :+ (con 2 :+ b)) refl sB (suc dd)
            -- TRAIL on a ν-endpoint position (toℕ z < 2): identity.
            trail-lo : (z : 𝔽 (2 + (sB + (sC₁ + n)))) → Fin.toℕ z Nat.< 2 →
                       Fin.toℕ ((weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))) z) ≡ Fin.toℕ z
            trail-lo z z<2 =
                ↑*-lo (θ4 ↑* sB) 2 (aS1sB (aS12 (weakenᵣ z))) (subst (Nat._< 2) (sym aS1sBℕ) z<2)
              ■ aS1sBℕ
              where
                wkℕ : Fin.toℕ (weakenᵣ z) ≡ suc (Fin.toℕ z)
                wkℕ = refl
                aS12ℕ : Fin.toℕ (aS12 (weakenᵣ z)) ≡ Fin.toℕ z
                aS12ℕ = toℕ-assoc-mid 1 2 (weakenᵣ z)
                          (subst (1 Nat.≤_) (sym wkℕ) (Nat.s≤s Nat.z≤n))
                          (subst (Nat._< 1 + 2) (sym wkℕ) (Nat.s≤s z<2))
                      ■ cong (Nat._∸ 1) wkℕ
                aS1sBℕ : Fin.toℕ (aS1sB (aS12 (weakenᵣ z))) ≡ Fin.toℕ z
                aS1sBℕ = ↑*-lo (assocSwapᵣ 1 sB) 2 (aS12 (weakenᵣ z)) (subst (Nat._< 2) (sym aS12ℕ) z<2)
                       ■ aS12ℕ
            full-2 : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i)
                     (sBsC₁≤ : sB + sC₁ Nat.≤ Fin.toℕ i) → Fin.toℕ i Nat.< sB + sC₁ + 2 →
                     Fin.toℕ (FULL i) ≡ Fin.toℕ i Nat.∸ (sB + sC₁)
            pref-2 : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i)
                     (sBsC₁≤ : sB + sC₁ Nat.≤ Fin.toℕ i) → Fin.toℕ i Nat.< sB + sC₁ + 2 →
                     Fin.toℕ (ρ₂ (ρ₁ i)) ≡ Fin.toℕ i Nat.∸ (sB + sC₁)
            pref-2 i sB≤ sBsC₁≤ p<2 =
                toℕ-assoc-mid sB 2 (ρ₁ i)
                  (subst (sB Nat.≤_) (sym ρ₁ℕ) (Nat.m≤m+n sB ee))
                  (subst (Nat._< sB + 2) (sym ρ₁ℕ) (Nat.+-monoʳ-< sB e<2))
              ■ cong (Nat._∸ sB) ρ₁ℕ ■ Nat.m+n∸m≡n sB ee
              where
                ee = Fin.toℕ i Nat.∸ (sB + sC₁)
                e<2 : ee Nat.< 2
                e<2 = Nat.+-cancelˡ-< (sB + sC₁) ee 2 (subst (Nat._< sB + sC₁ + 2) (sym (Nat.m+[n∸m]≡n sBsC₁≤)) p<2)
                sC₁≤loc : sC₁ Nat.≤ Fin.toℕ i Nat.∸ sB
                sC₁≤loc = Nat.+-cancelˡ-≤ sB sC₁ (Fin.toℕ i Nat.∸ sB)
                          (subst (sB + sC₁ Nat.≤_) (sym (Nat.m+[n∸m]≡n sB≤)) sBsC₁≤)
                redℕ : Fin.toℕ (Fin.reduce≥ i sB≤) ≡ Fin.toℕ i Nat.∸ sB
                redℕ = toℕ-reduce≥ i sB≤
                ρ₁ℕ : Fin.toℕ (ρ₁ i) ≡ sB + ee
                d<sC₁2 : Fin.toℕ i Nat.∸ sB Nat.< sC₁ + 2
                d<sC₁2 = Nat.+-cancelˡ-< sB (Fin.toℕ i Nat.∸ sB) (sC₁ + 2)
                          (subst (Nat._< sB + (sC₁ + 2)) (sym (Nat.m+[n∸m]≡n sB≤))
                            (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc sB sC₁ 2) p<2))
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁ 2) sB i sB≤
                    ■ cong (sB +_) ( toℕ-assoc-mid sC₁ 2 (Fin.reduce≥ i sB≤)
                                       (subst (sC₁ Nat.≤_) (sym redℕ) sC₁≤loc)
                                       (subst (Nat._< sC₁ + 2) (sym redℕ) d<sC₁2)
                                   ■ cong (Nat._∸ sC₁) redℕ
                                   ■ Nat.∸-+-assoc (Fin.toℕ i) sB sC₁ )
            full-2 i sB≤ sBsC₁≤ p<2 =
                trail-lo (ρ₂ (ρ₁ i)) (subst (Nat._< 2) (sym (pref-2 i sB≤ sBsC₁≤ p<2)) e<2)
              ■ pref-2 i sB≤ sBsC₁≤ p<2
              where
                e<2 : Fin.toℕ i Nat.∸ (sB + sC₁) Nat.< 2
                e<2 = Nat.+-cancelˡ-< (sB + sC₁) (Fin.toℕ i Nat.∸ (sB + sC₁)) 2
                        (subst (Nat._< sB + sC₁ + 2) (sym (Nat.m+[n∸m]≡n sBsC₁≤)) p<2)
            full-n : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i)
                     (sBsC₁≤ : sB + sC₁ Nat.≤ Fin.toℕ i) → sB + sC₁ + 2 Nat.≤ Fin.toℕ i →
                     Fin.toℕ (FULL i) ≡ 1 + Fin.toℕ i
            -- n-region: ρ₁/ρ₂ leave the position fixed (above both swap blocks).
            pref-n : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                     sB + sC₁ + 2 Nat.≤ Fin.toℕ i → Fin.toℕ (ρ₂ (ρ₁ i)) ≡ Fin.toℕ i
            pref-n i sB≤ p≥2 =
                toℕ-assoc-ge sB 2 (ρ₁ i) (subst (sB + 2 Nat.≤_) (sym ρ₁ℕ) sB2≤) ■ ρ₁ℕ
              where
                sC₁2≤d : sC₁ + 2 Nat.≤ Fin.toℕ i Nat.∸ sB
                sC₁2≤d = Nat.+-cancelˡ-≤ sB (sC₁ + 2) (Fin.toℕ i Nat.∸ sB)
                           (subst (sB + (sC₁ + 2) Nat.≤_) (sym (Nat.m+[n∸m]≡n sB≤))
                             (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc sB sC₁ 2) p≥2))
                redℕ : Fin.toℕ (Fin.reduce≥ i sB≤) ≡ Fin.toℕ i Nat.∸ sB
                redℕ = toℕ-reduce≥ i sB≤
                ρ₁ℕ : Fin.toℕ (ρ₁ i) ≡ Fin.toℕ i
                ρ₁ℕ = ↑*-hi (assocSwapᵣ sC₁ 2) sB i sB≤
                    ■ cong (sB +_) ( toℕ-assoc-ge sC₁ 2 (Fin.reduce≥ i sB≤)
                                       (subst (sC₁ + 2 Nat.≤_) (sym redℕ) sC₁2≤d) ■ redℕ )
                    ■ Nat.m+[n∸m]≡n sB≤
                sB2≤ : sB + 2 Nat.≤ Fin.toℕ i
                sB2≤ = Nat.≤-trans (Nat.+-monoʳ-≤ sB (Nat.m≤n+m 2 sC₁))
                         (subst (sB + (sC₁ + 2) Nat.≤_) (Nat.m+[n∸m]≡n sB≤)
                           (Nat.+-monoʳ-≤ sB sC₁2≤d))
            full-n i sB≤ sBsC₁≤ p≥2 =
                trail-hi (ρ₂ (ρ₁ i)) g' zw e₀ e₀ℕ
              ■ cong (λ z → 2 + (sB + z))
                  ( toℕ-assoc-ge 1 sT (subst 𝔽 M1 e₀) (subst (1 + sT Nat.≤_) (sym sM1ℕ) 1sT≤) ■ sM1ℕ )
              ■ final
              where
                f∸ = Fin.toℕ i Nat.∸ (sB + sC₁ + 2)
                g' = sC₁ + f∸
                sBsC₁2≤ : sB + sC₁ + 2 Nat.≤ Fin.toℕ i
                sBsC₁2≤ = p≥2
                pn : Fin.toℕ (ρ₂ (ρ₁ i)) ≡ Fin.toℕ i
                pn = pref-n i sB≤ p≥2
                iℕ : Fin.toℕ i ≡ 2 + (sB + g')
                iℕ = sym (Nat.m+[n∸m]≡n sBsC₁2≤)
                   ■ asolve
                  where open +-*-Solver
                        asolve : sB + sC₁ + 2 + f∸ ≡ 2 + (sB + (sC₁ + f∸))
                        asolve = solve 3 (λ a b c → a :+ b :+ con 2 :+ c := con 2 :+ (a :+ (b :+ c))) refl sB sC₁ f∸
                zw : Fin.toℕ (ρ₂ (ρ₁ i)) ≡ 2 + (sB + g')
                zw = pn ■ iℕ
                f∸<n : f∸ Nat.< n
                f∸<n = Nat.+-cancelˡ-< (sB + sC₁ + 2) f∸ n
                         (subst (Nat._< sB + sC₁ + 2 + n) (sym (Nat.m+[n∸m]≡n sBsC₁2≤))
                           (subst (Fin.toℕ i Nat.<_) reassoc (Fin.toℕ<n i)))
                  where reassoc : sB + (sC₁ + (2 + n)) ≡ sB + sC₁ + 2 + n
                        reassoc = bsolve
                          where open +-*-Solver
                                bsolve : sB + (sC₁ + (2 + n)) ≡ sB + sC₁ + 2 + n
                                bsolve = solve 3 (λ a b c → a :+ (b :+ (con 2 :+ c)) := a :+ b :+ con 2 :+ c) refl sB sC₁ n
                e₀< : suc g' Nat.< suc (sC₁ + n)
                e₀< = Nat.s≤s (Nat.+-monoʳ-< sC₁ f∸<n)
                e₀ : 𝔽 (suc (sC₁ + n))
                e₀ = Fin.fromℕ< e₀<
                e₀ℕ : Fin.toℕ e₀ ≡ suc g'
                e₀ℕ = Fin.toℕ-fromℕ< e₀<
                sM1ℕ : Fin.toℕ (subst 𝔽 M1 e₀) ≡ suc g'
                sM1ℕ = toℕ-subst𝔽 M1 e₀ ■ e₀ℕ
                1sT≤ : 1 + sT Nat.≤ suc g'
                1sT≤ = Nat.s≤s (Nat.≤-trans (sT≤syncs B₁) (Nat.m≤m+n sC₁ f∸))
                final : 2 + (sB + suc g') ≡ 1 + Fin.toℕ i
                final = cong (λ z → 2 + (sB + suc z)) refl
                      ■ fsolve ■ cong (1 +_) (sym iℕ)
                  where open +-*-Solver
                        fsolve : 2 + (sB + suc g') ≡ 1 + (2 + (sB + g'))
                        fsolve = solve 2 (λ a b → con 2 :+ (a :+ (con 1 :+ b)) := con 1 :+ (con 2 :+ (a :+ b))) refl sB g'
            keyFull-sC1 : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                          Fin.toℕ i Nat.< sB + sC₁ → FULL i ≡ target i
            keyFull-sC1 i sB≤ p<sBsC₁ with (Fin.toℕ i Nat.∸ sB) Nat.<? sT
            ... | yes d<sT =
                  Fin.toℕ-injective
                    ( full-sC1-lo i sB≤ d<sT
                    ■ sym (tgt-sC1≤ i sB≤ (Fin.toℕ i Nat.∸ sB)
                             (rinsℕ-lo i sB≤ d<sT) (v<sC₁'-lo i (λ q → Nat.<-irrefl refl (Nat.<-≤-trans q sB≤)) d<sT)) )
            ... | no  d≥sT =
                  Fin.toℕ-injective
                    ( full-sC1-hi i sB≤ p<sBsC₁ (Nat.≮⇒≥ d≥sT)
                    ■ sym (tgt-sC1≤ i sB≤ (suc (Fin.toℕ i Nat.∸ sB))
                             (rinsℕ-hi i sB≤ (Nat.≮⇒≥ d≥sT)) (v<sC₁'-hi i sB≤ p<sBsC₁)) )
            keyFull-2n : (i : 𝔽 (sB + (sC₁ + (2 + n)))) (sB≤ : sB Nat.≤ Fin.toℕ i) →
                         sB + sC₁ Nat.≤ Fin.toℕ i → FULL i ≡ target i
            keyFull-2n i sB≤ sBsC₁≤ with Fin.toℕ i Nat.<? sB + sC₁ + 2
            ... | yes p<2 =
                  Fin.toℕ-injective
                    ( full-2 i sB≤ sBsC₁≤ p<2 ■ sym (tgt-2 i sB≤ sBsC₁≤ p<2) )
            ... | no  p≥2 =
                  Fin.toℕ-injective
                    ( full-n i sB≤ sBsC₁≤ (Nat.≮⇒≥ p≥2) ■ sym (tgt-n i sB≤ sBsC₁≤ (Nat.≮⇒≥ p≥2)) )
            keyFull : (i : 𝔽 (sB + (sC₁ + (2 + n)))) → FULL i ≡ target i
            keyFull i with Fin.toℕ i Nat.<? sB
            ... | yes p<sB = Fin.toℕ-injective (full-sB i p<sB ■ sym (tgt-sB i p<sB))
            ... | no  p≥sB with Fin.toℕ i Nat.<? sB + sC₁
            ...               | yes p<sBsC₁ = keyFull-sC1 i (Nat.≮⇒≥ p≥sB) p<sBsC₁
            ...               | no  p≥sBsC₁ = keyFull-2n i (Nat.≮⇒≥ p≥sB) (Nat.≮⇒≥ p≥sBsC₁)
            threadEq : 𝐔.⟪ ((Fr ⋯ᶠ* weakenᵣ)
                            [ (((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⊗ (` suc Xch)) ⊗ (` 0F))
                            ⊗ (((` 0F) ⊗ (` suc Xch)) ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ)) ]*) ⟫
                       𝐔.⋯ₚ aS12 𝐔.⋯ₚ aS1sB 𝐔.⋯ₚ ρB
                       𝐔.≋ RpThread_R
            threadEq  = ≡→≋ (cong 𝐔.⟪_⟫ bodyEq)
              where
                ρ₁₂'R : (sB + (sC₁' + (2 + n))) →ᵣ (2 + (sB + (sC₁' + n)))
                ρ₁₂'R = ρ₁' ·ₖ aS_sB2
                σ'ᴿ : (sum C₁' + sum B + m) →ₛ (2 + (sB + (sC₁' + n)))
                σ'ᴿ = leafσ' ·ₖ ρ₁₂'R
                Vσ'ᴿ : VSub σ'ᴿ
                Vσ'ᴿ i = value-⋯ (Vleafσ' i) ρ₁₂'R (λ _ → V-`)
                Eᴿ : Frame* (sum C₁' + sum B + m)
                Eᴿ = E ⋯ᶠ* 𝐒.rwk
                pair : Tm (sum C₁' + sum B + m)
                pair = (` 𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 0F) ⊗ (` 𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 1F)
                WTRAIL : (2 + (sB + (sC₁ + n))) →ᵣ (2 + (sB + (sC₁' + n)))
                WTRAIL = weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))
                V1 : VSub (σ' ·ₖ WTRAIL)
                V1 i = value-⋯ (Vσ' i) WTRAIL (λ _ → V-`)
                sib = canonₛ-sib-r B₁ cc1 b₁ B₂
                h1 = proj₁ (hc-sib-agree-r B₁ cc1 b₁ B₂)
                h2 = proj₁ (proj₂ (hc-sib-agree-r B₁ cc1 b₁ B₂))
                h3 = proj₂ (proj₂ (hc-sib-agree-r B₁ cc1 b₁ B₂))
                cp0 cp1 : 𝔽 (sum C₁')
                cp0 = Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
                cp1 = Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 1F)
                leafσ'-inj : ∀ (cp : 𝔽 (sum C₁')) →
                             leafσ' ((cp ↑ˡ sum B) ↑ˡ m) ≡ canonₛ C₁' cc1 cp ⋯ weaken* ⦃ Kᵣ ⦄ sB
                leafσ'-inj cp =
                    cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (cp ↑ˡ sum B) m)
                  ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                         (Fin.splitAt-↑ˡ (sum C₁') cp (sum B))
                σ'ᴿinj0 : σ'ᴿ (𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 0F)
                          ≡ (((proj₁ sib ⊗ (` proj₁ (proj₂ sib))) ⊗ (` proj₁ (proj₂ (proj₂ (proj₂ sib))))) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ρ₁₂'R
                σ'ᴿinj0 = cong (_⋯ ρ₁₂'R) (leafσ'-inj cp0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ sib))))))
                σ'ᴿinj1 : σ'ᴿ (𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 1F)
                          ≡ ((((` proj₁ (proj₂ (proj₂ (proj₂ sib)))) ⊗ (` proj₁ (proj₂ sib))) ⊗ proj₁ (proj₂ (proj₂ sib))) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ρ₁₂'R
                σ'ᴿinj1 = cong (_⋯ ρ₁₂'R) (leafσ'-inj cp1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ sib))))))
                fusionT5 : (t : Tm (sB + (sC₁ + (2 + n)))) →
                           t ⋯ ρ₁₂ ⋯ weakenᵣ ⋯ aS12 ⋯ aS1sB ⋯ ρB ≡ t ⋯ FULL
                fusionT5 t =
                    fusion (t ⋯ ρ₁₂ ⋯ weakenᵣ ⋯ aS12) aS1sB ρB
                  ■ fusion (t ⋯ ρ₁₂ ⋯ weakenᵣ) aS12 (aS1sB ·ₖ ρB)
                  ■ fusion (t ⋯ ρ₁₂) weakenᵣ (aS12 ·ₖ (aS1sB ·ₖ ρB))
                  ■ fusion t ρ₁₂ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB)))
                compA : (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⋯ aS12 ⋯ aS1sB ⋯ ρB
                        ≡ proj₁ sib ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂'R
                compA =
                    fusionT5 (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                  ■ ⋯-cong (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB) keyFull
                  ■ sym (fusion (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB) (rinsB ↑* sB) ρ₁₂'R)
                  ■ cong (_⋯ ρ₁₂'R) (wkcom (proj₁ hc) ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) h1)
                compC : (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⋯ aS12 ⋯ aS1sB ⋯ ρB
                        ≡ proj₁ (proj₂ (proj₂ sib)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂'R
                compC =
                    fusionT5 (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                  ■ ⋯-cong (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB) keyFull
                  ■ sym (fusion (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB) (rinsB ↑* sB) ρ₁₂'R)
                  ■ cong (_⋯ ρ₁₂'R) (wkcom (proj₁ (proj₂ (proj₂ hc))) ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) h3)
                compX : ρB (aS1sB (aS12 (Fin.suc Xch))) ≡ ρ₁₂'R (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ sib)))
                compX =
                    keyFull (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ hc)))
                  ■ cong ρ₁₂'R (sym (↑*-wk rinsB sB (proj₁ (proj₂ hc))))
                  ■ cong (λ v → ρ₁₂'R (weaken* ⦃ Kᵣ ⦄ sB v)) h2
                freshℕ : Fin.toℕ (ρB (aS1sB (aS12 0F))) ≡ 2 + (sB + sT)
                freshℕ =
                    ↑*-hi (θ4 ↑* sB) 2 w twoLE
                  ■ cong (2 +_) (↑*-hi θ4 sB w' sB≤w' ■ cong (sB +_) θ4q)
                  where
                    w0ℕ : Fin.toℕ (aS12 0F) ≡ 2
                    w0ℕ = toℕ-assoc-lt 1 2 {sB + (sC₁ + n)} 0F (Nat.s≤s Nat.z≤n)
                    twoLE0 : 2 Nat.≤ Fin.toℕ (aS12 0F)
                    twoLE0 = subst (2 Nat.≤_) (sym w0ℕ) Nat.≤-refl
                    red0ℕ : Fin.toℕ (Fin.reduce≥ (aS12 0F) twoLE0) ≡ 0
                    red0ℕ = toℕ-reduce≥ (aS12 0F) twoLE0 ■ cong (Nat._∸ 2) w0ℕ
                    wℕ : Fin.toℕ (aS1sB (aS12 0F)) ≡ 2 + sB
                    wℕ = ↑*-hi (assocSwapᵣ 1 sB) 2 (aS12 0F) twoLE0
                       ■ cong (2 +_) ( toℕ-assoc-lt 1 sB (Fin.reduce≥ (aS12 0F) twoLE0)
                                         (subst (Nat._< 1) (sym red0ℕ) (Nat.s≤s Nat.z≤n))
                                     ■ cong (sB +_) red0ℕ ■ Nat.+-identityʳ sB )
                    w = aS1sB (aS12 0F)
                    twoLE : 2 Nat.≤ Fin.toℕ w
                    twoLE = subst (2 Nat.≤_) (sym wℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                    w' = Fin.reduce≥ w twoLE
                    w'ℕ : Fin.toℕ w' ≡ sB
                    w'ℕ = toℕ-reduce≥ w twoLE ■ cong (Nat._∸ 2) wℕ
                    sB≤w' : sB Nat.≤ Fin.toℕ w'
                    sB≤w' = subst (sB Nat.≤_) (sym w'ℕ) Nat.≤-refl
                    w'' = Fin.reduce≥ w' sB≤w'
                    w''ℕ : Fin.toℕ w'' ≡ 0
                    w''ℕ = toℕ-reduce≥ w' sB≤w' ■ cong (Nat._∸ sB) w'ℕ ■ Nat.n∸n≡0 sB
                    θ4q : Fin.toℕ (θ4 w'') ≡ sT
                    θ4q = θ4-toℕ-via w''
                        ■ toℕ-assoc-lt 1 sT (subst 𝔽 M1 w'')
                            (subst (Nat._< 1) (sym (toℕ-subst𝔽 M1 w'' ■ w''ℕ)) (Nat.s≤s Nat.z≤n))
                        ■ cong (sT +_) (toℕ-subst𝔽 M1 w'' ■ w''ℕ) ■ Nat.+-identityʳ sT
                rhsℕ : Fin.toℕ (ρ₁₂'R (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ (proj₂ sib)))))) ≡ 2 + (sB + sT)
                rhsℕ =
                    toℕ-assoc-ge sB 2 (ρ₁' wz) sB2≤
                  ■ ρ₁'ℕ
                  ■ arith
                  where
                    z = proj₁ (proj₂ (proj₂ (proj₂ sib)))
                    zℕ : Fin.toℕ z ≡ sT
                    zℕ = canonₛ-sib-r-zℕ B₁ cc1 b₁ B₂
                    wz = weaken* ⦃ Kᵣ ⦄ sB z
                    wzℕ : Fin.toℕ wz ≡ sB + sT
                    wzℕ = toℕ-wk sB z ■ cong (sB +_) zℕ
                    sB≤wz : sB Nat.≤ Fin.toℕ wz
                    sB≤wz = subst (sB Nat.≤_) (sym wzℕ) (Nat.m≤m+n sB sT)
                    redwzℕ : Fin.toℕ (Fin.reduce≥ wz sB≤wz) ≡ sT
                    redwzℕ = toℕ-reduce≥ wz sB≤wz ■ cong (Nat._∸ sB) wzℕ ■ Nat.m+n∸m≡n sB sT
                    sT<sC₁' : sT Nat.< sC₁'
                    sT<sC₁' = subst (sT Nat.<_) (sym (syncs-rwk B₁)) (Nat.s≤s (sT≤syncs B₁))
                    ρ₁'ℕ : Fin.toℕ (ρ₁' wz) ≡ sB + (2 + sT)
                    ρ₁'ℕ = ↑*-hi (assocSwapᵣ sC₁' 2) sB wz sB≤wz
                         ■ cong (sB +_) ( toℕ-assoc-lt sC₁' 2 (Fin.reduce≥ wz sB≤wz)
                                            (subst (Nat._< sC₁') (sym redwzℕ) sT<sC₁')
                                        ■ cong (2 +_) redwzℕ )
                    sB2≤ : sB + 2 Nat.≤ Fin.toℕ (ρ₁' wz)
                    sB2≤ = subst (sB + 2 Nat.≤_) (sym ρ₁'ℕ) (Nat.+-monoʳ-≤ sB (Nat.m≤m+n 2 sT))
                    arith : sB + (2 + sT) ≡ 2 + (sB + sT)
                    arith = solve 2 (λ a b → a :+ (con 2 :+ b) := con 2 :+ (a :+ b)) refl sB sT
                      where open +-*-Solver
                compZ : ρB (aS1sB (aS12 0F)) ≡ ρ₁₂'R (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ (proj₂ sib)))))
                compZ = Fin.toℕ-injective (freshℕ ■ sym rhsℕ)
                leftEq : (((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⊗ (` Fin.suc Xch)) ⊗ (` 0F))
                           ⋯ aS12 ⋯ aS1sB ⋯ ρB
                         ≡ σ'ᴿ (𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 0F)
                leftEq = cong₂ _⊗_ (cong₂ _⊗_ compA (cong `_ compX)) (cong `_ compZ) ■ sym σ'ᴿinj0
                rightEq : (((` 0F) ⊗ (` Fin.suc Xch)) ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ))
                            ⋯ aS12 ⋯ aS1sB ⋯ ρB
                          ≡ σ'ᴿ (𝐒.inj {1 ∷ suc b₁ ∷ []} {m} 1F)
                rightEq = cong₂ _⊗_ (cong₂ _⊗_ (cong `_ compZ) (cong `_ compX)) compC ■ sym σ'ᴿinj1
                holeEq = cong₂ _⊗_ leftEq rightEq
                ptw : (ρ⁻ ·ₖ (σ' ·ₖ WTRAIL)) ≗ (ρ⁻ ·ₖ (𝐒.rwk ·ₖ σ'ᴿ))
                ptw y =
                    fusion (leafσ (ρ⁻ y)) ρ₁₂ WTRAIL
                  ■ ⋯-cong (leafσ (ρ⁻ y)) keyFull
                  ■ sym (fusion (leafσ (ρ⁻ y)) (rinsB ↑* sB) ρ₁₂'R)
                  ■ cong (_⋯ ρ₁₂'R) (rwk-id-off0 (ρ⁻ y) (ρ⁻-skip y))
                fuse4 : (((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* aS12) ⋯ᶠ* aS1sB) ⋯ᶠ* ρB ≡ Fr ⋯ᶠ* WTRAIL
                fuse4 =
                    cong (λ e → (e ⋯ᶠ* aS1sB) ⋯ᶠ* ρB) (⋯ᶠ*-fusion Fr weakenᵣ aS12)
                  ■ cong (λ e → e ⋯ᶠ* ρB) (⋯ᶠ*-fusion Fr (weakenᵣ ·ₖ aS12) aS1sB)
                  ■ ⋯ᶠ*-fusion Fr ((weakenᵣ ·ₖ aS12) ·ₖ aS1sB) ρB
                frameEq : (((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* aS12) ⋯ᶠ* aS1sB) ⋯ᶠ* ρB ≡ frame*-⋯ Eᴿ σ'ᴿ Vσ'ᴿ
                frameEq =
                    fuse4
                  ■ frame*-⋯-then-ren E Vσ' WTRAIL V1
                  ■ cong (λ e → frame*-⋯ e (σ' ·ₖ WTRAIL) V1) Eeq
                  ■ frame*-fusion-gen E₀ V1 (λ y → V1 (ρ⁻ y))
                  ■ frame*-cong E₀ (λ y → V1 (ρ⁻ y)) (λ y → Vσ'ᴿ (𝐒.rwk (ρ⁻ y))) ptw
                  ■ sym (frame*-fusion-gen E₀ (λ y → Vσ'ᴿ (𝐒.rwk y)) (λ y → Vσ'ᴿ (𝐒.rwk (ρ⁻ y))))
                  ■ sym (frame*-fusion-gen (E₀ ⋯ᶠ* ρ⁻) Vσ'ᴿ (λ y → Vσ'ᴿ (𝐒.rwk y)))
                  ■ cong (λ e → frame*-⋯ (e ⋯ᶠ* 𝐒.rwk) σ'ᴿ Vσ'ᴿ) (sym Eeq)
                RpForm_R : (((Eᴿ [ pair ]*) ⋯ leafσ') ⋯ ρ₁') ⋯ assocSwapᵣ sB 2 ≡ frame*-⋯ Eᴿ σ'ᴿ Vσ'ᴿ [ pair ⋯ σ'ᴿ ]*
                RpForm_R =
                    fusion ((Eᴿ [ pair ]*) ⋯ leafσ') ρ₁' (assocSwapᵣ sB 2)
                  ■ fusion (Eᴿ [ pair ]*) leafσ' ρ₁₂'R
                  ■ frame-plug* Eᴿ σ'ᴿ Vσ'ᴿ
                pushChain : ((Fr ⋯ᶠ* weakenᵣ) [ (((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⊗ (` Fin.suc Xch)) ⊗ (` 0F))
                              ⊗ (((` 0F) ⊗ (` Fin.suc Xch)) ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ)) ]*)
                              ⋯ aS12 ⋯ aS1sB ⋯ ρB
                            ≡ ((((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* aS12) ⋯ᶠ* aS1sB) ⋯ᶠ* ρB)
                              [ ((((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ) ⊗ (` Fin.suc Xch)) ⊗ (` 0F))
                              ⊗ (((` 0F) ⊗ (` Fin.suc Xch)) ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂ ⋯ weakenᵣ)))
                              ⋯ aS12 ⋯ aS1sB ⋯ ρB ]*
                pushChain =
                    cong (λ z → z ⋯ aS1sB ⋯ ρB) (frame-plug*ᵣ (Fr ⋯ᶠ* weakenᵣ) aS12)
                  ■ cong (λ z → z ⋯ ρB) (frame-plug*ᵣ ((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* aS12) aS1sB)
                  ■ frame-plug*ᵣ (((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* aS12) ⋯ᶠ* aS1sB) ρB
                bodyEq = pushChain ■ cong₂ _[_]* frameEq holeEq ■ sym RpForm_R
            flagG1Eq : ((ρB (aS1sB (aS12 0F)) 𝐔.↦ 𝐔.unset)
                        𝐔.∥ (G1 𝐔.⋯ₚ weakenᵣ 𝐔.⋯ₚ aS12 𝐔.⋯ₚ aS1sB 𝐔.⋯ₚ ρB))
                       𝐔.≋ G1_R
            flagG1Eq  = Eq*.symmetric _
              (  ≡→≋ G1R-fuse
              ◅◅ flagsRenMerge B₁ {2 + n} {b₁} {B₂} ρcomp
              ◅◅ ≡→≋ (cong₂ 𝐔._∥_ flagPosEq rightStuffEq) )
              where
                ρcomp : (sC₁' + (2 + n)) →ᵣ (2 + (sB + (sC₁' + n)))
                ρcomp = weaken* ⦃ Kᵣ ⦄ sB ·ₖ (ρ₁' ·ₖ assocSwapᵣ sB 2)
                G1R-fuse : G1_R ≡ Flags C₁' 𝐔.⋯ₚ ρcomp
                G1R-fuse = 𝐔.fusionₚ (Flags C₁' 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) ρ₁' (assocSwapᵣ sB 2)
                         ■ 𝐔.fusionₚ (Flags C₁') (weaken* ⦃ Kᵣ ⦄ sB) (ρ₁' ·ₖ assocSwapᵣ sB 2)
                freshℕ : Fin.toℕ (ρB (aS1sB (aS12 0F))) ≡ 2 + (sB + sT)
                freshℕ =
                    ↑*-hi (θ4 ↑* sB) 2 w twoLE
                  ■ cong (2 +_) (↑*-hi θ4 sB w' sB≤w' ■ cong (sB +_) θ4q)
                  where
                    w0ℕ : Fin.toℕ (aS12 0F) ≡ 2
                    w0ℕ = toℕ-assoc-lt 1 2 {sB + (sC₁ + n)} 0F (Nat.s≤s Nat.z≤n)
                    twoLE0 : 2 Nat.≤ Fin.toℕ (aS12 0F)
                    twoLE0 = subst (2 Nat.≤_) (sym w0ℕ) Nat.≤-refl
                    red0ℕ : Fin.toℕ (Fin.reduce≥ (aS12 0F) twoLE0) ≡ 0
                    red0ℕ = toℕ-reduce≥ (aS12 0F) twoLE0 ■ cong (Nat._∸ 2) w0ℕ
                    wℕ : Fin.toℕ (aS1sB (aS12 0F)) ≡ 2 + sB
                    wℕ = ↑*-hi (assocSwapᵣ 1 sB) 2 (aS12 0F) twoLE0
                       ■ cong (2 +_) ( toℕ-assoc-lt 1 sB (Fin.reduce≥ (aS12 0F) twoLE0)
                                         (subst (Nat._< 1) (sym red0ℕ) (Nat.s≤s Nat.z≤n))
                                     ■ cong (sB +_) red0ℕ ■ Nat.+-identityʳ sB )
                    w = aS1sB (aS12 0F)
                    twoLE : 2 Nat.≤ Fin.toℕ w
                    twoLE = subst (2 Nat.≤_) (sym wℕ) (Nat.s≤s (Nat.s≤s Nat.z≤n))
                    w' = Fin.reduce≥ w twoLE
                    w'ℕ : Fin.toℕ w' ≡ sB
                    w'ℕ = toℕ-reduce≥ w twoLE ■ cong (Nat._∸ 2) wℕ
                    sB≤w' : sB Nat.≤ Fin.toℕ w'
                    sB≤w' = subst (sB Nat.≤_) (sym w'ℕ) Nat.≤-refl
                    w'' = Fin.reduce≥ w' sB≤w'
                    w''ℕ : Fin.toℕ w'' ≡ 0
                    w''ℕ = toℕ-reduce≥ w' sB≤w' ■ cong (Nat._∸ sB) w'ℕ ■ Nat.n∸n≡0 sB
                    θ4q : Fin.toℕ (θ4 w'') ≡ sT
                    θ4q = θ4-toℕ-via w''
                        ■ toℕ-assoc-lt 1 sT (subst 𝔽 M1 w'')
                            (subst (Nat._< 1) (sym (toℕ-subst𝔽 M1 w'' ■ w''ℕ)) (Nat.s≤s Nat.z≤n))
                        ■ cong (sT +_) (toℕ-subst𝔽 M1 w'' ■ w''ℕ) ■ Nat.+-identityʳ sT
                ρcompInsℕ : Fin.toℕ (ρcomp (insP B₁ {2 + n} b₁ B₂)) ≡ 2 + (sB + sT)
                ρcompInsℕ =
                    toℕ-assoc-ge sB 2 (ρ₁' wz) sB2≤
                  ■ ρ₁'ℕ
                  ■ arith
                  where
                    wz = weaken* ⦃ Kᵣ ⦄ sB (insP B₁ {2 + n} b₁ B₂)
                    wzℕ : Fin.toℕ wz ≡ sB + sT
                    wzℕ = toℕ-wk sB (insP B₁ {2 + n} b₁ B₂) ■ cong (sB +_) (insP-ℕ B₁ {2 + n} b₁ B₂)
                    sB≤wz : sB Nat.≤ Fin.toℕ wz
                    sB≤wz = subst (sB Nat.≤_) (sym wzℕ) (Nat.m≤m+n sB sT)
                    redwzℕ : Fin.toℕ (Fin.reduce≥ wz sB≤wz) ≡ sT
                    redwzℕ = toℕ-reduce≥ wz sB≤wz ■ cong (Nat._∸ sB) wzℕ ■ Nat.m+n∸m≡n sB sT
                    sT<sC₁' : sT Nat.< sC₁'
                    sT<sC₁' = subst (sT Nat.<_) (sym (syncs-rwk B₁)) (Nat.s≤s (sT≤syncs B₁))
                    ρ₁'ℕ : Fin.toℕ (ρ₁' wz) ≡ sB + (2 + sT)
                    ρ₁'ℕ = ↑*-hi (assocSwapᵣ sC₁' 2) sB wz sB≤wz
                         ■ cong (sB +_) ( toℕ-assoc-lt sC₁' 2 (Fin.reduce≥ wz sB≤wz)
                                            (subst (Nat._< sC₁') (sym redwzℕ) sT<sC₁')
                                        ■ cong (2 +_) redwzℕ )
                    sB2≤ : sB + 2 Nat.≤ Fin.toℕ (ρ₁' wz)
                    sB2≤ = subst (sB + 2 Nat.≤_) (sym ρ₁'ℕ) (Nat.+-monoʳ-≤ sB (Nat.m≤m+n 2 sT))
                    arith : sB + (2 + sT) ≡ 2 + (sB + sT)
                    arith = solve 2 (λ a b → a :+ (con 2 :+ b) := con 2 :+ (a :+ b)) refl sB sT
                      where open +-*-Solver
                flagPosEq : (ρcomp (insP B₁ {2 + n} b₁ B₂) 𝐔.↦ 𝐔.unset) ≡ (ρB (aS1sB (aS12 0F)) 𝐔.↦ 𝐔.unset)
                flagPosEq = cong (𝐔._↦ 𝐔.unset) (Fin.toℕ-injective (ρcompInsℕ ■ sym freshℕ))
                comm : (rins B₁ b₁ B₂ ·ₖ ρcomp) ≗ (weaken* ⦃ Kᵣ ⦄ sB ·ₖ target)
                comm y = cong (ρ₁' ·ₖ assocSwapᵣ sB 2) (↑*-wk rinsB sB y)
                rightStuffEq : Flags C₁ 𝐔.⋯ₚ (rins B₁ b₁ B₂ ·ₖ ρcomp)
                               ≡ G1 𝐔.⋯ₚ weakenᵣ 𝐔.⋯ₚ aS12 𝐔.⋯ₚ aS1sB 𝐔.⋯ₚ ρB
                rightStuffEq =
                    𝐔.⋯ₚ-cong (Flags C₁) comm
                  ■ sym (𝐔.fusionₚ (Flags C₁) (weaken* ⦃ Kᵣ ⦄ sB) target)
                  ■ sym (𝐔.⋯ₚ-cong (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) keyFull)
                  ■ sym (fuse6 (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB))
            SpEq = ≡→≋ Pleafeq′
              where
                FULLr = ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (aS12 ·ₖ (aS1sB ·ₖ ρB))))
                Pleafeq : U[ P ] leafσ 𝐔.⋯ₚ FULLr ≡ U[ P 𝐓.⋯ₚ 𝐒.rwk ] (leafσ' ·ₖ (ρ₁' ·ₖ assocSwapᵣ sB 2 {sC₁' + n}))
                Pleafeq =
                    U-σ⋯ P
                  ■ cong (λ p → U[ p ] (leafσ ·ₖ FULLr)) Peq
                  ■ U-⋯ₚ P₀
                  ■ U-cong P₀ (λ y → ⋯-cong (leafσ (ρ⁻ y)) keyFull
                                  ■ sym (fusion (leafσ (ρ⁻ y)) (rinsB ↑* sB) (ρ₁' ·ₖ assocSwapᵣ sB 2 {sC₁' + n}))
                                  ■ cong (_⋯ (ρ₁' ·ₖ assocSwapᵣ sB 2 {sC₁' + n})) (rwk-id-off0 (ρ⁻ y) (ρ⁻-skip y)))
                  ■ sym (U-⋯ₚ P₀)
                  ■ cong (λ p → U[ p ] (𝐒.rwk ·ₖ (leafσ' ·ₖ (ρ₁' ·ₖ assocSwapᵣ sB 2 {sC₁' + n})))) (sym Peq)
                  ■ sym (U-⋯ₚ P)
                Pleafeq′ : U[ P ] leafσ 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂ 𝐔.⋯ₚ weakenᵣ 𝐔.⋯ₚ aS12 𝐔.⋯ₚ aS1sB 𝐔.⋯ₚ ρB
                           ≡ U[ P 𝐓.⋯ₚ 𝐒.rwk ] leafσ' 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2 {sC₁' + n}
                Pleafeq′ =
                    fuse6 (U[ P ] leafσ)
                  ■ Pleafeq
                  ■ sym ( cong (𝐔._⋯ₚ assocSwapᵣ sB 2 {sC₁' + n})
                               (U-σ⋯ (P 𝐓.⋯ₚ 𝐒.rwk) {leafσ'} {ρ₁'})
                        ■ U-σ⋯ (P 𝐓.⋯ₚ 𝐒.rwk) {leafσ' ·ₖ ρ₁'} {assocSwapᵣ sB 2 {sC₁' + n}}
                        ■ U-cong (P 𝐓.⋯ₚ 𝐒.rwk)
                                 {(leafσ' ·ₖ ρ₁') ·ₖ assocSwapᵣ sB 2 {sC₁' + n}}
                                 {leafσ' ·ₖ (ρ₁' ·ₖ assocSwapᵣ sB 2 {sC₁' + n})}
                                 (λ y → fusion (leafσ' y) ρ₁' (assocSwapᵣ sB 2 {sC₁' + n})) )
            assembled = reorder
                    ◅◅  𝐔.∥-cong threadEq (𝐔.∥-cong G2Eq (𝐔.∥-cong flagG1Eq SpEq))
        dataReconcile =
            ≡→≋ (cong (λ z → subst (λ j → 𝐔.Proc (j + n)) e''
                              (subst 𝐔.Proc M3 (subst 𝐔.Proc M2 z)))
                      (subst-⋯ₚ′ M1 _ (assocSwapᵣ 1 sT {r + n})))
          ◅◅ ≡→≋ (cong (λ z → subst (λ j → 𝐔.Proc (j + n)) e'' (subst 𝐔.Proc M3 z))
                      (sym (subst-⋯ₚ-cod M2 _ _)))
          ◅◅ ≡→≋ (cong (subst (λ j → 𝐔.Proc (j + n)) e'') (sym (subst-⋯ₚ-cod M3 _ _)))
          ◅◅ ≡→≋ (sym (subst-cong+P e'' _))
          ◅◅ ≡→≋ (sym (subst-⋯ₚ-cod (cong (Nat._+ n) e'') _ _))
          ◅◅ ≡→≋ (φ^-⋯ₚ sB _ _)
          ◅◅ φ^-cong sB (𝐔.ν-cong compRec)