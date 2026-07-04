module BorrowedCF.Simulation.Theorems.SplitsLQ where

-- | q-generalized lsplit helpers: the interior local split fires at block
--   position q of a width-(q + suc b₁) block, growing it to width
--   (q + suc (suc b₁)).  These mirror the position-0 helpers in SplitsH1
--   (dlwk / 𝐒lwk-lo/hi / P1/P2/P3 / canonₛ-lwk / canonₛ-handle) but thread the
--   block position q, so lwk inserts at flat position sum B₁ + q + 1 and the
--   consumed handle sits at sum B₁ + q.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Simulation.BlockPerm
  using ( toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt )

open import BorrowedCF.Simulation.Theorems.SplitsH1 public

-- ============================================================================
--   dlwkq : data-level lwk on the C₁ block group, inserting a slot at flat
--   position sum B₁ + q + 1 (block position q+1, right after the handle).
-- ============================================================================
dlwkq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) →
        sum (B₁ ++ (q + suc b₁) ∷ B₂) →ᵣ sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
dlwkq []        zero    b₁ B₂ i = (weakenᵣ ↑* 1) i
dlwkq []        (suc q) b₁ B₂ i with i
... | zero   = zero
... | suc i′ = suc (dlwkq [] q b₁ B₂ i′)
dlwkq (a ∷ B₁') q b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ (q + suc (suc b₁)) ∷ B₂)) , (λ r → a ↑ʳ dlwkq B₁' q b₁ B₂ r) ]′ (splitAt a i)

-- dlwkq preserves toℕ below the insertion point (flat position sum B₁ + q + 1).
dlwkq-lo : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) (j : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
           Fin.toℕ j Nat.< sum B₁ + q + 1 → Fin.toℕ (dlwkq B₁ q b₁ B₂ j) ≡ Fin.toℕ j
dlwkq-lo []        zero    b₁ B₂ j lt = toℕ-↑*-lt weakenᵣ 1 j lt
dlwkq-lo []        (suc q) b₁ B₂ j lt with j
... | zero   = refl
... | suc j′ = cong suc (dlwkq-lo [] q b₁ B₂ j′ (Nat.s≤s⁻¹ lt))
dlwkq-lo (a ∷ B₁') q b₁ B₂ j lt with dlwkq-lo B₁' q b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ (q + suc b₁) ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwkq B₁' q b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        assoc3 : a + sum B₁' + q + 1 ≡ a + (sum B₁' + q + 1)
        assoc3 = cong (Nat._+ 1) (Nat.+-assoc a (sum B₁') q) ■ Nat.+-assoc a (sum B₁' + q) 1
        boundr : Fin.toℕ r Nat.< sum B₁' + q + 1
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁' + q + 1)
                   (subst (Nat._< a + (sum B₁' + q + 1)) jℕ
                     (subst (Fin.toℕ j Nat.<_) assoc3 lt))

-- dlwkq shifts toℕ by one at/above the insertion point.
dlwkq-hi : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) (j : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
           sum B₁ + q + 1 Nat.≤ Fin.toℕ j → Fin.toℕ (dlwkq B₁ q b₁ B₂ j) ≡ suc (Fin.toℕ j)
dlwkq-hi []        zero    b₁ B₂ j h =
    toℕ-↑*-ge weakenᵣ 1 j h
  ■ cong (1 +_) (cong suc (toℕ-reduce≥ j h))
  ■ cong suc (Nat.m+[n∸m]≡n h)
dlwkq-hi []        (suc q) b₁ B₂ j h with j
... | zero   = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.s≤s Nat.z≤n) h))
... | suc j′ = cong suc (dlwkq-hi [] q b₁ B₂ j′ (Nat.s≤s⁻¹ h))
dlwkq-hi (a ∷ B₁') q b₁ B₂ j h with dlwkq-hi B₁' q b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁' + q + 1))) (subst (Nat._≤ Fin.toℕ j) assoc3 h)))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ (q + suc b₁) ∷ B₂))
        assoc3 : a + sum B₁' + q + 1 ≡ a + (sum B₁' + q + 1)
        assoc3 = cong (Nat._+ 1) (Nat.+-assoc a (sum B₁') q) ■ Nat.+-assoc a (sum B₁' + q) 1
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwkq B₁' q b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        assoc3 : a + sum B₁' + q + 1 ≡ a + (sum B₁' + q + 1)
        assoc3 = cong (Nat._+ 1) (Nat.+-assoc a (sum B₁') q) ■ Nat.+-assoc a (sum B₁' + q) 1
        boundr : sum B₁' + q + 1 Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁' + q + 1) (Fin.toℕ r)
                   (subst (a + (sum B₁' + q + 1) Nat.≤_) jℕ
                     (subst (Nat._≤ Fin.toℕ j) assoc3 h))

-- The interior-grown bind group has exactly one more data slot.
sum-lwkq : ∀ (B₁ : BindGroup) {q b₁ B₂} →
           sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂))
sum-lwkq B₁ {q} {b₁} {B₂} = sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)
                          ■ cong (sum B₁ +_) (cong (Nat._+ sum B₂) (Nat.+-suc q (suc b₁)))
                          ■ Nat.+-suc (sum B₁) ((q + suc b₁) + sum B₂)
                          ■ cong suc (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))

-- syncs is width-agnostic, hence unchanged (explicit q form).
syncs-lwkq : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} →
             syncs (B₁ ++ (q + suc b₁) ∷ B₂) ≡ syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
syncs-lwkq []            {q} {b₁} {[]}      = refl
syncs-lwkq []            {q} {b₁} {b' ∷ B'} = refl
syncs-lwkq (a ∷ [])      {q} {b₁} {B₂}      = cong suc (syncs-lwkq [] {q} {b₁} {B₂})
syncs-lwkq (a ∷ d ∷ B₁″) {q} {b₁} {B₂}      = cong suc (syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂})

sB₁q+1≤sumC₁q : ∀ (B₁ : BindGroup) {q b₁ B₂} → sum B₁ + q + 1 Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
sB₁q+1≤sumC₁q B₁ {q} {b₁} {B₂} =
  subst (sum B₁ + q + 1 Nat.≤_) (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
    (subst (Nat._≤ sum B₁ + ((q + suc b₁) + sum B₂)) (sym (Nat.+-assoc (sum B₁) q 1))
      (Nat.+-monoʳ-≤ (sum B₁) q+1≤))
  where q+1≤ : q + 1 Nat.≤ (q + suc b₁) + sum B₂
        q+1≤ = Nat.≤-trans (Nat.+-monoʳ-≤ q (Nat.s≤s Nat.z≤n)) (Nat.m≤m+n (q + suc b₁) (sum B₂))

-- 𝐒.lwk {q} preserves toℕ below the insertion point.
𝐒lwkq-lo : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ}
             (x : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
             Fin.toℕ x Nat.< sum B₁ + q + 1 →
             Fin.toℕ (TR.SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} x) ≡ Fin.toℕ x
𝐒lwkq-lo B₁ B₂ B {q} {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-lt weakenᵣ (sum B₁ + q + 1) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁ + q + 1
        lt′ = subst (Nat._< sum B₁ + q + 1) (sym (Fin.toℕ-cast _ x)) lt

-- 𝐒.lwk {q} shifts toℕ by one at/above the insertion point.
𝐒lwkq-hi : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ}
             (x : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
             sum B₁ + q + 1 Nat.≤ Fin.toℕ x →
             Fin.toℕ (TR.SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒lwkq-hi B₁ B₂ B {q} {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-ge weakenᵣ (sum B₁ + q + 1) (Fin.cast _ x) h′
  ■ cong (sum B₁ + q + 1 +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ (sum B₁ + q + 1)) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁ + q + 1) (Fin.toℕ x Nat.∸ (sum B₁ + q + 1))
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ + q + 1 Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ + q + 1 Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

-- lwk on a C₁-embedded data position equals the dlwkq-shifted embedding.
P1q : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
      TR.SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
      ≡ (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1q B₁ B₂ B {q} {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁ + q + 1
... | yes lt = Fin.toℕ-injective
      ( 𝐒lwkq-lo B₁ B₂ B _ (subst (Nat._< sum B₁ + q + 1) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ dlwkq-lo B₁ q b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwkq B₁ q b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwkq B₁ q b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒lwkq-hi B₁ B₂ B _ (subst (sum B₁ + q + 1 Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ dlwkq-hi B₁ q b₁ B₂ d h≤) )
  where h≤ : sum B₁ + q + 1 Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwkq B₁ q b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwkq B₁ q b₁ B₂ d) (sum B)

-- lwk on a B-region position shifts the embedding scope by one.
P2q : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} (w : 𝔽 (sum B)) →
      TR.SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m)
      ≡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w) ↑ˡ m
P2q B₁ B₂ B {q} {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒lwkq-hi B₁ B₂ B _ (subst (sum B₁ + q + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁q+1≤sumC₁q B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ (q + suc b₁) ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc b₁) ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-lwkq B₁)

-- lwk on a tail (outer) position shifts the embedding scope by one.
P3q : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} (u : 𝔽 m) →
      TR.SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u)
      ≡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) ↑ʳ u
P3q B₁ B₂ B {q} {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒lwkq-hi B₁ B₂ B _ (subst (sum B₁ + q + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁q+1≤sumC₁q B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-lwkq B₁)
