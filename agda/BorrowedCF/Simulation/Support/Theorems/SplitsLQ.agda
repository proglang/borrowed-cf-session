module BorrowedCF.Simulation.Support.Theorems.SplitsLQ where

-- | q-generalized lsplit helpers: the interior local split fires at block
--   position q of a width-(q + suc b₁) block, growing it to width
--   (q + suc (suc b₁)).  These mirror the position-0 helpers in SplitsH1
--   (dlwk / 𝐒lwk-lo/hi / P1/P2/P3 / canonₛ-lwk / canonₛ-handle) but thread the
--   block position q, so lwk inserts at flat position sum B₁ + q + 1 and the
--   consumed handle sits at sum B₁ + q.

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Terms using (module SplitRenamings)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Simulation.Support.BlockPerm
  using ( toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt )

open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 public

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
             Fin.toℕ (SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} x) ≡ Fin.toℕ x
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
             Fin.toℕ (SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} x) ≡ suc (Fin.toℕ x)
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
      SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
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
      SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m)
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
      SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u)
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

-- ============================================================================
--   Position-q handle triple.  Ub[q + suc b] distributes: at the shifted
--   position q ↑ʳ 0F it is a channel triple whose junction is the channel c.
-- ============================================================================
Ub-triple : ∀ w {N} (e1 e2 : Tm N) (c : 𝔽 N) (i : 𝔽 w) →
  Σ[ a ∈ Tm N ] Σ[ e2' ∈ Tm N ] Ub[ w ] (e1 , c , e2) i ≡ (a ⊗ (` c)) ⊗ e2'
Ub-triple zero          e1 e2 c ()
Ub-triple (suc zero)    e1 e2 c zero    = e1 , e2 , refl
Ub-triple (suc zero)    e1 e2 c (suc ())
Ub-triple (suc (suc b)) e1 e2 c zero    = e1 , * , refl
Ub-triple (suc (suc b)) e1 e2 c (suc x) = Ub-triple (suc b) * e2 c x

private
  substTripL : ∀ {p qq} (eq : p ≡ qq) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
               subst Tm eq ((A ⊗ (` jj)) ⊗ C)
               ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
  substTripL refl A jj C = refl
  toℕ-subst𝔽L : ∀ {p qq} (e : p ≡ qq) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
  toℕ-subst𝔽L refl y = refl

-- canonₛ at the position-q handle of the single split block (prefix []),
-- a chanTriple whose junction sits at flat position syncs + toℕ x.
canonₛ-head-tripleq : ∀ (q b₁ : ℕ) (B₂ : BindGroup) {N} (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs ((q + suc b₁) ∷ B₂) + N) ] Σ[ c ∈ Tm (syncs ((q + suc b₁) ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs ((q + suc b₁) ∷ B₂) + N) ]
    (canonₛ ((q + suc b₁) ∷ B₂) (e1 , x , e2) ((q ↑ʳ 0F) ↑ˡ sum B₂) ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs ((q + suc b₁) ∷ B₂) + Fin.toℕ x)
canonₛ-head-tripleq q b₁ [] e1 e2 x
  with Ub-triple ((q + suc b₁) + 0) e1 e2 x ((q ↑ʳ 0F) ↑ˡ 0)
... | a , e2' , ubeq = a , e2' , x , ubeq , refl
canonₛ-head-tripleq q b₁ (c′ ∷ B) {N} e1 e2 x
  with Ub-triple (q + suc b₁) (wk e1) (` 0F) (suc x) (q ↑ʳ 0F)
... | a , e2' , ubeq =
  ( subst Tm (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq , junceq )
  where
    sB = syncs (c′ ∷ B)
    spliteq : splitAt (q + suc b₁) ((q ↑ʳ 0F) ↑ˡ sum (c′ ∷ B)) ≡ inj₁ (q ↑ʳ 0F)
    spliteq = Fin.splitAt-↑ˡ (q + suc b₁) (q ↑ʳ 0F) (sum (c′ ∷ B))
    tripeq : canonₛ ((q + suc b₁) ∷ c′ ∷ B) (e1 , x , e2) ((q ↑ʳ 0F) ↑ˡ sum (c′ ∷ B))
             ≡ (subst Tm (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ q + suc b₁ ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ (c′ ∷ B) (` 0F , suc x , wk e2) ]′ spliteq
               ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) ubeq)
           ■ substTripL (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽L (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)

-- ============================================================================
--   canonₛ-handleq : the position-q handle triple over a whole prefix B₁.
--   Mirrors canonₛ-handle (SplitsH1) but at block position q (base =
--   canonₛ-head-tripleq, and pos-split-gen replaces pos-split).
-- ============================================================================
canonₛ-handleq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N) ]
    (canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) (e₁ , x , e₂)
        (Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)))
       ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (B₁ ++ (q + suc b₁) ∷ B₂) + Fin.toℕ x)
canonₛ-handleq [] {N} e₁ x e₂ q b₁ B₂ =
  proj₁ h , proj₁ (proj₂ h) , proj₁ (proj₂ (proj₂ h))
  , castidx (proj₁ (proj₂ (proj₂ (proj₂ h))))
  , proj₂ (proj₂ (proj₂ (proj₂ h)))
  where
    h = canonₛ-head-tripleq q b₁ B₂ e₁ e₂ x
    castidx : canonₛ ((q + suc b₁) ∷ B₂) (e₁ , x , e₂) ((q ↑ʳ 0F) ↑ˡ sum B₂)
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h) →
              canonₛ ((q + suc b₁) ∷ B₂) (e₁ , x , e₂)
                (Fin.cast (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)))
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h)
    castidx = subst (λ z → canonₛ ((q + suc b₁) ∷ B₂) (e₁ , x , e₂) z
                            ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h))
                (sym (Fin.toℕ-injective (Fin.toℕ-cast (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)))))
canonₛ-handleq (a ∷ []) {N} e₁ x e₂ q b₁ B₂
  with canonₛ-handleq [] (` 0F) (suc x) (wk e₂) q b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs (([]) ++ (q + suc b₁) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ ([])) ((q + suc b₁) ∷ B₂))) (sum (a ∷ ([])) ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    cp′ = Fin.cast (sym (sum-++ ([]) ((q + suc b₁) ∷ B₂))) (sum ([]) ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a ([]) (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂))
            ■ Fin.splitAt-↑ʳ a (sum (([]) ++ (q + suc b₁) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ ([]) ++ (q + suc b₁) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ (([]) ++ (q + suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripL (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽L (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)
canonₛ-handleq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂
  with canonₛ-handleq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ (d ∷ B₁″)) ((q + suc b₁) ∷ B₂))) (sum (a ∷ (d ∷ B₁″)) ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    cp′ = Fin.cast (sym (sum-++ (d ∷ B₁″) ((q + suc b₁) ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a (d ∷ B₁″) (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂))
            ■ Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ (d ∷ B₁″) ++ (q + suc b₁) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripL (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽L (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)

-- ============================================================================
--   Ub-growth helpers for the B₁ = [] base of canonₛ-lwkq.  shiftq inserts a
--   new data slot right after handle position h; Ub-grow shows this growth is
--   invisible to Ub[_] away from the handle.
-- ============================================================================
shiftq : ∀ {w} (h : ℕ) (j : 𝔽 w) → 𝔽 (suc w)
shiftq zero    zero    = zero
shiftq zero    (suc x) = Fin.suc (Fin.suc x)
shiftq (suc h) zero    = zero
shiftq (suc h) (suc x) = Fin.suc (shiftq h x)

toℕ-shiftq : ∀ {w} (h : ℕ) (j : 𝔽 w) → Fin.toℕ j Nat.< suc h → Fin.toℕ (shiftq h j) ≡ Fin.toℕ j
toℕ-shiftq zero    zero    lt = refl
toℕ-shiftq zero    (suc x) (Nat.s≤s ())
toℕ-shiftq (suc h) zero    lt = refl
toℕ-shiftq (suc h) (suc x) lt = cong suc (toℕ-shiftq h x (Nat.s≤s⁻¹ lt))

toℕ-shiftq-hi : ∀ {w} (h : ℕ) (j : 𝔽 w) → suc h Nat.≤ Fin.toℕ j → Fin.toℕ (shiftq h j) ≡ suc (Fin.toℕ j)
toℕ-shiftq-hi zero    (suc x) le = refl
toℕ-shiftq-hi (suc h) zero    ()
toℕ-shiftq-hi (suc h) (suc x) le = cong suc (toℕ-shiftq-hi h x (Nat.s≤s⁻¹ le))

Ub-reindex : ∀ {w'} (W : ℕ) (weq : w' ≡ W) {N} (cc : UChan N) (j' : 𝔽 w') (k : 𝔽 W) →
             Fin.toℕ j' ≡ Fin.toℕ k → Ub[ w' ] cc j' ≡ Ub[ W ] cc k
Ub-reindex W refl cc j' k eqn = cong (Ub[ W ] cc) (Fin.toℕ-injective eqn)

Ub-grow : ∀ w (h : ℕ) {N} (cc : UChan N) (j : 𝔽 w) → h Nat.< w → Fin.toℕ j ≢ h →
          Ub[ w ] cc j ≡ Ub[ suc w ] cc (shiftq h j)
Ub-grow zero          h cc () h<w j≢h
Ub-grow (suc zero)    zero    cc zero    h<w          j≢h = ⊥-elim (j≢h refl)
Ub-grow (suc zero)    (suc h) cc zero    (Nat.s≤s ()) j≢h
Ub-grow (suc (suc b)) zero    cc zero    h<w          j≢h = ⊥-elim (j≢h refl)
Ub-grow (suc (suc b)) (suc h) cc zero    h<w          j≢h = refl
Ub-grow (suc (suc b)) zero    (e1 , c , e2) (suc x) h<w j≢h = refl
Ub-grow (suc (suc b)) (suc h) (e1 , c , e2) (suc x) h<w j≢h =
  Ub-grow (suc b) h (* , c , e2) x (Nat.s≤s⁻¹ h<w) (λ eq → j≢h (cong suc eq))

Ub-grow' : ∀ w (w' h : ℕ) {N} (cc : UChan N) (j : 𝔽 w) (j' : 𝔽 w') →
           w' ≡ suc w → h Nat.< w → Fin.toℕ j ≢ h → Fin.toℕ j' ≡ Fin.toℕ (shiftq h j) →
           Ub[ w ] cc j ≡ Ub[ w' ] cc j'
Ub-grow' w w' h cc j j' w'eq h<w j≢h j'eq =
    Ub-grow w h cc j h<w j≢h
  ■ Ub-reindex w' (sym w'eq) cc (shiftq h j) j' (sym j'eq)

-- splitAt characterised by toℕ (reverse of splitAt-↑ˡ / splitAt-↑ʳ).
splitAt-inj₁-toℕ : ∀ A {B} (x : 𝔽 (A + B)) (y : 𝔽 A) → Fin.toℕ x ≡ Fin.toℕ y →
                   Fin.splitAt A x ≡ inj₁ y
splitAt-inj₁-toℕ A {B} x y e =
  subst (λ z → Fin.splitAt A z ≡ inj₁ y)
    (sym (Fin.toℕ-injective (e ■ sym (Fin.toℕ-↑ˡ y B))))
    (Fin.splitAt-↑ˡ A y B)

splitAt-inj₂-toℕ : ∀ A {B} (x : 𝔽 (A + B)) (k : 𝔽 B) → Fin.toℕ x ≡ A + Fin.toℕ k →
                   Fin.splitAt A x ≡ inj₂ k
splitAt-inj₂-toℕ A {B} x k e =
  subst (λ z → Fin.splitAt A z ≡ inj₂ k)
    (sym (Fin.toℕ-injective (e ■ sym (Fin.toℕ-↑ʳ A k))))
    (Fin.splitAt-↑ʳ A B k)

-- ============================================================================
--   canonₛ-lwkq : q-generalized canonₛ-lwk.  Growth of the single split block
--   (q + suc b₁) ∷ B₂ → (q + suc (suc b₁)) ∷ B₂ is invisible to canonₛ away
--   from the position-q handle, where dlwkq inserts the new slot at block
--   position q+1 (flat sum B₁ + q + 1).  Mirrors canonₛ-lwk (SplitsH1).
-- ============================================================================
canonₛ-lwkq : ∀ (B₁ : BindGroup) {N} (cc : UChan N) (q b₁ : ℕ) (B₂ : BindGroup)
              (i : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
              i ≢ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)) →
              subst Tm (cong (_+ N) (syncs-lwkq B₁)) (canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) cc i)
              ≡ canonₛ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) cc (dlwkq B₁ q b₁ B₂ i)
canonₛ-lwkq [] {N} cc zero    b₁ B₂ i i≢ =
  subst (λ pf → subst Tm (cong (_+ N) pf) (canonₛ (suc b₁ ∷ B₂) cc i)
                ≡ canonₛ (suc (suc b₁) ∷ B₂) cc (dlwk [] b₁ B₂ i))
    (uipℕ (syncs-lwk [] {b₁} {B₂}) (syncs-lwkq [] {zero} {b₁} {B₂}))
    (canonₛ-lwk [] cc b₁ B₂ i i≢)
canonₛ-lwkq [] {N} cc (suc q) b₁ [] i i≢ =
    Ub-grow ((suc q + suc b₁) + 0) (suc q) cc i pw i≢toℕ
  ■ Ub-reindex ((suc q + suc (suc b₁)) + 0)
      (sym (sum-lwkq [] {suc q} {b₁} {[]})) cc
      (shiftq (suc q) i) (dlwkq [] (suc q) b₁ [] i) toℕeq
  where
    pw : suc q Nat.< (suc q + suc b₁) + 0
    pw = Nat.s≤s (subst (suc q Nat.≤_) (sym (Nat.+-identityʳ (q + suc b₁)))
                   (subst (suc q Nat.≤_) (sym (Nat.+-suc q b₁)) (Nat.s≤s (Nat.m≤m+n q b₁))))
    i≢toℕ : Fin.toℕ i ≢ suc q
    i≢toℕ e = i≢ (Fin.toℕ-injective
      ( e
      ■ sym ( Fin.toℕ-cast (sym (sum-++ [] ((suc q + suc b₁) ∷ []))) (sum [] ↑ʳ ((suc q ↑ʳ 0F) ↑ˡ sum []))
            ■ Fin.toℕ-↑ʳ (sum []) ((suc q ↑ʳ 0F) ↑ˡ sum [])
            ■ Fin.toℕ-↑ˡ (suc q ↑ʳ 0F) (sum [])
            ■ Fin.toℕ-↑ʳ (suc q) 0F
            ■ Nat.+-identityʳ (suc q) )))
    sqp1 : suc q + 1 ≡ suc (suc q)
    sqp1 = Nat.+-comm (suc q) 1
    toℕeq : Fin.toℕ (shiftq (suc q) i) ≡ Fin.toℕ (dlwkq [] (suc q) b₁ [] i)
    toℕeq with Fin.toℕ i Nat.<? suc (suc q)
    ... | yes lt = toℕ-shiftq (suc q) i lt
                 ■ sym (dlwkq-lo [] (suc q) b₁ [] i (subst (Fin.toℕ i Nat.<_) (sym sqp1) lt))
    ... | no ¬lt = toℕ-shiftq-hi (suc q) i (Nat.≮⇒≥ ¬lt)
                 ■ sym (dlwkq-hi [] (suc q) b₁ [] i (subst (Nat._≤ Fin.toℕ i) (sym sqp1) (Nat.≮⇒≥ ¬lt)))
canonₛ-lwkq [] {N} (e₁ , x , e₂) (suc q) b₁ (c' ∷ B) i i≢ =
  cong (subst Tm (+-suc sB2 N)) bracket-eq
  where
    sB2  = syncs (c' ∷ B)
    ccU  = (wk e₁ , suc x , ` 0F)
    ccr  = (` 0F , suc x , wk e₂)
    triL = Ub[ suc q + suc b₁ ] ccU ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
    triR = Ub[ suc q + suc (suc b₁) ] ccU ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
    G  = [ triL , canonₛ {n = suc N} (c' ∷ B) ccr ]′
    G′ = [ triR , canonₛ {n = suc N} (c' ∷ B) ccr ]′
    sqp1 : suc q + 1 ≡ suc (suc q)
    sqp1 = Nat.+-comm (suc q) 1
    w'eq : suc q + suc (suc b₁) ≡ suc (suc q + suc b₁)
    w'eq = cong suc (Nat.+-suc q (suc b₁))
    h<w : suc q Nat.< suc q + suc b₁
    h<w = Nat.s≤s (subst (suc q Nat.≤_) (sym (Nat.+-suc q b₁)) (Nat.s≤s (Nat.m≤m+n q b₁)))
    i≢toℕ : Fin.toℕ i ≢ suc q
    i≢toℕ e = i≢ (Fin.toℕ-injective
      ( e
      ■ sym ( Fin.toℕ-cast (sym (sum-++ [] ((suc q + suc b₁) ∷ (c' ∷ B)))) (sum [] ↑ʳ ((suc q ↑ʳ 0F) ↑ˡ sum (c' ∷ B)))
            ■ Fin.toℕ-↑ʳ (sum []) ((suc q ↑ʳ 0F) ↑ˡ sum (c' ∷ B))
            ■ Fin.toℕ-↑ˡ (suc q ↑ʳ 0F) (sum (c' ∷ B))
            ■ Fin.toℕ-↑ʳ (suc q) 0F
            ■ Nat.+-identityʳ (suc q) )))
    bracket-eq : G (Fin.splitAt (suc q + suc b₁) i)
               ≡ G′ (Fin.splitAt (suc q + suc (suc b₁)) (dlwkq [] (suc q) b₁ (c' ∷ B) i))
    bracket-eq with Fin.splitAt (suc q + suc b₁) i in seq
    ... | inj₁ p =
          cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2)
               (Ub-grow' (suc q + suc b₁) (suc q + suc (suc b₁)) (suc q) ccU p j' w'eq h<w
                  (λ e → i≢toℕ (toℕ-i≡p ■ e)) j'eq)
        ■ sym (cong G′ split1)
      where
        j' : 𝔽 (suc q + suc (suc b₁))
        j' = Fin.cast (sym w'eq) (shiftq (suc q) p)
        j'eq : Fin.toℕ j' ≡ Fin.toℕ (shiftq (suc q) p)
        j'eq = Fin.toℕ-cast (sym w'eq) (shiftq (suc q) p)
        toℕ-i≡p : Fin.toℕ i ≡ Fin.toℕ p
        toℕ-i≡p = cong Fin.toℕ (sym (Fin.join-splitAt (suc q + suc b₁) (sum (c' ∷ B)) i)
                              ■ cong (Fin.join (suc q + suc b₁) (sum (c' ∷ B))) seq)
                ■ Fin.toℕ-↑ˡ p (sum (c' ∷ B))
        dsh : Fin.toℕ (dlwkq [] (suc q) b₁ (c' ∷ B) i) ≡ Fin.toℕ (shiftq (suc q) p)
        dsh with Fin.toℕ i Nat.<? suc (suc q)
        ... | yes lt = dlwkq-lo [] (suc q) b₁ (c' ∷ B) i (subst (Fin.toℕ i Nat.<_) (sym sqp1) lt)
                     ■ toℕ-i≡p
                     ■ sym (toℕ-shiftq (suc q) p (subst (Nat._< suc (suc q)) toℕ-i≡p lt))
        ... | no ¬lt = dlwkq-hi [] (suc q) b₁ (c' ∷ B) i (subst (Nat._≤ Fin.toℕ i) (sym sqp1) (Nat.≮⇒≥ ¬lt))
                     ■ cong suc toℕ-i≡p
                     ■ sym (toℕ-shiftq-hi (suc q) p (subst (suc (suc q) Nat.≤_) toℕ-i≡p (Nat.≮⇒≥ ¬lt)))
        split1 : Fin.splitAt (suc q + suc (suc b₁)) (dlwkq [] (suc q) b₁ (c' ∷ B) i) ≡ inj₁ j'
        split1 = splitAt-inj₁-toℕ (suc q + suc (suc b₁)) (dlwkq [] (suc q) b₁ (c' ∷ B) i) j'
                   (dsh ■ sym j'eq)
    ... | inj₂ k = sym (cong G′ split2)
      where
        toℕ-i≡ : Fin.toℕ i ≡ (suc q + suc b₁) + Fin.toℕ k
        toℕ-i≡ = cong Fin.toℕ (sym (Fin.join-splitAt (suc q + suc b₁) (sum (c' ∷ B)) i)
                             ■ cong (Fin.join (suc q + suc b₁) (sum (c' ∷ B))) seq)
               ■ Fin.toℕ-↑ʳ (suc q + suc b₁) k
        bound : suc q + 1 Nat.≤ Fin.toℕ i
        bound = subst (suc q + 1 Nat.≤_) (sym toℕ-i≡)
                  (Nat.≤-trans (Nat.+-monoʳ-≤ (suc q) (Nat.s≤s Nat.z≤n))
                    (Nat.m≤m+n (suc q + suc b₁) (Fin.toℕ k)))
        toℕ-dlwkq≡ : Fin.toℕ (dlwkq [] (suc q) b₁ (c' ∷ B) i) ≡ (suc q + suc (suc b₁)) + Fin.toℕ k
        toℕ-dlwkq≡ = dlwkq-hi [] (suc q) b₁ (c' ∷ B) i bound
                   ■ cong suc toℕ-i≡
                   ■ cong suc (sym (cong (Nat._+ Fin.toℕ k) (Nat.+-suc q (suc b₁))))
        split2 : Fin.splitAt (suc q + suc (suc b₁)) (dlwkq [] (suc q) b₁ (c' ∷ B) i) ≡ inj₂ k
        split2 = splitAt-inj₂-toℕ (suc q + suc (suc b₁)) (dlwkq [] (suc q) b₁ (c' ∷ B) i) k toℕ-dlwkq≡
canonₛ-lwkq (a ∷ []) {N} (e₁ , x , e₂) q b₁ B₂ i i≢
  with canonₛ-lwkq ([]) (` 0F , suc x , wk e₂) q b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum (([]) ++ (q + suc (suc b₁)) ∷ B₂)))))
  where
    sT  = syncs (([]) ++ (q + suc b₁) ∷ B₂)
    sT′ = syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)
    sl   = syncs-lwkq ([]) {q} {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ (q + suc b₁) ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ (q + suc (suc b₁)) ∷ B₂) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (dlwkq ([]) q b₁ B₂ r))
        (rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum (([]) ++ (q + suc b₁) ∷ B₂)) i)
                          ■ cong (Fin.join a (sum (([]) ++ (q + suc b₁) ∷ B₂))) seq
                          ■ cong (a ↑ʳ_) r≡
                          ■ sym (pos-split-gen a ([]) (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) )))
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum (([]) ++ (q + suc (suc b₁)) ∷ B₂)) (dlwkq ([]) q b₁ B₂ r))))
  where
    sT  = syncs (([]) ++ (q + suc b₁) ∷ B₂)
    sT′ = syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)
    sl   = syncs-lwkq ([]) {q} {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ (q + suc b₁) ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ (q + suc (suc b₁)) ∷ B₂) cc-r ]′
canonₛ-lwkq (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) q b₁ B₂ i i≢
  with canonₛ-lwkq (d ∷ B₁″) (` 0F , suc x , wk e₂) q b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)))))
  where
    sT  = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)
    sl   = syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (dlwkq (d ∷ B₁″) q b₁ B₂ r))
        (rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) i)
                          ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂))) seq
                          ■ cong (a ↑ʳ_) r≡
                          ■ sym (pos-split-gen a (d ∷ B₁″) (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) )))
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) (dlwkq (d ∷ B₁″) q b₁ B₂ r))))
  where
    sT  = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)
    sl   = syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂) cc-r ]′
