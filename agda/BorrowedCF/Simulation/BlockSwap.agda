{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.BlockSwap where

-- | The block-swap renaming theory: swapᵣ / assocSwapᵣ identities, their toℕ
--   characterisation (a block rotation on indices), and the composition laws
--   R2 / R2' that drive the φ-binder permutation in BlockPermutation.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

assocSwap-01 : ∀ {m} → assocSwapᵣ 0 1 {m} ≗ idₖ
assocSwap-01 0F      = refl
assocSwap-01 (suc j) =
  cong suc (Fin.cast-is-id _ (Fin.cast _ j) ■ Fin.cast-is-id _ j)

-- Ub applies its continuation once, to the substitution it builds.

swapᵣ-inv : ∀ a b {nn} (x : 𝔽 (a + b + nn)) → swapᵣ b a (swapᵣ a b x) ≡ x
swapᵣ-inv a b {nn} x =
    cong (λ s → Fin.join (a + b) nn (Sum.map₁ (Fin.swap b) s))
         (Fin.splitAt-join (b + a) nn (Sum.map₁ (Fin.swap a) (Fin.splitAt (a + b) x)))
  ■ cong (Fin.join (a + b) nn) (lemma (Fin.splitAt (a + b) x))
  ■ Fin.join-splitAt (a + b) nn x
  where
    lemma : (s : 𝔽 (a + b) ⊎ 𝔽 nn) → Sum.map₁ (Fin.swap b) (Sum.map₁ (Fin.swap a) s) ≡ s
    lemma (inj₁ y) = cong inj₁ (Fin.swap-involutive a y)
    lemma (inj₂ z) = refl

wk*-suc : ∀ {n} k → (weaken* ⦃ Kᵣ ⦄ k ·ₖ weaken* ⦃ Kᵣ ⦄ 1) ≗ weaken* ⦃ Kᵣ ⦄ {n} (suc k)
wk*-suc k i = cong (1 ↑ʳ_) (weaken*~↑ʳ ⦃ Kᵣ ⦄ k i) ■ sym (weaken*~↑ʳ ⦃ Kᵣ ⦄ (suc k) i)

assocSwap-inv : ∀ a b {m} (i : 𝔽 (a + (b + m))) →
                assocSwapᵣ b a {m} (assocSwapᵣ a b {m} i) ≡ i
assocSwap-inv a b {m} i =
    cong (Fin.cast (+-assoc a b m) ∘ swapᵣ b a)
         (Fin.cast-trans (+-assoc b a m) (sym (+-assoc b a m)) _ ■ Fin.cast-is-id _ _)
  ■ cong (Fin.cast (+-assoc a b m)) (swapᵣ-inv a b _)
  ■ (Fin.cast-trans (sym (+-assoc a b m)) (+-assoc a b m) i ■ Fin.cast-is-id _ i)

swapᵣ-0a-toℕ : ∀ a {m} (w : 𝔽 (0 + a + m)) → Fin.toℕ (swapᵣ 0 a w) ≡ Fin.toℕ w
swapᵣ-0a-toℕ a {m} w with Fin.splitAt (0 + a) w in eq
... | inj₁ y = Fin.toℕ-↑ˡ (y Fin.↑ˡ 0) m ■ Fin.toℕ-↑ˡ y 0 ■ sym (Fin.toℕ-↑ˡ y m)
             ■ cong Fin.toℕ (Fin.splitAt⁻¹-↑ˡ eq)
... | inj₂ z = Fin.toℕ-↑ʳ (a + 0) z ■ cong (_+ Fin.toℕ z) (+-identityʳ a)
             ■ sym (Fin.toℕ-↑ʳ (0 + a) z) ■ cong Fin.toℕ (Fin.splitAt⁻¹-↑ʳ eq)

assocSwap-0a : ∀ a {m} → assocSwapᵣ 0 a {m} ≗ idₖ
assocSwap-0a a {m} i = Fin.toℕ-injective
  (Fin.toℕ-cast _ _ ■ swapᵣ-0a-toℕ a _ ■ Fin.toℕ-cast _ _)

R-base-b0 : ∀ b {m} → assocSwapᵣ b 0 {m} ≗ idₖ
R-base-b0 b i = cong (assocSwapᵣ b 0) (sym (assocSwap-0a b i)) ■ assocSwap-inv 0 b i

toℕ-swapᵣ : ∀ a b {m} (w : 𝔽 (a + b + m)) →
  Fin.toℕ (swapᵣ a b w)
  ≡ [ (λ u → [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′ (Fin.splitAt a u))
    , (λ v → b + a + Fin.toℕ v) ]′ (Fin.splitAt (a + b) w)
toℕ-swapᵣ a b {m} w with Fin.splitAt (a + b) w
... | inj₂ v = Fin.toℕ-↑ʳ (b + a) v
... | inj₁ u with Fin.splitAt a u
...   | inj₁ p = Fin.toℕ-↑ˡ (b Fin.↑ʳ p) m ■ Fin.toℕ-↑ʳ b p
...   | inj₂ q = Fin.toℕ-↑ˡ (q Fin.↑ˡ a) m ■ Fin.toℕ-↑ˡ q a

toℕ-reduce≥ : ∀ {m n} (i : 𝔽 (m + n)) (p : m Nat.≤ Fin.toℕ i) →
              Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ m
toℕ-reduce≥ {zero}  i       p = refl
toℕ-reduce≥ {suc m} (suc i) p = toℕ-reduce≥ i (Nat.s≤s⁻¹ p)

toℕ-assoc : ∀ a b {m} (x : 𝔽 (a + (b + m))) →
  Fin.toℕ (assocSwapᵣ a b x)
  ≡ [ (λ u → [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′ (Fin.splitAt a u))
    , (λ v → b + a + Fin.toℕ v) ]′ (Fin.splitAt (a + b) (Fin.cast (sym (+-assoc a b _)) x))
toℕ-assoc a b {m} x =
  Fin.toℕ-cast (+-assoc b a m) _ ■ toℕ-swapᵣ a b (Fin.cast (sym (+-assoc a b m)) x)

toℕ-assoc-lt : ∀ a b {m} (x : 𝔽 (a + (b + m))) → Fin.toℕ x Nat.< a →
               Fin.toℕ (assocSwapᵣ a b x) ≡ b + Fin.toℕ x
toℕ-assoc-lt a b {m} x lt =
    toℕ-assoc a b x
  ■ cong [ (λ u → [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′ (Fin.splitAt a u)) , (λ v → b + a + Fin.toℕ v) ]′
         (Fin.splitAt-< (a + b) (Fin.cast (sym (+-assoc a b m)) x) p1)
  ■ cong [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′
         (Fin.splitAt-< a (Fin.fromℕ< p1) p2)
  ■ cong (b +_) (Fin.toℕ-fromℕ< p2 ■ Fin.toℕ-fromℕ< p1 ■ Fin.toℕ-cast _ x)
  where
    cx≡x : Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x) ≡ Fin.toℕ x
    cx≡x = Fin.toℕ-cast _ x
    p1 : Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x) Nat.< a + b
    p1 = subst (Nat._< a + b) (sym cx≡x) (Nat.<-≤-trans lt (Nat.m≤m+n a b))
    p2 : Fin.toℕ (Fin.fromℕ< p1) Nat.< a
    p2 = subst (Nat._< a) (sym (Fin.toℕ-fromℕ< p1 ■ cx≡x)) lt

toℕ-assoc-mid : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< a + b →
                Fin.toℕ (assocSwapᵣ a b x) ≡ Fin.toℕ x Nat.∸ a
toℕ-assoc-mid a b {m} x ge lt =
    toℕ-assoc a b x
  ■ cong [ (λ u → [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′ (Fin.splitAt a u)) , (λ v → b + a + Fin.toℕ v) ]′
         (Fin.splitAt-< (a + b) (Fin.cast (sym (+-assoc a b m)) x) p1)
  ■ cong [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′
         (Fin.splitAt-≥ a (Fin.fromℕ< p1) p2)
  ■ toℕ-reduce≥ (Fin.fromℕ< p1) p2
  ■ cong (Nat._∸ a) (Fin.toℕ-fromℕ< p1 ■ cx≡x)
  where
    cx≡x : Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x) ≡ Fin.toℕ x
    cx≡x = Fin.toℕ-cast _ x
    p1 : Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x) Nat.< a + b
    p1 = subst (Nat._< a + b) (sym cx≡x) lt
    p2 : a Nat.≤ Fin.toℕ (Fin.fromℕ< p1)
    p2 = subst (a Nat.≤_) (sym (Fin.toℕ-fromℕ< p1 ■ cx≡x)) ge

toℕ-assoc-ge : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a + b Nat.≤ Fin.toℕ x →
               Fin.toℕ (assocSwapᵣ a b x) ≡ Fin.toℕ x
toℕ-assoc-ge a b {m} x geq =
    toℕ-assoc a b x
  ■ cong [ (λ u → [ (λ p → b + Fin.toℕ p) , Fin.toℕ ]′ (Fin.splitAt a u)) , (λ v → b + a + Fin.toℕ v) ]′
         (Fin.splitAt-≥ (a + b) (Fin.cast (sym (+-assoc a b m)) x) p1)
  ■ cong (b + a +_) (toℕ-reduce≥ (Fin.cast (sym (+-assoc a b m)) x) p1 ■ cong (Nat._∸ (a + b)) cx≡x)
  ■ cong (Nat._+ (Fin.toℕ x Nat.∸ (a + b))) (Nat.+-comm b a)
  ■ Nat.m+[n∸m]≡n geq
  where
    cx≡x : Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x) ≡ Fin.toℕ x
    cx≡x = Fin.toℕ-cast _ x
    p1 : a + b Nat.≤ Fin.toℕ (Fin.cast (sym (+-assoc a b m)) x)
    p1 = subst (a + b Nat.≤_) (sym cx≡x) geq

n<n+1 : ∀ n → n Nat.< n + 1
n<n+1 n = subst (n Nat.<_) (Nat.+-comm 1 n) (Nat.n<1+n n)

toℕ-↑ : ∀ {n n′} (ρ : n →ᵣ n′) (w : 𝔽 (suc n)) →
  Fin.toℕ ((ρ ↑) w) ≡ [ (λ _ → 0) , (λ j → suc (Fin.toℕ (ρ j))) ]′ (Fin.splitAt 1 w)
toℕ-↑ ρ 0F      = refl
toℕ-↑ ρ (suc j) = refl

R2 : ∀ b {m} → ((assocSwapᵣ b 1 {m} ↑) ·ₖ assocSwapᵣ 1 1) ≗ assocSwapᵣ (suc b) 1 {m}
R2 b 0F      = Fin.toℕ-injective
  (toℕ-assoc-lt  1 1 {b} 0F (Nat.s≤s Nat.z≤n) ■ sym (toℕ-assoc-lt (suc b) 1 {b} 0F (Nat.s≤s Nat.z≤n)))
R2 b (suc j) with Nat.<-cmp (Fin.toℕ j) b
... | tri< lt _ _ = Fin.toℕ-injective
      (toℕ-assoc-ge 1 1 (suc (assocSwapᵣ b 1 j))
         (subst (2 Nat.≤_) (cong suc (sym inner)) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
       ■ cong suc inner
       ■ sym (toℕ-assoc-lt (suc b) 1 (suc j) (Nat.s≤s lt)))
  where inner = toℕ-assoc-lt b 1 j lt
... | tri≈ _ eq _ = Fin.toℕ-injective (lhs ■ sym rhs)
  where
    inner0 : Fin.toℕ (assocSwapᵣ b 1 j) ≡ 0
    inner0 = toℕ-assoc-mid b 1 j (subst (Nat._≤ Fin.toℕ j) eq Nat.≤-refl)
                                 (subst (Nat._< b + 1) (sym eq) (n<n+1 b))
           ■ cong (Nat._∸ b) eq ■ Nat.n∸n≡0 b
    lhs : Fin.toℕ (assocSwapᵣ 1 1 (suc (assocSwapᵣ b 1 j))) ≡ 0
    lhs = toℕ-assoc-mid 1 1 (suc (assocSwapᵣ b 1 j)) (Nat.s≤s Nat.z≤n)
            (subst (Nat._< 2) (sym (cong suc inner0)) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
          ■ inner0
    rhs : Fin.toℕ (assocSwapᵣ (suc b) 1 (suc j)) ≡ 0
    rhs = toℕ-assoc-mid (suc b) 1 (suc j)
            (subst (suc b Nat.≤_) (cong suc (sym eq)) Nat.≤-refl)
            (subst (Nat._< suc b + 1) (cong suc (sym eq)) (n<n+1 (suc b)))
          ■ cong (Nat._∸ suc b) (cong suc eq) ■ Nat.n∸n≡0 (suc b)
... | tri> _ _ gt = Fin.toℕ-injective
      (toℕ-assoc-ge 1 1 (suc (assocSwapᵣ b 1 j))
         (subst (2 Nat.≤_) (cong suc (sym inner)) (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)))
       ■ cong suc inner
       ■ sym (toℕ-assoc-ge (suc b) 1 (suc j) (Nat.s≤s gtb1)))
  where gtb1 = subst (Nat._≤ Fin.toℕ j) (Nat.+-comm 1 b) gt
        inner = toℕ-assoc-ge b 1 j gtb1

∸-helper : ∀ k b → suc b Nat.≤ k → k Nat.∸ b ≡ suc ((k Nat.∸ 1) Nat.∸ b)
∸-helper k b ssb≤k = Nat.+-∸-assoc 1 ssb≤k ■ cong suc (sym (Nat.∸-+-assoc k 1 b))

R2' : ∀ b a {m} → (assocSwapᵣ b 1 {a + m} ·ₖ (assocSwapᵣ b a {m} ↑)) ≗ assocSwapᵣ b (suc a) {m}
R2' b a i with Nat.<-cmp (Fin.toℕ i) b
... | tri< lt _ _ = Fin.toℕ-injective
      (toℕ-↑ (assocSwapᵣ b a) (assocSwapᵣ b 1 i)
       ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ b a j))) ]′
              (Fin.splitAt-≥ 1 (assocSwapᵣ b 1 i) q1)
       ■ cong suc (toℕ-assoc-lt b a (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) q2 ■ cong (a +_) red≡)
       ■ sym (toℕ-assoc-lt b (suc a) i lt))
  where inner1 = toℕ-assoc-lt b 1 i lt
        q1 : 1 Nat.≤ Fin.toℕ (assocSwapᵣ b 1 i)
        q1 = subst (1 Nat.≤_) (sym inner1) (Nat.s≤s Nat.z≤n)
        red≡ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) ≡ Fin.toℕ i
        red≡ = toℕ-reduce≥ (assocSwapᵣ b 1 i) q1 ■ cong (Nat._∸ 1) inner1
        q2 : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) Nat.< b
        q2 = subst (Nat._< b) (sym red≡) lt
... | tri≈ _ eq _ = Fin.toℕ-injective
      (toℕ-↑ (assocSwapᵣ b a) (assocSwapᵣ b 1 i)
       ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ b a j))) ]′
              (Fin.splitAt-< 1 (assocSwapᵣ b 1 i) q1)
       ■ sym (toℕ-assoc-mid b (suc a) i ge2 lt2 ■ cong (Nat._∸ b) eq ■ Nat.n∸n≡0 b))
  where inner1 = toℕ-assoc-mid b 1 i (subst (Nat._≤ Fin.toℕ i) eq Nat.≤-refl)
                                     (subst (Nat._< b + 1) (sym eq) (n<n+1 b))
        inner1' : Fin.toℕ (assocSwapᵣ b 1 i) ≡ 0
        inner1' = inner1 ■ cong (Nat._∸ b) eq ■ Nat.n∸n≡0 b
        q1 : Fin.toℕ (assocSwapᵣ b 1 i) Nat.< 1
        q1 = subst (Nat._< 1) (sym inner1') (Nat.s≤s Nat.z≤n)
        ge2 : b Nat.≤ Fin.toℕ i
        ge2 = subst (Nat._≤ Fin.toℕ i) eq Nat.≤-refl
        lt2 : Fin.toℕ i Nat.< b + suc a
        lt2 = subst (Nat._< b + suc a) (sym eq)
                (Nat.<-≤-trans (n<n+1 b) (Nat.+-monoʳ-≤ b (Nat.s≤s Nat.z≤n)))
... | tri> _ _ gt with Nat.<-cmp (Fin.toℕ i) (b + suc a)
...   | tri< lt2 _ _ = Fin.toℕ-injective
        (toℕ-↑ (assocSwapᵣ b a) (assocSwapᵣ b 1 i)
         ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ b a j))) ]′
                (Fin.splitAt-≥ 1 (assocSwapᵣ b 1 i) q1)
         ■ cong suc (toℕ-assoc-mid b a (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) q2a q2b ■ cong (Nat._∸ b) red≡)
         ■ sym (toℕ-assoc-mid b (suc a) i (Nat.<⇒≤ gt) lt2 ■ ∸-helper (Fin.toℕ i) b gt))
  where inner1 = toℕ-assoc-ge b 1 i (subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 1 b) gt)
        q1 : 1 Nat.≤ Fin.toℕ (assocSwapᵣ b 1 i)
        q1 = subst (1 Nat.≤_) (sym inner1) (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
        red≡ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) ≡ Fin.toℕ i Nat.∸ 1
        red≡ = toℕ-reduce≥ (assocSwapᵣ b 1 i) q1 ■ cong (Nat._∸ 1) inner1
        q2a : b Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b 1 i) q1)
        q2a = subst (b Nat.≤_) (sym red≡) (Nat.∸-monoˡ-≤ 1 gt)
        q2b : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) Nat.< b + a
        q2b = subst (Nat._< b + a) (sym red≡)
                (Nat.<-≤-trans (Nat.≤-reflexive (Nat.m+[n∸m]≡n (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)))
                               (Nat.s≤s⁻¹ (subst (Fin.toℕ i Nat.<_) (Nat.+-suc b a) lt2)))
...   | tri≈ _ eq2 _ = Fin.toℕ-injective (gecase (Nat.≤-reflexive (sym eq2)))
  where gecase : b + suc a Nat.≤ Fin.toℕ i → _
        gecase ge3 =
            toℕ-↑ (assocSwapᵣ b a) (assocSwapᵣ b 1 i)
          ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ b a j))) ]′
                 (Fin.splitAt-≥ 1 (assocSwapᵣ b 1 i) q1)
          ■ cong suc (toℕ-assoc-ge b a (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) q3 ■ red≡)
          ■ Nat.m+[n∸m]≡n (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
          ■ sym (toℕ-assoc-ge b (suc a) i ge3)
          where inner1 = toℕ-assoc-ge b 1 i (subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 1 b) gt)
                q1 = subst (1 Nat.≤_) (sym inner1) (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
                red≡ = toℕ-reduce≥ (assocSwapᵣ b 1 i) q1 ■ cong (Nat._∸ 1) inner1
                q3 = subst (b + a Nat.≤_) (sym red≡)
                       (Nat.∸-monoˡ-≤ 1 (subst (Nat._≤ Fin.toℕ i) (Nat.+-suc b a) ge3))
...   | tri> _ _ gt2 = Fin.toℕ-injective (gecase (Nat.<⇒≤ gt2))
  where gecase : b + suc a Nat.≤ Fin.toℕ i → _
        gecase ge3 =
            toℕ-↑ (assocSwapᵣ b a) (assocSwapᵣ b 1 i)
          ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ b a j))) ]′
                 (Fin.splitAt-≥ 1 (assocSwapᵣ b 1 i) q1)
          ■ cong suc (toℕ-assoc-ge b a (Fin.reduce≥ (assocSwapᵣ b 1 i) q1) q3 ■ red≡)
          ■ Nat.m+[n∸m]≡n (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
          ■ sym (toℕ-assoc-ge b (suc a) i ge3)
          where inner1 = toℕ-assoc-ge b 1 i (subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 1 b) gt)
                q1 = subst (1 Nat.≤_) (sym inner1) (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
                red≡ = toℕ-reduce≥ (assocSwapᵣ b 1 i) q1 ■ cong (Nat._∸ 1) inner1
                q3 = subst (b + a Nat.≤_) (sym red≡)
                       (Nat.∸-monoˡ-≤ 1 (subst (Nat._≤ Fin.toℕ i) (Nat.+-suc b a) ge3))
