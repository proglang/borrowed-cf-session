module BorrowedCF.Simulation.Support.BlockPerm where

-- | The block-permutation renaming theory (ported, pure Fin/toℕ level):
--   swapᵣ / assocSwapᵣ identities, their toℕ characterisation (a block rotation
--   on indices), and the composition laws R2 / R2' that drive the φ-binder
--   block transpose in Congruence.  Foundation only — no Simulation/* import.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open Nat.Variables
open Fin.Patterns

-- toℕ characterisation of THIS codebase's cast-free assocSwapᵣ:
--   assocSwapᵣ a b {n} = [ (λ x → b ↑ʳ (x ↑ˡ n)) , join ∘ Sum.map₂ (a ↑ʳ_) ∘ splitAt b ]′ ∘ splitAt a

toℕ-reduce≥ : ∀ {m n} (i : 𝔽 (m + n)) (p : m Nat.≤ Fin.toℕ i) →
              Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ m
toℕ-reduce≥ {zero}  i       p = refl
toℕ-reduce≥ {suc m} (suc i) p = toℕ-reduce≥ i (Nat.s≤s⁻¹ p)

toℕ-assoc-lt : ∀ a b {m} (x : 𝔽 (a + (b + m))) → Fin.toℕ x Nat.< a →
               Fin.toℕ (assocSwapᵣ a b x) ≡ b + Fin.toℕ x
toℕ-assoc-lt a b {m} x lt =
    cong (λ s → Fin.toℕ ([ (λ y → b ↑ʳ (y ↑ˡ m))
                          , (λ y → Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (Fin.splitAt b y))) ]′ s))
         (Fin.splitAt-< a x lt)
  ■ Fin.toℕ-↑ʳ b (Fin.fromℕ< lt ↑ˡ m)
  ■ cong (b +_) (Fin.toℕ-↑ˡ (Fin.fromℕ< lt) m ■ Fin.toℕ-fromℕ< lt)

toℕ-assoc-mid : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< a + b →
                Fin.toℕ (assocSwapᵣ a b x) ≡ Fin.toℕ x Nat.∸ a
toℕ-assoc-mid a b {m} x ge lt =
    cong (λ s → Fin.toℕ ([ (λ y → b ↑ʳ (y ↑ˡ m))
                          , (λ y → Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (Fin.splitAt b y))) ]′ s))
         (Fin.splitAt-≥ a x ge)
  ■ cong (λ s → Fin.toℕ (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) s)))
         (Fin.splitAt-< b (Fin.reduce≥ x ge) p2)
  ■ Fin.toℕ-↑ˡ (Fin.fromℕ< p2) (a + m)
  ■ Fin.toℕ-fromℕ< p2
  ■ toℕ-reduce≥ x ge
  where
    red≡ : Fin.toℕ (Fin.reduce≥ x ge) ≡ Fin.toℕ x Nat.∸ a
    red≡ = toℕ-reduce≥ x ge
    p2 : Fin.toℕ (Fin.reduce≥ x ge) Nat.< b
    p2 = subst (Nat._< b) (sym red≡)
           (Nat.+-cancelˡ-< a (Fin.toℕ x Nat.∸ a) b
             (subst (Nat._< a + b) (sym (Nat.m+[n∸m]≡n ge)) lt))

toℕ-assoc-ge : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a + b Nat.≤ Fin.toℕ x →
               Fin.toℕ (assocSwapᵣ a b x) ≡ Fin.toℕ x
toℕ-assoc-ge a b {m} x geq =
    cong (λ s → Fin.toℕ ([ (λ y → b ↑ʳ (y ↑ˡ m))
                          , (λ y → Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (Fin.splitAt b y))) ]′ s))
         (Fin.splitAt-≥ a x a≤x)
  ■ cong (λ s → Fin.toℕ (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) s)))
         (Fin.splitAt-≥ b (Fin.reduce≥ x a≤x) p2)
  ■ Fin.toℕ-↑ʳ b (a ↑ʳ Fin.reduce≥ (Fin.reduce≥ x a≤x) p2)
  ■ cong (b +_) (Fin.toℕ-↑ʳ a (Fin.reduce≥ (Fin.reduce≥ x a≤x) p2))
  ■ cong (λ z → b + (a + z)) (toℕ-reduce≥ (Fin.reduce≥ x a≤x) p2 ■ cong (Nat._∸ b) red≡)
  ■ eqn
  where
    a≤x : a Nat.≤ Fin.toℕ x
    a≤x = Nat.≤-trans (Nat.m≤m+n a b) geq
    red≡ : Fin.toℕ (Fin.reduce≥ x a≤x) ≡ Fin.toℕ x Nat.∸ a
    red≡ = toℕ-reduce≥ x a≤x
    p2 : b Nat.≤ Fin.toℕ (Fin.reduce≥ x a≤x)
    p2 = subst (b Nat.≤_) (sym red≡) (Nat.≤-trans (Nat.≤-reflexive (sym (Nat.m+n∸m≡n a b)))
           (Nat.∸-monoˡ-≤ a geq))
    eqn : b + (a + (Fin.toℕ x Nat.∸ a Nat.∸ b)) ≡ Fin.toℕ x
    eqn = cong (λ z → b + (a + z)) (Nat.∸-+-assoc (Fin.toℕ x) a b)
        ■ sym (Nat.+-assoc b a (Fin.toℕ x Nat.∸ (a + b)))
        ■ cong (Nat._+ (Fin.toℕ x Nat.∸ (a + b))) (Nat.+-comm b a)
        ■ Nat.m+[n∸m]≡n geq

assocSwap-0a : ∀ a {m} → assocSwapᵣ 0 a {m} ≗ idₖ
assocSwap-0a a {m} i with Nat.<-cmp (Fin.toℕ i) a
... | tri< lt _ _ = Fin.toℕ-injective (toℕ-assoc-mid 0 a i Nat.z≤n lt)
... | tri≈ _ eq _ = Fin.toℕ-injective (toℕ-assoc-ge 0 a i (Nat.≤-reflexive (sym eq)))
... | tri> _ _ gt = Fin.toℕ-injective (toℕ-assoc-ge 0 a i (Nat.<⇒≤ gt))

assocSwap-01 : ∀ {m} → assocSwapᵣ 0 1 {m} ≗ idₖ
assocSwap-01 = assocSwap-0a 1

assocSwap-b0 : ∀ b {m} → assocSwapᵣ b 0 {m} ≗ idₖ
assocSwap-b0 b {m} i with Nat.<-cmp (Fin.toℕ i) b
... | tri< lt _ _ = Fin.toℕ-injective (toℕ-assoc-lt b 0 i lt)
... | tri≈ _ eq _ = Fin.toℕ-injective (toℕ-assoc-ge b 0 i
                      (subst (Nat._≤ Fin.toℕ i) (sym (Nat.+-identityʳ b)) (Nat.≤-reflexive (sym eq))))
... | tri> _ _ gt = Fin.toℕ-injective (toℕ-assoc-ge b 0 i
                      (subst (Nat._≤ Fin.toℕ i) (sym (Nat.+-identityʳ b)) (Nat.<⇒≤ gt)))

R-base-b0 : ∀ b {m} → assocSwapᵣ b 0 {m} ≗ idₖ
R-base-b0 = assocSwap-b0

-- assocSwapᵣ is involutive when composed with its block-swapped inverse.
private
  invol-abge : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a + b Nat.≤ Fin.toℕ x →
               (assocSwapᵣ a b {m} ·ₖ assocSwapᵣ b a {m}) x ≡ x
  invol-abge a b {m} x ab≤ = Fin.toℕ-injective
    ( toℕ-assoc-ge b a (assocSwapᵣ a b x)
        (subst (b + a Nat.≤_) (sym as) (subst (Nat._≤ Fin.toℕ x) (Nat.+-comm a b) ab≤))
    ■ as )
    where as = toℕ-assoc-ge a b x ab≤
  invol-lo : ∀ a b {m} (x : 𝔽 (a + (b + m))) → a Nat.≤ Fin.toℕ x →
             (assocSwapᵣ a b {m} ·ₖ assocSwapᵣ b a {m}) x ≡ x
  invol-lo a b {m} x a≤ with Nat.<-cmp (Fin.toℕ x) (a + b)
  ... | tri< lt2 _ _ = Fin.toℕ-injective
        ( toℕ-assoc-lt b a (assocSwapᵣ a b x) (subst (Nat._< b) (sym as) lt')
        ■ cong (a +_) as ■ Nat.+-comm a (Fin.toℕ x Nat.∸ a) ■ Nat.m∸n+n≡m a≤ )
    where as = toℕ-assoc-mid a b x a≤ lt2
          lt' : Fin.toℕ x Nat.∸ a Nat.< b
          lt' = Nat.+-cancelˡ-< a (Fin.toℕ x Nat.∸ a) b (subst (Nat._< a + b) (sym (Nat.m+[n∸m]≡n a≤)) lt2)
  ... | tri≈ _ eq2 _ = invol-abge a b x (Nat.≤-reflexive (sym eq2))
  ... | tri> _ _ gt2 = invol-abge a b x (Nat.<⇒≤ gt2)

assocSwap-invol : ∀ a b {m} → (assocSwapᵣ a b {m} ·ₖ assocSwapᵣ b a {m}) ≗ idₖ
assocSwap-invol a b {m} x with Nat.<-cmp (Fin.toℕ x) a
... | tri< lt _ _ = Fin.toℕ-injective
      ( toℕ-assoc-mid b a (assocSwapᵣ a b x)
          (subst (b Nat.≤_) (sym as) (Nat.m≤m+n b (Fin.toℕ x)))
          (subst (Nat._< b + a) (sym as) (Nat.+-monoʳ-< b lt))
      ■ cong (Nat._∸ b) as ■ Nat.m+n∸m≡n b (Fin.toℕ x) )
  where as = toℕ-assoc-lt a b x lt
... | tri≈ _ eq _ = invol-lo a b x (Nat.≤-reflexive (sym eq))
... | tri> _ _ gt = invol-lo a b x (Nat.<⇒≤ gt)

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


-- application lemma for ↑* on renamings (re-proved locally; foundation-only).
↑*-split : ∀ {m m′} (ρ : m →ᵣ m′) (len : ℕ) (i : 𝔽 (len + m)) →
           (ρ ↑* len) i ≡ [ (_↑ˡ m′) , (λ k → len ↑ʳ ρ k) ]′ (Fin.splitAt len i)
↑*-split ρ zero    i       = refl
↑*-split ρ (suc len) 0F    = refl
↑*-split {m} {m′} ρ (suc len) (suc i) =
  cong suc (↑*-split ρ len i) ■ helper (Fin.splitAt len i)
  where
    helper : (s : 𝔽 len ⊎ 𝔽 m) →
             suc ([ (_↑ˡ m′) , (λ k → len ↑ʳ ρ k) ]′ s)
             ≡ [ (_↑ˡ m′) , (λ k → suc len ↑ʳ ρ k) ]′ (Sum.map₁ suc s)
    helper (inj₁ y) = refl
    helper (inj₂ z) = refl

toℕ-as11↑*-lt : ∀ k {m} (i : 𝔽 (k + suc (suc m))) → Fin.toℕ i Nat.< k →
                Fin.toℕ ((assocSwapᵣ 1 1 {m} ↑* k) i) ≡ Fin.toℕ i
toℕ-as11↑*-lt k {m} i lt =
    cong Fin.toℕ (↑*-split (assocSwapᵣ 1 1 {m}) k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ assocSwapᵣ 1 1 j) ]′ s)) (Fin.splitAt-< k i lt)
  ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) _ ■ Fin.toℕ-fromℕ< lt

toℕ-as11↑*-ge : ∀ k {m} (i : 𝔽 (k + suc (suc m))) (p : k Nat.≤ Fin.toℕ i) →
                Fin.toℕ ((assocSwapᵣ 1 1 {m} ↑* k) i)
                ≡ k + Fin.toℕ (assocSwapᵣ 1 1 {m} (Fin.reduce≥ i p))
toℕ-as11↑*-ge k {m} i p =
    cong Fin.toℕ (↑*-split (assocSwapᵣ 1 1 {m}) k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ assocSwapᵣ 1 1 j) ]′ s)) (Fin.splitAt-≥ k i p)
  ■ Fin.toℕ-↑ʳ k (assocSwapᵣ 1 1 (Fin.reduce≥ i p))

toℕ-R3 : ∀ k {m} (i : 𝔽 (k + suc (suc m))) →
  Fin.toℕ (((assocSwapᵣ 1 1 {m} ↑* k) ·ₖ assocSwapᵣ k 1 {suc m}) i)
  ≡ Fin.toℕ (assocSwapᵣ (suc k) 1 {m} (Fin.cast (+-suc k (suc m)) i))
toℕ-R3 k {m} i with Nat.<-cmp (Fin.toℕ i) k
... | tri< lt _ _ =
      toℕ-assoc-lt k 1 ((assocSwapᵣ 1 1 ↑* k) i) (subst (Nat._< k) (sym inner) lt)
    ■ cong (1 +_) inner
    ■ sym (toℕ-assoc-lt (suc k) 1 (Fin.cast (+-suc k (suc m)) i)
             (subst (Nat._< suc k) (sym ci) (Nat.s≤s (Nat.<⇒≤ lt))) ■ cong (1 +_) ci)
  where inner = toℕ-as11↑*-lt k i lt
        ci = Fin.toℕ-cast (+-suc k (suc m)) i
... | tri≈ _ eq _ = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (suc m)) i
    red≡ : Fin.toℕ (Fin.reduce≥ i (Nat.≤-reflexive (sym eq))) ≡ 0
    red≡ = toℕ-reduce≥ i (Nat.≤-reflexive (sym eq)) ■ cong (Nat._∸ k) eq ■ Nat.n∸n≡0 k
    swap0 : Fin.toℕ (assocSwapᵣ 1 1 {m} (Fin.reduce≥ i (Nat.≤-reflexive (sym eq)))) ≡ 1
    swap0 = toℕ-assoc-lt 1 1 _ (subst (Nat._< 1) (sym red≡) (Nat.s≤s Nat.z≤n)) ■ cong (1 +_) red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 1 ↑* k) i) ≡ suc k
    ge = toℕ-as11↑*-ge k i (Nat.≤-reflexive (sym eq)) ■ cong (k +_) swap0 ■ Nat.+-comm k 1
    lhs : Fin.toℕ (assocSwapᵣ k 1 ((assocSwapᵣ 1 1 ↑* k) i)) ≡ suc k
    lhs = toℕ-assoc-ge k 1 _ (subst (k + 1 Nat.≤_) (sym ge) (Nat.≤-reflexive (Nat.+-comm k 1))) ■ ge
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 1 (Fin.cast (+-suc k (suc m)) i)) ≡ suc k
    rhs = toℕ-assoc-lt (suc k) 1 _ (subst (Nat._< suc k) (sym (ci ■ eq)) (Nat.n<1+n k)) ■ cong (1 +_) (ci ■ eq)
... | tri> _ _ gt with Nat.<-cmp (Fin.toℕ i) (suc k)
...   | tri< lt2 _ _ = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans gt (Nat.s≤s⁻¹ lt2)))
...   | tri≈ _ eq2 _ = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (suc m)) i
    p : k Nat.≤ Fin.toℕ i
    p = Nat.<⇒≤ gt
    red≡ : Fin.toℕ (Fin.reduce≥ i p) ≡ 1
    red≡ = toℕ-reduce≥ i p ■ cong (Nat._∸ k) eq2 ■ cong (Nat._∸ k) (Nat.+-comm 1 k) ■ Nat.m+n∸m≡n k 1
    swap1 : Fin.toℕ (assocSwapᵣ 1 1 {m} (Fin.reduce≥ i p)) ≡ 0
    swap1 = toℕ-assoc-mid 1 1 _ (subst (1 Nat.≤_) (sym red≡) Nat.≤-refl)
              (subst (Nat._< 2) (sym red≡) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
          ■ cong (Nat._∸ 1) red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 1 ↑* k) i) ≡ k
    ge = toℕ-as11↑*-ge k i p ■ cong (k +_) swap1 ■ Nat.+-identityʳ k
    lhs : Fin.toℕ (assocSwapᵣ k 1 ((assocSwapᵣ 1 1 ↑* k) i)) ≡ 0
    lhs = toℕ-assoc-mid k 1 _ (subst (k Nat.≤_) (sym ge) Nat.≤-refl)
            (subst (Nat._< k + 1) (sym ge) (subst (k Nat.<_) (Nat.+-comm 1 k) (Nat.n<1+n k)))
        ■ cong (Nat._∸ k) ge ■ Nat.n∸n≡0 k
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 1 (Fin.cast (+-suc k (suc m)) i)) ≡ 0
    rhs = toℕ-assoc-mid (suc k) 1 _ (Nat.≤-reflexive (sym (ci ■ eq2)))
            (subst (Nat._< suc k + 1) (sym (ci ■ eq2)) (subst (suc k Nat.<_) (Nat.+-comm 1 (suc k)) (Nat.n<1+n (suc k))))
        ■ cong (Nat._∸ suc k) (ci ■ eq2) ■ Nat.n∸n≡0 (suc k)
...   | tri> _ _ gt2 = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (suc m)) i
    p : k Nat.≤ Fin.toℕ i
    p = Nat.<⇒≤ (Nat.<-trans (Nat.n<1+n k) gt2)
    red≡ : Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ k
    red≡ = toℕ-reduce≥ i p
    sucred : 2 Nat.≤ Fin.toℕ (Fin.reduce≥ i p)
    sucred = subst (2 Nat.≤_) (sym red≡)
               (subst (Nat._≤ Fin.toℕ i Nat.∸ k) (Nat.m+n∸m≡n k 2)
                 (Nat.∸-monoˡ-≤ k (subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 2 k) gt2)))
    swapid : Fin.toℕ (assocSwapᵣ 1 1 {m} (Fin.reduce≥ i p)) ≡ Fin.toℕ i Nat.∸ k
    swapid = toℕ-assoc-ge 1 1 _ sucred ■ red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 1 ↑* k) i) ≡ Fin.toℕ i
    ge = toℕ-as11↑*-ge k i p ■ cong (k +_) swapid ■ Nat.m+[n∸m]≡n p
    lhs : Fin.toℕ (assocSwapᵣ k 1 ((assocSwapᵣ 1 1 ↑* k) i)) ≡ Fin.toℕ i
    lhs = toℕ-assoc-ge k 1 _ (subst (k + 1 Nat.≤_) (sym ge)
            (subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 1 k) (Nat.<-trans (Nat.n<1+n k) gt2))) ■ ge
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 1 (Fin.cast (+-suc k (suc m)) i)) ≡ Fin.toℕ i
    rhs = toℕ-assoc-ge (suc k) 1 _ (subst (Nat._≤ Fin.toℕ (Fin.cast (+-suc k (suc m)) i)) (Nat.+-comm 1 (suc k))
            (subst (suc (suc k) Nat.≤_) (sym ci) gt2)) ■ ci

-- toℕ of an arbitrary renaming lifted ↑* k, on a high index (≥ k).
toℕ-↑*-ge : ∀ {m m′} (ρ : m →ᵣ m′) k (i : 𝔽 (k + m)) (q : k Nat.≤ Fin.toℕ i) →
            Fin.toℕ ((ρ ↑* k) i) ≡ k + Fin.toℕ (ρ (Fin.reduce≥ i q))
toℕ-↑*-ge ρ k i q =
    cong Fin.toℕ (↑*-split ρ k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ ρ j) ]′ s)) (Fin.splitAt-≥ k i q)
  ■ Fin.toℕ-↑ʳ k (ρ (Fin.reduce≥ i q))

-- toℕ of an arbitrary renaming lifted ↑* k, on a low index (< k): identity.
toℕ-↑*-lt : ∀ {m m′} (ρ : m →ᵣ m′) k (i : 𝔽 (k + m)) → Fin.toℕ i Nat.< k →
            Fin.toℕ ((ρ ↑* k) i) ≡ Fin.toℕ i
toℕ-↑*-lt ρ k i lt =
    cong Fin.toℕ (↑*-split ρ k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ ρ j) ]′ s)) (Fin.splitAt-< k i lt)
  ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) _ ■ Fin.toℕ-fromℕ< lt

-- width-2 analogue of toℕ-R3 (moving a ν binder, width 2, past k φ binders).
toℕ-R3₂ : ∀ k {m} (i : 𝔽 (k + (2 + suc m))) →
  Fin.toℕ (((assocSwapᵣ 1 2 {m} ↑* k) ·ₖ assocSwapᵣ k 2 {suc m}) i)
  ≡ Fin.toℕ (assocSwapᵣ (suc k) 2 {m} (Fin.cast (+-suc k (2 + m)) i))
toℕ-R3₂ k {m} i with Nat.<-cmp (Fin.toℕ i) k
... | tri< lt _ _ =
      toℕ-assoc-lt k 2 ((assocSwapᵣ 1 2 ↑* k) i) (subst (Nat._< k) (sym inner) lt)
    ■ cong (2 +_) inner
    ■ sym (toℕ-assoc-lt (suc k) 2 (Fin.cast (+-suc k (2 + m)) i)
             (subst (Nat._< suc k) (sym ci) (Nat.s≤s (Nat.<⇒≤ lt))) ■ cong (2 +_) ci)
  where inner = toℕ-↑*-lt (assocSwapᵣ 1 2 {m}) k i lt
        ci = Fin.toℕ-cast (+-suc k (2 + m)) i
... | tri≈ _ eq _ = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (2 + m)) i
    pk = Nat.≤-reflexive (sym eq)
    red≡ : Fin.toℕ (Fin.reduce≥ i pk) ≡ 0
    red≡ = toℕ-reduce≥ i pk ■ cong (Nat._∸ k) eq ■ Nat.n∸n≡0 k
    swap0 : Fin.toℕ (assocSwapᵣ 1 2 {m} (Fin.reduce≥ i pk)) ≡ 2
    swap0 = toℕ-assoc-lt 1 2 _ (subst (Nat._< 1) (sym red≡) (Nat.s≤s Nat.z≤n)) ■ cong (2 +_) red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 2 ↑* k) i) ≡ k + 2
    ge = toℕ-↑*-ge (assocSwapᵣ 1 2 {m}) k i pk ■ cong (k +_) swap0
    lhs : Fin.toℕ (assocSwapᵣ k 2 ((assocSwapᵣ 1 2 ↑* k) i)) ≡ 2 + k
    lhs = toℕ-assoc-ge k 2 _ (subst (k + 2 Nat.≤_) (sym ge) Nat.≤-refl) ■ ge ■ Nat.+-comm k 2
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 2 (Fin.cast (+-suc k (2 + m)) i)) ≡ 2 + k
    rhs = toℕ-assoc-lt (suc k) 2 _ (subst (Nat._< suc k) (sym (ci ■ eq)) (Nat.n<1+n k)) ■ cong (2 +_) (ci ■ eq)
... | tri> _ _ gt with Nat.<-cmp (Fin.toℕ i) (suc k)
...   | tri< lt2 _ _ = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans gt (Nat.s≤s⁻¹ lt2)))
...   | tri≈ _ eq2 _ = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (2 + m)) i
    p = Nat.<⇒≤ gt
    red≡ : Fin.toℕ (Fin.reduce≥ i p) ≡ 1
    red≡ = toℕ-reduce≥ i p ■ cong (Nat._∸ k) eq2 ■ cong (Nat._∸ k) (Nat.+-comm 1 k) ■ Nat.m+n∸m≡n k 1
    swap1 : Fin.toℕ (assocSwapᵣ 1 2 {m} (Fin.reduce≥ i p)) ≡ 0
    swap1 = toℕ-assoc-mid 1 2 _ (subst (1 Nat.≤_) (sym red≡) Nat.≤-refl)
              (subst (Nat._< 3) (sym red≡) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
          ■ cong (Nat._∸ 1) red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 2 ↑* k) i) ≡ k
    ge = toℕ-↑*-ge (assocSwapᵣ 1 2 {m}) k i p ■ cong (k +_) swap1 ■ Nat.+-identityʳ k
    lhs : Fin.toℕ (assocSwapᵣ k 2 ((assocSwapᵣ 1 2 ↑* k) i)) ≡ 0
    lhs = toℕ-assoc-mid k 2 _ (subst (k Nat.≤_) (sym ge) Nat.≤-refl)
            (subst (Nat._< k + 2) (sym ge) (Nat.m<m+n k {2} (Nat.s≤s Nat.z≤n)))
        ■ cong (Nat._∸ k) ge ■ Nat.n∸n≡0 k
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 2 (Fin.cast (+-suc k (2 + m)) i)) ≡ 0
    rhs = toℕ-assoc-mid (suc k) 2 _ (Nat.≤-reflexive (sym (ci ■ eq2)))
            (subst (Nat._< suc k + 2) (sym (ci ■ eq2)) (Nat.m<m+n (suc k) {2} (Nat.s≤s Nat.z≤n)))
        ■ cong (Nat._∸ suc k) (ci ■ eq2) ■ Nat.n∸n≡0 (suc k)
...   | tri> _ _ gt2 with Nat.<-cmp (Fin.toℕ i) (suc (suc k))
...     | tri< lt3 _ _ = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans gt2 (Nat.s≤s⁻¹ lt3)))
...     | tri≈ _ eq3 _ = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (2 + m)) i
    p = Nat.<⇒≤ (Nat.<-trans (Nat.n<1+n k) gt2)
    red≡ : Fin.toℕ (Fin.reduce≥ i p) ≡ 2
    red≡ = toℕ-reduce≥ i p ■ cong (Nat._∸ k) eq3 ■ cong (Nat._∸ k) (Nat.+-comm 2 k) ■ Nat.m+n∸m≡n k 2
    swap2 : Fin.toℕ (assocSwapᵣ 1 2 {m} (Fin.reduce≥ i p)) ≡ 1
    swap2 = toℕ-assoc-mid 1 2 _ (subst (1 Nat.≤_) (sym red≡) (Nat.s≤s Nat.z≤n))
              (subst (Nat._< 3) (sym red≡) (Nat.s≤s (Nat.s≤s (Nat.s≤s Nat.z≤n))))
          ■ cong (Nat._∸ 1) red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 2 ↑* k) i) ≡ suc k
    ge = toℕ-↑*-ge (assocSwapᵣ 1 2 {m}) k i p ■ cong (k +_) swap2 ■ Nat.+-comm k 1
    lhs : Fin.toℕ (assocSwapᵣ k 2 ((assocSwapᵣ 1 2 ↑* k) i)) ≡ 1
    lhs = toℕ-assoc-mid k 2 _ (subst (k Nat.≤_) (sym ge) (Nat.n≤1+n k))
            (subst (Nat._< k + 2) (sym ge) (subst (suc k Nat.<_) (Nat.+-comm 2 k) (Nat.s≤s (Nat.n<1+n k))))
        ■ cong (Nat._∸ k) ge ■ cong (Nat._∸ k) (Nat.+-comm 1 k) ■ Nat.m+n∸m≡n k 1
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 2 (Fin.cast (+-suc k (2 + m)) i)) ≡ 1
    rhs = toℕ-assoc-mid (suc k) 2 _ (subst (suc k Nat.≤_) (sym (ci ■ eq3)) (Nat.n≤1+n (suc k)))
            (subst (Nat._< suc k + 2) (sym (ci ■ eq3)) (subst (suc (suc k) Nat.<_) (Nat.+-comm 2 (suc k)) (Nat.s≤s (Nat.n<1+n (suc k)))))
        ■ cong (Nat._∸ suc k) (ci ■ eq3) ■ cong (Nat._∸ suc k) (Nat.+-comm 1 (suc k)) ■ Nat.m+n∸m≡n (suc k) 1
...     | tri> _ _ gt3 = lhs ■ sym rhs
  where
    ci = Fin.toℕ-cast (+-suc k (2 + m)) i
    hi : 3 + k Nat.≤ Fin.toℕ i
    hi = gt3
    hi3 : k + 3 Nat.≤ Fin.toℕ i
    hi3 = subst (Nat._≤ Fin.toℕ i) (Nat.+-comm 3 k) hi
    p : k Nat.≤ Fin.toℕ i
    p = Nat.≤-trans (Nat.m≤n+m k 3) hi
    red≡ : Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ k
    red≡ = toℕ-reduce≥ i p
    red≥3 : 3 Nat.≤ Fin.toℕ (Fin.reduce≥ i p)
    red≥3 = subst (3 Nat.≤_) (sym red≡)
              (subst (Nat._≤ Fin.toℕ i Nat.∸ k) (Nat.m+n∸m≡n k 3) (Nat.∸-monoˡ-≤ k hi3))
    swapid : Fin.toℕ (assocSwapᵣ 1 2 {m} (Fin.reduce≥ i p)) ≡ Fin.toℕ i Nat.∸ k
    swapid = toℕ-assoc-ge 1 2 _ red≥3 ■ red≡
    ge : Fin.toℕ ((assocSwapᵣ 1 2 ↑* k) i) ≡ Fin.toℕ i
    ge = toℕ-↑*-ge (assocSwapᵣ 1 2 {m}) k i p ■ cong (k +_) swapid ■ Nat.m+[n∸m]≡n p
    lhs : Fin.toℕ (assocSwapᵣ k 2 ((assocSwapᵣ 1 2 ↑* k) i)) ≡ Fin.toℕ i
    lhs = toℕ-assoc-ge k 2 _ (subst (k + 2 Nat.≤_) (sym ge) (Nat.≤-trans (Nat.+-monoʳ-≤ k (Nat.n≤1+n 2)) hi3)) ■ ge
    rhs : Fin.toℕ (assocSwapᵣ (suc k) 2 (Fin.cast (+-suc k (2 + m)) i)) ≡ Fin.toℕ i
    rhs = toℕ-assoc-ge (suc k) 2 _ (subst (suc k + 2 Nat.≤_) (sym ci)
            (subst (Nat._≤ Fin.toℕ i) (Nat.+-suc k 2) hi3)) ■ ci

-- toℕ of the lifted assocSwapᵣ b 1 over k inert binders.
toℕ-asb1↑*-lt : ∀ k b {m} (i : 𝔽 (k + (b + suc m))) → Fin.toℕ i Nat.< k →
                Fin.toℕ ((assocSwapᵣ b 1 {m} ↑* k) i) ≡ Fin.toℕ i
toℕ-asb1↑*-lt k b {m} i lt =
    cong Fin.toℕ (↑*-split (assocSwapᵣ b 1 {m}) k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ assocSwapᵣ b 1 j) ]′ s)) (Fin.splitAt-< k i lt)
  ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) _ ■ Fin.toℕ-fromℕ< lt

toℕ-asb1↑*-ge : ∀ k b {m} (i : 𝔽 (k + (b + suc m))) (p : k Nat.≤ Fin.toℕ i) →
                Fin.toℕ ((assocSwapᵣ b 1 {m} ↑* k) i)
                ≡ k + Fin.toℕ (assocSwapᵣ b 1 {m} (Fin.reduce≥ i p))
toℕ-asb1↑*-ge k b {m} i p =
    cong Fin.toℕ (↑*-split (assocSwapᵣ b 1 {m}) k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ assocSwapᵣ b 1 j) ]′ s)) (Fin.splitAt-≥ k i p)
  ■ Fin.toℕ-↑ʳ k (assocSwapᵣ b 1 (Fin.reduce≥ i p))

private
  -- region A: toℕ i < b
  R4-A : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) → Fin.toℕ i Nat.< b →
         Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i) ≡ suc (k + Fin.toℕ i)
  R4-A b k {m} i lt =
      toℕ-asb1↑*-ge k b (assocSwapᵣ b k i) kj ■ cong (k +_) inner ■ Nat.+-suc k (Fin.toℕ i)
    where
      jt = toℕ-assoc-lt b k i lt
      kj : k Nat.≤ Fin.toℕ (assocSwapᵣ b k {suc m} i)
      kj = subst (k Nat.≤_) (sym jt) (Nat.m≤m+n k (Fin.toℕ i))
      red : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b k i) kj) ≡ Fin.toℕ i
      red = toℕ-reduce≥ (assocSwapᵣ b k i) kj ■ cong (Nat._∸ k) jt ■ Nat.m+n∸m≡n k (Fin.toℕ i)
      inner : Fin.toℕ (assocSwapᵣ b 1 {m} (Fin.reduce≥ (assocSwapᵣ b k i) kj)) ≡ suc (Fin.toℕ i)
      inner = toℕ-assoc-lt b 1 _ (subst (Nat._< b) (sym red) lt) ■ cong (1 +_) red

  -- region B: b ≤ toℕ i < b+k
  R4-B : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) → b Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< b + k →
         Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i) ≡ Fin.toℕ i Nat.∸ b
  R4-B b k {m} i bge ltk = toℕ-asb1↑*-lt k b (assocSwapᵣ b k i) jb ■ jt
    where
      jt : Fin.toℕ (assocSwapᵣ b k {suc m} i) ≡ Fin.toℕ i Nat.∸ b
      jt = toℕ-assoc-mid b k i bge ltk
      jb : Fin.toℕ (assocSwapᵣ b k {suc m} i) Nat.< k
      jb = subst (Nat._< k) (sym jt) (Nat.+-cancelˡ-< b (Fin.toℕ i Nat.∸ b) k
             (subst (Nat._< b + k) (sym (Nat.m+[n∸m]≡n bge)) ltk))

  -- region C0: toℕ i = b+k
  R4-C0 : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) → Fin.toℕ i ≡ b + k →
          Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i) ≡ k
  R4-C0 b k {m} i eqk =
      toℕ-asb1↑*-ge k b (assocSwapᵣ b k i) kj ■ cong (k +_) inner ■ Nat.+-identityʳ k
    where
      jt : Fin.toℕ (assocSwapᵣ b k {suc m} i) ≡ Fin.toℕ i
      jt = toℕ-assoc-ge b k i (Nat.≤-reflexive (sym eqk))
      kj : k Nat.≤ Fin.toℕ (assocSwapᵣ b k {suc m} i)
      kj = subst (k Nat.≤_) (sym jt) (subst (k Nat.≤_) (sym eqk) (Nat.m≤n+m k b))
      red : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b k i) kj) ≡ b
      red = toℕ-reduce≥ (assocSwapᵣ b k i) kj ■ cong (Nat._∸ k) jt ■ cong (Nat._∸ k) eqk
          ■ cong (Nat._∸ k) (Nat.+-comm b k) ■ Nat.m+n∸m≡n k b
      inner : Fin.toℕ (assocSwapᵣ b 1 {m} (Fin.reduce≥ (assocSwapᵣ b k i) kj)) ≡ 0
      inner = toℕ-assoc-mid b 1 _ (subst (b Nat.≤_) (sym red) Nat.≤-refl)
                (subst (Nat._< b + 1) (sym red) (n<n+1 b))
            ■ cong (Nat._∸ b) red ■ Nat.n∸n≡0 b

  -- region C+: b+k < toℕ i
  R4-C+ : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) → b + k Nat.< Fin.toℕ i →
          Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i) ≡ Fin.toℕ i
  R4-C+ b k {m} i gtk =
      toℕ-asb1↑*-ge k b (assocSwapᵣ b k i) kj ■ cong (k +_) inner
    ■ Nat.m+[n∸m]≡n (subst (k Nat.≤_) jt kj)
    where
      jt : Fin.toℕ (assocSwapᵣ b k {suc m} i) ≡ Fin.toℕ i
      jt = toℕ-assoc-ge b k i (Nat.<⇒≤ gtk)
      kj : k Nat.≤ Fin.toℕ (assocSwapᵣ b k {suc m} i)
      kj = subst (k Nat.≤_) (sym jt) (Nat.≤-trans (Nat.m≤n+m k b) (Nat.<⇒≤ gtk))
      redk : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b k i) kj) ≡ Fin.toℕ i Nat.∸ k
      redk = toℕ-reduce≥ (assocSwapᵣ b k i) kj ■ cong (Nat._∸ k) jt
      inner : Fin.toℕ (assocSwapᵣ b 1 {m} (Fin.reduce≥ (assocSwapᵣ b k i) kj)) ≡ Fin.toℕ i Nat.∸ k
      inner = toℕ-assoc-ge b 1 _ rgeb ■ redk
        where
          rgeb : b + 1 Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ b k i) kj)
          rgeb = subst (b + 1 Nat.≤_) (sym redk)
                   (subst (Nat._≤ Fin.toℕ i Nat.∸ k) eqq (Nat.∸-monoˡ-≤ k gtk))
            where
              eqq : suc (b + k) Nat.∸ k ≡ b + 1
              eqq = cong (Nat._∸ k) (Nat.+-comm (suc b) k) ■ Nat.m+n∸m≡n k (suc b) ■ Nat.+-comm 1 b

  -- helper for the t < b+k region (sub-splits on t vs b internally)
  R4-ltbk : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) → Fin.toℕ i Nat.< b + k →
            Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i)
            ≡ Fin.toℕ (assocSwapᵣ b (suc k) {m} (Fin.cast (cong (b +_) (+-suc k m)) i))
  R4-ltbk b k {m} i ltk with Nat.<-cmp (Fin.toℕ i) b
  ... | tri< lt _ _ = R4-A b k i lt
      ■ sym ( toℕ-assoc-lt b (suc k) _ (subst (Nat._< b) (sym ci) lt) ■ cong (suc k +_) ci )
    where ci = Fin.toℕ-cast (cong (b +_) (+-suc k m)) i
  ... | tri≈ _ eqb _ = R4-B b k i (Nat.≤-reflexive (sym eqb)) ltk
      ■ sym ( toℕ-assoc-mid b (suc k) _ (subst (b Nat.≤_) (sym ci) (Nat.≤-reflexive (sym eqb)))
                (subst (Nat._< b + suc k) (sym ci) (Nat.<-trans ltk (Nat.+-monoʳ-< b (Nat.n<1+n k))))
            ■ cong (Nat._∸ b) ci )
    where ci = Fin.toℕ-cast (cong (b +_) (+-suc k m)) i
  ... | tri> _ _ gtb = R4-B b k i (Nat.<⇒≤ gtb) ltk
      ■ sym ( toℕ-assoc-mid b (suc k) _ (subst (b Nat.≤_) (sym ci) (Nat.<⇒≤ gtb))
                (subst (Nat._< b + suc k) (sym ci) (Nat.<-trans ltk (Nat.+-monoʳ-< b (Nat.n<1+n k))))
            ■ cong (Nat._∸ b) ci )
    where ci = Fin.toℕ-cast (cong (b +_) (+-suc k m)) i

toℕ-R4 : ∀ b k {m} (i : 𝔽 (b + (k + suc m))) →
  Fin.toℕ (((assocSwapᵣ b k {suc m}) ·ₖ (assocSwapᵣ b 1 {m} ↑* k)) i)
  ≡ Fin.toℕ (assocSwapᵣ b (suc k) {m} (Fin.cast (cong (b +_) (+-suc k m)) i))
toℕ-R4 b k {m} i with Nat.<-cmp (Fin.toℕ i) (b + k)
... | tri< ltk _ _ = R4-ltbk b k i ltk
... | tri≈ _ eqk _ = R4-C0 b k i eqk
      ■ sym ( toℕ-assoc-mid b (suc k) _ (subst (b Nat.≤_) (sym ci) (subst (b Nat.≤_) (sym eqk) (Nat.m≤m+n b k)))
                (subst (Nat._< b + suc k) (sym ci) (subst (Nat._< b + suc k) (sym eqk)
                   (Nat.+-monoʳ-< b (Nat.n<1+n k))))
            ■ cong (Nat._∸ b) (ci ■ eqk) ■ Nat.m+n∸m≡n b k )
  where ci = Fin.toℕ-cast (cong (b +_) (+-suc k m)) i
... | tri> _ _ gtk = R4-C+ b k i gtk
      ■ sym ( toℕ-assoc-ge b (suc k) _ (subst (Nat._≤ Fin.toℕ (Fin.cast (cong (b +_) (+-suc k m)) i))
                (sym (Nat.+-suc b k)) (subst (suc (b + k) Nat.≤_) (sym ci) gtk)) ■ ci )
  where ci = Fin.toℕ-cast (cong (b +_) (+-suc k m)) i


------------------------------------------------------------------------
-- toℕ characterisation of swapᵣ (block swap); it agrees with assocSwapᵣ.
------------------------------------------------------------------------

-- toℕ of the local Fin.swap a {b}.
toℕ-finswap-lt : ∀ a b {-{m}-} (x : 𝔽 (a + b)) → Fin.toℕ x Nat.< a →
                 Fin.toℕ (Fin.swap a {b} x) ≡ b + Fin.toℕ x
toℕ-finswap-lt a b x lt =
    cong (λ s → Fin.toℕ (Fin.join b a (Sum.swap s))) (Fin.splitAt-< a x lt)
  ■ Fin.toℕ-↑ʳ b (Fin.fromℕ< lt)
  ■ cong (b +_) (Fin.toℕ-fromℕ< lt)

toℕ-finswap-ge : ∀ a b (x : 𝔽 (a + b)) → a Nat.≤ Fin.toℕ x →
                 Fin.toℕ (Fin.swap a {b} x) ≡ Fin.toℕ x Nat.∸ a
toℕ-finswap-ge a b x ge =
    cong (λ s → Fin.toℕ (Fin.join b a (Sum.swap s))) (Fin.splitAt-≥ a x ge)
  ■ Fin.toℕ-↑ˡ (Fin.reduce≥ x ge) a
  ■ toℕ-reduce≥ x ge

-- swapᵣ a b: toℕ matches assocSwapᵣ a b on all three regions.
toℕ-swapᵣ-lt : ∀ a b {n} (i : 𝔽 (a + b + n)) → Fin.toℕ i Nat.< a →
               Fin.toℕ (swapᵣ a b {n} i) ≡ b + Fin.toℕ i
toℕ-swapᵣ-lt a b {n} i lt =
    cong (λ s → Fin.toℕ (Fin.join (b + a) n (Sum.map₁ (Fin.swap a) s)))
         (Fin.splitAt-< (a + b) i (Nat.<-≤-trans lt (Nat.m≤m+n a b)))
  ■ Fin.toℕ-↑ˡ (Fin.swap a (Fin.fromℕ< (Nat.<-≤-trans lt (Nat.m≤m+n a b)))) n
  ■ toℕ-finswap-lt a b (Fin.fromℕ< (Nat.<-≤-trans lt (Nat.m≤m+n a b)))
      (subst (Nat._< a) (sym (Fin.toℕ-fromℕ< _)) lt)
  ■ cong (b +_) (Fin.toℕ-fromℕ< _)

toℕ-swapᵣ-mid : ∀ a b {n} (i : 𝔽 (a + b + n)) → a Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< a + b →
                Fin.toℕ (swapᵣ a b {n} i) ≡ Fin.toℕ i Nat.∸ a
toℕ-swapᵣ-mid a b {n} i ge lt =
    cong (λ s → Fin.toℕ (Fin.join (b + a) n (Sum.map₁ (Fin.swap a) s)))
         (Fin.splitAt-< (a + b) i lt)
  ■ Fin.toℕ-↑ˡ (Fin.swap a (Fin.fromℕ< lt)) n
  ■ toℕ-finswap-ge a b (Fin.fromℕ< lt) (subst (a Nat.≤_) (sym (Fin.toℕ-fromℕ< lt)) ge)
  ■ cong (Nat._∸ a) (Fin.toℕ-fromℕ< lt)

toℕ-swapᵣ-ge : ∀ a b {n} (i : 𝔽 (a + b + n)) → a + b Nat.≤ Fin.toℕ i →
               Fin.toℕ (swapᵣ a b {n} i) ≡ Fin.toℕ i
toℕ-swapᵣ-ge a b {n} i ge =
    cong (λ s → Fin.toℕ (Fin.join (b + a) n (Sum.map₁ (Fin.swap a) s)))
         (Fin.splitAt-≥ (a + b) i ge)
  ■ Fin.toℕ-↑ʳ (b + a) (Fin.reduce≥ i ge)
  ■ cong (b + a +_) (toℕ-reduce≥ i ge)
  ■ cong (Nat._+ (Fin.toℕ i Nat.∸ (a + b))) (Nat.+-comm b a)
  ■ Nat.m+[n∸m]≡n ge

-- placement of swapᵣ on canonical block indices (used by the leaf reconcile).
swap-place-A : ∀ b1 b2 {m} (j : 𝔽 b1) →
               swapᵣ b1 b2 {m} ((j ↑ˡ b2) ↑ˡ m) ≡ (b2 ↑ʳ j) ↑ˡ m
swap-place-A b1 b2 {m} j = Fin.toℕ-injective
  ( toℕ-swapᵣ-lt b1 b2 ((j ↑ˡ b2) ↑ˡ m)
      (subst (Nat._< b1) (sym src) (Fin.toℕ<n j))
  ■ cong (b2 +_) src
  ■ sym (Fin.toℕ-↑ˡ (b2 ↑ʳ j) m ■ Fin.toℕ-↑ʳ b2 j) )
  where src : Fin.toℕ ((j ↑ˡ b2) ↑ˡ m) ≡ Fin.toℕ j
        src = Fin.toℕ-↑ˡ (j ↑ˡ b2) m ■ Fin.toℕ-↑ˡ j b2

swap-place-B : ∀ b1 b2 {m} (k : 𝔽 b2) →
               swapᵣ b1 b2 {m} ((b1 ↑ʳ k) ↑ˡ m) ≡ (k ↑ˡ b1) ↑ˡ m
swap-place-B b1 b2 {m} k = Fin.toℕ-injective
  ( toℕ-swapᵣ-mid b1 b2 ((b1 ↑ʳ k) ↑ˡ m)
      (subst (b1 Nat.≤_) (sym src) (Nat.m≤m+n b1 (Fin.toℕ k)))
      (subst (Nat._< b1 + b2) (sym src) (Nat.+-monoʳ-< b1 (Fin.toℕ<n k)))
  ■ cong (Nat._∸ b1) src
  ■ Nat.m+n∸m≡n b1 (Fin.toℕ k)
  ■ sym (Fin.toℕ-↑ˡ (k ↑ˡ b1) m ■ Fin.toℕ-↑ˡ k b1) )
  where src : Fin.toℕ ((b1 ↑ʳ k) ↑ˡ m) ≡ b1 + Fin.toℕ k
        src = Fin.toℕ-↑ˡ (b1 ↑ʳ k) m ■ Fin.toℕ-↑ʳ b1 k

swap-place-tail : ∀ b1 b2 {m} (i : 𝔽 m) →
                  swapᵣ b1 b2 {m} ((b1 + b2) ↑ʳ i) ≡ (b2 + b1) ↑ʳ i
swap-place-tail b1 b2 {m} i = Fin.toℕ-injective
  ( toℕ-swapᵣ-ge b1 b2 ((b1 + b2) ↑ʳ i)
      (subst (b1 + b2 Nat.≤_) (sym src) (Nat.m≤m+n (b1 + b2) (Fin.toℕ i)))
  ■ src
  ■ cong (Nat._+ Fin.toℕ i) (Nat.+-comm b1 b2)
  ■ sym (Fin.toℕ-↑ʳ (b2 + b1) i) )
  where src : Fin.toℕ ((b1 + b2) ↑ʳ i) ≡ b1 + b2 + Fin.toℕ i
        src = Fin.toℕ-↑ʳ (b1 + b2) i


------------------------------------------------------------------------
-- weaken* (as a renaming) is _↑ʳ_ on indices; toℕ adds the offset.
------------------------------------------------------------------------

weaken*ᵣ~↑ʳ : ∀ (k : ℕ) {nn} (x : 𝔽 nn) → weaken* ⦃ Kᵣ ⦄ k x ≡ k ↑ʳ x
weaken*ᵣ~↑ʳ zero    x = refl
weaken*ᵣ~↑ʳ (suc k) x = cong suc (weaken*ᵣ~↑ʳ k x)

toℕ-weaken*ᵣ : ∀ (k : ℕ) {nn} (x : 𝔽 nn) → Fin.toℕ (weaken* ⦃ Kᵣ ⦄ k x) ≡ k + Fin.toℕ x
toℕ-weaken*ᵣ k x = cong Fin.toℕ (weaken*ᵣ~↑ʳ k x) ■ Fin.toℕ-↑ʳ k x

-- toℕ of (weaken* k) ↑* b on the two regions.
toℕ-wk↑*-lt : ∀ b k {p} (i : 𝔽 (b + p)) → Fin.toℕ i Nat.< b →
              Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ k ↑* b) i) ≡ Fin.toℕ i
toℕ-wk↑*-lt b k {p} i lt =
    cong Fin.toℕ (↑*-split (weaken* ⦃ Kᵣ ⦄ k) b i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → b ↑ʳ weaken* ⦃ Kᵣ ⦄ k j) ]′ s)) (Fin.splitAt-< b i lt)
  ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) _ ■ Fin.toℕ-fromℕ< lt

toℕ-wk↑*-ge : ∀ b k {p} (i : 𝔽 (b + p)) (q : b Nat.≤ Fin.toℕ i) →
              Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ k ↑* b) i) ≡ b + (k + (Fin.toℕ i Nat.∸ b))
toℕ-wk↑*-ge b k {p} i q =
    cong Fin.toℕ (↑*-split (weaken* ⦃ Kᵣ ⦄ k) b i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → b ↑ʳ weaken* ⦃ Kᵣ ⦄ k j) ]′ s)) (Fin.splitAt-≥ b i q)
  ■ Fin.toℕ-↑ʳ b (weaken* ⦃ Kᵣ ⦄ k (Fin.reduce≥ i q))
  ■ cong (b +_) (toℕ-weaken*ᵣ k (Fin.reduce≥ i q) ■ cong (k +_) (toℕ-reduce≥ i q))

-- toℕ of (swapᵣ a b) ↑* k on a high index (≥ k): drops k, applies swapᵣ on residual.
toℕ-swap↑*-ge : ∀ k a b {p} (i : 𝔽 (k + (a + b + p))) (q : k Nat.≤ Fin.toℕ i) →
                Fin.toℕ ((swapᵣ a b {p} ↑* k) i)
                ≡ k + Fin.toℕ (swapᵣ a b {p} (Fin.reduce≥ i q))
toℕ-swap↑*-ge k a b {p} i q =
    cong Fin.toℕ (↑*-split (swapᵣ a b {p}) k i)
  ■ cong (λ s → Fin.toℕ ([ (_↑ˡ _) , (λ j → k ↑ʳ swapᵣ a b j) ]′ s)) (Fin.splitAt-≥ k i q)
  ■ Fin.toℕ-↑ʳ k (swapᵣ a b (Fin.reduce≥ i q))

-- R' = (swapᵣ 1 1 ↑* sB2) ↑* sB1 fixes any index whose residual past sB1+sB2 is ≥ 2.
R'-fix-ge : ∀ sB1 sB2 {p} (i : 𝔽 (sB1 + (sB2 + (2 + p)))) → sB1 + (sB2 + 2) Nat.≤ Fin.toℕ i →
            Fin.toℕ (((swapᵣ 1 1 {p} ↑* sB2) ↑* sB1) i) ≡ Fin.toℕ i
R'-fix-ge sB1 sB2 {p} i ge =
    toℕ-↑*-ge (swapᵣ 1 1 {p} ↑* sB2) sB1 i q1
  ■ cong (sB1 +_) ( toℕ-swap↑*-ge sB2 1 1 (Fin.reduce≥ i q1) q2
                  ■ cong (sB2 +_) (toℕ-swapᵣ-ge 1 1 (Fin.reduce≥ (Fin.reduce≥ i q1) q2) q3 ■ red2)
                  ■ Nat.m+[n∸m]≡n q2 )
  ■ cong (sB1 +_) red1
  ■ Nat.m+[n∸m]≡n q1
  where
    q1 : sB1 Nat.≤ Fin.toℕ i
    q1 = Nat.≤-trans (Nat.m≤m+n sB1 (sB2 + 2)) ge
    red1 : Fin.toℕ (Fin.reduce≥ i q1) ≡ Fin.toℕ i Nat.∸ sB1
    red1 = toℕ-reduce≥ i q1
    sb2+2≤ : sB2 + 2 Nat.≤ Fin.toℕ (Fin.reduce≥ i q1)
    sb2+2≤ = subst (sB2 + 2 Nat.≤_) (sym red1)
               (Nat.≤-trans (Nat.≤-reflexive (sym (Nat.m+n∸m≡n sB1 (sB2 + 2)))) (Nat.∸-monoˡ-≤ sB1 ge))
    q2 : sB2 Nat.≤ Fin.toℕ (Fin.reduce≥ i q1)
    q2 = Nat.≤-trans (Nat.m≤m+n sB2 2) sb2+2≤
    red2 : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ i q1) q2) ≡ Fin.toℕ (Fin.reduce≥ i q1) Nat.∸ sB2
    red2 = toℕ-reduce≥ (Fin.reduce≥ i q1) q2
    q3 : 1 + 1 Nat.≤ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ i q1) q2)
    q3 = subst (2 Nat.≤_) (sym red2)
           (Nat.≤-trans (Nat.≤-reflexive (sym (Nat.m+n∸m≡n sB2 2))) (Nat.∸-monoˡ-≤ sB2 sb2+2≤))

-- toℕ of swapᵣ 1 1 depends only on toℕ of its argument.
swap11-cong : ∀ {q q′} (a : 𝔽 (1 + 1 + q)) (b : 𝔽 (1 + 1 + q′)) →
              Fin.toℕ a ≡ Fin.toℕ b → Fin.toℕ (swapᵣ 1 1 {q} a) ≡ Fin.toℕ (swapᵣ 1 1 {q′} b)
swap11-cong {q} {q′} a b e with Nat.<-cmp (Fin.toℕ a) 1
... | tri< lt _ _ = toℕ-swapᵣ-lt 1 1 a lt ■ cong (1 +_) e ■ sym (toℕ-swapᵣ-lt 1 1 b (subst (Nat._< 1) e lt))
... | tri≈ _ eq _ = toℕ-swapᵣ-mid 1 1 a (Nat.≤-reflexive (sym eq)) (subst (Nat._< 2) (sym eq) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
                  ■ cong (Nat._∸ 1) e
                  ■ sym (toℕ-swapᵣ-mid 1 1 b (Nat.≤-reflexive (sym beq)) (subst (Nat._< 2) (sym beq) (Nat.s≤s (Nat.s≤s Nat.z≤n))))
  where beq : Fin.toℕ b ≡ 1
        beq = sym e ■ eq
... | tri> _ _ gt = toℕ-swapᵣ-ge 1 1 a gt ■ e ■ sym (toℕ-swapᵣ-ge 1 1 b (subst (2 Nat.≤_) e gt))

-- the x ≥ sB region of commuteS (sub-cases on x vs sB+j internally).
private
  commuteS-ge-hi : ∀ sB j {p} (x : 𝔽 (sB + (j + (2 + p)))) → sB + j Nat.≤ Fin.toℕ x →
        Fin.toℕ ((assocSwapᵣ sB j ·ₖ ((swapᵣ 1 1 {p} ↑* sB) ↑* j)) x)
        ≡ Fin.toℕ ((((swapᵣ 1 1 {p} ↑* j) ↑* sB) ·ₖ assocSwapᵣ sB j {2 + p}) x)
  commuteS-ge-hi sB j {p} x hi = lhsH ■ congSwap ■ sym rhsH
        where
          p≥ : sB Nat.≤ Fin.toℕ x
          p≥ = Nat.≤-trans (Nat.m≤m+n sB j) hi
          j≤ : j Nat.≤ Fin.toℕ x
          j≤ = Nat.≤-trans (Nat.m≤n+m j sB) hi
          asgx = toℕ-assoc-ge sB j x hi
          qj : j Nat.≤ Fin.toℕ (assocSwapᵣ sB j x)
          qj = subst (j Nat.≤_) (sym asgx) j≤
          rj-as : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) ≡ Fin.toℕ x Nat.∸ j
          rj-as = toℕ-reduce≥ (assocSwapᵣ sB j x) qj ■ cong (Nat._∸ j) asgx
          qsB : sB Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ sB j x) qj)
          qsB = subst (sB Nat.≤_) (sym rj-as)
                  (subst (Nat._≤ Fin.toℕ x Nat.∸ j) (Nat.m+n∸m≡n j sB)
                    (Nat.∸-monoˡ-≤ j (subst (Nat._≤ Fin.toℕ x) (Nat.+-comm sB j) hi)))
          lhsH : Fin.toℕ (((swapᵣ 1 1 {p} ↑* sB) ↑* j) (assocSwapᵣ sB j x))
                 ≡ j + (sB + Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB)))
          lhsH = toℕ-↑*-ge (swapᵣ 1 1 {p} ↑* sB) j (assocSwapᵣ sB j x) qj
               ■ cong (j +_) (toℕ-↑*-ge (swapᵣ 1 1 {p}) sB (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB)
          rsB : Fin.toℕ (Fin.reduce≥ x p≥) ≡ Fin.toℕ x Nat.∸ sB
          rsB = toℕ-reduce≥ x p≥
          qj' : j Nat.≤ Fin.toℕ (Fin.reduce≥ x p≥)
          qj' = subst (j Nat.≤_) (sym rsB)
                  (subst (Nat._≤ Fin.toℕ x Nat.∸ sB) (Nat.m+n∸m≡n sB j) (Nat.∸-monoˡ-≤ sB hi))
          inner-toℕ : Fin.toℕ (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x)
                      ≡ sB + (j + Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ x p≥) qj')))
          inner-toℕ = toℕ-↑*-ge (swapᵣ 1 1 {p} ↑* j) sB x p≥
                    ■ cong (sB +_) (toℕ-↑*-ge (swapᵣ 1 1 {p}) j (Fin.reduce≥ x p≥) qj')
          hiRes : sB + j Nat.≤ Fin.toℕ (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x)
          hiRes = subst (sB + j Nat.≤_) (sym inner-toℕ)
                    (Nat.≤-trans (Nat.+-monoʳ-≤ sB (Nat.m≤m+n j _)) Nat.≤-refl)
          rhsH : Fin.toℕ (assocSwapᵣ sB j (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x))
                 ≡ sB + (j + Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ x p≥) qj')))
          rhsH = toℕ-assoc-ge sB j (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x) hiRes ■ inner-toℕ
          resEq : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB)
                  ≡ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x p≥) qj')
          resEq = toℕ-reduce≥ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB ■ cong (Nat._∸ sB) rj-as
                ■ Nat.∸-+-assoc (Fin.toℕ x) j sB ■ cong (Fin.toℕ x Nat.∸_) (Nat.+-comm j sB)
                ■ sym (Nat.∸-+-assoc (Fin.toℕ x) sB j)
                ■ sym (toℕ-reduce≥ (Fin.reduce≥ x p≥) qj' ■ cong (Nat._∸ j) rsB)
          congSwap : j + (sB + Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB)))
                     ≡ sB + (j + Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ x p≥) qj')))
          congSwap = cong (λ z → j + (sB + z))
                       (swap11-cong (Fin.reduce≥ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) qsB)
                                    (Fin.reduce≥ (Fin.reduce≥ x p≥) qj') resEq)
                   ■ ( sym (Nat.+-assoc j sB t) ■ cong (Nat._+ t) (Nat.+-comm j sB) ■ Nat.+-assoc sB j t )
            where t = Fin.toℕ (swapᵣ 1 1 {p} (Fin.reduce≥ (Fin.reduce≥ x p≥) qj'))

  commuteS-ge : ∀ sB j {p} (x : 𝔽 (sB + (j + (2 + p)))) → sB Nat.≤ Fin.toℕ x →
                Fin.toℕ ((assocSwapᵣ sB j ·ₖ ((swapᵣ 1 1 {p} ↑* sB) ↑* j)) x)
                ≡ Fin.toℕ ((((swapᵣ 1 1 {p} ↑* j) ↑* sB) ·ₖ assocSwapᵣ sB j {2 + p}) x)
  commuteS-ge sB j {p} x p≥ with Nat.<-cmp (Fin.toℕ x) (sB + j)
  ... | tri< ltj _ _ = lhsM ■ sym rhsM
    where
      asx = toℕ-assoc-mid sB j x p≥ ltj
      red<j : Fin.toℕ x Nat.∸ sB Nat.< j
      red<j = Nat.+-cancelˡ-< sB (Fin.toℕ x Nat.∸ sB) j
                (subst (Nat._< sB + j) (sym (Nat.m+[n∸m]≡n p≥)) ltj)
      lhsM : Fin.toℕ (((swapᵣ 1 1 {p} ↑* sB) ↑* j) (assocSwapᵣ sB j x)) ≡ Fin.toℕ x Nat.∸ sB
      lhsM = toℕ-↑*-lt (swapᵣ 1 1 {p} ↑* sB) j (assocSwapᵣ sB j x) (subst (Nat._< j) (sym asx) red<j) ■ asx
      sw≡ : Fin.toℕ (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x) ≡ Fin.toℕ x
      sw≡ = toℕ-↑*-ge (swapᵣ 1 1 {p} ↑* j) sB x p≥
          ■ cong (sB +_) (toℕ-↑*-lt (swapᵣ 1 1 {p}) j (Fin.reduce≥ x p≥)
                            (subst (Nat._< j) (sym (toℕ-reduce≥ x p≥)) red<j)
                          ■ toℕ-reduce≥ x p≥)
          ■ Nat.m+[n∸m]≡n p≥
      rhsM : Fin.toℕ (assocSwapᵣ sB j (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x)) ≡ Fin.toℕ x Nat.∸ sB
      rhsM = toℕ-assoc-mid sB j (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x)
               (subst (sB Nat.≤_) (sym sw≡) p≥) (subst (Nat._< sB + j) (sym sw≡) ltj)
           ■ cong (Nat._∸ sB) sw≡
  ... | tri≈ _ eqj _ = commuteS-ge-hi sB j x (Nat.≤-reflexive (sym eqj))
  ... | tri> _ _ gtj = commuteS-ge-hi sB j x (Nat.<⇒≤ gtj)

-- commute the assocSwap and the swap-lifted-deep renaming (they act on disjoint blocks).
commuteS : ∀ sB j {p} →
           (assocSwapᵣ sB j ·ₖ ((swapᵣ 1 1 {p} ↑* sB) ↑* j))
           ≗ (((swapᵣ 1 1 {p} ↑* j) ↑* sB) ·ₖ assocSwapᵣ sB j {2 + p})
commuteS sB j {p} x with Nat.<-cmp (Fin.toℕ x) sB
... | tri< lt _ _ = Fin.toℕ-injective (lhs ■ sym rhs)
  where
    asx = toℕ-assoc-lt sB j x lt
    qj : j Nat.≤ Fin.toℕ (assocSwapᵣ sB j x)
    qj = subst (j Nat.≤_) (sym asx) (Nat.m≤m+n j (Fin.toℕ x))
    lhs : Fin.toℕ (((swapᵣ 1 1 {p} ↑* sB) ↑* j) (assocSwapᵣ sB j x)) ≡ j + Fin.toℕ x
    lhs = toℕ-↑*-ge (swapᵣ 1 1 {p} ↑* sB) j (assocSwapᵣ sB j x) qj
        ■ cong (j +_) ( toℕ-↑*-lt (swapᵣ 1 1 {p}) sB (Fin.reduce≥ (assocSwapᵣ sB j x) qj) red<
                      ■ redt )
      where
        redt : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) ≡ Fin.toℕ x
        redt = toℕ-reduce≥ (assocSwapᵣ sB j x) qj ■ cong (Nat._∸ j) asx ■ Nat.m+n∸m≡n j (Fin.toℕ x)
        red< : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ sB j x) qj) Nat.< sB
        red< = subst (Nat._< sB) (sym redt) lt
    rhs : Fin.toℕ (assocSwapᵣ sB j (((swapᵣ 1 1 {p} ↑* j) ↑* sB) x)) ≡ j + Fin.toℕ x
    rhs = cong (λ z → Fin.toℕ (assocSwapᵣ sB j z)) (Fin.toℕ-injective (toℕ-↑*-lt (swapᵣ 1 1 {p} ↑* j) sB x lt))
        ■ toℕ-assoc-lt sB j x lt
... | tri≈ _ eq _ = Fin.toℕ-injective (commuteS-ge sB j x (Nat.≤-reflexive (sym eq)))
... | tri> _ _ gt = Fin.toℕ-injective (commuteS-ge sB j x (Nat.<⇒≤ gt))

-- (weaken* j ↑* sB) ·ₖ assocSwapᵣ sB j ≗ weaken* j  (binder block carried by the swap).
private
  wkSwap-cancel-ge : ∀ sB j {M} (x : 𝔽 (sB + M)) → sB Nat.≤ Fin.toℕ x →
                     ((weaken* ⦃ Kᵣ ⦄ j ↑* sB) ·ₖ assocSwapᵣ sB j {M}) x ≡ weaken* ⦃ Kᵣ ⦄ j x
  wkSwap-cancel-ge sB j {M} x p = Fin.toℕ-injective
      ( toℕ-assoc-ge sB j ((weaken* ⦃ Kᵣ ⦄ j ↑* sB) x)
          (subst (sB + j Nat.≤_) (sym wge) (Nat.+-monoʳ-≤ sB (Nat.m≤m+n j (Fin.toℕ x Nat.∸ sB))))
      ■ wge
      ■ ( Nat.+-comm sB (j + (Fin.toℕ x Nat.∸ sB))
        ■ Nat.+-assoc j (Fin.toℕ x Nat.∸ sB) sB
        ■ cong (j +_) (Nat.+-comm (Fin.toℕ x Nat.∸ sB) sB ■ Nat.m+[n∸m]≡n p) )
      ■ sym (toℕ-weaken*ᵣ j x) )
    where wge = toℕ-wk↑*-ge sB j x p

wkSwap-cancel : ∀ sB j {M} → ((weaken* ⦃ Kᵣ ⦄ j ↑* sB) ·ₖ assocSwapᵣ sB j {M}) ≗ weaken* ⦃ Kᵣ ⦄ j
wkSwap-cancel sB j {M} x with Nat.<-cmp (Fin.toℕ x) sB
... | tri< lt _ _ = Fin.toℕ-injective
      ( toℕ-assoc-lt sB j ((weaken* ⦃ Kᵣ ⦄ j ↑* sB) x) (subst (Nat._< sB) (sym wlt) lt)
      ■ cong (j +_) wlt ■ sym (toℕ-weaken*ᵣ j x) )
  where wlt = toℕ-wk↑*-lt sB j x lt
... | tri≈ _ eq _ = wkSwap-cancel-ge sB j x (Nat.≤-reflexive (sym eq))
... | tri> _ _ gt = wkSwap-cancel-ge sB j x (Nat.<⇒≤ gt)

-- Claim A: weaken* k ·ₖ assocSwapᵣ k b ≗ (weaken* k) ↑* b.
wk·assocSwap : ∀ k b {p} → (weaken* ⦃ Kᵣ ⦄ k ·ₖ assocSwapᵣ k b {p}) ≗ (weaken* ⦃ Kᵣ ⦄ k ↑* b)
wk·assocSwap k b {p} j with Nat.<-cmp (Fin.toℕ j) b
... | tri< lt _ _ = Fin.toℕ-injective
      ( toℕ-assoc-mid k b (weaken* ⦃ Kᵣ ⦄ k j)
          (subst (k Nat.≤_) (sym wkj) (Nat.m≤m+n k (Fin.toℕ j)))
          (subst (Nat._< k + b) (sym wkj) (Nat.+-monoʳ-< k lt))
      ■ cong (Nat._∸ k) wkj ■ Nat.m+n∸m≡n k (Fin.toℕ j)
      ■ sym (toℕ-wk↑*-lt b k j lt) )
  where wkj = toℕ-weaken*ᵣ k j
... | tri≈ _ eq _ = Fin.toℕ-injective
      ( toℕ-assoc-ge k b (weaken* ⦃ Kᵣ ⦄ k j)
          (subst (k + b Nat.≤_) (sym wkj) (Nat.+-monoʳ-≤ k (Nat.≤-reflexive (sym eq))))
      ■ wkj
      ■ sym ( toℕ-wk↑*-ge b k j (Nat.≤-reflexive (sym eq))
            ■ cong (λ z → b + (k + (z Nat.∸ b))) eq
            ■ cong (λ z → b + (k + z)) (Nat.n∸n≡0 b)
            ■ cong (b +_) (Nat.+-identityʳ k)
            ■ Nat.+-comm b k
            ■ cong (k +_) (sym eq) ) )
  where wkj = toℕ-weaken*ᵣ k j
... | tri> _ _ gt = Fin.toℕ-injective
      ( toℕ-assoc-ge k b (weaken* ⦃ Kᵣ ⦄ k j)
          (subst (k + b Nat.≤_) (sym wkj) (Nat.+-monoʳ-≤ k (Nat.<⇒≤ gt)))
      ■ wkj
      ■ sym ( toℕ-wk↑*-ge b k j (Nat.<⇒≤ gt)
            ■ cong (λ z → b + z) (sym (Nat.+-∸-assoc k (Nat.<⇒≤ gt)))
            ■ Nat.m+[n∸m]≡n {b} {k + Fin.toℕ j} (Nat.≤-trans (Nat.<⇒≤ gt) (Nat.m≤n+m (Fin.toℕ j) k)) ) )
  where wkj = toℕ-weaken*ᵣ k j

------------------------------------------------------------------------
-- assocSwapᵣ a b lifted past k inert binders fixes any index ≥ k + (a + b).
------------------------------------------------------------------------

toℕ-assoc↑*-fix-ge : ∀ k a b {p} (i : 𝔽 (k + (a + (b + p)))) → k + (a + b) Nat.≤ Fin.toℕ i →
                     Fin.toℕ ((assocSwapᵣ a b {p} ↑* k) i) ≡ Fin.toℕ i
toℕ-assoc↑*-fix-ge k a b {p} i ge =
    toℕ-↑*-ge (assocSwapᵣ a b {p}) k i q1
  ■ cong (k +_) ( toℕ-assoc-ge a b (Fin.reduce≥ i q1) ab≤ ■ red1 )
  ■ Nat.m+[n∸m]≡n q1
  where
    q1 : k Nat.≤ Fin.toℕ i
    q1 = Nat.≤-trans (Nat.m≤m+n k (a + b)) ge
    red1 : Fin.toℕ (Fin.reduce≥ i q1) ≡ Fin.toℕ i Nat.∸ k
    red1 = toℕ-reduce≥ i q1
    ab≤ : a + b Nat.≤ Fin.toℕ (Fin.reduce≥ i q1)
    ab≤ = subst (a + b Nat.≤_) (sym red1)
            (Nat.≤-trans (Nat.≤-reflexive (sym (Nat.m+n∸m≡n k (a + b)))) (Nat.∸-monoˡ-≤ k ge))

-- assocSwapᵣ a b lifted past k inert binders is the identity on indices < k.
toℕ-assoc↑*-lt : ∀ k a b {p} (i : 𝔽 (k + (a + (b + p)))) → Fin.toℕ i Nat.< k →
                 Fin.toℕ ((assocSwapᵣ a b {p} ↑* k) i) ≡ Fin.toℕ i
toℕ-assoc↑*-lt k a b {p} i lt = toℕ-↑*-lt (assocSwapᵣ a b {p}) k i lt

------------------------------------------------------------------------
-- positional placement of assocSwapᵣ a b on the three blocks.
------------------------------------------------------------------------

-- a-block (low): index k ↑ˡ (b+m) maps to b ↑ʳ (k ↑ˡ m).
assoc-place-lo : ∀ a b {m} (k : 𝔽 a) → assocSwapᵣ a b {m} (k ↑ˡ (b + m)) ≡ b ↑ʳ (k ↑ˡ m)
assoc-place-lo a b {m} k = Fin.toℕ-injective
  ( toℕ-assoc-lt a b (k ↑ˡ (b + m)) (subst (Nat._< a) (sym src) (Fin.toℕ<n k))
  ■ cong (b +_) src
  ■ sym (Fin.toℕ-↑ʳ b (k ↑ˡ m) ■ cong (b +_) (Fin.toℕ-↑ˡ k m)) )
  where src : Fin.toℕ (k ↑ˡ (b + m)) ≡ Fin.toℕ k
        src = Fin.toℕ-↑ˡ k (b + m)

-- b-block (mid): index a ↑ʳ (k ↑ˡ m) maps to k ↑ˡ (a+m).
assoc-place-mid : ∀ a b {m} (k : 𝔽 b) → assocSwapᵣ a b {m} (a ↑ʳ (k ↑ˡ m)) ≡ k ↑ˡ (a + m)
assoc-place-mid a b {m} k = Fin.toℕ-injective
  ( toℕ-assoc-mid a b (a ↑ʳ (k ↑ˡ m))
      (subst (a Nat.≤_) (sym src) (Nat.m≤m+n a (Fin.toℕ k)))
      (subst (Nat._< a + b) (sym src) (Nat.+-monoʳ-< a (Fin.toℕ<n k)))
  ■ cong (Nat._∸ a) src ■ Nat.m+n∸m≡n a (Fin.toℕ k)
  ■ sym (Fin.toℕ-↑ˡ k (a + m)) )
  where src : Fin.toℕ (a ↑ʳ (k ↑ˡ m)) ≡ a + Fin.toℕ k
        src = Fin.toℕ-↑ʳ a (k ↑ˡ m) ■ cong (a +_) (Fin.toℕ-↑ˡ k m)

-- tail (high): index a ↑ʳ (b ↑ʳ j) maps to b ↑ʳ (a ↑ʳ j).
assoc-place-tail : ∀ a b {m} (j : 𝔽 m) → assocSwapᵣ a b {m} (a ↑ʳ (b ↑ʳ j)) ≡ b ↑ʳ (a ↑ʳ j)
assoc-place-tail a b {m} j = Fin.toℕ-injective
  ( toℕ-assoc-ge a b (a ↑ʳ (b ↑ʳ j)) (subst (a + b Nat.≤_) (sym src) (Nat.m≤m+n (a + b) (Fin.toℕ j)))
  ■ src
  ■ cong (Nat._+ Fin.toℕ j) (Nat.+-comm a b)
  ■ sym (Fin.toℕ-↑ʳ b (a ↑ʳ j) ■ cong (b +_) (Fin.toℕ-↑ʳ a j) ■ sym (Nat.+-assoc b a (Fin.toℕ j))) )
  where src : Fin.toℕ (a ↑ʳ (b ↑ʳ j)) ≡ a + b + Fin.toℕ j
        src = Fin.toℕ-↑ʳ a (b ↑ʳ j) ■ cong (a +_) (Fin.toℕ-↑ʳ b j) ■ sym (Nat.+-assoc a b (Fin.toℕ j))
