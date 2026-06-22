module BorrowedCF.Simulation.Theorems.LSplit where

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

-- Reduction congruence for the iterated async-channel binder (iterated RU-Sync).
φ^-─→ : ∀ k {N} {P Q : 𝐔.Proc (k + N)} → P 𝐔R.─→ₚ Q → φ^ k P 𝐔R.─→ₚ φ^ k Q
φ^-─→ zero    pq = pq
φ^-─→ (suc k) pq = φ^-─→ k (𝐔R.RU-Sync pq)

-- Head handle of a (suc b)-chain whose tail term is closed (K`unit): the lsplit
-- target.  canonₛ threads e₂ as (e₂ ⋯ weakenᵣ) per chain, and the leaf's e₂ starts at
-- cc1.e₂ = K`unit, so every chain's tail term stays K`unit ⇒ this covers every chain.
Ubₛ-head : ∀ b {M} (e₁ : Tm M) (x : 𝔽 M) →
           Ubₛ (suc b) (e₁ , x , K `unit) 0F ≡ (e₁ ⊗ (` x)) ⊗ K `unit
Ubₛ-head zero    e₁ x = refl
Ubₛ-head (suc b) e₁ x = refl

-- Second handle of a (suc (suc b))-chain (the lsplit continuation): again uniform in b.
Ubₛ-2nd : ∀ b {M} (e₁ : Tm M) (x : 𝔽 M) →
          Ubₛ (suc (suc b)) (e₁ , x , K `unit) 1F ≡ (K `unit ⊗ (` x)) ⊗ K `unit
Ubₛ-2nd zero    e₁ x = refl
Ubₛ-2nd (suc b) e₁ x = refl

-- Growing a chain by one borrow shifts every borrow up by one slot; the borrow VALUES
-- are unchanged (only the head handle's tail moves to the new handle).  At position
-- suc j' the grown chain agrees with the original at suc (suc j').
Ubₛ-lwk : ∀ b {M} (cc : UChan M) (j′ : 𝔽 b) →
          Ubₛ (suc b) cc (suc j′) ≡ Ubₛ (suc (suc b)) cc (suc (suc j′))
Ubₛ-lwk (suc b) cc j′ = refl

-- subst over the term constructors (trivial; for distributing the canonₛ +-suc subst).
subst-⊗ : ∀ {a b} (eq : a ≡ b) (p r : Tm a) →
          subst Tm eq (p ⊗ r) ≡ subst Tm eq p ⊗ subst Tm eq r
subst-⊗ refl p r = refl

subst-` : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
subst-` refl q = refl

subst-Kunit : ∀ {a b} (eq : a ≡ b) → subst Tm eq (K `unit) ≡ K `unit
subst-Kunit refl = refl

-- The split handle position for (a ∷ B₁') factors as a ↑ʳ (the position for B₁') —
-- so it lands past Ubₛ a, in the recursive canonₛ block.
pos-split : ∀ a (B₁′ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Fin.cast (sym (sum-++ (a ∷ B₁′) (suc b₁ ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ 0F)
    ≡ a ↑ʳ Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F)
pos-split a B₁′ b₁ B₂ = Fin.toℕ-injective
  ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁′) (suc b₁ ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ 0F)
  ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁′)) 0F
  ■ +-assoc a (sum B₁′) 0
  ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F))
        ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F)
                      ■ Fin.toℕ-↑ʳ (sum B₁′) 0F ) ) )

pos-split-gen : ∀ a (B₁′ : 𝐓.BindGroup) (c : ℕ) (B₂ : 𝐓.BindGroup) (i : 𝔽 (sum (c ∷ B₂))) →
  Fin.cast (sym (sum-++ (a ∷ B₁′) (c ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ i)
    ≡ a ↑ʳ Fin.cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i)
pos-split-gen a B₁′ c B₂ i = Fin.toℕ-injective
  ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁′) (c ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ i)
  ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁′)) i
  ■ +-assoc a (sum B₁′) (Fin.toℕ i)
  ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i))
        ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i)
                      ■ Fin.toℕ-↑ʳ (sum B₁′) i ) ) )

-- Data-level handle insertion: growing the split chain inserts ONE slot at position 1
-- of that chain (the new inj 1F handle), leaving the chains in B₁ untouched.
dlwk : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
       sum (B₁ ++ suc b₁ ∷ B₂) →ᵣ sum (B₁ ++ suc (suc b₁) ∷ B₂)
dlwk []        b₁ B₂ i = (weakenᵣ ↑* 1) i
dlwk (a ∷ B₁') b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ suc (suc b₁) ∷ B₂)) , (λ r → a ↑ʳ dlwk B₁' b₁ B₂ r) ]′ (splitAt a i)

-- dlwk inserts a slot at flat position `sum B₁ + 1`: below it, toℕ is preserved; above, +1.
dlwk-lo : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          Fin.toℕ j Nat.< sum B₁ + 1 → Fin.toℕ (dlwk B₁ b₁ B₂ j) ≡ Fin.toℕ j
dlwk-lo []        b₁ B₂ j lt = ↑*-lo weakenᵣ 1 j lt
dlwk-lo (a ∷ B₁') b₁ B₂ j lt with dlwk-lo B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : Fin.toℕ r Nat.< sum B₁' + 1
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁' + 1)
                   (subst (Nat._< a + (sum B₁' + 1)) jℕ
                     (subst (Fin.toℕ j Nat.<_) (Nat.+-assoc a (sum B₁') 1) lt))

dlwk-hi : ∀ (B₁ : 𝐓.BindGroup) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          sum B₁ + 1 Nat.≤ Fin.toℕ j → Fin.toℕ (dlwk B₁ b₁ B₂ j) ≡ suc (Fin.toℕ j)
dlwk-hi []        b₁ B₂ j h =
    ↑*-hi weakenᵣ 1 j h
  ■ cong (1 +_) (cong suc (toℕ-reduce≥ j h))
  ■ cong suc (Nat.m+[n∸m]≡n h)
dlwk-hi (a ∷ B₁') b₁ B₂ j h with dlwk-hi B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁' + 1))) (subst (Nat._≤ Fin.toℕ j) (Nat.+-assoc a (sum B₁') 1) h)))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : sum B₁' + 1 Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁' + 1) (Fin.toℕ r)
                   (subst (a + (sum B₁' + 1) Nat.≤_) jℕ
                     (subst (Nat._≤ Fin.toℕ j) (Nat.+-assoc a (sum B₁') 1) h))

-- 𝐒.lwk inserts a slot at the same flat position `sum B₁ + 1` (over the FULL scope).
𝐒lwk-lo : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            Fin.toℕ x Nat.< sum B₁ + 1 →
            Fin.toℕ (𝐓R.SplitRenamings.lwk B₁ B₂ B {b₁} {m} x) ≡ Fin.toℕ x
𝐒lwk-lo B₁ B₂ B {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ ↑*-lo weakenᵣ (sum B₁ + 1) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁ + 1
        lt′ = subst (Nat._< sum B₁ + 1) (sym (Fin.toℕ-cast _ x)) lt

𝐒lwk-hi : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            sum B₁ + 1 Nat.≤ Fin.toℕ x →
            Fin.toℕ (𝐓R.SplitRenamings.lwk B₁ B₂ B {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒lwk-hi B₁ B₂ B {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ ↑*-hi weakenᵣ (sum B₁ + 1) (Fin.cast _ x) h′
  ■ cong (sum B₁ + 1 +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ (sum B₁ + 1)) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁ + 1) (Fin.toℕ x Nat.∸ (sum B₁ + 1))
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ + 1 Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ + 1 Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

-- The grown bind group has exactly one more data slot.
sum-lwk : ∀ (B₁ : 𝐓.BindGroup) {b₁ B₂} →
          sum (B₁ ++ suc (suc b₁) ∷ B₂) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂))
sum-lwk B₁ {b₁} {B₂} = sum-++ B₁ (suc (suc b₁) ∷ B₂)
                     ■ Nat.+-suc (sum B₁) (sum (suc b₁ ∷ B₂))
                     ■ cong suc (sym (sum-++ B₁ (suc b₁ ∷ B₂)))

sB₁≤sumC₁ : ∀ (B₁ : 𝐓.BindGroup) {b₁ B₂} → sum B₁ + 1 Nat.≤ sum (B₁ ++ suc b₁ ∷ B₂)
sB₁≤sumC₁ B₁ {b₁} {B₂} =
  subst (sum B₁ + 1 Nat.≤_) (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (Nat.+-monoʳ-≤ (sum B₁) (Nat.s≤s Nat.z≤n))

-- 𝐒.lwk vs the data-level dlwk on the three regions of the leaf domain (data | B | σ).
P1 : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
     𝐓R.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
     ≡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1 B₁ B₂ B {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁ + 1
... | yes lt = Fin.toℕ-injective
      ( 𝐒lwk-lo B₁ B₂ B _ (subst (Nat._< sum B₁ + 1) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ dlwk-lo B₁ b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ dlwk-hi B₁ b₁ B₂ d h≤) )
  where h≤ : sum B₁ + 1 Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d) (sum B)

P2 : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (w : 𝔽 (sum B)) →
     𝐓R.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m)
     ≡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m
P2 B₁ B₂ B {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁≤sumC₁ B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-lwk B₁)

P3 : ∀ (B₁ B₂ B : 𝐓.BindGroup) {b₁ m : ℕ} (u : 𝔽 m) →
     𝐓R.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u)
     ≡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) ↑ʳ u
P3 B₁ B₂ B {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁≤sumC₁ B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-lwk B₁)

-- THE CRUX (O1) — positional characterisation of the canonical leaf at the split
-- handle.  canonₛ (B₁ ++ suc b₁ ∷ B₂) cc at position `sum B₁` (= the (length B₁)-th
-- chain's FIRST handle) is a channel triple `(a ⊗ `x) ⊗ c`.  Existential in (a,x,c):
-- the tail c is K`unit on the last chain but a junction variable otherwise, and
-- RU-LSplit treats it opaquely.  Proof = induction on B₁ (TODO):
--   • B₁ = []  → position 0F (sum-++ [] _ = refl); split on B₂ ([] vs b∷B, the latter
--                via subst-Π) and read off head (Ubₛ-head) of the suc b₁ chain.
--   • B₁ = a∷B₁' → canonₛ peels chain a; position a+sum B₁' lands in the recursive
--                canonₛ (B₁'++…) part; recurse (threaded cc-r, ↑ʳ/splitAt + subst-Π).
canonₛ-handle : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
  Σ[ x ∈ 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
    canonₛ (B₁ ++ suc b₁ ∷ B₂) cc
      (Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F))
      ≡ (a ⊗ (` x)) ⊗ c
canonₛ-handle []        (e₁ , x , e₂) zero     []      = e₁ , x , e₂ , refl
canonₛ-handle []        (e₁ , x , e₂) (suc b₁) []      = e₁ , x , K `unit , refl
canonₛ-handle []        (e₁ , x , e₂) zero     (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , subst Tm eq e₂′ ,
  ( subst-Π eq g 0F
  ■ subst-⊗ eq (A ⊗ (` X)) e₂′
  ■ cong (_⊗ subst Tm eq e₂′) (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) )
  where
    sB = syncs (b ∷ B)
    eq = +-suc sB _
    A  = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    X  = weaken* ⦃ Kᵣ ⦄ sB (suc x)
    e₂′ = (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB
    g  = Ubₛ 1 (A , X , e₂′) ++ₛ canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
canonₛ-handle []        (e₁ , x , e₂) (suc b₁) (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , subst Tm eq (K `unit) ,
  ( subst-Π eq g 0F
  ■ subst-⊗ eq (A ⊗ (` X)) (K `unit)
  ■ cong (_⊗ subst Tm eq (K `unit)) (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) )
  where
    sB = syncs (b ∷ B)
    eq = +-suc sB _
    A  = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    X  = weaken* ⦃ Kᵣ ⦄ sB (suc x)
    g  = Ubₛ (suc (suc b₁)) (A , X , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ++ₛ canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
canonₛ-handle (a ∷ [])       (e₁ , x , e₂) b₁ B₂
  with canonₛ-handle [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , rp =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ ,
  ( subst-Π eq g P
  ■ cong (subst Tm eq)
      ( cong g (pos-split a [] b₁ B₂)
      ■ cong [ Ubₛ a cc-i , canonₛ (suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ Q)
      ■ rp )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) )
  where
    sT = syncs (suc b₁ ∷ B₂)
    eq = +-suc sT _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT , weaken* ⦃ Kᵣ ⦄ sT (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT )
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (suc b₁ ∷ B₂) cc-r
    P  = Fin.cast (sym (sum-++ (a ∷ []) (suc b₁ ∷ B₂))) (sum (a ∷ []) ↑ʳ 0F)
    Q  = Fin.cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F)
canonₛ-handle (a ∷ d ∷ B₁″)  (e₁ , x , e₂) b₁ B₂
  with canonₛ-handle (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , rp =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ ,
  ( subst-Π eq g P
  ■ cong (subst Tm eq)
      ( cong g (pos-split a (d ∷ B₁″) b₁ B₂)
      ■ cong [ Ubₛ a cc-i , canonₛ (d ∷ B₁″ ++ suc b₁ ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ Q)
      ■ rp )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) )
  where
    sT = syncs (d ∷ B₁″ ++ suc b₁ ∷ B₂)
    eq = +-suc sT _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT , weaken* ⦃ Kᵣ ⦄ sT (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT )
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (d ∷ B₁″ ++ suc b₁ ∷ B₂) cc-r
    P  = Fin.cast (sym (sum-++ (a ∷ d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (a ∷ d ∷ B₁″) ↑ʳ 0F)
    Q  = Fin.cast (sym (sum-++ (d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 0F)

-- The canonical leaf substitution is a value substitution (every chain handle is a
-- channel triple of values), so frame-plug* can fire on it.
VSub-Ubₛ : ∀ b {M} (cc : UChan M) → VChan cc → VSub (Ubₛ b cc)
VSub-Ubₛ zero          cc            Vcc          ()
VSub-Ubₛ (suc zero)    (e₁ , x , e₂) (Ve₁ , Ve₂) = ∷ₛ-VSub (V-⊗ (V-⊗ Ve₁ V-`) Ve₂) (λ ())
VSub-Ubₛ (suc (suc b)) (e₁ , x , e₂) (Ve₁ , Ve₂) =
  ∷ₛ-VSub (V-⊗ (V-⊗ Ve₁ V-`) V-K) (VSub-Ubₛ (suc b) (K `unit , x , e₂) (V-K , Ve₂))

VSub-canonₛ : ∀ (B : 𝐓.BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc          = λ ()
VSub-canonₛ (c ∷ [])      (e₁ , x , e₂) (Ve₁ , Ve₂) =
  ++ₛ-VSub (VSub-Ubₛ c (e₁ , x , e₂) (Ve₁ , Ve₂)) (λ ())
VSub-canonₛ (c ∷ (b ∷ B)) (e₁ , x , e₂) (Ve₁ , Ve₂) =
  VSub-subst (+-suc (syncs (b ∷ B)) _)
    (++ₛ-VSub (VSub-Ubₛ c _ (Ve₁ ⋯ᵛ weakenᵣ ⋯ᵛ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) , V-`))
              (VSub-canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) (V-` , Ve₂ ⋯ᵛ weakenᵣ)))

-- lsplit grows one borrow on the affected chain, which leaves the chain COUNT (hence
-- syncs and Flags) unchanged: ϕ[suc b₁] = ϕ[suc (suc b₁)] = unset.
syncs-lwk : ∀ (B₁ : 𝐓.BindGroup) {b₁ : ℕ} {B₂ : 𝐓.BindGroup} →
            syncs (B₁ ++ suc b₁ ∷ B₂) ≡ syncs (B₁ ++ suc (suc b₁) ∷ B₂)
syncs-lwk []            {b₁} {[]}      = refl
syncs-lwk []            {b₁} {b' ∷ B'} = refl
syncs-lwk (a ∷ [])      {b₁} {B₂}      = cong suc (syncs-lwk [] {b₁} {B₂})
syncs-lwk (a ∷ d ∷ B₁″) {b₁} {B₂}      = cong suc (syncs-lwk (d ∷ B₁″) {b₁} {B₂})

-- The two handles of the GROWN chain (suc (suc b₁)) at positions inj 0F / inj 1F: the
-- RU-LSplit output's two triples.  Mirror of canonₛ-handle (induction on B₁), two positions.
canonₛ-sib : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
  Σ[ x ∈ 𝔽 (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
    (canonₛ (B₁ ++ suc (suc b₁) ∷ B₂) cc
       (Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 0F))
       ≡ (a ⊗ (` x)) ⊗ K `unit)
  × (canonₛ (B₁ ++ suc (suc b₁) ∷ B₂) cc
       (Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 1F))
       ≡ (K `unit ⊗ (` x)) ⊗ c)
canonₛ-sib []        (e₁ , x , e₂) zero     []      = e₁ , x , e₂ , refl , refl
canonₛ-sib []        (e₁ , x , e₂) (suc b₁) []      = e₁ , x , K `unit , refl , refl
canonₛ-sib []        (e₁ , x , e₂) zero     (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , subst Tm eq e₂′ ,
  ( subst-Π eq g 0F ■ subst-⊗ eq (A ⊗ (` X)) (K `unit)
  ■ cong₂ _⊗_ (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) (subst-Kunit eq) ) ,
  ( subst-Π eq g 1F ■ subst-⊗ eq (K `unit ⊗ (` X)) e₂′
  ■ cong (_⊗ subst Tm eq e₂′) (subst-⊗ eq (K `unit) (` X) ■ cong₂ _⊗_ (subst-Kunit eq) (subst-` eq X)) )
  where
    sB = syncs (b ∷ B)
    eq = +-suc sB _
    A   = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    X   = weaken* ⦃ Kᵣ ⦄ sB (suc x)
    e₂′ = (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB
    g   = Ubₛ 2 (A , X , e₂′) ++ₛ canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
canonₛ-sib []        (e₁ , x , e₂) (suc b₁) (b ∷ B) =
  subst Tm eq A , subst 𝔽 eq X , subst Tm eq (K `unit) ,
  ( subst-Π eq g 0F ■ subst-⊗ eq (A ⊗ (` X)) (K `unit)
  ■ cong₂ _⊗_ (subst-⊗ eq A (` X) ■ cong (subst Tm eq A ⊗_) (subst-` eq X)) (subst-Kunit eq) ) ,
  ( subst-Π eq g 1F ■ subst-⊗ eq (K `unit ⊗ (` X)) (K `unit)
  ■ cong (_⊗ subst Tm eq (K `unit)) (subst-⊗ eq (K `unit) (` X) ■ cong₂ _⊗_ (subst-Kunit eq) (subst-` eq X)) )
  where
    sB = syncs (b ∷ B)
    eq = +-suc sB _
    A   = e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    X   = weaken* ⦃ Kᵣ ⦄ sB (suc x)
    g   = Ubₛ (suc (suc (suc b₁))) (A , X , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ++ₛ canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
canonₛ-sib (a ∷ [])       (e₁ , x , e₂) b₁ B₂
  with canonₛ-sib [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , rp0 , rp1 =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ ,
  ( subst-Π eq g (cast0 (sum (a ∷ []) ↑ʳ 0F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a [] (suc (suc b₁)) B₂ 0F)
      ■ cong [ Ubₛ a cc-i , canonₛ (suc (suc b₁) ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp0 )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) (K `unit)
  ■ cong₂ _⊗_ (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) (subst-Kunit eq) ) ,
  ( subst-Π eq g (cast0 (sum (a ∷ []) ↑ʳ 1F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a [] (suc (suc b₁)) B₂ 1F)
      ■ cong [ Ubₛ a cc-i , canonₛ (suc (suc b₁) ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp1 )
  ■ subst-⊗ eq (K `unit ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq (K `unit) (` x′) ■ cong₂ _⊗_ (subst-Kunit eq) (subst-` eq x′)) )
  where
    sB = syncs (suc (suc b₁) ∷ B₂)
    eq = +-suc sB _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (suc (suc b₁) ∷ B₂) cc-r
    cast0 = Fin.cast (sym (sum-++ (a ∷ []) (suc (suc b₁) ∷ B₂)))
canonₛ-sib (a ∷ d ∷ B₁″)  (e₁ , x , e₂) b₁ B₂
  with canonₛ-sib (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a′ , x′ , c′ , rp0 , rp1 =
  subst Tm eq a′ , subst 𝔽 eq x′ , subst Tm eq c′ ,
  ( subst-Π eq g (cast0 (sum (a ∷ d ∷ B₁″) ↑ʳ 0F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a (d ∷ B₁″) (suc (suc b₁)) B₂ 0F)
      ■ cong [ Ubₛ a cc-i , canonₛ (d ∷ B₁″ ++ suc (suc b₁) ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp0 )
  ■ subst-⊗ eq (a′ ⊗ (` x′)) (K `unit)
  ■ cong₂ _⊗_ (subst-⊗ eq a′ (` x′) ■ cong (subst Tm eq a′ ⊗_) (subst-` eq x′)) (subst-Kunit eq) ) ,
  ( subst-Π eq g (cast0 (sum (a ∷ d ∷ B₁″) ↑ʳ 1F))
  ■ cong (subst Tm eq)
      ( cong g (pos-split-gen a (d ∷ B₁″) (suc (suc b₁)) B₂ 1F)
      ■ cong [ Ubₛ a cc-i , canonₛ (d ∷ B₁″ ++ suc (suc b₁) ∷ B₂) cc-r ]′ (Fin.splitAt-↑ʳ a _ _) ■ rp1 )
  ■ subst-⊗ eq (K `unit ⊗ (` x′)) c′
  ■ cong (_⊗ subst Tm eq c′) (subst-⊗ eq (K `unit) (` x′) ■ cong₂ _⊗_ (subst-Kunit eq) (subst-` eq x′)) )
  where
    sB = syncs (d ∷ B₁″ ++ suc (suc b₁) ∷ B₂)
    eq = +-suc sB _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i ++ₛ canonₛ (d ∷ B₁″ ++ suc (suc b₁) ∷ B₂) cc-r
    cast0 = Fin.cast (sym (sum-++ (a ∷ d ∷ B₁″) (suc (suc b₁) ∷ B₂)))

-- Combine two transports; align transports along equal (ℕ-set) proofs; and the chain
-- coherence: Ubₛ of a syncs-transported channel is the transport of Ubₛ (free by J).
ss : ∀ {A : Set} {F : A → Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) {t : F x} →
     subst F q (subst F p t) ≡ subst F (p ■ q) t
ss refl refl = refl

uipℕ : {x y : ℕ} (p q : x ≡ y) → p ≡ q
uipℕ refl refl = refl

ubCoh : ∀ {N} (a : ℕ) (e₁ : Tm N) (x : 𝔽 N) {s s′ : ℕ} (eq : s ≡ s′) (p : 𝔽 a) →
        subst Tm (cong (_+ suc N) eq)
          (Ubₛ a ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ s , weaken* ⦃ Kᵣ ⦄ s (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ s ) p)
        ≡ Ubₛ a ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ s′ , weaken* ⦃ Kᵣ ⦄ s′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ s′ ) p
ubCoh a e₁ x refl p = refl

-- Transport glue shared by the step cases: lift a leaf equation (post canonₛ +-suc subst)
-- through the chain-peel, aligning the +-suc / syncs-lwk transports by ℕ-set UIP.
chainLwk : ∀ {N} {sT sT′ : ℕ} (sl : sT ≡ sT′)
           {DA DB : ℕ} (g : 𝔽 DA → Tm (sT + suc N)) (g′ : 𝔽 DB → Tm (sT′ + suc N))
           (i : 𝔽 DA) (di : 𝔽 DB) →
           subst Tm (cong (_+ suc N) sl) (g i) ≡ g′ di →
           subst Tm (cong (_+ N) (cong suc sl)) (subst (λ z → 𝔽 DA → Tm z) (+-suc sT N) g i)
           ≡ subst (λ z → 𝔽 DB → Tm z) (+-suc sT′ N) g′ di
chainLwk {N} {sT} {sT′} sl g g′ i di innerT =
    cong (subst Tm (cong (_+ N) (cong suc sl))) (subst-Π (+-suc sT N) g i)
  ■ ss (+-suc sT N) (cong (_+ N) (cong suc sl))
  ■ cong (λ pf → subst Tm pf (g i)) (uipℕ _ _)
  ■ sym (ss (cong (_+ suc N) sl) (+-suc sT′ N))
  ■ cong (subst Tm (+-suc sT′ N)) innerT
  ■ sym (subst-Π (+-suc sT′ N) g′ di)

-- canonₛ-handle and canonₛ-sib are built by the SAME induction with identical witnesses,
-- so their (a,x,c) agree modulo the syncs re-indexing.  This relates the LHS lsplit handle
-- to the two RHS handles of the grown chain.
hc-sib-agree : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup) →
  (subst Tm (cong (_+ N) (syncs-lwk B₁)) (proj₁ (canonₛ-handle B₁ cc b₁ B₂)) ≡ proj₁ (canonₛ-sib B₁ cc b₁ B₂))
  × (subst 𝔽 (cong (_+ N) (syncs-lwk B₁)) (proj₁ (proj₂ (canonₛ-handle B₁ cc b₁ B₂))) ≡ proj₁ (proj₂ (canonₛ-sib B₁ cc b₁ B₂)))
  × (subst Tm (cong (_+ N) (syncs-lwk B₁)) (proj₁ (proj₂ (proj₂ (canonₛ-handle B₁ cc b₁ B₂)))) ≡ proj₁ (proj₂ (proj₂ (canonₛ-sib B₁ cc b₁ B₂))))
hc-sib-agree []        (e₁ , x , e₂) zero     []      = refl , refl , refl
hc-sib-agree []        (e₁ , x , e₂) (suc b₁) []      = refl , refl , refl
hc-sib-agree []        (e₁ , x , e₂) zero     (b ∷ B) = refl , refl , refl
hc-sib-agree []        (e₁ , x , e₂) (suc b₁) (b ∷ B) = refl , refl , refl
hc-sib-agree (a ∷ [])       {N} (e₁ , x , e₂) b₁ B₂
  with canonₛ-handle [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
     | canonₛ-sib    [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
     | hc-sib-agree  [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a'r , x'r , c'r , _ | a_r , x_r , c_r , _ , _ | ag1 , ag2 , ag3 =
      compT a'r a_r ag1 , compF x'r x_r ag2 , compT c'r c_r ag3
  where
    sT  = syncs (suc b₁ ∷ B₂)
    sT2 = syncs (suc (suc b₁) ∷ B₂)
    sl  = syncs-lwk [] {b₁} {B₂}
    compT : (h : Tm (sT + suc N)) (s : Tm (sT2 + suc N)) → subst Tm (cong (_+ suc N) sl) h ≡ s →
            subst Tm (cong (_+ N) (cong suc sl)) (subst Tm (+-suc sT N) h) ≡ subst Tm (+-suc sT2 N) s
    compT h s ag = ss (+-suc sT N) (cong (_+ N) (cong suc sl)) ■ cong (λ pf → subst Tm pf h) (uipℕ _ _)
                 ■ sym (ss (cong (_+ suc N) sl) (+-suc sT2 N)) ■ cong (subst Tm (+-suc sT2 N)) ag
    compF : (h : 𝔽 (sT + suc N)) (s : 𝔽 (sT2 + suc N)) → subst 𝔽 (cong (_+ suc N) sl) h ≡ s →
            subst 𝔽 (cong (_+ N) (cong suc sl)) (subst 𝔽 (+-suc sT N) h) ≡ subst 𝔽 (+-suc sT2 N) s
    compF h s ag = ss (+-suc sT N) (cong (_+ N) (cong suc sl)) ■ cong (λ pf → subst 𝔽 pf h) (uipℕ _ _)
                 ■ sym (ss (cong (_+ suc N) sl) (+-suc sT2 N)) ■ cong (subst 𝔽 (+-suc sT2 N)) ag
hc-sib-agree (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂
  with canonₛ-handle (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
     | canonₛ-sib    (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
     | hc-sib-agree  (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | a'r , x'r , c'r , _ | a_r , x_r , c_r , _ , _ | ag1 , ag2 , ag3 =
      compT a'r a_r ag1 , compF x'r x_r ag2 , compT c'r c_r ag3
  where
    sT  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sT2 = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    sl  = syncs-lwk (d ∷ B₁″) {b₁} {B₂}
    compT : (h : Tm (sT + suc N)) (s : Tm (sT2 + suc N)) → subst Tm (cong (_+ suc N) sl) h ≡ s →
            subst Tm (cong (_+ N) (cong suc sl)) (subst Tm (+-suc sT N) h) ≡ subst Tm (+-suc sT2 N) s
    compT h s ag = ss (+-suc sT N) (cong (_+ N) (cong suc sl)) ■ cong (λ pf → subst Tm pf h) (uipℕ _ _)
                 ■ sym (ss (cong (_+ suc N) sl) (+-suc sT2 N)) ■ cong (subst Tm (+-suc sT2 N)) ag
    compF : (h : 𝔽 (sT + suc N)) (s : 𝔽 (sT2 + suc N)) → subst 𝔽 (cong (_+ suc N) sl) h ≡ s →
            subst 𝔽 (cong (_+ N) (cong suc sl)) (subst 𝔽 (+-suc sT N) h) ≡ subst 𝔽 (+-suc sT2 N) s
    compF h s ag = ss (+-suc sT N) (cong (_+ N) (cong suc sl)) ■ cong (λ pf → subst 𝔽 pf h) (uipℕ _ _)
                 ■ sym (ss (cong (_+ suc N) sl) (+-suc sT2 N)) ■ cong (subst 𝔽 (+-suc sT2 N)) ag

-- canonₛ is invariant under growing the split chain's borrow, EXCEPT at the consumed
-- handle (position `sum B₁`): everywhere else the canonical leaf agrees with the grown
-- group's leaf at the inserted position `dlwk i`.  This is the off-handle part of the
-- lwk-identity; the consumed handle is excluded by the typing hypothesis (it is linear).
canonₛ-lwk : ∀ (B₁ : 𝐓.BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : 𝐓.BindGroup)
             (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F) →
             subst Tm (cong (_+ N) (syncs-lwk B₁)) (canonₛ (B₁ ++ suc b₁ ∷ B₂) cc i)
             ≡ canonₛ (B₁ ++ suc (suc b₁) ∷ B₂) cc (dlwk B₁ b₁ B₂ i)
canonₛ-lwk []            cc b₁ []      i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
... | suc i′ with splitAt b₁ i′
...   | inj₁ k′ = Ubₛ-lwk b₁ cc k′
...   | inj₂ ()
canonₛ-lwk []            (e₁ , x , e₂) b₁ (b ∷ B) i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
... | suc i′ =
      subst-Π eqs gL (suc i′)
    ■ cong (subst Tm eqs) inner
    ■ sym (subst-Π eqs gR (suc (suc i′)))
  where
    sB′  = syncs (b ∷ B)
    eqs  = +-suc sB′ _
    cc-i = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB′ , weaken* ⦃ Kᵣ ⦄ sB′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB′ )
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    gL   = Ubₛ (suc b₁) cc-i ++ₛ canonₛ (b ∷ B) cc-r
    gR   = Ubₛ (suc (suc b₁)) cc-i ++ₛ canonₛ (b ∷ B) cc-r
    inner : gL (suc i′) ≡ gR (suc (suc i′))
    inner with splitAt b₁ i′
    ... | inj₁ k′ = Ubₛ-lwk b₁ cc-i k′
    ... | inj₂ q  = refl
canonₛ-lwk (a ∷ [])      {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-lwk [] ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | rec with splitAt a i in seq
... | inj₁ p = chainLwk sl g g′ i (p ↑ˡ sum (suc (suc b₁) ∷ B₂))
                 ( cong (subst Tm (cong (_+ suc N) sl)) (cong GL seq)
                 ■ ubCoh a e₁ x sl p
                 ■ sym (cong G′ (Fin.splitAt-↑ˡ a p (sum (suc (suc b₁) ∷ B₂)))) )
  where
    sT  = syncs (suc b₁ ∷ B₂)
    sT′ = syncs (suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk [] {b₁} {B₂}
    cc-i  = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT  , weaken* ⦃ Kᵣ ⦄ sT  (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT  )
    cc-i′ = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT′ , weaken* ⦃ Kᵣ ⦄ sT′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT′ )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i  ++ₛ canonₛ (suc b₁ ∷ B₂) cc-r
    g′ = Ubₛ a cc-i′ ++ₛ canonₛ (suc (suc b₁) ∷ B₂) cc-r
    GL = [ Ubₛ a cc-i  , canonₛ (suc b₁ ∷ B₂) cc-r ]′
    G′ = [ Ubₛ a cc-i′ , canonₛ (suc (suc b₁) ∷ B₂) cc-r ]′
... | inj₂ r = chainLwk sl g g′ i (a ↑ʳ dlwk [] b₁ B₂ r)
                 ( cong (subst Tm (cong (_+ suc N) sl)) (cong GL seq)
                 ■ rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum (suc b₁ ∷ B₂)) i)
                                    ■ cong (Fin.join a (sum (suc b₁ ∷ B₂))) seq
                                    ■ cong (a ↑ʳ_) r≡
                                    ■ sym (pos-split a [] b₁ B₂) ))
                 ■ sym (cong G′ (Fin.splitAt-↑ʳ a (sum (suc (suc b₁) ∷ B₂)) (dlwk [] b₁ B₂ r))) )
  where
    sT  = syncs (suc b₁ ∷ B₂)
    sT′ = syncs (suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk [] {b₁} {B₂}
    cc-i  = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT  , weaken* ⦃ Kᵣ ⦄ sT  (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT  )
    cc-i′ = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT′ , weaken* ⦃ Kᵣ ⦄ sT′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT′ )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i  ++ₛ canonₛ (suc b₁ ∷ B₂) cc-r
    g′ = Ubₛ a cc-i′ ++ₛ canonₛ (suc (suc b₁) ∷ B₂) cc-r
    GL = [ Ubₛ a cc-i  , canonₛ (suc b₁ ∷ B₂) cc-r ]′
    G′ = [ Ubₛ a cc-i′ , canonₛ (suc (suc b₁) ∷ B₂) cc-r ]′
canonₛ-lwk (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-lwk (d ∷ B₁″) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) b₁ B₂
... | rec with splitAt a i in seq
... | inj₁ p = chainLwk sl g g′ i (p ↑ˡ sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂))
                 ( cong (subst Tm (cong (_+ suc N) sl)) (cong GL seq)
                 ■ ubCoh a e₁ x sl p
                 ■ sym (cong G′ (Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)))) )
  where
    sT  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk (d ∷ B₁″) {b₁} {B₂}
    cc-i  = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT  , weaken* ⦃ Kᵣ ⦄ sT  (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT  )
    cc-i′ = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT′ , weaken* ⦃ Kᵣ ⦄ sT′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT′ )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i  ++ₛ canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r
    g′ = Ubₛ a cc-i′ ++ₛ canonₛ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r
    GL = [ Ubₛ a cc-i  , canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ Ubₛ a cc-i′ , canonₛ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r ]′
... | inj₂ r = chainLwk sl g g′ i (a ↑ʳ dlwk (d ∷ B₁″) b₁ B₂ r)
                 ( cong (subst Tm (cong (_+ suc N) sl)) (cong GL seq)
                 ■ rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) i)
                                    ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) seq
                                    ■ cong (a ↑ʳ_) r≡
                                    ■ sym (pos-split a (d ∷ B₁″) b₁ B₂) ))
                 ■ sym (cong G′ (Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) (dlwk (d ∷ B₁″) b₁ B₂ r))) )
  where
    sT  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk (d ∷ B₁″) {b₁} {B₂}
    cc-i  = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT  , weaken* ⦃ Kᵣ ⦄ sT  (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT  )
    cc-i′ = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sT′ , weaken* ⦃ Kᵣ ⦄ sT′ (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sT′ )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    g  = Ubₛ a cc-i  ++ₛ canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r
    g′ = Ubₛ a cc-i′ ++ₛ canonₛ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r
    GL = [ Ubₛ a cc-i  , canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ Ubₛ a cc-i′ , canonₛ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r ]′

-- Transport a φ^-prefix along an equality of its depth (bridges syncs C₁ ↔ syncs C₁').
φ^-cast : ∀ {k k′ N} (eq : k ≡ k′) (P : 𝐔.Proc (k + N)) →
          φ^ k P ≡ φ^ k′ (subst (λ j → 𝐔.Proc (j + N)) eq P)
φ^-cast refl P = refl

-- Push a depth-transport subst through φ^ / ν / ∥ (all refl on the equality).
subst-φ^ : ∀ d {N k k′} (eq : k ≡ k′) (W : 𝐔.Proc (d + (k + N))) →
           subst (λ j → 𝐔.Proc (j + N)) eq (φ^ d W)
           ≡ φ^ d (subst (λ j → 𝐔.Proc (d + (j + N))) eq W)
subst-φ^ d refl W = refl

subst-νf : ∀ {k k′} (f : ℕ → ℕ) (eq : k ≡ k′) (Z : 𝐔.Proc (2 + f k)) →
           subst (λ j → 𝐔.Proc (f j)) eq (𝐔.ν Z)
           ≡ 𝐔.ν (subst (λ j → 𝐔.Proc (2 + f j)) eq Z)
subst-νf f refl Z = refl

subst-∥f : ∀ {k k′} (f : ℕ → ℕ) (eq : k ≡ k′) (A B : 𝐔.Proc (f k)) →
           subst (λ j → 𝐔.Proc (f j)) eq (A 𝐔.∥ B)
           ≡ subst (λ j → 𝐔.Proc (f j)) eq A 𝐔.∥ subst (λ j → 𝐔.Proc (f j)) eq B
subst-∥f f refl A B = refl

-- A depth-transport commutes past a (uniform-in-the-index) process renaming — free by J.
transport-⋯ₚ : ∀ {k k′} (f g : ℕ → ℕ) (ρ : ∀ j → f j →ᵣ g j) (eq : k ≡ k′) (X : 𝐔.Proc (f k)) →
                subst (λ j → 𝐔.Proc (g j)) eq (X 𝐔.⋯ₚ ρ k)
                ≡ (subst (λ j → 𝐔.Proc (f j)) eq X) 𝐔.⋯ₚ ρ k′
transport-⋯ₚ f g ρ refl X = refl

-- Flags is parametric in its base — transporting the base is the identity (free by J).
Flags-base-nat : ∀ (B : 𝐓.BindGroup) {k k′} (f : ℕ → ℕ) (eq : k ≡ k′) →
                 subst (λ j → 𝐔.Proc (syncs B + f j)) eq (Flags {f k} B) ≡ Flags {f k′} B
Flags-base-nat B f refl = refl

-- Likewise the translation is parametric in its codomain index.
U-cod-transport : ∀ (P : 𝐓.Proc m) {k k′} (f : ℕ → ℕ) (eq : k ≡ k′) (σ : m →ₛ f k) →
                  subst (λ j → 𝐔.Proc (f j)) eq (U[ P ] σ)
                  ≡ U[ P ] (subst (λ j → m →ₛ f j) eq σ)
U-cod-transport P f refl σ = refl

-- One Flags layer, transported along an equality of the inner syncs depth (J on eq).
flagsStep : ∀ {N} (k k′ : ℕ) (eq : k ≡ k′) (flag : 𝐔.Flag)
            (Q : 𝐔.Proc (k + suc N)) (Q′ : 𝐔.Proc (k′ + suc N)) →
            subst 𝐔.Proc (cong (_+ suc N) eq) Q ≡ Q′ →
            subst 𝐔.Proc (cong (_+ N) (cong suc eq))
              (subst 𝐔.Proc (+-suc k N) ((weaken* ⦃ Kᵣ ⦄ k 0F 𝐔.↦ flag) 𝐔.∥ Q))
            ≡ subst 𝐔.Proc (+-suc k′ N) ((weaken* ⦃ Kᵣ ⦄ k′ 0F 𝐔.↦ flag) 𝐔.∥ Q′)
flagsStep k k refl flag Q Q′ qeq =
  cong (subst 𝐔.Proc (+-suc k _)) (cong ((weaken* ⦃ Kᵣ ⦄ k 0F 𝐔.↦ flag) 𝐔.∥_) qeq)

-- Flags is invariant under growing the affected chain's borrow (ϕ unchanged), modulo the
-- syncs re-indexing.
Flags-lwk : ∀ (B₁ : 𝐓.BindGroup) {N b₁ B₂} →
            subst 𝐔.Proc (cong (_+ N) (syncs-lwk B₁)) (Flags (B₁ ++ suc b₁ ∷ B₂))
            ≡ Flags (B₁ ++ suc (suc b₁) ∷ B₂)
Flags-lwk []            {N} {b₁} {[]}      = refl
Flags-lwk []            {N} {b₁} {b′ ∷ B′} = refl
Flags-lwk (a ∷ [])      {N} {b₁} {B₂}      = flagsStep _ _ (syncs-lwk [] {b₁} {B₂}) ϕ[ a ] _ _ (Flags-lwk [] {suc N} {b₁} {B₂})
Flags-lwk (a ∷ d ∷ B₁″) {N} {b₁} {B₂}      = flagsStep _ _ (syncs-lwk (d ∷ B₁″) {b₁} {B₂}) ϕ[ a ] _ _ (Flags-lwk (d ∷ B₁″) {suc N} {b₁} {B₂})

-- Re-index a term transport between `cong (_+ N)` and the explicit motive (free by J).
subst-cong+ : ∀ {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
              subst Tm (cong (_+ N) eq) t ≡ subst (λ j → Tm (j + N)) eq t
subst-cong+ refl t = refl

subst-cong+P : ∀ {a b N} (eq : a ≡ b) (t : 𝐔.Proc (a + N)) →
               subst 𝐔.Proc (cong (_+ N) eq) t ≡ subst (λ j → 𝐔.Proc (j + N)) eq t
subst-cong+P refl t = refl

-- Push a codomain transport through the thread constructor (free by J).
subst-⟪⟫ : ∀ (f : ℕ → ℕ) {a b} (eq : a ≡ b) (t : Tm (f a)) →
           subst (λ j → 𝐔.Proc (f j)) eq (𝐔.⟪ t ⟫) ≡ 𝐔.⟪ subst (λ j → Tm (f j)) eq t ⟫
subst-⟪⟫ f refl t = refl

-- Apply a codomain transport pointwise to a substitution (free by J).
subst-app : ∀ {D} (f : ℕ → ℕ) {a b} (eq : a ≡ b) (σ : D →ₛ f a) (y : 𝔽 D) →
            subst (λ j → D →ₛ f j) eq σ y ≡ subst (λ j → Tm (f j)) eq (σ y)
subst-app f refl σ y = refl

-- A codomain transport commutes past `⋯ weaken* sB` (free by J).
subst-wkB : ∀ (sB : ℕ) {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
            subst (λ j → Tm (sB + (j + N))) eq (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
            ≡ (subst (λ j → Tm (j + N)) eq t) ⋯ weaken* ⦃ Kᵣ ⦄ sB
subst-wkB sB refl t = refl

-- A codomain transport commutes past a (uniform-in-the-index) term renaming — free by J.
transport-⋯T : ∀ {k k′} (f g : ℕ → ℕ) (ρ : ∀ j → f j →ᵣ g j) (eq : k ≡ k′) (t : Tm (f k)) →
               subst (λ j → Tm (g j)) eq (t ⋯ ρ k)
               ≡ (subst (λ j → Tm (f j)) eq t) ⋯ ρ k′
transport-⋯T f g ρ refl t = refl

-- The 𝔽-level analogues of the above (all free by J): transports commute past a renaming
-- application, past weaken*, and re-index between cong(_+N) and the explicit motive; plus
-- distributing a codomain transport over the term constructors.
transport-ρ𝔽 : ∀ {k k′} (f g : ℕ → ℕ) (ρ : ∀ j → f j →ᵣ g j) (eq : k ≡ k′) (z : 𝔽 (f k)) →
               subst (λ j → 𝔽 (g j)) eq (ρ k z) ≡ ρ k′ (subst (λ j → 𝔽 (f j)) eq z)
transport-ρ𝔽 f g ρ refl z = refl

subst-wk𝔽 : ∀ (sB : ℕ) {a b N} (eq : a ≡ b) (z : 𝔽 (a + N)) →
            subst (λ j → 𝔽 (sB + (j + N))) eq (weaken* ⦃ Kᵣ ⦄ sB z)
            ≡ weaken* ⦃ Kᵣ ⦄ sB (subst (λ j → 𝔽 (j + N)) eq z)
subst-wk𝔽 sB refl z = refl

subst-cong+𝔽 : ∀ {a b N} (eq : a ≡ b) (z : 𝔽 (a + N)) →
               subst 𝔽 (cong (_+ N) eq) z ≡ subst (λ j → 𝔽 (j + N)) eq z
subst-cong+𝔽 refl z = refl

subst-⊗f : ∀ (f : ℕ → ℕ) {a b} (eq : a ≡ b) (p r : Tm (f a)) →
           subst (λ j → Tm (f j)) eq (p ⊗ r)
           ≡ subst (λ j → Tm (f j)) eq p ⊗ subst (λ j → Tm (f j)) eq r
subst-⊗f f refl p r = refl

subst-`f : ∀ (f : ℕ → ℕ) {a b} (eq : a ≡ b) (z : 𝔽 (f a)) →
           subst (λ j → Tm (f j)) eq (` z) ≡ ` subst (λ j → 𝔽 (f j)) eq z
subst-`f f refl z = refl

subst-Kunit-f : ∀ (f : ℕ → ℕ) {a b} (eq : a ≡ b) →
                subst (λ j → Tm (f j)) eq (K `unit) ≡ K `unit
subst-Kunit-f f refl = refl

VSub-cod-subst : ∀ {D} (f : ℕ → ℕ) {a b} (eq : a ≡ b) {σ : D →ₛ f a} →
                 VSub σ → VSub (subst (λ j → D →ₛ f j) eq σ)
VSub-cod-subst f refl Vσ = Vσ

-- Push a codomain transport through frame plugging and through frame*-⋯ (free by J).
subst-frame-plug : ∀ (h : ℕ → ℕ) {a b} (eq : a ≡ b) (F : Frame* (h a)) (t : Tm (h a)) →
                   subst (λ j → Tm (h j)) eq (F [ t ]*)
                   ≡ (subst (λ j → Frame* (h j)) eq F) [ subst (λ j → Tm (h j)) eq t ]*
subst-frame-plug h refl F t = refl

-- Frame* (list) versions of frame-cong / frame-fusion-gen.
frame*-cong : (E : Frame* m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
              frame*-⋯ E ϕ Vϕ ≡ frame*-⋯ E ψ Vψ
frame*-cong []      Vϕ Vψ eq = refl
frame*-cong (F ∷ E) Vϕ Vψ eq = cong₂ _∷_ (frame-cong F Vϕ Vψ eq) (frame*-cong E Vϕ Vψ eq)

subst-frame* : ∀ {D} (h : ℕ → ℕ) {a b} (eq : a ≡ b) (E : Frame* D) (σ : D →ₛ h a) (Vσ : VSub σ)
               (Vσ′ : VSub (subst (λ j → D →ₛ h j) eq σ)) →
               subst (λ j → Frame* (h j)) eq (frame*-⋯ E σ Vσ)
               ≡ frame*-⋯ E (subst (λ j → D →ₛ h j) eq σ) Vσ′
subst-frame* h refl E σ Vσ Vσ′ = frame*-cong E Vσ Vσ′ (λ _ → refl)

frame*-fusion-gen : ∀ {m₁ p} (E : Frame* m) {ϕ : m →ᵣ m₁} {ξ : m₁ →ₛ p} (Vξ : VSub ξ)
                    (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                    frame*-⋯ (E ⋯ᶠ* ϕ) ξ Vξ ≡ frame*-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame*-fusion-gen []      Vξ Vϕξ = refl
frame*-fusion-gen (F ∷ E) {ϕ} Vξ Vϕξ =
  cong₂ _∷_ (frame-fusion-gen F (λ _ → V-`) Vξ Vϕξ) (frame*-fusion-gen E Vξ Vϕξ)

-- Swap the first of three nested parallel components past the second.
∥-swap-mid : ∀ {N} {A B C : 𝐔.Proc N} → (A 𝐔.∥ (B 𝐔.∥ C)) 𝐔.≋ (B 𝐔.∥ (A 𝐔.∥ C))
∥-swap-mid = 𝐔.∥-assoc ◅◅ 𝐔.∥-cong 𝐔.∥-comm ε ◅◅ Eq*.symmetric _ 𝐔.∥-assoc

-- Bring the redex thread R (the third leaf) to the front of the body, so RU-LSplit can
-- fire on ν (R ∥ Prest).  The exact Prest order is irrelevant — RU-LSplit's parallel
-- process is arbitrary.
reorder-front : ∀ {N} (Ap Bp Rp Sp : 𝐔.Proc N) →
                (Ap 𝐔.∥ (Bp 𝐔.∥ (Rp 𝐔.∥ Sp))) 𝐔.≋ (Rp 𝐔.∥ (Bp 𝐔.∥ (Ap 𝐔.∥ Sp)))
reorder-front Ap Bp Rp Sp =
     ∥-swap-mid
  ◅◅ 𝐔.∥-cong ε ∥-swap-mid
  ◅◅ ∥-swap-mid

U-lsplit : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {B₁ B₂ B : 𝐓.BindGroup} {b₁ : ℕ} {s : 𝕊 0}
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
                (𝐓.⟪ E [ K (`lsplit s) · (` 𝐒.inj 0F) ]* ⟫ 𝐓.∥ P) ] σ
             𝐔R.─→ₚ
           U[ 𝐓.ν (B₁ ++ suc (suc b₁) ∷ B₂) B
                (𝐓.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫
                 𝐓.∥ (P 𝐓.⋯ₚ 𝐒.lwk)) ] σ
-- ════════════════════════════════════════════════════════════════════════════
-- ROUTE (forward simulation for local channel split; VSub-only, no typing needed).
-- The body fires RU-LSplit, which needs scope `2+_` (the 2 data channels INNERMOST),
-- but the translation puts those channels ABOVE the φ-bound sync binders.  So we must
-- commute the single ν inward past the φ-nest, fire, and push back.  Structure:
--
--   RU-Struct (Uν-flat σ C₁ B Q ◅◅ step2L ◅◅ step3L)   -- LHS ≋ MID_L
--             (φ^-─→ sC₁ (φ^-─→ sB (𝐔R.RU-LSplit F {x})))  -- MID_L ─→ MID_R
--             rhs                                         -- MID_R ≋ RHS
--
--   • step2L : DONE below — the ν-φ^-comm×2 transpose.  Output:
--       φ^ sC₁ (φ^ sB (ν (BODY_L ⋯ TRANSP)))   where
--       TRANSP = (assocSwapᵣ sC₁ 2 ↑* sB) ·ₖ assocSwapᵣ sB 2  brings the 2 channels
--       to indices 0,1 at scope `2 + (sB + (sC₁ + n))`.
--   • BODY_L ⋯ TRANSP  distributes over ∥ (definitional):
--       (Flags C₁ ⋯ wk sB ⋯ TRANSP) ∥ ((Flags B ⋯ TRANSP) ∥ (U[Q]leafσ ⋯ TRANSP)),
--       and U[Q]leafσ = ⟪ redex ⋯ leafσ ⟫ ∥ U[P]leafσ.
--   • step3L (TODO) : ∥-reorder (∥-comm/∥-assoc) to bring the redex thread to the
--       front AND ≡→≋ (frame-plug*) to rewrite `redex ⋯ leafσ ⋯ TRANSP` into the
--       RU-LSplit pattern  ⟪ F [ lsplit · ((e₁ ⊗ `x) ⊗ e₂) ]* ⟫  with x the ν-bound
--       data channel.  MID_L = φ^ sC₁ (φ^ sB (ν (⟪F[lsplit·triple]⟫ ∥ Prest))).
--
-- TWO HEAVY OBLIGATIONS (each ≈ a chunk of U-ν-comm; do NOT guess proof terms):
--   (O1) LEAF RECONCILE (the subEqLemma analogue) — the crux.  Compute
--        `redex ⋯ leafσ ⋯ TRANSP` via frame-plug*: the lsplit argument is
--        leafσ (𝐒.inj 0F) = canonₛ C₁ cc1 (handle at position `sum B₁`) ⋯ wk sB,
--        i.e. the (length B₁)-th chain's FIRST handle triple.
--
--        HANDLE FACTS (verified by hand vs the Ubₛ/canonₛ defs; cc = that chain's
--        threaded UChan = (e₁,x,e₂), where for length B₁ ≥ 1 canonₛ sets e₁ = `0F (a
--        sync) and x = (suc-shifted data channel) — this is why the redex references
--        a sync binder, forcing the transpose):
--          • LHS handle  = head (Ubₛ (suc b₁) cc):
--               b₁ = 0   →  (e₁ ⊗ `x) ⊗ e₂        (e₂ = chain tail)
--               b₁ ≥ 1   →  (e₁ ⊗ `x) ⊗ K`unit
--          • RU-LSplit on input triple (a ⊗ `x) ⊗ c yields
--               ((a ⊗ `x) ⊗ K`unit) ⊗ ((K`unit ⊗ `x) ⊗ c).
--          • RHS handles = head & 2nd of (Ubₛ (suc (suc b₁)) cc):
--               head = (e₁ ⊗ `x) ⊗ K`unit;  2nd = head (Ubₛ (suc b₁) (K`unit,x,e₂)):
--                 b₁ = 0 → (K`unit ⊗ `x) ⊗ e₂ ;  b₁ ≥ 1 → (K`unit ⊗ `x) ⊗ K`unit.
--          ⇒ in BOTH b₁ cases  RU-LSplit-output = (RHS head handle) ⊗ (RHS 2nd handle).
--          The chain TAIL e₂ lives only in the chain's LAST handle, untouched.
--
--        So O1 = a canonₛ-split lemma (induction on B₁: B₁=[] hits the head chain at
--        pos 0; B₁=a∷B₁' peels chain a and recurses at pos sum B₁') giving
--          canonₛ C₁ cc1 (handle@sumB₁) = LHS-handle-triple   and
--          canonₛ C₁' cc1 (inj 0F / inj 1F) = RHS head / 2nd handle,
--        PLUS  leafσ_LHS ≗ (𝐒.lwk ·ₖ leafσ_RHS) on E/P's vars (lwk inserts the new
--        handle slot; non-split vars preserved), absorbed at the leaf via
--        U-σ⋯ / U-⋯ₚ / U-cong (cf. NuComm.leafeq = U-σ⋯ ■ U-cong subEq ■ sym U-⋯ₚ).
--        NEW machinery; reuse canonₛ-nat (Toolkit:338) / Ubₛ-nat (Toolkit:308).
--   (O2) FLAGS-UNDER-TRANSP — Flags C₁ = Flags C₁' (syncs equal AND
--        ϕ[suc b₁]=ϕ[suc(suc b₁)]=unset), so the flag groups match; reconcile their
--        TRANSP-renaming via Flags-⋯-cong with toℕ/cleanT-style var equalities
--        (cf. NuComm c1–c4, but a single-ν assocSwap).
--
-- RHS chain `rhs` = the mirror of (Uν-flat ◅◅ step2L ◅◅ step3L) for C₁'/Q', i.e.
--   reorder back, φ^-ν-comm×2 (sym of step2L's transpose), sym Uν-flat.
-- ════════════════════════════════════════════════════════════════════════════
U-lsplit {m} {n} σ Vσ {B₁} {B₂} {B} {b₁} {s} {E} {P} ρ⁻ ρ⁻-skip {E₀} Eeq {P₀} Peq =
  𝐔R.RU-Struct
    (Uν-flat σ C₁ B Q ◅◅ step2L ◅◅ step3L)
    (φ^-─→ sC₁ (φ^-─→ sB (𝐔R.RU-LSplit Fr)))
    (middleReconcile ◅◅ Eq*.symmetric _ reverseChain)
  where
    module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
    C₁ : 𝐓.BindGroup
    C₁ = B₁ ++ suc b₁ ∷ B₂
    Q : 𝐓.Proc (sum C₁ + sum B + m)
    Q = 𝐓.⟪ E [ K (`lsplit s) · (` 𝐒.inj 0F) ]* ⟫ 𝐓.∥ P
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
    RpForm : ((E [ K (`lsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ⋯ ρ₁ ⋯ ρ₂
             ≡ Fr [ K (`lsplit s) · redexTriple ]*
    RpForm =
        fusion ((E [ K (`lsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ρ₁ ρ₂
      ■ fusion (E [ K (`lsplit s) · (` 𝐒.inj 0F) ]*) leafσ ρ₁₂
      ■ frame-plug* E σ' Vσ'
      ■ cong (λ z → Fr [ K (`lsplit s) · z ]*) σ'inj0
    G1 G2 Sp RpThread Prest : 𝐔.Proc (2 + (sB + (sC₁ + n)))
    G1 = (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    G2 = Flags B 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    Sp = U[ P ] leafσ 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂
    RpThread = 𝐔.⟪ ((E [ K (`lsplit s) · (` 𝐒.inj 0F) ]*) ⋯ leafσ) ⋯ ρ₁ ⋯ ρ₂ ⟫
    Prest = G2 𝐔.∥ (G1 𝐔.∥ Sp)
    step3L : φ^ sC₁ (φ^ sB (𝐔.ν (BODY_L 𝐔.⋯ₚ ρ₁ 𝐔.⋯ₚ ρ₂))) 𝐔.≋
             φ^ sC₁ (φ^ sB (𝐔.ν (𝐔.⟪ Fr [ K (`lsplit s) · redexTriple ]* ⟫ 𝐔.∥ Prest)))
    step3L = φ^-cong sC₁ (φ^-cong sB (𝐔.ν-cong
               ( reorder-front G1 G2 RpThread Sp
               ◅◅ ≡→≋ (cong (𝐔._∥ Prest) (cong 𝐔.⟪_⟫ RpForm)) )))
    -- ── RHS side (C₁' = the grown bind group): a cast-free mirror of the lhs chain. ──
    C₁' : 𝐓.BindGroup
    C₁' = B₁ ++ suc (suc b₁) ∷ B₂
    sC₁' = syncs C₁'
    Q' : 𝐓.Proc (sum C₁' + sum B + m)
    Q' = 𝐓.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ 𝐓.∥ (P 𝐓.⋯ₚ 𝐒.lwk)
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
    Sp_R = U[ P 𝐓.⋯ₚ 𝐒.lwk ] leafσ' 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2
    RpThread_R = 𝐔.⟪ (((E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]*) ⋯ leafσ') ⋯ ρ₁') ⋯ assocSwapᵣ sB 2 ⟫
    Prest_R = G2_R 𝐔.∥ (G1_R 𝐔.∥ Sp_R)
    reorderR : φ^ sC₁' (φ^ sB (𝐔.ν (BODY_R 𝐔.⋯ₚ ρ₁' 𝐔.⋯ₚ assocSwapᵣ sB 2))) 𝐔.≋
               φ^ sC₁' (φ^ sB (𝐔.ν (RpThread_R 𝐔.∥ Prest_R)))
    reorderR = φ^-cong sC₁' (φ^-cong sB (𝐔.ν-cong (reorder-front G1_R G2_R RpThread_R Sp_R)))
    reverseChain : U[ 𝐓.ν C₁' B Q' ] σ 𝐔.≋ φ^ sC₁' (φ^ sB (𝐔.ν (RpThread_R 𝐔.∥ Prest_R)))
    reverseChain = Uν-flat σ C₁' B Q' ◅◅ step2R ◅◅ reorderR
    splitResult : Tm (2 + (sB + (sC₁ + n)))
    splitResult = (((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂) ⊗ (` Xch)) ⊗ K `unit)
                ⊗ ((K `unit ⊗ (` Xch)) ⊗ (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂))
    -- ── lwk-identity off the consumed handle: leafσ ≗ 𝐒.lwk ·ₖ leafσ' away from inj 0F. ──
    ccfn : (s : ℕ) → UChan (s + (2 + n))
    ccfn s = (K `unit , weaken* ⦃ Kᵣ ⦄ s 1F , K `unit)
    σfn : (s : ℕ) → m →ₛ (sB + (s + (2 + n)))
    σfn s = λ u → σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ s ⋯ weaken* ⦃ Kᵣ ⦄ sB
    canonB-coh : ∀ (s′ : ℕ) (eq : sC₁ ≡ s′) (w : 𝔽 (sum B)) →
                 subst (λ j → Tm (sB + (j + (2 + n)))) eq (canonₛ B (ccfn sC₁) w) ≡ canonₛ B (ccfn s′) w
    canonB-coh _ refl w = refl
    σ-coh : ∀ (s′ : ℕ) (eq : sC₁ ≡ s′) (u : 𝔽 m) →
            subst (λ j → Tm (sB + (j + (2 + n)))) eq (σfn sC₁ u) ≡ σfn s′ u
    σ-coh _ refl u = refl
    data-coh : ∀ (d : 𝔽 (sum C₁)) → d ≢ castpos →
               subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwk B₁) (canonₛ C₁ cc1 d ⋯ weaken* ⦃ Kᵣ ⦄ sB)
               ≡ canonₛ C₁' cc1 (dlwk B₁ b₁ B₂ d) ⋯ weaken* ⦃ Kᵣ ⦄ sB
    data-coh d d≢ =
        subst-wkB sB (syncs-lwk B₁) (canonₛ C₁ cc1 d)
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB)
          (sym (subst-cong+ (syncs-lwk B₁) (canonₛ C₁ cc1 d)) ■ canonₛ-lwk B₁ cc1 b₁ B₂ d d≢)
    lwk-id-off0 : ∀ (i : 𝔽 (sum C₁ + sum B + m)) → i ≢ 𝐒.inj {suc b₁ ∷ []} {m} 0F →
                  subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwk B₁) (leafσ i) ≡ leafσ' (𝐒.lwk i)
    lwk-id-off0 i i≢ with splitAt (sum C₁ + sum B) i | Fin.join-splitAt (sum C₁ + sum B) m i
    ... | inj₂ u  | jeq =
          σ-coh sC₁' (syncs-lwk B₁) u
        ■ sym ( cong leafσ' (cong (𝐒.lwk) (sym jeq) ■ P3 B₁ B₂ B u)
              ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ʳ (sum C₁' + sum B) m u) )
    ... | inj₁ db | jeq with splitAt (sum C₁) db | Fin.join-splitAt (sum C₁) (sum B) db
    ...   | inj₂ w | jeq2 =
            canonB-coh sC₁' (syncs-lwk B₁) w
          ■ sym ( cong leafσ' (cong (𝐒.lwk) ieq ■ P2 B₁ B₂ B w)
                ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (sum C₁' ↑ʳ w) m)
                ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                       (Fin.splitAt-↑ʳ (sum C₁') (sum B) w) )
      where ieq : i ≡ (sum C₁ ↑ʳ w) ↑ˡ m
            ieq = sym jeq ■ cong (_↑ˡ m) (sym jeq2)
    ...   | inj₁ d | jeq2 =
            data-coh d d≢
          ■ sym ( cong leafσ' (cong (𝐒.lwk) ieq ■ P1 B₁ B₂ B d)
                ■ cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m)
                ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                       (Fin.splitAt-↑ˡ (sum C₁') (dlwk B₁ b₁ B₂ d) (sum B)) )
      where ieq : i ≡ (d ↑ˡ sum B) ↑ˡ m
            ieq = sym jeq ■ cong (_↑ˡ m) (sym jeq2)
            d≢ : d ≢ castpos
            d≢ d≡ = i≢ (ieq ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡)

    middleReconcile : φ^ sC₁ (φ^ sB (𝐔.ν (𝐔.⟪ Fr [ splitResult ]* ⟫ 𝐔.∥ Prest)))
                      𝐔.≋ φ^ sC₁' (φ^ sB (𝐔.ν (RpThread_R 𝐔.∥ Prest_R)))
    middleReconcile =
      ≡→≋ (φ^-cast (syncs-lwk B₁) (φ^ sB (𝐔.ν (𝐔.⟪ Fr [ splitResult ]* ⟫ 𝐔.∥ Prest))))
      ◅◅ φ^-cong sC₁'
          ( ≡→≋ ( subst-φ^ sB (syncs-lwk B₁) (𝐔.ν (𝐔.⟪ Fr [ splitResult ]* ⟫ 𝐔.∥ Prest))
                ■ cong (φ^ sB) (subst-νf (λ j → sB + (j + n)) (syncs-lwk B₁) (𝐔.⟪ Fr [ splitResult ]* ⟫ 𝐔.∥ Prest))
                ■ cong (λ z → φ^ sB (𝐔.ν z)) (subst-∥f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) (𝐔.⟪ Fr [ splitResult ]* ⟫) Prest) )
          ◅◅ φ^-cong sB (𝐔.ν-cong (𝐔.∥-cong redexRec PrestRec)) )
      where
        ρ₂F : (j : ℕ) → (sB + (2 + (j + n))) →ᵣ (2 + (sB + (j + n)))
        ρ₂F j = assocSwapᵣ sB 2 {j + n}
        ρ₁F : (j : ℕ) → (sB + (j + (2 + n))) →ᵣ (sB + (2 + (j + n)))
        ρ₁F j = assocSwapᵣ j 2 {n} ↑* sB
        G2rec : subst (λ j → 𝐔.Proc (2 + (sB + (j + n)))) (syncs-lwk B₁) G2 ≡ G2_R
        G2rec =
            transport-⋯ₚ (λ j → sB + (2 + (j + n))) (λ j → 2 + (sB + (j + n))) ρ₂F (syncs-lwk B₁) (Flags B 𝐔.⋯ₚ ρ₁)
          ■ cong (𝐔._⋯ₚ ρ₂F sC₁')
              ( transport-⋯ₚ (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) ρ₁F (syncs-lwk B₁) (Flags B)
              ■ cong (𝐔._⋯ₚ ρ₁F sC₁') (Flags-base-nat B (λ j → j + (2 + n)) (syncs-lwk B₁)) )
        G1rec : subst (λ j → 𝐔.Proc (2 + (sB + (j + n)))) (syncs-lwk B₁) G1 ≡ G1_R
        G1rec =
            transport-⋯ₚ (λ j → sB + (2 + (j + n))) (λ j → 2 + (sB + (j + n))) ρ₂F (syncs-lwk B₁) ((Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.⋯ₚ ρ₁)
          ■ cong (𝐔._⋯ₚ ρ₂F sC₁')
              ( transport-⋯ₚ (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) ρ₁F (syncs-lwk B₁) (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB)
              ■ cong (𝐔._⋯ₚ ρ₁F sC₁')
                  ( transport-⋯ₚ (λ j → j + (2 + n)) (λ j → sB + (j + (2 + n))) (λ _ → weaken* ⦃ Kᵣ ⦄ sB) (syncs-lwk B₁) (Flags C₁)
                  ■ cong (𝐔._⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+P (syncs-lwk B₁) (Flags C₁)) ■ Flags-lwk B₁) ) )
        Sprec : subst (λ j → 𝐔.Proc (2 + (sB + (j + n)))) (syncs-lwk B₁) Sp ≡ Sp_R
        Sprec =
            transport-⋯ₚ (λ j → sB + (2 + (j + n))) (λ j → 2 + (sB + (j + n))) ρ₂F (syncs-lwk B₁) (U[ P ] leafσ 𝐔.⋯ₚ ρ₁)
          ■ cong (𝐔._⋯ₚ ρ₂F sC₁')
              ( transport-⋯ₚ (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) ρ₁F (syncs-lwk B₁) (U[ P ] leafσ)
              ■ cong (𝐔._⋯ₚ ρ₁F sC₁') Pleafeq )
          where
            Pleafeq : subst (λ j → 𝐔.Proc (sB + (j + (2 + n)))) (syncs-lwk B₁) (U[ P ] leafσ) ≡ U[ P 𝐓.⋯ₚ 𝐒.lwk ] leafσ'
            Pleafeq =
                U-cod-transport P (λ j → sB + (j + (2 + n))) (syncs-lwk B₁) leafσ
              ■ cong (λ p → U[ p ] (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) (syncs-lwk B₁) leafσ)) Peq
              ■ U-⋯ₚ P₀
              ■ U-cong P₀ (λ y → subst-app (λ j → sB + (j + (2 + n))) (syncs-lwk B₁) leafσ (ρ⁻ y)
                               ■ lwk-id-off0 (ρ⁻ y) (ρ⁻-skip y))
              ■ sym (U-⋯ₚ P₀)
              ■ cong (λ p → U[ p ] (𝐒.lwk ·ₖ leafσ')) (sym Peq)
              ■ sym (U-⋯ₚ P)
        PrestRec : subst (λ j → 𝐔.Proc (2 + (sB + (j + n)))) (syncs-lwk B₁) Prest 𝐔.≋ Prest_R
        PrestRec = ≡→≋
          ( subst-∥f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) G2 (G1 𝐔.∥ Sp)
          ■ cong₂ 𝐔._∥_ G2rec
              ( subst-∥f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) G1 Sp
              ■ cong₂ 𝐔._∥_ G1rec Sprec ) )
        redexRec : subst (λ j → 𝐔.Proc (2 + (sB + (j + n)))) (syncs-lwk B₁) 𝐔.⟪ Fr [ splitResult ]* ⟫ 𝐔.≋ RpThread_R
        redexRec = ≡→≋
          ( subst-⟪⟫ (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) (Fr [ splitResult ]*)
          ■ cong 𝐔.⟪_⟫
              ( subst-frame-plug (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) Fr splitResult
              ■ cong₂ _[_]* frameEq holeEq
              ■ sym RpForm_R ) )
          where
            ρ₁₂F : (j : ℕ) → (sB + (j + (2 + n))) →ᵣ (2 + (sB + (j + n)))
            ρ₁₂F j = ρ₁F j ·ₖ ρ₂F j
            ρ₁₂'R : (sB + (sC₁' + (2 + n))) →ᵣ (2 + (sB + (sC₁' + n)))
            ρ₁₂'R = ρ₁₂F sC₁'
            σ'ᴿ : (sum C₁' + sum B + m) →ₛ (2 + (sB + (sC₁' + n)))
            σ'ᴿ = leafσ' ·ₖ ρ₁₂'R
            Vσ'ᴿ : VSub σ'ᴿ
            Vσ'ᴿ i = value-⋯ (Vleafσ' i) ρ₁₂'R (λ _ → V-`)
            Vσ'T : VSub (subst (λ j → (sum C₁ + sum B + m) →ₛ (2 + (sB + (j + n)))) (syncs-lwk B₁) σ')
            Vσ'T = VSub-cod-subst (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) Vσ'
            Eᴿ : Frame* (sum C₁' + sum B + m)
            Eᴿ = E ⋯ᶠ* 𝐒.lwk
            pair : Tm (sum C₁' + sum B + m)
            pair = (` 𝐒.inj {suc (suc b₁) ∷ []} {m} 0F) ⊗ (` 𝐒.inj {suc (suc b₁) ∷ []} {m} 1F)
            sib = canonₛ-sib B₁ cc1 b₁ B₂
            cp0 cp1 : 𝔽 (sum C₁')
            cp0 = Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 0F)
            cp1 = Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 1F)
            leafσ'-inj : ∀ (cp : 𝔽 (sum C₁')) →
                         leafσ' ((cp ↑ˡ sum B) ↑ˡ m) ≡ canonₛ C₁' cc1 cp ⋯ weaken* ⦃ Kᵣ ⦄ sB
            leafσ'-inj cp =
                cong [ Xleaf' , σpart' ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum B) (cp ↑ˡ sum B) m)
              ■ cong [ (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB) , canonₛ B cc2' ]′
                     (Fin.splitAt-↑ˡ (sum C₁') cp (sum B))
            σ'ᴿinj0 : σ'ᴿ (𝐒.inj {suc (suc b₁) ∷ []} {m} 0F)
                      ≡ (((proj₁ sib ⊗ (` proj₁ (proj₂ sib))) ⊗ K `unit) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ρ₁₂'R
            σ'ᴿinj0 = cong (_⋯ ρ₁₂'R) (leafσ'-inj cp0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ sib)))))
            σ'ᴿinj1 : σ'ᴿ (𝐒.inj {suc (suc b₁) ∷ []} {m} 1F)
                      ≡ (((K `unit ⊗ (` proj₁ (proj₂ sib))) ⊗ proj₁ (proj₂ (proj₂ sib))) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ρ₁₂'R
            σ'ᴿinj1 = cong (_⋯ ρ₁₂'R) (leafσ'-inj cp1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₂ (proj₂ (proj₂ (proj₂ sib)))))
            aEq : subst (λ j → Tm (2 + (sB + (j + n)))) (syncs-lwk B₁) (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂)
                  ≡ proj₁ sib ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂'R
            aEq = transport-⋯T (λ j → sB + (j + (2 + n))) (λ j → 2 + (sB + (j + n))) ρ₁₂F (syncs-lwk B₁) (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                ■ cong (_⋯ ρ₁₂F sC₁')
                    ( subst-wkB sB (syncs-lwk B₁) (proj₁ hc)
                    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+ (syncs-lwk B₁) (proj₁ hc)) ■ proj₁ (hc-sib-agree B₁ cc1 b₁ B₂)) )
            cEq : subst (λ j → Tm (2 + (sB + (j + n)))) (syncs-lwk B₁) (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂)
                  ≡ proj₁ (proj₂ (proj₂ sib)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁₂'R
            cEq = transport-⋯T (λ j → sB + (j + (2 + n))) (λ j → 2 + (sB + (j + n))) ρ₁₂F (syncs-lwk B₁) (proj₁ (proj₂ (proj₂ hc)) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                ■ cong (_⋯ ρ₁₂F sC₁')
                    ( subst-wkB sB (syncs-lwk B₁) (proj₁ (proj₂ (proj₂ hc)))
                    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+ (syncs-lwk B₁) (proj₁ (proj₂ (proj₂ hc)))) ■ proj₂ (proj₂ (hc-sib-agree B₁ cc1 b₁ B₂))) )
            xEq : subst (λ j → 𝔽 (2 + (sB + (j + n)))) (syncs-lwk B₁) Xch ≡ ρ₁₂'R (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ sib)))
            xEq = transport-ρ𝔽 (λ j → sB + (j + (2 + n))) (λ j → 2 + (sB + (j + n))) ρ₁₂F (syncs-lwk B₁) (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ hc)))
                ■ cong (ρ₁₂F sC₁')
                    ( subst-wk𝔽 sB (syncs-lwk B₁) (proj₁ (proj₂ hc))
                    ■ cong (weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+𝔽 (syncs-lwk B₁) (proj₁ (proj₂ hc))) ■ proj₁ (proj₂ (hc-sib-agree B₁ cc1 b₁ B₂))) )
            holeEq : subst (λ j → Tm (2 + (sB + (j + n)))) (syncs-lwk B₁) splitResult ≡ pair ⋯ σ'ᴿ
            holeEq =
                subst-⊗f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) _ _
              ■ cong₂ _⊗_
                  ( subst-⊗f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) _ _
                  ■ cong₂ _⊗_
                      ( subst-⊗f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) _ _
                      ■ cong₂ _⊗_ aEq (subst-`f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) Xch ■ cong `_ xEq) )
                      (subst-Kunit-f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁))
                  ■ sym σ'ᴿinj0 )
                  ( subst-⊗f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) _ _
                  ■ cong₂ _⊗_
                      ( subst-⊗f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) _ _
                      ■ cong₂ _⊗_ (subst-Kunit-f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁))
                                  (subst-`f (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) Xch ■ cong `_ xEq) )
                      cEq
                  ■ sym σ'ᴿinj1 )
            ptw : (ρ⁻ ·ₖ subst (λ j → (sum C₁ + sum B + m) →ₛ (2 + (sB + (j + n)))) (syncs-lwk B₁) σ')
                  ≗ (ρ⁻ ·ₖ (𝐒.lwk ·ₖ σ'ᴿ))
            ptw y = subst-app (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) σ' (ρ⁻ y)
                  ■ transport-⋯T (λ j → sB + (j + (2 + n))) (λ j → 2 + (sB + (j + n))) ρ₁₂F (syncs-lwk B₁) (leafσ (ρ⁻ y))
                  ■ cong (_⋯ ρ₁₂F sC₁') (lwk-id-off0 (ρ⁻ y) (ρ⁻-skip y))
            frameEq : subst (λ j → Frame* (2 + (sB + (j + n)))) (syncs-lwk B₁) Fr ≡ frame*-⋯ Eᴿ σ'ᴿ Vσ'ᴿ
            frameEq =
                subst-frame* (λ j → 2 + (sB + (j + n))) (syncs-lwk B₁) E σ' Vσ' Vσ'T
              ■ cong (λ e → frame*-⋯ e (subst (λ j → (sum C₁ + sum B + m) →ₛ (2 + (sB + (j + n)))) (syncs-lwk B₁) σ') Vσ'T) Eeq
              ■ frame*-fusion-gen E₀ Vσ'T (λ y → Vσ'T (ρ⁻ y))
              ■ frame*-cong E₀ (λ y → Vσ'T (ρ⁻ y)) (λ y → Vσ'ᴿ (𝐒.lwk (ρ⁻ y))) ptw
              ■ sym (frame*-fusion-gen E₀ (λ y → Vσ'ᴿ (𝐒.lwk y)) (λ y → Vσ'ᴿ (𝐒.lwk (ρ⁻ y))))
              ■ sym (frame*-fusion-gen (E₀ ⋯ᶠ* ρ⁻) Vσ'ᴿ (λ y → Vσ'ᴿ (𝐒.lwk y)))
              ■ cong (λ e → frame*-⋯ (e ⋯ᶠ* 𝐒.lwk) σ'ᴿ Vσ'ᴿ) (sym Eeq)
            RpForm_R : (((Eᴿ [ pair ]*) ⋯ leafσ') ⋯ ρ₁') ⋯ assocSwapᵣ sB 2 ≡ frame*-⋯ Eᴿ σ'ᴿ Vσ'ᴿ [ pair ⋯ σ'ᴿ ]*
            RpForm_R =
                fusion ((Eᴿ [ pair ]*) ⋯ leafσ') ρ₁' (assocSwapᵣ sB 2)
              ■ fusion (Eᴿ [ pair ]*) leafσ' ρ₁₂'R
              ■ frame-plug* Eᴿ σ'ᴿ Vσ'ᴿ
