module BorrowedCF.Simulation.Theorems.Toolkit where

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

toℕ-wk : ∀ a {m} (z : 𝔽 m) → Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a z) ≡ a + Fin.toℕ z
toℕ-wk a z = cong Fin.toℕ (weaken*~↑ʳ ⦃ Kᵣ ⦄ a z) ■ Fin.toℕ-↑ʳ a z

toℕ-↑* : ∀ {n₁ n₂} (ρ : n₁ →ᵣ n₂) m (z : 𝔽 (m + n₁)) →
         Fin.toℕ ((ρ ↑* m) z) ≡ [ Fin.toℕ , (λ q → m + Fin.toℕ (ρ q)) ]′ (Fin.splitAt m z)
toℕ-↑* ρ m z = cong Fin.toℕ (↑*∼id/wk-splitAt ρ m z) ■ hh (Fin.splitAt m z)
  where
    hh : (s : 𝔽 m ⊎ 𝔽 _) →
         Fin.toℕ ([ id/` ⦃ Kᵣ ⦄ ∘ (_↑ˡ _) , ρ ·ₖ weaken* ⦃ Kᵣ ⦄ m ]′ s)
         ≡ [ Fin.toℕ , (λ q → m + Fin.toℕ (ρ q)) ]′ s
    hh (inj₁ p) = Fin.toℕ-↑ˡ p _
    hh (inj₂ q) = cong Fin.toℕ (weaken*~↑ʳ ⦃ Kᵣ ⦄ m (ρ q)) ■ Fin.toℕ-↑ʳ m (ρ q)

-- Pushing toℕ through a ↑*-lift, split on whether the index is in the fixed prefix.
↑*-lo : ∀ {n₁ n₂} (ρ : n₁ →ᵣ n₂) p (y : 𝔽 (p + n₁)) → Fin.toℕ y Nat.< p →
        Fin.toℕ ((ρ ↑* p) y) ≡ Fin.toℕ y
↑*-lo ρ p y lt =
    toℕ-↑* ρ p y
  ■ cong [ Fin.toℕ , (λ q → p + Fin.toℕ (ρ q)) ]′ (Fin.splitAt-< p y lt)
  ■ Fin.toℕ-fromℕ< lt

↑*-hi : ∀ {n₁ n₂} (ρ : n₁ →ᵣ n₂) p (y : 𝔽 (p + n₁)) (h : p Nat.≤ Fin.toℕ y) →
        Fin.toℕ ((ρ ↑* p) y) ≡ p + Fin.toℕ (ρ (Fin.reduce≥ y h))
↑*-hi ρ p y h =
    toℕ-↑* ρ p y
  ■ cong [ Fin.toℕ , (λ q → p + Fin.toℕ (ρ q)) ]′ (Fin.splitAt-≥ p y h)

sub-lt : ∀ {a b c} → a Nat.≤ c → c Nat.< a + b → c Nat.∸ a Nat.< b
sub-lt {a} {b} {c} a≤c c<ab =
  Nat.+-cancelˡ-< a (c Nat.∸ a) b (subst (Nat._< a + b) (sym (Nat.m+[n∸m]≡n a≤c)) c<ab)

∸3 : ∀ a b c v → ((v Nat.∸ a) Nat.∸ b) Nat.∸ c ≡ v Nat.∸ (a + b + c)
∸3 a b c v = cong (Nat._∸ c) (Nat.∸-+-assoc v a b) ■ Nat.∸-+-assoc v (a + b) c

-- "Move a width-w block past a width-(b+c) block": the composite assocSwapᵣ w b ·ₖ (assocSwapᵣ w c ↑* b).
Mv : ∀ w b c {rest} → (w + (b + (c + rest))) →ᵣ (b + (c + (w + rest)))
Mv w b c = assocSwapᵣ w b ·ₖ (assocSwapᵣ w c ↑* b)

Mv-lt : ∀ w b c {rest} (y : 𝔽 (w + (b + (c + rest)))) → Fin.toℕ y Nat.< w →
        Fin.toℕ (Mv w b c y) ≡ (b + c) + Fin.toℕ y
Mv-lt w b c y lt =
    ↑*-hi (assocSwapᵣ w c) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (toℕ-assoc-lt w c (Fin.reduce≥ (assocSwapᵣ w b y) hge) ltc ■ cong (c +_) redℕ)
  ■ sym (Nat.+-assoc b c (Fin.toℕ y))
  where
    sℕ : Fin.toℕ (assocSwapᵣ w b y) ≡ b + Fin.toℕ y
    sℕ = toℕ-assoc-lt w b y lt
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sℕ) (Nat.m≤m+n b (Fin.toℕ y))
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sℕ ■ Nat.m+n∸m≡n b (Fin.toℕ y)
    ltc : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) Nat.< w
    ltc = subst (Nat._< w) (sym redℕ) lt

Mv-ge : ∀ w b c {rest} (y : 𝔽 (w + (b + (c + rest)))) → w + (b + c) Nat.≤ Fin.toℕ y →
        Fin.toℕ (Mv w b c y) ≡ Fin.toℕ y
Mv-ge w b c y ge =
    ↑*-hi (assocSwapᵣ w c) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (toℕ-assoc-ge w c (Fin.reduce≥ (assocSwapᵣ w b y) hge) gec ■ redℕ)
  ■ Nat.m+[n∸m]≡n bley
  where
    wbley : w + b Nat.≤ Fin.toℕ y
    wbley = Nat.≤-trans (Nat.+-monoʳ-≤ w (Nat.m≤m+n b c)) ge
    sℕ : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y
    sℕ = toℕ-assoc-ge w b y wbley
    bley : b Nat.≤ Fin.toℕ y
    bley = Nat.≤-trans (Nat.m≤m+n b w) (Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm b w)) wbley)
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sℕ) bley
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y Nat.∸ b
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sℕ
    gec : w + c Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge)
    gec = subst (w + c Nat.≤_) (sym redℕ) wcleyb
      where
        wcleyb : w + c Nat.≤ Fin.toℕ y Nat.∸ b
        wcleyb = subst (Nat._≤ Fin.toℕ y Nat.∸ b) (Nat.m+n∸m≡n b (w + c))
                   (Nat.∸-monoˡ-≤ b (subst (Nat._≤ Fin.toℕ y) (lemma) ge))
          where lemma : w + (b + c) ≡ b + (w + c)
                lemma = sym (Nat.+-assoc w b c) ■ cong (Nat._+ c) (Nat.+-comm w b) ■ Nat.+-assoc b w c

Mv-mid : ∀ w b c {rest} (y : 𝔽 (w + (b + (c + rest)))) →
         w Nat.≤ Fin.toℕ y → Fin.toℕ y Nat.< w + (b + c) →
         Fin.toℕ (Mv w b c y) ≡ Fin.toℕ y Nat.∸ w
Mv-mid w b c y wley lt with Fin.toℕ y Nat.<? (w + b)
... | yes p =
    ↑*-lo (assocSwapᵣ w c) b (assocSwapᵣ w b y)
          (subst (Nat._< b) (sym smid) (sub-lt wley p))
  ■ smid
  where
    smid : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y Nat.∸ w
    smid = toℕ-assoc-mid w b y wley p
... | no ¬p =
    ↑*-hi (assocSwapᵣ w c) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (toℕ-assoc-mid w c (Fin.reduce≥ (assocSwapᵣ w b y) hge) gec ltc
                 ■ cong (Nat._∸ w) redℕ)
  ■ ( cong (b +_) (Nat.∸-+-assoc (Fin.toℕ y) b w)
    ■ cong (λ z → b + (Fin.toℕ y Nat.∸ z)) (Nat.+-comm b w)
    ■ cong (b +_) (sym (Nat.∸-+-assoc (Fin.toℕ y) w b))
    ■ Nat.m+[n∸m]≡n (subst (Nat._≤ Fin.toℕ y Nat.∸ w) (Nat.m+n∸m≡n w b) (Nat.∸-monoˡ-≤ w wbley)) )
  where
    wbley : w + b Nat.≤ Fin.toℕ y
    wbley = Nat.≮⇒≥ ¬p
    bley : b Nat.≤ Fin.toℕ y
    bley = Nat.≤-trans (Nat.m≤n+m b w) wbley
    sge : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y
    sge = toℕ-assoc-ge w b y wbley
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sge) bley
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y Nat.∸ b
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sge
    wley-yb : w Nat.≤ Fin.toℕ y Nat.∸ b
    wley-yb = subst (Nat._≤ Fin.toℕ y Nat.∸ b) (Nat.m+n∸n≡m w b) (Nat.∸-monoˡ-≤ b wbley)
    gec : w Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge)
    gec = subst (w Nat.≤_) (sym redℕ) wley-yb
    ltc : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) Nat.< w + c
    ltc = subst (Nat._< w + c) (sym redℕ) (sub-lt bley (subst (Fin.toℕ y Nat.<_) reassoc lt))
      where reassoc : w + (b + c) ≡ b + (w + c)
            reassoc = sym (Nat.+-assoc w b c) ■ cong (Nat._+ c) (Nat.+-comm w b) ■ Nat.+-assoc b w c

-- "Move a width-w block past a width-(b+c+d) block": three sub-blocks (reuses Mv).
Mv3 : ∀ w b c d {rest} → (w + (b + (c + (d + rest)))) →ᵣ (b + (c + (d + (w + rest))))
Mv3 w b c d = assocSwapᵣ w b ·ₖ (Mv w c d ↑* b)

Mv3-lt : ∀ w b c d {rest} (y : 𝔽 (w + (b + (c + (d + rest))))) → Fin.toℕ y Nat.< w →
         Fin.toℕ (Mv3 w b c d y) ≡ (b + (c + d)) + Fin.toℕ y
Mv3-lt w b c d y lt =
    ↑*-hi (Mv w c d) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (Mv-lt w c d (Fin.reduce≥ (assocSwapᵣ w b y) hge) ltc ■ cong ((c + d) +_) redℕ)
  ■ sym (Nat.+-assoc b (c + d) (Fin.toℕ y))
  where
    sℕ : Fin.toℕ (assocSwapᵣ w b y) ≡ b + Fin.toℕ y
    sℕ = toℕ-assoc-lt w b y lt
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sℕ) (Nat.m≤m+n b (Fin.toℕ y))
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sℕ ■ Nat.m+n∸m≡n b (Fin.toℕ y)
    ltc : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) Nat.< w
    ltc = subst (Nat._< w) (sym redℕ) lt

Mv3-ge : ∀ w b c d {rest} (y : 𝔽 (w + (b + (c + (d + rest))))) →
         w + (b + (c + d)) Nat.≤ Fin.toℕ y → Fin.toℕ (Mv3 w b c d y) ≡ Fin.toℕ y
Mv3-ge w b c d y ge =
    ↑*-hi (Mv w c d) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (Mv-ge w c d (Fin.reduce≥ (assocSwapᵣ w b y) hge) gec ■ redℕ)
  ■ Nat.m+[n∸m]≡n bley
  where
    wbley : w + b Nat.≤ Fin.toℕ y
    wbley = Nat.≤-trans (Nat.+-monoʳ-≤ w (Nat.m≤m+n b (c + d))) ge
    sℕ : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y
    sℕ = toℕ-assoc-ge w b y wbley
    bley : b Nat.≤ Fin.toℕ y
    bley = Nat.≤-trans (Nat.m≤n+m b w) wbley
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sℕ) bley
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y Nat.∸ b
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sℕ
    gec : w + (c + d) Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge)
    gec = subst (w + (c + d) Nat.≤_) (sym redℕ)
            (subst (Nat._≤ Fin.toℕ y Nat.∸ b) (Nat.m+n∸m≡n b (w + (c + d)))
              (Nat.∸-monoˡ-≤ b (subst (Nat._≤ Fin.toℕ y) reassoc ge)))
      where reassoc : w + (b + (c + d)) ≡ b + (w + (c + d))
            reassoc = sym (Nat.+-assoc w b (c + d)) ■ cong (Nat._+ (c + d)) (Nat.+-comm w b) ■ Nat.+-assoc b w (c + d)

Mv3-mid : ∀ w b c d {rest} (y : 𝔽 (w + (b + (c + (d + rest))))) →
          w Nat.≤ Fin.toℕ y → Fin.toℕ y Nat.< w + (b + (c + d)) →
          Fin.toℕ (Mv3 w b c d y) ≡ Fin.toℕ y Nat.∸ w
Mv3-mid w b c d y wley lt with Fin.toℕ y Nat.<? (w + b)
... | yes p =
    ↑*-lo (Mv w c d) b (assocSwapᵣ w b y) (subst (Nat._< b) (sym smid) (sub-lt wley p))
  ■ smid
  where
    smid : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y Nat.∸ w
    smid = toℕ-assoc-mid w b y wley p
... | no ¬p =
    ↑*-hi (Mv w c d) b (assocSwapᵣ w b y) hge
  ■ cong (b +_) (Mv-mid w c d (Fin.reduce≥ (assocSwapᵣ w b y) hge) gec ltc ■ cong (Nat._∸ w) redℕ)
  ■ ( cong (b +_) (Nat.∸-+-assoc (Fin.toℕ y) b w)
    ■ cong (λ z → b + (Fin.toℕ y Nat.∸ z)) (Nat.+-comm b w)
    ■ cong (b +_) (sym (Nat.∸-+-assoc (Fin.toℕ y) w b))
    ■ Nat.m+[n∸m]≡n (subst (Nat._≤ Fin.toℕ y Nat.∸ w) (Nat.m+n∸m≡n w b) (Nat.∸-monoˡ-≤ w wbley)) )
  where
    wbley : w + b Nat.≤ Fin.toℕ y
    wbley = Nat.≮⇒≥ ¬p
    bley : b Nat.≤ Fin.toℕ y
    bley = Nat.≤-trans (Nat.m≤n+m b w) wbley
    sge : Fin.toℕ (assocSwapᵣ w b y) ≡ Fin.toℕ y
    sge = toℕ-assoc-ge w b y wbley
    hge : b Nat.≤ Fin.toℕ (assocSwapᵣ w b y)
    hge = subst (b Nat.≤_) (sym sge) bley
    redℕ : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) ≡ Fin.toℕ y Nat.∸ b
    redℕ = toℕ-reduce≥ (assocSwapᵣ w b y) hge ■ cong (Nat._∸ b) sge
    wley-yb : w Nat.≤ Fin.toℕ y Nat.∸ b
    wley-yb = subst (Nat._≤ Fin.toℕ y Nat.∸ b) (Nat.m+n∸n≡m w b) (Nat.∸-monoˡ-≤ b wbley)
    gec : w Nat.≤ Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge)
    gec = subst (w Nat.≤_) (sym redℕ) wley-yb
    ltc : Fin.toℕ (Fin.reduce≥ (assocSwapᵣ w b y) hge) Nat.< w + (c + d)
    ltc = subst (Nat._< w + (c + d)) (sym redℕ) (sub-lt bley (subst (Fin.toℕ y Nat.<_) reassoc lt))
      where reassoc : w + (b + (c + d)) ≡ b + (w + (c + d))
            reassoc = sym (Nat.+-assoc w b (c + d)) ■ cong (Nat._+ (c + d)) (Nat.+-comm w b) ■ Nat.+-assoc b w (c + d)

-- The σ-block reassociation: shifting by b then a, swapped, equals shifting by a then b.
renId3 : ∀ a b {m} → ((weaken* ⦃ Kᵣ ⦄ b ·ₖ weaken* ⦃ Kᵣ ⦄ a) ·ₖ assocSwapᵣ a b {m})
                     ≗ (weaken* ⦃ Kᵣ ⦄ a ·ₖ weaken* ⦃ Kᵣ ⦄ b)
renId3 a b {m} z = Fin.toℕ-injective
  ( toℕ-assoc-ge a b (weaken* ⦃ Kᵣ ⦄ a (weaken* ⦃ Kᵣ ⦄ b z)) ge
  ■ tL ■ reassoc ■ sym tR )
  where
    tL : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a (weaken* ⦃ Kᵣ ⦄ b z)) ≡ a + (b + Fin.toℕ z)
    tL = toℕ-wk a (weaken* ⦃ Kᵣ ⦄ b z) ■ cong (a +_) (toℕ-wk b z)
    tR : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ b (weaken* ⦃ Kᵣ ⦄ a z)) ≡ b + (a + Fin.toℕ z)
    tR = toℕ-wk b (weaken* ⦃ Kᵣ ⦄ a z) ■ cong (b +_) (toℕ-wk a z)
    reassoc : a + (b + Fin.toℕ z) ≡ b + (a + Fin.toℕ z)
    reassoc = sym (Nat.+-assoc a b _) ■ cong (Nat._+ Fin.toℕ z) (Nat.+-comm a b) ■ Nat.+-assoc b a _
    ge : a + b Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a (weaken* ⦃ Kᵣ ⦄ b z))
    ge = subst (a + b Nat.≤_) (sym tL)
           (subst (a + b Nat.≤_) (Nat.+-assoc a b _) (Nat.m≤m+n (a + b) (Fin.toℕ z)))

-- Shifting by a then block-swapping equals lifting the shift over the b-block.
renId1 : ∀ a b {m} → (weaken* ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b {m}) ≗ (weaken* ⦃ Kᵣ ⦄ a ↑* b)
renId1 a b {m} z = hh (Fin.splitAt b z) (Fin.join-splitAt b m z)
  where
    motive : 𝔽 (b + m) → Set
    motive w = (weaken* ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b) w ≡ (weaken* ⦃ Kᵣ ⦄ a ↑* b) w
    hh : (s : 𝔽 b ⊎ 𝔽 m) → Fin.join b m s ≡ z → motive z
    hh (inj₁ p) jz = subst motive jz (Fin.toℕ-injective (lhsP ■ sym rhsP))
      where
        geP : a Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a (p ↑ˡ m))
        geP = subst (a Nat.≤_) (sym (toℕ-wk a (p ↑ˡ m))) (Nat.m≤m+n a (Fin.toℕ (p ↑ˡ m)))
        ltP : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a (p ↑ˡ m)) Nat.< a + b
        ltP = subst (Nat._< a + b) (sym (toℕ-wk a (p ↑ˡ m)))
                (Nat.+-monoʳ-< a (subst (Nat._< b) (sym (Fin.toℕ-↑ˡ p m)) (Fin.toℕ<n p)))
        lhsP : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b) (p ↑ˡ m)) ≡ Fin.toℕ p
        lhsP = toℕ-assoc-mid a b (weaken* ⦃ Kᵣ ⦄ a (p ↑ˡ m)) geP ltP
             ■ cong (Nat._∸ a) (toℕ-wk a (p ↑ˡ m)) ■ Nat.m+n∸m≡n a (Fin.toℕ (p ↑ˡ m)) ■ Fin.toℕ-↑ˡ p m
        rhsP : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ a ↑* b) (p ↑ˡ m)) ≡ Fin.toℕ p
        rhsP = toℕ-↑* (weaken* ⦃ Kᵣ ⦄ a) b (p ↑ˡ m)
             ■ cong [ Fin.toℕ , (λ q → b + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a q)) ]′ (Fin.splitAt-↑ˡ b p m)
    hh (inj₂ q) jz = subst motive jz (Fin.toℕ-injective (lhsQ ■ reassoc ■ sym rhsQ))
      where
        geQ : a + b Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a (b ↑ʳ q))
        geQ = subst (a + b Nat.≤_) (sym (toℕ-wk a (b ↑ʳ q) ■ cong (a +_) (Fin.toℕ-↑ʳ b q)))
                (subst (a + b Nat.≤_) (Nat.+-assoc a b _) (Nat.m≤m+n (a + b) (Fin.toℕ q)))
        lhsQ : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b) (b ↑ʳ q)) ≡ a + (b + Fin.toℕ q)
        lhsQ = toℕ-assoc-ge a b (weaken* ⦃ Kᵣ ⦄ a (b ↑ʳ q)) geQ
             ■ toℕ-wk a (b ↑ʳ q) ■ cong (a +_) (Fin.toℕ-↑ʳ b q)
        rhsQ : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ a ↑* b) (b ↑ʳ q)) ≡ b + (a + Fin.toℕ q)
        rhsQ = toℕ-↑* (weaken* ⦃ Kᵣ ⦄ a) b (b ↑ʳ q)
             ■ cong [ Fin.toℕ , (λ q′ → b + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ a q′)) ]′ (Fin.splitAt-↑ʳ b m q)
             ■ cong (b +_) (toℕ-wk a q)
        reassoc : a + (b + Fin.toℕ q) ≡ b + (a + Fin.toℕ q)
        reassoc = sym (Nat.+-assoc a b _) ■ cong (Nat._+ Fin.toℕ q) (Nat.+-comm a b) ■ Nat.+-assoc b a _

-- A b-shift lifted over the a-block, then block-swapped, is just the b-shift.
renId2 : ∀ a b {m} → ((weaken* ⦃ Kᵣ ⦄ b ↑* a) ·ₖ assocSwapᵣ a b {m}) ≗ weaken* ⦃ Kᵣ ⦄ b
renId2 a b {m} z = hh (Fin.splitAt a z) (Fin.join-splitAt a m z)
  where
    motive : 𝔽 (a + m) → Set
    motive w = ((weaken* ⦃ Kᵣ ⦄ b ↑* a) ·ₖ assocSwapᵣ a b) w ≡ weaken* ⦃ Kᵣ ⦄ b w
    hh : (s : 𝔽 a ⊎ 𝔽 m) → Fin.join a m s ≡ z → motive z
    hh (inj₁ p) jz = subst motive jz (Fin.toℕ-injective (lhsP ■ sym rhsP))
      where
        toℕX : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ b ↑* a) (p ↑ˡ m)) ≡ Fin.toℕ p
        toℕX = toℕ-↑* (weaken* ⦃ Kᵣ ⦄ b) a (p ↑ˡ m)
             ■ cong [ Fin.toℕ , (λ q → a + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ b q)) ]′ (Fin.splitAt-↑ˡ a p m)
        lhsP : Fin.toℕ (((weaken* ⦃ Kᵣ ⦄ b ↑* a) ·ₖ assocSwapᵣ a b) (p ↑ˡ m)) ≡ b + Fin.toℕ p
        lhsP = toℕ-assoc-lt a b ((weaken* ⦃ Kᵣ ⦄ b ↑* a) (p ↑ˡ m))
                 (subst (Nat._< a) (sym toℕX) (Fin.toℕ<n p))
             ■ cong (b +_) toℕX
        rhsP : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ b (p ↑ˡ m)) ≡ b + Fin.toℕ p
        rhsP = toℕ-wk b (p ↑ˡ m) ■ cong (b +_) (Fin.toℕ-↑ˡ p m)
    hh (inj₂ q) jz = subst motive jz (Fin.toℕ-injective (lhsQ ■ sym rhsQ))
      where
        toℕX : Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ b ↑* a) (a ↑ʳ q)) ≡ a + (b + Fin.toℕ q)
        toℕX = toℕ-↑* (weaken* ⦃ Kᵣ ⦄ b) a (a ↑ʳ q)
             ■ cong [ Fin.toℕ , (λ q′ → a + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ b q′)) ]′ (Fin.splitAt-↑ʳ a m q)
             ■ cong (a +_) (toℕ-wk b q)
        reassoc : a + (b + Fin.toℕ q) ≡ b + (a + Fin.toℕ q)
        reassoc = sym (Nat.+-assoc a b _) ■ cong (Nat._+ Fin.toℕ q) (Nat.+-comm a b) ■ Nat.+-assoc b a _
        geX : a + b Nat.≤ Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ b ↑* a) (a ↑ʳ q))
        geX = subst (a + b Nat.≤_) (sym toℕX)
                (subst (a + b Nat.≤_) (Nat.+-assoc a b _) (Nat.m≤m+n (a + b) (Fin.toℕ q)))
        lhsQ : Fin.toℕ (((weaken* ⦃ Kᵣ ⦄ b ↑* a) ·ₖ assocSwapᵣ a b) (a ↑ʳ q)) ≡ b + (a + Fin.toℕ q)
        lhsQ = toℕ-assoc-ge a b ((weaken* ⦃ Kᵣ ⦄ b ↑* a) (a ↑ʳ q)) geX ■ toℕX ■ reassoc
        rhsQ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ b (a ↑ʳ q)) ≡ b + (a + Fin.toℕ q)
        rhsQ = toℕ-wk b (a ↑ʳ q) ■ cong (b +_) (Fin.toℕ-↑ʳ a q)

-- Renaming naturality of the binder-free sequencing substitution.

Ubₛ-nat : (b : ℕ) {M M′ : ℕ} (cc : UChan M) (θ : M →ᵣ M′) →
          Ubₛ b (mapᶜ θ cc) ≗ (λ i → Ubₛ b cc i ⋯ θ)
Ubₛ-nat zero          cc            θ ()
Ubₛ-nat (suc zero)    (e₁ , x , e₂) θ zero    = refl
Ubₛ-nat (suc zero)    (e₁ , x , e₂) θ (suc ())
Ubₛ-nat (suc (suc b)) (e₁ , x , e₂) θ zero    = refl
Ubₛ-nat (suc (suc b)) (e₁ , x , e₂) θ (suc i) = Ubₛ-nat (suc b) (K `unit , x , e₂) θ i

++ₛ-cong₂ : ∀ {a b D} {σ₁ σ₁′ : a →ₛ D} {σ₂ σ₂′ : b →ₛ D} →
            σ₁ ≗ σ₁′ → σ₂ ≗ σ₂′ → (σ₁ ++ₛ σ₂) ≗ (σ₁′ ++ₛ σ₂′)
++ₛ-cong₂ {a} h₁ h₂ i = [,]-cong h₁ h₂ (splitAt a i)

-- swapᵣ permutes the first two ++ₛ-blocks of a substitution.
swap-++ₛ : ∀ a b {nn D} (Wb : b →ₛ D) (Wa : a →ₛ D) (Wm : nn →ₛ D) →
           (swapᵣ a b ·ₖ ((Wb ++ₛ Wa) ++ₛ Wm)) ≗ ((Wa ++ₛ Wb) ++ₛ Wm)
swap-++ₛ a b {nn} Wb Wa Wm j = helper (Fin.splitAt (a + b) j)
  where
    helper : (s : 𝔽 (a + b) ⊎ 𝔽 nn) →
      ((Wb ++ₛ Wa) ++ₛ Wm) (Fin.join (b + a) nn (Sum.map₁ (Fin.swap a) s))
      ≡ [ Wa ++ₛ Wb , Wm ]′ s
    helper (inj₂ v) rewrite Fin.splitAt-↑ʳ (b + a) nn v = refl
    helper (inj₁ u) rewrite Fin.splitAt-↑ˡ (b + a) (Fin.swap a u) nn = goalI (Fin.splitAt a u)
      where
        goalI : (s′ : 𝔽 a ⊎ 𝔽 b) →
          (Wb ++ₛ Wa) (Fin.join b a (Sum.swap s′)) ≡ [ Wa , Wb ]′ s′
        goalI (inj₁ p) rewrite Fin.splitAt-↑ʳ b a p = refl
        goalI (inj₂ q) rewrite Fin.splitAt-↑ˡ b q a = refl

-- Renaming naturality of the canonical flattened substitution.

canonₛ-nat : (B : 𝐓.BindGroup) {N N′ : ℕ} (cc : UChan N) (θ : N →ᵣ N′) →
             canonₛ B (mapᶜ θ cc) ≗ (λ i → canonₛ B cc i ⋯ (θ ↑* syncs B))
canonₛ-nat []            cc            θ ()
canonₛ-nat (c ∷ [])      (e₁ , x , e₂) θ j with splitAt c j
... | inj₁ k = Ubₛ-nat c (e₁ , x , e₂) θ k
... | inj₂ ()
canonₛ-nat (c ∷ (b ∷ B)) {N} {N′} (e₁ , x , e₂) θ j =
    subst-Π (+-suc sB N′) (Ubₛ c cc-i′ ++ₛ canonₛ (b ∷ B) cc-r′) j
  ■ cong (subst Tm (+-suc sB N′))
      ( ++ₛ-cong₂ (λ k → cong (λ z → Ubₛ c z k) ccIEq ■ Ubₛ-nat c cc-i Θ k)
                  (λ k → cong (λ z → canonₛ (b ∷ B) z k) ccEq ■ canonₛ-nat (b ∷ B) cc-r (θ ↑) k) j
      ■ sym (++ₛ-⋯ (Ubₛ c cc-i) (canonₛ (b ∷ B) cc-r) Θ j) )
  ■ sym ( cong (_⋯ θ ↑* (suc sB)) (subst-Π (+-suc sB N) (Ubₛ c cc-i ++ₛ canonₛ (b ∷ B) cc-r) j)
        ■ subst-⋯ (+-suc sB N) ((Ubₛ c cc-i ++ₛ canonₛ (b ∷ B) cc-r) j) (θ ↑* (suc sB))
        ■ ΘrelEq ((Ubₛ c cc-i ++ₛ canonₛ (b ∷ B) cc-r) j) )
  where
    sB = syncs (b ∷ B)
    Θ : (sB + suc N) →ᵣ (sB + suc N′)
    Θ = (θ ↑) ↑* sB
    θ⁻ : (sB + suc N) →ᵣ suc (sB + N′)
    θ⁻ = subst (λ z → z →ᵣ suc (sB + N′)) (sym (+-suc sB N)) (θ ↑* suc sB)
    cc-i  = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-i′ = ( (e₁ ⋯ θ) ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc (θ x)) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB )
    cc-r  = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    cc-r′ = ((` 0F) , suc (θ x) , (e₂ ⋯ θ) ⋯ weakenᵣ)
    ΘθEq : Θ ≡ subst (λ z → (sB + suc N) →ᵣ z) (sym (+-suc sB N′)) θ⁻
    ΘθEq = sym ( sym (subst₂→ (sym (+-suc sB N)) (sym (+-suc sB N′)) (θ ↑* suc sB))
               ■ cong (subst₂ _→ᵣ_ (sym (+-suc sB N)) (sym (+-suc sB N′))) (sym (liftCast sB θ))
               ■ subst₂-cancel (+-suc sB N) (+-suc sB N′) Θ )
    ΘrelEq : (t : Tm (sB + suc N)) → t ⋯ θ⁻ ≡ subst Tm (+-suc sB N′) (t ⋯ Θ)
    ΘrelEq t = sym ( cong (λ r → subst Tm (+-suc sB N′) (t ⋯ r)) ΘθEq
                   ■ cong (subst Tm (+-suc sB N′)) (subst-⋯-cod (sym (+-suc sB N′)) t θ⁻)
                   ■ subst-subst-sym′ (+-suc sB N′) )
    ccIEq : cc-i′ ≡ mapᶜ Θ cc-i
    ccIEq = sym (cong₂ _,_ (sym (⋯-↑*-wk (e₁ ⋯ weakenᵣ) (θ ↑) sB) ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (⋯-↑-wk e₁ θ)))
                           (cong₂ _,_ (varΘ sB (θ ↑) (suc x)) (cong `_ (varΘ sB (θ ↑) 0F))))
    ccEq : cc-r′ ≡ mapᶜ (θ ↑) cc-r
    ccEq = cong₂ _,_ refl (cong₂ _,_ refl (⋯-↑-wk e₂ θ))
