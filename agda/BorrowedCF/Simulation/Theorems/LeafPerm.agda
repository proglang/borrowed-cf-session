{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.Theorems.LeafPerm where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.TypedMW as 𝐓R
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Frames
open import BorrowedCF.Simulation.TranslationProperties
open import BorrowedCF.Simulation.Flatten
open import BorrowedCF.Simulation.BlockPermutation
open import BorrowedCF.Simulation.NuExtrusion
open import Data.Nat.Solver using (module +-*-Solver)
open import BorrowedCF.Simulation.Theorems.Toolkit
open import BorrowedCF.Simulation.Theorems.NuSwap
open import BorrowedCF.Simulation.Theorems.CleanT

-- The two canonical leaf substitutions of U-ν-comm (extracted so the leaf
-- data-permutation lemma below is top-level rather than buried in U-ν-comm).
τB-comm : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : 𝐓.BindGroup) →
          (sum B₁ + sum B₂ + m) →ₛ (syncs B₂ + (syncs B₁ + (2 + n)))
τB-comm σ B₁ B₂ =
  ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ
   canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))

τA′-comm : ∀ {m n} (σ : m →ₛ n) (A₁ A₂ : 𝐓.BindGroup) →
           (sum A₁ + sum A₂ + m) →ₛ (syncs A₂ + (syncs A₁ + (2 + n)))
τA′-comm σ A₁ A₂ =
  ((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂)) ++ₛ
   canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs A₁) 1F , K `unit))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂))

-- The leaf 4-block data-permutation under the clean block-transpose cleanT-comm.
subEqLemma : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ A₁ A₂ : 𝐓.BindGroup) →
  ((((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂)) ++ₛ
      canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs A₁) 1F , K `unit))
     ++ₛ (λ i → τB-comm σ B₁ B₂ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂)))
    ·ₖ cleanT-comm (syncs B₁) (syncs B₂) (syncs A₁) (syncs A₂))
  ≗ (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)
     ·ₖ (((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ
          canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit))
         ++ₛ (λ i → τA′-comm σ A₁ A₂ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))))
subEqLemma {m} {n} σ B₁ B₂ A₁ A₂ = go
  where
            sA1 = syncs A₁
            sA2 = syncs A₂
            sB1 = syncs B₁
            sB2 = syncs B₂
            cT = cleanT-comm sB1 sB2 sA1 sA2
            τB = τB-comm σ B₁ B₂
            τA′ = τA′-comm σ A₁ A₂
            go : ((((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2) ++ₛ
                        canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit))
                       ++ₛ (λ i → τB i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2))
                      ·ₖ cT)
                    ≗ (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)
                       ·ₖ (((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2) ++ₛ
                            canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                           ++ₛ (λ i → τA′ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)))
            go j =
                ++ₛ-⋯ AcanL AthL cT j
              ■ ++ₛ-cong₂ caseSA caseSBm j
              ■ sym ( reorg (assocSwapᵣ SA SB j)
                    ■ assocSwap-++ₛ SA SB BthA BcanR Bthσ j )
              where
                SA = sum A₁ + sum A₂
                SB = sum B₁ + sum B₂
                AcanL = (λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                          ++ₛ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                AthL = λ i → τB i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                BcanR = (λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                          ++ₛ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit)
                BthA : sum A₁ + sum A₂ →ₛ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                BthA i = τA′ (i ↑ˡ m) ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                Bthσ : m →ₛ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Bthσ i = τA′ ((sum A₁ + sum A₂) ↑ʳ i) ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                reorg : (BcanR ++ₛ (λ i → τA′ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2))
                        ≗ (BcanR ++ₛ (BthA ++ₛ Bthσ))
                reorg = ++ₛ-congʳ BcanR bthEq
                  where
                    bthEq : (λ i → τA′ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                            ≗ (BthA ++ₛ Bthσ)
                    bthEq i = helper (Fin.splitAt (sum A₁ + sum A₂) i) (Fin.join-splitAt (sum A₁ + sum A₂) m i)
                      where
                        motive : 𝔽 ((sum A₁ + sum A₂) + m) → Set
                        motive k = τA′ k ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                                   ≡ (BthA ++ₛ Bthσ) k
                        helper : (s : 𝔽 (sum A₁ + sum A₂) ⊎ 𝔽 m) → Fin.join (sum A₁ + sum A₂) m s ≡ i → motive i
                        helper (inj₁ u) jk = subst motive jk
                          (sym (cong [ BthA , Bthσ ]′ (Fin.splitAt-↑ˡ (sum A₁ + sum A₂) u m)))
                        helper (inj₂ v) jk = subst motive jk
                          (sym (cong [ BthA , Bthσ ]′ (Fin.splitAt-↑ʳ (sum A₁ + sum A₂) m v)))
                caseSA : (λ i → AcanL i ⋯ cT) ≗ BthA
                caseSA i = h (Fin.splitAt (sum A₁) i) (Fin.join-splitAt (sum A₁) (sum A₂) i)
                  where
                    mot : 𝔽 (sum A₁ + sum A₂) → Set
                    mot k = AcanL k ⋯ cT ≡ BthA k
                    h : (s : 𝔽 (sum A₁) ⊎ 𝔽 (sum A₂)) → Fin.join (sum A₁) (sum A₂) s ≡ i → mot i
                    h (inj₁ p) js = subst mot js
                      ( cong (_⋯ cT) redL
                      ■ cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ cT) (canonₛ-nat A₁ (K `unit , 0F , K `unit) θ₁ p)
                      ■ fusion (Z ⋯ (θ₁ ↑* sA1)) (weaken* ⦃ Kᵣ ⦄ sA2) cT
                      ■ fusion Z (θ₁ ↑* sA1) (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
                      ■ ⋯-cong Z renId₁
                      ■ sym (fusion Z (weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)))
                      ■ sym (fusion (Z ⋯ weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2))
                      ■ sym (fusion (Z ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                      ■ sym redR )
                      where
                        Z : Tm (sA1 + (2 + n))
                        Z = canonₛ A₁ (K `unit , 0F , K `unit) p
                        θ₁ : (2 + n) →ᵣ (2 + (sB2 + (sB1 + (2 + n))))
                        θ₁ z = [ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                               , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ (Fin.splitAt 2 z)
                        redL : AcanL (p ↑ˡ sum A₂) ≡ canonₛ A₁ (K `unit , 0F , K `unit) p ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                        redL = cong [ (λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                    , canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) ]′
                                   (Fin.splitAt-↑ˡ (sum A₁) p (sum A₂))
                        redR : BthA (p ↑ˡ sum A₂)
                               ≡ canonₛ A₁ (K `unit , 0F , K `unit) p ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                                 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                        redR = cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                    ( cong [ ((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                              ++ₛ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit))
                                           , (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2) ]′
                                           (Fin.splitAt-↑ˡ (sum A₁ + sum A₂) (p ↑ˡ sum A₂) m)
                                    ■ cong [ (λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                           , canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) ]′
                                           (Fin.splitAt-↑ˡ (sum A₁) p (sum A₂)) )
                        θ₁ℕ-lo : (w : 𝔽 (2 + n)) → Fin.toℕ w Nat.< 2 → Fin.toℕ (θ₁ w) ≡ Fin.toℕ w
                        θ₁ℕ-lo w lt = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                                                          , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ s))
                                           (Fin.splitAt-< 2 w lt)
                                    ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) (sB2 + (sB1 + (2 + n))) ■ Fin.toℕ-fromℕ< lt
                        θ₁ℕ-hi : (w : 𝔽 (2 + n)) (h : 2 Nat.≤ Fin.toℕ w) →
                                 Fin.toℕ (θ₁ w) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ w
                        θ₁ℕ-hi w h = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                                                          , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ s))
                                          (Fin.splitAt-≥ 2 w h)
                                   ■ Fin.toℕ-↑ʳ 2 (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ Fin.reduce≥ w h)))
                                   ■ cong (2 +_) (Fin.toℕ-↑ʳ sB2 _ ■ cong (sB2 +_) (Fin.toℕ-↑ʳ sB1 _
                                       ■ cong (sB1 +_) (Fin.toℕ-↑ʳ 2 (Fin.reduce≥ w h) ■ cong (2 +_) (toℕ-reduce≥ w h))))
                                   ■ reB
                          where reB : 2 + (sB2 + (sB1 + (2 + (Fin.toℕ w Nat.∸ 2)))) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ w
                                reB = cong (λ t → 2 + (sB2 + (sB1 + t))) (Nat.m+[n∸m]≡n h)
                                    ■ solve 3 (λ b₂ b₁ w → con 2 :+ (b₂ :+ (b₁ :+ w)) := (b₂ :+ (b₁ :+ con 2)) :+ w)
                                              refl sB2 sB1 (Fin.toℕ w)
                                  where open +-*-Solver
                        renId₁ : ((θ₁ ↑* sA1) ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))
                                 ≗ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)))
                        renId₁ z = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
                          where
                            rhsℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB2 (weaken* ⦃ Kᵣ ⦄ sB1 (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ sA2 z))))
                                   ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                            rhsℕ = toℕ-wk sB2 _ ■ cong (sB2 +_) (toℕ-wk sB1 _ ■ cong (sB1 +_)
                                     (toℕ-wk 2 _ ■ cong (2 +_) (toℕ-wk sA2 z)))
                            lhsℕ : Fin.toℕ (cT (weaken* ⦃ Kᵣ ⦄ sA2 ((θ₁ ↑* sA1) z)))
                                   ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                            lhsℕ with Fin.toℕ z Nat.<? sA1
                            ... | yes z<a =
                                  cleanTℕ-lt sB1 sB2 sA1 sA2 (weaken* ⦃ Kᵣ ⦄ sA2 X) bnd
                                ■ cong ((sB2 + (sB1 + 2)) +_) eqX ■ assoc1
                              where
                                X = (θ₁ ↑* sA1) z
                                eqX : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X) ≡ sA2 + Fin.toℕ z
                                eqX = toℕ-wk sA2 X ■ cong (sA2 +_) (↑*-lo θ₁ sA1 z z<a)
                                bnd : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X) Nat.< sA2 + (sA1 + 2)
                                bnd = subst (Nat._< sA2 + (sA1 + 2)) (sym eqX)
                                        (Nat.+-monoʳ-< sA2 (Nat.<-≤-trans z<a (Nat.m≤m+n sA1 2)))
                                assoc1 : (sB2 + (sB1 + 2)) + (sA2 + Fin.toℕ z) ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                                assoc1 = solve 4 (λ b₂ b₁ a w → (b₂ :+ (b₁ :+ con 2)) :+ (a :+ w)
                                                              := b₂ :+ (b₁ :+ (con 2 :+ (a :+ w)))) refl sB2 sB1 sA2 (Fin.toℕ z)
                                  where open +-*-Solver
                            ... | no z≥a with Fin.toℕ z Nat.<? (sA1 + 2)
                            ...    | yes z<a2 =
                                     cleanTℕ-lt sB1 sB2 sA1 sA2 (weaken* ⦃ Kᵣ ⦄ sA2 X) bnd
                                   ■ cong ((sB2 + (sB1 + 2)) +_) eqX ■ assoc1
                                 where
                                   alez = Nat.≮⇒≥ z≥a
                                   X = (θ₁ ↑* sA1) z
                                   tX : Fin.toℕ X ≡ Fin.toℕ z
                                   tX = ↑*-hi θ₁ sA1 z alez
                                      ■ cong (sA1 +_) (θ₁ℕ-lo (Fin.reduce≥ z alez)
                                                         (subst (Nat._< 2) (sym (toℕ-reduce≥ z alez)) (sub-lt alez z<a2))
                                                       ■ toℕ-reduce≥ z alez)
                                      ■ Nat.m+[n∸m]≡n alez
                                   eqX : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X) ≡ sA2 + Fin.toℕ z
                                   eqX = toℕ-wk sA2 X ■ cong (sA2 +_) tX
                                   bnd : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X) Nat.< sA2 + (sA1 + 2)
                                   bnd = subst (Nat._< sA2 + (sA1 + 2)) (sym eqX) (Nat.+-monoʳ-< sA2 z<a2)
                                   assoc1 : (sB2 + (sB1 + 2)) + (sA2 + Fin.toℕ z) ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                                   assoc1 = solve 4 (λ b₂ b₁ a w → (b₂ :+ (b₁ :+ con 2)) :+ (a :+ w)
                                                                 := b₂ :+ (b₁ :+ (con 2 :+ (a :+ w)))) refl sB2 sB1 sA2 (Fin.toℕ z)
                                     where open +-*-Solver
                            ...    | no z≥a2 =
                                     cleanTℕ-ge sB1 sB2 sA1 sA2 (weaken* ⦃ Kᵣ ⦄ sA2 X) bnd ■ eqX ■ arith
                                 where
                                   alez = Nat.≮⇒≥ z≥a
                                   a2lez = Nat.≮⇒≥ z≥a2
                                   X = (θ₁ ↑* sA1) z
                                   2≤R : 2 Nat.≤ Fin.toℕ z Nat.∸ sA1
                                   2≤R = subst (Nat._≤ Fin.toℕ z Nat.∸ sA1) (Nat.m+n∸m≡n sA1 2) (Nat.∸-monoˡ-≤ sA1 a2lez)
                                   2≤red : 2 Nat.≤ Fin.toℕ (Fin.reduce≥ z alez)
                                   2≤red = subst (2 Nat.≤_) (sym (toℕ-reduce≥ z alez)) 2≤R
                                   tX : Fin.toℕ X ≡ sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1))
                                   tX = ↑*-hi θ₁ sA1 z alez
                                      ■ cong (sA1 +_) (θ₁ℕ-hi (Fin.reduce≥ z alez) 2≤red
                                                       ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ z alez))
                                   eqX : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X)
                                         ≡ sA2 + (sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)))
                                   eqX = toℕ-wk sA2 X ■ cong (sA2 +_) tX
                                   2≤R+ : 2 + (sB2 + (sB1 + 2)) Nat.≤ (sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)
                                   2≤R+ = subst (Nat._≤ (sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)) (Nat.+-comm (sB2 + (sB1 + 2)) 2)
                                            (Nat.+-monoʳ-≤ (sB2 + (sB1 + 2)) 2≤R)
                                   bnd : (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 X)
                                   bnd = subst ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤_) (sym eqX)
                                           (subst (Nat._≤ sA2 + (sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)))) (sym waWBeq)
                                             (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 2≤R+)))
                                     where waWBeq : (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                                           waWBeq = solve 4 (λ a₂ a₁ b₂ b₁ → (a₂ :+ (a₁ :+ con 2)) :+ (b₂ :+ (b₁ :+ con 2))
                                                                           := a₂ :+ (a₁ :+ (con 2 :+ (b₂ :+ (b₁ :+ con 2))))) refl sA2 sA1 sB2 sB1
                                             where open +-*-Solver
                                   arith : sA2 + (sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)))
                                           ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                                   arith = solve₅ ■ cong (λ t → sA2 + ((sB2 + (sB1 + 2)) + t)) (Nat.m+[n∸m]≡n alez) ■ solve₅′
                                     where
                                       open +-*-Solver
                                       solve₅ : sA2 + (sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA1)))
                                                ≡ sA2 + ((sB2 + (sB1 + 2)) + (sA1 + (Fin.toℕ z Nat.∸ sA1)))
                                       solve₅ = solve 5 (λ a₂ a₁ b₂ b₁ r → a₂ :+ (a₁ :+ ((b₂ :+ (b₁ :+ con 2)) :+ r))
                                                                        := a₂ :+ ((b₂ :+ (b₁ :+ con 2)) :+ (a₁ :+ r))) refl sA2 sA1 sB2 sB1 (Fin.toℕ z Nat.∸ sA1)
                                       solve₅′ : sA2 + ((sB2 + (sB1 + 2)) + Fin.toℕ z) ≡ sB2 + (sB1 + (2 + (sA2 + Fin.toℕ z)))
                                       solve₅′ = solve 4 (λ a₂ b₂ b₁ w → a₂ :+ ((b₂ :+ (b₁ :+ con 2)) :+ w)
                                                                       := b₂ :+ (b₁ :+ (con 2 :+ (a₂ :+ w)))) refl sA2 sB2 sB1 (Fin.toℕ z)
                    h (inj₂ q) js = subst mot js
                      ( cong (_⋯ cT) (redL2 ■ cong (λ cc → canonₛ A₂ cc q) (sym mapᶜEq))
                      ■ cong (_⋯ cT) (canonₛ-nat A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) θ₂ q)
                      ■ fusion Z₂ (θ₂ ↑* sA2) cT
                      ■ ⋯-cong Z₂ renId₂
                      ■ sym (fusion Z₂ (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2))
                      ■ sym (fusion (Z₂ ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                      ■ sym redR2 )
                      where
                        θ₁′ : (2 + n) →ᵣ (2 + (sB2 + (sB1 + (2 + n))))
                        θ₁′ z = [ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                                , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ (Fin.splitAt 2 z)
                        θ₂ : (sA1 + (2 + n)) →ᵣ (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
                        θ₂ z = [ (λ u → u ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))) , (λ w → sA1 ↑ʳ θ₁′ w) ]′ (Fin.splitAt sA1 z)
                        Z₂ : Tm (sA2 + (sA1 + (2 + n)))
                        Z₂ = canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) q
                        mapᶜEq : mapᶜ θ₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                                 ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                        mapᶜEq = cong₂ _,_ refl (cong₂ _,_ θ₂eq refl)
                          where
                            θ₂eq : θ₂ (weaken* ⦃ Kᵣ ⦄ sA1 1F) ≡ weaken* ⦃ Kᵣ ⦄ sA1 1F
                            θ₂eq = cong θ₂ (weaken*~↑ʳ ⦃ Kᵣ ⦄ sA1 1F)
                                 ■ cong [ (λ u → u ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))) , (λ w → sA1 ↑ʳ θ₁′ w) ]′
                                        (Fin.splitAt-↑ʳ sA1 (2 + n) 1F)
                                 ■ sym (weaken*~↑ʳ ⦃ Kᵣ ⦄ sA1 1F)
                        redL2 : AcanL (sum A₁ ↑ʳ q) ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) q
                        redL2 = cong [ (λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                     , canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) ]′
                                    (Fin.splitAt-↑ʳ (sum A₁) (sum A₂) q)
                        redR2 : BthA (sum A₁ ↑ʳ q)
                                ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) q
                                  ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                        redR2 = cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                     ( cong [ ((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                               ++ₛ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit))
                                            , (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2) ]′
                                            (Fin.splitAt-↑ˡ (sum A₁ + sum A₂) (sum A₁ ↑ʳ q) m)
                                     ■ cong [ (λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                            , canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) ]′
                                            (Fin.splitAt-↑ʳ (sum A₁) (sum A₂) q) )
                        θ₁′ℕ-lo : (w : 𝔽 (2 + n)) → Fin.toℕ w Nat.< 2 → Fin.toℕ (θ₁′ w) ≡ Fin.toℕ w
                        θ₁′ℕ-lo w lt = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                                                            , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ s))
                                            (Fin.splitAt-< 2 w lt)
                                     ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) (sB2 + (sB1 + (2 + n))) ■ Fin.toℕ-fromℕ< lt
                        θ₁′ℕ-hi : (w : 𝔽 (2 + n)) (h : 2 Nat.≤ Fin.toℕ w) →
                                  Fin.toℕ (θ₁′ w) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ w
                        θ₁′ℕ-hi w h = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sB2 + (sB1 + (2 + n))))
                                                           , (λ k → 2 ↑ʳ (sB2 ↑ʳ (sB1 ↑ʳ (2 ↑ʳ k)))) ]′ s))
                                           (Fin.splitAt-≥ 2 w h)
                                    ■ Fin.toℕ-↑ʳ 2 _ ■ cong (2 +_) (Fin.toℕ-↑ʳ sB2 _ ■ cong (sB2 +_) (Fin.toℕ-↑ʳ sB1 _
                                        ■ cong (sB1 +_) (Fin.toℕ-↑ʳ 2 (Fin.reduce≥ w h) ■ cong (2 +_) (toℕ-reduce≥ w h))))
                                    ■ cong (λ t → 2 + (sB2 + (sB1 + t))) (Nat.m+[n∸m]≡n h)
                                    ■ solve 3 (λ b₂ b₁ w → con 2 :+ (b₂ :+ (b₁ :+ w)) := (b₂ :+ (b₁ :+ con 2)) :+ w) refl sB2 sB1 (Fin.toℕ w)
                          where open +-*-Solver
                        θ₂ℕ-lo : (w : 𝔽 (sA1 + (2 + n))) → Fin.toℕ w Nat.< sA1 + 2 → Fin.toℕ (θ₂ w) ≡ Fin.toℕ w
                        θ₂ℕ-lo w lt with Fin.toℕ w Nat.<? sA1
                        ... | yes w<a = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))) , (λ w′ → sA1 ↑ʳ θ₁′ w′) ]′ s))
                                             (Fin.splitAt-< sA1 w w<a)
                                      ■ Fin.toℕ-↑ˡ (Fin.fromℕ< w<a) (2 + (sB2 + (sB1 + (2 + n)))) ■ Fin.toℕ-fromℕ< w<a
                        ... | no w≥a = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))) , (λ w′ → sA1 ↑ʳ θ₁′ w′) ]′ s))
                                            (Fin.splitAt-≥ sA1 w (Nat.≮⇒≥ w≥a))
                                     ■ Fin.toℕ-↑ʳ sA1 (θ₁′ (Fin.reduce≥ w (Nat.≮⇒≥ w≥a)))
                                     ■ cong (sA1 +_) (θ₁′ℕ-lo (Fin.reduce≥ w (Nat.≮⇒≥ w≥a))
                                                        (subst (Nat._< 2) (sym (toℕ-reduce≥ w (Nat.≮⇒≥ w≥a))) (sub-lt (Nat.≮⇒≥ w≥a) lt))
                                                      ■ toℕ-reduce≥ w (Nat.≮⇒≥ w≥a))
                                     ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ w≥a)
                        θ₂ℕ-hi : (w : 𝔽 (sA1 + (2 + n))) (h : sA1 + 2 Nat.≤ Fin.toℕ w) →
                                 Fin.toℕ (θ₂ w) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ w
                        θ₂ℕ-hi w h = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))) , (λ w′ → sA1 ↑ʳ θ₁′ w′) ]′ s))
                                          (Fin.splitAt-≥ sA1 w sA1≤w)
                                   ■ Fin.toℕ-↑ʳ sA1 (θ₁′ (Fin.reduce≥ w sA1≤w))
                                   ■ cong (sA1 +_) (θ₁′ℕ-hi (Fin.reduce≥ w sA1≤w) 2≤red
                                                    ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ w sA1≤w))
                                   ■ ar
                          where
                            sA1≤w : sA1 Nat.≤ Fin.toℕ w
                            sA1≤w = Nat.≤-trans (Nat.m≤m+n sA1 2) h
                            2≤red : 2 Nat.≤ Fin.toℕ (Fin.reduce≥ w sA1≤w)
                            2≤red = subst (2 Nat.≤_) (sym (toℕ-reduce≥ w sA1≤w))
                                      (subst (Nat._≤ Fin.toℕ w Nat.∸ sA1) (Nat.m+n∸m≡n sA1 2) (Nat.∸-monoˡ-≤ sA1 h))
                            ar : sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ w Nat.∸ sA1)) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ w
                            ar = solve₅ ■ cong ((sB2 + (sB1 + 2)) +_) (Nat.m+[n∸m]≡n sA1≤w)
                              where open +-*-Solver
                                    solve₅ : sA1 + ((sB2 + (sB1 + 2)) + (Fin.toℕ w Nat.∸ sA1))
                                             ≡ (sB2 + (sB1 + 2)) + (sA1 + (Fin.toℕ w Nat.∸ sA1))
                                    solve₅ = solve 4 (λ a₁ b₂ b₁ r → a₁ :+ ((b₂ :+ (b₁ :+ con 2)) :+ r)
                                                                  := (b₂ :+ (b₁ :+ con 2)) :+ (a₁ :+ r)) refl sA1 sB2 sB1 (Fin.toℕ w Nat.∸ sA1)
                        renId₂ : ((θ₂ ↑* sA2) ·ₖ cT) ≗ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2))
                        renId₂ z = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
                          where
                            rhsℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB2 (weaken* ⦃ Kᵣ ⦄ sB1 (weaken* ⦃ Kᵣ ⦄ 2 z)))
                                   ≡ sB2 + (sB1 + (2 + Fin.toℕ z))
                            rhsℕ = toℕ-wk sB2 _ ■ cong (sB2 +_) (toℕ-wk sB1 _ ■ cong (sB1 +_) (toℕ-wk 2 z))
                            θ₂shift-lo : Fin.toℕ z Nat.< sA2 + (sA1 + 2) → Fin.toℕ ((θ₂ ↑* sA2) z) ≡ Fin.toℕ z
                            θ₂shift-lo lt with Fin.toℕ z Nat.<? sA2
                            ... | yes z<a = ↑*-lo θ₂ sA2 z z<a
                            ... | no z≥a = ↑*-hi θ₂ sA2 z (Nat.≮⇒≥ z≥a)
                                         ■ cong (sA2 +_) (θ₂ℕ-lo (Fin.reduce≥ z (Nat.≮⇒≥ z≥a))
                                                            (subst (Nat._< sA1 + 2) (sym (toℕ-reduce≥ z (Nat.≮⇒≥ z≥a))) (sub-lt (Nat.≮⇒≥ z≥a) lt))
                                                          ■ toℕ-reduce≥ z (Nat.≮⇒≥ z≥a))
                                         ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ z≥a)
                            θ₂shift-hi : sA2 + (sA1 + 2) Nat.≤ Fin.toℕ z → Fin.toℕ ((θ₂ ↑* sA2) z) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ z
                            θ₂shift-hi ge = ↑*-hi θ₂ sA2 z sa2≤z
                                          ■ cong (sA2 +_) (θ₂ℕ-hi (Fin.reduce≥ z sa2≤z) 2red
                                                           ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ z sa2≤z))
                                          ■ ar2
                              where
                                sa2≤z : sA2 Nat.≤ Fin.toℕ z
                                sa2≤z = Nat.≤-trans (Nat.m≤m+n sA2 (sA1 + 2)) ge
                                2red : sA1 + 2 Nat.≤ Fin.toℕ (Fin.reduce≥ z sa2≤z)
                                2red = subst (sA1 + 2 Nat.≤_) (sym (toℕ-reduce≥ z sa2≤z))
                                         (subst (Nat._≤ Fin.toℕ z Nat.∸ sA2) (Nat.m+n∸m≡n sA2 (sA1 + 2)) (Nat.∸-monoˡ-≤ sA2 ge))
                                ar2 : sA2 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z Nat.∸ sA2)) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ z
                                ar2 = solve 4 (λ a₂ b₂ b₁ r → a₂ :+ ((b₂ :+ (b₁ :+ con 2)) :+ r)
                                                            := (b₂ :+ (b₁ :+ con 2)) :+ (a₂ :+ r)) refl sA2 sB2 sB1 (Fin.toℕ z Nat.∸ sA2)
                                    ■ cong ((sB2 + (sB1 + 2)) +_) (Nat.m+[n∸m]≡n sa2≤z)
                                  where open +-*-Solver
                            lhsℕ : Fin.toℕ (cT ((θ₂ ↑* sA2) z)) ≡ sB2 + (sB1 + (2 + Fin.toℕ z))
                            lhsℕ with Fin.toℕ z Nat.<? (sA2 + (sA1 + 2))
                            ... | yes z<wa = cleanTℕ-lt sB1 sB2 sA1 sA2 ((θ₂ ↑* sA2) z)
                                               (subst (Nat._< sA2 + (sA1 + 2)) (sym (θ₂shift-lo z<wa)) z<wa)
                                           ■ cong ((sB2 + (sB1 + 2)) +_) (θ₂shift-lo z<wa)
                                           ■ solve 3 (λ b₂ b₁ w → (b₂ :+ (b₁ :+ con 2)) :+ w := b₂ :+ (b₁ :+ (con 2 :+ w))) refl sB2 sB1 (Fin.toℕ z)
                              where open +-*-Solver
                            ... | no z≥wa = cleanTℕ-ge sB1 sB2 sA1 sA2 ((θ₂ ↑* sA2) z) gebnd
                                          ■ θ₂shift-hi (Nat.≮⇒≥ z≥wa)
                                          ■ solve 3 (λ b₂ b₁ w → (b₂ :+ (b₁ :+ con 2)) :+ w := b₂ :+ (b₁ :+ (con 2 :+ w))) refl sB2 sB1 (Fin.toℕ z)
                              where
                                open +-*-Solver
                                gebnd : (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ ((θ₂ ↑* sA2) z)
                                gebnd = subst ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤_) (sym (θ₂shift-hi (Nat.≮⇒≥ z≥wa)))
                                          (subst (Nat._≤ (sB2 + (sB1 + 2)) + Fin.toℕ z) (Nat.+-comm (sB2 + (sB1 + 2)) (sA2 + (sA1 + 2)))
                                            (Nat.+-monoʳ-≤ (sB2 + (sB1 + 2)) (Nat.≮⇒≥ z≥wa)))
                θB : (2 + n) →ᵣ (2 + (sA2 + (sA1 + (2 + n))))
                θB z = [ (λ p′ → p′ ↑ˡ (sA2 + (sA1 + (2 + n))))
                       , (λ k → 2 ↑ʳ (sA2 ↑ʳ (sA1 ↑ʳ (2 ↑ʳ k)))) ]′ (Fin.splitAt 2 z)
                θBℕ-lo : (w : 𝔽 (2 + n)) → Fin.toℕ w Nat.< 2 → Fin.toℕ (θB w) ≡ Fin.toℕ w
                θBℕ-lo w lt = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sA2 + (sA1 + (2 + n))))
                                                   , (λ k → 2 ↑ʳ (sA2 ↑ʳ (sA1 ↑ʳ (2 ↑ʳ k)))) ]′ s)) (Fin.splitAt-< 2 w lt)
                            ■ Fin.toℕ-↑ˡ (Fin.fromℕ< lt) (sA2 + (sA1 + (2 + n))) ■ Fin.toℕ-fromℕ< lt
                θBℕ-hi : (w : 𝔽 (2 + n)) (h : 2 Nat.≤ Fin.toℕ w) → Fin.toℕ (θB w) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                θBℕ-hi w h = cong (λ s → Fin.toℕ ([ (λ p′ → p′ ↑ˡ (sA2 + (sA1 + (2 + n))))
                                                  , (λ k → 2 ↑ʳ (sA2 ↑ʳ (sA1 ↑ʳ (2 ↑ʳ k)))) ]′ s)) (Fin.splitAt-≥ 2 w h)
                           ■ Fin.toℕ-↑ʳ 2 _ ■ cong (2 +_) (Fin.toℕ-↑ʳ sA2 _ ■ cong (sA2 +_) (Fin.toℕ-↑ʳ sA1 _
                               ■ cong (sA1 +_) (Fin.toℕ-↑ʳ 2 (Fin.reduce≥ w h) ■ cong (2 +_) (toℕ-reduce≥ w h))))
                           ■ cong (λ t → 2 + (sA2 + (sA1 + t))) (Nat.m+[n∸m]≡n h)
                           ■ solve 3 (λ a₂ a₁ w → con 2 :+ (a₂ :+ (a₁ :+ w)) := (a₂ :+ (a₁ :+ con 2)) :+ w) refl sA2 sA1 (Fin.toℕ w)
                  where open +-*-Solver
                -- cT's action on a B-block var (toℕ in [WA, WA+WB)): mid, sends it down by WA.
                renIdB1 : (weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))))
                          ≗ ((θB ↑* sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
                renIdB1 w with Fin.toℕ w Nat.<? (sB1 + 2)
                ... | yes w<wb = Fin.toℕ-injective
                      ( cleanTℕ-mid sB1 sB2 sA1 sA2 Ww
                          (subst (sA2 + (sA1 + 2) Nat.≤_) (sym wℕ) (Nat.m≤m+n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ w)))
                          (subst (Nat._< (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2))) (sym wℕ)
                            (Nat.+-monoʳ-< (sA2 + (sA1 + 2)) (Nat.+-monoʳ-< sB2 w<wb)))
                      ■ cong (Nat._∸ (sA2 + (sA1 + 2))) wℕ ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ w)
                      ■ sym (toℕ-wk sB2 ((θB ↑* sB1) w) ■ cong (sB2 +_) shiftlo) )
                  where
                    Ww = weaken* ⦃ Kᵣ ⦄ sA2 (weaken* ⦃ Kᵣ ⦄ sA1 (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ sB2 w)))
                    wℕ : Fin.toℕ Ww ≡ (sA2 + (sA1 + 2)) + (sB2 + Fin.toℕ w)
                    wℕ = toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 _ ■ cong (2 +_) (toℕ-wk sB2 w)))
                       ■ solve 3 (λ a₂ a₁ x → a₂ :+ (a₁ :+ (con 2 :+ x)) := (a₂ :+ (a₁ :+ con 2)) :+ x) refl sA2 sA1 (sB2 + Fin.toℕ w)
                      where open +-*-Solver
                    shiftlo : Fin.toℕ ((θB ↑* sB1) w) ≡ Fin.toℕ w
                    shiftlo with Fin.toℕ w Nat.<? sB1
                    ... | yes w<b = ↑*-lo θB sB1 w w<b
                    ... | no w≥b = ↑*-hi θB sB1 w (Nat.≮⇒≥ w≥b)
                                 ■ cong (sB1 +_) (θBℕ-lo (Fin.reduce≥ w (Nat.≮⇒≥ w≥b))
                                                    (subst (Nat._< 2) (sym (toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))) (sub-lt (Nat.≮⇒≥ w≥b) w<wb))
                                                  ■ toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))
                                 ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ w≥b)
                ... | no w≥wb = Fin.toℕ-injective
                      ( cleanTℕ-ge sB1 sB2 sA1 sA2 Ww
                          (subst ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤_) (sym wℕ)
                            (Nat.+-monoʳ-≤ (sA2 + (sA1 + 2)) (Nat.+-monoʳ-≤ sB2 (Nat.≮⇒≥ w≥wb))))
                      ■ wℕ
                      ■ solve 3 (λ a b x → a :+ (b :+ x) := b :+ (a :+ x)) refl (sA2 + (sA1 + 2)) sB2 (Fin.toℕ w)
                      ■ sym (toℕ-wk sB2 ((θB ↑* sB1) w) ■ cong (sB2 +_) shifthi) )
                  where
                    open +-*-Solver
                    Ww = weaken* ⦃ Kᵣ ⦄ sA2 (weaken* ⦃ Kᵣ ⦄ sA1 (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ sB2 w)))
                    wℕ : Fin.toℕ Ww ≡ (sA2 + (sA1 + 2)) + (sB2 + Fin.toℕ w)
                    wℕ = toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 _ ■ cong (2 +_) (toℕ-wk sB2 w)))
                       ■ solve 3 (λ a₂ a₁ x → a₂ :+ (a₁ :+ (con 2 :+ x)) := (a₂ :+ (a₁ :+ con 2)) :+ x) refl sA2 sA1 (sB2 + Fin.toℕ w)
                    sb1≤w = Nat.≤-trans (Nat.m≤m+n sB1 2) (Nat.≮⇒≥ w≥wb)
                    shifthi : Fin.toℕ ((θB ↑* sB1) w) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                    shifthi = ↑*-hi θB sB1 w sb1≤w
                            ■ cong (sB1 +_) (θBℕ-hi (Fin.reduce≥ w sb1≤w)
                                               (subst (2 Nat.≤_) (sym (toℕ-reduce≥ w sb1≤w))
                                                 (subst (Nat._≤ Fin.toℕ w Nat.∸ sB1) (Nat.m+n∸m≡n sB1 2) (Nat.∸-monoˡ-≤ sB1 (Nat.≮⇒≥ w≥wb))))
                                             ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ w sb1≤w))
                            ■ solve 4 (λ a₂ a₁ b₁ r → b₁ :+ ((a₂ :+ (a₁ :+ con 2)) :+ r) := (a₂ :+ (a₁ :+ con 2)) :+ (b₁ :+ r)) refl sA2 sA1 sB1 (Fin.toℕ w Nat.∸ sB1)
                            ■ cong ((sA2 + (sA1 + 2)) +_) (Nat.m+[n∸m]≡n sb1≤w)
                caseSBm : (λ i → AthL i ⋯ cT) ≗ (BcanR ++ₛ Bthσ)
                caseSBm i = hB (Fin.splitAt (sum B₁ + sum B₂) i) (Fin.join-splitAt (sum B₁ + sum B₂) m i)
                  where
                    motB : 𝔽 ((sum B₁ + sum B₂) + m) → Set
                    motB k = AthL k ⋯ cT ≡ (BcanR ++ₛ Bthσ) k
                    hB : (s : 𝔽 (sum B₁ + sum B₂) ⊎ 𝔽 m) → Fin.join (sum B₁ + sum B₂) m s ≡ i → motB i
                    hB (inj₁ u) ju = subst motB ju
                      (hB1 (Fin.splitAt (sum B₁) u) (Fin.join-splitAt (sum B₁) (sum B₂) u))
                      where
                        hB1 : (s′ : 𝔽 (sum B₁) ⊎ 𝔽 (sum B₂)) → Fin.join (sum B₁) (sum B₂) s′ ≡ u →
                              motB (u ↑ˡ m)
                        hB1 (inj₁ p) jp = subst (λ u′ → motB (u′ ↑ˡ m)) jp
                          ( cong (_⋯ cT) redLB1
                          ■ fusion (ZB ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) cT
                          ■ fusion (ZB ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
                          ■ fusion (ZB ⋯ weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))
                          ■ fusion ZB (weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)))
                          ■ ⋯-cong ZB renIdB1
                          ■ sym (fusion ZB (θB ↑* sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                          ■ sym (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2) (canonₛ-nat B₁ (K `unit , 0F , K `unit) θB p))
                          ■ sym redRB1 )
                          where
                            ZB : Tm (sB1 + (2 + n))
                            ZB = canonₛ B₁ (K `unit , 0F , K `unit) p
                            redLB1 : AthL (p ↑ˡ sum B₂ ↑ˡ m)
                                     ≡ canonₛ B₁ (K `unit , 0F , K `unit) p ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                                       ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                            redLB1 = cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                          ( cong [ ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                                    ++ₛ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                                                 , (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2) ]′
                                                 (Fin.splitAt-↑ˡ (sum B₁ + sum B₂) (p ↑ˡ sum B₂) m)
                                          ■ cong [ (λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                                 , canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) ]′
                                                 (Fin.splitAt-↑ˡ (sum B₁) p (sum B₂)) )
                            redRB1 : (BcanR ++ₛ Bthσ) (p ↑ˡ sum B₂ ↑ˡ m)
                                     ≡ canonₛ B₁ (K `unit , 0F , K `unit) p ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                            redRB1 = cong [ ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                             ++ₛ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                                          , Bthσ ]′
                                          (Fin.splitAt-↑ˡ (sum B₁ + sum B₂) (p ↑ˡ sum B₂) m)
                                   ■ cong [ (λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                          , canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) ]′
                                          (Fin.splitAt-↑ˡ (sum B₁) p (sum B₂))
                        hB1 (inj₂ q) jq = subst (λ u′ → motB (u′ ↑ˡ m)) jq
                          ( cong (_⋯ cT) redLB2
                          ■ fusion (ZB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) cT
                          ■ fusion (ZB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
                          ■ fusion ZB2 (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))
                          ■ ⋯-cong ZB2 renIdB2
                          ■ sym (canonₛ-nat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) θB2 q)
                          ■ cong (λ c → canonₛ B₂ c q) mapᶜEqB
                          ■ sym redRB2 )
                          where
                            ZB2 : Tm (sB2 + (sB1 + (2 + n)))
                            ZB2 = canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) q
                            θB2 : (sB1 + (2 + n)) →ᵣ (sB1 + (2 + (sA2 + (sA1 + (2 + n)))))
                            θB2 z = [ (λ u → u ↑ˡ (2 + (sA2 + (sA1 + (2 + n))))) , (λ w → sB1 ↑ʳ θB w) ]′ (Fin.splitAt sB1 z)
                            mapᶜEqB : mapᶜ θB2 (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit)
                                      ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit)
                            mapᶜEqB = cong₂ _,_ refl (cong₂ _,_ θB2eq refl)
                              where
                                θB2eq : θB2 (weaken* ⦃ Kᵣ ⦄ sB1 1F) ≡ weaken* ⦃ Kᵣ ⦄ sB1 1F
                                θB2eq = cong θB2 (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB1 1F)
                                      ■ cong [ (λ u → u ↑ˡ (2 + (sA2 + (sA1 + (2 + n))))) , (λ w → sB1 ↑ʳ θB w) ]′
                                             (Fin.splitAt-↑ʳ sB1 (2 + n) 1F)
                                      ■ sym (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB1 1F)
                            redLB2 : AthL ((sum B₁ ↑ʳ q) ↑ˡ m)
                                     ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) q
                                       ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                            redLB2 = cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                                          ( cong [ ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                                    ++ₛ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                                                 , (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2) ]′
                                                 (Fin.splitAt-↑ˡ (sum B₁ + sum B₂) (sum B₁ ↑ʳ q) m)
                                          ■ cong [ (λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                                 , canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) ]′
                                                 (Fin.splitAt-↑ʳ (sum B₁) (sum B₂) q) )
                            redRB2 : (BcanR ++ₛ Bthσ) ((sum B₁ ↑ʳ q) ↑ˡ m)
                                     ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) q
                            redRB2 = cong [ ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                             ++ₛ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                                          , Bthσ ]′
                                          (Fin.splitAt-↑ˡ (sum B₁ + sum B₂) (sum B₁ ↑ʳ q) m)
                                   ■ cong [ (λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                                          , canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) ]′
                                          (Fin.splitAt-↑ʳ (sum B₁) (sum B₂) q)
                            θB2ℕ-lo : (w : 𝔽 (sB1 + (2 + n))) → Fin.toℕ w Nat.< sB1 + 2 → Fin.toℕ (θB2 w) ≡ Fin.toℕ w
                            θB2ℕ-lo w lt with Fin.toℕ w Nat.<? sB1
                            ... | yes w<b = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sA2 + (sA1 + (2 + n))))) , (λ w′ → sB1 ↑ʳ θB w′) ]′ s))
                                                 (Fin.splitAt-< sB1 w w<b)
                                          ■ Fin.toℕ-↑ˡ (Fin.fromℕ< w<b) (2 + (sA2 + (sA1 + (2 + n)))) ■ Fin.toℕ-fromℕ< w<b
                            ... | no w≥b = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sA2 + (sA1 + (2 + n))))) , (λ w′ → sB1 ↑ʳ θB w′) ]′ s))
                                                (Fin.splitAt-≥ sB1 w (Nat.≮⇒≥ w≥b))
                                         ■ Fin.toℕ-↑ʳ sB1 (θB (Fin.reduce≥ w (Nat.≮⇒≥ w≥b)))
                                         ■ cong (sB1 +_) (θBℕ-lo (Fin.reduce≥ w (Nat.≮⇒≥ w≥b))
                                                            (subst (Nat._< 2) (sym (toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))) (sub-lt (Nat.≮⇒≥ w≥b) lt))
                                                          ■ toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))
                                         ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ w≥b)
                            θB2ℕ-hi : (w : 𝔽 (sB1 + (2 + n))) (h : sB1 + 2 Nat.≤ Fin.toℕ w) →
                                      Fin.toℕ (θB2 w) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                            θB2ℕ-hi w h = cong (λ s → Fin.toℕ ([ (λ u → u ↑ˡ (2 + (sA2 + (sA1 + (2 + n))))) , (λ w′ → sB1 ↑ʳ θB w′) ]′ s))
                                               (Fin.splitAt-≥ sB1 w sB1≤w)
                                        ■ Fin.toℕ-↑ʳ sB1 (θB (Fin.reduce≥ w sB1≤w))
                                        ■ cong (sB1 +_) (θBℕ-hi (Fin.reduce≥ w sB1≤w) 2≤red
                                                         ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ w sB1≤w))
                                        ■ arB
                              where
                                sB1≤w : sB1 Nat.≤ Fin.toℕ w
                                sB1≤w = Nat.≤-trans (Nat.m≤m+n sB1 2) h
                                2≤red : 2 Nat.≤ Fin.toℕ (Fin.reduce≥ w sB1≤w)
                                2≤red = subst (2 Nat.≤_) (sym (toℕ-reduce≥ w sB1≤w))
                                          (subst (Nat._≤ Fin.toℕ w Nat.∸ sB1) (Nat.m+n∸m≡n sB1 2) (Nat.∸-monoˡ-≤ sB1 h))
                                arB : sB1 + ((sA2 + (sA1 + 2)) + (Fin.toℕ w Nat.∸ sB1)) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                                arB = solve₅ ■ cong ((sA2 + (sA1 + 2)) +_) (Nat.m+[n∸m]≡n sB1≤w)
                                  where open +-*-Solver
                                        solve₅ : sB1 + ((sA2 + (sA1 + 2)) + (Fin.toℕ w Nat.∸ sB1))
                                                 ≡ (sA2 + (sA1 + 2)) + (sB1 + (Fin.toℕ w Nat.∸ sB1))
                                        solve₅ = solve 4 (λ b₁ a₂ a₁ r → b₁ :+ ((a₂ :+ (a₁ :+ con 2)) :+ r)
                                                                      := (a₂ :+ (a₁ :+ con 2)) :+ (b₁ :+ r)) refl sB1 sA2 sA1 (Fin.toℕ w Nat.∸ sB1)
                            renIdB2 : (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)))
                                      ≗ (θB2 ↑* sB2)
                            renIdB2 w with Fin.toℕ w Nat.<? (sB2 + (sB1 + 2))
                            ... | yes w<wb = Fin.toℕ-injective
                                  ( cleanTℕ-mid sB1 sB2 sA1 sA2 Vw
                                      (subst (sA2 + (sA1 + 2) Nat.≤_) (sym vℕ) (Nat.m≤m+n (sA2 + (sA1 + 2)) (Fin.toℕ w)))
                                      (subst (Nat._< (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2))) (sym vℕ)
                                        (Nat.+-monoʳ-< (sA2 + (sA1 + 2)) w<wb))
                                  ■ cong (Nat._∸ (sA2 + (sA1 + 2))) vℕ ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (Fin.toℕ w)
                                  ■ sym shiftlo2 )
                              where
                                Vw = weaken* ⦃ Kᵣ ⦄ sA2 (weaken* ⦃ Kᵣ ⦄ sA1 (weaken* ⦃ Kᵣ ⦄ 2 w))
                                vℕ : Fin.toℕ Vw ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                                vℕ = toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 w))
                                   ■ solve 3 (λ a₂ a₁ x → a₂ :+ (a₁ :+ (con 2 :+ x)) := (a₂ :+ (a₁ :+ con 2)) :+ x) refl sA2 sA1 (Fin.toℕ w)
                                  where open +-*-Solver
                                shiftlo2 : Fin.toℕ ((θB2 ↑* sB2) w) ≡ Fin.toℕ w
                                shiftlo2 with Fin.toℕ w Nat.<? sB2
                                ... | yes w<b = ↑*-lo θB2 sB2 w w<b
                                ... | no w≥b = ↑*-hi θB2 sB2 w (Nat.≮⇒≥ w≥b)
                                             ■ cong (sB2 +_) (θB2ℕ-lo (Fin.reduce≥ w (Nat.≮⇒≥ w≥b))
                                                                (subst (Nat._< sB1 + 2) (sym (toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))) (sub-lt (Nat.≮⇒≥ w≥b) w<wb))
                                                              ■ toℕ-reduce≥ w (Nat.≮⇒≥ w≥b))
                                             ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ w≥b)
                            ... | no w≥wb = Fin.toℕ-injective
                                  ( cleanTℕ-ge sB1 sB2 sA1 sA2 Vw
                                      (subst ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤_) (sym vℕ)
                                        (Nat.+-monoʳ-≤ (sA2 + (sA1 + 2)) (Nat.≮⇒≥ w≥wb)))
                                  ■ vℕ
                                  ■ sym shifthi2 )
                              where
                                Vw = weaken* ⦃ Kᵣ ⦄ sA2 (weaken* ⦃ Kᵣ ⦄ sA1 (weaken* ⦃ Kᵣ ⦄ 2 w))
                                vℕ : Fin.toℕ Vw ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                                vℕ = toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 w))
                                   ■ solve 3 (λ a₂ a₁ x → a₂ :+ (a₁ :+ (con 2 :+ x)) := (a₂ :+ (a₁ :+ con 2)) :+ x) refl sA2 sA1 (Fin.toℕ w)
                                  where open +-*-Solver
                                sb2≤w : sB2 Nat.≤ Fin.toℕ w
                                sb2≤w = Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2)) (Nat.≮⇒≥ w≥wb)
                                shifthi2 : Fin.toℕ ((θB2 ↑* sB2) w) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                                shifthi2 = ↑*-hi θB2 sB2 w sb2≤w
                                         ■ cong (sB2 +_) (θB2ℕ-hi (Fin.reduce≥ w sb2≤w)
                                                            (subst (sB1 + 2 Nat.≤_) (sym (toℕ-reduce≥ w sb2≤w))
                                                              (subst (Nat._≤ Fin.toℕ w Nat.∸ sB2) (Nat.m+n∸m≡n sB2 (sB1 + 2)) (Nat.∸-monoˡ-≤ sB2 (Nat.≮⇒≥ w≥wb))))
                                                          ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ w sb2≤w))
                                         ■ arB2
                                  where
                                    open +-*-Solver
                                    arB2 : sB2 + ((sA2 + (sA1 + 2)) + (Fin.toℕ w Nat.∸ sB2)) ≡ (sA2 + (sA1 + 2)) + Fin.toℕ w
                                    arB2 = solve 4 (λ b₂ a₂ a₁ r → b₂ :+ ((a₂ :+ (a₁ :+ con 2)) :+ r) := (a₂ :+ (a₁ :+ con 2)) :+ (b₂ :+ r)) refl sB2 sA2 sA1 (Fin.toℕ w Nat.∸ sB2)
                                         ■ cong ((sA2 + (sA1 + 2)) +_) (Nat.m+[n∸m]≡n sb2≤w)
                    hB (inj₂ v) jv = subst motB jv
                      ( cong (_⋯ cT) redLσ
                      ■ wk6cT
                      ■ ⋯-cong Sv renIdσ
                      ■ sym wk6
                      ■ sym redRσ )
                      where
                        Sv = σ v
                        wk2′ : ∀ {X} → 𝔽 X → 𝔽 (2 + X)
                        wk2′ = weaken* ⦃ Kᵣ ⦄ 2
                        wkB1 : ∀ {X} → 𝔽 X → 𝔽 (sB1 + X)
                        wkB1 = weaken* ⦃ Kᵣ ⦄ sB1
                        wkB2 : ∀ {X} → 𝔽 X → 𝔽 (sB2 + X)
                        wkB2 = weaken* ⦃ Kᵣ ⦄ sB2
                        wkA1 : ∀ {X} → 𝔽 X → 𝔽 (sA1 + X)
                        wkA1 = weaken* ⦃ Kᵣ ⦄ sA1
                        wkA2 : ∀ {X} → 𝔽 X → 𝔽 (sA2 + X)
                        wkA2 = weaken* ⦃ Kᵣ ⦄ sA2
                        redLσ : AthL ((sum B₁ + sum B₂) ↑ʳ v)
                                ≡ Sv ⋯ wk2′ ⋯ wkB1 ⋯ wkB2 ⋯ wk2′ ⋯ wkA1 ⋯ wkA2
                        redLσ = cong (λ z → z ⋯ wk2′ ⋯ wkA1 ⋯ wkA2)
                                     (cong [ ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ wkB2)
                                              ++ₛ canonₛ B₂ (K `unit , wkB1 1F , K `unit))
                                           , (λ i → σ i ⋯ wk2′ ⋯ wkB1 ⋯ wkB2) ]′
                                           (Fin.splitAt-↑ʳ (sum B₁ + sum B₂) m v))
                        wk6cT : Sv ⋯ wk2′ ⋯ wkB1 ⋯ wkB2 ⋯ wk2′ ⋯ wkA1 ⋯ wkA2 ⋯ cT
                                ≡ Sv ⋯ (wk2′ ·ₖ (wkB1 ·ₖ (wkB2 ·ₖ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ cT))))))
                        wk6cT = fusion (Sv ⋯ wk2′ ⋯ wkB1 ⋯ wkB2 ⋯ wk2′ ⋯ wkA1) wkA2 cT
                              ■ fusion (Sv ⋯ wk2′ ⋯ wkB1 ⋯ wkB2 ⋯ wk2′) wkA1 (wkA2 ·ₖ cT)
                              ■ fusion (Sv ⋯ wk2′ ⋯ wkB1 ⋯ wkB2) wk2′ (wkA1 ·ₖ (wkA2 ·ₖ cT))
                              ■ fusion (Sv ⋯ wk2′ ⋯ wkB1) wkB2 (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ cT)))
                              ■ fusion (Sv ⋯ wk2′) wkB1 (wkB2 ·ₖ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ cT))))
                              ■ fusion Sv wk2′ (wkB1 ·ₖ (wkB2 ·ₖ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ cT)))))
                        wk6 : Sv ⋯ wk2′ ⋯ wkA1 ⋯ wkA2 ⋯ wk2′ ⋯ wkB1 ⋯ wkB2
                              ≡ Sv ⋯ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ (wk2′ ·ₖ (wkB1 ·ₖ wkB2)))))
                        wk6 = fusion (Sv ⋯ wk2′ ⋯ wkA1 ⋯ wkA2 ⋯ wk2′) wkB1 wkB2
                            ■ fusion (Sv ⋯ wk2′ ⋯ wkA1 ⋯ wkA2) wk2′ (wkB1 ·ₖ wkB2)
                            ■ fusion (Sv ⋯ wk2′ ⋯ wkA1) wkA2 (wk2′ ·ₖ (wkB1 ·ₖ wkB2))
                            ■ fusion (Sv ⋯ wk2′) wkA1 (wkA2 ·ₖ (wk2′ ·ₖ (wkB1 ·ₖ wkB2)))
                            ■ fusion Sv wk2′ (wkA1 ·ₖ (wkA2 ·ₖ (wk2′ ·ₖ (wkB1 ·ₖ wkB2))))
                        renIdσ : (wk2′ ·ₖ (wkB1 ·ₖ (wkB2 ·ₖ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ cT))))))
                                 ≗ (wk2′ ·ₖ (wkA1 ·ₖ (wkA2 ·ₖ (wk2′ ·ₖ (wkB1 ·ₖ wkB2)))))
                        renIdσ z = Fin.toℕ-injective (lσ ■ sym rσ)
                          where
                            lσ0 : Fin.toℕ (wkA2 (wkA1 (wk2′ (wkB2 (wkB1 (wk2′ z)))))) ≡ ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2))) + Fin.toℕ z
                            lσ0 = toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 _ ■ cong (2 +_)
                                    (toℕ-wk sB2 _ ■ cong (sB2 +_) (toℕ-wk sB1 _ ■ cong (sB1 +_) (toℕ-wk 2 z)))))
                                ■ solve 5 (λ a₂ a₁ b₂ b₁ x → a₂ :+ (a₁ :+ (con 2 :+ (b₂ :+ (b₁ :+ (con 2 :+ x)))))
                                                          := ((a₂ :+ (a₁ :+ con 2)) :+ (b₂ :+ (b₁ :+ con 2))) :+ x) refl sA2 sA1 sB2 sB1 (Fin.toℕ z)
                              where open +-*-Solver
                            geσ : (sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ (wkA2 (wkA1 (wk2′ (wkB2 (wkB1 (wk2′ z))))))
                            geσ = subst ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2)) Nat.≤_) (sym lσ0) (Nat.m≤m+n _ (Fin.toℕ z))
                            lσ : Fin.toℕ (cT (wkA2 (wkA1 (wk2′ (wkB2 (wkB1 (wk2′ z))))))) ≡ ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2))) + Fin.toℕ z
                            lσ = cleanTℕ-ge sB1 sB2 sA1 sA2 _ geσ ■ lσ0
                            rσ : Fin.toℕ (wkB2 (wkB1 (wk2′ (wkA2 (wkA1 (wk2′ z)))))) ≡ ((sA2 + (sA1 + 2)) + (sB2 + (sB1 + 2))) + Fin.toℕ z
                            rσ = toℕ-wk sB2 _ ■ cong (sB2 +_) (toℕ-wk sB1 _ ■ cong (sB1 +_) (toℕ-wk 2 _ ■ cong (2 +_)
                                   (toℕ-wk sA2 _ ■ cong (sA2 +_) (toℕ-wk sA1 _ ■ cong (sA1 +_) (toℕ-wk 2 z)))))
                               ■ solve 5 (λ a₂ a₁ b₂ b₁ x → b₂ :+ (b₁ :+ (con 2 :+ (a₂ :+ (a₁ :+ (con 2 :+ x)))))
                                                         := ((a₂ :+ (a₁ :+ con 2)) :+ (b₂ :+ (b₁ :+ con 2))) :+ x) refl sA2 sA1 sB2 sB1 (Fin.toℕ z)
                              where open +-*-Solver
                        redRσ : (BcanR ++ₛ Bthσ) ((sum B₁ + sum B₂) ↑ʳ v)
                                ≡ Sv ⋯ wk2′ ⋯ wkA1 ⋯ wkA2 ⋯ wk2′ ⋯ wkB1 ⋯ wkB2
                        redRσ = cong [ BcanR , Bthσ ]′ (Fin.splitAt-↑ʳ (sum B₁ + sum B₂) m v)
                              ■ cong (λ z → z ⋯ wk2′ ⋯ wkB1 ⋯ wkB2)
                                     (cong [ ((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ wkA2)
                                              ++ₛ canonₛ A₂ (K `unit , wkA1 1F , K `unit))
                                           , (λ i → σ i ⋯ wk2′ ⋯ wkA1 ⋯ wkA2) ]′
                                           (Fin.splitAt-↑ʳ (sum A₁ + sum A₂) m v))
