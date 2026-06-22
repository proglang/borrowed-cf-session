{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.Theorems.NuSwap where

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
open import BorrowedCF.Simulation.Theorems.Toolkit

U-ν-swap : (σ : m →ₛ n) {B₁ B₂ : 𝐓.BindGroup} {P : 𝐓.Proc (sum B₁ + sum B₂ + m)} →
           U[ 𝐓.ν B₁ B₂ P ] σ 𝐔.≋ U[ 𝐓.ν B₂ B₁ (P 𝐓.⋯ₚ swapᵣ (sum B₁) (sum B₂)) ] σ
U-ν-swap {m = m} {n = n} σ {B₁} {[]} {P} =
  Eq*.return 𝐔.ν-swap′
  ◅◅ 𝐔.ν-cong (≡→≋ (UB-nat B₁ (K `unit , 0F , K `unit) (swapᵣ 1 1) {f′ = f′} hyp ■ cong (λ cc → UB[ B₁ ] cc f′) ccEq))
  where
    e∅ : ∀ {N} → 0 →ₛ N
    e∅ = λ ()
    f′ : (sum B₁ →ₛ syncs B₁ + (1 + (1 + n))) → 𝐔.Proc (syncs B₁ + (1 + (1 + n)))
    f′ σ₂ = U[ P 𝐓.⋯ₚ swapᵣ (sum B₁) (sum []) ]
              (((λ i → e∅ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ++ₛ σ₂) ++ₛ
               (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)))
    ccEq : mapᶜ (swapᵣ 1 1) (K `unit , 0F , K `unit) ≡ (K `unit , idᵣ 1F , K `unit)
    ccEq = cong₂ _,_ refl (cong₂ _,_ refl refl)
    leafEq : ∀ τ →
      (((λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs [])) ++ₛ (λ ())) ++ₛ
       (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs [])))
      ·ₖ (swapᵣ 1 1 ↑* syncs B₁)
      ≗
      swapᵣ (sum B₁) (sum []) ·ₖ
      (((λ i → e∅ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ++ₛ (λ i → τ i ⋯ (swapᵣ 1 1 ↑* syncs B₁))) ++ₛ
       (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)))
    leafEq τ z = helperL (Fin.splitAt (sum B₁ + sum []) z)
      where
        helperL : (s : 𝔽 (sum B₁ + sum []) ⊎ 𝔽 _) →
          [ (λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs [])) ++ₛ (λ ()) ,
            (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs [])) ]′ s
            ⋯ (swapᵣ 1 1 ↑* syncs B₁)
          ≡
          [ (λ i → e∅ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ++ₛ (λ i → τ i ⋯ (swapᵣ 1 1 ↑* syncs B₁)) ,
            (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ]′
            (Fin.splitAt (sum B₁) (Fin.join _ _ (Sum.map₁ (Fin.swap (sum B₁)) s)))
        helperL (inj₁ w) = goalI (Fin.splitAt (sum B₁) w)
          where
            goalI : (s′ : 𝔽 (sum B₁) ⊎ 𝔽 (sum [])) →
              [ (λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs [])) , (λ ()) ]′ s′ ⋯ (swapᵣ 1 1 ↑* syncs B₁)
              ≡
              [ (λ i → e∅ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ++ₛ (λ i → τ i ⋯ (swapᵣ 1 1 ↑* syncs B₁)) ,
                (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) ]′
                (Fin.splitAt (sum B₁) (Fin.join (sum [] + sum B₁) m (inj₁ (Fin.join (sum []) (sum B₁) (Sum.swap s′)))))
            goalI (inj₁ w′) rewrite Fin.splitAt-↑ˡ (sum B₁) w′ m =
              cong (_⋯ swapᵣ 1 1 ↑* syncs B₁) (⋯-id (τ w′) (λ _ → refl))
            goalI (inj₂ ())
        helperL (inj₂ v) rewrite Fin.splitAt-↑ʳ (sum B₁) m v =
          cong (_⋯ swapᵣ 1 1 ↑* syncs B₁)
               (⋯-id (σ v ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) (λ _ → refl))
          ■ sym (⋯-↑*-wk (σ v ⋯ weaken* ⦃ Kᵣ ⦄ 2) (swapᵣ 1 1) (syncs B₁))
          ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁))
                 (fusion (σ v) (weaken* ⦃ Kᵣ ⦄ 2) (swapᵣ 1 1)
                  ■ ⋯-cong (σ v) (wk-swap 1 1)
                  ■ sym (⋯-id (σ v ⋯ weaken* ⦃ Kᵣ ⦄ 2) (λ _ → refl)))
    hyp : ∀ τ → _ 𝐔.⋯ₚ (swapᵣ 1 1 ↑* syncs B₁) ≡ f′ (λ i → τ i ⋯ (swapᵣ 1 1 ↑* syncs B₁))
    hyp τ = U-σ⋯ P ■ U-cong P (leafEq τ) ■ sym (U-⋯ₚ P)
U-ν-swap σ {[]} {x ∷ B₂} {P} =
  Eq*.symmetric _
    (subst (λ R → U[ 𝐓.ν (x ∷ B₂) [] (P 𝐓.⋯ₚ swapᵣ 0 (sum (x ∷ B₂))) ] σ 𝐔.≋ U[ 𝐓.ν [] (x ∷ B₂) R ] σ)
           pEq
           (U-ν-swap σ {x ∷ B₂} {[]} {P 𝐓.⋯ₚ swapᵣ 0 (sum (x ∷ B₂))}))
  where
    pEq : (P 𝐓.⋯ₚ swapᵣ 0 (sum (x ∷ B₂))) 𝐓.⋯ₚ swapᵣ (sum (x ∷ B₂)) 0 ≡ P
    pEq = 𝐓.fusionₚ P (swapᵣ 0 (sum (x ∷ B₂))) (swapᵣ (sum (x ∷ B₂)) 0)
        ■ 𝐓⋯ₚ-id P (swapᵣ-inv 0 (sum (x ∷ B₂)))
U-ν-swap {m = m} {n = n} σ {y ∷ B₁} {x ∷ B₂} {P} =
  Eq*.return 𝐔.ν-swap′
  ◅◅ 𝐔.ν-cong (≡→≋ (UB-nat (y ∷ B₁) (K `unit , 0F , K `unit) (swapᵣ 1 1) {f′ = g₁}
                       (λ τ₁ → UB-nat (x ∷ B₂) (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit)
                                      (swapᵣ 1 1 ↑* sB₁) {f′ = g₂ (λ i → τ₁ i ⋯ (swapᵣ 1 1 ↑* sB₁))}
                                 (λ τ₂ → U-σ⋯ P ■ U-cong P (dist τ₁ τ₂))))
              ◅◅ ( UB-flat (y ∷ B₁) ccL₁ g₁
                 ◅◅ φ^-cong sB₁ (UBflat-assoc (y ∷ B₁) ccL₁ g₁)
                 ◅◅ φ^-cong sB₁ (𝐔.∥-cong ε (UB-flat (x ∷ B₂) ccL₂ leafL))
                 ◅◅ φ^-cong sB₁ (φ-ext* sB₂ {Flags (y ∷ B₁)} {UBflat (x ∷ B₂) ccL₂ leafL})
                 ◅◅ φ^-cong sB₁ (φ^-cong sB₂ (𝐔.∥-cong ε (UBflat-assoc (x ∷ B₂) ccL₂ leafL)))
                 ◅◅ φ^-swap sB₁ sB₂ BodyL
                 ◅◅ φ^-cong sB₂ (φ^-cong sB₁ bodyMatch)
                 ◅◅ Eq*.symmetric _ rhsFlat))
  where
    sB₁ = syncs (y ∷ B₁)
    sB₂ = syncs (x ∷ B₂)
    Ξ₁ : (sB₁ + (2 + n)) →ᵣ (sB₁ + (2 + n))
    Ξ₁ = swapᵣ 1 1 ↑* sB₁
    Ξ₂ : (sB₂ + (sB₁ + (2 + n))) →ᵣ (sB₂ + (sB₁ + (2 + n)))
    Ξ₂ = Ξ₁ ↑* sB₂
    g₂ : (sum (y ∷ B₁) →ₛ sB₁ + (2 + n)) → (sum (x ∷ B₂) →ₛ sB₂ + (sB₁ + (2 + n))) → 𝐔.Proc (sB₂ + (sB₁ + (2 + n)))
    g₂ σ₁ σ₂ = U[ P ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ σ₂)
                      ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    g₁ : (sum (y ∷ B₁) →ₛ sB₁ + (2 + n)) → 𝐔.Proc (sB₁ + (2 + n))
    g₁ σ₁ = UB[ x ∷ B₂ ] (mapᶜ (swapᵣ 1 1 ↑* sB₁) (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit)) (g₂ σ₁)
    ccL₁ = mapᶜ (swapᵣ 1 1) (K `unit , 0F , K `unit)
    ccL₂ = mapᶜ (swapᵣ 1 1 ↑* sB₁) (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit)
    canon₁ = canonₛ (y ∷ B₁) ccL₁
    leafL = g₂ canon₁
    BodyL = (Flags (y ∷ B₁) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.∥ (Flags (x ∷ B₂) 𝐔.∥ leafL (canonₛ (x ∷ B₂) ccL₂))
    ccR₁ = (K `unit , 0F , K `unit)
    ccR₂ = (K `unit , weaken* ⦃ Kᵣ ⦄ sB₂ 1F , K `unit)
    gR₂ : (sum (x ∷ B₂) →ₛ sB₂ + (2 + n)) → (sum (y ∷ B₁) →ₛ sB₁ + (sB₂ + (2 + n))) → 𝐔.Proc (sB₁ + (sB₂ + (2 + n)))
    gR₂ σ₁ σ₂ = U[ P 𝐓.⋯ₚ swapᵣ (sum (y ∷ B₁)) (sum (x ∷ B₂)) ]
                  (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) ++ₛ σ₂)
                   ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ weaken* ⦃ Kᵣ ⦄ sB₁))
    gR₁ : (sum (x ∷ B₂) →ₛ sB₂ + (2 + n)) → 𝐔.Proc (sB₂ + (2 + n))
    gR₁ σ₁ = UB[ y ∷ B₁ ] ccR₂ (gR₂ σ₁)
    rhsFlat = UB-flat (x ∷ B₂) ccR₁ gR₁
            ◅◅ φ^-cong sB₂ (UBflat-assoc (x ∷ B₂) ccR₁ gR₁)
            ◅◅ φ^-cong sB₂ (𝐔.∥-cong ε (UB-flat (y ∷ B₁) ccR₂ (gR₂ (canonₛ (x ∷ B₂) ccR₁))))
            ◅◅ φ^-cong sB₂ (φ-ext* sB₁ {Flags (x ∷ B₂)} {UBflat (y ∷ B₁) ccR₂ (gR₂ (canonₛ (x ∷ B₂) ccR₁))})
            ◅◅ φ^-cong sB₂ (φ^-cong sB₁ (𝐔.∥-cong ε (UBflat-assoc (y ∷ B₁) ccR₂ (gR₂ (canonₛ (x ∷ B₂) ccR₁)))))
    bodyMatch = ≡→≋ (cong₂ 𝐔._∥_ compAeq (cong₂ 𝐔._∥_ compBeq compCeq))
              ◅◅ 𝐔.∥-assoc ◅◅ 𝐔.∥-cong 𝐔.∥-comm ε ◅◅ Eq*.symmetric _ 𝐔.∥-assoc
      where
        compAeq : (Flags (y ∷ B₁) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.⋯ₚ assocSwapᵣ sB₂ sB₁ ≡ Flags (y ∷ B₁)
        compAeq = 𝐔.fusionₚ (Flags (y ∷ B₁)) (weaken* ⦃ Kᵣ ⦄ sB₂) (assocSwapᵣ sB₂ sB₁)
                ■ Flags-⋯-cong (y ∷ B₁) (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ assocSwapᵣ sB₂ sB₁) idₖ hypA
                ■ ⋯ₚ-id (Flags (y ∷ B₁)) (λ _ → refl)
          where
            hypA : ∀ (i : 𝔽 (syncs (y ∷ B₁))) →
                   (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ assocSwapᵣ sB₂ sB₁) (i ↑ˡ (2 + n)) ≡ idₖ (i ↑ˡ (sB₂ + (2 + n)))
            hypA i = Fin.toℕ-injective
              ( toℕ-assoc-mid sB₂ sB₁ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) ge lt
              ■ cong (Nat._∸ sB₂) toℕx ■ Nat.m+n∸m≡n sB₂ (Fin.toℕ i)
              ■ sym (Fin.toℕ-↑ˡ i (sB₂ + (2 + n))) )
              where
                toℕx : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) ≡ sB₂ + Fin.toℕ i
                toℕx = cong Fin.toℕ (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))
                     ■ Fin.toℕ-↑ʳ sB₂ (i ↑ˡ (2 + n)) ■ cong (sB₂ +_) (Fin.toℕ-↑ˡ i (2 + n))
                ge = subst (sB₂ Nat.≤_) (sym toℕx) (Nat.m≤m+n sB₂ (Fin.toℕ i))
                lt = subst (Nat._< sB₂ + sB₁) (sym toℕx) (Nat.+-monoʳ-< sB₂ (Fin.toℕ<n i))
        compBeq : Flags (x ∷ B₂) 𝐔.⋯ₚ assocSwapᵣ sB₂ sB₁ ≡ Flags (x ∷ B₂) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₁
        compBeq = Flags-⋯-cong (x ∷ B₂) (assocSwapᵣ sB₂ sB₁) (weaken* ⦃ Kᵣ ⦄ sB₁) hypB
          where
            hypB : ∀ (i : 𝔽 (syncs (x ∷ B₂))) →
                   assocSwapᵣ sB₂ sB₁ (i ↑ˡ (sB₁ + (2 + n))) ≡ weaken* ⦃ Kᵣ ⦄ sB₁ (i ↑ˡ (2 + n))
            hypB i = Fin.toℕ-injective
              ( toℕ-assoc-lt sB₂ sB₁ (i ↑ˡ (sB₁ + (2 + n)))
                  (subst (Nat._< sB₂) (sym (Fin.toℕ-↑ˡ i (sB₁ + (2 + n)))) (Fin.toℕ<n i))
              ■ cong (sB₁ +_) (Fin.toℕ-↑ˡ i (sB₁ + (2 + n)))
              ■ sym ( cong Fin.toℕ (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB₁ (i ↑ˡ (2 + n)))
                    ■ Fin.toℕ-↑ʳ sB₁ (i ↑ˡ (2 + n)) ■ cong (sB₁ +_) (Fin.toℕ-↑ˡ i (2 + n))) )
        compCeq : leafL (canonₛ (x ∷ B₂) ccL₂) 𝐔.⋯ₚ assocSwapᵣ sB₂ sB₁
                  ≡ gR₂ (canonₛ (x ∷ B₂) ccR₁) (canonₛ (y ∷ B₁) ccR₂)
        compCeq = U-σ⋯ P
                ■ U-cong P subEq
                ■ sym (U-⋯ₚ P)
          where
            subEq : (((λ i → canon₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ canonₛ (x ∷ B₂) ccL₂)
                     ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
                    ·ₖ assocSwapᵣ sB₂ sB₁
                    ≗ swapᵣ (sum (y ∷ B₁)) (sum (x ∷ B₂))
                    ·ₖ (((λ i → canonₛ (x ∷ B₂) ccR₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) ++ₛ canonₛ (y ∷ B₁) ccR₂)
                        ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ weaken* ⦃ Kᵣ ⦄ sB₁))
            subEq j =
                ++ₛ-⋯ ((λ i → canon₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ canonₛ (x ∷ B₂) ccL₂)
                      (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                      (assocSwapᵣ sB₂ sB₁) j
              ■ ++ₛ-cong₂
                  (λ i → ++ₛ-⋯ (λ i → canon₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (canonₛ (x ∷ B₂) ccL₂)
                               (assocSwapᵣ sB₂ sB₁) i
                       ■ ++ₛ-cong₂ case1 case2 i)
                  case3 j
              ■ sym (swap-++ₛ (sum (y ∷ B₁)) (sum (x ∷ B₂))
                       (λ i → canonₛ (x ∷ B₂) ccR₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₁)
                       (canonₛ (y ∷ B₁) ccR₂)
                       (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) j)
              where
                ccR₂eq : ccR₂ ≡ mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) ccL₁
                ccR₂eq = refl
                ccL₂eq : ccL₂ ≡ mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₁) ccR₁
                ccL₂eq = cong (λ z → K `unit , z , K `unit) midEq
                  where
                    midEq : (swapᵣ 1 1 ↑* sB₁) (weaken* ⦃ Kᵣ ⦄ sB₁ 1F) ≡ weaken* ⦃ Kᵣ ⦄ sB₁ 0F
                    midEq = Fin.toℕ-injective (rhsM ■ sym lhsM)
                      where
                        lhsM : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₁ 0F) ≡ sB₁
                        lhsM = toℕ-wk sB₁ 0F ■ Nat.+-identityʳ sB₁
                        rhsM : Fin.toℕ ((swapᵣ 1 1 ↑* sB₁) (weaken* ⦃ Kᵣ ⦄ sB₁ 1F)) ≡ sB₁
                        rhsM = toℕ-↑* (swapᵣ 1 1) sB₁ (weaken* ⦃ Kᵣ ⦄ sB₁ 1F)
                             ■ cong [ Fin.toℕ , (λ q → sB₁ + Fin.toℕ (swapᵣ 1 1 q)) ]′
                                    (cong (Fin.splitAt sB₁) (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB₁ 1F) ■ Fin.splitAt-↑ʳ sB₁ _ 1F)
                             ■ Nat.+-identityʳ sB₁
                case1 : (k : 𝔽 (sum (y ∷ B₁))) →
                        (canon₁ k ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ assocSwapᵣ sB₂ sB₁ ≡ canonₛ (y ∷ B₁) ccR₂ k
                case1 k = fusion (canon₁ k) (weaken* ⦃ Kᵣ ⦄ sB₂) (assocSwapᵣ sB₂ sB₁)
                        ■ ⋯-cong (canon₁ k) (renId1 sB₂ sB₁)
                        ■ sym (canonₛ-nat (y ∷ B₁) ccL₁ (weaken* ⦃ Kᵣ ⦄ sB₂) k)
                        ■ sym (cong (λ cc → canonₛ (y ∷ B₁) cc k) ccR₂eq)
                case2 : (k : 𝔽 (sum (x ∷ B₂))) →
                        canonₛ (x ∷ B₂) ccL₂ k ⋯ assocSwapᵣ sB₂ sB₁
                        ≡ canonₛ (x ∷ B₂) ccR₁ k ⋯ weaken* ⦃ Kᵣ ⦄ sB₁
                case2 k = cong (_⋯ assocSwapᵣ sB₂ sB₁)
                               (cong (λ cc → canonₛ (x ∷ B₂) cc k) ccL₂eq
                                ■ canonₛ-nat (x ∷ B₂) ccR₁ (weaken* ⦃ Kᵣ ⦄ sB₁) k)
                        ■ fusion (canonₛ (x ∷ B₂) ccR₁ k) (weaken* ⦃ Kᵣ ⦄ sB₁ ↑* sB₂) (assocSwapᵣ sB₂ sB₁)
                        ■ ⋯-cong (canonₛ (x ∷ B₂) ccR₁ k) (renId2 sB₂ sB₁)
                case3 : (k : 𝔽 _) →
                        (σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ assocSwapᵣ sB₂ sB₁
                        ≡ σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ weaken* ⦃ Kᵣ ⦄ sB₁
                case3 k = cong (_⋯ assocSwapᵣ sB₂ sB₁)
                               (fusion (σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB₁) (weaken* ⦃ Kᵣ ⦄ sB₂))
                        ■ fusion (σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB₁ ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) (assocSwapᵣ sB₂ sB₁)
                        ■ ⋯-cong (σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2) (renId3 sB₂ sB₁)
                        ■ sym (fusion (σ k ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB₂) (weaken* ⦃ Kᵣ ⦄ sB₁))
    dist : ∀ (τ₁ : sum (y ∷ B₁) →ₛ sB₁ + (2 + n)) (τ₂ : sum (x ∷ B₂) →ₛ sB₂ + (sB₁ + (2 + n))) →
           (((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
             ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)) ·ₖ Ξ₂
           ≗ ((λ i → (τ₁ i ⋯ Ξ₁) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂))
             ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    dist τ₁ τ₂ j =
        ++ₛ-⋯ ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
              (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) Ξ₂ j
      ■ [,]-cong compA compB (Fin.splitAt (sum (y ∷ B₁) + sum (x ∷ B₂)) j)
      where
        compA : ∀ i → ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂) i ⋯ Ξ₂
                      ≡ ((λ i → (τ₁ i ⋯ Ξ₁) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂)) i
        compA i = ++ₛ-⋯ (λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) τ₂ Ξ₂ i
                ■ [,]-cong (λ j → sym (⋯-↑*-wk (τ₁ j) Ξ₁ sB₂)) (λ j → refl) (Fin.splitAt (sum (y ∷ B₁)) i)
        compB : ∀ i → (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ Ξ₂
                      ≡ σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        compB i = sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) Ξ₁ sB₂)
                ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (swapᵣ 1 1) sB₁))
                ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                       (fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (swapᵣ 1 1) ■ ⋯-cong (σ i) (wk-swap 1 1))

-- ν-block commutation engine (the U-ν-comm analogue of BlockPermutation's φ-suite):
-- bubble a ν binder up past a block of φ binders.

φ-ν-comm : ∀ {m} (P : 𝐔.Proc (2 + (1 + m))) →
           𝐔.φ (𝐔.ν P) 𝐔.≋ 𝐔.ν (𝐔.φ (P 𝐔.⋯ₚ assocSwapᵣ 2 1 {m}))
φ-ν-comm {m} P =
     ≡→≋ (cong (λ z → 𝐔.φ (𝐔.ν z))
                (sym (𝐔.fusionₚ P (assocSwapᵣ 2 1) (assocSwapᵣ 1 2)
                      ■ ⋯ₚ-id P (assocSwap-inv 2 1))))
  ◅◅ Eq*.symmetric _ (Eq*.return 𝐔.νφ-comm′)

φ^-ν-comm : ∀ k {m} (P : 𝐔.Proc (2 + (k + m))) →
            φ^ k (𝐔.ν P) 𝐔.≋ 𝐔.ν (φ^ k (P 𝐔.⋯ₚ assocSwapᵣ 2 k {m}))
φ^-ν-comm zero    P = ≡→≋ (cong 𝐔.ν (sym (⋯ₚ-id P (R-base-b0 2))))
φ^-ν-comm (suc k) P =
     φ^-cong k (φ-ν-comm P)
  ◅◅ φ^-ν-comm k (𝐔.φ (P 𝐔.⋯ₚ assocSwapᵣ 2 1))
  ◅◅ ≡→≋ (cong 𝐔.ν (cong (φ^ k)
       (cong 𝐔.φ (𝐔.fusionₚ P (assocSwapᵣ 2 1) (assocSwapᵣ 2 k ↑)
                  ■ 𝐔.⋯ₚ-cong P (R2' 2 k)))))

-- Reverse direction: push a φ-block out past a ν (pull a ν in under φ's).
ν-φ^-comm : ∀ k {m} (Q : 𝐔.Proc (k + (2 + m))) →
            𝐔.ν (φ^ k Q) 𝐔.≋ φ^ k (𝐔.ν (Q 𝐔.⋯ₚ assocSwapᵣ k 2 {m}))
ν-φ^-comm k {m} Q =
     ≡→≋ (cong 𝐔.ν (cong (φ^ k)
            (sym (𝐔.fusionₚ Q (assocSwapᵣ k 2) (assocSwapᵣ 2 k)
                  ■ ⋯ₚ-id Q (assocSwap-inv k 2)))))
  ◅◅ Eq*.symmetric _ (φ^-ν-comm k (Q 𝐔.⋯ₚ assocSwapᵣ k 2))

-- Renaming distributes through a φ^ block (exposes binder structure between engine steps).
φ^-⋯ₚ : ∀ k {a b} (Z : 𝐔.Proc (k + a)) (ρ : a →ᵣ b) →
        φ^ k Z 𝐔.⋯ₚ ρ ≡ φ^ k (Z 𝐔.⋯ₚ (ρ ↑* k))
φ^-⋯ₚ zero    Z ρ = refl
φ^-⋯ₚ (suc k) Z ρ = φ^-⋯ₚ k (𝐔.φ Z) ρ

-- Push a parallel component R into a ν(φ^ a (φ^ b ·)) block (weakening it past the binders).
νφφ-ext : ∀ a b {m} (Rp : 𝐔.Proc m) (Yp : 𝐔.Proc (b + (a + (2 + m)))) →
  Rp 𝐔.∥ 𝐔.ν (φ^ a (φ^ b Yp)) 𝐔.≋
  𝐔.ν (φ^ a (φ^ b ((Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ a 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ b) 𝐔.∥ Yp)))
νφφ-ext a b Rp Yp =
     Eq*.return 𝐔.ν-ext′
  ◅◅ 𝐔.ν-cong (φ-ext* a {Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2} {φ^ b Yp})
  ◅◅ 𝐔.ν-cong (φ^-cong a (φ-ext* b {Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ a} {Yp}))

-- Flatten one whole ν-block of the translation into ν (φ^ (φ^ (Flags ∥ Flags ∥ leaf))).
-- The leaf substitution is the canonical one (canonₛ on each half, σ weakened past everything).

Uν-flat : ∀ {k N} (τ : k →ₛ N) (C₁ C₂ : 𝐓.BindGroup) (Q : 𝐓.Proc (sum C₁ + sum C₂ + k)) →
  U[ 𝐓.ν C₁ C₂ Q ] τ 𝐔.≋
  𝐔.ν (φ^ (syncs C₁) (φ^ (syncs C₂)
    ( (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs C₂))
    𝐔.∥ (Flags C₂
        𝐔.∥ U[ Q ] (((λ i → canonₛ C₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)) ++ₛ
                      canonₛ C₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs C₁) 1F , K `unit))
                     ++ₛ (λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)))))))
Uν-flat {k} {N} τ C₁ C₂ Q =
  𝐔.ν-cong
    ( UB-flat C₁ cc1 g
    ◅◅ φ^-cong (syncs C₁) (UBflat-assoc C₁ cc1 g)
    ◅◅ φ^-cong (syncs C₁) (𝐔.∥-cong ε (UB-flat C₂ cc2 leaf))
    ◅◅ φ^-cong (syncs C₁) (φ-ext* (syncs C₂) {Flags C₁} {UBflat C₂ cc2 leaf})
    ◅◅ φ^-cong (syncs C₁) (φ^-cong (syncs C₂) (𝐔.∥-cong ε (UBflat-assoc C₂ cc2 leaf))) )
  where
    cc1 = (K `unit , 0F , K `unit)
    cc2 = (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs C₁) 1F , K `unit)
    leaf : (sum C₂ →ₛ syncs C₂ + (syncs C₁ + (2 + N))) → 𝐔.Proc (syncs C₂ + (syncs C₁ + (2 + N)))
    leaf σ₂ = U[ Q ] (((λ i → canonₛ C₁ cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)) ++ₛ σ₂)
                     ++ₛ (λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)))
    g : (sum C₁ →ₛ syncs C₁ + (2 + N)) → 𝐔.Proc (syncs C₁ + (2 + N))
    g σ₁ = UB[ C₂ ] cc2 (λ σ₂ → U[ Q ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)) ++ₛ σ₂)
                     ++ₛ (λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂))))

-- The clean block-transpose renaming telescope-transpose realises: a cast-wrapped
-- assocSwapᵣ swapping the whole A-telescope-block (width sA₂+sA₁+2) past the
-- B-telescope-block (width sB₂+sB₁+2), keeping the trailing scope.
