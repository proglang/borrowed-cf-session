module BorrowedCF.Simulation.NuExtrusion where

-- | Translation of ν scope-extrusion: U[_] commutes with pushing a parallel
--   component underneath a ν binder-group.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.TranslationProperties

Ub-distrib : (b : ℕ) (cc : UChan m) (Rp : 𝐔.Proc m) (g : (b →ₛ m) → 𝐔.Proc m) →
             Rp 𝐔.∥ Ub[ b ] cc g ≡ Ub[ b ] cc (λ σh → Rp 𝐔.∥ g σh)
Ub-distrib zero cc Rp g = refl
Ub-distrib (suc zero) (e₁ , x , e₂) Rp g = refl
Ub-distrib (suc (suc b)) (e₁ , x , e₂) Rp g =
  Ub-distrib (suc b) (K `unit , x , e₂) Rp (λ σ → g (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ))

-- Scope-coercion distributes over parallel composition.

weakenComp : ∀ {nn} k (Rp : 𝐔.Proc nn) →
             (Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ k
             ≡ subst 𝐔.Proc (sym (+-suc k nn)) (Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc k))
weakenComp {nn} k Rp =
    𝐔.fusionₚ Rp (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ k)
  ■ 𝐔.⋯ₚ-cong Rp wkrenEq
  ■ subst-⋯ₚ-cod (sym (+-suc k nn)) Rp (weaken* ⦃ Kᵣ ⦄ (suc k))
  where
    wkrenEq : weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ k
              ≗ subst (λ z → nn →ᵣ z) (sym (+-suc k nn)) (weaken* ⦃ Kᵣ ⦄ (suc k))
    wkrenEq x =
        cong (weaken* ⦃ Kᵣ ⦄ k) (weaken*~↑ʳ ⦃ Kᵣ ⦄ 1 x)
      ■ weaken*~↑ʳ ⦃ Kᵣ ⦄ k (suc x)
      ■ subst-flip (+-suc k nn) (↑ʳ-suc k x)
      ■ cong (subst 𝔽 (sym (+-suc k nn))) (sym (weaken*~↑ʳ ⦃ Kᵣ ⦄ (suc k) x))
      ■ sym (subst-ren-cod (sym (+-suc k nn)) (weaken* ⦃ Kᵣ ⦄ (suc k)) x)

-- Pushing a left parallel component into the φ-nest (weakening it appropriately).

UB-ext : (B : 𝐓.BindGroup) (cc : UChan n) (Rp : 𝐔.Proc n)
         (f : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) →
         (Rp 𝐔.∥ UB[ B ] cc f) 𝐔.≋ UB[ B ] cc (λ τ → (Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B)) 𝐔.∥ f τ)
UB-ext [] cc Rp f = ≡→≋ (cong (𝐔._∥ f (λ ())) (sym (⋯ₚ-id Rp (λ _ → refl))))
UB-ext (c ∷ []) cc Rp f =
  ≡→≋ (Ub-distrib c cc Rp (λ σh → f (σh ++ₛ λ ()))
       ■ Ub-cong-≡ c cc (λ σh → cong (𝐔._∥ f (σh ++ₛ λ ())) (sym (⋯ₚ-id Rp (λ _ → refl)))))
UB-ext (c ∷ B@(_ ∷ _)) (e₁ , x , e₂) Rp f =
  Eq*.return 𝐔.φ-ext′
  ◅◅ 𝐔.φ-cong
       ( ∥-swap-mid
       ◅◅ 𝐔.∥-cong ε (UB-ext B cc' (Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) g)
       ◅◅ ≡→≋ (cong ((0F 𝐔.↦ ϕ[ c ]) 𝐔.∥_) (UB-cong-≡ B cc' perτ)) )
  where
    sB = syncs B
    cc' : UChan (suc _)
    cc' = (` 0F , suc x , e₂ ⋯ weakenᵣ)
    cc'' : UChan (sB + suc _)
    cc'' = (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` weaken* ⦃ Kᵣ ⦄ sB 0F))
    g : (sum B →ₛ sB + suc _) → 𝐔.Proc (sB + suc _)
    g σt = Ub[ c ] cc'' (λ σh → subst 𝐔.Proc (sym (+-suc sB _)) (f (subst (sum (c ∷ B) →ₛ_) (+-suc sB _) (σh ++ₛ σt))))
    ∥-swap-mid : ∀ {A B C : 𝐔.Proc n} → (A 𝐔.∥ (B 𝐔.∥ C)) 𝐔.≋ (B 𝐔.∥ (A 𝐔.∥ C))
    ∥-swap-mid = 𝐔.∥-assoc ◅◅ 𝐔.∥-cong 𝐔.∥-comm ε ◅◅ Eq*.symmetric _ 𝐔.∥-assoc
    perτ : ∀ σt → ((Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) 𝐔.∥ g σt
                  ≡ Ub[ c ] cc'' (λ σh → subst 𝐔.Proc (sym (+-suc sB _))
                                            ((Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc sB)) 𝐔.∥
                                             f (subst (sum (c ∷ B) →ₛ_) (+-suc sB _) (σh ++ₛ σt))))
    perτ σt =
        Ub-distrib c cc'' ((Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB)
          (λ σh → subst 𝐔.Proc (sym (+-suc sB _)) (f (subst (sum (c ∷ B) →ₛ_) (+-suc sB _) (σh ++ₛ σt))))
      ■ Ub-cong-≡ c cc'' (λ σh →
            cong (𝐔._∥ subst 𝐔.Proc (sym (+-suc sB _)) (f (subst (sum (c ∷ B) →ₛ_) (+-suc sB _) (σh ++ₛ σt))))
                 (weakenComp sB Rp)
          ■ sym (subst-∥ (sym (+-suc sB _)) (Rp 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc sB))
                         (f (subst (sum (c ∷ B) →ₛ_) (+-suc sB _) (σh ++ₛ σt)))))

-- ν-extrusion for the translation: push the parallel component through the binder + φ-nest.

U-ν-ext : (σ : m →ₛ n) (P : 𝐓.Proc m) (B₁ B₂ : 𝐓.BindGroup)
          (Q : 𝐓.Proc (sum B₁ + sum B₂ + m)) →
          U[ P 𝐓.∥ 𝐓.ν B₁ B₂ Q ] σ 𝐔.≋
          U[ 𝐓.ν B₁ B₂ ((P 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) 𝐓.∥ Q) ] σ
U-ν-ext {m = m} {n = n} σ P B₁ B₂ Q =
  Eq*.return 𝐔.ν-ext′
  ◅◅ 𝐔.ν-cong
       ( UB-ext B₁ (K `unit , 0F , K `unit) (U[ P ] σ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) _
       ◅◅ UB-cong B₁ _ (λ τ₁ →
            UB-ext B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
              ((U[ P ] σ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) _)
       ◅◅ UB-cong B₁ _ (λ τ₁ → UB-cong B₂ _ (λ τ₂ →
            ≡→≋ (cong (𝐔._∥ U[ Q ] (σ′ τ₁ τ₂)) (step4eq τ₁ τ₂)))) )
  where
    wkK = weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)
    Bσ : m →ₛ syncs B₂ + (syncs B₁ + (2 + n))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
    σ′ : (sum B₁ →ₛ syncs B₁ + (2 + n)) → (sum B₂ →ₛ syncs B₂ + (syncs B₁ + (2 + n))) →
         (sum B₁ + sum B₂ + m →ₛ syncs B₂ + (syncs B₁ + (2 + n)))
    σ′ τ₁ τ₂ = ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂) ++ₛ Bσ
    wkσ′≗Bσ : ∀ τ₁ τ₂ → wkK ·ₖ σ′ τ₁ τ₂ ≗ Bσ
    wkσ′≗Bσ τ₁ τ₂ i =
        cong (σ′ τ₁ τ₂) (weaken*~↑ʳ ⦃ Kᵣ ⦄ (sum B₁ + sum B₂) i)
      ■ cong [ _ , _ ]′ (splitAt-↑ʳ (sum B₁ + sum B₂) _ i)
    step4eq : ∀ τ₁ τ₂ →
              ((U[ P ] σ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁))
                𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
              ≡ U[ P 𝐓.⋯ₚ wkK ] (σ′ τ₁ τ₂)
    step4eq τ₁ τ₂ =
        ( cong (λ z → z 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (U-σ⋯ P)
        ■ cong (λ z → z 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (U-σ⋯ P)
        ■ U-σ⋯ P )
      ■ sym (U-⋯ₚ P ■ U-cong P (wkσ′≗Bσ τ₁ τ₂))

-- subst commutes through a φ binder.
