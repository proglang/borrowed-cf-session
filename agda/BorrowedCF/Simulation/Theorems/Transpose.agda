module BorrowedCF.Simulation.Theorems.Transpose where

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
open import BorrowedCF.Simulation.Theorems.NuSwap
open import BorrowedCF.Simulation.Theorems.CleanT

telescope-transpose : ∀ sB₁ sB₂ sA₁ sA₂ {nn}
  (X : 𝐔.Proc (sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))))) →
  𝐔.ν (φ^ sB₁ (φ^ sB₂ (𝐔.ν (φ^ sA₁ (φ^ sA₂ X))))) 𝐔.≋
  𝐔.ν (φ^ sA₁ (φ^ sA₂ (𝐔.ν (φ^ sB₁ (φ^ sB₂ (X 𝐔.⋯ₚ cleanT-comm sB₁ sB₂ sA₁ sA₂))))))
telescope-transpose sB₁ sB₂ sA₁ sA₂ X =
     𝐔.ν-cong (φ^-cong sB₁ (φ^-ν-comm sB₂ _))
  ◅◅ 𝐔.ν-cong (φ^-ν-comm sB₁ _)
  ◅◅ Eq*.return 𝐔.ν-comm′
  ◅◅ ≡→≋ (cong 𝐔.ν (cong 𝐔.ν consolidate))
  ◅◅ 𝐔.ν-cong (𝐔.ν-cong (φ^-cong sB₁ (φ^-swap sB₂ sA₁ _)))
  ◅◅ 𝐔.ν-cong (𝐔.ν-cong (φ^-swap sB₁ sA₁ _))
  ◅◅ 𝐔.ν-cong (ν-φ^-comm sA₁ _)
  ◅◅ ≡→≋ (cong 𝐔.ν (cong (φ^ sA₁) (cong 𝐔.ν consolidate-2)))
  ◅◅ 𝐔.ν-cong (φ^-cong sA₁ (𝐔.ν-cong (φ^-cong sB₁ (φ^-swap sB₂ sA₂ _))))
  ◅◅ 𝐔.ν-cong (φ^-cong sA₁ (𝐔.ν-cong (φ^-swap sB₁ sA₂ _)))
  ◅◅ 𝐔.ν-cong (φ^-cong sA₁ (ν-φ^-comm sA₂ _))
  ◅◅ ≡→≋ (cong (λ z → 𝐔.ν (φ^ sA₁ (φ^ sA₂ (𝐔.ν z)))) consolidate-3)
  ◅◅ ≡→≋ (cong (λ z → 𝐔.ν (φ^ sA₁ (φ^ sA₂ (𝐔.ν (φ^ sB₁ (φ^ sB₂ z))))))
       ( 𝐔.fusionₚ (X 𝐔.⋯ₚ r1 𝐔.⋯ₚ r2) r3 r4′
       ■ 𝐔.fusionₚ (X 𝐔.⋯ₚ r1) r2 (r3 ·ₖ r4′)
       ■ 𝐔.fusionₚ X r1 (r2 ·ₖ (r3 ·ₖ r4′)) ))
  ◅◅ ≡→≋ (cong (λ z → 𝐔.ν (φ^ sA₁ (φ^ sA₂ (𝐔.ν (φ^ sB₁ (φ^ sB₂ z))))))
             (𝐔.⋯ₚ-cong X transpEq))
  where
    r1 = (assocSwapᵣ 2 sB₂ ·ₖ (assocSwapᵣ 2 sB₁ ·ₖ assocSwapᵣ 2 2 ↑* sB₁) ↑* sB₂) ↑* sA₁ ↑* sA₂
    r2 = (assocSwapᵣ sA₁ sB₂ ·ₖ (assocSwapᵣ sA₁ sB₁ ·ₖ assocSwapᵣ sA₁ 2 ↑* sB₁) ↑* sB₂) ↑* sA₂
    r3 = assocSwapᵣ sA₂ sB₂
    r4′ = (assocSwapᵣ sA₂ sB₁ ·ₖ (assocSwapᵣ sA₂ 2 ↑* sB₁)) ↑* sB₂
    transpEq : (r1 ·ₖ (r2 ·ₖ (r3 ·ₖ r4′))) ≗ cleanT-comm sB₁ sB₂ sA₁ sA₂
    transpEq x = Fin.toℕ-injective dispatch
      where
        WA = sA₂ + (sA₁ + 2)
        WB = sB₂ + (sB₁ + 2)
        cD = castDom-comm sB₁ sB₂ sA₁ sA₂
        cC = castCod-comm sB₁ sB₂ sA₁ sA₂
        -- clean (RHS) characterisation: cleanT is the block transpose assocSwapᵣ WA WB.
        clean-lt : Fin.toℕ x Nat.< WA → Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ x) ≡ WB + Fin.toℕ x
        clean-lt lt =
            Fin.toℕ-cast cC _
          ■ toℕ-assoc-lt WA WB (Fin.cast cD x) (subst (Nat._< WA) (sym (Fin.toℕ-cast cD x)) lt)
          ■ cong (WB +_) (Fin.toℕ-cast cD x)
        clean-mid : WA Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< WA + WB →
                    Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ x) ≡ Fin.toℕ x Nat.∸ WA
        clean-mid ge lt =
            Fin.toℕ-cast cC _
          ■ toℕ-assoc-mid WA WB (Fin.cast cD x)
              (subst (WA Nat.≤_) (sym (Fin.toℕ-cast cD x)) ge)
              (subst (Nat._< WA + WB) (sym (Fin.toℕ-cast cD x)) lt)
          ■ cong (Nat._∸ WA) (Fin.toℕ-cast cD x)
        clean-ge : WA + WB Nat.≤ Fin.toℕ x → Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ x) ≡ Fin.toℕ x
        clean-ge ge =
            Fin.toℕ-cast cC _
          ■ toℕ-assoc-ge WA WB (Fin.cast cD x) (subst (WA + WB Nat.≤_) (sym (Fin.toℕ-cast cD x)) ge)
          ■ Fin.toℕ-cast cD x
        mover : ∀ p q v → p Nat.≤ v → p + (q + (v Nat.∸ p)) ≡ q + v
        mover p q v ple =
            sym (Nat.+-assoc p q (v Nat.∸ p))
          ■ cong (Nat._+ (v Nat.∸ p)) (Nat.+-comm p q)
          ■ Nat.+-assoc q p (v Nat.∸ p)
          ■ cong (q +_) (Nat.m+[n∸m]≡n ple)
        -- Block A₂ (toℕ x < sA₂): r1,r2 fix it; r3 sends sA₂↦sB₂; r4′ moves it up by sB₁+2.
        lhsA2 : Fin.toℕ x Nat.< sA₂ → Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ WB + Fin.toℕ x
        lhsA2 lt =
            ↑*-hi _ sB₂ (r3 (r2 (r1 x))) hge
          ■ cong (sB₂ +_) innerChain
          ■ sym (Nat.+-assoc sB₂ (sB₁ + 2) kx ■ cong (sB₂ +_) (Nat.+-assoc sB₁ 2 kx))
          where
            kx = Fin.toℕ x
            e1 : Fin.toℕ (r1 x) ≡ kx
            e1 = ↑*-lo _ sA₂ x lt
            e2 : Fin.toℕ (r2 (r1 x)) ≡ kx
            e2 = ↑*-lo _ sA₂ (r1 x) (subst (Nat._< sA₂) (sym e1) lt) ■ e1
            e3 : Fin.toℕ (r3 (r2 (r1 x))) ≡ sB₂ + kx
            e3 = toℕ-assoc-lt sA₂ sB₂ (r2 (r1 x)) (subst (Nat._< sA₂) (sym e2) lt) ■ cong (sB₂ +_) e2
            hge : sB₂ Nat.≤ Fin.toℕ (r3 (r2 (r1 x)))
            hge = subst (sB₂ Nat.≤_) (sym e3) (Nat.m≤m+n sB₂ kx)
            red = Fin.reduce≥ (r3 (r2 (r1 x))) hge
            redℕ : Fin.toℕ red ≡ kx
            redℕ = toℕ-reduce≥ (r3 (r2 (r1 x))) hge ■ cong (Nat._∸ sB₂) e3 ■ Nat.m+n∸m≡n sB₂ kx
            s1 = assocSwapᵣ sA₂ sB₁ red
            f1 : Fin.toℕ s1 ≡ sB₁ + kx
            f1 = toℕ-assoc-lt sA₂ sB₁ red (subst (Nat._< sA₂) (sym redℕ) lt) ■ cong (sB₁ +_) redℕ
            hge2 : sB₁ Nat.≤ Fin.toℕ s1
            hge2 = subst (sB₁ Nat.≤_) (sym f1) (Nat.m≤m+n sB₁ kx)
            red2 = Fin.reduce≥ s1 hge2
            red2ℕ : Fin.toℕ red2 ≡ kx
            red2ℕ = toℕ-reduce≥ s1 hge2 ■ cong (Nat._∸ sB₁) f1 ■ Nat.m+n∸m≡n sB₁ kx
            innerChain : Fin.toℕ ((assocSwapᵣ sA₂ sB₁ ·ₖ (assocSwapᵣ sA₂ 2 ↑* sB₁)) red) ≡ sB₁ + (2 + kx)
            innerChain = ↑*-hi (assocSwapᵣ sA₂ 2) sB₁ s1 hge2
                       ■ cong (sB₁ +_) (toℕ-assoc-lt sA₂ 2 red2 (subst (Nat._< sA₂) (sym red2ℕ) lt)
                                        ■ cong (2 +_) red2ℕ)

        mover2 : ∀ p₁ p₂ q v → p₁ + p₂ Nat.≤ v →
                 p₁ + (p₂ + (q + ((v Nat.∸ p₁) Nat.∸ p₂))) ≡ q + v
        mover2 p₁ p₂ q v ple =
            cong (λ z → p₁ + (p₂ + (q + z))) (Nat.∸-+-assoc v p₁ p₂)
          ■ sym (Nat.+-assoc p₁ p₂ (q + (v Nat.∸ (p₁ + p₂))))
          ■ mover (p₁ + p₂) q v ple
        -- The shared e3 + r4′ tail of the A-blocks (when toℕ (r2 (r1 x)) = WB + kx).
        fromE2-A : sA₂ Nat.≤ Fin.toℕ x → Fin.toℕ (r2 (r1 x)) ≡ WB + Fin.toℕ x →
                   Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ WB + Fin.toℕ x
        fromE2-A ge e2 =
            ↑*-hi _ sB₂ (r3 (r2 (r1 x))) hge4
          ■ cong (sB₂ +_) (Mv-ge sA₂ sB₁ 2 (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ge4 ■ red4ℕ)
          ■ sym (Nat.+-assoc sB₂ (sB₁ + 2) (Fin.toℕ x))
          where
            kx = Fin.toℕ x
            ge3 : sA₂ + sB₂ Nat.≤ Fin.toℕ (r2 (r1 x))
            ge3 = subst (sA₂ + sB₂ Nat.≤_) (sym e2)
                    (subst (sA₂ + sB₂ Nat.≤_) (Nat.+-comm kx WB) (Nat.+-mono-≤ ge (Nat.m≤m+n sB₂ (sB₁ + 2))))
            e3 : Fin.toℕ (r3 (r2 (r1 x))) ≡ WB + kx
            e3 = toℕ-assoc-ge sA₂ sB₂ (r2 (r1 x)) ge3 ■ e2
            hge4 : sB₂ Nat.≤ Fin.toℕ (r3 (r2 (r1 x)))
            hge4 = subst (sB₂ Nat.≤_) (sym e3) (Nat.≤-trans (Nat.m≤m+n sB₂ (sB₁ + 2)) (Nat.m≤m+n WB kx))
            red4ℕ : Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ≡ (sB₁ + 2) + kx
            red4ℕ = toℕ-reduce≥ (r3 (r2 (r1 x))) hge4
                  ■ cong (Nat._∸ sB₂) e3
                  ■ cong (Nat._∸ sB₂) (Nat.+-assoc sB₂ (sB₁ + 2) kx)
                  ■ Nat.m+n∸m≡n sB₂ ((sB₁ + 2) + kx)
            ge4 : sA₂ + (sB₁ + 2) Nat.≤ Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4)
            ge4 = subst (sA₂ + (sB₁ + 2) Nat.≤_) (sym red4ℕ)
                    (subst (sA₂ + (sB₁ + 2) Nat.≤_) (Nat.+-comm kx (sB₁ + 2))
                      (Nat.+-monoˡ-≤ (sB₁ + 2) ge))

        -- Block A₁ (sA₂ ≤ kx < sA₂+sA₁): r1,r2 fix it (hi-then-lo).
        lhsA1 : sA₂ Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< sA₂ + sA₁ →
                Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ WB + Fin.toℕ x
        lhsA1 ge lt = fromE2-A ge e2
          where
            kx = Fin.toℕ x
            e1 : Fin.toℕ (r1 x) ≡ kx
            e1 = ↑*-hi _ sA₂ x ge
               ■ cong (sA₂ +_) (↑*-lo _ sA₁ (Fin.reduce≥ x ge)
                                  (subst (Nat._< sA₁) (sym (toℕ-reduce≥ x ge)) (sub-lt ge lt))
                                ■ toℕ-reduce≥ x ge)
               ■ Nat.m+[n∸m]≡n ge
            ge2 : sA₂ Nat.≤ Fin.toℕ (r1 x)
            ge2 = subst (sA₂ Nat.≤_) (sym e1) ge
            red2ℕ : Fin.toℕ (Fin.reduce≥ (r1 x) ge2) ≡ kx Nat.∸ sA₂
            red2ℕ = toℕ-reduce≥ (r1 x) ge2 ■ cong (Nat._∸ sA₂) e1
            e2 : Fin.toℕ (r2 (r1 x)) ≡ WB + kx
            e2 = ↑*-hi _ sA₂ (r1 x) ge2
               ■ cong (sA₂ +_) (Mv3-lt sA₁ sB₂ sB₁ 2 (Fin.reduce≥ (r1 x) ge2)
                                  (subst (Nat._< sA₁) (sym red2ℕ) (sub-lt ge lt))
                                ■ cong (WB +_) red2ℕ)
               ■ mover sA₂ WB kx ge

        -- Block Aν (sA₂+sA₁ ≤ kx < sA₂+sA₁+2): r1 moves it up (double-hi then Mv3-lt).
        lhsAv : sA₂ + sA₁ Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< sA₂ + sA₁ + 2 →
                Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ WB + Fin.toℕ x
        lhsAv geA ltA = fromE2-A ge e2
          where
            kx = Fin.toℕ x
            ge : sA₂ Nat.≤ kx
            ge = Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) geA
            geI0 : sA₁ Nat.≤ kx Nat.∸ sA₂
            geI0 = subst (Nat._≤ kx Nat.∸ sA₂) (Nat.m+n∸m≡n sA₂ sA₁) (Nat.∸-monoˡ-≤ sA₂ geA)
            geI : sA₁ Nat.≤ Fin.toℕ (Fin.reduce≥ x ge)
            geI = subst (sA₁ Nat.≤_) (sym (toℕ-reduce≥ x ge)) geI0
            redIℕ : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI) ≡ (kx Nat.∸ sA₂) Nat.∸ sA₁
            redIℕ = toℕ-reduce≥ (Fin.reduce≥ x ge) geI ■ cong (Nat._∸ sA₁) (toℕ-reduce≥ x ge)
            lt2 : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI) Nat.< 2
            lt2 = subst (Nat._< 2) (sym (redIℕ ■ Nat.∸-+-assoc kx sA₂ sA₁)) (sub-lt geA ltA)
            e1 : Fin.toℕ (r1 x) ≡ WB + kx
            e1 = ↑*-hi _ sA₂ x ge
               ■ cong (sA₂ +_) (↑*-hi _ sA₁ (Fin.reduce≥ x ge) geI
                                ■ cong (sA₁ +_) (Mv3-lt 2 sB₂ sB₁ 2 (Fin.reduce≥ (Fin.reduce≥ x ge) geI) lt2
                                                 ■ cong (WB +_) redIℕ))
               ■ mover2 sA₂ sA₁ WB kx geA
            ge2 : sA₂ Nat.≤ Fin.toℕ (r1 x)
            ge2 = subst (sA₂ Nat.≤_) (sym e1) (Nat.≤-trans ge (Nat.m≤n+m kx WB))
            red2ℕ : Fin.toℕ (Fin.reduce≥ (r1 x) ge2) ≡ WB + (kx Nat.∸ sA₂)
            red2ℕ = toℕ-reduce≥ (r1 x) ge2 ■ cong (Nat._∸ sA₂) e1 ■ Nat.+-∸-assoc WB ge
            geM : sA₁ + WB Nat.≤ Fin.toℕ (Fin.reduce≥ (r1 x) ge2)
            geM = subst (sA₁ + WB Nat.≤_) (sym red2ℕ)
                    (subst (Nat._≤ WB + (kx Nat.∸ sA₂)) (Nat.+-comm WB sA₁) (Nat.+-monoʳ-≤ WB geI0))
            e2 : Fin.toℕ (r2 (r1 x)) ≡ WB + kx
            e2 = ↑*-hi _ sA₂ (r1 x) ge2
               ■ cong (sA₂ +_) (Mv3-ge sA₁ sB₂ sB₁ 2 (Fin.reduce≥ (r1 x) ge2) geM ■ red2ℕ)
               ■ mover sA₂ WB kx ge

        recB : (sA₂ + sA₁) + 2 Nat.≤ Fin.toℕ x →
               sA₂ + (sA₁ + ((Fin.toℕ x Nat.∸ (sA₂ + sA₁)) Nat.∸ 2)) ≡ Fin.toℕ x Nat.∸ 2
        recB le =
            sym (Nat.+-assoc sA₂ sA₁ ((Fin.toℕ x Nat.∸ (sA₂ + sA₁)) Nat.∸ 2))
          ■ cong ((sA₂ + sA₁) +_) Xeq
          ■ Nat.m+[n∸m]≡n saa≤u
          where
            Xeq : (Fin.toℕ x Nat.∸ (sA₂ + sA₁)) Nat.∸ 2 ≡ (Fin.toℕ x Nat.∸ 2) Nat.∸ (sA₂ + sA₁)
            Xeq = Nat.∸-+-assoc (Fin.toℕ x) (sA₂ + sA₁) 2
                ■ cong (Fin.toℕ x Nat.∸_) (Nat.+-comm (sA₂ + sA₁) 2)
                ■ sym (Nat.∸-+-assoc (Fin.toℕ x) 2 (sA₂ + sA₁))
            saa≤u : sA₂ + sA₁ Nat.≤ Fin.toℕ x Nat.∸ 2
            saa≤u = subst (Nat._≤ Fin.toℕ x Nat.∸ 2) (Nat.m+n∸n≡m (sA₂ + sA₁) 2) (Nat.∸-monoˡ-≤ 2 le)

        recE2 : ∀ a b v → a + b Nat.≤ v → a + ((v Nat.∸ a) Nat.∸ b) ≡ v Nat.∸ b
        recE2 a b v ab≤v =
            cong (a +_) (Nat.∸-+-assoc v a b ■ cong (v Nat.∸_) (Nat.+-comm a b) ■ sym (Nat.∸-+-assoc v b a))
          ■ Nat.m+[n∸m]≡n (subst (Nat._≤ v Nat.∸ b) (Nat.m+n∸n≡m a b) (Nat.∸-monoˡ-≤ b ab≤v))

        -- B-super shared: r1 sends k ↦ k∸2 (mid); r2 sends it ↦ (k∸2)∸sA₁ (mid).
        eB1 : (sA₂ + sA₁) + 2 Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + WB →
              Fin.toℕ (r1 x) ≡ Fin.toℕ x Nat.∸ 2
        eB1 geW ltW =
            ↑*-hi _ sA₂ x ge
          ■ cong (sA₂ +_) (↑*-hi _ sA₁ (Fin.reduce≥ x ge) geI
                           ■ cong (sA₁ +_) (Mv3-mid 2 sB₂ sB₁ 2 (Fin.reduce≥ (Fin.reduce≥ x ge) geI) ge2m lt2m
                                            ■ cong (Nat._∸ 2) redIℕ))
          ■ recB geW
          where
            kx = Fin.toℕ x
            saa≤kx : sA₂ + sA₁ Nat.≤ kx
            saa≤kx = Nat.≤-trans (Nat.m≤m+n (sA₂ + sA₁) 2) geW
            ge : sA₂ Nat.≤ kx
            ge = Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) saa≤kx
            geI0 : sA₁ Nat.≤ kx Nat.∸ sA₂
            geI0 = subst (Nat._≤ kx Nat.∸ sA₂) (Nat.m+n∸m≡n sA₂ sA₁) (Nat.∸-monoˡ-≤ sA₂ saa≤kx)
            geI : sA₁ Nat.≤ Fin.toℕ (Fin.reduce≥ x ge)
            geI = subst (sA₁ Nat.≤_) (sym (toℕ-reduce≥ x ge)) geI0
            redIℕ : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI) ≡ kx Nat.∸ (sA₂ + sA₁)
            redIℕ = toℕ-reduce≥ (Fin.reduce≥ x ge) geI ■ cong (Nat._∸ sA₁) (toℕ-reduce≥ x ge)
                  ■ Nat.∸-+-assoc kx sA₂ sA₁
            ge2m : 2 Nat.≤ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI)
            ge2m = subst (2 Nat.≤_) (sym redIℕ)
                     (subst (Nat._≤ kx Nat.∸ (sA₂ + sA₁)) (Nat.m+n∸m≡n (sA₂ + sA₁) 2)
                       (Nat.∸-monoˡ-≤ (sA₂ + sA₁) geW))
            lt2m : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI) Nat.< 2 + WB
            lt2m = subst (Nat._< 2 + WB) (sym redIℕ)
                     (sub-lt saa≤kx (subst (kx Nat.<_) (Nat.+-assoc (sA₂ + sA₁) 2 WB) ltW))

        eB2 : (sA₂ + sA₁) + 2 Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + WB →
              Fin.toℕ (r2 (r1 x)) ≡ (Fin.toℕ x Nat.∸ 2) Nat.∸ sA₁
        eB2 geW ltW =
            ↑*-hi _ sA₂ (r1 x) ge2
          ■ cong (sA₂ +_) (Mv3-mid sA₁ sB₂ sB₁ 2 (Fin.reduce≥ (r1 x) ge2) geMm ltMm ■ cong (Nat._∸ sA₁) red2ℕ)
          ■ recE2 sA₂ sA₁ (Fin.toℕ x Nat.∸ 2) saa≤u
          where
            kx = Fin.toℕ x
            saa≤u : sA₂ + sA₁ Nat.≤ kx Nat.∸ 2
            saa≤u = subst (Nat._≤ kx Nat.∸ 2) (Nat.m+n∸n≡m (sA₂ + sA₁) 2) (Nat.∸-monoˡ-≤ 2 geW)
            sA₂≤u : sA₂ Nat.≤ kx Nat.∸ 2
            sA₂≤u = Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) saa≤u
            2≤kx : 2 Nat.≤ kx
            2≤kx = Nat.≤-trans (Nat.m≤n+m 2 (sA₂ + sA₁)) geW
            e1 : Fin.toℕ (r1 x) ≡ kx Nat.∸ 2
            e1 = eB1 geW ltW
            ge2 : sA₂ Nat.≤ Fin.toℕ (r1 x)
            ge2 = subst (sA₂ Nat.≤_) (sym e1) sA₂≤u
            red2ℕ : Fin.toℕ (Fin.reduce≥ (r1 x) ge2) ≡ (kx Nat.∸ 2) Nat.∸ sA₂
            red2ℕ = toℕ-reduce≥ (r1 x) ge2 ■ cong (Nat._∸ sA₂) e1
            geMm : sA₁ Nat.≤ Fin.toℕ (Fin.reduce≥ (r1 x) ge2)
            geMm = subst (sA₁ Nat.≤_) (sym red2ℕ)
                     (subst (Nat._≤ (kx Nat.∸ 2) Nat.∸ sA₂) (Nat.m+n∸m≡n sA₂ sA₁) (Nat.∸-monoˡ-≤ sA₂ saa≤u))
            ltMm : Fin.toℕ (Fin.reduce≥ (r1 x) ge2) Nat.< sA₁ + WB
            ltMm = subst (Nat._< sA₁ + WB) (sym red2ℕ) klt
              where
                -- (kx ∸ 2) ∸ sA₂ < sA₁ + WB
                klt : (kx Nat.∸ 2) Nat.∸ sA₂ Nat.< sA₁ + WB
                klt = sub-lt sA₂≤u (subst (kx Nat.∸ 2 Nat.<_) (Nat.+-assoc sA₂ sA₁ WB) kx∸2<)
                  where
                    kx∸2< : kx Nat.∸ 2 Nat.< (sA₂ + sA₁) + WB
                    kx∸2< = sub-lt 2≤kx (subst (kx Nat.<_) reassoc ltW)
                      where reassoc : (sA₂ + sA₁) + 2 + WB ≡ 2 + ((sA₂ + sA₁) + WB)
                            reassoc = cong (Nat._+ WB) (Nat.+-comm (sA₂ + sA₁) 2)
                                    ■ Nat.+-assoc 2 (sA₂ + sA₁) WB

        open +-*-Solver

        -- Block B₂ (WA ≤ kx < WA+sB₂): r3 mid, r4′ lo.
        lhsB2 : (sA₂ + sA₁) + 2 Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + sB₂ →
                Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ Fin.toℕ x Nat.∸ WA
        lhsB2 geW ltB =
            ↑*-lo _ sB₂ (r3 (r2 (r1 x))) lt4 ■ e3 ■ ∸3 2 sA₁ sA₂ kx ■ cong (kx Nat.∸_) plusWA
          where
            kx = Fin.toℕ x
            eqWaa : (sA₂ + sA₁) + 2 ≡ 2 + sA₁ + sA₂
            eqWaa = solve 2 (λ a b → (a :+ b) :+ con 2 := (con 2 :+ b) :+ a) refl sA₂ sA₁
            plusWA : 2 + sA₁ + sA₂ ≡ WA
            plusWA = solve 2 (λ a b → (con 2 :+ a) :+ b := b :+ (a :+ con 2)) refl sA₁ sA₂
            waa≤kx : 2 + sA₁ + sA₂ Nat.≤ kx
            waa≤kx = subst (Nat._≤ kx) eqWaa geW
            ltW : kx Nat.< (sA₂ + sA₁) + 2 + WB
            ltW = Nat.<-≤-trans ltB (Nat.+-monoʳ-≤ ((sA₂ + sA₁) + 2) (Nat.m≤m+n sB₂ (sB₁ + 2)))
            e2 : Fin.toℕ (r2 (r1 x)) ≡ (kx Nat.∸ 2) Nat.∸ sA₁
            e2 = eB2 geW ltW
            saa≤u : sA₂ + sA₁ Nat.≤ kx Nat.∸ 2
            saa≤u = subst (Nat._≤ kx Nat.∸ 2) (Nat.m+n∸n≡m (sA₂ + sA₁) 2) (Nat.∸-monoˡ-≤ 2 geW)
            ge3 : sA₂ Nat.≤ Fin.toℕ (r2 (r1 x))
            ge3 = subst (sA₂ Nat.≤_) (sym e2)
                    (subst (Nat._≤ (kx Nat.∸ 2) Nat.∸ sA₁) (Nat.m+n∸n≡m sA₂ sA₁) (Nat.∸-monoˡ-≤ sA₁ saa≤u))
            lt3 : Fin.toℕ (r2 (r1 x)) Nat.< sA₂ + sB₂
            lt3 = subst (Nat._< sA₂ + sB₂) (sym e2)
                    (subst (Nat._< sA₂ + sB₂) (sym (Nat.∸-+-assoc kx 2 sA₁))
                      (sub-lt 2+sA₁≤kx (subst (kx Nat.<_) eqLt3 ltB)))
              where
                2+sA₁≤kx : 2 + sA₁ Nat.≤ kx
                2+sA₁≤kx = Nat.≤-trans (Nat.m≤m+n (2 + sA₁) sA₂) waa≤kx
                eqLt3 : (sA₂ + sA₁) + 2 + sB₂ ≡ (2 + sA₁) + (sA₂ + sB₂)
                eqLt3 = solve 3 (λ a b c → ((a :+ b) :+ con 2) :+ c := (con 2 :+ b) :+ (a :+ c)) refl sA₂ sA₁ sB₂
            e3 : Fin.toℕ (r3 (r2 (r1 x))) ≡ ((kx Nat.∸ 2) Nat.∸ sA₁) Nat.∸ sA₂
            e3 = toℕ-assoc-mid sA₂ sB₂ (r2 (r1 x)) ge3 lt3 ■ cong (Nat._∸ sA₂) e2
            lt4 : Fin.toℕ (r3 (r2 (r1 x))) Nat.< sB₂
            lt4 = subst (Nat._< sB₂) (sym e3)
                    (subst (Nat._< sB₂) (sym (∸3 2 sA₁ sA₂ kx))
                      (sub-lt waa≤kx (subst (kx Nat.<_) (cong (Nat._+ sB₂) eqWaa) ltB)))

        -- Block nn (WA+WB ≤ kx): everything is fixed (all ge).
        lhsNN : (sA₂ + sA₁) + 2 + WB Nat.≤ Fin.toℕ x → Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ Fin.toℕ x
        lhsNN geWW =
            ↑*-hi _ sB₂ (r3 (r2 (r1 x))) hge4
          ■ cong (sB₂ +_) (Mv-ge sA₂ sB₁ 2 (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ge4 ■ red4ℕ)
          ■ Nat.m+[n∸m]≡n sB₂≤kx
          where
            kx = Fin.toℕ x
            saa≤kx : sA₂ + sA₁ Nat.≤ kx
            saa≤kx = Nat.≤-trans (Nat.m≤m+n (sA₂ + sA₁) 2) (Nat.≤-trans (Nat.m≤m+n ((sA₂ + sA₁) + 2) WB) geWW)
            ge : sA₂ Nat.≤ kx
            ge = Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) saa≤kx
            geI0 : sA₁ Nat.≤ kx Nat.∸ sA₂
            geI0 = subst (Nat._≤ kx Nat.∸ sA₂) (Nat.m+n∸m≡n sA₂ sA₁) (Nat.∸-monoˡ-≤ sA₂ saa≤kx)
            geI : sA₁ Nat.≤ Fin.toℕ (Fin.reduce≥ x ge)
            geI = subst (sA₁ Nat.≤_) (sym (toℕ-reduce≥ x ge)) geI0
            redIℕ : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI) ≡ kx Nat.∸ (sA₂ + sA₁)
            redIℕ = toℕ-reduce≥ (Fin.reduce≥ x ge) geI ■ cong (Nat._∸ sA₁) (toℕ-reduce≥ x ge) ■ Nat.∸-+-assoc kx sA₂ sA₁
            ge2g : 2 + WB Nat.≤ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ x ge) geI)
            ge2g = subst (2 + WB Nat.≤_) (sym redIℕ)
                     (subst (Nat._≤ kx Nat.∸ (sA₂ + sA₁)) (Nat.m+n∸m≡n (sA₂ + sA₁) (2 + WB))
                       (Nat.∸-monoˡ-≤ (sA₂ + sA₁) (subst (Nat._≤ kx) (Nat.+-assoc (sA₂ + sA₁) 2 WB) geWW)))
            e1 : Fin.toℕ (r1 x) ≡ kx
            e1 = ↑*-hi _ sA₂ x ge
               ■ cong (sA₂ +_) (↑*-hi _ sA₁ (Fin.reduce≥ x ge) geI
                                ■ cong (sA₁ +_) (Mv3-ge 2 sB₂ sB₁ 2 (Fin.reduce≥ (Fin.reduce≥ x ge) geI) ge2g ■ redIℕ))
               ■ (sym (Nat.+-assoc sA₂ sA₁ (kx Nat.∸ (sA₂ + sA₁))) ■ Nat.m+[n∸m]≡n saa≤kx)
            ge2 : sA₂ Nat.≤ Fin.toℕ (r1 x)
            ge2 = subst (sA₂ Nat.≤_) (sym e1) ge
            red2ℕ : Fin.toℕ (Fin.reduce≥ (r1 x) ge2) ≡ kx Nat.∸ sA₂
            red2ℕ = toℕ-reduce≥ (r1 x) ge2 ■ cong (Nat._∸ sA₂) e1
            geM2 : sA₁ + WB Nat.≤ Fin.toℕ (Fin.reduce≥ (r1 x) ge2)
            geM2 = subst (sA₁ + WB Nat.≤_) (sym red2ℕ)
                     (subst (Nat._≤ kx Nat.∸ sA₂) (Nat.m+n∸m≡n sA₂ (sA₁ + WB))
                       (Nat.∸-monoˡ-≤ sA₂ (subst (Nat._≤ kx) (Nat.+-assoc sA₂ sA₁ WB)
                         (Nat.≤-trans (Nat.+-monoˡ-≤ WB (Nat.m≤m+n (sA₂ + sA₁) 2)) geWW))))
            e2 : Fin.toℕ (r2 (r1 x)) ≡ kx
            e2 = ↑*-hi _ sA₂ (r1 x) ge2
               ■ cong (sA₂ +_) (Mv3-ge sA₁ sB₂ sB₁ 2 (Fin.reduce≥ (r1 x) ge2) geM2 ■ red2ℕ)
               ■ Nat.m+[n∸m]≡n ge
            sA₂+sB₂≤kx : sA₂ + sB₂ Nat.≤ kx
            sA₂+sB₂≤kx = Nat.≤-trans (Nat.+-mono-≤ (Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) (Nat.m≤m+n (sA₂ + sA₁) 2))
                                                   (Nat.m≤m+n sB₂ (sB₁ + 2))) geWW
            ge3 : sA₂ + sB₂ Nat.≤ Fin.toℕ (r2 (r1 x))
            ge3 = subst (sA₂ + sB₂ Nat.≤_) (sym e2) sA₂+sB₂≤kx
            e3 : Fin.toℕ (r3 (r2 (r1 x))) ≡ kx
            e3 = toℕ-assoc-ge sA₂ sB₂ (r2 (r1 x)) ge3 ■ e2
            sB₂≤kx : sB₂ Nat.≤ kx
            sB₂≤kx = Nat.≤-trans (Nat.m≤n+m sB₂ sA₂) sA₂+sB₂≤kx
            hge4 : sB₂ Nat.≤ Fin.toℕ (r3 (r2 (r1 x)))
            hge4 = subst (sB₂ Nat.≤_) (sym e3) sB₂≤kx
            red4ℕ : Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ≡ kx Nat.∸ sB₂
            red4ℕ = toℕ-reduce≥ (r3 (r2 (r1 x))) hge4 ■ cong (Nat._∸ sB₂) e3
            wfull : sA₂ + (sB₂ + (sB₁ + 2)) Nat.≤ kx
            wfull = Nat.≤-trans (Nat.+-monoˡ-≤ WB (Nat.≤-trans (Nat.m≤m+n sA₂ sA₁) (Nat.m≤m+n (sA₂ + sA₁) 2))) geWW
            ge4 : sA₂ + (sB₁ + 2) Nat.≤ Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4)
            ge4 = subst (sA₂ + (sB₁ + 2) Nat.≤_) (sym red4ℕ)
                    (subst (Nat._≤ kx Nat.∸ sB₂) (Nat.m+n∸m≡n sB₂ (sA₂ + (sB₁ + 2)))
                      (Nat.∸-monoˡ-≤ sB₂ (subst (Nat._≤ kx) eqReord wfull)))
              where eqReord : sA₂ + (sB₂ + (sB₁ + 2)) ≡ sB₂ + (sA₂ + (sB₁ + 2))
                    eqReord = solve 3 (λ a b c → a :+ (b :+ c) := b :+ (a :+ c)) refl sA₂ sB₂ (sB₁ + 2)

        -- Shared B₁/Bν tail: r3 ge, r4′ hi+Mv-mid (when toℕ (r2 (r1 x)) = (kx∸2)∸sA₁ and kx ≥ WA+sB₂).
        fromE2-B : (sA₂ + sA₁) + 2 + sB₂ Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + WB →
                   Fin.toℕ (r2 (r1 x)) ≡ (Fin.toℕ x Nat.∸ 2) Nat.∸ sA₁ →
                   Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ Fin.toℕ x Nat.∸ WA
        fromE2-B geS ltS e2 =
            ↑*-hi _ sB₂ (r3 (r2 (r1 x))) hge4
          ■ cong (sB₂ +_) (Mv-mid sA₂ sB₁ 2 (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ge4 lt4r ■ cong (Nat._∸ sA₂) red4ℕ)
          ■ recE2 sB₂ sA₂ u sB₂+sA₂≤u
          ■ ∸3 2 sA₁ sA₂ kx ■ cong (kx Nat.∸_) plusWA
          where
            kx = Fin.toℕ x
            u = (kx Nat.∸ 2) Nat.∸ sA₁
            plusWA : 2 + sA₁ + sA₂ ≡ WA
            plusWA = solve 2 (λ a b → (con 2 :+ a) :+ b := b :+ (a :+ con 2)) refl sA₁ sA₂
            sAsB≤u : sA₂ + sB₂ Nat.≤ u
            sAsB≤u = subst (sA₂ + sB₂ Nat.≤_) (sym (Nat.∸-+-assoc kx 2 sA₁))
                       (subst (Nat._≤ kx Nat.∸ (2 + sA₁)) (Nat.m+n∸m≡n (2 + sA₁) (sA₂ + sB₂))
                         (Nat.∸-monoˡ-≤ (2 + sA₁) (subst (Nat._≤ kx) eqGe3 geS)))
              where eqGe3 : (sA₂ + sA₁) + 2 + sB₂ ≡ (2 + sA₁) + (sA₂ + sB₂)
                    eqGe3 = solve 3 (λ a b c → ((a :+ b) :+ con 2) :+ c := (con 2 :+ b) :+ (a :+ c)) refl sA₂ sA₁ sB₂
            sB₂+sA₂≤u : sB₂ + sA₂ Nat.≤ u
            sB₂+sA₂≤u = subst (Nat._≤ u) (Nat.+-comm sA₂ sB₂) sAsB≤u
            ge3 : sA₂ + sB₂ Nat.≤ Fin.toℕ (r2 (r1 x))
            ge3 = subst (sA₂ + sB₂ Nat.≤_) (sym e2) sAsB≤u
            e3 : Fin.toℕ (r3 (r2 (r1 x))) ≡ u
            e3 = toℕ-assoc-ge sA₂ sB₂ (r2 (r1 x)) ge3 ■ e2
            sB₂≤u : sB₂ Nat.≤ u
            sB₂≤u = Nat.≤-trans (Nat.m≤n+m sB₂ sA₂) sAsB≤u
            hge4 : sB₂ Nat.≤ Fin.toℕ (r3 (r2 (r1 x)))
            hge4 = subst (sB₂ Nat.≤_) (sym e3) sB₂≤u
            red4ℕ : Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ≡ u Nat.∸ sB₂
            red4ℕ = toℕ-reduce≥ (r3 (r2 (r1 x))) hge4 ■ cong (Nat._∸ sB₂) e3
            ge4 : sA₂ Nat.≤ Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4)
            ge4 = subst (sA₂ Nat.≤_) (sym red4ℕ)
                    (subst (Nat._≤ u Nat.∸ sB₂) (Nat.m+n∸n≡m sA₂ sB₂) (Nat.∸-monoˡ-≤ sB₂ sAsB≤u))
            lt4r : Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) Nat.< sA₂ + (sB₁ + 2)
            lt4r = subst (Nat._< sA₂ + (sB₁ + 2)) (sym red4canon)
                     (sub-lt waaB≤kx (subst (kx Nat.<_) eqLt4 ltS))
              where
                red4canon : Fin.toℕ (Fin.reduce≥ (r3 (r2 (r1 x))) hge4) ≡ kx Nat.∸ ((2 + sA₁) + sB₂)
                red4canon = red4ℕ ■ cong (Nat._∸ sB₂) (Nat.∸-+-assoc kx 2 sA₁) ■ Nat.∸-+-assoc kx (2 + sA₁) sB₂
                waaB≤kx : (2 + sA₁) + sB₂ Nat.≤ kx
                waaB≤kx = Nat.≤-trans (Nat.+-monoˡ-≤ sB₂ loWaa) geS
                  where loWaa : 2 + sA₁ Nat.≤ (sA₂ + sA₁) + 2
                        loWaa = subst (2 + sA₁ Nat.≤_)
                                  (solve 2 (λ a b → a :+ (con 2 :+ b) := (a :+ b) :+ con 2) refl sA₂ sA₁)
                                  (Nat.m≤n+m (2 + sA₁) sA₂)
                eqLt4 : (sA₂ + sA₁) + 2 + WB ≡ ((2 + sA₁) + sB₂) + (sA₂ + (sB₁ + 2))
                eqLt4 = solve 4 (λ a b c d → ((a :+ b) :+ con 2) :+ (c :+ (d :+ con 2))
                                            := ((con 2 :+ b) :+ c) :+ (a :+ (d :+ con 2))) refl sA₂ sA₁ sB₂ sB₁

        lhsB1 : (sA₂ + sA₁) + 2 + sB₂ Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + sB₂ + sB₁ →
                Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ Fin.toℕ x Nat.∸ WA
        lhsB1 geS ltB1 = fromE2-B geS ltS (eB2 geW ltS)
          where
            kx = Fin.toℕ x
            geW : (sA₂ + sA₁) + 2 Nat.≤ kx
            geW = Nat.≤-trans (Nat.m≤m+n ((sA₂ + sA₁) + 2) sB₂) geS
            ltS : kx Nat.< (sA₂ + sA₁) + 2 + WB
            ltS = Nat.<-≤-trans (subst (kx Nat.<_) (Nat.+-assoc ((sA₂ + sA₁) + 2) sB₂ sB₁) ltB1)
                                (Nat.+-monoʳ-≤ ((sA₂ + sA₁) + 2) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n sB₁ 2)))

        lhsBv : (sA₂ + sA₁) + 2 + sB₂ + sB₁ Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< (sA₂ + sA₁) + 2 + WB →
                Fin.toℕ (r4′ (r3 (r2 (r1 x)))) ≡ Fin.toℕ x Nat.∸ WA
        lhsBv geBv ltS = fromE2-B geS ltS (eB2 geW ltS)
          where
            kx = Fin.toℕ x
            geS : (sA₂ + sA₁) + 2 + sB₂ Nat.≤ kx
            geS = Nat.≤-trans (Nat.m≤m+n ((sA₂ + sA₁) + 2 + sB₂) sB₁) geBv
            geW : (sA₂ + sA₁) + 2 Nat.≤ kx
            geW = Nat.≤-trans (Nat.m≤m+n ((sA₂ + sA₁) + 2) sB₂) geS

        dispatch : Fin.toℕ ((r1 ·ₖ (r2 ·ₖ (r3 ·ₖ r4′))) x) ≡ Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ x)
        dispatch = body
          where
            WAassoc : (sA₂ + sA₁) + 2 ≡ WA
            WAassoc = Nat.+-assoc sA₂ sA₁ 2
            mid-ge : (sA₂ + sA₁) + 2 Nat.≤ Fin.toℕ x → WA Nat.≤ Fin.toℕ x
            mid-ge h = subst (Nat._≤ Fin.toℕ x) WAassoc h
            mid-lt : Fin.toℕ x Nat.< ((sA₂ + sA₁) + 2) + WB → Fin.toℕ x Nat.< WA + WB
            mid-lt h = subst (Fin.toℕ x Nat.<_) (cong (Nat._+ WB) WAassoc) h
            sB₂≤WB : sB₂ Nat.≤ WB
            sB₂≤WB = Nat.m≤m+n sB₂ (sB₁ + 2)
            body : Fin.toℕ ((r1 ·ₖ (r2 ·ₖ (r3 ·ₖ r4′))) x) ≡ Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ x)
            body with Fin.toℕ x Nat.<? sA₂
            ... | yes p = lhsA2 p ■ sym (clean-lt (Nat.<-≤-trans p (Nat.m≤m+n sA₂ (sA₁ + 2))))
            ... | no ¬p with Fin.toℕ x Nat.<? (sA₂ + sA₁)
            ...   | yes q = lhsA1 (Nat.≮⇒≥ ¬p) q
                          ■ sym (clean-lt (Nat.<-≤-trans q (subst (sA₂ + sA₁ Nat.≤_) WAassoc (Nat.m≤m+n (sA₂ + sA₁) 2))))
            ...   | no ¬q with Fin.toℕ x Nat.<? ((sA₂ + sA₁) + 2)
            ...      | yes r = lhsAv (Nat.≮⇒≥ ¬q) r ■ sym (clean-lt (subst (Fin.toℕ x Nat.<_) WAassoc r))
            ...      | no ¬r with Fin.toℕ x Nat.<? ((sA₂ + sA₁) + 2 + sB₂)
            ...         | yes s = lhsB2 (Nat.≮⇒≥ ¬r) s
                                ■ sym (clean-mid (mid-ge (Nat.≮⇒≥ ¬r))
                                        (mid-lt (Nat.<-≤-trans s (Nat.+-monoʳ-≤ ((sA₂ + sA₁) + 2) sB₂≤WB))))
            ...         | no ¬s with Fin.toℕ x Nat.<? ((sA₂ + sA₁) + 2 + sB₂ + sB₁)
            ...            | yes t = lhsB1 (Nat.≮⇒≥ ¬s) t
                                   ■ sym (clean-mid (mid-ge (Nat.≮⇒≥ ¬r))
                                           (mid-lt (Nat.<-≤-trans
                                             (subst (Fin.toℕ x Nat.<_) (Nat.+-assoc ((sA₂ + sA₁) + 2) sB₂ sB₁) t)
                                             (Nat.+-monoʳ-≤ ((sA₂ + sA₁) + 2) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n sB₁ 2))))))
            ...            | no ¬t with Fin.toℕ x Nat.<? ((sA₂ + sA₁) + 2 + WB)
            ...               | yes u = lhsBv (Nat.≮⇒≥ ¬t) u ■ sym (clean-mid (mid-ge (Nat.≮⇒≥ ¬r)) (mid-lt u))
            ...               | no ¬u = lhsNN (Nat.≮⇒≥ ¬u)
                                       ■ sym (clean-ge (subst (Nat._≤ Fin.toℕ x) (cong (Nat._+ WB) WAassoc) (Nat.≮⇒≥ ¬u)))
    consolidate-3 : _ ≡ _
    consolidate-3 =
        φ^-⋯ₚ sB₁ _ (assocSwapᵣ sA₂ 2)
      ■ cong (φ^ sB₁)
          ( 𝐔.fusionₚ _ (assocSwapᵣ sA₂ sB₁) (assocSwapᵣ sA₂ 2 ↑* sB₁)
          ■ φ^-⋯ₚ sB₂ _ (assocSwapᵣ sA₂ sB₁ ·ₖ (assocSwapᵣ sA₂ 2 ↑* sB₁)) )
    consolidate-2 : _ ≡ _
    consolidate-2 =
        φ^-⋯ₚ sB₁ _ (assocSwapᵣ sA₁ 2)
      ■ cong (φ^ sB₁)
          ( 𝐔.fusionₚ _ (assocSwapᵣ sA₁ sB₁) (assocSwapᵣ sA₁ 2 ↑* sB₁)
          ■ φ^-⋯ₚ sB₂ _ (assocSwapᵣ sA₁ sB₁ ·ₖ (assocSwapᵣ sA₁ 2 ↑* sB₁))
          ■ cong (φ^ sB₂)
              ( 𝐔.fusionₚ _ (assocSwapᵣ sA₁ sB₂) ((assocSwapᵣ sA₁ sB₁ ·ₖ (assocSwapᵣ sA₁ 2 ↑* sB₁)) ↑* sB₂)
              ■ φ^-⋯ₚ sA₂ _ (assocSwapᵣ sA₁ sB₂ ·ₖ ((assocSwapᵣ sA₁ sB₁ ·ₖ (assocSwapᵣ sA₁ 2 ↑* sB₁)) ↑* sB₂)) ) )
    consolidate : _ ≡ _
    consolidate =
        φ^-⋯ₚ sB₁ _ (assocSwapᵣ 2 2)
      ■ cong (φ^ sB₁)
          ( 𝐔.fusionₚ _ (assocSwapᵣ 2 sB₁) (assocSwapᵣ 2 2 ↑* sB₁)
          ■ φ^-⋯ₚ sB₂ _ (assocSwapᵣ 2 sB₁ ·ₖ (assocSwapᵣ 2 2 ↑* sB₁))
          ■ cong (φ^ sB₂)
              ( 𝐔.fusionₚ _ (assocSwapᵣ 2 sB₂) ((assocSwapᵣ 2 sB₁ ·ₖ (assocSwapᵣ 2 2 ↑* sB₁)) ↑* sB₂)
              ■ φ^-⋯ₚ sA₁ _ (assocSwapᵣ 2 sB₂ ·ₖ ((assocSwapᵣ 2 sB₁ ·ₖ (assocSwapᵣ 2 2 ↑* sB₁)) ↑* sB₂))
              ■ cong (φ^ sA₁)
                  (φ^-⋯ₚ sA₂ _ ((assocSwapᵣ 2 sB₂ ·ₖ ((assocSwapᵣ 2 sB₁ ·ₖ (assocSwapᵣ 2 2 ↑* sB₁)) ↑* sB₂)) ↑* sA₁)) ) )

