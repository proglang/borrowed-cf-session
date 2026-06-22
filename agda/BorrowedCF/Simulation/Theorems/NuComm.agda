module BorrowedCF.Simulation.Theorems.NuComm where

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
open import BorrowedCF.Simulation.Theorems.Transpose
open import BorrowedCF.Simulation.Theorems.LeafPerm

U-ν-comm : (σ : m →ₛ n) {B₁ B₂ A₁ A₂ : 𝐓.BindGroup} {P : 𝐓.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + m))} →
           U[ 𝐓.ν B₁ B₂ (𝐓.ν A₁ A₂ P) ] σ 𝐔.≋
           U[ 𝐓.ν A₁ A₂ (𝐓.ν B₁ B₂ (P 𝐓.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))) ] σ
U-ν-comm {m = m} {n = n} σ {B₁} {B₂} {A₁} {A₂} {P} =
     Uν-flat σ B₁ B₂ (𝐓.ν A₁ A₂ P)
  ◅◅ 𝐔.ν-cong (φ^-cong (syncs B₁) (φ^-cong (syncs B₂)
       (𝐔.∥-cong ε (𝐔.∥-cong ε (Uν-flat τB A₁ A₂ P)))))
  ◅◅ 𝐔.ν-cong (φ^-cong (syncs B₁) (φ^-cong (syncs B₂)
       (𝐔.∥-assoc ◅◅ νφφ-ext (syncs A₁) (syncs A₂) _ _)))
  -- CENTRAL: MID_L ≋ MID_R.  telescope-transpose moves the binders; the remaining hole
  -- is PHASE 3 — the body reconciliation BODY_L ⋯ₚ TRANSP ≋ BODY_R (under the binders),
  -- where BODY_L = (FlagsB₁⋯ ∥ FlagsB₂⋯) ∥ (FlagsA₁⋯ ∥ (FlagsA₂ ∥ U[P]τA))
  --   and BODY_R = (FlagsA₁⋯ ∥ FlagsA₂⋯) ∥ (FlagsB₁⋯ ∥ (FlagsB₂ ∥ U[P′]τB′)).
  -- This is a ≋ (not ≡): (i) prove TRANSP ≗ assocSwapᵣ (sA₂+sA₁+2) (sB₂+sB₁+2) [clean block
  -- transpose, ~50-80 line toℕ proof] and rewrite via ⋯ₚ-cong; (ii) ∥-comm/assoc to reorder
  -- the flag groups; (iii) per flag: Flags-⋯-cong (Flatten.agda); (iv) leaf:
  -- U[P]τA ⋯ₚ TRANSP ≡ U[P′]τB′ via U-σ⋯/U-⋯ₚ/U-cong + canonₛ-nat + a swap-++ₛ-style 4-block
  -- data permutation (analogue of U-ν-swap's subEq, ~doubled).  See handoff notes in
  -- the memory file simulation-progress.md (UPDATE 5).
  ◅◅ telescope-transpose (syncs B₁) (syncs B₂) (syncs A₁) (syncs A₂) _
  ◅◅ 𝐔.ν-cong (φ^-cong (syncs A₁) (φ^-cong (syncs A₂)
       (𝐔.ν-cong (φ^-cong (syncs B₁) (φ^-cong (syncs B₂) bodyReconcile)))))
  ◅◅ Eq*.symmetric _ (𝐔.ν-cong (φ^-cong (syncs A₁) (φ^-cong (syncs A₂)
       (𝐔.∥-assoc ◅◅ νφφ-ext (syncs B₁) (syncs B₂) _ _))))
  ◅◅ Eq*.symmetric _
       (𝐔.ν-cong (φ^-cong (syncs A₁) (φ^-cong (syncs A₂)
          (𝐔.∥-cong ε (𝐔.∥-cong ε (Uν-flat τA′ B₁ B₂ P′))))))
  ◅◅ Eq*.symmetric _ (Uν-flat σ A₁ A₂ (𝐓.ν B₁ B₂ P′))
  where
    P′ : 𝐓.Proc (sum B₁ + sum B₂ + (sum A₁ + sum A₂ + m))
    P′ = P 𝐓.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)
    τB : (sum B₁ + sum B₂ + m) →ₛ (syncs B₂ + (syncs B₁ + (2 + n)))
    τB = ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ
          canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit))
         ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
    τA′ : (sum A₁ + sum A₂ + m) →ₛ (syncs A₂ + (syncs A₁ + (2 + n)))
    τA′ = ((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂)) ++ₛ
           canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs A₁) 1F , K `unit))
          ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs A₂))
    sA1 = syncs A₁
    sA2 = syncs A₂
    sB1 = syncs B₁
    sB2 = syncs B₂
    cT = cleanT-comm sB1 sB2 sA1 sA2
    WA = sA2 + (sA1 + 2)
    WB = sB2 + (sB1 + 2)
    c1 : (Flags {2 + n} B₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA1
              𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2 𝐔.⋯ₚ cT)
         ≡ (Flags {2 + (sA2 + (sA1 + (2 + n)))} B₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2)
    c1 =
        𝐔.fusionₚ (Flags B₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) cT
      ■ 𝐔.fusionₚ (Flags B₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
      ■ 𝐔.fusionₚ (Flags B₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))
      ■ 𝐔.fusionₚ (Flags B₁) (weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)))
      ■ Flags-⋯-cong B₁ _ (weaken* ⦃ Kᵣ ⦄ sB2) h1
      where
        h1 : ∀ (i : 𝔽 sB1) →
             (weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)))) (i ↑ˡ (2 + n))
             ≡ weaken* ⦃ Kᵣ ⦄ sB2 (i ↑ˡ (2 + (sA2 + (sA1 + (2 + n)))))
        h1 i = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
          where
            w0 = i ↑ˡ (2 + n)
            w1 = weaken* ⦃ Kᵣ ⦄ sB2 w0
            w2 = weaken* ⦃ Kᵣ ⦄ 2 w1
            w3 = weaken* ⦃ Kᵣ ⦄ sA1 w2
            w4 = weaken* ⦃ Kᵣ ⦄ sA2 w3
            w4ℕ : Fin.toℕ w4 ≡ sA2 + (sA1 + (2 + (sB2 + Fin.toℕ i)))
            w4ℕ = toℕ-wk sA2 w3 ■ cong (sA2 +_) (toℕ-wk sA1 w2 ■ cong (sA1 +_)
                    (toℕ-wk 2 w1 ■ cong (2 +_) (toℕ-wk sB2 w0 ■ cong (sB2 +_) (Fin.toℕ-↑ˡ i (2 + n)))))
            w4eq : sA2 + (sA1 + (2 + (sB2 + Fin.toℕ i))) ≡ WA + (sB2 + Fin.toℕ i)
            w4eq = solve 4 (λ a b c k → a :+ (b :+ (con 2 :+ (c :+ k))) := (a :+ (b :+ con 2)) :+ (c :+ k))
                          refl sA2 sA1 sB2 (Fin.toℕ i)
              where open +-*-Solver
            i<WB : sB2 + Fin.toℕ i Nat.< WB
            i<WB = Nat.+-monoʳ-< sB2 (Nat.<-≤-trans (Fin.toℕ<n i) (Nat.m≤m+n sB1 2))
            lhsℕ : Fin.toℕ (cT w4) ≡ sB2 + Fin.toℕ i
            lhsℕ = cleanTℕ-mid sB1 sB2 sA1 sA2 w4
                     (subst (WA Nat.≤_) (sym (w4ℕ ■ w4eq)) (Nat.m≤m+n WA (sB2 + Fin.toℕ i)))
                     (subst (Nat._< WA + WB) (sym (w4ℕ ■ w4eq)) (Nat.+-monoʳ-< WA i<WB))
                 ■ cong (Nat._∸ WA) (w4ℕ ■ w4eq) ■ Nat.m+n∸m≡n WA (sB2 + Fin.toℕ i)
            rhsℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB2 (i ↑ˡ (2 + (sA2 + (sA1 + (2 + n)))))) ≡ sB2 + Fin.toℕ i
            rhsℕ = toℕ-wk sB2 (i ↑ˡ (2 + (sA2 + (sA1 + (2 + n)))))
                 ■ cong (sB2 +_) (Fin.toℕ-↑ˡ i (2 + (sA2 + (sA1 + (2 + n)))))
    c2 : (Flags {sB1 + (2 + n)} B₂ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA1 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2 𝐔.⋯ₚ cT)
         ≡ Flags {sB1 + (2 + (sA2 + (sA1 + (2 + n))))} B₂
    c2 =
        𝐔.fusionₚ (Flags B₂ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) cT
      ■ 𝐔.fusionₚ (Flags B₂ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
      ■ 𝐔.fusionₚ (Flags B₂) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))
      ■ Flags-⋯-cong B₂ _ idₖ h2
      ■ ⋯ₚ-id (Flags B₂) (λ _ → refl)
      where
        h2 : ∀ (i : 𝔽 sB2) →
             (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA1 ·ₖ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT))) (i ↑ˡ (sB1 + (2 + n)))
             ≡ idₖ (i ↑ˡ (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
        h2 i = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
          where
            w0 = i ↑ˡ (sB1 + (2 + n))
            w1 = weaken* ⦃ Kᵣ ⦄ 2 w0
            w2 = weaken* ⦃ Kᵣ ⦄ sA1 w1
            w3 = weaken* ⦃ Kᵣ ⦄ sA2 w2
            w3ℕ : Fin.toℕ w3 ≡ sA2 + (sA1 + (2 + Fin.toℕ i))
            w3ℕ = toℕ-wk sA2 w2 ■ cong (sA2 +_) (toℕ-wk sA1 w1 ■ cong (sA1 +_)
                    (toℕ-wk 2 w0 ■ cong (2 +_) (Fin.toℕ-↑ˡ i (sB1 + (2 + n)))))
            w3eq : sA2 + (sA1 + (2 + Fin.toℕ i)) ≡ WA + Fin.toℕ i
            w3eq = solve 3 (λ a b k → a :+ (b :+ (con 2 :+ k)) := (a :+ (b :+ con 2)) :+ k) refl sA2 sA1 (Fin.toℕ i)
              where open +-*-Solver
            i<WB : Fin.toℕ i Nat.< WB
            i<WB = Nat.<-≤-trans (Fin.toℕ<n i) (Nat.m≤m+n sB2 (sB1 + 2))
            lhsℕ : Fin.toℕ (cT w3) ≡ Fin.toℕ i
            lhsℕ = cleanTℕ-mid sB1 sB2 sA1 sA2 w3
                     (subst (WA Nat.≤_) (sym (w3ℕ ■ w3eq)) (Nat.m≤m+n WA (Fin.toℕ i)))
                     (subst (Nat._< WA + WB) (sym (w3ℕ ■ w3eq)) (Nat.+-monoʳ-< WA i<WB))
                 ■ cong (Nat._∸ WA) (w3ℕ ■ w3eq) ■ Nat.m+n∸m≡n WA (Fin.toℕ i)
            rhsℕ : Fin.toℕ (i ↑ˡ (sB1 + (2 + (sA2 + (sA1 + (2 + n)))))) ≡ Fin.toℕ i
            rhsℕ = Fin.toℕ-↑ˡ i (sB1 + (2 + (sA2 + (sA1 + (2 + n)))))
    c3 : (Flags {2 + (sB2 + (sB1 + (2 + n)))} A₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2 𝐔.⋯ₚ cT)
         ≡ (Flags {2 + n} A₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB1 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2)
    c3 =
        𝐔.fusionₚ (Flags A₁) (weaken* ⦃ Kᵣ ⦄ sA2) cT
      ■ Flags-⋯-cong A₁ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT)
                        (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2))) h3
      ■ sym ( 𝐔.fusionₚ (Flags A₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2)
            ■ 𝐔.fusionₚ (Flags A₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
            ■ 𝐔.fusionₚ (Flags A₁) (weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)) )
      where
        h3 : ∀ (i : 𝔽 sA1) →
             (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ cT) (i ↑ˡ (2 + (sB2 + (sB1 + (2 + n)))))
             ≡ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2))) (i ↑ˡ (2 + n))
        h3 i = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
          where
            w0 = i ↑ˡ (2 + (sB2 + (sB1 + (2 + n))))
            w1 = weaken* ⦃ Kᵣ ⦄ sA2 w0
            w1ℕ : Fin.toℕ w1 ≡ sA2 + Fin.toℕ i
            w1ℕ = toℕ-wk sA2 w0 ■ cong (sA2 +_) (Fin.toℕ-↑ˡ i (2 + (sB2 + (sB1 + (2 + n)))))
            w1<WA : Fin.toℕ w1 Nat.< WA
            w1<WA = subst (Nat._< WA) (sym w1ℕ)
                      (Nat.+-monoʳ-< sA2 (Nat.<-≤-trans (Fin.toℕ<n i) (Nat.m≤m+n sA1 2)))
            lhsℕ : Fin.toℕ (cT w1) ≡ WB + (sA2 + Fin.toℕ i)
            lhsℕ = cleanTℕ-lt sB1 sB2 sA1 sA2 w1 w1<WA ■ cong (WB +_) w1ℕ
            v0 = i ↑ˡ (2 + n)
            v1 = weaken* ⦃ Kᵣ ⦄ sA2 v0
            v2 = weaken* ⦃ Kᵣ ⦄ 2 v1
            v3 = weaken* ⦃ Kᵣ ⦄ sB1 v2
            rhsℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB2 v3) ≡ WB + (sA2 + Fin.toℕ i)
            rhsℕ = toℕ-wk sB2 v3 ■ cong (sB2 +_) (toℕ-wk sB1 v2 ■ cong (sB1 +_) (toℕ-wk 2 v1 ■ cong (2 +_)
                     (toℕ-wk sA2 v0 ■ cong (sA2 +_) (Fin.toℕ-↑ˡ i (2 + n)))))
                 ■ solve 4 (λ b₂ b₁ a k → b₂ :+ (b₁ :+ (con 2 :+ (a :+ k))) := (b₂ :+ (b₁ :+ con 2)) :+ (a :+ k))
                          refl sB2 sB1 sA2 (Fin.toℕ i)
              where open +-*-Solver
    c4 : (Flags {sA1 + (2 + (sB2 + (sB1 + (2 + n))))} A₂ 𝐔.⋯ₚ cT)
         ≡ (Flags {sA1 + (2 + n)} A₂ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB1 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB2)
    c4 =
        Flags-⋯-cong A₂ cT (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)) h4
      ■ sym ( 𝐔.fusionₚ (Flags A₂ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2)
            ■ 𝐔.fusionₚ (Flags A₂) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) )
      where
        h4 : ∀ (i : 𝔽 sA2) →
             cT (i ↑ˡ (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
             ≡ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ sB1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)) (i ↑ˡ (sA1 + (2 + n)))
        h4 i = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
          where
            w0 = i ↑ˡ (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
            w0ℕ : Fin.toℕ w0 ≡ Fin.toℕ i
            w0ℕ = Fin.toℕ-↑ˡ i (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
            w0<WA : Fin.toℕ w0 Nat.< WA
            w0<WA = subst (Nat._< WA) (sym w0ℕ)
                      (Nat.<-≤-trans (Fin.toℕ<n i) (Nat.m≤m+n sA2 (sA1 + 2)))
            lhsℕ : Fin.toℕ (cT w0) ≡ WB + Fin.toℕ i
            lhsℕ = cleanTℕ-lt sB1 sB2 sA1 sA2 w0 w0<WA ■ cong (WB +_) w0ℕ
            v0 = i ↑ˡ (sA1 + (2 + n))
            v1 = weaken* ⦃ Kᵣ ⦄ 2 v0
            v2 = weaken* ⦃ Kᵣ ⦄ sB1 v1
            rhsℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB2 v2) ≡ WB + Fin.toℕ i
            rhsℕ = toℕ-wk sB2 v2 ■ cong (sB2 +_) (toℕ-wk sB1 v1 ■ cong (sB1 +_) (toℕ-wk 2 v0 ■ cong (2 +_) (Fin.toℕ-↑ˡ i (sA1 + (2 + n)))))
                 ■ solve 3 (λ b₂ b₁ k → b₂ :+ (b₁ :+ (con 2 :+ k)) := (b₂ :+ (b₁ :+ con 2)) :+ k) refl sB2 sB1 (Fin.toℕ i)
              where open +-*-Solver
    bodyReconcile =
        ≡→≋ (cong₂ 𝐔._∥_ (cong₂ 𝐔._∥_ c1 c2) (cong₂ 𝐔._∥_ c3 (cong₂ 𝐔._∥_ c4 leafeq)))
      ◅◅ 𝐔.∥-comm
      ◅◅ 𝐔.∥-cong 𝐔.∥-assoc ε
      ◅◅ Eq*.symmetric _ 𝐔.∥-assoc
      ◅◅ 𝐔.∥-cong ε (𝐔.∥-comm ◅◅ Eq*.symmetric _ 𝐔.∥-assoc)
      where
        leafeq : (U[ P ] (((λ i → canonₛ A₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sA2) ++ₛ
                            canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit))
                           ++ₛ (λ i → τB i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2))
                  𝐔.⋯ₚ cT)
                 ≡ U[ P′ ] (((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ sB2) ++ₛ
                             canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit))
                            ++ₛ (λ i → τA′ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2))
        leafeq = U-σ⋯ P ■ U-cong P (subEqLemma σ B₁ B₂ A₁ A₂) ■ sym (U-⋯ₚ P)
