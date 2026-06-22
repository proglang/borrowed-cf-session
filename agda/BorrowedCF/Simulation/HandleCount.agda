module BorrowedCF.Simulation.HandleCount where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; cast)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Processes.Typed
  using (BindGroup; structBinder; structBinderWk; structBinder+²)
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
open import BorrowedCF.Simulation.Confine using (count)
open import BorrowedCF.Simulation.StructDom
  using (count-cast; count-structBinder-lt; count-weaken*-lo)

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ)

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; +-assoc; +-identityʳ; +-suc; m≤m+n; <-≤-trans)


-- The lsplit handle 𝐒.inj 0F sits at flat position sum B₁.
toℕ-handle : ∀ (B₁ B₂ B : BindGroup) (b₁ : ℕ) {m} →
  let module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B in
  Fin.toℕ (𝐒.inj {suc b₁ ∷ []} {m} 0F) ≡ sum B₁
toℕ-handle B₁ B₂ B b₁ {m} =
  toℕ-↑ˡ _ m
  ■ toℕ-↑ˡ _ (sum B)
  ■ toℕ-cast (sym (sum-++ B₁ ((suc b₁ ∷ []) ++ B₂))) (sum B₁ ↑ʳ 0F)
  ■ toℕ-↑ʳ (sum B₁) 0F
  ■ +-identityʳ (sum B₁)

-- sum B₁ < sum (B₁ ++ suc b₁ ∷ B₂).
sumB₁<sumC₁ : ∀ (B₁ B₂ : BindGroup) (b₁ : ℕ) → sum B₁ < sum (B₁ ++ suc b₁ ∷ B₂)
sumB₁<sumC₁ B₁ B₂ b₁ =
  subst (sum B₁ <_) (sym (sum-++ B₁ (suc b₁ ∷ B₂)))
    (subst (suc (sum B₁) ≤_) (sym (+-suc (sum B₁) (b₁ + sum B₂)))
       (m≤m+n (suc (sum B₁)) (b₁ + sum B₂)))

-- The bind-context of the lsplit redex counts the handle exactly once.
count-handle-γinner : ∀ (B₁ B₂ B : BindGroup) (b₁ : ℕ) {m} (γ : Struct m) →
  let module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
      C₁ = B₁ ++ suc b₁ ∷ B₂ in
  count (𝐒.inj {suc b₁ ∷ []} {m} 0F)
    ( structBinder+² (sum B) C₁
    ∥ structBinderWk (sum C₁) B
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B)) ) ≡ 1
count-handle-γinner B₁ B₂ B b₁ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
    C₁ : BindGroup
    C₁ = B₁ ++ suc b₁ ∷ B₂
    handle : 𝔽 (sum C₁ + sum B + m)
    handle = 𝐒.inj {suc b₁ ∷ []} {m} 0F
    hℕ : Fin.toℕ handle ≡ sum B₁
    hℕ = toℕ-handle B₁ B₂ B b₁
    eqA : sum C₁ + (sum B + m) ≡ sum C₁ + sum B + m
    eqA = sym (+-assoc (sum C₁) (sum B) m)
    lt< : Fin.toℕ (Fin.cast (sym eqA) handle) < sum C₁
    lt< = subst (_< sum C₁) (sym (toℕ-cast (sym eqA) handle ■ hℕ)) (sumB₁<sumC₁ B₁ B₂ b₁)
    partA : count handle (structBinder+² (sum B) C₁) ≡ 1
    partA = count-cast eqA (structBinder C₁) handle
          ■ count-structBinder-lt C₁ (Fin.cast (sym eqA) handle) lt<
    partB : count handle (structBinderWk (sum C₁) B) ≡ 0
    partB = count-cast eqA (structBinder B 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁)) handle
          ■ count-weaken*-lo (sum C₁) (structBinder B) (Fin.cast (sym eqA) handle) lt<
    partC : count handle (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum B) γ handle
              (subst (_< sum C₁ + sum B) (sym hℕ)
                 (<-≤-trans (sumB₁<sumC₁ B₁ B₂ b₁) (m≤m+n (sum C₁) (sum B))))

-- The scope of the lsplit redex factors as sum B₁ + suc rest.
splitN-eq : ∀ (B₁ B₂ B : BindGroup) (b₁ : ℕ) {m} →
  sum B₁ + suc ((b₁ + sum B₂) + sum B + m) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m
splitN-eq B₁ B₂ B b₁ {m} rewrite sum-++ B₁ (suc b₁ ∷ B₂) =
  solve 5 (λ a b c d e →
    a :+ (con 1 :+ ((b :+ c) :+ d :+ e)) := (a :+ (con 1 :+ b :+ c)) :+ d :+ e)
    refl (sum B₁) b₁ (sum B₂) (sum B) m
  where open +-*-Solver

-- The thinning's missing point (cast of sum B₁ ↑ʳ zero) is the handle.
mp≡handle : ∀ (B₁ B₂ B : BindGroup) (b₁ : ℕ) {m} →
  let module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B in
  Fin.cast (splitN-eq B₁ B₂ B b₁ {m}) (sum B₁ ↑ʳ 0F) ≡ 𝐒.inj {suc b₁ ∷ []} {m} 0F
mp≡handle B₁ B₂ B b₁ {m} = Fin.toℕ-injective
  ( toℕ-cast (splitN-eq B₁ B₂ B b₁) (sum B₁ ↑ʳ 0F)
  ■ toℕ-↑ʳ (sum B₁) 0F
  ■ +-identityʳ (sum B₁)
  ■ sym (toℕ-handle B₁ B₂ B b₁) )
