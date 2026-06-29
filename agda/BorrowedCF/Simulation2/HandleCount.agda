-- Handle-counting for the lsplit / rsplit redex, adapted to the current
-- typed reduction's `SplitRenamings.inj` 3-part scope and the new
-- `structBinder`/TP-Res context shape.
--
-- The consumed handle of an lsplit/rsplit redex is `𝐒.inj {suc b₁ ∷ []} 0F`,
-- which sits at flat position `sum B₁` inside the binder scope
-- `sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m`.  The bind-context produced by
-- `inv-ν` (TP-Res) counts that handle exactly once.

module BorrowedCF.Simulation2.HandleCount where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; cast)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder)
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
open import BorrowedCF.Simulation2.Confine using (count)
open import BorrowedCF.Simulation2.StructDom
  using (count-cast; count-structBinder-lt; count-weaken*-lo
        ; count-⋯ᵣwkʳ-↑ˡ; count-⋯ᵣwkʳ-↑ʳ)

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ)

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; +-assoc; +-identityʳ; +-suc; m≤m+n; <-≤-trans)

-- The lsplit/rsplit handle 𝐒.inj 0F sits at flat position sum B₁.
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

-- The handle, after stripping the outer ` _ ↑ˡ m `, is ` (cast … (sum B₁ ↑ʳ 0F)) ↑ˡ sum B `.
private
  z₁ : ∀ (B₁ B₂ : BindGroup) (b₁ : ℕ) → 𝔽 (sum (B₁ ++ (suc b₁ ∷ []) ++ B₂))
  z₁ B₁ B₂ b₁ = Fin.cast (sym (sum-++ B₁ ((suc b₁ ∷ []) ++ B₂))) (sum B₁ ↑ʳ 0F)

  toℕ-z₁ : ∀ (B₁ B₂ : BindGroup) (b₁ : ℕ) → Fin.toℕ (z₁ B₁ B₂ b₁) ≡ sum B₁
  toℕ-z₁ B₁ B₂ b₁ =
    toℕ-cast (sym (sum-++ B₁ ((suc b₁ ∷ []) ++ B₂))) (sum B₁ ↑ʳ 0F)
    ■ toℕ-↑ʳ (sum B₁) 0F
    ■ +-identityʳ (sum B₁)

-- The bind-context produced by inv-ν of the lsplit/rsplit redex counts the
-- handle exactly once.  The context is the TP-Res shape with outer binder
-- B₁ := C₁ = B₁ ++ suc b₁ ∷ B₂ and outer binder B₂ := B.
count-handle-γinner : ∀ (B₁ B₂ B : BindGroup) (b₁ : ℕ) {m} (γ : Struct m) →
  let module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
      C₁ = B₁ ++ suc b₁ ∷ B₂ in
  count (𝐒.inj {suc b₁ ∷ []} {m} 0F)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder B  𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B)) ) ≡ 1
count-handle-γinner B₁ B₂ B b₁ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    module 𝐒 = 𝐓R.SplitRenamings B₁ B₂ B
    C₁ : BindGroup
    C₁ = B₁ ++ suc b₁ ∷ B₂
    zz : 𝔽 (sum C₁)
    zz = z₁ B₁ B₂ b₁
    toℕ-zz : Fin.toℕ zz ≡ sum B₁
    toℕ-zz = toℕ-z₁ B₁ B₂ b₁
    zz<C₁ : Fin.toℕ zz < sum C₁
    zz<C₁ = subst (_< sum C₁) (sym toℕ-zz) (sumB₁<sumC₁ B₁ B₂ b₁)
    -- 𝐒.inj {suc b₁ ∷ []} {m} 0F ≡ (zz ↑ˡ sum B) ↑ˡ m  definitionally (inj's definition).
    partA : count (𝐒.inj {suc b₁ ∷ []} {m} 0F) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B)) (zz ↑ˡ sum B)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum B) (structBinder C₁) zz
          ■ count-structBinder-lt C₁ zz zz<C₁
    partB : count (𝐒.inj {suc b₁ ∷ []} {m} 0F) (structBinder B 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder B 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (zz ↑ˡ sum B)
          ■ cong (count (zz ↑ˡ sum B)) (StructDom-wkˡ≡weaken* (sum C₁) (structBinder B))
          ■ count-weaken*-lo (sum C₁) (structBinder B) (zz ↑ˡ sum B) zz↑<C₁
      where
        zz↑<C₁ : Fin.toℕ (zz ↑ˡ sum B) < sum C₁
        zz↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ zz (sum B))) zz<C₁
        StructDom-wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        StructDom-wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count (𝐒.inj {suc b₁ ∷ []} {m} 0F) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum B) γ (𝐒.inj {suc b₁ ∷ []} {m} 0F)
              (subst (_< sum C₁ + sum B) (sym (toℕ-handle B₁ B₂ B b₁))
                 (<-≤-trans (sumB₁<sumC₁ B₁ B₂ b₁) (m≤m+n (sum C₁) (sum B))))

-- The scope of the lsplit/rsplit redex factors as sum B₁ + suc rest.
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
