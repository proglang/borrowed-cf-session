module BorrowedCF.Simulation.Support.RevGrindC where

-- Block-2 mirrors of the RevComConfine / ReverseConfine block-1 machinery,
-- needed to force the RU-Close R endpoint (`end ⁇`) handle to the block-2 head.
--
--   before-com-binderᴿ : the ;-order fact — a non-head block-2 handle has the
--     block-2 head ;-before it in the binder (structNSeq is a ;-chain).
--   count-handle-comᴿ  : the cross-thread linearity — any block-2 handle counts
--     exactly once in the inner binder of ν (b₁ ∷ []) (b₂ ∷ []) _.
--   inj-wkˡ            : injectivity of the left-weakening renaming.
--   chanCx-¬Unr        : channels are never Unr (linear-skip calculus).
--
-- These are the block-2 analogues of RevComConfine.before-com-binderᴸ /
-- ReverseConfine.count-handle-comᴸ and feed the same generic RevComConfine.com-xS-min
-- squeeze (end ⁇ is 𝕀, so its frame stack is LeftPat; the redex arg is a bare
-- handle, so ¬before is trivial).

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; Ctx)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder; structNSeq)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.StructDom
  using (count-structBinder-lt; count-weaken*-lo; count-weaken*-shift; count-⋯ᵣwkʳ-↑ˡ; count-⋯ᵣwkʳ-↑ʳ)
open import BorrowedCF.Simulation.Support.BeforeOrder
  using (before; before-structNSeq; before-⋯ᵣ-inj)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import BorrowedCF.Types using (Unr; ⟨_⟩)

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; ↑ˡ-injective; ↑ʳ-injective)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_; [])

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; s≤s; z≤n; +-identityʳ; m≤m+n; m≤n+m; <-≤-trans; +-suc; +-monoʳ-<)

-- ── channels are never Unr ──
chanCx-¬Unr : ∀ {N} {Γ : Ctx N} → ChanCx Γ → (x : 𝔽 N) → ¬ Unr (Γ x)
chanCx-¬Unr Γ-S x u with Γ-S x
... | s , eq with subst Unr eq u
...   | ⟨ () ⟩

-- ── injectivity of the two weakening renamings ──
inj-wkˡ : ∀ {n} k → 𝐂S.Inj (𝐂S.wkˡ {n = n} k)
inj-wkˡ k {x} {y} eq = ↑ʳ-injective k x y eq

inj-wkʳ : ∀ {n} k → 𝐂S.Inj (𝐂S.wkʳ {n = n} k)
inj-wkʳ k {x} {y} eq = ↑ˡ-injective k x y eq

-- ── the block-2 ;-order fact (mirror of before-com-binderᴸ) ──
-- A non-head block-2 handle (w₀ = suc w′) has the block-2 head ;-before it.
before-com-binderᴿ : ∀ (b₁ b₂ : ℕ) {m} (γ : Struct m) (w₀ : 𝔽 (suc b₂)) → Fin.toℕ w₀ ≢ 0 →
  let C₁ = b₁ ∷ []
      C₂ = suc b₂ ∷ [] in
  before ((𝐂S.wkˡ (sum C₁) ((Fin.zero {b₂}) ↑ˡ 0)) ↑ˡ m)
         ((𝐂S.wkˡ (sum C₁) (w₀ ↑ˡ 0)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) )
before-com-binderᴿ b₁ b₂ {m} γ 0F       w₀≢ = ⊥-elim (w₀≢ refl)
before-com-binderᴿ b₁ b₂ {m} γ (suc w′) w₀≢ =
  inj₁ (inj₂ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
         (structBinder (suc b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (b₁ + 0))
         (before-⋯ᵣ-inj (𝐂S.wkˡ (b₁ + 0)) (inj-wkˡ (b₁ + 0))
           (structBinder (suc b₂ ∷ []))
           (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ 0) (inj-wkʳ 0) (structNSeq (suc b₂))
                   (before-structNSeq b₂ w′))))))

-- ── the block-2 cross-thread linearity (mirror of count-handle-comᴸ) ──
count-handle-comᴿ : ∀ (b₁ b₂ : ℕ) {m} (γ : Struct m) (w : 𝔽 (b₂ + 0)) →
  let C₁ = b₁ ∷ []
      C₂ = b₂ ∷ [] in
  count ((sum C₁ ↑ʳ w) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ) ≡ 1
count-handle-comᴿ b₁ b₂ {m} γ w = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = b₁ ∷ []
    C₂ : BindGroup
    C₂ = b₂ ∷ []
    hdl : 𝔽 (sum C₁ + sum C₂)
    hdl = sum C₁ ↑ʳ w
    w<C₂ : Fin.toℕ w < sum C₂
    w<C₂ = Fin.toℕ<n w
    partA : count (hdl ↑ˡ m) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) hdl
          ■ count-⋯ᵣwkʳ-↑ʳ (sum C₂) (structBinder C₁) w
    partB : count (hdl ↑ˡ m) (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) hdl
          ■ cong (count hdl) (wkˡ≡weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-shift (sum C₁) (structBinder C₂) w
          ■ count-structBinder-lt C₂ w w<C₂
      where
        wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count (hdl ↑ˡ m) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ (hdl ↑ˡ m) hdl<
      where
        hdl< : Fin.toℕ (hdl ↑ˡ m) < sum C₁ + sum C₂
        hdl< = subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ hdl m))
                 (subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ʳ (sum C₁) w))
                   (+-monoʳ-< (sum C₁) w<C₂))
