-- Front-forcing confinement lemmas for the reverse RU-Drop reflection.
--
-- The drop handle is pinned by drop-image to the head block's LAST index
-- (fromℕ b₁).  For a well-typed IMPURE drop redex the consumed handle must be
-- at the FRONT (0F) of its block — nothing can be `before` it (com-xS-min).
-- Combined, front = last ⟹ the head block has width 1 (b₁ ≡ 0).
--
-- These are the drop analogs of ReverseConfine.count-handle-comᴸ and
-- RevComConfine.before-com-binderᴸ, over the 2-block first group
-- suc b₁ ∷ c ∷ [] (whose structBinder's first ∥-component is the head block
-- structNSeq (suc b₁), shifted by wkʳ (c + 0) rather than com's wkʳ 0).
module BorrowedCF.Simulation.RevDropConfine where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder; structNSeq)
open import BorrowedCF.Simulation.Confine using (count)
open import BorrowedCF.Simulation.StructDom
open import BorrowedCF.Simulation.BeforeOrder using (before; before-⋯ᵣ-inj; before-structNSeq)
open import BorrowedCF.Simulation.RevGrindC using (inj-wkʳ)
open import BorrowedCF.Simulation.RevComConfine using (bindCtx′-NoAcq)
open import BorrowedCF.Simulation.CloseVacuityProbe
  using (NoAcq; noAcq-;-fst; noAcq-≃; new-end⇒noAcq)
import BorrowedCF.Simulation.CloseVacuityProbe as CV
open import BorrowedCF.Processes.Typed
  using (BindCtx; BindCtx′; bindCtx′⇒chanCtx; cons-ret/acq)
open import BorrowedCF.Types using (New; _≃_; ≃-sym; _;_; end; ret)
open import BorrowedCF.Context using (Ctx)
open import Data.Fin.Base using (_↑ˡ_)
open import Data.Fin.Properties using (toℕ-↑ˡ)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (m≤m+n; <-≤-trans)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.List using (_∷_; [])
import BorrowedCF.Processes.Typed as TP

open Fin.Patterns

------------------------------------------------------------------------
-- count-handle-groupᴸ : a handle at position z of the FIRST bind group C₁
-- occurs exactly once in the (C₁ ∥ C₂ ∥ γ) binder context.  Generic in C₁, C₂
-- (verbatim ReverseConfine.count-handle-comᴸ, whose proof never used C₁ = b ∷ []).
------------------------------------------------------------------------

count-handle-groupᴸ : ∀ (C₁ C₂ : BindGroup) {m} (γ : Struct m) (z : 𝔽 (sum C₁)) →
  count ((z ↑ˡ (sum C₂)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ) ≡ 1
count-handle-groupᴸ C₁ C₂ {m} γ z = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    z<C₁ : Fin.toℕ z < sum C₁
    z<C₁ = Fin.toℕ<n z
    partA : count ((z ↑ˡ sum C₂) ↑ˡ m) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) (z ↑ˡ sum C₂)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum C₂) (structBinder C₁) z
          ■ count-structBinder-lt C₁ z z<C₁
    partB : count ((z ↑ˡ sum C₂) ↑ˡ m) (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (z ↑ˡ sum C₂)
          ■ cong (count (z ↑ˡ sum C₂)) (wkˡ≡weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-lo (sum C₁) (structBinder C₂) (z ↑ˡ sum C₂) z↑<C₁
      where
        z↑<C₁ : Fin.toℕ (z ↑ˡ sum C₂) < sum C₁
        z↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ z (sum C₂))) z<C₁
        wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count ((z ↑ˡ sum C₂) ↑ˡ m) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ ((z ↑ˡ sum C₂) ↑ˡ m) hdl<
      where
        hdl< : Fin.toℕ ((z ↑ˡ sum C₂) ↑ˡ m) < sum C₁ + sum C₂
        hdl< = subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ (z ↑ˡ sum C₂) m))
                 (subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ z (sum C₂)))
                   (<-≤-trans z<C₁ (m≤m+n (sum C₁) (sum C₂))))

------------------------------------------------------------------------
-- before-drop-binderᴸ : if the head-block handle position z₀ is NOT the front
-- (toℕ z₀ ≢ 0), then 0F is `before` it in the binder context.  Mirror of
-- RevComConfine.before-com-binderᴸ with the 2-block first group (extra wkʳ
-- (c + 0) peel and ↑ˡ (c + 0) shift for the head block structNSeq (suc b₁)).
------------------------------------------------------------------------

before-drop-binderᴸ : ∀ (b₁ c b₂ : ℕ) {m} (γ : Struct m) (z₀ : 𝔽 (suc b₁)) → Fin.toℕ z₀ ≢ 0 →
  let C₁ = suc b₁ ∷ c ∷ []
      C₂ = b₂ ∷ [] in
  before 0F (((z₀ ↑ˡ (c + 0)) ↑ˡ (b₂ + 0)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) )
before-drop-binderᴸ b₁ c b₂ {m} γ 0F       z₀≢ = ⊥-elim (z₀≢ refl)
before-drop-binderᴸ b₁ c b₂ {m} γ (suc z′) z₀≢ =
  inj₁ (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
         (structBinder (suc b₁ ∷ c ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (b₂ + 0))
         (before-⋯ᵣ-inj (𝐂S.wkʳ (b₂ + 0)) (inj-wkʳ (b₂ + 0))
           (structBinder (suc b₁ ∷ c ∷ []))
           (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ (c + 0)) (inj-wkʳ (c + 0)) (structNSeq (suc b₁))
                   (before-structNSeq b₁ z′))))))

------------------------------------------------------------------------
-- head-block-NoAcq : every channel of the HEAD block (a s₁ ; ret borrow of a
-- 2-block bind group) is NoAcq, hence non-mobile.  s₁ is a prefix of the
-- New-derived s ; end p, so NoAcq s₁ (noAcq-;-fst ∘ transport), and
-- NoAcq (s₁ ; ret) = NoAcq s₁ ; ret.  drop-go reconciles the full-context
-- lookup with this head-local one (as close-go does with lookupL).
------------------------------------------------------------------------

head-block-NoAcq : ∀ {s p s₁ s₂ b₁} {Γₕ : Ctx (suc b₁)} → New s
  → s₁ ; s₂ ≃ (s ; end p)
  → (headBC : BindCtx′ (s₁ ; ret) (suc b₁) Γₕ) (x₁ : 𝔽 (suc b₁))
  → NoAcq (proj₁ (bindCtx′⇒chanCtx headBC x₁))
head-block-NoAcq N s≃ headBC x₁ =
  bindCtx′-NoAcq
    (CV._;_ (noAcq-;-fst (noAcq-≃ (≃-sym s≃) (new-end⇒noAcq N))) CV.ret)
    headBC x₁
