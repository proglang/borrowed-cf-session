------------------------------------------------------------------------
-- Preservation, case R-LSplit.
--
-- STATUS: the binder-context half of the case is complete (`lsplit-binder`
-- below); the premise-free `pres-LSplit` lives in `LSplit/Total.agda` (P3c).
--
-- `lsplit-binder` inverts the typing of the R-LSplit redex and returns the
-- reshuffled first binder context together with its `BindCtx` derivation and
-- the types of the two handles the rule introduces.  That is exactly the
-- premise `C` of `TP-Res` for the right-hand side of the rule.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Terms
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Splits.Chain
open import BorrowedCF.Safety.Preservation.Splits.Group
open import BorrowedCF.Safety.Preservation.Splits.Redex
open import BorrowedCF.Safety.Preservation.Splits.Shift
open import BorrowedCF.Safety.Preservation.Splits.Struct

open import BorrowedCF.Safety.Preservation.Splits.Confine
open import BorrowedCF.Simulation.Support.FrameRename using (⋯ᶠ*-fuse)
open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ
  using (dlwkq; dlwkq-lo; dlwkq-hi; P1q; P2q; P3q)

open Nat.Variables
open Fin.Patterns

-- `⊢ᴮ-lsplit` restated for the width shape the reduction rule uses.
⊢ᴮ-lsplit′ : ∀ (B₁ : BindGroup) (q b : ℕ) {B₂} →
  ⊢ᴮ (B₁ ++ (q + suc b) ∷ B₂) → ⊢ᴮ (B₁ ++ (q + suc (suc b)) ∷ B₂)
⊢ᴮ-lsplit′ B₁ q b {B₂} x =
  subst (λ w → ⊢ᴮ (B₁ ++ w ∷ B₂)) (Nat.+-assoc q 2 b)
    (⊢ᴮ-lsplit B₁ q {b}
      (subst (λ w → ⊢ᴮ (B₁ ++ w ∷ B₂)) (sym (Nat.+-assoc q 1 b)) x))

-- The variable the rule consumes sits at flat position `sum B₁ + q` of the
-- FIRST binder context.
atk-lookup : ∀ (B₁ B₂ B : BindGroup) {q b₁ m}
  (Γ₁ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))) (Γ₂ : Ctx (sum B)) (Γ : Ctx m) →
  ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    ≡ Γ₁ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                    (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ =
  V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁ Γ₂ _

lsplit-binder : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`lsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Σ[ s₀ ∈ 𝕊 0 ] Σ[ pol ∈ Pol ] Σ[ t₁ ∈ 𝕊 0 ] Σ[ t₂ ∈ 𝕊 0 ]
    Σ[ Γ₁′ ∈ Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) ]
      New s₀
      × ⊢ᴮ (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
      × BindCtx (s₀ ; end pol) (B₁ ++ (q + suc (suc b₁)) ∷ B₂) Γ₁′
      × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))
                        (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)) ≡ ⟨ t₁ ⟩)
      × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))
                        (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)) ≡ ⟨ t₂ ⟩)
lsplit-binder {m} {Γ} {γ} {B₁} {B₂} {B} {q} {b₁} {s} {E} ⊢P
  with Γ₁ , Γ₂ , s₀ , pol , N , ⊢B₁ , ⊢B , C₁ , C₂ , ⊢body ← inv-ν ⊢P
  with α , β , αβ≼ , ⊢thread , ⊢Ppar ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eqT , ϵ≤ , ⊢E , ⊢app
     ← ⊢[]*⁻¹ E _ (inv-⟪⟫ ⊢thread)
  with a , γc , γx , _ , ≤γ″ , ≤ₐ , refl , ⊢const , ⊢var
     ← inv-·-unr ⊢app (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , eq₁ `→ eq₂ , []≤ , `lsplit t₁ t₂ ¬S₁ ¬S₂ ← inv-K ⊢const
  with T≃ , x≤ ← inv-` ⊢var
  with t , eqpos ← chanCx-lookup (bindCtx⇒chanCtx C₁) _
  with ⟨ teq ⟩ ← subst (⟨ t₁ ; t₂ ⟩ ≃_) (atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos) (≃-trans eq₁ T≃)
  with Γ₁′ , C₁′ , spec₁ , spec₂ , _ ← lsplit-bindCtx B₁ ¬S₁ ¬S₂ (≃-sym teq) eqpos C₁
  = s₀ , pol , t₁ , t₂ , Γ₁′ , N , ⊢ᴮ-lsplit′ B₁ q b₁ ⊢B₁ , C₁′ , spec₁ , spec₂

------------------------------------------------------------------------
-- The struct substitution that expands the consumed handle into the two
-- new ones and shifts every other variable along `lwk`.

θL : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) →
  (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m) 𝐂.→ₛ
  (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B + m)
θL B₁ B₂ B q b₁ m z with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes _ = (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
            ; (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F))
... | no  _ = ` SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} z

θL-h : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) →
  θL B₁ B₂ B q b₁ m (SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F))
    ≡ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
    ; (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F))
θL-h B₁ B₂ B q b₁ m
  with SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
     Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

θL-≢ : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) z →
  z ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
  θL B₁ B₂ B q b₁ m z ≡ ` SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} z
θL-≢ B₁ B₂ B q b₁ m z ne
  with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

-- The second new handle sits one slot after the consumed one.
toℕ-dh₂ : ∀ (B₁ B₂ : BindGroup) (q b₁ : ℕ) →
  Fin.toℕ (Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))
                    (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)))
    ≡ suc (sum B₁ + q)
toℕ-dh₂ B₁ B₂ q b₁ =
    Fin.toℕ-cast _ (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
  ■ Fin.toℕ-↑ʳ (sum B₁) ((q ↑ʳ 1F) ↑ˡ sum B₂)
  ■ cong (sum B₁ +_) (Fin.toℕ-↑ˡ (q ↑ʳ (Fin.suc Fin.zero)) (sum B₂)
                     ■ Fin.toℕ-↑ʳ q (Fin.suc Fin.zero)
                     ■ Nat.+-comm q 1)
  ■ Nat.+-suc (sum B₁) q

-- The ambient part of the ν-binder structure.
γbigL : ∀ (Bl B : BindGroup) {m} (γ : Struct m) → Struct (sum Bl + sum B + m)
γbigL Bl B {m} γ =
    (structBinder Bl 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m)
  ∥ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ (sum Bl) 𝐂.⋯ᵣ 𝐂.wkʳ m)
  ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum Bl + sum B))

------------------------------------------------------------------------
-- The ν-binder structure of the right-hand side dominates the image of
-- the left-hand one under θL.

γbig-lsplit : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} {Γ : Ctx m} {γ : Struct m}
  (Γ₁′ : Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂))) (Γ₂ : Ctx (sum B)) →
  ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
    γbigL (B₁ ++ (q + suc b₁) ∷ B₂) B γ 𝐂.⋯ₛ θL B₁ B₂ B q b₁ m
      ≼ γbigL (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B γ
γbig-lsplit B₁ B₂ B {q} {b₁} {m} {Γ} {γ} Γ₁′ Γ₂ =
  ≼-cong-∥ (≼-cong-∥ part1 (≼-refl (≈-reflexive part2))) (≼-refl (≈-reflexive part3))
  where
    W  = sum (B₁ ++ (q + suc b₁) ∷ B₂)
    W′ = sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
    θ  = θL B₁ B₂ B q b₁ m
    dh₀ : 𝔽 W
    dh₀ = Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    tℕι : ∀ (j : 𝔽 W) → Fin.toℕ ((j ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ j
    tℕι j = Fin.toℕ-↑ˡ (j ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ j (sum B)
    tℕatk : Fin.toℕ (SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F))
              ≡ sum B₁ + q
    tℕatk = tℕι dh₀ ■ toℕ-dh B₁ B₂ q b₁
    neι : ∀ (j : 𝔽 W) → Fin.toℕ j ≢ sum B₁ + q →
          (j ↑ˡ sum B) ↑ˡ m ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    neι j nj e = nj (sym (tℕι j) ■ cong Fin.toℕ e ■ tℕatk)
    lo : ∀ j j′ → Fin.toℕ j Nat.< sum B₁ + q → Fin.toℕ j′ ≡ Fin.toℕ j →
         θ ((j ↑ˡ sum B) ↑ˡ m) ≡ ` ((j′ ↑ˡ sum B) ↑ˡ m)
    lo j j′ lt e =
        θL-≢ B₁ B₂ B q b₁ m _ (neι j (λ x → Nat.<-irrefl x lt))
      ■ cong `_ (P1q B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective
               (dlwkq-lo B₁ q b₁ B₂ j
                 (subst (Fin.toℕ j Nat.<_) (Nat.+-comm 1 (sum B₁ + q))
                        (Nat.<-trans lt (Nat.n<1+n _)))
               ■ sym e))
    at : ∀ j j₁ j₂ → Fin.toℕ j ≡ sum B₁ + q → Fin.toℕ j₁ ≡ sum B₁ + q →
         Fin.toℕ j₂ ≡ suc (sum B₁ + q) →
         θ ((j ↑ˡ sum B) ↑ˡ m)
           ≡ ((` ((j₁ ↑ˡ sum B) ↑ˡ m)) ; (` ((j₂ ↑ˡ sum B) ↑ˡ m)))
    at j j₁ j₂ e e₁ e₂ =
        cong (λ w → θ ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective (e ■ sym (toℕ-dh B₁ B₂ q b₁)))
      ■ θL-h B₁ B₂ B q b₁ m
      ■ cong₂ (λ a c → (` ((a ↑ˡ sum B) ↑ˡ m)) ; (` ((c ↑ˡ sum B) ↑ˡ m)))
              (sym (Fin.toℕ-injective (e₁ ■ sym (toℕ-dh B₁ B₂ q (suc b₁)))))
              (sym (Fin.toℕ-injective (e₂ ■ sym (toℕ-dh₂ B₁ B₂ q b₁))))
    hi : ∀ j j′ → sum B₁ + q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
         θ ((j ↑ˡ sum B) ↑ˡ m) ≡ ` ((j′ ↑ˡ sum B) ↑ˡ m)
    hi j j′ gt e =
        θL-≢ B₁ B₂ B q b₁ m _ (neι j (λ x → Nat.<-irrefl (sym x) gt))
      ■ cong `_ (P1q B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective
               (dlwkq-hi B₁ q b₁ B₂ j
                 (subst (Nat._≤ Fin.toℕ j) (Nat.+-comm 1 (sum B₁ + q)) gt)
               ■ sym e))
    eqA : (structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
            ≡ structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ₛ (λ d → θ ((d ↑ˡ sum B) ↑ˡ m))
    eqA = cong (λ z → z 𝐂.⋯ₛ θ)
               (⋯ᵣᵣ (structBinder (B₁ ++ (q + suc b₁) ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m))
        ■ ⋯ᵣₛ (structBinder (B₁ ++ (q + suc b₁) ∷ B₂)) (λ d → (d ↑ˡ sum B) ↑ˡ m) θ
    eqB : structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m
            ≡ structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂) 𝐂.⋯ₛ (λ d → ` ((d ↑ˡ sum B) ↑ˡ m))
    eqB = ⋯ᵣᵣ (structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m)
        ■ ⋯ᵣ⇒ₛ (structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) (λ d → (d ↑ˡ sum B) ↑ˡ m)
    part1 : ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
            (structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
              ≼ (structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part1 = ≼-refl (≈-trans (≈-reflexive eqA)
                   (≈-trans (sb-lsplit B₁ q b₁ B₂ refl _ _ lo at hi)
                            (≈-reflexive (sym eqB))))
    pw₂ : ∀ (w : 𝔽 (sum B)) → θ ((W ↑ʳ w) ↑ˡ m) ≡ ` ((W′ ↑ʳ w) ↑ˡ m)
    pw₂ w = θL-≢ B₁ B₂ B q b₁ m _ (λ e → Fin.↑ˡ≢↑ʳ (sym (Fin.↑ˡ-injective m _ _ e)))
          ■ cong `_ (P2q B₁ B₂ B w)
    part2 : (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
              ≡ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W′ 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part2 = cong (λ z → z 𝐂.⋯ₛ θ) (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W) (𝐂.wkʳ m))
          ■ ⋯ᵣₛ (structBinder B) (λ w → (W ↑ʳ w) ↑ˡ m) θ
          ■ ⋯ₛ-cong (structBinder B) pw₂
          ■ sym (⋯ᵣ⇒ₛ (structBinder B) (λ w → (W′ ↑ʳ w) ↑ˡ m))
          ■ sym (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W′) (𝐂.wkʳ m))
    pw₃ : ∀ (u : 𝔽 m) → θ ((W + sum B) ↑ʳ u) ≡ ` ((W′ + sum B) ↑ʳ u)
    pw₃ u = θL-≢ B₁ B₂ B q b₁ m _ (λ e → Fin.↑ˡ≢↑ʳ (sym e))
          ■ cong `_ (P3q B₁ B₂ B u)
    part3 : (γ 𝐂.⋯ᵣ 𝐂.weaken* (W + sum B)) 𝐂.⋯ₛ θ ≡ (γ 𝐂.⋯ᵣ 𝐂.weaken* (W′ + sum B))
    part3 = cong (λ z → z 𝐂.⋯ₛ θ) (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W + sum B)))
          ■ ⋯ᵣₛ γ (𝐂.wkˡ (W + sum B)) θ
          ■ ⋯ₛ-cong γ pw₃
          ■ sym (⋯ᵣ⇒ₛ γ (𝐂.wkˡ (W′ + sum B)))
          ■ sym (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W′ + sum B)))

------------------------------------------------------------------------
-- θL is a structure-preserving map of the two ν-body contexts.
--
-- The ONLY place where this can fail is the consumed handle: after an
-- l-split neither half is `Mobile` any more (see Splits-STATUS.md), so we
-- ask that the left half is not acq-headed, which rules the case out.

¬unr-handle : ∀ {s : 𝕊 0} → ¬ Unr ⟨ s ⟩
¬unr-handle ⟨ () ⟩

-- The exact side condition: the consumed handle must not be `Mobile`.
-- Its type is `⟨ t ⟩` with `t ≃ s ; t₂` for the rule's own `s`, so the
-- condition can be stated over `s` alone.
mob-lsplit-absurd : ∀ {t t₁ t₂ : 𝕊 0} → t ≃ t₁ ; t₂ →
  (∀ (u : 𝕊 0) → ¬ Mobile ⟨ t₁ ; u ⟩) → ¬ Mobile ⟨ t ⟩
mob-lsplit-absurd {t₂ = t₂} teq ¬mob mo = ¬mob t₂ (mobile-≃ ⟨ teq ⟩ mo)

θL-⇒ : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} {t t₁ t₂ : 𝕊 0} {Γ : Ctx m}
  (Γ₁  : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)))
  (Γ₂  : Ctx (sum B)) →
  Agree (sum B₁ + q) Γ₁ Γ₁′ →
  (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) ≡ ⟨ t ⟩) →
  t ≃ t₁ ; t₂ → (∀ (u : 𝕊 0) → ¬ Mobile ⟨ t₁ ; u ⟩) →
  𝐂._∶_⇒_ (θL B₁ B₂ B q b₁ m) ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
θL-⇒ B₁ B₂ B {q} {b₁} {m} {Γ = Γ} Γ₁ Γ₁′ Γ₂ Ag eqh teq ¬mob z =
  case z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) of λ where
    (yes p) →
      subst Mot (sym (cong (θL B₁ B₂ B q b₁ m) p ■ θL-h B₁ B₂ B q b₁ m))
        ( (λ u  → ⊥-elim (¬unr-handle (subst Unr (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) u)))
        , (λ mo → ⊥-elim (mob-lsplit-absurd teq ¬mob
                            (subst Mobile (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) mo))) )
    (no ne) →
      subst Mot (sym (θL-≢ B₁ B₂ B q b₁ m z ne))
        ( (λ u  → ` subst Unr    (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) u)
        , (λ mo → ` subst Mobile (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) mo) )
  where
    Mot : Struct (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B + m) → Set
    Mot w = (Unr    (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → UnrCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)
          × (Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → MobCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)

------------------------------------------------------------------------
-- Preservation for R-LSplit.
--
-- EXTRA PREMISE `¬acq`: the left half of the split must not be
-- acq-headed.  It is used only to rule out `Mobile` on the consumed
-- handle; see the discussion in Splits-STATUS.md.

pres-LSplit-immobile : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  ChanCx Γ →
  (¬mob : ∀ (u : 𝕊 0) → ¬ Mobile ⟨ s ; u ⟩) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`lsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
             (⟪ (E ⋯ᶠ* SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m})
                  [ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
                  ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F)) ]* ⟫
               ∥ (P ⋯ₚ SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m}))
pres-LSplit-immobile {m} {Γ} {γ} {B₁} {B₂} {B} {q} {b₁} {s} {E} {P} Γ-S ¬mob ⊢P
  with k , ρ⁻ , skp , inj⁻ , E₀ , refl , P₀ , refl ← lsplit-confine′ Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with Γ₁ , Γ₂ , s₀ , pol , Nw , ⊢B₁ , ⊢B , C₁ , C₂ , ⊢body ← inv-ν ⊢P
  with α , β , αβ≼ , ⊢thread , ⊢Ppar ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eqT , ϵ≤ , ⊢E , ⊢app
     ← ⊢[]*⁻¹ (E₀ ⋯ᶠ* ρ⁻) _ (inv-⟪⟫ ⊢thread)
  with a , γc , γx , _ , ≤γ″ , ≤ₐ , refl , ⊢const , ⊢var
     ← inv-·-unr ⊢app (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , eq₁ `→ eq₂ , []≤ , `lsplit t₁ t₂ ¬S₁ ¬S₂ ← inv-K ⊢const
  with T≃ , x≤ ← inv-` ⊢var
  with t , eqpos ← chanCx-lookup (bindCtx⇒chanCtx C₁) _
  with ⟨ teq ⟩ ← subst (⟨ t₁ ; t₂ ⟩ ≃_) (atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos) (≃-trans eq₁ T≃)
  with Γ₁′ , C₁′ , spec₁ , spec₂ , Ag ← lsplit-bindCtx B₁ ¬S₁ ¬S₂ (≃-sym teq) eqpos C₁
  = let
      lwk = SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m}
      θ   = θL B₁ B₂ B q b₁ m
      Γsm = V.tabulate (λ y → ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ ρ⁻ y)

      ⊢ρ⁻ : ρ⁻ ⊢ Γsm ⇒ᵣ ((Γ₁ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁻ = ⊢ren (λ y → V.lookup∘tabulate _ y)

      ⊢ρ⁺ : (λ y → lwk (ρ⁻ y)) ⊢ Γsm ⇒ᵣ ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁺ = ⊢ren (λ y → V.lookup∘tabulate _ y
                      ■ sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag (ρ⁻ y) (skp y)))

      pwρ : ∀ y → θ (ρ⁻ y) ≡ ` (lwk (ρ⁻ y))
      pwρ y = θL-≢ B₁ B₂ B q b₁ m (ρ⁻ y) (skp y)

      eqh : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
              ≡ ⟨ t ⟩
      eqh = atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos
    in
    let 𝒫₀ , ≤𝒫 , ⊢E₀ = ⊢E    ⊢⋯ᶠ*⁻¹ ⊢ρ⁻ / inj⁻
        β₀ , ≤β , ⊢P₀ = ⊢Ppar ⊢⋯ₚ⁻¹ ⊢ρ⁻ / inj⁻
    in
    let
      lk₁ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F) ≡ ⟨ t₁ ⟩
      lk₁ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₁

      lk₂ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F) ≡ ⟨ t₂ ⟩
      lk₂ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₂

      `h≼γ′ = ≼-trans (≼-refl (≈-sym (join-unitʳ (Arr.dir a))))
                      (≼-trans (≼-join (Arr.dir a) x≤ []≤) ≤γ″)

      old≼ = ≼-trans (≼-cong-∥ (≼-trans (≤𝒫 `h≼γ′) ≤γ′) ≤β) αβ≼

      Deq = cong₂ _∥_
              ([-]-dist-⋯ (𝒫₀ ⋯𝓅 (`_ ∘ ρ⁻)) (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) θ
                ■ cong₂ (λ 𝒬 v → 𝒬 [ v ]𝓅) (𝓅∘ 𝒫₀ ρ⁻ θ (λ y → lwk (ρ⁻ y)) pwρ)
                                            (θL-h B₁ B₂ B q b₁ m))
              (σ∘ β₀ ρ⁻ θ (λ y → lwk (ρ⁻ y)) pwρ)

      ineq = ≼-trans (≼-refl (≈-reflexive (sym Deq)))
                     (≼-trans (𝐂.≼-⋯ (θL-⇒ B₁ B₂ B Γ₁ Γ₁′ Γ₂ Ag eqh (≃-sym teq) ¬mob) old≼)
                              (γbig-lsplit B₁ B₂ B {γ = γ} Γ₁′ Γ₂))
    in
    subst₂ (λ F Q → Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
              (⟪ F [ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
                   ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F)) ]* ⟫ ∥ Q))
      (sym (⋯ᶠ*-fuse E₀ ρ⁻ lwk)) (sym (fusionₚ P₀ ρ⁻ lwk))
      (TP-Res Nw pol (⊢ᴮ-lsplit′ B₁ q b₁ ⊢B₁) ⊢B C₁′ C₂
        (TP-Weaken ineq
          (TP-Par
            (TP-Expr (T-Conv eqT ϵ≤
              ⊢⟨ ⊢E₀ ⊢⋯ᶠ* ⊢ρ⁺
                 [ T-Conv eq₂ ℙ≤ϵ (T-Pair seq seq (T-Var _ lk₁) (T-Var _ lk₂)) ]*⟩))
            (⊢P₀ ⊢⋯ₚ ⊢ρ⁺))))
