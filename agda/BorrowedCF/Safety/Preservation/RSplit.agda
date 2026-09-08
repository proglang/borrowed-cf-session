------------------------------------------------------------------------
-- Preservation, case R-RSplit.
--
-- STATUS: the binder-context half of the case is complete (`rsplit-binder`
-- below); the full `pres-RSplit` is not yet assembled, see Splits-STATUS.md.
--
-- `rsplit-binder` inverts the typing of the R-RSplit redex and returns the
-- reshuffled first binder context (one group MORE than before) together with
-- its `BindCtx` derivation and the types of the two handles the rule
-- introduces.  That is exactly the premise `C` of `TP-Res` for the
-- right-hand side of the rule.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.RSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Relation.Unary.All as Allᴸ using ([]; _∷_) renaming (All to Allᴸ)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomCons using (acq-;-split)

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Splits.Chain
open import BorrowedCF.Safety.Preservation.Splits.Group
open import BorrowedCF.Safety.Preservation.Splits.Redex
open import BorrowedCF.Safety.Preservation.Splits.Shift
open import BorrowedCF.Safety.Preservation.Splits.Struct
open import BorrowedCF.Safety.Preservation.Splits.Confine
open import BorrowedCF.Safety.Preservation.LSplit using (γbigL; ¬unr-handle)

open import BorrowedCF.Simulation.Support.FrameRename using (⋯ᶠ*-fuse)
open import BorrowedCF.Simulation.Support.Theorems.SplitsRQ
  using (drwkq; drwkq-lo; drwkq-hi; P1rq; P2rq; P3rq)

open Nat.Variables
open Fin.Patterns

-- `⊢ᴮ` for the width shape the reduction rule uses: the group q + suc b splits
-- into the two groups (q + 1) and suc b, and the NEW group is non-empty.
private
  nz-suc : ∀ (q : ℕ) → Nat.NonZero (q + 1)
  nz-suc q = Nat.>-nonZero (subst (0 Nat.<_) (Nat.+-comm 1 q) Nat.z<s)

  goᴮ : ∀ (B : BindGroup) (q b : ℕ) {B₂} →
    Allᴸ Nat.NonZero (B ++ (q + suc b) ∷ B₂) →
    Allᴸ Nat.NonZero (B ++ (q + 1) ∷ suc b ∷ B₂)
  goᴮ []      q b (p ∷ ps) = nz-suc q ∷ _ ∷ ps
  goᴮ (x ∷ B) q b (p ∷ ps) = p ∷ goᴮ B q b ps

⊢ᴮ-rsplit′ : ∀ (B₁ : BindGroup) (q b : ℕ) {B₂} →
  ⊢ᴮ (B₁ ++ (q + suc b) ∷ B₂) → ⊢ᴮ (B₁ ++ (q + 1) ∷ suc b ∷ B₂)
⊢ᴮ-rsplit′ []       q b x = _ ∷ x
⊢ᴮ-rsplit′ (_ ∷ B₁) q b x = goᴮ B₁ q b x

-- The variable the rule consumes sits at flat position `sum B₁ + q` of the
-- FIRST binder context.
atk-lookup : ∀ (B₁ B₂ B : BindGroup) {q b₁ m}
  (Γ₁ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))) (Γ₂ : Ctx (sum B)) (Γ : Ctx m) →
  ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    ≡ Γ₁ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                    (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ =
  V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁ Γ₂ _

rsplit-binder : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`rsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Σ[ s₀ ∈ 𝕊 0 ] Σ[ pol ∈ Pol ] Σ[ t₁ ∈ 𝕊 0 ] Σ[ t₂ ∈ 𝕊 0 ]
    Σ[ Γ₁′ ∈ Ctx (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) ]
      New s₀
      × ⊢ᴮ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)
      × BindCtx (s₀ ; end pol) (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) Γ₁′
      × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                        (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ≡ (⟨ t₁ ; ret ⟩))
      × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                        (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F)) ≡ (⟨ acq ; t₂ ⟩))
rsplit-binder {m} {Γ} {γ} {B₁} {B₂} {B} {q} {b₁} {s} {E} ⊢P
  with Γ₁ , Γ₂ , s₀ , pol , N , ⊢B₁ , ⊢B , C₁ , C₂ , ⊢body ← inv-ν ⊢P
  with α , β , αβ≼ , ⊢thread , ⊢Ppar ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eqT , ϵ≤ , ⊢E , ⊢app
     ← ⊢[]*⁻¹ E _ (inv-⟪⟫ ⊢thread)
  with a , γc , γx , _ , ≤γ″ , ≤ₐ , refl , ⊢const , ⊢var
     ← inv-·-unr ⊢app (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , eq₁ `→ eq₂ , []≤ , `rsplit t₁ t₂ ¬S₁ ¬S₂ ← inv-K ⊢const
  with T≃ , x≤ ← inv-` ⊢var
  with t , eqpos ← chanCx-lookup (bindCtx⇒chanCtx C₁) _
  with ⟨ teq ⟩ ← subst ((⟨ t₁ ; t₂ ⟩) ≃_) (atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos) (≃-trans eq₁ T≃)
  with Γ₁′ , C₁′ , spec₁ , spec₂ , _ ← rsplit-bindCtx B₁ ¬S₁ ¬S₂ (≃-sym teq) eqpos C₁
  = s₀ , pol , t₁ , t₂ , Γ₁′ , N , ⊢ᴮ-rsplit′ B₁ q b₁ ⊢B₁ , C₁′ , spec₁ , spec₂

------------------------------------------------------------------------
-- The struct substitution for R-RSplit.  Unlike the l-split one it is
-- always a `⇒`: both halves of an r-split stay `Mobile` when the
-- consumed handle was (the rule inserts the ret/acq boundary, so each
-- half is again a self-contained borrow).

θR : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) →
  (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m) 𝐂.→ₛ
  (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B + m)
θR B₁ B₂ B q b₁ m z with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes _ = (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                   ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
            ∥ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                   ((q + 1) ↑ʳ 0F))
... | no  _ = ` SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} z

θR-h : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) →
  θR B₁ B₂ B q b₁ m (SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F))
    ≡ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
           ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
    ∥ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
           ((q + 1) ↑ʳ 0F))
θR-h B₁ B₂ B q b₁ m
  with SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
     Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

θR-≢ : ∀ (B₁ B₂ B : BindGroup) (q b₁ m : ℕ) z →
  z ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
  θR B₁ B₂ B q b₁ m z ≡ ` SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} z
θR-≢ B₁ B₂ B q b₁ m z ne
  with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

toℕ-dhR₁ : ∀ (B₁ B₂ : BindGroup) (q b₁ : ℕ) →
  Fin.toℕ (Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                    (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
    ≡ sum B₁ + q
toℕ-dhR₁ B₁ B₂ q b₁ =
    Fin.toℕ-cast _ (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
  ■ Fin.toℕ-↑ʳ (sum B₁) ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))
  ■ cong (sum B₁ +_) (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (suc b₁ + sum B₂)
                     ■ Fin.toℕ-↑ʳ q 0F
                     ■ Nat.+-identityʳ q)

toℕ-dhR₂ : ∀ (B₁ B₂ : BindGroup) (q b₁ : ℕ) →
  Fin.toℕ (Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                    (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F)))
    ≡ suc (sum B₁ + q)
toℕ-dhR₂ B₁ B₂ q b₁ =
    Fin.toℕ-cast _ (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F))
  ■ Fin.toℕ-↑ʳ (sum B₁) ((q + 1) ↑ʳ 0F)
  ■ cong (sum B₁ +_) (Fin.toℕ-↑ʳ (q + 1) 0F
                     ■ Nat.+-identityʳ (q + 1)
                     ■ Nat.+-comm q 1)
  ■ Nat.+-suc (sum B₁) q

------------------------------------------------------------------------

γbig-rsplit : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} {Γ : Ctx m} {γ : Struct m}
  (Γ₁′ : Ctx (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂))) (Γ₂ : Ctx (sum B)) →
  ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
    γbigL (B₁ ++ (q + suc b₁) ∷ B₂) B γ 𝐂.⋯ₛ θR B₁ B₂ B q b₁ m
      ≼ γbigL (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B γ
γbig-rsplit B₁ B₂ B {q} {b₁} {m} {Γ} {γ} Γ₁′ Γ₂ =
  ≼-cong-∥ (≼-cong-∥ part1 (≼-refl (≈-reflexive part2))) (≼-refl (≈-reflexive part3))
  where
    W  = sum (B₁ ++ (q + suc b₁) ∷ B₂)
    W′ = sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)
    θ  = θR B₁ B₂ B q b₁ m
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
        θR-≢ B₁ B₂ B q b₁ m _ (neι j (λ x → Nat.<-irrefl x lt))
      ■ cong `_ (P1rq B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective (drwkq-lo B₁ q b₁ B₂ j lt ■ sym e))
    at : ∀ j j₁ j₂ → Fin.toℕ j ≡ sum B₁ + q → Fin.toℕ j₁ ≡ sum B₁ + q →
         Fin.toℕ j₂ ≡ suc (sum B₁ + q) →
         θ ((j ↑ˡ sum B) ↑ˡ m)
           ≡ ((` ((j₁ ↑ˡ sum B) ↑ˡ m)) ∥ (` ((j₂ ↑ˡ sum B) ↑ˡ m)))
    at j j₁ j₂ e e₁ e₂ =
        cong (λ w → θ ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective (e ■ sym (toℕ-dh B₁ B₂ q b₁)))
      ■ θR-h B₁ B₂ B q b₁ m
      ■ cong₂ (λ a c → (` ((a ↑ˡ sum B) ↑ˡ m)) ∥ (` ((c ↑ˡ sum B) ↑ˡ m)))
              (sym (Fin.toℕ-injective (e₁ ■ sym (toℕ-dhR₁ B₁ B₂ q b₁))))
              (sym (Fin.toℕ-injective (e₂ ■ sym (toℕ-dhR₂ B₁ B₂ q b₁))))
    hi : ∀ j j′ → sum B₁ + q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
         θ ((j ↑ˡ sum B) ↑ˡ m) ≡ ` ((j′ ↑ˡ sum B) ↑ˡ m)
    hi j j′ gt e =
        θR-≢ B₁ B₂ B q b₁ m _ (neι j (λ x → Nat.<-irrefl (sym x) gt))
      ■ cong `_ (P1rq B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective (drwkq-hi B₁ q b₁ B₂ j (Nat.<⇒≤ gt) ■ sym e))
    eqA : (structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
            ≡ structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ₛ (λ d → θ ((d ↑ˡ sum B) ↑ˡ m))
    eqA = cong (λ z → z 𝐂.⋯ₛ θ)
               (⋯ᵣᵣ (structBinder (B₁ ++ (q + suc b₁) ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m))
        ■ ⋯ᵣₛ (structBinder (B₁ ++ (q + suc b₁) ∷ B₂)) (λ d → (d ↑ˡ sum B) ↑ˡ m) θ
    eqB : structBinder (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m
            ≡ structBinder (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) 𝐂.⋯ₛ (λ d → ` ((d ↑ˡ sum B) ↑ˡ m))
    eqB = ⋯ᵣᵣ (structBinder (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m)
        ■ ⋯ᵣ⇒ₛ (structBinder (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) (λ d → (d ↑ˡ sum B) ↑ˡ m)
    part1 : ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
            (structBinder (B₁ ++ (q + suc b₁) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
              ≼ (structBinder (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part1 = ≼-trans (≼-refl (≈-reflexive eqA))
            (≼-trans (sb-rsplit B₁ q b₁ B₂ refl _ _ lo at hi)
                     (≼-refl (≈-reflexive (sym eqB))))
    pw₂ : ∀ (w : 𝔽 (sum B)) → θ ((W ↑ʳ w) ↑ˡ m) ≡ ` ((W′ ↑ʳ w) ↑ˡ m)
    pw₂ w = θR-≢ B₁ B₂ B q b₁ m _ (λ e → Fin.↑ˡ≢↑ʳ (sym (Fin.↑ˡ-injective m _ _ e)))
          ■ cong `_ (P2rq B₁ B₂ B w)
    part2 : (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
              ≡ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W′ 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part2 = cong (λ z → z 𝐂.⋯ₛ θ) (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W) (𝐂.wkʳ m))
          ■ ⋯ᵣₛ (structBinder B) (λ w → (W ↑ʳ w) ↑ˡ m) θ
          ■ ⋯ₛ-cong (structBinder B) pw₂
          ■ sym (⋯ᵣ⇒ₛ (structBinder B) (λ w → (W′ ↑ʳ w) ↑ˡ m))
          ■ sym (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W′) (𝐂.wkʳ m))
    pw₃ : ∀ (u : 𝔽 m) → θ ((W + sum B) ↑ʳ u) ≡ ` ((W′ + sum B) ↑ʳ u)
    pw₃ u = θR-≢ B₁ B₂ B q b₁ m _ (λ e → Fin.↑ˡ≢↑ʳ (sym e))
          ■ cong `_ (P3rq B₁ B₂ B u)
    part3 : (γ 𝐂.⋯ᵣ 𝐂.weaken* (W + sum B)) 𝐂.⋯ₛ θ ≡ (γ 𝐂.⋯ᵣ 𝐂.weaken* (W′ + sum B))
    part3 = cong (λ z → z 𝐂.⋯ₛ θ) (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W + sum B)))
          ■ ⋯ᵣₛ γ (𝐂.wkˡ (W + sum B)) θ
          ■ ⋯ₛ-cong γ pw₃
          ■ sym (⋯ᵣ⇒ₛ γ (𝐂.wkˡ (W′ + sum B)))
          ■ sym (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W′ + sum B)))

------------------------------------------------------------------------
-- Mobility survives an r-split.

mob-rsplit : ∀ {t t₁ t₂ : 𝕊 0} → t ≃ t₁ ; t₂ → ¬ Skips t₁ → ¬ Skips t₂ →
  Mobile ⟨ t ⟩ → Mobile ⟨ t₁ ; ret ⟩ × Mobile ⟨ acq ; t₂ ⟩
mob-rsplit {t₂ = t₂} teq ¬S₁ ¬S₂ ⟨ v , Bv , t≃ ⟩
  with acq-;-split (≃-trans (≃-sym teq) t≃)
... | inj₁ (Sk , _)      = ⊥-elim (¬S₁ Sk)
... | inj₂ (h′ , t₁≃ , e) =
      ⟨ (h′ ; ret) , -;₂ ret , ≃-trans (≃-; t₁≃ ≃-refl) ≃-assoc-; ⟩
    , ⟨ t₂ , bt₂ , ≃-refl ⟩
  where
    bt₂ : Bounded t₂
    bt₂ with bounded-;⁻ (≃-bounded (≃-sym e) Bv)
    ... | inj₁ (_ , Sk) = ⊥-elim (¬S₂ Sk)
    ... | inj₂ B        = B

θR-⇒ : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} {t t₁ t₂ : 𝕊 0} {Γ : Ctx m}
  (Γ₁  : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)))
  (Γ₂  : Ctx (sum B)) →
  Agree (sum B₁ + q) Γ₁ Γ₁′ →
  (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) ≡ ⟨ t ⟩) →
  (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
      ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)) ≡ ⟨ t₁ ; ret ⟩) →
  (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
      ((q + 1) ↑ʳ 0F) ≡ ⟨ acq ; t₂ ⟩) →
  t ≃ t₁ ; t₂ → ¬ Skips t₁ → ¬ Skips t₂ →
  𝐂._∶_⇒_ (θR B₁ B₂ B q b₁ m) ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
θR-⇒ B₁ B₂ B {q} {b₁} {m} {Γ = Γ} Γ₁ Γ₁′ Γ₂ Ag eqh lk₁ lk₂ teq ¬S₁ ¬S₂ z =
  case z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) of λ where
    (yes p) →
      subst Mot (sym (cong (θR B₁ B₂ B q b₁ m) p ■ θR-h B₁ B₂ B q b₁ m))
        ( (λ u  → ⊥-elim (¬unr-handle (subst Unr (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) u)))
        , (λ mo → let mm = mob-rsplit teq ¬S₁ ¬S₂
                             (subst Mobile (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) mo)
                  in (` subst Mobile (sym lk₁) (mm .proj₁))
                   ∥ (` subst Mobile (sym lk₂) (mm .proj₂))) )
    (no ne) →
      subst Mot (sym (θR-≢ B₁ B₂ B q b₁ m z ne))
        ( (λ u  → ` subst Unr    (sym (rsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) u)
        , (λ mo → ` subst Mobile (sym (rsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) mo) )
  where
    Mot : Struct (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B + m) → Set
    Mot w = (Unr    (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → UnrCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)
          × (Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → MobCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)

------------------------------------------------------------------------
-- Preservation for R-RSplit.

pres-RSplit : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  ChanCx Γ →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`rsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
             (⟪ (E ⋯ᶠ* SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m})
                  [ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                         ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
                  ⊗ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                         ((q + 1) ↑ʳ 0F)) ]* ⟫
               ∥ (P ⋯ₚ SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m}))
pres-RSplit {m} {Γ} {γ} {B₁} {B₂} {B} {q} {b₁} {s} {E} {P} Γ-S ⊢P
  with k , ρ⁻ , skp , inj⁻ , E₀ , refl , P₀ , refl
     ← rsplit-confine′ Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with Γ₁ , Γ₂ , s₀ , pol , Nw , ⊢B₁ , ⊢B , C₁ , C₂ , ⊢body ← inv-ν ⊢P
  with α , β , αβ≼ , ⊢thread , ⊢Ppar ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eqT , ϵ≤ , ⊢E , ⊢app
     ← ⊢[]*⁻¹ (E₀ ⋯ᶠ* ρ⁻) _ (inv-⟪⟫ ⊢thread)
  with a , γc , γx , _ , ≤γ″ , ≤ₐ , refl , ⊢const , ⊢var
     ← inv-·-unr ⊢app (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , eq₁ `→ eq₂ , []≤ , `rsplit t₁ t₂ ¬S₁ ¬S₂ ← inv-K ⊢const
  with T≃ , x≤ ← inv-` ⊢var
  with t , eqpos ← chanCx-lookup (bindCtx⇒chanCtx C₁) _
  with ⟨ teq ⟩ ← subst ((⟨ t₁ ; t₂ ⟩) ≃_) (atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos) (≃-trans eq₁ T≃)
  with Γ₁′ , C₁′ , spec₁ , spec₂ , Ag ← rsplit-bindCtx B₁ ¬S₁ ¬S₂ (≃-sym teq) eqpos C₁
  = let
      rwk = SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m}
      θ   = θR B₁ B₂ B q b₁ m
      Γsm = V.tabulate (λ y → ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ ρ⁻ y)

      ⊢ρ⁻ : ρ⁻ ⊢ Γsm ⇒ᵣ ((Γ₁ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁻ = ⊢ren (λ y → V.lookup∘tabulate _ y)

      ⊢ρ⁺ : (λ y → rwk (ρ⁻ y)) ⊢ Γsm ⇒ᵣ ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁺ = ⊢ren (λ y → V.lookup∘tabulate _ y
                      ■ sym (rsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag (ρ⁻ y) (skp y)))

      pwρ : ∀ y → θ (ρ⁻ y) ≡ ` (rwk (ρ⁻ y))
      pwρ y = θR-≢ B₁ B₂ B q b₁ m (ρ⁻ y) (skp y)

      eqh : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
              ≡ ⟨ t ⟩
      eqh = atk-lookup B₁ B₂ B Γ₁ Γ₂ Γ ■ eqpos

      lk₁ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                    ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)) ≡ ⟨ t₁ ; ret ⟩
      lk₁ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₁

      lk₂ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                    ((q + 1) ↑ʳ 0F) ≡ ⟨ acq ; t₂ ⟩
      lk₂ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₂
    in
    let 𝒫₀ , ≤𝒫 , ⊢E₀ = ⊢E    ⊢⋯ᶠ*⁻¹ ⊢ρ⁻ / inj⁻
        β₀ , ≤β , ⊢P₀ = ⊢Ppar ⊢⋯ₚ⁻¹ ⊢ρ⁻ / inj⁻
    in
    let
      `h≼γ′ = ≼-trans (≼-refl (≈-sym (join-unitʳ (Arr.dir a))))
                      (≼-trans (≼-join (Arr.dir a) x≤ []≤) ≤γ″)

      old≼ = ≼-trans (≼-cong-∥ (≼-trans (≤𝒫 `h≼γ′) ≤γ′) ≤β) αβ≼

      Deq = cong₂ _∥_
              ([-]-dist-⋯ (𝒫₀ ⋯𝓅 (`_ ∘ ρ⁻))
                          (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) θ
                ■ cong₂ (λ 𝒬 v → 𝒬 [ v ]𝓅) (𝓅∘ 𝒫₀ ρ⁻ θ (λ y → rwk (ρ⁻ y)) pwρ)
                                            (θR-h B₁ B₂ B q b₁ m))
              (σ∘ β₀ ρ⁻ θ (λ y → rwk (ρ⁻ y)) pwρ)

      ineq = ≼-trans (≼-refl (≈-reflexive (sym Deq)))
                     (≼-trans (𝐂.≼-⋯ (θR-⇒ B₁ B₂ B Γ₁ Γ₁′ Γ₂ Ag eqh lk₁ lk₂ (≃-sym teq) ¬S₁ ¬S₂) old≼)
                              (γbig-rsplit B₁ B₂ B {γ = γ} Γ₁′ Γ₂))
    in
    subst₂ (λ F Q → Γ ; γ ⊢ₚ ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
              (⟪ F [ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                          ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
                   ⊗ (` SplitRenamings.inj B₁ B₂ (sum B) {(q + 1) ∷ suc b₁ ∷ []} {m}
                          ((q + 1) ↑ʳ 0F)) ]* ⟫ ∥ Q))
      (sym (⋯ᶠ*-fuse E₀ ρ⁻ rwk)) (sym (fusionₚ P₀ ρ⁻ rwk))
      (TP-Res Nw pol (⊢ᴮ-rsplit′ B₁ q b₁ ⊢B₁) ⊢B C₁′ C₂
        (TP-Weaken ineq
          (TP-Par
            (TP-Expr (T-Conv eqT ϵ≤
              ⊢⟨ ⊢E₀ ⊢⋯ᶠ* ⊢ρ⁺
                 [ T-Conv eq₂ ℙ≤ϵ (T-Pair par par (T-Var _ lk₁) (T-Var _ lk₂)) ]*⟩))
            (⊢P₀ ⊢⋯ₚ ⊢ρ⁺))))
