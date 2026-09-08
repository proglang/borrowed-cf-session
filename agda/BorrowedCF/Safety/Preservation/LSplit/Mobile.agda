------------------------------------------------------------------------
-- P3c, step 3: R-LSplit preservation when the consumed handle MAY BE
-- MOBILE, i.e. when its group has width one (`q = 0`, `b₁ = 0`).
--
-- P3b transports the ν-body inequality along the struct substitution
-- `θL` that expands the handle into `` ` x₁ ; ` x₂ ``.  That substitution
-- is a legal `⇒` only if the handle is immobile, because `MobCx` is
-- atom-wise and neither half of an l-split is mobile.  A MOBILE handle,
-- however, is its group's only handle (`LSplit/Shape.agda`), so its
-- contribution to the ν-binder structure is `` ` h ; [] ``, a top-level
-- `∥`-component.  The proof therefore ERASES it, exactly as
-- `Handles/Acq.agda`'s `acq-final` does at index `0F`:
--
--   * `zapL` sends the handle to `[]` and every other variable along
--     `lwk`.  Sending a variable to `[]` is legal between ANY two contexts
--     (`[]` satisfies `UnrCx` and `MobCx`), so `zapL-⇒` has NO side
--     condition and `𝐂.≼-⋯` transports the whole old inequality.
--   * `pat-hole-≼` (P4b) puts the new pair back in front of the erased
--     frame, and `γbig-zap`/`sb-zap` say that the new ν-binder structure is
--     the old erased one with the pair in parallel.
--
-- Nothing here mentions `Mobile`.  The clause is used for `q = 0`,
-- `b₁ = 0` whether or not the handle is mobile, which is what makes the
-- premise-free `pres-LSplit` possible without deciding `Mobile`.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit.Mobile where

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
import BorrowedCF.Context.Equivalence as 𝐄

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
open import BorrowedCF.Safety.Preservation.LSplit
open import BorrowedCF.Safety.Preservation.LSplit.Struct using (sb-zap)
open import BorrowedCF.Safety.Preservation.Handles.Acq using (pat-hole-≼)

------------------------------------------------------------------------
-- 1.  `zapL`: erase the consumed handle, shift everything else along `lwk`.

zapL : ∀ (B₁ B₂ B : BindGroup) (m : ℕ) →
  (sum (B₁ ++ 1 ∷ B₂) + sum B + m) 𝐂.→ₛ (sum (B₁ ++ 2 ∷ B₂) + sum B + m)
zapL B₁ B₂ B m z with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
... | yes _ = []
... | no  _ = ` SplitRenamings.lwk B₁ B₂ (sum B) {0} {0} {m} z

zapL-h : ∀ (B₁ B₂ B : BindGroup) (m : ℕ) →
  zapL B₁ B₂ B m (SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F) ≡ []
zapL-h B₁ B₂ B m
  with SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
     Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

zapL-≢ : ∀ (B₁ B₂ B : BindGroup) (m : ℕ) z →
  z ≢ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F →
  zapL B₁ B₂ B m z ≡ ` SplitRenamings.lwk B₁ B₂ (sum B) {0} {0} {m} z
zapL-≢ B₁ B₂ B m z ne
  with z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

-- No side condition: `[]` satisfies every context predicate, so the slot
-- whose type changes is exactly the slot that is erased.
zapL-⇒ : ∀ (B₁ B₂ B : BindGroup) {m : ℕ} {Γ : Ctx m}
  (Γ₁  : Ctx (sum (B₁ ++ 1 ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ 2 ∷ B₂)))
  (Γ₂  : Ctx (sum B)) →
  Agree (sum B₁ + 0) Γ₁ Γ₁′ →
  𝐂._∶_⇒_ (zapL B₁ B₂ B m) ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
zapL-⇒ B₁ B₂ B {m} {Γ} Γ₁ Γ₁′ Γ₂ Ag z =
  case z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F of λ where
    (yes p) →
      subst Mot (sym (cong (zapL B₁ B₂ B m) p ■ zapL-h B₁ B₂ B m))
        ((λ _ → []) , (λ _ → []))
    (no ne) →
      subst Mot (sym (zapL-≢ B₁ B₂ B m z ne))
        ( (λ u  → ` subst Unr    (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) u)
        , (λ mo → ` subst Mobile (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) mo) )
  where
    Mot : Struct (sum (B₁ ++ 2 ∷ B₂) + sum B + m) → Set
    Mot w = (Unr    (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → UnrCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)
          × (Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → MobCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)

------------------------------------------------------------------------
-- 2.  The ν-binder structure of the right-hand side is the erased image of
--     the left-hand one, with the new pair in parallel.

private
  rot : ∀ {n} {Γ : Ctx n} {a b c d : Struct n} →
    Γ ∶ a ∥ ((b ∥ c) ∥ d) ≈ ((a ∥ b) ∥ c) ∥ d
  rot = ≈-sym (≈-trans (𝐄.∥-cong 𝐄.∥-assoc ≈-refl) 𝐄.∥-assoc)

γbig-zap : ∀ (B₁ B₂ B : BindGroup) {m : ℕ} {Γ : Ctx m} {γ : Struct m}
  (Γ₁′ : Ctx (sum (B₁ ++ 2 ∷ B₂))) (Γ₂ : Ctx (sum B)) →
  ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
    ((` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 0F)
      ; (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 1F))
      ∥ (γbigL (B₁ ++ 1 ∷ B₂) B γ 𝐂.⋯ₛ zapL B₁ B₂ B m)
    ≈ γbigL (B₁ ++ 2 ∷ B₂) B γ
γbig-zap B₁ B₂ B {m} {Γ} {γ} Γ₁′ Γ₂ =
  ≈-trans rot (𝐄.∥-cong (𝐄.∥-cong part1 (≈-reflexive part2)) (≈-reflexive part3))
  where
    W  = sum (B₁ ++ 1 ∷ B₂)
    W′ = sum (B₁ ++ 2 ∷ B₂)
    θ  = zapL B₁ B₂ B m
    pr : Struct (W′ + sum B + m)
    pr = (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 0F)
       ; (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 1F)
    dh₀ : 𝔽 W
    dh₀ = dh B₁ B₂ 0 0
    tℕι : ∀ (j : 𝔽 W) → Fin.toℕ ((j ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ j
    tℕι j = Fin.toℕ-↑ˡ (j ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ j (sum B)
    tℕatk : Fin.toℕ (SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F) ≡ sum B₁ + 0
    tℕatk = tℕι dh₀ ■ toℕ-dh B₁ B₂ 0 0
    neι : ∀ (j : 𝔽 W) → Fin.toℕ j ≢ sum B₁ + 0 →
          (j ↑ˡ sum B) ↑ˡ m ≢ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
    neι j nj e = nj (sym (tℕι j) ■ cong Fin.toℕ e ■ tℕatk)
    lo : ∀ j j′ → Fin.toℕ j Nat.< sum B₁ + 0 → Fin.toℕ j′ ≡ Fin.toℕ j →
         θ ((j ↑ˡ sum B) ↑ˡ m) ≡ ` ((j′ ↑ˡ sum B) ↑ˡ m)
    lo j j′ lt e =
        zapL-≢ B₁ B₂ B m _ (neι j (λ x → Nat.<-irrefl x lt))
      ■ cong `_ (P1q B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective
               (dlwkq-lo B₁ 0 0 B₂ j
                 (subst (Fin.toℕ j Nat.<_) (Nat.+-comm 1 (sum B₁ + 0))
                        (Nat.<-trans lt (Nat.n<1+n _)))
               ■ sym e))
    atz : ∀ j → Fin.toℕ j ≡ sum B₁ + 0 → θ ((j ↑ˡ sum B) ↑ˡ m) ≡ []
    atz j e =
        cong (λ w → θ ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective (e ■ sym (toℕ-dh B₁ B₂ 0 0)))
      ■ zapL-h B₁ B₂ B m
    atg : ∀ j₁ j₂ → Fin.toℕ j₁ ≡ sum B₁ + 0 → Fin.toℕ j₂ ≡ suc (sum B₁ + 0) →
          ((` ((j₁ ↑ˡ sum B) ↑ˡ m)) ; (` ((j₂ ↑ˡ sum B) ↑ˡ m))) ≡ pr
    atg j₁ j₂ e₁ e₂ =
      cong₂ (λ a c → (` ((a ↑ˡ sum B) ↑ˡ m)) ; (` ((c ↑ˡ sum B) ↑ˡ m)))
            (Fin.toℕ-injective (e₁ ■ sym (toℕ-dh B₁ B₂ 0 1)))
            (Fin.toℕ-injective (e₂ ■ sym (toℕ-dh₂ B₁ B₂ 0 0)))
    hi : ∀ j j′ → sum B₁ + 0 Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
         θ ((j ↑ˡ sum B) ↑ˡ m) ≡ ` ((j′ ↑ˡ sum B) ↑ˡ m)
    hi j j′ gt e =
        zapL-≢ B₁ B₂ B m _ (neι j (λ x → Nat.<-irrefl (sym x) gt))
      ■ cong `_ (P1q B₁ B₂ B j)
      ■ cong (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
             (Fin.toℕ-injective
               (dlwkq-hi B₁ 0 0 B₂ j
                 (subst (Nat._≤ Fin.toℕ j) (Nat.+-comm 1 (sum B₁ + 0)) gt)
               ■ sym e))
    eqA : (structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
            ≡ structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ₛ (λ w → θ ((w ↑ˡ sum B) ↑ˡ m))
    eqA = cong (λ zz → zz 𝐂.⋯ₛ θ)
               (⋯ᵣᵣ (structBinder (B₁ ++ 1 ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m))
        ■ ⋯ᵣₛ (structBinder (B₁ ++ 1 ∷ B₂)) (λ w → (w ↑ˡ sum B) ↑ˡ m) θ
    eqB : structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m
            ≡ structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ₛ (λ w → ` ((w ↑ˡ sum B) ↑ˡ m))
    eqB = ⋯ᵣᵣ (structBinder (B₁ ++ 2 ∷ B₂)) (𝐂.wkʳ (sum B)) (𝐂.wkʳ m)
        ■ ⋯ᵣ⇒ₛ (structBinder (B₁ ++ 2 ∷ B₂)) (λ w → (w ↑ˡ sum B) ↑ˡ m)
    part1 : ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ∶
            pr ∥ ((structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ)
              ≈ (structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part1 = ≈-trans (≈-reflexive (cong (pr ∥_) eqA))
            (≈-trans (sb-zap B₁ B₂ (sym (Nat.+-identityʳ (sum B₁)))
                        (λ w → θ ((w ↑ˡ sum B) ↑ˡ m))
                        (λ w → ` ((w ↑ˡ sum B) ↑ˡ m)) pr lo atz atg hi)
                     (≈-reflexive (sym eqB)))
    pw₂ : ∀ (w : 𝔽 (sum B)) → θ ((W ↑ʳ w) ↑ˡ m) ≡ ` ((W′ ↑ʳ w) ↑ˡ m)
    pw₂ w = zapL-≢ B₁ B₂ B m _ (λ e → Fin.↑ˡ≢↑ʳ (sym (Fin.↑ˡ-injective m _ _ e)))
          ■ cong `_ (P2q B₁ B₂ B w)
    part2 : (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W 𝐂.⋯ᵣ 𝐂.wkʳ m) 𝐂.⋯ₛ θ
              ≡ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ W′ 𝐂.⋯ᵣ 𝐂.wkʳ m)
    part2 = cong (λ zz → zz 𝐂.⋯ₛ θ) (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W) (𝐂.wkʳ m))
          ■ ⋯ᵣₛ (structBinder B) (λ w → (W ↑ʳ w) ↑ˡ m) θ
          ■ ⋯ₛ-cong (structBinder B) pw₂
          ■ sym (⋯ᵣ⇒ₛ (structBinder B) (λ w → (W′ ↑ʳ w) ↑ˡ m))
          ■ sym (⋯ᵣᵣ (structBinder B) (𝐂.wkˡ W′) (𝐂.wkʳ m))
    pw₃ : ∀ (u : 𝔽 m) → θ ((W + sum B) ↑ʳ u) ≡ ` ((W′ + sum B) ↑ʳ u)
    pw₃ u = zapL-≢ B₁ B₂ B m _ (λ e → Fin.↑ˡ≢↑ʳ (sym e))
          ■ cong `_ (P3q B₁ B₂ B u)
    part3 : (γ 𝐂.⋯ᵣ 𝐂.weaken* (W + sum B)) 𝐂.⋯ₛ θ ≡ (γ 𝐂.⋯ᵣ 𝐂.weaken* (W′ + sum B))
    part3 = cong (λ zz → zz 𝐂.⋯ₛ θ) (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W + sum B)))
          ■ ⋯ᵣₛ γ (𝐂.wkˡ (W + sum B)) θ
          ■ ⋯ₛ-cong γ pw₃
          ■ sym (⋯ᵣ⇒ₛ γ (𝐂.wkˡ (W′ + sum B)))
          ■ sym (𝐂.⋯-cong γ (𝐂.weaken*~wkˡ (W′ + sum B)))

------------------------------------------------------------------------
-- 3.  Preservation for R-LSplit at a width-one group.

pres-LSplit-mobile : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ 1 ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ 1 ∷ B₂) + sum B + m)} →
  ChanCx Γ →
  Γ ; γ ⊢ₚ ν (B₁ ++ 1 ∷ B₂) B
             (⟪ E [ K (`lsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (B₁ ++ 2 ∷ B₂) B
             (⟪ (E ⋯ᶠ* SplitRenamings.lwk B₁ B₂ (sum B) {0} {0} {m})
                  [ (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 0F)
                  ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 1F) ]* ⟫
               ∥ (P ⋯ₚ SplitRenamings.lwk B₁ B₂ (sum B) {0} {0} {m}))
pres-LSplit-mobile {m} {Γ} {γ} {B₁} {B₂} {B} {s} {E} {P} Γ-S ⊢P
  with k , ρ⁻ , skp , inj⁻ , E₀ , refl , P₀ , refl ← lsplit-confine′ Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = 0} {b₁ = 0} {s = s} {E = E} {P = P} ⊢P
  with Γ₁ , Γ₂ , s₀ , pol , Nw , ⊢B₁ , ⊢B , C₁ , C₂ , ⊢body ← inv-ν ⊢P
  with α , β , αβ≼ , ⊢thread , ⊢Ppar ← inv-∥ ⊢body
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ′ , eqT , ϵ≤ , ⊢E , ⊢app
     ← ⊢[]*⁻¹ (E₀ ⋯ᶠ* ρ⁻) _ (inv-⟪⟫ ⊢thread)
  with a , γc , γx , _ , ≤γ″ , ≤ₐ , refl , ⊢const , ⊢var
     ← inv-·-unr ⊢app (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , eq₁ `→ eq₂ , []≤ , `lsplit t₁ t₂ ¬S₁ ¬S₂ ← inv-K ⊢const
  with T≃ , x≤ ← inv-` ⊢var
  with t , eqpos ← chanCx-lookup (bindCtx⇒chanCtx C₁) _
  with ⟨ teq ⟩ ← subst (⟨ t₁ ; t₂ ⟩ ≃_) (atk-lookup B₁ B₂ B {q = 0} {b₁ = 0} Γ₁ Γ₂ Γ ■ eqpos) (≃-trans eq₁ T≃)
  with Γ₁′ , C₁′ , spec₁ , spec₂ , Ag ← lsplit-bindCtx B₁ {B₂ = B₂} {q = 0} {b₁ = 0} ¬S₁ ¬S₂ (≃-sym teq) eqpos C₁
  = let
      lwk = SplitRenamings.lwk B₁ B₂ (sum B) {0} {0} {m}
      θ   = zapL B₁ B₂ B m
      Γsm = V.tabulate (λ y → ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ ρ⁻ y)

      ⊢ρ⁻ : ρ⁻ ⊢ Γsm ⇒ᵣ ((Γ₁ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁻ = ⊢ren (λ y → V.lookup∘tabulate _ y)

      ⊢ρ⁺ : (λ y → lwk (ρ⁻ y)) ⊢ Γsm ⇒ᵣ ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
      ⊢ρ⁺ = ⊢ren (λ y → V.lookup∘tabulate _ y
                      ■ sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag (ρ⁻ y) (skp y)))

      pwρ : ∀ y → θ (ρ⁻ y) ≡ ` (lwk (ρ⁻ y))
      pwρ y = zapL-≢ B₁ B₂ B m (ρ⁻ y) (skp y)

      eqh : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F
              ≡ ⟨ t ⟩
      eqh = atk-lookup B₁ B₂ B {q = 0} {b₁ = 0} Γ₁ Γ₂ Γ ■ eqpos
    in
    let 𝒫₀ , ≤𝒫 , ⊢E₀ = ⊢E    ⊢⋯ᶠ*⁻¹ ⊢ρ⁻ / inj⁻
        β₀ , ≤β , ⊢P₀ = ⊢Ppar ⊢⋯ₚ⁻¹ ⊢ρ⁻ / inj⁻
    in
    let
      lk₁ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 0F ≡ ⟨ t₁ ⟩
      lk₁ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₁

      lk₂ : ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
              ﹫ SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 1F ≡ ⟨ t₂ ⟩
      lk₂ = V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ _ ■ V.lookup-++ˡ Γ₁′ Γ₂ _ ■ spec₂

      `h≼γ′ = ≼-trans (≼-refl (≈-sym (join-unitʳ (Arr.dir a))))
                      (≼-trans (≼-join (Arr.dir a) x≤ []≤) ≤γ″)

      old≼ = ≼-trans (≼-cong-∥ (≼-trans (≤𝒫 `h≼γ′) ≤γ′) ≤β) αβ≼

      Deq = cong₂ _∥_
              ([-]-dist-⋯ (𝒫₀ ⋯𝓅 (`_ ∘ ρ⁻)) (` SplitRenamings.atk B₁ B₂ (sum B) {1} {m} 0F) θ
                ■ cong₂ (λ 𝒬 v → 𝒬 [ v ]𝓅) (𝓅∘ 𝒫₀ ρ⁻ θ (λ y → lwk (ρ⁻ y)) pwρ)
                                            (zapL-h B₁ B₂ B m))
              (σ∘ β₀ ρ⁻ θ (λ y → lwk (ρ⁻ y)) pwρ)

      zapped = ≼-trans (≼-refl (≈-reflexive (sym Deq)))
                       (𝐂.≼-⋯ (zapL-⇒ B₁ B₂ B Γ₁ Γ₁′ Γ₂ Ag) old≼)

      ineq = ≼-trans (≼-cong-∥ (pat-hole-≼ (𝒫₀ ⋯𝓅 (`_ ∘ (λ y → lwk (ρ⁻ y))))) (≼-refl ≈-refl))
             (≼-trans (≼-refl 𝐄.∥-assoc)
             (≼-trans (≼-cong-∥ (≼-refl ≈-refl) zapped)
                      (≼-refl (γbig-zap B₁ B₂ B {γ = γ} Γ₁′ Γ₂))))
    in
    subst₂ (λ F Q → Γ ; γ ⊢ₚ ν (B₁ ++ 2 ∷ B₂) B
              (⟪ F [ (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 0F)
                   ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {2} {m} 1F) ]* ⟫ ∥ Q))
      (sym (⋯ᶠ*-fuse E₀ ρ⁻ lwk)) (sym (fusionₚ P₀ ρ⁻ lwk))
      (TP-Res Nw pol (⊢ᴮ-lsplit′ B₁ 0 0 ⊢B₁) ⊢B C₁′ C₂
        (TP-Weaken ineq
          (TP-Par
            (TP-Expr (T-Conv eqT ϵ≤
              ⊢⟨ ⊢E₀ ⊢⋯ᶠ* ⊢ρ⁺
                 [ T-Conv eq₂ ℙ≤ϵ (T-Pair seq seq (T-Var _ lk₁) (T-Var _ lk₂)) ]*⟩))
            (⊢P₀ ⊢⋯ₚ ⊢ρ⁺))))
