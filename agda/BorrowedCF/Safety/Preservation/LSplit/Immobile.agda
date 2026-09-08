------------------------------------------------------------------------
-- P3c, step 2: R-LSplit preservation when the consumed handle is IMMOBILE.
--
-- This is P3b's `pres-LSplit-immobile` (LSplit.agda) with its premise
-- weakened from
--
--     ∀ u → ¬ Mobile ⟨ s ; u ⟩          ("the left half is not acq-headed")
--
-- to the immobility of the consumed handle's OWN type.  The two are not
-- equivalent: `Bounded (h ; ret)` holds for every `h`, so `s ≃ acq ; h`
-- already gives `Mobile ⟨ s ; ret ⟩`, i.e. P3b's premise says exactly "`s`
-- is not acq-headed"; and the head of a NON-FIRST group IS acq-headed
-- (`Crux.laterGroup-head-acq`) while still being immobile as soon as its
-- group is at least two handles wide.  That case -- `q ≡ 0`, `b₁ > 0` --
-- is the one P3b's lemma cannot serve, and it is why the assembly is
-- restated here.
--
-- The premise is taken in the form "whatever binder context the derivation
-- produces, the handle's slot in it is immobile", which is what
-- `LSplit/Shape.agda`'s `handle-interior-¬mobile` / `handle-wide-¬mobile`
-- deliver.  Everything else is P3b's proof verbatim.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit.Immobile where

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

open import BorrowedCF.Safety.Preservation.LSplit
open import BorrowedCF.Safety.Preservation.LSplit.Shape using (dpos)

------------------------------------------------------------------------
-- `θL` is a structure-preserving map of the two ν-body contexts, given
-- only the immobility of the consumed handle.  (P3b's `θL-⇒` derives that
-- immobility from the stronger "not acq-headed" premise.)

θL-⇒′ : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} {t : 𝕊 0} {Γ : Ctx m}
  (Γ₁  : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)))
  (Γ₂  : Ctx (sum B)) →
  Agree (sum B₁ + q) Γ₁ Γ₁′ →
  (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) ≡ ⟨ t ⟩) →
  ¬ Mobile ⟨ t ⟩ →
  𝐂._∶_⇒_ (θL B₁ B₂ B q b₁ m) ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((Γ₁′ ⸴* Γ₂) ⸴* Γ)
θL-⇒′ B₁ B₂ B {q} {b₁} {m} {Γ = Γ} Γ₁ Γ₁′ Γ₂ Ag eqh ¬mobT z =
  case z Fin.≟ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) of λ where
    (yes p) →
      subst Mot (sym (cong (θL B₁ B₂ B q b₁ m) p ■ θL-h B₁ B₂ B q b₁ m))
        ( (λ u  → ⊥-elim (¬unr-handle (subst Unr (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) u)))
        , (λ mo → ⊥-elim (¬mobT (subst Mobile (cong (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫_) p ■ eqh) mo))) )
    (no ne) →
      subst Mot (sym (θL-≢ B₁ B₂ B q b₁ m z ne))
        ( (λ u  → ` subst Unr    (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) u)
        , (λ mo → ` subst Mobile (sym (lsplit-lookup B₁ B₂ B Γ₁ Γ₁′ Γ₂ Γ Ag z ne)) mo) )
  where
    Mot : Struct (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B + m) → Set
    Mot w = (Unr    (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → UnrCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)
          × (Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z) → MobCx ((Γ₁′ ⸴* Γ₂) ⸴* Γ) w)

------------------------------------------------------------------------
-- Preservation for R-LSplit at an immobile handle.

pres-LSplit-shape : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  ChanCx Γ →
  (¬mobA : ∀ {Γ₁ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))} {s₀ : 𝕊 0} {pol : Pol} →
     New s₀ → ⊢ᴮ (B₁ ++ (q + suc b₁) ∷ B₂) →
     BindCtx (s₀ ; end pol) (B₁ ++ (q + suc b₁) ∷ B₂) Γ₁ →
     ¬ Mobile (Γ₁ ﹫ dpos B₁ q b₁ B₂)) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`lsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
             (⟪ (E ⋯ᶠ* SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m})
                  [ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
                  ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F)) ]* ⟫
               ∥ (P ⋯ₚ SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m}))
pres-LSplit-shape {m} {Γ} {γ} {B₁} {B₂} {B} {q} {b₁} {s} {E} {P} Γ-S ¬mobA ⊢P
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
                     (≼-trans (𝐂.≼-⋯ (θL-⇒′ B₁ B₂ B Γ₁ Γ₁′ Γ₂ Ag eqh
                                          (subst (λ T → ¬ Mobile T) eqpos (¬mobA Nw ⊢B₁ C₁))) old≼)
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
