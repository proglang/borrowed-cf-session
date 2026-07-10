-- | Backward simulation, RU-Choice.  Reflects one untyped select/branch
--   rendezvous back to a typed R-Choice step in the CLEAN single-step codomain.
--   Ported from BorrowedCF.Simulation.Support.RevChoice: the ⊎ cleanup slot of the old
--   codomain collapsed to a bare  Q ≈ U[ P′ ] σ, and the z≡0F / w≡0F
--   front-handle pinning uses the before-ordering/confinement theory (¬ Mobile
--   handles via ¬mobile-block-at).  Interface mirrors Backward.LSplit; wired at
--   Backward.agda like bwd-fork by  choice-reflect σ Vσ Γ-S ⊢P (sym eq).
module BorrowedCF.Simulation.Backward.Choice where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; νσ-VSub; close-arg-var; inv-U-ν-∥-shape; U-ν-singleton;
         inv-ν-chanCx; ν-inj; frameApp-reflect)
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-comᴿ; before-com-binderᴿ)
open import BorrowedCF.Simulation.Support.RevGrindA
  using (choice-¬before; barevar-arg-count;
         select-arg-decomp; select-app-𝕀; branch-arg-decomp; branch-app-𝕀)
open import BorrowedCF.Simulation.Support.RevComConfine
  using (frames-𝕀; com-xS-min; before-com-binderᴸ; ¬mobile-block-at)
open import BorrowedCF.Types using (new-dual; unr⇒mobile)
open import BorrowedCF.Simulation.Support.RevComImage
  using (com-image-block1; recv-image-block2; pos⇒suc)
open import BorrowedCF.Simulation.Support.ReverseConfine using (count-handle-comᴸ)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before)
open import BorrowedCF.Context using (_⸴*_)
import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂S
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-injective)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using ([_,_]′)
import Data.Sum as Sum
open TP using (BindGroup; structBinder)

open Fin.Patterns

------------------------------------------------------------------------
-- choice-go : reflect the ν-headed select/branch redex (both bind groups
-- singletons) back to R-Choice.  z≡0F / w≡0F pin the consumed handles to the
-- ν-bound front pair (the before-minimality confinement engine); finish then
-- fires R-Struct ∘ R-Choice ∘ R-Struct and reconciles the codomain.
------------------------------------------------------------------------

choice-go :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ b₂ : ℕ) (k : Side)
    {F₀ˢ F₀ᴿ : Frame* (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {argˢ argᴿ : Tm (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {Pr : TP.Proc (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {F₁ F₂ : Frame* (2 + n)} {e₁ e₁′ e₂ e₂′ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
  → Γ ; g ⊢ₚ TP.ν (b₁ ∷ []) (b₂ ∷ [])
       (TP.⟪ F₀ˢ [ K (`select k) ·¹ argˢ ]* ⟫ TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ argᴿ ]* ⟫ TP.∥ Pr))
  → F₁ ≡ frame*-⋯ F₀ˢ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₁ ⊗ (` 0F)) ⊗ e₁′) ≡ argˢ ⋯ νσ b₁ b₂ σ
  → F₂ ≡ frame*-⋯ F₀ᴿ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₂ ⊗ (` 1F)) ⊗ e₂′) ≡ argᴿ ⋯ νσ b₁ b₂ σ
  → P₁ ≡ U[ Pr ] (νσ b₁ b₂ σ)
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_
          (TP.ν (b₁ ∷ []) (b₂ ∷ [])
            (TP.⟪ F₀ˢ [ K (`select k) ·¹ argˢ ]* ⟫ TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ argᴿ ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UP.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫
             UP.∥ (UP.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ UP.∥ P₁))
              ≈ U[ P′ ] σ )
choice-go {m} {n} σ Vσ {Γ} Γ-S {g} b₁ b₂ k {F₀ˢ} {F₀ᴿ} {argˢ} {argᴿ} {Pr}
          {F₁} {F₂} {e₁} {e₁′} {e₂} {e₂′} {P₁} ⊢P FeqS argeqS FeqR argeqR Preq
  with Γ₁ , Γ₂ , s' , p' , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with αS , βrest , ≼₁ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with αR , βP , ≼₂ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with 𝒫ˢ , γrˢ , _ , _ , _ , _ , ≼ˢ , _ , _ , ⊢Fˢ , ⊢redexˢ
       ← ⊢[]*⁻¹ F₀ˢ (K (`select k) ·¹ argˢ) (inv-⟪⟫ ⊢PS)
  with s₁ˢ , s₂ˢ , βs , Rs , ϵs , brn≃ , ⊢argSty ← select-arg-decomp ⊢redexˢ
  with xS , refl ← close-arg-var argˢ ⊢argSty brn≃ (νσ b₁ b₂ σ) (sym argeqS)
  with refl ← select-app-𝕀 ⊢redexˢ
  with refl , lpˢ ← frames-𝕀 ⊢Fˢ
  with z , 1≤b₁ , refl ← com-image-block1 b₁ b₂ σ Vσ xS argeqS
  with b₁' , refl ← pos⇒suc 1≤b₁
  with 𝒫ᴿ , γrᴿ , _ , _ , _ , _ , ≼ᴿ , _ , _ , ⊢Fᴿ , ⊢redexᴿ
       ← ⊢[]*⁻¹ F₀ᴿ (K `branch ·¹ argᴿ) (inv-⟪⟫ ⊢PR)
  with s₁ʳ , s₂ʳ , βb , Rb , ϵb , brn⁇≃ , ⊢argRty ← branch-arg-decomp ⊢redexᴿ
  with xR , refl ← close-arg-var argᴿ ⊢argRty brn⁇≃ (νσ (suc b₁') b₂ σ) (sym argeqR)
  with refl ← branch-app-𝕀 ⊢redexᴿ
  with refl , lpᴿ ← frames-𝕀 ⊢Fᴿ
  with w , 1≤b₂ , refl ← recv-image-block2 (suc b₁') b₂ σ Vσ xR argeqR
  with b₂' , refl ← pos⇒suc 1≤b₂
  = finish z≡0F w≡0F
  where
    Sb : Struct (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ []) + m)
    Sb = (structBinder (suc b₁' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (suc b₂' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (structBinder (suc b₂' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (suc b₁' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ [])))

    lookupL-z : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m) ≡ Γ₁ z
    lookupL-z = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) (z ↑ˡ (suc b₂' + 0)) m)
              ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0) z (suc b₂' + 0))
    ¬u0 = ¬mobile-block-at Nnew C 0F refl

    ¬uxS = ¬mobile-block-at Nnew C z lookupL-z
    1≤c  = barevar-arg-count (¬uxS ∘ unr⇒mobile) ⊢redexˢ
    cnt1 = count-handle-comᴸ (suc b₁') (suc b₂') g z
    z₀   = Fin.cast (+-identityʳ (suc b₁')) z
    z₀↑0≡z : z₀ ↑ˡ 0 ≡ z
    z₀↑0≡z = toℕ-injective (toℕ-↑ˡ z₀ 0 ■ toℕ-cast (+-identityʳ (suc b₁')) z)
    contra : Fin.toℕ z₀ ≢ 0 → ⊥
    contra ne = com-xS-min ¬uxS ¬u0 lpˢ ≼ˢ ≼₁ cnt1
                  (subst (λ zz → before 0F ((zz ↑ˡ (suc b₂' + 0)) ↑ˡ m) Sb) z₀↑0≡z
                    (before-com-binderᴸ b₁' (suc b₂') g z₀ ne))
                  1≤c (choice-¬before ¬uxS ¬u0 ⊢redexˢ)
    z≡0F : z ≡ 0F
    z≡0F with Fin.toℕ z₀ Nat.≟ 0
    ... | yes e0 = toℕ-injective (sym (toℕ-cast (+-identityʳ (suc b₁')) z) ■ e0)
    ... | no  ne = ⊥-elim (contra ne)

    posR : 𝔽 (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ []) + m)
    posR = ((suc b₁' + 0) ↑ʳ (Fin.zero {b₂' + 0})) ↑ˡ m
    lookupR : ((Γ₁ ⸴* Γ₂) ⸴* Γ) posR ≡ Γ₂ 0F
    lookupR = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) ((suc b₁' + 0) ↑ʳ (Fin.zero {b₂' + 0})) m)
            ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁' + 0) (suc b₂' + 0) (Fin.zero {b₂' + 0}))
    lookupL-w : ((Γ₁ ⸴* Γ₂) ⸴* Γ) (((suc b₁' + 0) ↑ʳ w) ↑ˡ m) ≡ Γ₂ w
    lookupL-w = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) ((suc b₁' + 0) ↑ʳ w) m)
              ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁' + 0) (suc b₂' + 0) w)
    ¬uxR = ¬mobile-block-at (new-dual Nnew) C′ w lookupL-w
    ¬uyR = ¬mobile-block-at (new-dual Nnew) C′ 0F lookupR
    1≤cᴿ = barevar-arg-count (¬uxR ∘ unr⇒mobile) ⊢redexᴿ
    cnt1ᴿ = count-handle-comᴿ (suc b₁') (suc b₂') g w
    w₀   = Fin.cast (+-identityʳ (suc b₂')) w
    w₀↑0≡w : w₀ ↑ˡ 0 ≡ w
    w₀↑0≡w = toℕ-injective (toℕ-↑ˡ w₀ 0 ■ toℕ-cast (+-identityʳ (suc b₂')) w)
    combined≼ =
      𝐂.≼-trans (𝐂.≼-refl (𝐂.≈-trans (𝐂.≈-sym 𝐂.∥-assoc) 𝐂.∥-comm))
        (𝐂.≼-trans (𝐂.≼-cong-∥ (𝐂.≼-refl 𝐂.≈-refl) ≼₂) ≼₁)
    contraᴿ : Fin.toℕ w₀ ≢ 0 → ⊥
    contraᴿ ne = com-xS-min ¬uxR ¬uyR lpᴿ ≼ᴿ combined≼ cnt1ᴿ
                   (subst (λ ww → before posR (((suc b₁' + 0) ↑ʳ ww) ↑ˡ m) Sb) w₀↑0≡w
                     (before-com-binderᴿ (suc b₁') b₂' g w₀ ne))
                   1≤cᴿ (choice-¬before ¬uxR ¬uyR ⊢redexᴿ)
    w≡0F : w ≡ 0F
    w≡0F with Fin.toℕ w₀ Nat.≟ 0
    ... | yes e0 = toℕ-injective (sym (toℕ-cast (+-identityʳ (suc b₂')) w) ■ e0)
    ... | no  ne = ⊥-elim (contraᴿ ne)

    finish : z ≡ 0F → w ≡ 0F →
      Σ[ P′ ∈ TP.Proc m ]
        ( Star TR._─→ₚ_
            (TP.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
              (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m)) ]* ⟫
               TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` (((suc b₁' + 0) ↑ʳ w) ↑ˡ m)) ]* ⟫ TP.∥ Pr))) P′ )
        × ( UP.ν (UP.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫
               UP.∥ (UP.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ UP.∥ P₁))
                ≈ U[ P′ ] σ )
    finish refl refl =
      let
        νσ0 = νσ (suc b₁') (suc b₂') σ
        Vνσ0 = νσ-VSub (suc b₁') (suc b₂') σ Vσ
        P′ = TP.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
               (TP.⟪ F₀ˢ [ ` 0F ]* ⟫
                TP.∥ (TP.⟪ F₀ᴿ [ `inj k (` (Fin.suc ((b₁' + 0 ↑ʳ 0F) ↑ˡ m))) ]* ⟫ TP.∥ Pr))
        step0 = TR.R-Struct (TP.ν-cong TP.∥-assoc)
                  (TR.R-Choice {b₁ = b₁'} {B₁ = []} {b₂ = b₂'} {B₂ = []} {P = Pr} F₀ˢ F₀ᴿ k)
                  (TP.ν-cong (Eq*.symmetric TP._≋′_ TP.∥-assoc)) ◅ ε
        thread₁ = cong UP.⟪_⟫
          ( cong₂ _[_]* FeqS argeqS
          ■ sym (frame-plug* F₀ˢ νσ0 Vνσ0) )
        thread₂ = cong UP.⟪_⟫
          ( cong₂ _[_]* FeqR (cong (`inj k) argeqR)
          ■ sym (frame-plug* F₀ᴿ νσ0 Vνσ0) )
        recon = cong UP.ν (cong₂ UP._∥_ thread₁ (cong₂ UP._∥_ thread₂ Preq))
      in P′ , step0 , ≋⇒≈ (≡→≋ recon)

------------------------------------------------------------------------
-- The exported reflection.  Interface mirrors Backward.LSplit.lsplit-reflect:
-- the untyped redex is presented as its frames F₁/F₂ plus the equation
-- U[ P ] σ ≡ (RU-Choice LHS); the result is the (RU-Choice RHS) ≈-bridged to
-- U[ P′ ] σ.  Wired at Backward.agda by  choice-reflect σ Vσ Γ-S ⊢P (sym eq).
------------------------------------------------------------------------

choice-reflect : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
               → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
               → {k : Side} {e₁ e₁′ e₂ e₂′ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
                 {F₁ F₂ : Frame* (2 + n)}
               → U[ P ] σ ≡ UP.ν (UP.⟪ F₁ [ K (`select k) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₁′) ]* ⟫
                              UP.∥ (UP.⟪ F₂ [ K `branch ·¹ ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫
                              UP.∥ P₁))
               → Σ[ P′ ∈ TP.Proc m ]
                   ( Star TR._─→ₚ_ P P′
                   × UP.ν (UP.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫
                       UP.∥ (UP.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ UP.∥ P₁))
                       ≈ U[ P′ ] σ )
choice-reflect σ Vσ Γ-S {P = P} ⊢P {k = k} {F₁ = F₁} {F₂ = F₂} eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PS , Prest , refl , Seq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with PR , Pr , refl , Req , Preq ← inv-U-∥ Prest (νσ b₁ b₂ σ) (sym Resteq)
  with eS , refl , Seq′ ← inv-U-⟪⟫ PS (νσ b₁ b₂ σ) (sym Seq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with _ , _ , _ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with _ , _ , _ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with F₀ˢ , argˢ , refl , FeqS , argeqS
       ← frameApp-reflect Γ′-S eS (inv-⟪⟫ ⊢PS) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`select k)
           F₁ (sym Seq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `branch
           F₂ (sym Req′)
  = choice-go σ Vσ Γ-S b₁ b₂ k ⊢P FeqS argeqS FeqR argeqR Preq
