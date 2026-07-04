module BorrowedCF.Simulation.RevChoice where

-- Reverse RU-Choice: reflect an untyped select/branch rendezvous at a strict
-- image back to a typed R-Choice step.  Mirror of RevCom.com-go, simpler:
-- R-Choice neither consumes handles nor reweakens (the binder is preserved),
-- so no strengthening and no leaf-substitution collapse are needed.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.ReverseInv
  using (νσ; νσ-VSub; close-arg-var)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.RevGrindC
  using (count-handle-comᴿ; before-com-binderᴿ)
open import BorrowedCF.Simulation.RevGrindA
  using (chanCx-¬Unr; choice-¬before; barevar-arg-count;
         select-arg-decomp; select-app-𝕀; branch-arg-decomp; branch-app-𝕀)
open import BorrowedCF.Simulation.RevComConfine
  using (frames-𝕀; com-xS-min; before-com-binderᴸ)
open import BorrowedCF.Simulation.RevComImage
  using (com-image-block1; recv-image-block2; pos⇒suc)
open import BorrowedCF.Simulation.ReverseConfine using (count-handle-comᴸ)
open import BorrowedCF.Simulation.BeforeOrder using (before)
open import BorrowedCF.Context using (Ctx; Struct; _∶_≼_)
import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Reduction.Base using (ChanCx)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-injective)
open import Data.Nat.Properties using (+-identityʳ)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open T using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)

open Fin.Patterns

choice-go :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ b₂ : ℕ) (k : Side)
    {F₀ˢ F₀ᴿ : Frame* (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {argˢ argᴿ : Tm (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {Pr : T.Proc (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {F₁ F₂ : Frame* (2 + n)} {e₁ e₁′ e₂ e₂′ : Tm (2 + n)} {P₁ : U.Proc (2 + n)}
  → Γ ; g ⊢ₚ T.ν (b₁ ∷ []) (b₂ ∷ [])
       (T.⟪ F₀ˢ [ K (`select k) ·¹ argˢ ]* ⟫ T.∥ (T.⟪ F₀ᴿ [ K `branch ·¹ argᴿ ]* ⟫ T.∥ Pr))
  → F₁ ≡ frame*-⋯ F₀ˢ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₁ ⊗ (` 0F)) ⊗ e₁′) ≡ argˢ ⋯ νσ b₁ b₂ σ
  → F₂ ≡ frame*-⋯ F₀ᴿ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₂ ⊗ (` 1F)) ⊗ e₂′) ≡ argᴿ ⋯ νσ b₁ b₂ σ
  → P₁ ≡ U[ Pr ] (νσ b₁ b₂ σ)
  → Σ[ P′ ∈ T.Proc m ] Σ[ Q′ ∈ U.Proc n ]
      ( Star TR._─→ₚ_
          (T.ν (b₁ ∷ []) (b₂ ∷ [])
            (T.⟪ F₀ˢ [ K (`select k) ·¹ argˢ ]* ⟫ T.∥ (T.⟪ F₀ᴿ [ K `branch ·¹ argᴿ ]* ⟫ T.∥ Pr))) P′ )
      × ( (U.ν (U.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫ U.∥ (U.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ U.∥ P₁)) ≡ Q′)
          Sum.⊎ (U.ν (U.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫ U.∥ (U.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ U.∥ P₁)) UR.─→ₚ Q′) )
      × (Q′ ≈ U[ P′ ] σ)
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
    Sb = (T.structBinder (suc b₁' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (suc b₂' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (T.structBinder (suc b₂' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (suc b₁' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ [])))

    ¬u0 = chanCx-¬Unr Γ′-S 0F

    ¬uxS = chanCx-¬Unr Γ′-S ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m)
    1≤c  = barevar-arg-count ¬uxS ⊢redexˢ
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
    ¬uxR = chanCx-¬Unr Γ′-S (((suc b₁' + 0) ↑ʳ w) ↑ˡ m)
    ¬uyR = chanCx-¬Unr Γ′-S posR
    1≤cᴿ = barevar-arg-count ¬uxR ⊢redexᴿ
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
      Σ[ P′ ∈ T.Proc m ] Σ[ Q′ ∈ U.Proc n ]
        ( Star TR._─→ₚ_
            (T.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
              (T.⟪ F₀ˢ [ K (`select k) ·¹ (` ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m)) ]* ⟫
               T.∥ (T.⟪ F₀ᴿ [ K `branch ·¹ (` (((suc b₁' + 0) ↑ʳ w) ↑ˡ m)) ]* ⟫ T.∥ Pr))) P′ )
        × ( (U.ν (U.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫ U.∥ (U.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ U.∥ P₁)) ≡ Q′)
            Sum.⊎ (U.ν (U.⟪ F₁ [ (e₁ ⊗ (` 0F)) ⊗ e₁′ ]* ⟫ U.∥ (U.⟪ F₂ [ `inj k ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ U.∥ P₁)) UR.─→ₚ Q′) )
        × (Q′ ≈ U[ P′ ] σ)
    finish refl refl =
      let
        νσ0 = νσ (suc b₁') (suc b₂') σ
        Vνσ0 = νσ-VSub (suc b₁') (suc b₂') σ Vσ
        P′ = T.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
               (T.⟪ F₀ˢ [ ` 0F ]* ⟫
                T.∥ (T.⟪ F₀ᴿ [ `inj k (` (Fin.suc ((b₁' + 0 ↑ʳ 0F) ↑ˡ m))) ]* ⟫ T.∥ Pr))
        step0 = TR.R-Struct (T.ν-cong T.∥-assoc)
                  (TR.R-Choice {b₁ = b₁'} {B₁ = []} {b₂ = b₂'} {B₂ = []} {P = Pr} {E₁ = F₀ˢ} {E₂ = F₀ᴿ} {i = k})
                  (T.ν-cong (Eq*.symmetric T._≋′_ T.∥-assoc)) ◅ ε
        thread₁ = cong U.⟪_⟫
          ( cong₂ _[_]* FeqS argeqS
          ■ sym (frame-plug* F₀ˢ νσ0 Vνσ0) )
        thread₂ = cong U.⟪_⟫
          ( cong₂ _[_]* FeqR (cong (`inj k) argeqR)
          ■ sym (frame-plug* F₀ᴿ νσ0 Vνσ0) )
        recon = cong U.ν (cong₂ U._∥_ thread₁ (cong₂ U._∥_ thread₂ Preq))
      in P′ , _ , step0 , Sum.inj₁ refl , ≋⇒≈ (≡→≋ recon)
