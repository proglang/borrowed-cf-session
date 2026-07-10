-- | Backward simulation, RU-Close.  Reflects one untyped end‼/end⁇ rendezvous
--   back to a typed R-Close step in the CLEAN single-step codomain.  Ported from
--   BorrowedCF.Simulation.Support.RevClose (close-go), with the handle front-forcing
--   (z≡0F / w≡0F) supplied by the now-compiling ¬Mobile before-ordering theory
--   (¬mobile-block-at + com-xS-min), mirroring BorrowedCF.Simulation.Support.RevChoice;
--   the old Q′/─→ᶜ? cleanup slot collapsed to the ≈-bridge.
module BorrowedCF.Simulation.Backward.Close where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; νσ-VSub; close-arg-var; frameApp-reflect; inv-U-ν-∥-shape;
         inv-ν-chanCx; ν-inj; U-ν-singleton; frame-fusion-gen; frame-cong)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (frame-plug*ᵣ)
open import BorrowedCF.Simulation.Support.RevGrindC
  using (count-handle-comᴿ; before-com-binderᴿ)
open import BorrowedCF.Simulation.Support.RevGrindA
  using (choice-¬before; barevar-arg-count; 𝕀≤⇒≡𝕀)
open import BorrowedCF.Simulation.Support.RevComConfine
  using (frames-𝕀; com-xS-min; before-com-binderᴸ; ¬mobile-block-at)
open import BorrowedCF.Simulation.Support.RevComImage
  using (com-image-block1; recv-image-block2; pos⇒suc)
open import BorrowedCF.Simulation.Support.ReverseConfine
  using (count-handle-comᴸ; close-confine; bc-len1; close-handle-end; fn-end-dom)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before)
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Types using (new-dual; unr⇒mobile)
open import BorrowedCF.Context using (Ctx; Struct; _∶_≼_; _⸴*_)
import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Sum using ([_,_]′)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-injective)
open import Data.Nat.Properties using (+-identityʳ)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

open Fin.Patterns

------------------------------------------------------------------------
-- Cancelling a 2-fold weakening on terms via a substitution retraction.
------------------------------------------------------------------------

private
  down2 : ∀ {k} → (2 + k) →ₛ k
  down2 0F            = K `unit
  down2 (Fin.suc 0F)  = K `unit
  down2 (Fin.suc (Fin.suc x)) = ` x

  roundtrip : ∀ {k} (t : Tm k) → (t ⋯ weaken* ⦃ Kᵣ ⦄ 2) ⋯ down2 ≡ t
  roundtrip t = fusion t (weaken* ⦃ Kᵣ ⦄ 2) down2 ■ ⋯-id t (λ x → refl)

cancel-wk2 : ∀ {k} (t₁ t₂ : Tm k) →
             t₁ ⋯ weaken* ⦃ Kᵣ ⦄ 2 ≡ t₂ ⋯ weaken* ⦃ Kᵣ ⦄ 2 → t₁ ≡ t₂
cancel-wk2 t₁ t₂ eq = sym (roundtrip t₁) ■ cong (_⋯ down2) eq ■ roundtrip t₂

------------------------------------------------------------------------
-- end-side typing extractors.
------------------------------------------------------------------------

ead-core : ∀ {N} {Γ : Ctx N} {α β : Struct N} {arg : Tm N} {p Targ Uu ϵ₁ ϵ₂ a}
  → Γ ; α ⊢ K (`end p) ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ arg ∶ Targ ∣ ϵ₂
  → Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ end p ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
ead-core {β = β} ⊢fn ⊢arg = β , _ , _ , fn-end-dom ⊢fn , ⊢arg

end-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {p Uu ϵ}
  → Γ ; γ ⊢ K (`end p) ·¹ arg ∶ Uu ∣ ϵ
  → Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ end p ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
end-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = ead-core ⊢fn ⊢arg
end-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = ead-core ⊢fn ⊢arg
end-arg-decomp (T-Conv _ _ d) = end-arg-decomp d
end-arg-decomp (T-Weaken _ d) = end-arg-decomp d

end-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {p T Uu a ϵ}
  → Γ ; α ⊢ K (`end p) ∶ T ⟨ a ⟩→ Uu ∣ ϵ → Arr.eff a ≡ 𝕀
end-fn-eff-𝕀 (T-Const `end) = refl
end-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = end-fn-eff-𝕀 d
end-fn-eff-𝕀 (T-Weaken _ d) = end-fn-eff-𝕀 d

end-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {p Uu ϵ}
  → Γ ; γ ⊢ K (`end p) ·¹ arg ∶ Uu ∣ ϵ → ϵ ≡ 𝕀
end-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (end-fn-eff-𝕀 ⊢fn) ≤ₐ)
end-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (end-fn-eff-𝕀 ⊢fn) ≤ₐ)
end-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (end-app-𝕀 d) ≤)
end-app-𝕀 (T-Weaken _ d) = end-app-𝕀 d

------------------------------------------------------------------------
-- close-go : the reverse RU-Close engine, clean codomain.
------------------------------------------------------------------------

close-go :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ b₂ : ℕ)
    {F₀ᴸ F₀ᴿ : Frame* (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {argᴸ argᴿ : Tm (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {F₁ F₂ : Frame* n} {e₁ e₁′ e₂ e₂′ : Tm (2 + n)}
  → Γ ; g ⊢ₚ TP.ν (b₁ ∷ []) (b₂ ∷ [])
       (TP.⟪ F₀ᴸ [ K (`end ‼) ·¹ argᴸ ]* ⟫ TP.∥ TP.⟪ F₀ᴿ [ K (`end ⁇) ·¹ argᴿ ]* ⟫)
  → (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) ≡ frame*-⋯ F₀ᴸ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₁ ⊗ (` 0F)) ⊗ e₁′) ≡ argᴸ ⋯ νσ b₁ b₂ σ
  → (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) ≡ frame*-⋯ F₀ᴿ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₂ ⊗ (` 1F)) ⊗ e₂′) ≡ argᴿ ⋯ νσ b₁ b₂ σ
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_
          (TP.ν (b₁ ∷ []) (b₂ ∷ [])
            (TP.⟪ F₀ᴸ [ K (`end ‼) ·¹ argᴸ ]* ⟫ TP.∥ TP.⟪ F₀ᴿ [ K (`end ⁇) ·¹ argᴿ ]* ⟫)) P′ )
      × ((UP.⟪ F₁ [ * ]* ⟫ UP.∥ UP.⟪ F₂ [ * ]* ⟫) ≈ U[ P′ ] σ)
close-go {m} {n} σ Vσ {Γ} Γ-S {g} b₁ b₂ {F₀ᴸ} {F₀ᴿ} {argᴸ} {argᴿ}
         {F₁} {F₂} {e₁} {e₁′} {e₂} {e₂′} ⊢P FeqL argeqL FeqR argeqR
  with Γ₁ , Γ₂ , s' , p' , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with αL , αRb , ≼₁ , ⊢PL , ⊢PR ← inv-∥ ⊢body
  with 𝒫ᴸ , γrᴸ , _ , _ , _ , _ , ≼ᴸ , _ , _ , ⊢Fᴸ , ⊢redexᴸ
       ← ⊢[]*⁻¹ F₀ᴸ (K (`end ‼) ·¹ argᴸ) (inv-⟪⟫ ⊢PL)
  with βe , Re , ϵe , end≃L , ⊢argLty ← end-arg-decomp ⊢redexᴸ
  with xL , refl ← close-arg-var argᴸ ⊢argLty end≃L (νσ b₁ b₂ σ) (sym argeqL)
  with refl ← end-app-𝕀 ⊢redexᴸ
  with refl , lpᴸ ← frames-𝕀 ⊢Fᴸ
  with z , 1≤b₁ , refl ← com-image-block1 b₁ b₂ σ Vσ xL argeqL
  with b₁' , refl ← pos⇒suc 1≤b₁
  with 𝒫ᴿ , γrᴿ , _ , _ , _ , _ , ≼ᴿ , _ , _ , ⊢Fᴿ , ⊢redexᴿ
       ← ⊢[]*⁻¹ F₀ᴿ (K (`end ⁇) ·¹ argᴿ) (inv-⟪⟫ ⊢PR)
  with βe′ , Re′ , ϵe′ , end≃R , ⊢argRty ← end-arg-decomp ⊢redexᴿ
  with xR , refl ← close-arg-var argᴿ ⊢argRty end≃R (νσ (suc b₁') b₂ σ) (sym argeqR)
  with refl ← end-app-𝕀 ⊢redexᴿ
  with refl , lpᴿ ← frames-𝕀 ⊢Fᴿ
  with w , 1≤b₂ , refl ← recv-image-block2 (suc b₁') b₂ σ Vσ xR argeqR
  with b₂' , refl ← pos⇒suc 1≤b₂
  = finish z≡0F w≡0F
  where
    Sb : Struct (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ []) + m)
    Sb = (TP.structBinder (suc b₁' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (suc b₂' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (TP.structBinder (suc b₂' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (suc b₁' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ [])))

    lookupL-z : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m) ≡ Γ₁ z
    lookupL-z = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) (z ↑ˡ (suc b₂' + 0)) m)
              ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0) z (suc b₂' + 0))
    ¬u0 = ¬mobile-block-at Nnew C 0F refl
    ¬uxL = ¬mobile-block-at Nnew C z lookupL-z
    1≤c  = barevar-arg-count (¬uxL ∘ unr⇒mobile) ⊢redexᴸ
    cnt1 = count-handle-comᴸ (suc b₁') (suc b₂') g z
    z₀   = Fin.cast (+-identityʳ (suc b₁')) z
    z₀↑0≡z : z₀ ↑ˡ 0 ≡ z
    z₀↑0≡z = toℕ-injective (toℕ-↑ˡ z₀ 0 ■ toℕ-cast (+-identityʳ (suc b₁')) z)
    contra : Fin.toℕ z₀ ≢ 0 → ⊥
    contra ne = com-xS-min ¬uxL ¬u0 lpᴸ ≼ᴸ ≼₁ cnt1
                  (subst (λ zz → before 0F ((zz ↑ˡ (suc b₂' + 0)) ↑ˡ m) Sb) z₀↑0≡z
                    (before-com-binderᴸ b₁' (suc b₂') g z₀ ne))
                  1≤c (choice-¬before ¬uxL ¬u0 ⊢redexᴸ)
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
    contraᴿ : Fin.toℕ w₀ ≢ 0 → ⊥
    contraᴿ ne = com-xS-min ¬uxR ¬uyR lpᴿ ≼ᴿ
                   (𝐂.≼-trans (𝐂.≼-refl 𝐂.∥-comm) ≼₁) cnt1ᴿ
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
              (TP.⟪ F₀ᴸ [ K (`end ‼) ·¹ (` ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m)) ]* ⟫
               TP.∥ TP.⟪ F₀ᴿ [ K (`end ⁇) ·¹ (` (((suc b₁' + 0) ↑ʳ w) ↑ˡ m)) ]* ⟫)) P′ )
        × ((UP.⟪ F₁ [ * ]* ⟫ UP.∥ UP.⟪ F₂ [ * ]* ⟫) ≈ U[ P′ ] σ)
    finish refl refl = finish₂ b₁'≡0 b₂'≡0
      where
        s₀L = proj₁ (Γ′-S 0F)
        Γ'0F≡ : ((Γ₁ ⸴* Γ₂) ⸴* Γ) 0F ≡ ⟨ s₀L ⟩
        Γ'0F≡ = proj₂ (Γ′-S 0F)
        b₁'≡0 : b₁' ≡ 0
        b₁'≡0 = bc-len1 Nnew C Γ'0F≡ (close-handle-end ⊢redexᴸ Γ'0F≡)
        s₀R = proj₁ (Γ′-S posR)
        Γ'posR≡ : ((Γ₁ ⸴* Γ₂) ⸴* Γ) posR ≡ ⟨ s₀R ⟩
        Γ'posR≡ = proj₂ (Γ′-S posR)
        Γ₂0F≡ : Γ₂ 0F ≡ ⟨ s₀R ⟩
        Γ₂0F≡ = sym lookupR ■ Γ'posR≡
        b₂'≡0 : b₂' ≡ 0
        b₂'≡0 = bc-len1 (new-dual Nnew) C′ Γ₂0F≡ (close-handle-end ⊢redexᴿ Γ'posR≡)

        finish₂ : b₁' ≡ 0 → b₂' ≡ 0 →
          Σ[ P′ ∈ TP.Proc m ]
            ( Star TR._─→ₚ_
                (TP.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
                  (TP.⟪ F₀ᴸ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
                   TP.∥ TP.⟪ F₀ᴿ [ K (`end ⁇) ·¹ (` posR) ]* ⟫)) P′ )
            × ((UP.⟪ F₁ [ * ]* ⟫ UP.∥ UP.⟪ F₂ [ * ]* ⟫) ≈ U[ P′ ] σ)
        finish₂ refl refl = P′ , step , ≋⇒≈ (≡→≋ recon)
          where
            cc = close-confine Γ-S ⊢P
            E₁ = proj₁ cc
            EeqL = proj₁ (proj₂ cc)
            E₂ = proj₁ (proj₂ (proj₂ cc))
            EeqR = proj₂ (proj₂ (proj₂ cc))
            νσ0 = νσ 1 1 σ
            Vνσ0 = νσ-VSub 1 1 σ Vσ
            P′ : TP.Proc m
            P′ = TP.⟪ E₁ [ * ]* ⟫ TP.∥ TP.⟪ E₂ [ * ]* ⟫
            srcEq = cong₂ (λ X Y → TP.ν (1 ∷ []) (1 ∷ [])
                       (TP.⟪ X [ K (`end ‼) ·¹ (` 0F) ]* ⟫ TP.∥ TP.⟪ Y [ K (`end ⁇) ·¹ (` 1F) ]* ⟫))
                       EeqL EeqR
            step0 : Star TR._─→ₚ_
                      (TP.ν (1 ∷ []) (1 ∷ [])
                        (TP.⟪ (E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) ·¹ (` 0F) ]* ⟫
                         TP.∥ TP.⟪ (E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) ·¹ (` 1F) ]* ⟫)) P′
            step0 = TR.R-Close {E₁ = E₁} {E₂ = E₂} ◅ ε
            step = subst (λ Z → Star TR._─→ₚ_ Z P′) (sym srcEq) step0
            weakenEq : (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0)
                       ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2)
            weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0) (weaken* ⦃ Kᵣ ⦄ 0)
                       ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0 ·ₖ weaken* ⦃ Kᵣ ⦄ 0)
            perF : (F : Frame m) → frame-⋯ (F ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2) νσ0 Vνσ0
                                   ≡ frame-⋯ F σ Vσ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2
            perF F = frame-fusion-gen F (λ _ → V-`) Vνσ0 (λ x → Vνσ0 (weaken* ⦃ Kᵣ ⦄ 2 x))
                   ■ frame-cong F (λ x → Vνσ0 (weaken* ⦃ Kᵣ ⦄ 2 x))
                       (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)) weakenEq
                   ■ sym (frame-fusion-gen F Vσ (λ _ → V-`)
                       (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)))
            frameEqA : (E* : Frame* m) →
                       frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) νσ0 Vνσ0
                       ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2
            frameEqA []        = refl
            frameEqA (F ∷ E*) = cong₂ _∷_ (perF F) (frameEqA E*)
            tmEq : (Fr : Frame* n) (E* : Frame* m) →
                   (Fr ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) ≡ frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) νσ0 Vνσ0 →
                   Fr [ * ]* ≡ (E* [ * ]*) ⋯ σ
            tmEq Fr E* eqF = cancel-wk2 (Fr [ * ]*) ((E* [ * ]*) ⋯ σ)
              ( frame-plug*ᵣ Fr (weaken* ⦃ Kᵣ ⦄ 2)
              ■ cong (_[ * ]*) (eqF ■ frameEqA E*)
              ■ sym (frame-plug*ᵣ (frame*-⋯ E* σ Vσ) (weaken* ⦃ Kᵣ ⦄ 2))
              ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 2) (sym (frame-plug* E* σ Vσ)) )
            recon : (UP.⟪ F₁ [ * ]* ⟫ UP.∥ UP.⟪ F₂ [ * ]* ⟫) ≡ U[ P′ ] σ
            recon = cong₂ UP._∥_
                      (cong UP.⟪_⟫ (tmEq F₁ E₁ (FeqL ■ cong (λ X → frame*-⋯ X νσ0 Vνσ0) EeqL)))
                      (cong UP.⟪_⟫ (tmEq F₂ E₂ (FeqR ■ cong (λ X → frame*-⋯ X νσ0 Vνσ0) EeqR)))

------------------------------------------------------------------------
-- close-reflect : the leaf-style RU-Close reflection.  Interface mirrors
-- Backward.LSplit.lsplit-reflect: the untyped redex is presented as the
-- equation  U[ P ] σ ≡ (RU-Close LHS); the result is the (RU-Close RHS)
-- ≈-bridged to U[ P′ ] σ.  Wired at Backward.agda:121 by
--   close-reflect σ Vσ Γ-S ⊢P (sym eq).
------------------------------------------------------------------------

close-reflect : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
              → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
              → {F₁ F₂ : Frame* n} {e₁ e₁′ e₂ e₂′ : Tm (2 + n)}
              → U[ P ] σ ≡ UP.ν
                  ( UP.⟪ (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₁′) ]* ⟫
                  UP.∥ UP.⟪ (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) ·¹ ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫ )
              → Σ[ P′ ∈ TP.Proc m ]
                  (Star TR._─→ₚ_ P P′
                   × (UP.⟪ F₁ [ * ]* ⟫ UP.∥ UP.⟪ F₂ [ * ]* ⟫) ≈ U[ P′ ] σ)
close-reflect σ Vσ Γ-S {P = P} ⊢P {F₁ = F₁} {F₂ = F₂} eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PL , PR , refl , Leq , Req ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with _ , _ , _ , ⊢PL , ⊢PR ← inv-∥ ⊢body
  with F₀ᴸ , argᴸ , refl , FeqL , argeqL
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`end ‼)
           (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (sym Leq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`end ⁇)
           (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (sym Req′)
  = close-go σ Vσ Γ-S b₁ b₂ ⊢P FeqL argeqL FeqR argeqR
