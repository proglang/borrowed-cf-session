-- | The impurity FRONT-FORCING for the reverse RU-Drop reflection: the drop
--   redex is 𝕀, so its consumed handle is ;-minimal (com-xS-min); drop-image
--   pins that handle to the head block's LAST index fromℕ b₁, hence front = last
--   ⟹ b₁ ≡ 0 (the head bind block has width 1).  This is the crux that makes
--   the reverse drop reflection well-posed (see interior-q resolution: drop is
--   impure now, so it front-confines like com/close/choice/acq).
--
--   νσᵈ is kept OPAQUE (abstract σᵈ + σᵈ≡) to avoid a --rewriting normalization
--   blowup on `arg ⋯ νσᵈ`; transported to the applied form νσᵈ … xx only at the
--   drop-image call.
module BorrowedCF.Simulation.Backward.DropGo where
open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open import BorrowedCF.Context using (Ctx; Struct; _⸴*_)
open import BorrowedCF.Reduction.Base using (ChanCx; Frame*; _[_]*; ⊢[]*⁻¹)
open import BorrowedCF.Simulation.Support.ReverseInv using (close-arg-var)
open import BorrowedCF.Simulation.Backward.Drop using (νσᵈ; drop-arg-decomp; drop-image)
open import BorrowedCF.Simulation.Support.RevDropConfine using (before-drop-binderᴸ; count-handle-groupᴸ; head-block-NoAcq)
open import BorrowedCF.Simulation.Support.RevComConfine using (frames-𝕀; com-xS-min)
open import BorrowedCF.Simulation.Support.RevGrindA using (barevar-arg-count; choice-¬before; 𝕀≤⇒≡𝕀)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe using (¬mobile-of)
open import BorrowedCF.Types using (Mobile; unr⇒mobile)
open import BorrowedCF.Processes.Typed using (bindCtx′⇒chanCtx; cons-ret/acq)
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Base using (_↑ˡ_; fromℕ)
open import Data.Fin.Properties using (toℕ-fromℕ; splitAt-↑ˡ)
open import Data.Sum using ([_,_]′)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Context.Base using (_∥_)
open import BorrowedCF.Processes.Typed using (structBinder)
open TP using (inv-⟪⟫; inv-∥; inv-ν)
open import Relation.Nullary using (yes; no)
open Fin.Patterns
pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

drop-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu aa ϵ}
  → Γ ; α ⊢ K `drop ∶ T ⟨ aa ⟩→ Uu ∣ ϵ → Arr.eff aa ≡ 𝕀
drop-fn-eff-𝕀 (T-Const `drop) = refl
drop-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = drop-fn-eff-𝕀 d
drop-fn-eff-𝕀 (T-Weaken _ d) = drop-fn-eff-𝕀 d

drop-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `drop ·¹ arg ∶ Uu ∣ ϵ → ϵ ≡ 𝕀
drop-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-fn-eff-𝕀 ⊢fn) ≤ₐ)
drop-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-fn-eff-𝕀 ⊢fn) ≤ₐ)
drop-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-app-𝕀 d) ≤)
drop-app-𝕀 (T-Weaken _ d) = drop-app-𝕀 d

drop-front-force :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ c b₂ : ℕ)
    (σᵈ : (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m) →ₛ (3 + n))
    (σᵈ≡ : σᵈ ≡ νσᵈ b₁ c b₂ σ)
    {F₀ : Frame* (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m)}
    {arg : Tm (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m)}
    {P₀ᵣ : TP.Proc (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m)}
    {a : Tm (3 + n)} {xd : 𝔽 (2 + n)}
  → Γ ; g ⊢ₚ TP.ν (suc b₁ ∷ c ∷ []) (b₂ ∷ [])
        (TP.⟪ F₀ [ K `drop ·¹ arg ]* ⟫ TP.∥ P₀ᵣ)
  → 𝓒[ a × Fin.suc xd × ` 0F ] ≡ arg ⋯ σᵈ
  → b₁ ≡ 0
drop-front-force {m} {n} σ Vσ {Γ} Γ-S {g} b₁ c b₂ σᵈ σᵈ≡ {F₀} {arg} {P₀ᵣ} ⊢P argeq
  with Γ₁ , Γ₂ , s' , p' , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with α , β , ≼₁ , ⊢Pt , ⊢Pr ← inv-∥ ⊢body
  with 𝒫 , γr , _ , _ , _ , _ , ≼F , _ , _ , ⊢F , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `drop ·¹ arg) (inv-⟪⟫ ⊢Pt)
  with β' , Rt , ϵ' , ret≃ , ⊢argty ← drop-arg-decomp ⊢redex
  with xx , refl ← close-arg-var arg ⊢argty ret≃ σᵈ (sym argeq)
  with hdl≡ ← drop-image b₁ c b₂ σ Vσ xx (argeq ■ cong (λ f → f xx) σᵈ≡)
  with refl ← drop-app-𝕀 ⊢redex
  with refl , lp ← frames-𝕀 ⊢F
  with cons-ret/acq s₁ s≃ Γ≗ headBC tailBC ← C
  = case-b₁
  where
    ¬mob-at : (i : 𝔽 (suc b₁))
            → ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) (((i ↑ˡ (c + 0)) ↑ˡ (b₂ + 0)) ↑ˡ m))
    ¬mob-at i = ¬mobile-of look (head-block-NoAcq Nnew s≃ headBC i)
      where
        look : ((Γ₁ ⸴* Γ₂) ⸴* Γ) (((i ↑ˡ (c + 0)) ↑ˡ (b₂ + 0)) ↑ˡ m)
             ≡ ⟨ proj₁ (bindCtx′⇒chanCtx headBC i) ⟩
        look = cong [ _ , _ ]′ (splitAt-↑ˡ (suc b₁ + (c + 0) + (b₂ + 0)) ((i ↑ˡ (c + 0)) ↑ˡ (b₂ + 0)) m)
             ■ cong [ _ , _ ]′ (splitAt-↑ˡ (suc b₁ + (c + 0)) (i ↑ˡ (c + 0)) (b₂ + 0))
             ■ sym (Γ≗ (i ↑ˡ (c + 0)))
             ■ cong [ _ , _ ]′ (splitAt-↑ˡ (suc b₁) i (c + 0))
             ■ proj₂ (bindCtx′⇒chanCtx headBC i)
    ¬uxS : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) xx)
    ¬uxS = subst (λ h → ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) h)) (sym hdl≡) (¬mob-at (fromℕ b₁))
    ¬u0 : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ) 0F)
    ¬u0 = ¬mob-at 0F
    Sb : Struct (suc (b₁ + (c + 0) + (b₂ + 0) + m))
    Sb = (structBinder (suc b₁ ∷ c ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (b₂ + 0) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
       ∥ (structBinder (b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (suc b₁ + (c + 0)) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
       ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (suc b₁ + (c + 0) + (b₂ + 0)))
    contra : b₁ ≢ 0 → ⊥
    contra b₁≢0 = com-xS-min {γinner = Sb} {xS = xx} {y = 0F} ¬uxS ¬u0 lp ≼F ≼₁
                    (subst (λ h → count h Sb ≡ 1) (sym hdl≡)
                       (count-handle-groupᴸ (suc b₁ ∷ c ∷ []) (b₂ ∷ []) g (fromℕ b₁ ↑ˡ (c + 0))))
                    (subst (λ h → before 0F h Sb) (sym hdl≡)
                       (before-drop-binderᴸ b₁ c b₂ g (fromℕ b₁)
                          (λ e → b₁≢0 (sym (toℕ-fromℕ b₁) ■ e))))
                    (barevar-arg-count (¬uxS ∘ unr⇒mobile) ⊢redex)
                    (choice-¬before ¬uxS ¬u0 ⊢redex)
    case-b₁ : b₁ ≡ 0
    case-b₁ with b₁ Nat.≟ 0
    ... | yes p = p
    ... | no ¬p = ⊥-elim (contra ¬p)
