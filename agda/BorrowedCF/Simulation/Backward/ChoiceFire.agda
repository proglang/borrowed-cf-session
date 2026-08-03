-- | Backward R-Choice FIRE+RECONCILE engine for the ALREADY-FRONT-FORCED,
--   multi-block redex, plus the collapse-reshape dispatch wrapper.  Twin of
--   ComFire, but DRASTICALLY simpler: R-Choice does NOT consume the channels
--   (contractum keeps the SAME bind groups), so there is NO wkₚ weakening, NO
--   strengthening, NO linearity counting — just fire R-Choice under a `∥-assoc`
--   R-Struct and reconcile with ChoiceReconcile.choice-back.
module BorrowedCF.Simulation.Backward.ChoiceFire where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import BorrowedCF.Simulation.Backward.ComReconcile   as CR
open import BorrowedCF.Simulation.Backward.ChoiceReconcile using (choice-back)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.Support.Frames using (frame*-⋯; ++ₛ-VSub)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (VSub-canonₛ)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (leafσ)
open import BorrowedCF.Simulation.Support.Theorems.PhiTel using (Btel; _++Φ_)
open import BorrowedCF.Reduction.Base using (value-⋯; V-K; V-`)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-↑ˡ; toℕ-↑ʳ)
open import BorrowedCF.Processes.Translation using (syncs)

open TP using (BindGroup)
open Fin.Patterns

-- VSub of the leaf substitution (identical to Com.Vτ-of; select/recv-agnostic).
Vτ-of : ∀ {m n} (σ : m →ₛ n) → VSub σ → (BL BR : BindGroup) → VSub (leafσ σ BL BR)
Vτ-of σ Vσ BL BR =
  ++ₛ-VSub
    (++ₛ-VSub
      (λ i → value-⋯ (VSub-canonₛ BL (K `unit , 0F , K `unit) (V-K , V-K) i)
                (weaken* ⦃ Kᵣ ⦄ (syncs BR)) (λ _ → V-`))
      (VSub-canonₛ BR (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs BL) 1F , K `unit) (V-K , V-K)))
    (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
              (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
              (weaken* ⦃ Kᵣ ⦄ (syncs BL)) (λ _ → V-`))
              (weaken* ⦃ Kᵣ ⦄ (syncs BR)) (λ _ → V-`))

choice-fire : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) (k : Side)
    {F₀ˢ F₀ᴿ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
    {Pr : TP.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
    {F₁ F₂ : Frame* (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
    {v₁ v₂ : Tm (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
    {P₁ : UP.Proc (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
  → F₁ ≡ frame*-⋯ F₀ˢ (CR.τ σ Vσ b₁ b₂ B₁ B₂) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
  → v₁ ≡ (` 0F) ⋯ CR.τ σ Vσ b₁ b₂ B₁ B₂
  → F₂ ≡ frame*-⋯ F₀ᴿ (CR.τ σ Vσ b₁ b₂ B₁ B₂) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
  → v₂ ≡ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ⋯ CR.τ σ Vσ b₁ b₂ B₁ B₂
  → P₁ ≡ U[ Pr ] (CR.τ σ Vσ b₁ b₂ B₁ B₂)
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` 0F) ]* ⟫
           TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
            (UP.⟪ F₁ [ v₁ ]* ⟫ UP.∥ (UP.⟪ F₂ [ `inj k v₂ ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ )
choice-fire {m} {n} σ Vσ b₁ b₂ B₁ B₂ k {F₀ˢ} {F₀ᴿ} {Pr} {F₁} {F₂} {v₁} {v₂} {P₁}
            FeqS argeqS FeqR argeqR Preq =
  P′ , step , bis
  where
    posR : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    posR = wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)

    P′ : TP.Proc m
    P′ = TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
           ((TP.⟪ F₀ˢ [ ` 0F ]* ⟫ TP.∥ TP.⟪ F₀ᴿ [ `inj k (` posR) ]* ⟫) TP.∥ Pr)

    step : Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
             (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` 0F) ]* ⟫
              TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` posR) ]* ⟫ TP.∥ Pr))) P′
    step = TR.R-Struct (TP.ν-cong TP.∥-assoc)
             (TR.R-Choice {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂} {P = Pr} F₀ˢ F₀ᴿ k)
             ε ◅ ε

    align : UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
              (UP.⟪ F₁ [ v₁ ]* ⟫ UP.∥ (UP.⟪ F₂ [ `inj k v₂ ]* ⟫ UP.∥ P₁)))
          ≡ UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
              ( UP.⟪ frame*-⋯ F₀ˢ (CR.τ σ Vσ b₁ b₂ B₁ B₂) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
                       [ (` 0F) ⋯ CR.τ σ Vσ b₁ b₂ B₁ B₂ ]* ⟫
                UP.∥ ( UP.⟪ frame*-⋯ F₀ᴿ (CR.τ σ Vσ b₁ b₂ B₁ B₂) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
                         [ (`inj k (` posR)) ⋯ CR.τ σ Vσ b₁ b₂ B₁ B₂ ]* ⟫
                  UP.∥ U[ Pr ] (CR.τ σ Vσ b₁ b₂ B₁ B₂) ) ))
    align = cong (λ Z → UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂) Z))
              (cong₂ UP._∥_
                (cong₂ (λ F v → UP.⟪ F [ v ]* ⟫) FeqS argeqS)
                (cong₂ UP._∥_
                  (cong₂ (λ F v → UP.⟪ F [ `inj k v ]* ⟫) FeqR argeqR)
                  Preq))

    bis : UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
            (UP.⟪ F₁ [ v₁ ]* ⟫ UP.∥ (UP.⟪ F₂ [ `inj k v₂ ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ
    bis = ≋⇒≈ (≡→≋ align ◅◅ choice-back σ Vσ b₁ b₂ B₁ B₂ F₀ˢ F₀ᴿ (` 0F) (`inj k (` posR)) Pr)

------------------------------------------------------------------------
-- choice-fire-dispatch : reshape wrapper.  Takes the abstract bind groups
-- BL BR with the collapse equations (BL ≡ suc b₁ ∷ B₁, refl-matched) and the two
-- front-located handle toℕ facts, and delegates to choice-fire.  Twin of
-- com-fire-dispatch, minus the ⊢P reshaping (choice-fire needs no typing).
------------------------------------------------------------------------

choice-fire-dispatch : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    {BL BR : BindGroup}
    (BLeq : BL ≡ suc b₁ ∷ B₁) (BReq : BR ≡ suc b₂ ∷ B₂)
    (k : Side)
    {F₀ˢ F₀ᴿ : Frame* (sum BL + sum BR + m)}
    {Pr : TP.Proc (sum BL + sum BR + m)}
    {xS xR : 𝔽 (sum BL + sum BR + m)}
    (xStoℕ : Fin.toℕ xS ≡ 0)
    (xRtoℕ : Fin.toℕ xR ≡ sum BL)
    {Φ : UR.Φ* (2 + n) (syncs BR + (syncs BL + (2 + n)))}
    {F₁ F₂ : Frame* (syncs BR + (syncs BL + (2 + n)))}
    {e₁ e₁′ e₂ e₂′ : Tm (syncs BR + (syncs BL + (2 + n)))}
    {P₁ : UP.Proc (syncs BR + (syncs BL + (2 + n)))}
  → Φ ≡ Btel BL (K `unit , 0F , K `unit) ++Φ Btel BR (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs BL) 1F , K `unit)
  → F₁ ≡ frame*-⋯ F₀ˢ (leafσ σ BL BR) (Vτ-of σ Vσ BL BR)
  → UR.𝓒[ e₁ × UR.wkΦ Φ 0F × e₁′ ] ≡ (` xS) ⋯ leafσ σ BL BR
  → F₂ ≡ frame*-⋯ F₀ᴿ (leafσ σ BL BR) (Vτ-of σ Vσ BL BR)
  → UR.𝓒[ e₂ × UR.wkΦ Φ 1F × e₂′ ] ≡ (` xR) ⋯ leafσ σ BL BR
  → P₁ ≡ U[ Pr ] (leafσ σ BL BR)
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_ (TP.ν BL BR
          (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` xS) ]* ⟫
           TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` xR) ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UR.plugΦ Φ (UP.⟪ F₁ [ UR.𝓒[ e₁ × UR.wkΦ Φ 0F × e₁′ ] ]* ⟫
             UP.∥ (UP.⟪ F₂ [ `inj k UR.𝓒[ e₂ × UR.wkΦ Φ 1F × e₂′ ] ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ )
choice-fire-dispatch {m} {n} σ Vσ b₁ b₂ B₁ B₂ refl refl k
    {F₀ˢ} {F₀ᴿ} {Pr} {xS} {xR} xStoℕ xRtoℕ {Φ} {F₁} {F₂} {e₁} {e₁′} {e₂} {e₂′} {P₁}
    Φeq FeqS argeqS FeqR argeqR Preq =
  P′ , step′ , bis′
  where
    posR : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    posR = wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)
    xS0 : xS ≡ 0F
    xS0 = toℕ-injective xStoℕ
    toℕ-posR : Fin.toℕ posR ≡ suc b₁ + sum B₁
    toℕ-posR = toℕ-↑ˡ (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F) m
             ■ toℕ-↑ʳ (suc b₁ + sum B₁) 0F ■ +-identityʳ (suc b₁ + sum B₁)
    xRP : xR ≡ posR
    xRP = toℕ-injective (xRtoℕ ■ sym toℕ-posR)

    argeqS′ = subst (λ v → UR.𝓒[ e₁ × UR.wkΦ Φ 0F × e₁′ ] ≡ (` v) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) xS0 argeqS
    argeqR′ = subst (λ v → UR.𝓒[ e₂ × UR.wkΦ Φ 1F × e₂′ ] ≡ (` v) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) xRP argeqR
    argeqS″ = subst (λ ϕ → UR.𝓒[ e₁ × UR.wkΦ ϕ 0F × e₁′ ] ≡ (` 0F) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) Φeq argeqS′
    argeqR″ = subst (λ ϕ → UR.𝓒[ e₂ × UR.wkΦ ϕ 1F × e₂′ ] ≡ (` posR) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) Φeq argeqR′

    result = choice-fire σ Vσ b₁ b₂ B₁ B₂ k {F₀ˢ} {F₀ᴿ} {Pr} FeqS argeqS″ FeqR argeqR″ Preq
    P′   = proj₁ result
    step = proj₁ (proj₂ result)
    bis  = proj₂ (proj₂ result)

    step′ : Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` xS) ]* ⟫
               TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` xR) ]* ⟫ TP.∥ Pr))) P′
    step′ = subst (λ v → Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
                (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` v) ]* ⟫
                 TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` xR) ]* ⟫ TP.∥ Pr))) P′) (sym xS0)
              (subst (λ v → Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
                (TP.⟪ F₀ˢ [ K (`select k) ·¹ (` 0F) ]* ⟫
                 TP.∥ (TP.⟪ F₀ᴿ [ K `branch ·¹ (` v) ]* ⟫ TP.∥ Pr))) P′) (sym xRP) step)

    bis′ = subst (λ ϕ → UP.ν (UR.plugΦ ϕ
             (UP.⟪ F₁ [ UR.𝓒[ e₁ × UR.wkΦ ϕ 0F × e₁′ ] ]* ⟫
              UP.∥ (UP.⟪ F₂ [ `inj k UR.𝓒[ e₂ × UR.wkΦ ϕ 1F × e₂′ ] ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ)
             (sym Φeq) bis
