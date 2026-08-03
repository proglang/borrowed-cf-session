-- | Backward R-Choice FIRE+RECONCILE engine for the ALREADY-FRONT-FORCED,
--   multi-block redex.  Twin of ComFire.com-fire, but DRASTICALLY simpler:
--   R-Choice does NOT consume the channels (contractum keeps the SAME bind
--   groups), so there is NO wkₚ weakening, NO strengthening, NO linearity
--   counting — just fire R-Choice under a `∥-assoc` R-Struct and reconcile with
--   ChoiceReconcile.choice-back.  The select handle sits at 0F and the branch
--   handle at posR = wkʳ m (wkˡ (suc b₁ + sum B₁) 0F); the fired frames stay in
--   the leaf scope of τ = leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂).
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
open import BorrowedCF.Simulation.Support.Frames using (frame*-⋯)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Translation using (syncs)

open TP using (BindGroup)
open Fin.Patterns

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
