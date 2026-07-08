-- | Backward simulation — thread-level leaf reflections (RU-Exp/Fork/New).
--
--   Each reflects a single untyped thread step back to a typed step, producing
--   the backward codomain  Σ P′. P ─→ₚ* P′ × Q ≈ U[ P′ ] σ.  These are the
--   image-refl (ε-prefix) cases; they need no recursion.
module BorrowedCF.Simulation2.Backward.Leaf where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation2.Backward.Inversions using (inv-U-⟪⟫)
open import BorrowedCF.Simulation.ReverseInv using (⋯→-reflect; frameApp-reflect; value-⋯⁻¹)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-refl; ≋⇒≈)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open TP using (_;_⊢ₚ_; inv-⟪⟫)

-- RU-Exp: a translated thread ⟪e₀⋯σ⟫ steps by an expression reduction; reflect
-- the substituted step back to a source step (typing rules out a VSub creating
-- a head redex at a channel var).
bwd-exp : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
        → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
        → {e₁ e₂ : Tm n} → U[ P ] σ ≡ UP.⟪ e₁ ⟫ → e₁ ⋯→ e₂
        → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × UP.⟪ e₂ ⟫ ≈ U[ P′ ] σ)
bwd-exp σ Vσ Γ-S {P = P} ⊢P eq step
  with e₀ , refl , refl ← inv-U-⟪⟫ P σ eq
  with e₀′ , s , refl ← ⋯→-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ step =
  TP.⟪ e₀′ ⟫ , TR.R-Exp s ◅ ε , ≈-refl


-- RU-Fork: reflect a translated fork redex; frameApp-reflect recovers the
-- source frame + argument, fire R-Fork, reconcile via frame-plug*.
bwd-fork : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
         → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
         → {F : Frame* n} {e : Tm n} (V : Value e)
         → U[ P ] σ ≡ UP.⟪ F [ K `fork ·¹ e ]* ⟫
         → Σ[ P′ ∈ TP.Proc m ]
             (Star TR._─→ₚ_ P P′ × (UP.⟪ F [ * ]* ⟫ UP.∥ UP.⟪ e ·¹ * ⟫) ≈ U[ P′ ] σ)
bwd-fork σ Vσ Γ-S {P = P} ⊢P {F} {e} V eq
  with e₀ , refl , feq ← inv-U-⟪⟫ P σ eq
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ `fork F (sym feq) =
  TP.⟪ F₀ [ K `unit ]* ⟫ TP.∥ TP.⟪ arg₀ ·¹ K `unit ⟫
  , TR.R-Fork F₀ (value-⋯⁻¹ σ Vσ arg₀ (subst Value argeq V)) ◅ ε
  , ≋⇒≈ (≡→≋ (cong₂ UP._∥_
      (cong UP.⟪_⟫ (cong (_[ K `unit ]*) Feq ■ sym (frame-plug* F₀ σ Vσ)))
      (cong (λ z → UP.⟪ z ·¹ K `unit ⟫) argeq)))
