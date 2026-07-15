-- | Backward simulation — thread-level leaf reflections (RU-Exp/Fork/New).
--
--   Each reflects a single untyped thread step back to a typed step, producing
--   the backward codomain  Σ P′. P ─→ₚ* P′ × Q ≈ U[ P′ ] σ.  These are the
--   image-refl (ε-prefix) cases; they need no recursion.
module BorrowedCF.Simulation.Backward.Leaf where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫)
open import BorrowedCF.Simulation.Support.ReverseInv
  using (⋯→-reflect; frameApp-reflect; value-⋯⁻¹; headK; new-arg-notVar)
open import BorrowedCF.Simulation.Support.InvFrame using (strengthen-frame)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Forward.New using (rnew-bridge; tL)
open import Data.Empty using (⊥-elim)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≈-refl; ≋⇒≈)
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


-- RU-New : reflect a translated `new` redex.  frameApp-reflect recovers the
-- source frame F₀ + argument; headK/new-arg-notVar force the arg to K `unit (a
-- unit-typed source var is ruled out by ChanCx), i.e. an R-New redex.  The
-- codomain ≋ is the post-swap rnew-bridge (the two channel triples substitute
-- into the unswapped leaf tL; typed body `0F⊗`1F, matching the swapped RU-New).
bwd-new : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
        → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
        → {s : 𝕊 0} {F : Frame* n}
        → U[ P ] σ ≡ UP.⟪ F [ K (`new s) ·¹ * ]* ⟫
        → Σ[ P′ ∈ TP.Proc m ]
            (Star TR._─→ₚ_ P P′ ×
             UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
                (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫))
               ≈ U[ P′ ] σ)
bwd-new σ Vσ Γ-S {P = P} ⊢P {s = s} {F = F} eq
  with e₀ , refl , feq ← inv-U-⟪⟫ P σ eq
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ (`new s) F (sym feq)
  with headK σ arg₀ (sym argeq)
... | inj₁ (x , refl)
      with _ , (_ , _ , ⊢redex) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢P)
      = ⊥-elim (new-arg-notVar Γ-S ⊢redex)
... | inj₂ refl =
  TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
    TP.⟪ (F₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 0F) ⊗ (` 1F) ]* ⟫ ,
  TR.R-New F₀ ◅ ε ,
  ≋⇒≈ (subst (λ z → UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
                  (z ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫)) UP.≋ _)
        (sym Feq) (rnew-bridge F₀ σ Vσ))
