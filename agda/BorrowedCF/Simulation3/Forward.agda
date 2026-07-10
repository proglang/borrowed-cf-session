-- | FORWARD simulation — the CLEAN statement.
--
--   Every typed process step is simulated by exactly ONE untyped step of the
--   translation.  This single-step form is available because acquire is now
--   ATOMIC (RU-Acquire consumes the sync cell and substitutes in one step — no
--   `done` flag, no RU-Cleanup), so no typed rule expands to two untyped steps,
--   and the φ-nest transposes are absorbed into RU-Struct (itself one ─→ₚ).
--
--   sim→ is assembled in this module by dispatch; each channel-op case is
--   proved in its own BorrowedCF.Simulation3.Forward.<Op> module.
module BorrowedCF.Simulation3.Forward where

open import BorrowedCF.Simulation3.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

Forward-Sim : Set
Forward-Sim =
  ∀ {m} {n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
  → {P′ : TP.Proc m} → P TR.─→ₚ P′
  → U[ P ] σ UR.─→ₚ U[ P′ ] σ

-- Done leaf cases (re-exported; wired the moment the module lands):
open import BorrowedCF.Simulation3.Forward.Fork  using (U-fork)  public
open import BorrowedCF.Simulation3.Forward.New   using (U-new)   public
open import BorrowedCF.Simulation3.Forward.Close  using (U-close)  public
open import BorrowedCF.Simulation3.Forward.Com    using (U-com)    public
open import BorrowedCF.Simulation3.Forward.Choice  using (U-choice)  public
open import BorrowedCF.Simulation3.Forward.LSplit  using (U-lsplit→)  public
open import BorrowedCF.Simulation3.Forward.RSplit  using (U-rsplit→)  public
open import BorrowedCF.Simulation3.Forward.Discard using (U-discard)  public
open import BorrowedCF.Simulation3.Forward.Drop    using (U-drop→)   public
open import BorrowedCF.Simulation3.Forward.Acq     using (U-acq→)    public
open import BorrowedCF.Simulation3.Support.Frames using (⋯→-⋯ₛ; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation3.Support.Congruence using (U-≋)
open import BorrowedCF.Simulation3.Support.TranslationProperties using (UB-cong-─→)
open TP using (⊢-≋)

-- ── sim→ WIRING MAP (every typed constructor MUST be dispatched here; Agda's
--    coverage checker enforces completeness when sim→ is assembled) ──
--   R-Exp     → RU-Exp (⋯→-⋯ₛ)              inline
--   R-Fork    → U-fork                        DONE
--   R-New     → U-new                         DONE (untyped RU-New swap)
--   R-Close   → U-close                       DONE
--   R-Par     → RU-Par (sim→ …)               inline (recursive)
--   R-Bind    → RU-Res (UB-cong-─→ … sim→)    inline (recursive)
--   R-Struct  → RU-Struct (U-≋ …) (sim→ …)    inline (recursive)
--   R-Com     → U-com                         DONE
--   R-Choice  → U-choice                      DONE
--   R-LSplit  → U-lsplit→                     DONE
--   R-RSplit  → U-rsplit→                     DONE
--   R-Drop    → U-drop→                       DONE
--   R-Acq     → U-acq→                        DONE (atomic single-step)
--   R-Discard → U-discard                     DONE

-- sim→ : the assembled dispatcher — TOTAL coverage (all 14 typed constructors).
-- 13 cases proved; R-Acq is a single interaction hole pending the Acq lemma.
sim→ : Forward-Sim
sim→ σ Vσ Γ-S ⊢P (TR.R-Exp x)          = UR.RU-Exp (⋯→-⋯ₛ σ Vσ x)
sim→ σ Vσ Γ-S ⊢P (TR.R-Fork E V)       = U-fork σ Vσ {E = E} V
sim→ σ Vσ Γ-S ⊢P (TR.R-New E)          = U-new σ Vσ {E = E}
sim→ σ Vσ Γ-S ⊢P (TR.R-Com {E₁ = E₁} {E₂ = E₂} V) = U-com σ Vσ Γ-S {E₁ = E₁} {E₂ = E₂} V ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-Choice E₁ E₂ i) = U-choice σ Vσ Γ-S {i = i} {E₁ = E₁} {E₂ = E₂} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-LSplit {E = E}) = U-lsplit→ σ Vσ Γ-S {E = E} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-RSplit {E = E}) = U-rsplit→ σ Vσ Γ-S {E = E} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-Drop {E = E})   = U-drop→ σ Vσ Γ-S {E = E} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-Acq {E = E})    = U-acq→ σ Vσ Γ-S {E = E} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-Close {E₁ = E₁} {E₂ = E₂}) = U-close σ Vσ {E₁ = E₁} {E₂ = E₂}
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {E = E}) = U-discard σ Vσ Γ-S {E = E} ⊢P
sim→ σ Vσ Γ-S ⊢P (TR.R-Par red) with inv-∥ ⊢P
... | _ , _ , _ , p , _ = UR.RU-Par (sim→ σ Vσ Γ-S p red)
sim→ σ Vσ Γ-S ⊢P (TR.R-Bind {B₁} {B₂} red) with inv-ν ⊢P
... | _ , _ , _ , _ , _ , _ , _ , C , C′ , ⊢Q =
  UR.RU-Res (UB-cong-─→ B₁ (* , 0F , *) (V-K , V-K)
    (λ σ₁ Vσ₁ → UB-cong-─→ B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *) (V-K , V-K)
      (λ σ₂ Vσ₂ → sim→ _
        (++ₛ-VSub (++ₛ-VSub (weaken-VSub (syncs B₂) Vσ₁) Vσ₂)
          (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ))))
        (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) ⊢Q red)))
sim→ σ Vσ Γ-S ⊢P (TR.R-Struct e r e′) =
  UR.RU-Struct (U-≋ σ e) (sim→ σ Vσ Γ-S (⊢-≋ Γ-S e ⊢P) r) (U-≋ σ e′)
