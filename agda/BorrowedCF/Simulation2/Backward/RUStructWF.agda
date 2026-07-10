-- | Measure foundations for the WF per-generator RU-Struct dispatch.
--
--   The reflectors (RUStructDispatch, PhiCommReflect, EscapeReflect) reflect the
--   RU-Struct case by firing a TRANSPORTED reduction on the strict image via a
--   supplied `rec`.  To wire this into a WELL-FOUNDED sim←ᵍ (no TERMINATING
--   pragma) the transported reduction's measure ∣_∣ must be shown to descend.
--   Two facts suffice:
--
--   • ∣-red  : renaming a reduction (red-⋯ₚ) preserves ∣_∣ — it maps every
--              constructor to the same constructor.
--   • ∣-subst: transporting a reduction along a proc-index equality preserves
--              ∣_∣ (J on the equality).
module BorrowedCF.Simulation2.Backward.RUStructWF where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevCongStrong using (∣_∣)
open import BorrowedCF.Simulation.RedRename using (red-⋯ₚ)

open UR using (_─→ₚ_; RU-Exp; RU-Fork; RU-New; RU-LSplit; RU-RSplit; RU-Drop;
               RU-Discard; RU-Acquire; RU-Close; RU-Com; RU-Choice;
               RU-Par; RU-Par-right; RU-Res; RU-Sync; RU-Struct)

-- Transport of a reduction along index equalities preserves ∣_∣.
∣-subst : {R R′ Q Q′ : UP.Proc n} (e₁ : R ≡ R′) (e₂ : Q ≡ Q′)
        → (r : R ─→ₚ Q) → ∣ subst₂ _─→ₚ_ e₁ e₂ r ∣ ≡ ∣ r ∣
∣-subst refl refl r = refl

∣-subst₁ : {R Q Q′ : UP.Proc n} (e : Q ≡ Q′)
         → (r : R ─→ₚ Q) → ∣ subst (R ─→ₚ_) e r ∣ ≡ ∣ r ∣
∣-subst₁ refl r = refl

∣-substL : {R R′ Q : UP.Proc n} (e : R ≡ R′)
         → (r : R ─→ₚ Q) → ∣ subst (_─→ₚ Q) e r ∣ ≡ ∣ r ∣
∣-substL refl r = refl

-- Renaming a reduction preserves ∣_∣ (red-⋯ₚ is a constructor homomorphism).
∣-red : {R Q : UP.Proc m} (ρ : m →ᵣ n) (r : R ─→ₚ Q)
      → ∣ red-⋯ₚ ρ r ∣ ≡ ∣ r ∣
∣-red ρ (RU-Exp red)      = refl
∣-red ρ (RU-Par r)        = cong suc (∣-red ρ r)
∣-red ρ (RU-Par-right r)  = cong suc (∣-red ρ r)
∣-red ρ (RU-Res r)        = cong suc (∣-red (ρ ↑* 2) r)
∣-red ρ (RU-Sync r)       = cong suc (∣-red (ρ ↑) r)
∣-red ρ (RU-Struct c₁ r c₂) = cong suc (∣-red ρ r)
∣-red ρ (RU-Discard F V)    = ∣-subst _ _ (RU-Discard _ _)
∣-red ρ (RU-Fork F V)       = ∣-subst _ _ (RU-Fork _ _)
∣-red ρ (RU-New F)          = ∣-subst _ _ (RU-New _)
∣-red ρ (RU-LSplit F)       = ∣-subst _ _ (RU-LSplit _)
∣-red ρ (RU-RSplit F)       = ∣-subst _ _ (RU-RSplit _)
∣-red ρ (RU-Drop F)         = ∣-subst _ _ (RU-Drop _)
∣-red ρ (RU-Acquire F)      = ∣-subst _ _ (RU-Acquire _)
∣-red ρ (RU-Close F₁ F₂)    = ∣-subst _ _ (RU-Close _ _)
∣-red ρ (RU-Com F₁ F₂ V)    = ∣-subst _ _ (RU-Com _ _ _)
∣-red ρ (RU-Choice F₁ F₂ k) = ∣-subst _ _ (RU-Choice _ _ k)
