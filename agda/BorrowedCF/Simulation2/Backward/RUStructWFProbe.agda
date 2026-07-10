-- Probe: measure-carrying νswap-reflect. Tests whether the reflector's rec call
-- can be threaded with a WF measure bound (∣_∣ < N) using RUStructWF's ∣-red /
-- ∣-subst lemmas, so that wiring rec = sim←ᵍ refl gives a NON-pragma WF recursion.
module BorrowedCF.Simulation2.Backward.RUStructWFProbe where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RedRename using (red-⋯ₚ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-trans; ≋⇒≈)
open import BorrowedCF.Simulation.RevCongStrong using (∣_∣)
open import BorrowedCF.Simulation2.Backward.RUStructDispatch using (Res; swapₚ-invU)
open import BorrowedCF.Simulation2.Backward.RUStructWF using (∣-red; ∣-substL)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Nat using (_<_)

open Fin.Patterns

-- measure of the reduction the reflector fires on rec.
νswap-fire-∣ : ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → {body : UP.Proc (2 + n)} (imgeq : U[ P ] σ ≡ UP.ν body)
  → {T : UP.Proc (2 + n)} (sub : (body UP.⋯ₚ swapᵣ 1 1) UR.─→ₚ T)
  → ∣ subst (λ Z → Z UR.─→ₚ UP.ν (T UP.⋯ₚ swapᵣ 1 1)) (sym imgeq)
        (UR.RU-Res (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ swapᵣ 1 1)) (swapₚ-invU body)
                          (red-⋯ₚ (swapᵣ 1 1) sub))) ∣
    ≡ suc ∣ sub ∣
νswap-fire-∣ σ {P} imgeq {T} sub =
  ∣-substL (sym imgeq) (UR.RU-Res _)
  ■ cong suc (∣-substL (swapₚ-invU _) (red-⋯ₚ (swapᵣ 1 1) sub) ■ ∣-red (swapᵣ 1 1) sub)

νswap-reflect-m :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m} {N : ℕ}
  → (rec : ∀ {Q′} (r : U[ P ] σ UR.─→ₚ Q′) → ∣ r ∣ < N → Res σ P Q′)
  → {body : UP.Proc (2 + n)}
  → (imgeq : U[ P ] σ ≡ UP.ν body)
  → {T : UP.Proc (2 + n)}
  → (sub : (body UP.⋯ₚ swapᵣ 1 1) UR.─→ₚ T)
  → suc ∣ sub ∣ < N
  → Res σ P (UP.ν T)
νswap-reflect-m σ {P} {N} rec {body} imgeq {T} sub bnd
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (T UP.⋯ₚ swapᵣ 1 1)) (sym imgeq)
          (UR.RU-Res (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ swapᵣ 1 1)) (swapₚ-invU body)
                            (red-⋯ₚ (swapᵣ 1 1) sub))))
        (subst (_< N) (sym (νswap-fire-∣ σ imgeq sub)) bnd)
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.return (UP.ν-swap′ {P = T}))) codom
