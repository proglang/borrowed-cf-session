module BorrowedCF.Simulation.DiscardProbe where

-- MACHINE EVIDENCE for the RU-Discard admin classification.
--
-- A discard redex on an AMBIENT (σ-substituted) handle is reachable in a
-- well-typed image:  Γ = (x : ⟨skip⟩),  P = ⟪ K `discard ·¹ ` x ⟫  is
-- well-typed, and U[ P ] σ fires RU-Discard for any VSub σ.  The typed side
-- has NO matching rule (R-Discard is ν-level and consumes a BINDER handle;
-- ⟪ discard · x ⟫ alone has no typed step, and ≋ preserves thread contents),
-- so the strict "typed step matches" reading of sim← is refutable at
-- RU-Discard.  Hence RU-Discard is classified ADMINISTRATIVE (RevAdmin
-- a-discard): a silent GC of a spent ⟨skip⟩ handle, absorbed by ≈.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open T using (_;_⊢ₚ_)
open Fin.Patterns

Γ₁ : Ctx 1
Γ₁ x = ⟨ skip ⟩

Γ₁-chan : ChanCx Γ₁
Γ₁-chan x = skip , refl

P₁ : T.Proc 1
P₁ = T.⟪ K `discard ·¹ (` 0F) ⟫

σ₁ : 1 →ₛ 0
σ₁ x = K `unit

Vσ₁ : VSub σ₁
Vσ₁ x = V-K

-- the configuration is well-typed …
⊢P₁ : Γ₁ ; (Struct.[] Struct.∥ Struct.` 0F) ⊢ₚ P₁
⊢P₁ = T.TP-Expr
  (T-AppUnr refl ℙ≤ϵ
    (T-Conv ≃-refl ℙ≤ϵ (T-Const `discard))
    (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)))

-- … and its image fires RU-Discard with no binder in sight.
step₁ : U[ P₁ ] σ₁ UR.─→ₚ U.⟪ * ⟫
step₁ = UR.RU-Discard [] V-K
