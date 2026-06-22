{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.DropWitness where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.TypedMW as RR

open Fin.Patterns
open Nat.Variables

-- R-Drop is GENUINELY TYPABLE.
--
-- `drop : <(ret)> ->1M `T | P  carries NO Mobile premise (Terms.agda:121),
-- so the ComWitness obstruction (an un-Mobile message argument) does NOT
-- apply.  The drop thread types whenever 0F's session ~= ret, a perfectly
-- valid bind-context handle.

-- A front bind group  suc b1 :: B1  with sum 1 whose single handle is <(ret)>.
sesD : 𝕊 0
sesD = ret ; skip

gD : Ctx 1
gD = ⟨ ret ⟩ F.∷ F.[]

-- The BindCtx that  TP-Res + inv-ν  expose for the drop side:
-- 0F : gD 0 = <(ret)>, exactly `drop's domain.
bcD : BindCtx {1} sesD gD
bcD = -∷ []

-- The drop thread types in body context gD, with 0F : <(ret)>.
dropExpr : gD ; ([] ∥ (` 0F)) ⊢ K `drop · (` 0F) ∶ `⊤ ∣ ℙ
dropExpr = T-AppLin refl
  (T-Const `drop)
  (T-Var 0F refl)

-- Wrapped as a typed THREAD (TP-Expr needs effect I and result `T; conv first).
⊢drop-thread : gD ; ([] ∥ (` 0F)) ⊢ₚ ⟪ K `drop · (` 0F) ⟫
⊢drop-thread = TP-Expr (T-Conv ≃-refl ℙ≤ϵ dropExpr)
