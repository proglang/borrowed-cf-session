{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.AcqWitness where

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

-- R-Acq is GENUINELY TYPABLE (its redex is well-typed).
--
-- `acq : <(acq ; s)> ->1M <(s)> | P  carries NO Mobile premise
-- (Terms.agda:122).  Its domain is the acq-led session itself, a perfectly
-- valid bind-context handle, so the ComWitness obstruction (an un-Mobile
-- message argument) does NOT apply.  Unlike `drop / `send / `recv (result
-- `T), `acq's result is a CHANNEL <(s)>, so the redex cannot stand alone as a
-- thread body (TP-Expr needs `T | I); the surrounding frame E continues it to
-- `T.  The load-bearing fact for vacuity is that the redex itself is typable,
-- which we witness here (mirroring ComWitness.sendExpr / recvExpr).

-- A front handle  <(acq ; ret)>  packaged as a sum-1 bind group.  (In R-Acq
-- the front group is  zero :: suc b1 :: B1; the leading 0-chain contributes
-- no handle, so 0F indexes this front handle of the suc-b1 chain.)
sesA : 𝕊 0
sesA = (acq ; ret) ; skip

gA : Ctx 1
gA = ⟨ acq ; ret ⟩ F.∷ F.[]

-- The BindCtx that  TP-Res + inv-ν  expose for the acq side:
-- 0F : gA 0 = <(acq ; ret)>, exactly `acq's domain (with s = ret).
bcA : BindCtx {1} sesA gA
bcA = -∷ []

-- The acq redex types in body context gA, with 0F : <(acq ; ret)>,
-- producing the residual channel <(ret)>.  Hole-free: R-Acq is NOT vacuous.
acqExpr : gA ; ([] ∥ (` 0F)) ⊢ K `acq · (` 0F) ∶ ⟨ ret ⟩ ∣ ℙ
acqExpr = T-AppLin refl
  (T-Const `acq)
  (T-Var 0F refl)

-- And the acq side embeds in a genuine, fully-typed THREAD via the closing
-- frame E = (K `drop ·□) :: [], which consumes the residual <(ret)> channel
-- and yields `T | P.  This is the real R-Acq thread shape  ⟪ E [ acq·0F ]* ⟫.
acqFrame : Frame* 1
acqFrame = (V-K {c = `drop} ·□) ∷ []

acqThreadBody : gA ; ([] ∥ ([] ∥ (` 0F))) ⊢ acqFrame [ K `acq · (` 0F) ]* ∶ `⊤ ∣ ℙ
acqThreadBody = T-AppLin refl (T-Const `drop) acqExpr

⊢acq-thread : gA ; ([] ∥ ([] ∥ (` 0F))) ⊢ₚ ⟪ acqFrame [ K `acq · (` 0F) ]* ⟫
⊢acq-thread = TP-Expr (T-Conv ≃-refl ℙ≤ϵ acqThreadBody)
