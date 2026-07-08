-- | Shared preamble for the clean simulation development (Simulation2).
--
--   Re-exports the source/target calculi, the translation, and the (drift-free,
--   reusable) machinery that already compiles under BorrowedCF.Simulation.
--   The forward/backward statements and the per-case proofs are built on top.
module BorrowedCF.Simulation2.Base where

open import BorrowedCF.Prelude public
open import BorrowedCF.Terms public
open import BorrowedCF.Types public
open import BorrowedCF.Reduction.Base public
open import BorrowedCF.Reduction.Expressions public

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap) public
import Relation.Binary.Construct.Closure.Equivalence as Eq* public
open import Data.Sum using (_⊎_; inj₁; inj₂) public

open import Data.Nat.ListAction using (sum) public
open import BorrowedCF.Context using (Ctx; Struct) public

-- The translation U[_] and its channel-triple helpers.
open import BorrowedCF.Processes.Bisim public

-- Source (typed) and target (untyped) process calculi + reductions.
import BorrowedCF.Processes.Typed             as TP public
import BorrowedCF.Processes.Untyped           as UP public
import BorrowedCF.Reduction.Processes.Typed   as TR public
import BorrowedCF.Reduction.Processes.Untyped as UR public

open Nat.Variables public
open Fin.Patterns public

open TP using (_;_⊢ₚ_; TP-Expr; TP-Par; TP-Res; TP-Weaken;
               inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx) public
