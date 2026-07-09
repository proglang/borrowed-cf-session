module BorrowedCF.Simulation.RevCongStrongLE where

-- | MACHINE-CHECKED roadblock for STEP 1 of the reverse-simulation ?0 plan.
--
--   The plan asks to strengthen the ≋-transport lever (RevCongStrong) from the
--   TRUE bound  sc red′ ≤ suc (sc red)  to the bound STEP 6's chain-engine
--   termination requires,  sc red′ ≤ sc red  (RU-Struct-free / sc-PRESERVING
--   replay), for EVERY ≋′ generator.
--
--   This module isolates a concrete instance where that strengthened lever is
--   UNINHABITABLE by the only structurally-available witness: the RENAMING
--   generator  ν-swap′ : ν P ≋′ ν (P ⋯ₚ swapᵣ 1 1)  met by a ν-HEADED
--   CHANNEL-OP LEAF reduction (RU-LSplit).
--
--   WHY.  swapᵣ 1 1 swaps the two ν-bound endpoints (var 0 ↔ var 1), so it
--   displaces the lsplit redex's HARDCODED channel index  0F ↦ 1F.  RU-LSplit
--   fires only on 0F, so the swapped process  RHS  is no longer an lsplit redex:
--   it can be reduced to a ≋-neighbour of the original reduct ONLY by first
--   swapping back, i.e. by a RU-Struct wrapper (sc = 1).  That wrapper is the
--   ONLY generic witness (cf. ∥-red-inv in RevCongStrong, and the identical
--   non-termination noted in RevPhiNest:29 / Reverse:277 — the RU-Par-right
--   lever fixed ∥-comm but there is NO analogous fix for the ν-renaming
--   generators short of parameterising the channel-op rules over an arbitrary
--   bound index = a CALCULUS REDESIGN).
--
--   Below: the fallback witness `red′` has  sc red′ ≡ 1, while  sc red ≡ 0, so
--   `sc red′ ≤ sc red` (= 1 ≤ 0) is EMPTY.  `fallback-violates` proves it.
--   Hence STEP 1 cannot be completed as specified, and STEP 6's greedy engine
--   has no descent metric — the documented roadblock.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Simulation.RevCongStrong using (sc)

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)

open Nat using (_≤_)
open Fin.Patterns

open UP using (Proc; ν; ⟪_⟫; _∥_; _≋_; _≋′_; ν-swap′)
open UR using (_─→ₚ_; RU-LSplit; RU-Struct)

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

module _ {n : ℕ} (s : 𝕊 0) (F : Frame* (2 + n))
         {e₁ e₂ : Tm (2 + n)} {Q : Proc (2 + n)} where

  -- The ν-body carrying an lsplit redex on the ν-bound endpoint 0F.
  body : Proc (2 + n)
  body = ⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ] ]* ⟫ ∥ Q

  LHS : Proc n
  LHS = ν body

  -- The given untyped step: the lsplit fires.  It has NO RU-Struct node.
  red : LHS ─→ₚ ν (⟪ F [ 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ] ]* ⟫ ∥ Q)
  red = RU-LSplit F

  sc-red≡0 : sc red ≡ 0
  sc-red≡0 = refl

  -- ν-swap′ : LHS ≋′ RHS, RHS = ν(body ⋯ₚ swapᵣ 1 1).  The rename sends the
  -- redex's 0F to 1F, so RHS is NOT an lsplit redex.
  RHS : Proc n
  RHS = ν (body UP.⋯ₚ swapᵣ 1 1)

  swap≋ : LHS ≋ RHS
  swap≋ = Eq*.return (ν-swap′ {P = body})

  -- The ONLY structurally-available replay on RHS: swap back (RU-Struct), then
  -- reuse `red`.  It carries exactly one RU-Struct node.
  red′ : RHS ─→ₚ ν (⟪ F [ 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ] ]* ⟫ ∥ Q)
  red′ = RU-Struct (Eq*.symmetric _ swap≋) red ε

  sc-red′≡1 : sc red′ ≡ 1
  sc-red′≡1 = refl

  -- STEP 6 needs  sc red′ ≤ sc red.  For this instance that is  1 ≤ 0  — EMPTY.
  fallback-violates : ¬ (sc red′ ≤ sc red)
  fallback-violates ()

-- Corollary (concrete witness): swapᵣ 1 1 genuinely DISPLACES the lsplit
-- channel index 0F ↦ 1F, so RHS is not a 0F-lsplit-redex and RU-LSplit (which
-- fires only on 0F) has no genuine replay on it — the fallback above is forced.
module _ (s : 𝕊 0) where
  cbody : Proc 2
  cbody = ⟪ ([] [ K (`lsplit s) ·¹ 𝓒[ * × 0F × * ] ]*) ⟫ ∥ ⟪ * ⟫

  swap-displaces :
      (cbody UP.⋯ₚ swapᵣ 1 1)
    ≡ (⟪ ([] [ K (`lsplit s) ·¹ 𝓒[ * × 1F × * ] ]*) ⟫ ∥ ⟪ * ⟫)
  swap-displaces = refl
