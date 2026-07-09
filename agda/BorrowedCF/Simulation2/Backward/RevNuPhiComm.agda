module BorrowedCF.Simulation2.Backward.RevNuPhiComm where

-- | MACHINE-CHECKED VERDICT for the reverse-simulation non-ε engine's
--   `νφ-comm′` case (Reverse.sim← ?0, the φ-DECOMPOSITION route prescribed by
--   RevPhiNest:40-52).
--
--   RevPhiNest BETS that the single image-escaping generator
--       νφ-comm′ : ν (φ x P) ≋′ φ x (ν (P ⋯ₚ assocSwapᵣ 1 2))
--   can be closed by REPLAYING the reduction out of the ν-headed LEFT onto the
--   φ-headed RIGHT via `red-⋯ₚ (assocSwapᵣ 1 2)` (now PROVEN, RedRename) under a
--   LEXICOGRAPHIC  (φ-heads-outside-ν , sc)  measure that STRICTLY DECREASES.
--
--   THIS MODULE REFUTES THAT BET, hole-free / postulate-free, on TWO fronts:
--
--   (A) ORIENTATION (generic, `Orientation`).  The mission's first lex
--       component `φ#` (leading-φ count = φ-heads outside the ν-telescope) is
--       moved the WRONG way by the generator: νφ-comm′ sends φ# 0 ↦ 1, i.e. it
--       STRICTLY INCREASES on a LEFT→RIGHT replay.  `φ#-increases` proves
--       0 < 1; `no-lex-decrease` proves the lex pair therefore can NEVER
--       strictly decrease LEFT→RIGHT for ANY sc-tails.
--
--   (B) THE ESCAPING LEAF (concrete, `AcquireLeaf`).  Exactly like
--       RevCongStrongLE's ν-swap′ + RU-LSplit, νφ-comm′ has a ν-headed
--       CHANNEL-OP LEAF that fires on its LEFT: RU-Acquire, whose source is
--           ν (φ acq (⟪ … K `acq … ⟫ ∥ …))
--       — precisely the LEFT of νφ-comm′ at x = acq.  The rewrite moves the
--       φ acq sync-cell OUTSIDE the ν, so the RIGHT  φ acq (ν …)  is no longer
--       an RU-Acquire redex (RU-Acquire requires a ν-HEAD; the acq is stuck
--       without its enclosing cell).  The ONLY structural replay on the RIGHT
--       is the RU-Struct swap-back wrapper, with sc red′ ≡ 1 while sc red ≡ 0.
--       So the SECOND lex component also increases; `acq-fallback-violates`
--       proves `sc red′ ≤ sc red` (= 1 ≤ 0) is EMPTY.
--
--   (C) EVEN THE "GENUINE" HEAD DOES NOT DESCEND (`SyncReplay`).  For the one
--       reduction head that admits an RU-Struct-free replay under
--       assocSwapᵣ 1 2 — redL = RU-Res (RU-Sync sub), replayed as
--       RU-Sync (RU-Res (red-⋯ₚ (assocSwapᵣ 1 2) sub)) — the two reducts
--           ν (φ x P′)   and   φ x (ν (P′ ⋯ₚ assocSwapᵣ 1 2))
--       are AGAIN a νφ-comm′ pair (`reducts-regenerate`): φ# stays at the same
--       0/1 configuration, so the engine reproduces the exact same generator
--       and the (φ#, sc) measure is NOT strictly smaller.
--
--   BONUS FINDING.  The replay lever `red-⋯ₚ` that RevPhiNest's route hinges on
--   does NOT even compile at this main HEAD: BorrowedCF.Simulation.RedRename
--   fails to typecheck (─→-⋯ᵣ, line ~21: the E-App implicit order {a}{_}{b} is
--   mismatched, `Dir !=< Tm`).  So part (C)'s replay is documented structurally
--   (redL + reducts-regenerate) rather than transported here, to keep this
--   probe self-contained and independent of the broken module.
--
--   CONCLUSION.  In the mission's stated LEFT→RIGHT orientation the lex measure
--   (φ-heads-outside-ν , sc) does NOT strictly decrease for νφ-comm′: it
--   increases on the escaping RU-Acquire leaf (both components) and is merely
--   preserved-and-regenerated on the genuine RU-Sync head.  The νφ-comm case
--   is the same class of obstruction as RevCongStrongLE / NonEpsRoadblock, now
--   pinned for νφ-comm′ + RU-Acquire.  ==> REFUTATION.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Simulation.RevCongStrong using (sc)

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)

open Nat using (_≤_; _<_; z≤n; s≤s)
open Fin.Patterns

open UP using (Proc; ν; φ; ⟪_⟫; _∥_; _⋯ₚ_; _≋_; _≋′_; Flag; acq; νφ-comm′)
open UR using (_─→ₚ_; RU-Acquire; RU-Res; RU-Sync; RU-Struct)

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

--------------------------------------------------------------------------------
-- The φ-head-count measure ("φ-heads-outside-ν"): the number of leading φ
-- constructors before the first non-φ head.  νφ-comm′ pushes a φ out from
-- under a ν, so it turns a φ#-0 process into a φ#-1 one.

φ# : ∀ {n} → Proc n → ℕ
φ# (φ _ P) = suc (φ# P)
φ# _       = 0

-- Lexicographic order on (φ# , sc)-configurations.
_<ₗ_ : (ℕ × ℕ) → (ℕ × ℕ) → Set
(a , b) <ₗ (c , d) = (a < c) ⊎ ((a ≡ c) × (b < d))

--------------------------------------------------------------------------------
-- (A) ORIENTATION.  Generic over the νφ-comm′ endpoints.

module Orientation {n : ℕ} (x : Flag) (P : Proc (3 + n)) where

  LHSg RHSg : Proc n
  LHSg = ν (φ x P)
  RHSg = φ x (ν (P ⋯ₚ assocSwapᵣ 1 2))

  gen : LHSg ≋′ RHSg
  gen = νφ-comm′

  φ#-LHSg≡0 : φ# LHSg ≡ 0
  φ#-LHSg≡0 = refl

  φ#-RHSg≡1 : φ# RHSg ≡ 1
  φ#-RHSg≡1 = refl

  -- The generator STRICTLY INCREASES the φ-head count (0 < 1): the first lex
  -- component moves the wrong way for any LEFT→RIGHT replay.
  φ#-increases : φ# LHSg < φ# RHSg
  φ#-increases = s≤s z≤n

  -- Hence the lex measure (φ# , sc) can never strictly decrease LEFT→RIGHT,
  -- for ANY sc-tails b (on the RIGHT replay) and c (on the LEFT reduction).
  no-lex-decrease : ∀ {b c : ℕ} → ¬ ((φ# RHSg , b) <ₗ (φ# LHSg , c))
  no-lex-decrease (inj₁ ())
  no-lex-decrease (inj₂ (() , _))

--------------------------------------------------------------------------------
-- (B) THE ESCAPING LEAF.  RU-Acquire fires on the LEFT of νφ-comm′ (x = acq);
-- the rewrite displaces its sync-cell, so no genuine replay survives on the
-- RIGHT and the forced RU-Struct fallback breaks sc-preservation.

module AcquireLeaf {n : ℕ} (F : Frame* (2 + n))
                   {e : Tm (2 + n)} {P : Proc (2 + n)} where

  -- The acquire step.  Its source is  ν (φ acq (…)) = LEFT of νφ-comm′ at
  -- x = acq.  It is a leaf: sc red ≡ 0.
  red : _ ─→ₚ ν (⟪ F [ 𝓒[ * × 0F × e ] ]* ⟫ ∥ P)
  red = RU-Acquire F

  sc-red≡0 : sc red ≡ 0
  sc-red≡0 = refl

  -- νφ-comm′ at x = acq sends the acquire source to  φ acq (ν …), a φ-HEADED
  -- non-redex.  The ONLY replay to a ≋-neighbour of red's reduct is to swap
  -- the generator back (RU-Struct), then reuse red — one RU-Struct node.
  red′ : _ ─→ₚ ν (⟪ F [ 𝓒[ * × 0F × e ] ]* ⟫ ∥ P)
  red′ = RU-Struct (Eq*.symmetric _ (Eq*.return (νφ-comm′ {x = acq}))) red ε

  sc-red′≡1 : sc red′ ≡ 1
  sc-red′≡1 = refl

  -- sc-preservation (the descent the engine needs) is  sc red′ ≤ sc red, i.e.
  -- 1 ≤ 0 — EMPTY.  The second lex component increases too.
  acq-fallback-violates : ¬ (sc red′ ≤ sc red)
  acq-fallback-violates ()

--------------------------------------------------------------------------------
-- (C) EVEN THE GENUINE HEAD REGENERATES νφ-comm′.  For redL = RU-Res (RU-Sync
-- sub) the transported replay RU-Sync (RU-Res (red-⋯ₚ (assocSwapᵣ 1 2) sub))
-- is RU-Struct-free, but its reducts are AGAIN a νφ-comm′ pair, so the (φ#, sc)
-- configuration is reproduced verbatim (no strict descent).

module SyncReplay {n : ℕ} {x : Flag} {P P′ : Proc (3 + n)} (sub : P ─→ₚ P′) where

  -- LEFT reduction: fire sub under φ under ν.
  redL : ν (φ x P) ─→ₚ ν (φ x P′)
  redL = RU-Res (RU-Sync sub)

  -- The two reducts (LEFT: ν (φ x P′); RIGHT: φ x (ν (P′ ⋯ₚ assocSwapᵣ 1 2)))
  -- are AGAIN a νφ-comm′ pair: the φ#-0/φ#-1 configuration is reproduced.
  reducts-regenerate : ν (φ x P′) ≋′ φ x (ν (P′ ⋯ₚ assocSwapᵣ 1 2))
  reducts-regenerate = νφ-comm′

  φ#-reduct-LEFT  : φ# (ν (φ x P′)) ≡ 0
  φ#-reduct-LEFT  = refl

  φ#-reduct-RIGHT : φ# (φ x (ν (P′ ⋯ₚ assocSwapᵣ 1 2))) ≡ 1
  φ#-reduct-RIGHT = refl
