-- | The EXACT residual gap after the seed lemma + φcomm-reflect: a φ-comm′
--   generator whose inner step is FLAG-SENSITIVE (RU-Sync (RU-Drop …)) at a cell
--   the swap RE-FLAGGED.  This is the one φ-comm′ shape φcomm-reflect does NOT
--   cover (it handles only the flag-POLYMORPHIC descent RU-Sync (RU-Sync sub)),
--   and it forces RevCongStrong.≋′-sim-strong-revᵐ's generic +1 fallback,
--   breaking the ∣_∣ / sc well-founded descent the reverse RU-Struct dispatch
--   needs.  Same class as RevNuPhiComm's νφ-comm′ + RU-Acquire refutation.
--
--   CONFIGURATION (mirror of φ-comm′, x = drop, y = acq).  D is a genuine
--   drop-redex thread.
--       LHS = φ drop (φ acq (D ⋯ₚ assocSwapᵣ 1 1))
--       RHS = φ acq (φ drop D)         ( = φ-comm′ RHS, assocSwap involutive)
--     • On RHS the drop FIRES: RU-Sync (RU-Drop []) — the inner φ drop wraps the
--       thread D.  sc = 0 (a leaf: no RU-Struct).
--     • On LHS the corresponding inner cell is φ ACQ, so RU-Drop cannot replay
--       there (flag clash acq ≢ drop; `inner-flag-clash`).  The ONLY structural
--       transport of the RHS step back onto LHS is the generic RU-Struct wrapper
--       (RevCongStrong fallback), with sc = 1.  `fallback-violates` proves
--       sc(fallback) ≤ sc(fire)  ( = 1 ≤ 0 )  is EMPTY.
--
--   So a per-generator, ∣_∣-descending reflector dispatch over c₁ CANNOT be
--   total: at this φ-comm′ + flag-sensitive-inner shape it neither descends nor
--   transports equivariantly.  Proving φ-comm′ "inessential" on image-order
--   (acq-outer) telescopes (SeedProbe) is true but does NOT remove this shape,
--   which arises on drop-outer intermediates inside a multi-generator c₁.  The
--   residual is the SAME `Base` / sim←-base obligation (a φ-telescope-aware
--   reverse inversion / statement change), not closeable by φ-comm inessentiality.
--
--   All results hole-free / postulate-free.
module BorrowedCF.Simulation2.Backward.PhiCommFail where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Reduction.Processes.Untyped
open import BorrowedCF.Simulation.RevCongStrong using (sc)

open import Data.Empty using (⊥)
open import Data.Nat using (_≤_)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)

open Nat.Variables
open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- Genuine drop-redex thread body (Proc 2), and the two φ-comm′ endpoints.
D : Proc 2
D = ⟪ K `drop ·¹ 𝓒[ * × 1F × ` 0F ] ⟫ ∥ ⟪ * ⟫

LHS : Proc 0
LHS = φ drop (φ acq (D ⋯ₚ assocSwapᵣ 1 1))

RHS : Proc 0
RHS = φ acq (φ drop D)

-- One φ-comm′ generator links them (assocSwapᵣ 1 1 is involutive, so the RHS
-- reindex of  D ⋯ₚ assocSwapᵣ 1 1  is  D).
gen : LHS ≋′ RHS
gen = φ-comm′ {x = drop} {y = acq}

------------------------------------------------------------------------
-- (1) The FLAG-SENSITIVE inner step fires on RHS: RU-Sync (RU-Drop []).
--     It is a leaf — no RU-Struct node — so sc = 0.
fire : RHS ─→ₚ φ acq (φ acq (⟪ [] [ * ]* ⟫ ∥ ⟪ * ⟫))
fire = RU-Sync (RU-Drop [] {x = 0F})

sc-fire≡0 : sc fire Eq.≡ 0
sc-fire≡0 = Eq.refl

------------------------------------------------------------------------
-- (2) On LHS the corresponding inner cell is φ ACQ, so the drop cannot replay
--     there: RU-Drop's redex requires φ DROP.  Flag clash acq ≢ drop.
inner-flag-clash : ∀ {k} {X Y : Proc (1 + k)} → φ acq X Eq.≡ φ drop Y → ⊥
inner-flag-clash ()

------------------------------------------------------------------------
-- (3) The ONLY structural transport of `fire` back onto LHS is the generic
--     RevCongStrong fallback  RU-Struct (return gen) fire ε — a FRESH RU-Struct,
--     with sc = suc (sc fire) = 1.  The WF descent the dispatch needs is
--     sc(fallback) ≤ sc(fire) = 1 ≤ 0, which is EMPTY.
fallback : LHS ─→ₚ φ acq (φ acq (⟪ [] [ * ]* ⟫ ∥ ⟪ * ⟫))
fallback = RU-Struct (Eq*.return gen) fire ε

sc-fallback≡1 : sc fallback Eq.≡ 1
sc-fallback≡1 = Eq.refl

fallback-violates : ¬ (sc fallback ≤ sc fire)
fallback-violates ()
