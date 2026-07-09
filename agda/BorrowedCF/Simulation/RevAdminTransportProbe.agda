module BorrowedCF.Simulation.RevAdminTransportProbe where

-- | Machine-checked residual obstruction to the reverse "≈-chain engine"
--   (sim← non-ε case, Simulation2.Backward ?0), that survives the RU-Par-right
--   lever.
--
--   BACKGROUND.  The RU-Par-right lever (RevCongStrong, this session) makes the
--   structural-congruence (≋) transport sc-PRESERVING: ∥-comm is now genuinely
--   replayed (RU-Par ↔ RU-Par-right), introducing NO fresh RU-Struct.  So
--   RevPhiNest's specific non-termination argument ("─→ₚ has no right-∥ rule, so
--   ∥-comm forces a +1 RU-Struct") is now STALE.
--
--   RESIDUAL OBSTRUCTION.  The sim← INPUT is up to  ≈ = EqClosure (≋ ∪ ─→ᵃ)
--   (RevAdmin), whose chain also carries ADMINISTRATIVE (─→ᵃ) links.  A per-link
--   ≈-transport engine (≈link-sim, wired in Backward.agda for the ≋ links) would
--   need to move a reduction  red : R ─→ₚ Q  across an admin link  R ─→ᵃ R′  to
--   a SINGLE reduction  R′ ─→ₚ Q′  with  Q ≈ Q′.  That single-step admin
--   transport is FALSE.
--
--   WITNESS.  Exploiting  `pattern * = K `unit`  (Terms.agda:50), the silent GC
--   step a-discard and the observable RU-Discard from the SAME source land on
--   the IDENTICAL reduct — the value-thread  ⟪ K `unit ⟫.  So after the admin
--   link there is no residual reduction to carry (the target is a thread whose
--   only expression step is refuted by value-↛).  The transport must therefore
--   degrade to a reflexive-transitive (0-or-more step, silent/observable)
--   codomain, which no longer composes step-by-step with sim←ᵍ's strict-image
--   reflection.  That weak-bisimulation development is what ?0 still requires;
--   the RU-Par-right lever does not reach it.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Reduction.Base using (Value; V-K)
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Processes.Untyped
open import BorrowedCF.Simulation.RevAdmin using (_─→ᵃ_; a-discard)

open import Data.Product using (_×_; _,_)
open import Data.List using ([])

------------------------------------------------------------------------
-- The concrete source and its (unique) reduct.
--   R = ⟪ K `discard ·¹ K `unit ⟫.
------------------------------------------------------------------------

Radm : Proc 0
Radm = ⟪ K `discard ·¹ K `unit ⟫

------------------------------------------------------------------------
-- (1) The admin link and the observable reduction from Radm COINCIDE: both
--     land on the identical reduct ⟪ K `unit ⟫  (since * = K `unit).  So an
--     admin ≈-link can literally BE the reduction the engine wants to reflect.
------------------------------------------------------------------------

admin-red-coincide : (Radm ─→ᵃ ⟪ K `unit ⟫) × (Radm ─→ₚ ⟪ K `unit ⟫)
admin-red-coincide = a-discard [] V-K , RU-Discard [] V-K

-- (2) The admin target ⟪ K `unit ⟫ is a VALUE-thread (V-K): it carries no
--     residual expression step, so the admin link leaves nothing behind for a
--     single-step transport to produce — the transport must degrade to a weak
--     (0-or-more-step) codomain, which no longer composes with sim←ᵍ's strict
--     image reflection.  That weak-bisimulation development is what ?0 still
--     requires; the RU-Par-right lever does not reach it.
