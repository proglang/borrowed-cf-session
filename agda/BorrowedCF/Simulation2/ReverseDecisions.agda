{-# OPTIONS --rewriting #-}
-- ============================================================================
--  Concrete examples for the REVERSE-direction decisions.
--  D1's witness lives in OrderPincer.agda (head-min FALSE).  This file gives a
--  machine-checked D2 example (the φ flag lifecycle) and cross-refs D1.
-- ============================================================================
module BorrowedCF.Simulation2.ReverseDecisions where

open import BorrowedCF.Simulation2.Base
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)

open U.Proc
open Fin.Patterns

-- ============================================================================
-- D2 — the async φ handshake flips a synchronization FLAG: drop → acq → done.
-- A single untyped step lands at an INTERMEDIATE flag-state that is NOT the
-- U[_]-image of any typed process (typed processes have no half-done handshakes).
-- ============================================================================

-- A concrete φ-drop process with a drop redex (n = 1, so the channel `suc 0F`
-- and the flag ` 0F both exist under the φ binder).
flagSrc : U.Proc 1
flagSrc = φ U.drop
            ( ⟪ [] [ K `drop ·¹ ((* ⊗ (` suc 0F)) ⊗ (` 0F)) ]* ⟫
            ∥ ⟪ K `unit ⟫ )

-- It fires RU-Drop; the constructor DEFINES the reduct.
flagStep : Σ (U.Proc 1) (λ R → flagSrc UR.─→ₚ R)
flagStep = _ , UR.RU-Drop {e = *} [] {x = 0F}

flagReduct : U.Proc 1
flagReduct = proj₁ flagStep

-- The reduct is in flag-state `acq` (an intermediate handshake state), where the
-- source was in flag-state `drop`, and the dropped handle became `*`.
flagReduct-shape : flagReduct ≡ φ U.acq (⟪ [] [ * ]* ⟫ ∥ ⟪ K `unit ⟫)
flagReduct-shape = refl

-- The flags genuinely differ (acq ≠ drop): the reduct is not syntactically the
-- source, so the reverse's  flagReduct ≋ U[P′]σ  cannot hold by matching flags —
-- unless ≋ is made flag-invariant (option a) or a normal-form lemma is used (b).
acq≢drop : U.acq ≡ U.drop → ⊥
acq≢drop ()

-- The three-state lifecycle, for reference (all from Reduction/Processes/Untyped):
--   RU-Drop    : φ drop (⟪F[drop·𝓒[e×suc x×` 0F]]⟫ ∥ P)  ─→  φ acq  (⟪F[*]⟫ ∥ P)
--   RU-Acquire : ν (φ acq (⟪F[acq·𝓒[` 0F×1F×e]]⟫ ∥ P))    ─→  ν (φ done (⟪F[…]⟫ ∥ P))
--   RU-Cleanup : φ done P                                 ─→  P ⋯ₚ ⦅ * ⦆ₛ
-- So ONE typed R-Acq = TWO untyped steps (RU-Acquire ; RU-Cleanup), passing
-- through the `done` intermediate; observing ONE of them in reverse leaves you
-- at a state between two U[_] images.
