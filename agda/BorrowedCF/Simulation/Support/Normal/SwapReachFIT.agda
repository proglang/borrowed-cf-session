{-# OPTIONS --rewriting #-}
-- PROBE (verify-first): is nf-reach's SwapUnreachable counterexample actually
-- in the DOMAIN of realise's swap-R leg?  realise only ever receives residues
-- whose SOURCE telescope satisfies `FIT idₖ` (front-independence), threaded
-- from factor′'s `fit` argument.  This module machine-checks that the
-- SwapUnreachable instance's telescope T₂ᵗ = tv (tφ drop `0 (tv [])) does NOT
-- satisfy FIT: its phi channel is the genuine inner-nu variable `0F, not an
-- ambient (front-independent) image.  Hence the SwapUnreachable verdict is on
-- an OUT-OF-DOMAIN instance -- exactly what its own WALL 2 (`noFRun`) proves.
module BorrowedCF.Simulation.Support.Normal.SwapReachFIT where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped using (Flag; drop)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.FrontIndep using (FIT)

open Fin.Patterns
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Empty using (⊥)
open Nat.Variables

T₂ᵗ : Tel 0 5
T₂ᵗ = tν (tφ drop (` 0F) (tν []))

noVar0-w2 : (cf : Tm 0) -> ` 0F ≡ cf ⋯ (idₖ ⦃ Kᵣ ⦄ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) -> ⊥
noVar0-w2 (` ())
noVar0-w2 (K x)                      ()
noVar0-w2 (ƛ cf)                   ()
noVar0-w2 (μ cf)                    ()
noVar0-w2 (cf ·⟨ d ⟩ cf1)    ()
noVar0-w2 (cf ; cf1)              ()
noVar0-w2 (cf ⊗ cf1)            ()
noVar0-w2 (`let cf `in cf1)          ()
noVar0-w2 (`let⊗ cf `in cf1)    ()
noVar0-w2 (`inj i cf)                ()
noVar0-w2 (`case cf `of⟨ cf1 ; cf2 ⟩) ()

T₂ᵗ-notFIT : FIT (idₖ ⦃ Kᵣ ⦄) T₂ᵗ -> ⊥
T₂ᵗ-notFIT ((cf , ceq) , _) = noVar0-w2 cf ceq
