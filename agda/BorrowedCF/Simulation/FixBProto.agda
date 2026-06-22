{-# OPTIONS --rewriting #-}

-- Fix B proof-of-concept: decoupling the borrow-obligation flag from the count.
--
-- ROOT CAUSE (current code): Bisim.ϕ[_] : ℕ → Flag with ϕ[zero]=set, ϕ[suc _]=unset
-- reads the COUNT.  Both R-Com and R-Drop do  suc b₁ ∷ B₁ → b₁ ∷ B₁  (decrement the
-- front count), so ϕ flips exactly when the count reaches 0 — but RU-Com must NOT flip
-- and RU-Drop must ALWAYS flip.  Neither matches ϕ[count].
--
-- FIX B: carry the flag explicitly (Chain = ℕ × Flag); ϕ′ reads the flag.  Then Com
-- preserves it and Drop sets it — each matching its untyped rule, for ALL counts.

module BorrowedCF.Simulation.FixBProto where

open import BorrowedCF.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using () renaming (Bool to Flag; true to set; false to unset)
import BorrowedCF.Processes.Bisim as Old   -- the current (buggy) ϕ[_]

Chain : Set
Chain = ℕ × Flag

-- The fixed junction-flag reader: it reads the carried flag, NOT (count ≟ 0).
ϕ′ : Chain → Flag
ϕ′ (_ , f) = f

-- Bind-group transitions at the chain level (front chain only shown).
comStep : Chain → Chain          -- communication: count down, flag PRESERVED
comStep (suc c , f) = c , f
comStep (zero  , f) = zero , f

dropStep : Chain → Chain         -- drop: count down, flag SET (obligation discharged)
dropStep (suc c , _) = c , set
dropStep (zero  , _) = zero , set

-- ════════════════════════════════════════════════════════════════════
-- THE FIX, machine-checked: under ϕ′, Com preserves the flag and Drop sets it,
-- for EVERY count c — so they match RU-Com (no flag change) / RU-Drop (→set).
-- ════════════════════════════════════════════════════════════════════

com-preserves-flag : ∀ c f → ϕ′ (comStep (suc c , f)) ≡ ϕ′ (suc c , f)
com-preserves-flag c f = refl

drop-sets-flag : ∀ c f → ϕ′ (dropStep (suc c , f)) ≡ set
drop-sets-flag c f = refl

-- ════════════════════════════════════════════════════════════════════
-- Contrast: the CURRENT ϕ[count] FLIPS the front flag at the b₁=0 boundary
-- (the exact ComScratch obstruction) — unset (count 1) vs set (count 0).
-- ════════════════════════════════════════════════════════════════════

old-com-flips-at-0 : Old.ϕ[ 1 ] ≢ Old.ϕ[ 0 ]
old-com-flips-at-0 ()

-- And the resolution: with the explicit flag the SAME b₁=0 transition keeps the flag
-- (front chain (1,unset) → (0,unset)), so LHS and RHS front flags now AGREE.
fixed-com-agrees-at-0 : ϕ′ (comStep (1 , unset)) ≡ ϕ′ (1 , unset)
fixed-com-agrees-at-0 = refl
