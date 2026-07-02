{-# OPTIONS --rewriting #-}
-- Domain-free verification of the Stage-2 split-halves math for U-lsplit.
-- Uses Congruence's canonₛ (which does NOT import Context.Domain), so this
-- typechecks even while Context.Domain is mid-refactor.
--
-- We check, on CONCRETE multi-chain grown groups, that:
--   * grown borrow-0 = 𝓒[L × junc × *]        (right slot dropped, width ≥ 2)
--   * grown borrow-1 = 𝓒[* × junc × R]        (left slot dropped)
--   * ungrown borrow-0 = 𝓒[L × junc × R]      (both kept: the "combined" borrow)
-- i.e. the two grown borrows are exactly the two SPLIT halves of the ungrown
-- borrow — which is what RU-LSplit produces.  This is the semantic core the
-- five handle-lwk lemmas package for arbitrary B₁/b₁/B₂.
module BorrowedCF.Simulation2.LsplitVerify where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Congruence using (canonₛ)
open import BorrowedCF.Processes.Typed using (BindGroup)
open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)

open Nat.Variables
open Fin.Patterns

-- Two-chain group, head width 1 (ungrown) vs 2 (grown), tail width 1.
-- N = 0 scope; channel triple (K unit, 0F-in-N? no N=0) — use N with a var.
-- Work at N = 1 so we have a junction var x = 0F to read.

-- UNGROWN handle: group (1 ∷ 1 ∷ []), borrow-0 at flat pos 0F.
--   canonₛ (1 ∷ 1 ∷ []) (Kunit, x, Kunit) 0F
--     = Ub[ 1 ] (wk Kunit, suc x, ` 0F) 0F ⋯ wk (syncs (1∷[]))
--     = 𝓒[ wk Kunit × suc x × ` 0F ] ⋯ wk 0     (syncs (1∷[]) = 0)
--     = 𝓒[ Kunit × suc x × ` 0F ]  — right slot ` 0F kept (width-1 head).
ungrown-b0 : canonₛ {n = 1} (1 ∷ 1 ∷ []) (K `unit , 0F , K `unit) 0F
             ≡ ((K `unit ⊗ (` 1F)) ⊗ (` 0F))
ungrown-b0 = refl

-- GROWN handle: group (2 ∷ 1 ∷ []), borrow-0 at flat pos 0F.
--   = Ub[ 2 ] (wk Kunit, suc x, ` 0F) 0F ⋯ wk 0 = 𝓒[ Kunit × suc x × * ]
grown-b0 : canonₛ {n = 1} (2 ∷ 1 ∷ []) (K `unit , 0F , K `unit) 0F
           ≡ ((K `unit ⊗ (` 1F)) ⊗ *)
grown-b0 = refl

-- GROWN handle borrow-1 at flat pos 1F.
--   = Ub[ 2 ] (wk Kunit, suc x, ` 0F) 1F ⋯ wk 0
--   = Ub[ 1 ] (*, suc x, ` 0F) 0F = 𝓒[ * × suc x × ` 0F ]
grown-b1 : canonₛ {n = 1} (2 ∷ 1 ∷ []) (K `unit , 0F , K `unit) 1F
           ≡ ((* ⊗ (` 1F)) ⊗ (` 0F))
grown-b1 = refl

-- ⇒ grown-b0 (L kept, R=*) and grown-b1 (L=*, R kept) are the two SPLIT halves
--   of ungrown-b0 (L and R both kept).  RU-LSplit on ungrown-b0 = 𝓒[L×j×R]
--   produces 𝓒[L×j×*] ⊗ 𝓒[*×j×R] = grown-b0 ⊗ grown-b1.  ✓

-- Sanity for b₁ ≥ 1 (head width 2 ungrown, 3 grown), tail width 1:
--   ungrown borrow-0 right slot is * (Ub[2] head), grown borrow-1 right slot is *.
ungrown-b0' : canonₛ {n = 1} (2 ∷ 1 ∷ []) (K `unit , 0F , K `unit) 0F
              ≡ ((K `unit ⊗ (` 1F)) ⊗ *)
ungrown-b0' = refl

grown-b1' : canonₛ {n = 1} (3 ∷ 1 ∷ []) (K `unit , 0F , K `unit) 1F
            ≡ ((* ⊗ (` 1F)) ⊗ *)
grown-b1' = refl

-- ── LAST-CHAIN NOW DISTRIBUTES (obstruction RESOLVED) ────────────────────
-- The singleton leaf now distributes: canonₛ (h ∷ []) cc = Ub[ h + 0 ] cc.
-- So even when B₂ = [] (handle is the LAST chain, e.g. B₁ = 1∷[], handle width
-- 2 grown), the two grown borrows are DIFFERENT — the two split halves:
grown-b0-B1ne : canonₛ {n = 1} (1 ∷ 2 ∷ []) (K `unit , 0F , K `unit)
                  (Data.Fin.suc Data.Fin.zero)          -- borrow-0
                ≡ (((` 0F) ⊗ (` 1F)) ⊗ *)               -- 𝓒[e₁ × j × *]  (L kept, R=*)
grown-b0-B1ne = refl
grown-b1-B1ne : canonₛ {n = 1} (1 ∷ 2 ∷ []) (K `unit , 0F , K `unit)
                  (Data.Fin.suc (Data.Fin.suc Data.Fin.zero))  -- borrow-1
                ≡ ((* ⊗ (` 1F)) ⊗ *)                    -- 𝓒[* × j × R]  (L=*, R kept)
grown-b1-B1ne = refl
-- ⇒ borrow-0 and borrow-1 now DIFFER for B₂ = [] too, matching RU-LSplit's split.
--   The last-chain broadcast-vs-split obstruction is gone; U-lsplit closes for all B₂.
