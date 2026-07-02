{-# OPTIONS --rewriting #-}
-- ============================================================================
--  Does origin/main's new Ub (commit 9544f3a "NUb[] got a case for a b=1")
--  fix Drop and/or LSplit?  Machine-checked against the UNCHANGED reduction
--  rules (RU-Drop needs the flag variable ` 0F in the right sync component;
--  RU-LSplit duplicates a handle into two IDENTICAL triples).
--
--  The new Ub is transcribed verbatim below.
-- ============================================================================
module BorrowedCF.Simulation2.NewFixCheck where

open import BorrowedCF.Simulation2.Base
open import Data.Fin using (zero; suc)

open Nat.Variables
open Fin.Patterns

UChanN : ℕ → Set
UChanN n = Tm n × 𝔽 n × Tm n

ctriN : UChanN n → Tm n
ctriN (e₁ , c , e₂) = (e₁ ⊗ (` c)) ⊗ e₂

-- NEW Ub (origin/main 9544f3a), verbatim:
NUb[_] : (b : ℕ) → UChanN n → 𝔽 b → Tm n
NUb[ 1 ]           (e₁ , c , e₂) zero    = ctriN (e₁ , c , e₂)
NUb[ suc (suc b) ] (e₁ , c , e₂) zero    = ctriN (e₁ , c , *)
NUb[ suc (suc b) ] (e₁ , c , e₂) (suc x) = NUb[ suc b ] (* , c , e₂) x

-- slot projectors
sL sC sR : Tm n → Tm n
sL ((a ⊗ b) ⊗ c) = a
sL _ = *
sC ((a ⊗ b) ⊗ c) = b
sC _ = *
sR ((a ⊗ b) ⊗ c) = c
sR _ = *

-- ============================================================================
-- DROP.  The drop-head of a WIDTH-1 chain is  NUb[ 1 ] (e₁ , c , ` 0F) zero.
-- RU-Drop needs its right-sync component = the flag variable ` 0F.
-- ============================================================================

-- the drop-head input triple at scope 2 (data ref suc 0F = ` 1F, right sync = flag ` 0F)
ccDrop : UChanN 2
ccDrop = (K `unit , suc 0F , (` 0F))

-- NEW: width-1 drop-head keeps the flag ` 0F in the right-sync slot.  DROP FIRES.
new-drophead-width1-keeps-flag : sR (NUb[ 1 ] ccDrop zero) ≡ (` 0F)
new-drophead-width1-keeps-flag = refl

-- The full width-1 drop-head triple matches RU-Drop's read shape 𝓒[ e × suc x × ` 0F ].
new-drophead-shape :
  NUb[ 1 ] ccDrop zero ≡ ((K `unit ⊗ (` suc 0F)) ⊗ (` 0F))
new-drophead-shape = refl

-- ============================================================================
-- LSPLIT.  A local split turns one channel into a WIDTH-2 chain; RU-LSplit
-- duplicates the handle into TWO IDENTICAL triples, so the two borrows
-- (index 0F and 1F) of the width-2 chain must translate EQUAL.
-- ============================================================================

-- The two borrows of a width-2 chain under the NEW Ub:
w2-borrow0 : Tm 2
w2-borrow0 = NUb[ 2 ] ((` 0F) , 0F , (` 1F)) 0F     -- = 𝓒[ ` 0F × 0F × * ]
w2-borrow1 : Tm 2
w2-borrow1 = NUb[ 2 ] ((` 0F) , 0F , (` 1F)) 1F     -- = 𝓒[ *    × 0F × ` 1F ]

w2-borrow0-shape : w2-borrow0 ≡ (((` 0F) ⊗ (` 0F)) ⊗ *)
w2-borrow0-shape = refl
w2-borrow1-shape : w2-borrow1 ≡ ((* ⊗ (` 0F)) ⊗ (` 1F))
w2-borrow1-shape = refl

-- The two borrows are NOT identical (left-sync ` 0F vs *): RU-LSplit's identical
-- duplication is still NOT matched.  LSPLIT STILL BROKEN under the new Ub.
new-lsplit-borrows-differ : w2-borrow0 ≢ w2-borrow1
new-lsplit-borrows-differ ()
