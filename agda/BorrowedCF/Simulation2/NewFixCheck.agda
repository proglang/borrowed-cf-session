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
-- LSPLIT (CORRECTED).  The typed lsplit splits ⟨ s ; s′ ⟩ into ⟨ s ⟩ ⊗ ⟨ s′ ⟩ —
-- two DIFFERENT halves.  The corrected RU-LSplit (origin/main 7c1fc9c) splits:
--     𝓒[ e₁ × 0F × e₂ ]  →  𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ]
-- (left half keeps the left sync e₁; right half keeps the right sync e₂; the
-- data channel 0F is shared; unit in the cut positions).  The distributing
-- translation's two borrows MATCH this split exactly.
--
-- (RETRACTION: an earlier version of this file claimed the two borrows must be
-- IDENTICAL and that the fix broke LSplit.  That premise was WRONG — it rested on
-- the OLD RU-LSplit which duplicated the handle identically, itself a bug, now
-- fixed on main.  The distributing translation was correct all along.)
-- ============================================================================

-- The two borrows of the split (width-2) chain under the distributing Ub, with
-- handle triple (e₁ , data , e₂) = (` 0F , 0F , ` 1F):
w2-borrow0 : Tm 2
w2-borrow0 = NUb[ 2 ] ((` 0F) , 0F , (` 1F)) 0F
w2-borrow1 : Tm 2
w2-borrow1 = NUb[ 2 ] ((` 0F) , 0F , (` 1F)) 1F

-- LEFT borrow  = 𝓒[ e₁ × 0F × * ]  — the corrected RU-LSplit's LEFT half.
new-lsplit-left-matches  : w2-borrow0 ≡ (((` 0F) ⊗ (` 0F)) ⊗ *)
new-lsplit-left-matches  = refl
-- RIGHT borrow = 𝓒[ * × 0F × e₂ ]  — the corrected RU-LSplit's RIGHT half.
new-lsplit-right-matches : w2-borrow1 ≡ ((* ⊗ (` 0F)) ⊗ (` 1F))
new-lsplit-right-matches = refl

-- So the distributing translation and the corrected RU-LSplit AGREE on the two
-- split halves (at the isolated-triple level).  LSplit is consistent again.
