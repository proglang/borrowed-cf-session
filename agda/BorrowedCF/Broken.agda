
-- A machine-checked witness that the translation breaks the forward simulation
-- for `lsplit` under the current (liberal) typing.
--
-- Source program it corresponds to (well-typed because the handle u is Unr):
--
--     let (c, _) = new skip   in     -- c : ⟨ acq ; skip ⟩
--     let (_, u) = lsplit c   in     -- u : ⟨ skip ⟩            ← Unr
--     let (a, b) = lsplit u   in     -- split #1, handle = u
--     let (a',b') = lsplit u  in     -- u referenced again in the continuation E
--     unit
--
-- At split #1 the typed redex is  ν (1 ∷ 1 ∷ []) B (⟪ E[lsplit·(inj 0F)] ⟫ ∥ P)
-- with the handle inj 0F = position 0 occurring again in E (the second lsplit).
-- R-LSplit grows its chain 1 → 2, so the redex becomes  ν (2 ∷ 1 ∷ []) B (…).
--
-- The untyped RU-LSplit leaves the translated frame UNCHANGED, so for the step
-- to exist ⟦E⟧ must be equal on both sides.  But the leaf substitution that the
-- translation feeds to E maps the handle (var 0F) to DIFFERENT channel triples
-- before vs after the lsplit — they disagree in the third (drop-sync) slot:
--
--     before (chain 1 ∷ 1 ∷ []):  (K`unit ⊗ ` 1F) ⊗ (` 0F)   -- third = junction sync
--     after  (chain 2 ∷ 1 ∷ []):  (K`unit ⊗ ` 1F) ⊗  K`unit   -- third = unit
--
-- So ⟦E⟧ genuinely changes, RU-LSplit cannot produce it, and ⟦P⟧ ⇝ ⟦P′⟧ has no
-- derivation: the bisimulation fails on a well-typed program.

module BorrowedCF.Broken where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Bisim using (UChan)
open import BorrowedCF.Simulation.Flatten using (canonₛ)

open Nat.Variables
open Fin.Patterns

-- the ν-bound channel triple the translation starts from (data channel 0F, no syncs)
cc1 : UChan 2
cc1 = K `unit , 0F , K `unit

-- the exact channel triple the handle (var 0F) is translated to, before/after:
before : canonₛ (1 ∷ 1 ∷ []) cc1 0F ≡ (K `unit ⊗ (` 1F)) ⊗ (` 0F)
before = refl

after  : canonₛ (2 ∷ 1 ∷ []) cc1 0F ≡ (K `unit ⊗ (` 1F)) ⊗ K `unit
after  = refl

-- hence the handle translates differently before vs after the lsplit
break : canonₛ (1 ∷ 1 ∷ []) cc1 0F ≢ canonₛ (2 ∷ 1 ∷ []) cc1 0F
break ()
