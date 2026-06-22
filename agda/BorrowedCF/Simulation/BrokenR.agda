{-# OPTIONS --rewriting #-}

-- A machine-checked witness that the translation breaks the forward simulation
-- for `rsplit` under the current (liberal) typing — i.e. WITHOUT a `¬ Skips s`
-- premise on the `rsplit` constant.  This is the exact analogue of `Broken.agda`
-- (the `lsplit` witness); they differ only in WHICH triple slot diverges.
--
-- Source program it corresponds to (well-typed ONLY because the handle u is Unr,
-- which requires the rsplit'd type ⟨ s ; s′ ⟩ to satisfy Skips s ∧ Skips s′):
--
--     … obtain  u : ⟨ skip ; skip ⟩            ← Unr (Skips skip ∧ Skips skip)
--     let (a, b)  = rsplit u  in     -- split, handle = u
--     let (a',b') = rsplit u  in     -- u referenced AGAIN in the continuation E
--     unit                            -- (only possible because u is unrestricted)
--
-- At the first rsplit the typed redex is  ν (1 ∷ []) B (⟪ E[rsplit·(inj 0F)] ⟫ ∥ P),
-- with the handle inj 0F = position 0 occurring AGAIN inside E (the second rsplit).
-- R-RSplit INSERTS a fresh chain (1 → 1 ∷ 1), so the result is ν (1 ∷ 1 ∷ []) B (…),
-- the bound frame becomes E ⋯ᶠ* rwk (here rwk = weakenᵣ, since B₁ = []), and the old
-- handle is shifted to position 1 = inj 1F.
--
-- The untyped RU-RSplit allocates a FRESH sync φ (`0F ↦ unset`) and only WEAKENS the
-- translated frame (F ⋯ᶠ* weakenᵣ); it cannot retroactively rewrite a second
-- occurrence of the handle to mention that fresh sync.  But the translation's leaf
-- substitution maps the handle to DIFFERENT channel triples before vs after — they
-- disagree in the FIRST (acquire-sync) slot:
--
--     RU-RSplit's view  (canonₛ (1 ∷ [])     0F ⋯ weakenᵣ):  (K`unit ⊗ ` 1F) ⊗ K`unit
--     source-RHS's view (canonₛ (1 ∷ 1 ∷ []) 1F          ):  ((` 0F) ⊗ ` 1F) ⊗ K`unit
--                                                              ^^^^^^ the fresh sync
--
-- So ⟦E⟧ genuinely changes (the continuation must now acquire on the fresh sync),
-- RU-RSplit cannot produce it, and ⟦P⟧ ⇝ ⟦P′⟧ has no derivation: the bisimulation
-- fails on a well-typed program.  Adding `¬ Skips s` to `rsplit` rules out the Unr
-- handle that allows the second occurrence — exactly as it does for `lsplit`.

module BorrowedCF.BrokenR where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Bisim using (UChan)
open import BorrowedCF.Simulation.Flatten using (canonₛ)

open Nat.Variables
open Fin.Patterns

-- the ν-bound channel triple the translation starts from (data channel 0F, no syncs)
cc1 : UChan 2
cc1 = K `unit , 0F , K `unit

-- what RU-RSplit feeds the handle's continuation: the before-triple, merely weakened
-- past the freshly-introduced φ.
before : canonₛ (1 ∷ []) cc1 0F ⋯ weakenᵣ ≡ (K `unit ⊗ (` 1F)) ⊗ K `unit
before = refl

-- what the translation of the rsplit RESULT feeds it: the after-triple, which now
-- references the fresh sync (` 0F) in its acquire slot.
after : canonₛ (1 ∷ 1 ∷ []) cc1 1F ≡ ((` 0F) ⊗ (` 1F)) ⊗ K `unit
after = refl

-- hence the handle translates differently — RU-RSplit's weakened frame ≠ the result's.
break : canonₛ (1 ∷ []) cc1 0F ⋯ weakenᵣ ≢ canonₛ (1 ∷ 1 ∷ []) cc1 1F
break ()
