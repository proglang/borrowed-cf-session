-- | The three binding cases of the completeness induction (agent C4).
--
--   Split into one module per case: each is a large elaboration (three induction hypotheses,
--   a canonical split and a binder confinement), and Agda needs them checked separately.
--
--   Owner: agent C4.
module BorrowedCF.Completeness.Main.Bind where

open import BorrowedCF.Completeness.Main.Bind.Let public using (let-case)
open import BorrowedCF.Completeness.Main.Bind.LetPair public using (letpair-case)
open import BorrowedCF.Completeness.Main.Bind.Case public using (case-case)
