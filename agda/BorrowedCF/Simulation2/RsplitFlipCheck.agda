{-# OPTIONS --rewriting #-}
-- Machine-checked: the merged translation fix (distributing Ub[_]) does NOT change
-- the two canonS values the rsplit off-handle obligation compares.
module BorrowedCF.Simulation2.RsplitFlipCheck where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Congruence
open import BorrowedCF.Processes.Typed using (BindGroup)
open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)

cc0 : UChan 1
cc0 = (K `unit , 0F , K `unit)

-- ungrown chain [2], P's off-handle borrow at index 1F:
--   triple = chanTriple of a UChan whose FIRST component is the constant  K `unit
A-value : canonₛ (2 ∷ []) cc0 (suc zero)
        ≡ chanTriple (K `unit , 0F , K `unit)
A-value = refl

-- rwk-grown chain [1,2], the SAME borrow now at index 2F:
--   triple = chanTriple of a UChan whose FIRST component is the VARIABLE  ` 0F
B-value : canonₛ (1 ∷ 2 ∷ []) cc0 (suc (suc zero))
        ≡ chanTriple ((` 0F) , suc 0F , K `unit)
B-value = refl
