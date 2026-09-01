module BorrowedCF.Terms.BaseSoup.Properties where

open import Data.Maybe using (just)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup

open Nat.Variables

resolveRef-zero :
  (r : PhiRef n) → resolveRef 0 r ≡ just r
resolveRef-zero (x , k) = refl

resolveRef-suc :
  ∀ d (r : PhiRef (d + n)) →
  resolveRef (suc d) (renameRef suc r) ≡ resolveRef d r
resolveRef-suc zero (x , k) = refl
resolveRef-suc (suc d) (zero , k) = refl
resolveRef-suc (suc d) (suc x , k) with Fin.splitAt d x
... | inj₁ _ = refl
... | inj₂ _ = refl
