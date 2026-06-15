{-# OPTIONS --rewriting #-}
module BorrowedCF.Types where

open import BorrowedCF.Types.Syntax public
open import BorrowedCF.Types.Predicates public
open import BorrowedCF.Types.Equivalence public

import BorrowedCF.Types.Substitution as Substitution

open Substitution using
  ( dual-⋯ᵣ
  ; skips-⋯
  ; skips-⋯ᵣ⁻¹
  ; skips-⋯⁻¹
  ; skips-irr-⋯
  ; 𝓖-⋯
  ; unfold
  ; ⊢unfold
  )
  public
