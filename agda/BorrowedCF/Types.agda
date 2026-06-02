{-# OPTIONS --rewriting #-}
module BorrowedCF.Types where

open import BorrowedCF.Types.Equivalence public
open import BorrowedCF.Types.Predicates public
open import BorrowedCF.Types.Syntax public

open import BorrowedCF.Types.Substitution using
  ( skips-⋯
  ; skips-⋯ᵣ⁻¹
  ; skips-⋯⁻¹
  ; skips-irr-⋯
  ; 𝓖-⋯
  ; unfold
  ; ⊢unfold
  )
  public
