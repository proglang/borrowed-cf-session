{-# OPTIONS --rewriting #-}
module BorrowedCF.Types where

open import BorrowedCF.Types.Syntax as Syntax hiding (dual)
open import BorrowedCF.Types.Substitution as Substitution hiding (module Syntax)

open import BorrowedCF.Types.Predicates public

module UV where
  open import BorrowedCF.Prelude
  open UVar public

  -- Sub = (α : UVar) → ∃[ s ] (UVar.Mobile α → Bounded s)
  Sub = ℕ → 𝕊 0

  dual : UVar → UVar
  dual α = record α { pol = dualPol (pol α) }

  dual/id : UVar → 𝕊 0 → 𝕊 0
  dual/id record { pol = ‼ } = id
  dual/id record { pol = ⁇ } = Syntax.dual

  ap : UVar → Sub → 𝕊 0
  ap α σ = dual/id α (σ (var α))

  dual/dual : (α : UVar) (σ : Sub) → Syntax.dual (ap α σ) ≡ ap (dual α) σ
  dual/dual record { pol = ‼ } σ = refl
  dual/dual record { pol = ⁇ } σ = refl

open Syntax public

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

open import BorrowedCF.Types.Equivalence public
