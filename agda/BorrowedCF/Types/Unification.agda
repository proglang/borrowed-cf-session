{-# OPTIONS --rewriting #-}

module BorrowedCF.Types.Unification where

open import BorrowedCF.Prelude

import BorrowedCF.Types.Syntax as Syn

open Syn hiding (UVar; dual)

module UV where
  open Syn using (UVar) public
  open UVar public

  dual : UVar → UVar
  dual α = record α { pol = dualPol (pol α) }

  dual/id : UVar → 𝕊 0 → 𝕊 0
  dual/id record { pol = ‼ } = id
  dual/id record { pol = ⁇ } = Syn.dual

  record Sub : Set where
    field
      ap : UVar → 𝕊 0
      ap-¬skips : ∀ α → ¬ Skips (ap α)
      ap-dual/dual : ∀ α → Syn.dual (ap α) ≡ ap (dual α)

  open Sub public

  fresh : ℕ → UVar
  fresh k = uvar ‼ k

  weaken : ℕ → Sub
  weaken n = record
    { ap = λ α → `` uvar (pol α) (n + var α)
    ; ap-¬skips = λ α ()
    ; ap-dual/dual = λ α → refl
    }

  someSub : Sub
  someSub = record { ap = end ∘ pol ; ap-¬skips = λ _ () ; ap-dual/dual = λ _ → refl }

Constraint = 𝕋 × 𝕋

CSet : Set
CSet = List Constraint

variable
  Δ Δ₁ Δ₂ Δ₃ Δ′ : CSet
