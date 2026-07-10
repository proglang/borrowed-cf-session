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

  skips-dual/id⁺ : (α : UVar) → Skips s → Skips (dual/id α s)
  skips-dual/id⁺ record { pol = ‼ } = id
  skips-dual/id⁺ record { pol = ⁇ } = skips-dual⁺

  skips-dual/id⁻ : (α : UVar) → Skips (dual/id α s) → Skips s
  skips-dual/id⁻ record { pol = ‼ } = id
  skips-dual/id⁻ record { pol = ⁇ } = skips-dual⁻

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

  subAll : ¬ Skips {0} s → Sub
  subAll {s = s} ¬Ss = record
    { ap = λ α → dual/id α s
    ; ap-¬skips = λ α → ¬Ss ∘ skips-dual/id⁻ α
    ; ap-dual/dual = λ where
        record { pol = ‼ } → refl
        record { pol = ⁇ } → dual-involutive s
    }

  someSub : Sub
  someSub = subAll {s = end ‼} λ()

data Constraint : Set where
  C-Eq : 𝕋 → 𝕋 → Constraint
  C-Mob : 𝕋 → Constraint

CSet : Set
CSet = List Constraint

variable
  Δ Δ₁ Δ₂ Δ₃ Δ′ : CSet
