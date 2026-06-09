{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.Confine where

open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Data.Nat.Solver using (module +-*-Solver)

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (Unr)
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext

open Nat.Variables
open Nat using (_≤_; +-comm; +-assoc; +-identityʳ; ≤-reflexive; ≤-trans; +-mono-≤; z≤n)
open Variables

variable
  x y : 𝔽 n

-- Multiplicity of a variable in an ordered context.  Unlike `dom` (a Subset,
-- which forgets repetition), `count` tracks how many `` ` x `` leaves equal x —
-- the bookkeeping needed to express linearity of a single channel.
count : 𝔽 n → Struct n → ℕ
count x (` y) with x Fin.≟ y
... | yes _ = 1
... | no  _ = 0
count x []      = 0
count x (α ∥ β) = count x α + count x β
count x (α ; β) = count x α + count x β

-- A variable whose type is NOT unrestricted does not occur in an unrestricted
-- context, hence has count 0 there.
unrCx⇒count0 : ¬ Unr (Γ x) → UnrCx Γ α → count x α ≡ 0
unrCx⇒count0 ¬u []        = refl
unrCx⇒count0 ¬u (C₁ ∥ C₂) = cong₂ _+_ (unrCx⇒count0 ¬u C₁) (unrCx⇒count0 ¬u C₂)
unrCx⇒count0 ¬u (C₁ ; C₂) = cong₂ _+_ (unrCx⇒count0 ¬u C₁) (unrCx⇒count0 ¬u C₂)
unrCx⇒count0 {x = x} ¬u (`_ {y} py) with x Fin.≟ y
... | yes refl = ⊥-elim (¬u py)
... | no  _    = refl

-- `count x` is invariant under one-step ≈ — provided x is non-unrestricted, so
-- that the only duplicating rule (∥′-dup, on an UnrCx) leaves it untouched.
count-≈′ : ¬ Unr (Γ x) → Γ ∶ α ≈′ β → count x α ≡ count x β
count-≈′ {x = x} ¬u (;′-assoc {α} {β} {γ}) = +-assoc (count x α) (count x β) (count x γ)
count-≈′ ¬u (;′-cong₁ s) = cong (_+ _) (count-≈′ ¬u s)
count-≈′ ¬u (;′-cong₂ s) = cong (_ +_) (count-≈′ ¬u s)
count-≈′ {x = x} ¬u (∥′-unit {α}) = +-identityʳ (count x α)
count-≈′ {x = x} ¬u (∥′-assoc {α} {β} {γ}) = +-assoc (count x α) (count x β) (count x γ)
count-≈′ {x = x} ¬u (∥′-comm {α} {β}) = +-comm (count x α) (count x β)
count-≈′ ¬u (∥′-cong₁ s) = cong (_+ _) (count-≈′ ¬u s)
count-≈′ {x = x} ¬u (∥′-dup {α} U) =
  unrCx⇒count0 ¬u U ■ sym (cong₂ _+_ (unrCx⇒count0 ¬u U) (unrCx⇒count0 ¬u U))
count-≈′ ¬u (∥′-tm-; _) = refl

count-≈ : ¬ Unr (Γ x) → Γ ∶ α ≈ β → count x α ≡ count x β
count-≈ ¬u ε             = refl
count-≈ ¬u (fwd s ◅ rest) = count-≈′ ¬u s ■ count-≈ ¬u rest
count-≈ ¬u (bwd s ◅ rest) = sym (count-≈′ ¬u s) ■ count-≈ ¬u rest

-- The linearity lever: ≼ never increases the multiplicity of a non-unrestricted
-- variable (≼-∅ drops, ≼-wk rearranges, ≼-refl is ≈).  Count analogue of ≼⇒dom⊆.
≼⇒count≤ : ¬ Unr (Γ x) → Γ ∶ α ≼ β → count x α ≤ count x β
≼⇒count≤ ¬u (≼-refl eq) = ≤-reflexive (count-≈ ¬u eq)
≼⇒count≤ ¬u (≼-∅ _)     = z≤n
≼⇒count≤ {x = x} ¬u (≼-wk {α₁} {α₂} {β₁} {β₂}) = ≤-reflexive (lemma (count x α₁) (count x α₂) (count x β₁) (count x β₂))
  where
    lemma : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lemma a b c d = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl a b c d
      where open +-*-Solver
≼⇒count≤ ¬u (≼-trans x y) = ≤-trans (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)
≼⇒count≤ ¬u (≼-cong-; x y) = +-mono-≤ (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)
≼⇒count≤ ¬u (≼-cong-∥ x y) = +-mono-≤ (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)
