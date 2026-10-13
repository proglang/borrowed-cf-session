-- | Exact-image dispatcher for backward soup simulation.
module BorrowedCF.Simulation.BackwardSoup.Main where

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction

open import BorrowedCF.Simulation.ForwardSoup.World using (GlobalImage)
open import BorrowedCF.Simulation.BackwardSoup.Statement
  using (_≈ˢ_; ≈ˢ-refl)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Exp using (exp-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Fork using (fork-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.New using (new-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.LSplit using (lsplit-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.RSplit using (rsplit-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Drop using (drop-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Discard using (discard-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Acq using (acq-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Close using (close-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Com using (com-reflect)
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Choice using (choice-reflect)

open Typed using (_;_⊢ₚ_)

Backward-Core : Set
Backward-Core =
  ∀ {P : Typed.Proc 0} {n m n′ m′ : ℕ}
    {C : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  [] ; Context.[] ⊢ₚ P →
  GlobalImage P C →
  C SoupReduction.─→ₚ C′ →
  Σ[ P′ ∈ Typed.Proc 0 ] (P TypedReduction.─→ₚ P′) ×
  Σ[ C₀′ ∈ Soup.Config n′ m′ ] GlobalImage P′ C₀′ × C₀′ ≈ˢ C′

private
  exact-result :
    ∀ {P P′ : Typed.Proc 0} {n m : ℕ} {C : Soup.Config n m} →
    P TypedReduction.─→ₚ P′ →
    GlobalImage P′ C →
    Σ[ Q ∈ Typed.Proc 0 ] (P TypedReduction.─→ₚ Q) ×
    Σ[ D ∈ Soup.Config n m ] GlobalImage Q D × D ≈ˢ C
  exact-result red image = _ , red , _ , image , ≈ˢ-refl

backward-core : Backward-Core
backward-core ⊢P image (SoupReduction.RUS-Exp j red)
  with exp-reflect ⊢P image red
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image (SoupReduction.RUS-Fork j F Ve selected)
  with fork-reflect j F Ve selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image (SoupReduction.RUS-New j i F selected)
  with new-reflect j i F selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image (SoupReduction.RUS-LSplit j i side F openEq selected)
  with lsplit-reflect j i side F openEq selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image
  (SoupReduction.RUS-RSplit j i side F before after openEq flags selected) =
  rsplit-reflect j i side F before after openEq flags selected ⊢P image
backward-core ⊢P image
  (SoupReduction.RUS-Drop j i side F before after openEq flags selected)
  with drop-reflect j i side F before after openEq flags selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image (SoupReduction.RUS-Discard j F Ve selected)
  with discard-reflect j F Ve selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image
  (SoupReduction.RUS-Acquire j i side F before after openEq flags selected)
  with acq-reflect j i side F before after openEq flags selected ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image
  (SoupReduction.RUS-Close j k i side₁ side₂ F₁ F₂
    apart opposite channel selected₁ selected₂)
  with close-reflect j k i side₁ side₂ F₁ F₂
         apart opposite channel selected₁ selected₂ ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image
  (SoupReduction.RUS-Com j k i side₁ side₂ F₁ F₂
    apart opposite openEq Ve selected₁ selected₂)
  with com-reflect j k i side₁ side₂ F₁ F₂
         apart opposite openEq Ve selected₁ selected₂ ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
backward-core ⊢P image
  (SoupReduction.RUS-Choice j k i side₁ side₂ F₁ F₂ choice
    apart opposite openEq selected₁ selected₂)
  with choice-reflect j k i side₁ side₂ F₁ F₂ choice
         apart opposite openEq selected₁ selected₂ ⊢P image
... | _ , sourceRed , image′ = exact-result sourceRed image′
