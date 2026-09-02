-- | Forward simulation from the typed process calculus to process soups.
module BorrowedCF.Simulation.ForwardSoup where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as TypedReduction

open import BorrowedCF.Context.Base using (Struct; [])
open Typed using (_;_⊢ₚ_)

open import BorrowedCF.Simulation.ForwardSoup.Base
open import BorrowedCF.Simulation.ForwardSoup.Exp
open import BorrowedCF.Simulation.ForwardSoup.Fork
open import BorrowedCF.Simulation.ForwardSoup.New
open import BorrowedCF.Simulation.ForwardSoup.Close
open import BorrowedCF.Simulation.ForwardSoup.Choice
open import BorrowedCF.Simulation.ForwardSoup.Com using (U-com)

import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 as ComHelpers

Forward-Sim : Set
Forward-Sim =
  ∀ {P P′ : Typed.Proc 0} {n m} {C : Soup.Config n m} →
  [] ; [] ⊢ₚ P →
  SoupImage P C →
  P TypedReduction.─→ₚ P′ →
  StepImage P′ C

sim→ : Forward-Sim
sim→ ⊢P image (TypedReduction.R-Exp red)
  with U-exp image red
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image (TypedReduction.R-Fork E V)
  with U-fork {E = E} image V
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image (TypedReduction.R-New {s = s} E)
  with U-new {E = E} {s = s} image
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image
  (TypedReduction.R-Com {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂}
    {e = e} {P = P₀} {E₁ = E₁} {E₂ = E₂} V)
  with ComHelpers.com-head≥1 {E₁ = E₁} {E₂ = E₂} {P = P₀} V ⊢P
... | b₁′ , refl
  with ComHelpers.com-head≥2 {E₁ = E₁} {E₂ = E₂} {P = P₀} V ⊢P
... | b₂′ , refl
  with U-com {b₁ = b₁′} {b₂ = b₂′} {B₁ = B₁} {B₂ = B₂}
        {E₁ = E₁} {E₂ = E₂} {P = P₀} {e = e} V ⊢P image
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image (TypedReduction.R-Choice E₁ E₂ side)
  with U-choice {E₁ = E₁} {E₂ = E₂} {side = side} image
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image TypedReduction.R-LSplit = {!!}
sim→ ⊢P image TypedReduction.R-RSplit = {!!}
sim→ ⊢P image TypedReduction.R-Drop = {!!}
sim→ ⊢P image TypedReduction.R-Acq = {!!}
sim→ ⊢P image (TypedReduction.R-Close {E₁ = E₁} {E₂ = E₂})
  with U-close {E₁ = E₁} {E₂ = E₂} image
... | C′ , step , image′ = _ , _ , C′ , step , image′
sim→ ⊢P image TypedReduction.R-Discard = {!!}
sim→ ⊢P image (TypedReduction.R-Par red) = {!!}
sim→ ⊢P image (TypedReduction.R-Bind red) = {!!}
sim→ ⊢P image (TypedReduction.R-Struct eq₁ red eq₂) = {!!}
