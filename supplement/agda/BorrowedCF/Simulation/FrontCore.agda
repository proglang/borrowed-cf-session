-- Fixed-front soup target, using the existing unary expression syntax.
-- The general reduction is retained as a proof tool for canonical images
-- and flag-permutation transport; FrontStep is the paper's target relation.
module BorrowedCF.Simulation.FrontCore where

import Data.Nat.Properties as NatP
open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as SourceReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as RUS
import BorrowedCF.Simulation.ForwardSoup.Local as Forward
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; initialGlobalImage)
open import BorrowedCF.Simulation.BackwardSoup.Statement
  using (_≈ˢ_; ≈ˢ-refl; ≈ˢ-trans)
open import BorrowedCF.Simulation.BackwardSoup.SlotInsert
  using (rsplitResult; rsplit-positions; insertDrop-prefix)
open import BorrowedCF.Simulation.BackwardSoup.SlotBisim using (slot-bisim)

open Typed using (_;_⊢ₚ_)
open Nat.Variables

-- IsFront tests a reduction witness, never an operand or runtime handle.
IsFront : ∀ {n m n′ m′} {C : Soup.Config n m} {D : Soup.Config n′ m′} →
  C RUS.─→ₚ D → Set
IsFront (RUS.RUS-RSplit j i side F before after opened flags selected) = before ≡ []
IsFront _ = ⊤

record FrontStep {n m n′ m′ : ℕ}
  (C : Soup.Config n m) (D : Soup.Config n′ m′) : Set where
  constructor front-step
  field
    underlying : C RUS.─→ₚ D
    frontOnly : IsFront underlying
open FrontStep public

-- The actual physical configuration need only be a slot permutation of a
-- canonical GlobalImage; the permutation acts on flags AND every phi ref.
FrontImage : Typed.Proc 0 → Soup.Config n m → Set
FrontImage {n} {m} P C = Σ[ C₀ ∈ Soup.Config n m ] GlobalImage P C₀ × C₀ ≈ˢ C

private
  prefix-bound : (before after : List Soup.Flag) →
    L.length before Nat.≤ L.length (before L.++ after)
  prefix-bound before after =
    subst (L.length before Nat.≤_) (sym (L.length-++ before))
      (NatP.m≤m+n (L.length before) (L.length after))

  keep-step : ∀ {n m n′ m′} {C : Soup.Config n m} {D : Soup.Config n′ m′}
    (step : C RUS.─→ₚ D) → IsFront step →
    Σ[ D₀ ∈ Soup.Config n′ m′ ] FrontStep C D₀ × D ≈ˢ D₀
  keep-step {D = D} step front = D , front-step step front , ≈ˢ-refl

-- Every old step has a front-only representative, at the same source and
-- with the same channel/thread counts. This is the key new lemma.
normalize-step : ∀ {n m n′ m′} {C : Soup.Config n m} {D : Soup.Config n′ m′} →
  C RUS.─→ₚ D →
  Σ[ D₀ ∈ Soup.Config n′ m′ ] FrontStep C D₀ × D ≈ˢ D₀
normalize-step {D = D}
  (RUS.RUS-RSplit {cs = cs} {ts = ts}
    j i side F before after {e₁ = e₁} {e₂ = e₂} opened flags selected) =
  frontResult ,
  front-step (RUS.RUS-RSplit j i side F [] (before L.++ after)
    opened flags selected) refl ,
  subst (_≈ˢ frontResult) oldResultEq positions
  where
  frontResult = rsplitResult cs ts j i side F (before L.++ after) zero e₁ e₂

  positions = rsplit-positions cs ts j i side F (before L.++ after)
    (L.length before) zero e₁ e₂ (prefix-bound before after) Nat.z≤n

  oldResultEq :
    rsplitResult cs ts j i side F (before L.++ after) (L.length before) e₁ e₂ ≡ D
  oldResultEq =
    cong (λ fs → Soup.config
      (V.updateAt cs i (RUS.setEndpointFlags side fs)) (Soup.threads D))
      (insertDrop-prefix before after)
normalize-step step@(RUS.RUS-Exp j red) = keep-step step tt
normalize-step step@(RUS.RUS-Fork j F value selected) = keep-step step tt
normalize-step step@(RUS.RUS-New j i F selected) = keep-step step tt
normalize-step step@(RUS.RUS-LSplit j i side F opened selected) = keep-step step tt
normalize-step step@(RUS.RUS-Drop j i side F before after opened flags selected) =
  keep-step step tt
normalize-step step@(RUS.RUS-Discard j F value selected) = keep-step step tt
normalize-step step@(RUS.RUS-Acquire j i side F before after opened flags selected) =
  keep-step step tt
normalize-step step@(RUS.RUS-Close j k i side₁ side₂ F₁ F₂ distinct opposite flags selected₁ selected₂) =
  keep-step step tt
normalize-step step@(RUS.RUS-Com j k i side₁ side₂ F₁ F₂ distinct opposite opened value selected₁ selected₂) =
  keep-step step tt
normalize-step step@(RUS.RUS-Choice j k i side₁ side₂ F₁ F₂ choice distinct opposite opened selected₁ selected₂) =
  keep-step step tt

-- Fixed-front dynamics also respects slot equivalence, although simply
-- transporting a front split need not leave its insertion at the front.
-- Normalize the transported step, then compose its result equivalences.
front-slot-bisim : ∀ {n m n′ m′}
  {C D : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  C ≈ˢ D → FrontStep C C′ →
  Σ[ D′ ∈ Soup.Config n′ m′ ] FrontStep D D′ × C′ ≈ˢ D′
front-slot-bisim equivalent step with slot-bisim equivalent (underlying step)
... | D′ , transported , eq₁ with normalize-step transported
... | D₀ , normalized , eq₂ = D₀ , normalized , ≈ˢ-trans eq₁ eq₂

-- Exact canonical forward simulation, quotient transport, then front
-- normalization. No source typing/safety or confinement proof is changed.
forward-front : ∀ {P P′ : Typed.Proc 0} {n m} {C : Soup.Config n m} →
  [] ; Context.[] ⊢ₚ P →
  FrontImage P C → P SourceReduction.─→ₚ P′ →
  Σ[ n′ ∈ ℕ ] Σ[ m′ ∈ ℕ ] Σ[ C′ ∈ Soup.Config n′ m′ ]
    FrontStep C C′ × FrontImage P′ C′
forward-front typing (C₀ , image , equivalent) sourceStep
  with Forward.sim-global typing image sourceStep
... | n′ , m′ , C₁ , canonicalStep , nextImage
  with slot-bisim equivalent canonicalStep
... | C₂ , transportedStep , eq₁ with normalize-step transportedStep
... | C₃ , frontStep , eq₂ =
  n′ , m′ , C₃ , frontStep , C₁ , nextImage , ≈ˢ-trans eq₁ eq₂

-- Initial translation, including its expression clauses, remains unchanged.
initial-front : (P : Typed.Proc 0) →
  FrontImage P
    (Soup.config
      (proj₁ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ())))
      (proj₂ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ()))))
initial-front P = _ , initialGlobalImage P , ≈ˢ-refl
