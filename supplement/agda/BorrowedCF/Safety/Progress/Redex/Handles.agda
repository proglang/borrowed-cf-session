-- | The `drop` / `discard` redexes (agent G1, wave 2).
--
--   The crux of `Simulation/BackwardSoup/Position/Crux.agda` places the handle
--   of an impure constant at the head of the FIRST group of its side, which is
--   exactly the position `R-Drop` / `R-Discard` fire on.  `canon-drop` /
--   `canon-discard` then float the thread into rule position, and `red-in-ctx`
--   puts it back under the ambient process context.
module BorrowedCF.Safety.Progress.Redex.Handles where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Context
import BorrowedCF.Processes.TranslationSoup as TranslationS
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
  using (Proc; ⟪_⟫; _∥_; ν; BindGroup; _⋯ₚ_; _;_⊢ₚ_)
open import BorrowedCF.Reduction.Processes.Typed
  using (_─→ₚ_; R-Drop; R-Discard; R-Struct)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; plug)
import BorrowedCF.Simulation.BackwardSoup.Position as Pos
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (resolve; binderWidth; binderRest)
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head; drop-first-group-singleton)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (CanonRedex; canonRedex; canon-drop; canon-discard; headOfFirstGroup⇒shape)

open import BorrowedCF.Safety.Progress.Redex.Context using (red-in-ctx)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The two rules, with every index given explicitly.
--
--     `R-Drop` and `R-Discard` put the residual under `_⋯ₚ weakenᵣ` and the
--     frame under `_⋯ᶠ* weakenᵣ`.  Leaving their indices to inference makes
--     Agda solve `sum (?b ∷ ?B) + sum ?C + ?n ≡ …`, which it cannot do by
--     pattern unification; spelling the indices out turns the application into
--     a syntactic conversion check.

private
  dropStep :
    {n : ℕ} (bh : ℕ) (D₁ D₂ : BindGroup)
    (E₀ : Frame* (sum (bh L.∷ D₁) + sum D₂ + n))
    (Q₀ : Proc (sum (bh L.∷ D₁) + sum D₂ + n)) →
    ν (suc bh L.∷ D₁) D₂
      (⟪ E₀ ⋯ᶠ* weakenᵣ [ K `drop ·¹ (` 0F) ]* ⟫ ∥ (Q₀ ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (bh L.∷ D₁) D₂ (⟪ E₀ [ * ]* ⟫ ∥ Q₀)
  dropStep bh D₁ D₂ E₀ Q₀ = R-Drop {P = Q₀} {E = E₀}

  discardStep :
    {n : ℕ} (bh : ℕ) (D₁ D₂ : BindGroup)
    (E₀ : Frame* (sum (bh L.∷ D₁) + sum D₂ + n))
    (Q₀ : Proc (sum (bh L.∷ D₁) + sum D₂ + n)) →
    ν (suc bh L.∷ D₁) D₂
      (⟪ E₀ ⋯ᶠ* weakenᵣ [ K `discard ·¹ (` 0F) ]* ⟫ ∥ (Q₀ ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (bh L.∷ D₁) D₂ (⟪ E₀ [ * ]* ⟫ ∥ Q₀)
  discardStep bh D₁ D₂ E₀ Q₀ = R-Discard {P = Q₀} {E = E₀}

------------------------------------------------------------------------
-- 2.  Reading a `CanonRedex` off as a reduction.
--
--     Stated for an ARBITRARY closed process, and consumed by an ordinary
--     pattern match rather than by `with`: abstracting a `CanonRedex` with
--     `with` makes Agda's memory grow without bound (>20 GB), because the
--     with-abstraction has to generalise the `src` index
--     `threadInContext ctx ⟪ E [ K c ·¹ (` x) ]* ⟫ 0F` as well.

private
  fromCanonDrop :
    {P : Proc 0} {src : 𝔽 (TranslationS.processCount P)} →
    CanonRedex P `drop src → Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′
  fromCanonDrop (canonRedex bh D₁ D₂ ab E₀ Q₀ ≋r trk) =
    _ , R-Struct ≋r (red-in-ctx ab (dropStep bh D₁ D₂ E₀ Q₀)) ≋-refl

  fromCanonDiscard :
    {P : Proc 0} {src : 𝔽 (TranslationS.processCount P)} →
    CanonRedex P `discard src → Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′
  fromCanonDiscard (canonRedex bh D₁ D₂ ab E₀ Q₀ ≋r trk) =
    _ , R-Struct ≋r (red-in-ctx ab (discardStep bh D₁ D₂ E₀ Q₀)) ≋-refl

------------------------------------------------------------------------
-- 3.  The redexes.

redex-drop :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
  [] ; [] ⊢ₚ plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
  Σ[ P′ ∈ Proc 0 ] plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ ─→ₚ P′
redex-drop ctx E x ⊢P =
  fromCanonDrop
    (canon-drop E (resolve ctx x)
      (headOfFirstGroup⇒shape (resolve ctx x)
        (impure-redex-head {ctx = ctx} {E = E} {x = x} ⊢P Pos.`drop))
      ⊢P)

redex-discard :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
  [] ; [] ⊢ₚ plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ →
  Σ[ P′ ∈ Proc 0 ] plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ ─→ₚ P′
redex-discard ctx E x ⊢P =
  fromCanonDiscard
    (canon-discard E (resolve ctx x)
      (headOfFirstGroup⇒shape (resolve ctx x)
        (impure-redex-head {ctx = ctx} {E = E} {x = x} ⊢P Pos.`discard))
      ⊢P)

------------------------------------------------------------------------
-- 4.  `drop` pins the group SHAPE as well (`Crux.drop-first-group-singleton`),
--     re-exported for the process-progress proof.

drop-first-group :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
  [] ; [] ⊢ₚ plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
  (binderWidth (resolve ctx x) ≡ 1) × (binderRest (resolve ctx x) ≢ L.[])
drop-first-group ctx E x = drop-first-group-singleton {ctx = ctx} {E = E} {x = x}
