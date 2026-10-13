-- Machine-checked refutation of the *unconditional* front-¬mobile lemma the
-- telescoped backward R-Com needs for its `¬u0`.
--
-- front-¬mobile would claim: for New s and any BindCtx (s ; end p) B Γ, the
-- global front channel (slot 0F) is ¬ Mobile.  This is FALSE: a leading
-- cons-acq block whose single channel carries the WHOLE acq-New session is
-- Mobile (ComColocated.mob-whole).  Here we build exactly such an inhabited
-- BindCtx and inhabit `Mobile (lookup Γ 0F)`, so the ¬ can never hold.
module BorrowedCF.Simulation.Backward.ComFrontMobileCex where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
  using (BindCtx; BindCtx′; last; cons; cons-acq; nil)
open import Data.Nat.ListAction using (sum)

open Fin.Patterns

sN : 𝕊 0
sN = msg ‼ `⊤

s-New : New sN
s-New = P.msg

whole : 𝕊 0
whole = acq ; (sN ; end ‼)

¬sk-whole : ¬ Skips whole
¬sk-whole (() ; _)

-- Inhabited: a New-derived ν whose front block is a cons-acq marker over a
-- single channel carrying the whole acq-New session.
cexΓ : Ctx (sum (0 ∷ 1 ∷ []))
cexΓ = ⟨ whole ⟩ ∷ []

cexBC : BindCtx (sN ; end ‼) (0 ∷ 1 ∷ []) cexΓ
cexBC = cons-acq (last (cons whole skip ¬sk-whole ≃-skipʳ (nil skip)))

-- The front slot IS Mobile (its Bounded whole-continuation reaches `end`).
front-Mobile : Mobile (lookup cexΓ 0F)
front-Mobile = P.⟨ (sN ; end ‼) , (P.-;₂ P.end) , ≃-refl ⟩

-- Hence the front-¬mobile lemma (¬ Mobile of the front) is unprovable:
front-¬mobile-would-refute : ¬ Mobile (lookup cexΓ 0F) → ⊥
front-¬mobile-would-refute nm = nm front-Mobile
