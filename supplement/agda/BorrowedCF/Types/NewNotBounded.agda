-- | The ends-theory decider for the backward-com "separated firing com" question.
--
--   `ComSeparatedCex` showed a MOBILE `acq;ret` front with a msg channel behind it is
--   a well-typed BIND-CONTEXT block.  The question is whether it is reachable over a
--   NEW-derived com ν.  It is NOT — the crux is a clean induction:
--
--     new⇒¬bounded : New s → ¬ Bounded s
--
--   (New leaves = var/msg/skip; Bounded leaves = end/ret — disjoint), and its corollary
--
--     new-cont⇒¬mobile-acq : New X → ¬ Mobile ⟨ acq ; X ⟩
--
--   the cons-acq front of a New-derived com ν has a New continuation, so 0F is NOT
--   Mobile — the parallel split that a separated firing com needs is unavailable.
--   Verdict (A): the com is co-located; no linked-φ obstruction.
module BorrowedCF.Types.NewNotBounded where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence using (_≃_; ≃-sym)
import BorrowedCF.Types.Predicates as P
open P using (New; Bounded; Mobile)
open import Data.Sum using ([_,_]′)

new⇒¬bounded : ∀ {n} {s : 𝕊 n} → New s → ¬ Bounded s
new⇒¬bounded P.`-          b               = P.¬bounded-` b
new⇒¬bounded P.msg         ()
new⇒¬bounded P.skip        ()
new⇒¬bounded (N₁ P.; N₂) (b P.;₁ sk) = new⇒¬bounded N₁ b
new⇒¬bounded (N₁ P.; N₂) (P.-;₂ b)   = new⇒¬bounded N₂ b
new⇒¬bounded (P.mu N)      (P.mu b)        = new⇒¬bounded N b
new⇒¬bounded (P.brn N₁ N₂) (P.brn b₁ b₂)   = new⇒¬bounded N₁ b₁

-- DECIDER: an acq-headed handle whose continuation is New is NOT Mobile.
new-cont⇒¬mobile-acq : ∀ {X : 𝕊 0} → New X → ¬ Mobile ⟨ acq ; X ⟩
new-cont⇒¬mobile-acq NX P.⟨ s′ , bnd , eq ⟩ =
  [ (λ { (() , _) })
  , (λ bX → new⇒¬bounded NX bX)
  ]′ (P.bounded-;⁻ (P.≃-bounded (≃-sym eq) (P.-;₂ bnd)))
