-- | THE RECURRING OBSTRUCTION, distilled.
--
--   This module is SELF-CONTAINED: it imports only the standard library, uses
--   none of the project's machinery (no φ-telescopes, no translation U[_], no
--   bind groups, no HandleId/canonₛ). It isolates the single mathematical fact
--   that the reverse simulation (`sim←-base`, the paper's backward/completeness
--   conjecture) keeps bottoming out at, regardless of how the rest is formulated.
--
--   THE TWO INGREDIENTS, both present in the real calculus verbatim:
--
--   (1) Every reduction rule fires on a FIXED ν-bound endpoint.  In the real
--       rules the send/recv/acq/drop/close redex names the innermost bound
--       channel `0F`:  R-Com `send · (e ⊗ ` 0F)`, R-Acq `acq · ` 0F`, R-Drop
--       `drop · ` 0F`, R-Close `end · ` 0F`, and the untyped RU-* likewise on
--       `wkΦ Φ 0F`.  Here that is `fire : ν (use a) ─→ ✓` — it fires on `a`, the
--       first bound endpoint, and on nothing else.
--
--   (2) Structural congruence can PERMUTE the two bound endpoints.  In the real
--       calculus this is  ν-swap′ : ν P ≋ ν (P ⋯ₚ swapᵣ 1 1)  — swapping the two
--       channels a ν binds.  Here that is `ν-swap : ν P ≋ ν (swap P)`.
--
--   THE OBLIGATION the reverse simulation needs (and cannot get):  to reflect an
--   untyped step against a process that is only ≋-equivalent to a translation
--   image, you must REPLAY the step across each ≋ link — and, crucially, replay
--   it BY A GENUINE RULE, so the reflected derivation is no larger.  A terminating
--   reverse-simulation recursion needs exactly this measure-preserving replay
--   (`GenuineReplay` below).
--
--   THE FAILURE (machine-checked as `replay-fails`):  ν-swap turns the redex on
--   `a` into a redex on `b`, and NO rule fires on `b`.  So there is no genuine
--   replay — the swapped process is simply stuck.  The only escape the real
--   calculus has is to re-wrap the ORIGINAL reduction under the congruence (its
--   `RU-Struct` rule: from `R ≋ S` and `R ─→ Q` conclude `S ─→ Q`), but that
--   GROWS the derivation instead of replaying it, so the reverse-simulation
--   recursion that peels ≋ links and re-wraps them never shrinks.  That is the
--   loop we keep hitting: genuine replay is impossible (this module), and the
--   wrapper that saves existence destroys the termination measure.
module BorrowedCF.ReplayObstruction where

open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A ν binds a dual pair of endpoints.  `a` is the innermost ("0F"), `b` the
-- other ("1F").
------------------------------------------------------------------------

data Endpoint : Set where
  a b : Endpoint

infixr 40 ν_
infix  4 _─→_
infix  4 _≋_

data Proc : Set where
  ✓    : Proc                 -- terminated
  use  : Endpoint → Proc      -- a thread poised to act on one endpoint
  ν_   : Proc → Proc          -- binds the dual pair (a , b)

------------------------------------------------------------------------
-- (1) Reduction fires only on the first bound endpoint `a`
--     (mirrors R-Com/R-Acq/R-Drop/R-Close and RU-* all reading 0F).
------------------------------------------------------------------------

data _─→_ : Proc → Proc → Set where
  fire : ν (use a) ─→ ✓

-- There is NO reduction from a redex on the OTHER endpoint `b`:
no-step-from-b : ∀ {Q} → ¬ (ν (use b) ─→ Q)
no-step-from-b ()

------------------------------------------------------------------------
-- (2) The endpoint-swapping renaming and the ν-swap congruence
--     (mirrors ν-swap′ : ν P ≋ ν (P ⋯ₚ swapᵣ 1 1)).
------------------------------------------------------------------------

swap : Proc → Proc
swap ✓        = ✓
swap (use a)  = use b
swap (use b)  = use a
swap (ν P)    = ν P          -- an inner ν binds different channels; irrelevant here

data _≋_ : Proc → Proc → Set where
  ν-swap : ∀ {P} → ν P ≋ ν (swap P)

------------------------------------------------------------------------
-- THE OBLIGATION: measure-preserving replay of a reduction across a ≋ link.
-- (What a terminating reverse-simulation recursion requires.)
------------------------------------------------------------------------

GenuineReplay : Set
GenuineReplay = ∀ {R S Q} → R ≋ S → R ─→ Q → ∃ λ Q′ → (S ─→ Q′) × (Q ≋ Q′)

------------------------------------------------------------------------
-- THE FAILURE, machine-checked.  R = ν (use a) fires; its ν-swap is
-- S = ν (use b), which cannot reduce — so the replay cannot exist.
------------------------------------------------------------------------

replay-fails : ¬ GenuineReplay
replay-fails replay with replay (ν-swap {use a}) fire
... | _ , step-from-b , _ = no-step-from-b step-from-b
