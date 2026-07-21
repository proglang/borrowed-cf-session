-- | Phase 3: the equivalence `~` on normal forms.
--
--   Two normal forms are equivalent when one is reachable from the other by
--   permuting binders, permuting threads, and inserting/deleting spent `unit`
--   threads.  The design decision here is to GENERATE `~` from ADJACENT binder
--   transpositions rather than to build a permutation groupoid: then `~` is an
--   equivalence and a tν/tφ congruence by construction, and a `~` derivation
--   still yields a concrete composite renaming for downstream redex location.
--
--   Each transposition carries a PREFIX telescope `s`, so it can fire at any
--   depth.  Without it the generators only act at the head and `~` is not a
--   congruence — pushing a binder outside has to move the generator one level
--   deeper, which `s` makes definitional (`tν s ++ᵗ u ≡ tν (s ++ᵗ u)`).
--
--   The four transpositions are exactly the calculus's own binder-permuting
--   generators, with exactly their renamings:
--
--       perm-ν1  ↔ ν-swap′    swapᵣ 1 1
--       perm-νν  ↔ ν-comm′    assocSwapᵣ 2 2
--       perm-φφ  ↔ φ-comm′    assocSwapᵣ 1 1
--       perm-νφ  ↔ νφ-comm′   assocSwapᵣ 1 2
--
--   All four are ENDOmorphisms on their scope (`1 + (2 + n)` and `2 + (1 + n)`
--   are definitionally equal, etc.), which is what lets `liftId` push them under
--   a telescope with no `subst` — the transport trap that the width-indexed
--   telescope would have sprung here.
module BorrowedCF.Simulation.Support.Normal.Equiv where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Pushing a scope ENDOmorphism under a telescope.
------------------------------------------------------------------------

-- Unlike `Rename.liftRen`, this keeps the inner scope FIXED, so it needs no
-- transport.  That is exactly why the four transpositions above are usable.
liftId : ∀ {n k} (t : Tel n k) → (n →ᵣ n) → k →ᵣ k
liftId []       ρ = ρ
liftId (tν t)   ρ = liftId t (ρ ↑* 2)
liftId (tφ _ t) ρ = liftId t (ρ ↑)

------------------------------------------------------------------------
-- One-step generators.
------------------------------------------------------------------------

data _~₁_ {n} : NF n → NF n → Set where

  -- swap the two names bound by a single ν
  perm-ν1 : ∀ {j k} (s : Tel n j) (t : Tel (2 + j) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tν t) es ~₁ mkNF (s ++ᵗ tν t) (map (_⋯ liftId t (swapᵣ 1 1)) es)

  -- transpose two adjacent ν binders
  perm-νν : ∀ {j k} (s : Tel n j) (t : Tel (2 + (2 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tν (tν t)) es ~₁ mkNF (s ++ᵗ tν (tν t)) (map (_⋯ liftId t (assocSwapᵣ 2 2)) es)

  -- transpose two adjacent φ cells (the flags travel with them)
  perm-φφ : ∀ {j k} (s : Tel n j) (x y : Flag) (t : Tel (1 + (1 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tφ x (tφ y t)) es ~₁ mkNF (s ++ᵗ tφ y (tφ x t)) (map (_⋯ liftId t (assocSwapᵣ 1 1)) es)

  -- pull a φ cell out of a ν  (the νφ-comm escape, at the normal-form level)
  perm-νφ : ∀ {j k} (s : Tel n j) (x : Flag) (t : Tel (1 + (2 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tν (tφ x t)) es ~₁ mkNF (s ++ᵗ tφ x (tν t)) (map (_⋯ liftId t (assocSwapᵣ 1 2)) es)

  -- permute the threads
  perm-thr : ∀ {k} (t : Tel n k) {es es′ : List (Tm k)} →
    es ↭ es′ → mkNF t es ~₁ mkNF t es′

  -- delete a spent `unit` thread
  unit-del : ∀ {k} (t : Tel n k) (es : List (Tm k)) →
    mkNF t (K `unit ∷ es) ~₁ mkNF t es

infix 4 _~_

_~_ : ∀ {n} → NF n → NF n → Set
_~_ = EqClosure _~₁_

~-refl : ∀ {n} {N : NF n} → N ~ N
~-refl = Eq*.reflexive _

~-sym : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → N₂ ~ N₁
~-sym = Eq*.symmetric _

~-trans : ∀ {n} {N₁ N₂ N₃ : NF n} → N₁ ~ N₂ → N₂ ~ N₃ → N₁ ~ N₃
~-trans = Eq*.transitive _

------------------------------------------------------------------------
-- Congruences: `~` is compatible with pushing a binder on the outside.
------------------------------------------------------------------------

νNF : ∀ {n} → NF (2 + n) → NF n
νNF (mkNF t es) = mkNF (tν t) es

φNF : ∀ {n} → Flag → NF (1 + n) → NF n
φNF f (mkNF t es) = mkNF (tφ f t) es

~₁-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~₁ N₂ → νNF N₁ ~₁ νNF N₂
~₁-νNF (perm-ν1 s t es)       = perm-ν1 (tν s) t es
~₁-νNF (perm-νν s t es)       = perm-νν (tν s) t es
~₁-νNF (perm-φφ s x y t es)   = perm-φφ (tν s) x y t es
~₁-νNF (perm-νφ s x t es)     = perm-νφ (tν s) x t es
~₁-νNF (perm-thr t p)         = perm-thr (tν t) p
~₁-νNF (unit-del t es)        = unit-del (tν t) es

~₁-φNF : ∀ {n} {f} {N₁ N₂ : NF (1 + n)} → N₁ ~₁ N₂ → φNF f N₁ ~₁ φNF f N₂
~₁-φNF (perm-ν1 s t es)       = perm-ν1 (tφ _ s) t es
~₁-φNF (perm-νν s t es)       = perm-νν (tφ _ s) t es
~₁-φNF (perm-φφ s x y t es)   = perm-φφ (tφ _ s) x y t es
~₁-φNF (perm-νφ s x t es)     = perm-νφ (tφ _ s) x t es
~₁-φNF (perm-thr t p)         = perm-thr (tφ _ t) p
~₁-φNF (unit-del t es)        = unit-del (tφ _ t) es

~-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~ N₂ → νNF N₁ ~ νNF N₂
~-νNF = Eq*.gmap νNF ~₁-νNF

~-φNF : ∀ {n} {f} {N₁ N₂ : NF (1 + n)} → N₁ ~ N₂ → φNF f N₁ ~ φNF f N₂
~-φNF {f = f} = Eq*.gmap (φNF f) ~₁-φNF
