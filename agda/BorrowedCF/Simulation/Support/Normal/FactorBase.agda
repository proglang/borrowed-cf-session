-- | The φ-only sub-equivalence `~ᵩ`, block heads, and `blockify`.
--
--   Foundation for Normal.Factor (the factorisation probe).  `~` mixes two
--   very different kinds of discrepancy between normal forms:
--
--     * φ-cell DISPLACEMENT — `perm-φφ` / `perm-νφ` move sync cells around,
--       plus the binder-free `perm-thr` / `unit-del`.  Downstream these are
--       absorbed by the up-to-φ relation `≈`; nothing typed has to move.
--     * ν-REINDEXING — `perm-ν1` / `perm-νν` leave the telescope alone but
--       permute which ν binds what.  Downstream these must be realised by a
--       TYPED rearrangement, so they have to be quarantined.
--
--   `_~ᵩ_` is `~` with the second kind removed: the sub-equivalence generated
--   by `perm-φφ`, `perm-νφ`, `perm-thr`, `unit-del` only.  The justifying
--   invariant is that a `~ᵩ` derivation never re-associates ν names: its two
--   ν-changing generators do not exist, and the two shape-changing ones it
--   keeps (`perm-φφ`, `perm-νφ`) rename threads by `assocSwapᵣ 1 1` /
--   `assocSwapᵣ 1 2` lifts, which carry a single φ name across its neighbour
--   and fix every ν pair as a pair.  At the SHAPE level this module proves the
--   count invariants (`~-νcountᵗ` / `~-φcountᵗ`, over full `~`, which
--   subsumes `~ᵩ` via the embedding `~ᵩ⇒~`); the name-level ν-order
--   invariance is definitional per generator and is consumed implicitly by
--   Normal.Factor's block moves.
--
--   The constructive payoff is `blockify`: every normal form with at least
--   one ν (or no binders at all) is `~ᵩ`-equal to one in BLOCK form — no
--   leading φ.  The leading φ-run is bubbled inward past the first ν with
--   `perm-νφ` steps only, by the recursion pattern of Normal.Bubble; the
--   composite renaming is the INVERSE `bubν⁻` of Bubble's `bubν`, proved so
--   pointwise (`bubν-inv` / `bubφ-inv`).
module BorrowedCF.Simulation.Support.Normal.FactorBase where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift
  using (shift2; shift1; liftId-·; liftId-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (bubν; bubφ; bubbleν; bubbleφ; map-⋯-cong; map-⋯-id; ≡→~; aswap-21-12)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (aswap-22-inv; aswap-11-inv; aswap-12-21)
open import BorrowedCF.Simulation.Support.Normal.Nat using (map-fuse)

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- The φ-only generators: Normal.Equiv's `_~₁_` minus perm-ν1/perm-νν.
------------------------------------------------------------------------

data _~ᵩ₁_ {n} : NF n → NF n → Set where

  φφᵩ : ∀ {j k} (s : Tel n j) (x y : Flag) (t : Tel (1 + (1 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tφ x (tφ y t)) es ~ᵩ₁ mkNF (s ++ᵗ tφ y (tφ x t)) (map (_⋯ liftId t (assocSwapᵣ 1 1)) es)

  νφᵩ : ∀ {j k} (s : Tel n j) (x : Flag) (t : Tel (1 + (2 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tν (tφ x t)) es ~ᵩ₁ mkNF (s ++ᵗ tφ x (tν t)) (map (_⋯ liftId t (assocSwapᵣ 1 2)) es)

  thrᵩ : ∀ {k} (t : Tel n k) {es es′ : List (Tm k)} →
    es ↭ es′ → mkNF t es ~ᵩ₁ mkNF t es′

  delᵩ : ∀ {k} (t : Tel n k) (es : List (Tm k)) →
    mkNF t (K `unit ∷ es) ~ᵩ₁ mkNF t es

infix 4 _~ᵩ_

_~ᵩ_ : ∀ {n} → NF n → NF n → Set
_~ᵩ_ = EqClosure _~ᵩ₁_

~ᵩ-refl : ∀ {n} {N : NF n} → N ~ᵩ N
~ᵩ-refl = Eq*.reflexive _

~ᵩ-sym : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵩ N₂ → N₂ ~ᵩ N₁
~ᵩ-sym = Eq*.symmetric _

~ᵩ-trans : ∀ {n} {N₁ N₂ N₃ : NF n} → N₁ ~ᵩ N₂ → N₂ ~ᵩ N₃ → N₁ ~ᵩ N₃
~ᵩ-trans = Eq*.transitive _

≡→~ᵩ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ᵩ N₂
≡→~ᵩ refl = ~ᵩ-refl

------------------------------------------------------------------------
-- The embedding: every `~ᵩ` generator is a `~` generator, verbatim.
------------------------------------------------------------------------

~ᵩ₁⇒~₁ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵩ₁ N₂ → N₁ ~₁ N₂
~ᵩ₁⇒~₁ (φφᵩ s x y t es) = perm-φφ s x y t es
~ᵩ₁⇒~₁ (νφᵩ s x t es)   = perm-νφ s x t es
~ᵩ₁⇒~₁ (thrᵩ t p)       = perm-thr t p
~ᵩ₁⇒~₁ (delᵩ t es)      = unit-del t es

~ᵩ⇒~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵩ N₂ → N₁ ~ N₂
~ᵩ⇒~ = Eq*.gmap (λ N → N) ~ᵩ₁⇒~₁

------------------------------------------------------------------------
-- Congruences, mirroring Normal.Equiv's.
------------------------------------------------------------------------

~ᵩ₁-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~ᵩ₁ N₂ → νNF N₁ ~ᵩ₁ νNF N₂
~ᵩ₁-νNF (φφᵩ s x y t es) = φφᵩ (tν s) x y t es
~ᵩ₁-νNF (νφᵩ s x t es)   = νφᵩ (tν s) x t es
~ᵩ₁-νNF (thrᵩ t p)       = thrᵩ (tν t) p
~ᵩ₁-νNF (delᵩ t es)      = delᵩ (tν t) es

~ᵩ₁-φNF : ∀ {n} {f} {N₁ N₂ : NF (1 + n)} → N₁ ~ᵩ₁ N₂ → φNF f N₁ ~ᵩ₁ φNF f N₂
~ᵩ₁-φNF (φφᵩ s x y t es) = φφᵩ (tφ _ s) x y t es
~ᵩ₁-φNF (νφᵩ s x t es)   = νφᵩ (tφ _ s) x t es
~ᵩ₁-φNF (thrᵩ t p)       = thrᵩ (tφ _ t) p
~ᵩ₁-φNF (delᵩ t es)      = delᵩ (tφ _ t) es

~ᵩ-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~ᵩ N₂ → νNF N₁ ~ᵩ νNF N₂
~ᵩ-νNF = Eq*.gmap νNF ~ᵩ₁-νNF

~ᵩ-φNF : ∀ {n} {f} {N₁ N₂ : NF (1 + n)} → N₁ ~ᵩ N₂ → φNF f N₁ ~ᵩ φNF f N₂
~ᵩ-φNF {f = f} = Eq*.gmap (φNF f) ~ᵩ₁-φNF

------------------------------------------------------------------------
-- Telescope binder counts, and their `~`-invariance.
------------------------------------------------------------------------

νcountᵗ : ∀ {n k} → Tel n k → ℕ
νcountᵗ []       = 0
νcountᵗ (tν t)   = suc (νcountᵗ t)
νcountᵗ (tφ _ t) = νcountᵗ t

φcountᵗ : ∀ {n k} → Tel n k → ℕ
φcountᵗ []       = 0
φcountᵗ (tν t)   = φcountᵗ t
φcountᵗ (tφ _ t) = suc (φcountᵗ t)

νcountᵗ-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
              νcountᵗ (t ++ᵗ s) ≡ νcountᵗ t + νcountᵗ s
νcountᵗ-++ᵗ []       s = refl
νcountᵗ-++ᵗ (tν t)   s = cong suc (νcountᵗ-++ᵗ t s)
νcountᵗ-++ᵗ (tφ f t) s = νcountᵗ-++ᵗ t s

φcountᵗ-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
              φcountᵗ (t ++ᵗ s) ≡ φcountᵗ t + φcountᵗ s
φcountᵗ-++ᵗ []       s = refl
φcountᵗ-++ᵗ (tν t)   s = φcountᵗ-++ᵗ t s
φcountᵗ-++ᵗ (tφ f t) s = cong suc (φcountᵗ-++ᵗ t s)

-- Every `~₁` generator preserves both counts: the two ν-reindexing
-- generators do not touch the telescope at all, and the two φ movers
-- carry a binder across without creating or destroying one.
~₁-νcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → νcountᵗ (tel N₁) ≡ νcountᵗ (tel N₂)
~₁-νcountᵗ (perm-ν1 s t es)     = refl
~₁-νcountᵗ (perm-νν s t es)     = refl
~₁-νcountᵗ (perm-φφ s x y t es) = νcountᵗ-++ᵗ s (tφ x (tφ y t)) ■ sym (νcountᵗ-++ᵗ s (tφ y (tφ x t)))
~₁-νcountᵗ (perm-νφ s x t es)   = νcountᵗ-++ᵗ s (tν (tφ x t)) ■ sym (νcountᵗ-++ᵗ s (tφ x (tν t)))
~₁-νcountᵗ (perm-thr t p)       = refl
~₁-νcountᵗ (unit-del t es)      = refl

~₁-φcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → φcountᵗ (tel N₁) ≡ φcountᵗ (tel N₂)
~₁-φcountᵗ (perm-ν1 s t es)     = refl
~₁-φcountᵗ (perm-νν s t es)     = refl
~₁-φcountᵗ (perm-φφ s x y t es) = φcountᵗ-++ᵗ s (tφ x (tφ y t)) ■ sym (φcountᵗ-++ᵗ s (tφ y (tφ x t)))
~₁-φcountᵗ (perm-νφ s x t es)   = φcountᵗ-++ᵗ s (tν (tφ x t)) ■ sym (φcountᵗ-++ᵗ s (tφ x (tν t)))
~₁-φcountᵗ (perm-thr t p)       = refl
~₁-φcountᵗ (unit-del t es)      = refl

~-νcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → νcountᵗ (tel N₁) ≡ νcountᵗ (tel N₂)
~-νcountᵗ ε           = refl
~-νcountᵗ (fwd g ◅ c) = ~₁-νcountᵗ g ■ ~-νcountᵗ c
~-νcountᵗ (bwd g ◅ c) = sym (~₁-νcountᵗ g) ■ ~-νcountᵗ c

~-φcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → φcountᵗ (tel N₁) ≡ φcountᵗ (tel N₂)
~-φcountᵗ ε           = refl
~-φcountᵗ (fwd g ◅ c) = ~₁-φcountᵗ g ■ ~-φcountᵗ c
~-φcountᵗ (bwd g ◅ c) = sym (~₁-φcountᵗ g) ■ ~-φcountᵗ c

------------------------------------------------------------------------
-- Runs and blocks.
------------------------------------------------------------------------

-- A RUN: a φ-only telescope.
data Run : ∀ {n k} → Tel n k → Set where
  rnil : ∀ {n} → Run ([] {n})
  rφ   : ∀ {n k} {f : Flag} {r : Tel (1 + n) k} → Run r → Run (tφ f r)

-- BLOCK form: no leading φ.  Since a telescope only has ν and φ cells, this
-- is exactly "the telescope parses as ν-headed blocks": each tν, together
-- with the φ-run following it, is one block, and Normal.Image shows every
-- translation image has this form (`shape-U-ν`: `sν` first, then the bind
-- groups' `sφ`s).
data Block : ∀ {n k} → Tel n k → Set where
  bnil : ∀ {n} → Block ([] {n})
  bν   : ∀ {n k} {t : Tel (2 + n) k} → Block (tν t)

run-νcountᵗ : ∀ {n k} {t : Tel n k} → Run t → νcountᵗ t ≡ 0
run-νcountᵗ rnil   = refl
run-νcountᵗ (rφ r) = run-νcountᵗ r

-- A run with no φ cells is the empty telescope, hence block-form.
run-Block : ∀ {n k} {t : Tel n k} → Run t → φcountᵗ t ≡ 0 → Block t
run-Block rnil   _  = bnil

-- Every telescope is either a bare run or a run followed by a first ν.
data HeadView {n} : ∀ {k} → Tel n k → Set where
  vrun : ∀ {k} {r : Tel n k} → Run r → HeadView r
  vν   : ∀ {j k} {s : Tel n j} (rs : Run s) (u : Tel (2 + j) k) → HeadView (s ++ᵗ tν u)

headView : ∀ {n k} (t : Tel n k) → HeadView t
headView []       = vrun rnil
headView (tν t)   = vν rnil t
headView (tφ f t) with headView t
... | vrun r    = vrun (rφ r)
... | vν rs u   = vν (rφ rs) u

------------------------------------------------------------------------
-- Inverses of the bubble renamings.
------------------------------------------------------------------------

-- `bubν s` moves a ν from outside `s` to inside; `bubν⁻ s` is its pointwise
-- inverse, one inverse transposition per binder of `s`, in reverse order.
bubν⁻ : ∀ {n j} → Tel n j → 2 + j →ᵣ 2 + j
bubν⁻ []       = idₖ ⦃ Kᵣ ⦄
bubν⁻ (tν s)   = bubν⁻ s ·ₖ liftId (shift2 s) (assocSwapᵣ 2 2)
bubν⁻ (tφ f s) = bubν⁻ s ·ₖ liftId (shift2 s) (assocSwapᵣ 2 1)

bubφ⁻ : ∀ {n j} → Tel n j → 1 + j →ᵣ 1 + j
bubφ⁻ []       = idₖ ⦃ Kᵣ ⦄
bubφ⁻ (tν s)   = bubφ⁻ s ·ₖ liftId (shift1 s) (assocSwapᵣ 1 2)
bubφ⁻ (tφ f s) = bubφ⁻ s ·ₖ liftId (shift1 s) (assocSwapᵣ 1 1)

bubν-inv : ∀ {n j} (s : Tel n j) (x : 𝔽 (2 + j)) → bubν s (bubν⁻ s x) ≡ x
bubν-inv []       x = refl
bubν-inv (tν s)   x =
  cong (bubν s) ( liftId-· (shift2 s) (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) (bubν⁻ s x)
                ■ liftId-id (shift2 s) (λ y → aswap-22-inv y) (bubν⁻ s x) )
    ■ bubν-inv s x
bubν-inv (tφ f s) x =
  cong (bubν s) ( liftId-· (shift2 s) (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) (bubν⁻ s x)
                ■ liftId-id (shift2 s) (λ y → aswap-21-12 y) (bubν⁻ s x) )
    ■ bubν-inv s x

bubφ-inv : ∀ {n j} (s : Tel n j) (x : 𝔽 (1 + j)) → bubφ s (bubφ⁻ s x) ≡ x
bubφ-inv []       x = refl
bubφ-inv (tν s)   x =
  cong (bubφ s) ( liftId-· (shift1 s) (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) (bubφ⁻ s x)
                ■ liftId-id (shift1 s) (λ y → aswap-12-21 y) (bubφ⁻ s x) )
    ■ bubφ-inv s x
bubφ-inv (tφ f s) x =
  cong (bubφ s) ( liftId-· (shift1 s) (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) (bubφ⁻ s x)
                ■ liftId-id (shift1 s) (λ y → aswap-11-inv y) (bubφ⁻ s x) )
    ■ bubφ-inv s x

------------------------------------------------------------------------
-- Bubbling a binder OUTWARD: `bubbleν`/`bubbleφ` read right-to-left, with
-- the threads on the natural side thanks to `bubν⁻`/`bubφ⁻`.
------------------------------------------------------------------------

bubbleν⁻ : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tν u) es ~ mkNF (tν (shift2 s ++ᵗ u)) (map (_⋯ liftId u (bubν⁻ s)) es)
bubbleν⁻ s u es =
  ~-trans (≡→~ (cong (mkNF (s ++ᵗ tν u)) (sym undo)))
          (~-sym (bubbleν s u (map (_⋯ liftId u (bubν⁻ s)) es)))
  where
    undo : map (_⋯ liftId u (bubν s)) (map (_⋯ liftId u (bubν⁻ s)) es) ≡ es
    undo = map-fuse (liftId u (bubν⁻ s)) (liftId u (bubν s)) es
             ■ map-⋯-id (λ x → liftId-· u (bubν⁻ s) (bubν s) x
                                 ■ liftId-id u (bubν-inv s) x) es

bubbleφ⁻ : ∀ {n j k} (f : Flag) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tφ f u) es ~ mkNF (tφ f (shift1 s ++ᵗ u)) (map (_⋯ liftId u (bubφ⁻ s)) es)
bubbleφ⁻ f s u es =
  ~-trans (≡→~ (cong (mkNF (s ++ᵗ tφ f u)) (sym undo)))
          (~-sym (bubbleφ f s u (map (_⋯ liftId u (bubφ⁻ s)) es)))
  where
    undo : map (_⋯ liftId u (bubφ s)) (map (_⋯ liftId u (bubφ⁻ s)) es) ≡ es
    undo = map-fuse (liftId u (bubφ⁻ s)) (liftId u (bubφ s)) es
             ■ map-⋯-id (λ x → liftId-· u (bubφ⁻ s) (bubφ s) x
                                 ■ liftId-id u (bubφ-inv s) x) es

------------------------------------------------------------------------
-- The `~ᵩ` bubble: a ν travelling through a RUN needs only `perm-νφ`.
------------------------------------------------------------------------

-- Normal.Bubble's `bubbleν`, minus the `tν` case (which needs `perm-νν`,
-- the generator `~ᵩ` bans).  A `Run` prefix never hits that case.
bubbleνᵩ : ∀ {n j k} {s : Tel n j} (rs : Run s) (u : Tel (2 + j) k) (es : List (Tm k)) →
           mkNF (tν (shift2 s ++ᵗ u)) es ~ᵩ mkNF (s ++ᵗ tν u) (map (_⋯ liftId u (bubν s)) es)

bubbleνᵩ rnil u es = ≡→~ᵩ (cong (mkNF (tν u)) (sym (map-⋯-id (liftId-id u (λ _ → refl)) es)))

bubbleνᵩ (rφ {f = f} {r = s} rs) u es =
  ~ᵩ-trans (Eq*.return (νφᵩ [] f (shift2 s ++ᵗ u) es))
    (~ᵩ-trans (~ᵩ-φNF (bubbleνᵩ rs u (map (_⋯ liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2)) es)))
              (≡→~ᵩ (cong (mkNF (tφ f (s ++ᵗ tν u)))
                          ( map-fuse (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2))
                                     (liftId u (bubν s)) es
                          ■ map-⋯-cong fuse es ))))
  where
    fuse : ∀ x → liftId u (bubν s) (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2) x)
                   ≡ liftId u (bubν (tφ f s)) x
    fuse x = cong (liftId u (bubν s)) (liftId-++ᵗ (shift2 s) u (assocSwapᵣ 1 2) x)
               ■ liftId-· u (liftId (shift2 s) (assocSwapᵣ 1 2)) (bubν s) x

-- The outward direction, threads on the natural side (cf. `bubbleν⁻`).
bubbleνᵩ⁻ : ∀ {n j k} {s : Tel n j} (rs : Run s) (u : Tel (2 + j) k) (es : List (Tm k)) →
            mkNF (s ++ᵗ tν u) es ~ᵩ mkNF (tν (shift2 s ++ᵗ u)) (map (_⋯ liftId u (bubν⁻ s)) es)
bubbleνᵩ⁻ {s = s} rs u es =
  ~ᵩ-trans (≡→~ᵩ (cong (mkNF (s ++ᵗ tν u)) (sym undo)))
           (~ᵩ-sym (bubbleνᵩ rs u (map (_⋯ liftId u (bubν⁻ s)) es)))
  where
    undo : map (_⋯ liftId u (bubν s)) (map (_⋯ liftId u (bubν⁻ s)) es) ≡ es
    undo = map-fuse (liftId u (bubν⁻ s)) (liftId u (bubν s)) es
             ■ map-⋯-id (λ x → liftId-· u (bubν⁻ s) (bubν s) x
                                 ■ liftId-id u (bubν-inv s) x) es

------------------------------------------------------------------------
-- Blockify: every normal form with enough νs is `~ᵩ`-equal to block form.
------------------------------------------------------------------------

-- The hypothesis is exactly what a `~`-relation to a block form supplies
-- (Normal.Factor): if there is no ν then there is no binder at all.  A
-- telescope that is all φ and nonempty genuinely CANNOT be blockified —
-- `~ᵩ` (indeed `~`) preserves both counts, and block form with 0 νs has 0
-- φs — so this hypothesis is the weakest possible.
blockify : ∀ {n} (N : NF n) →
           (νcountᵗ (tel N) ≡ 0 → φcountᵗ (tel N) ≡ 0) →
           Σ[ M ∈ NF n ] Block (tel M) × (N ~ᵩ M)
blockify (mkNF t es) hyp with headView t
... | vrun r =
  mkNF t es , run-Block r (hyp (run-νcountᵗ r)) , ~ᵩ-refl
... | vν {s = s} rs u =
  mkNF (tν (shift2 s ++ᵗ u)) (map (_⋯ liftId u (bubν⁻ s)) es)
    , bν
    , bubbleνᵩ⁻ rs u es
