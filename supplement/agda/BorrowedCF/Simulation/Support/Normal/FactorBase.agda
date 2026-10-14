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
--   by `perm-φφ`, `perm-νφ`, `perm-thr`, `unit-del` only.
--
--   Linked-φ: the two φ movers now carry the guarded CHANNELS (mirroring
--   Normal.Equiv's `perm-φφ` / `perm-νφ`), and rename the deep telescope by
--   `renTel`, thread by `liftRen`.  The `blockify` payoff and its inward /
--   outward bubbles (`bubbleνᵩ` / `bubbleνᵩ⁻`) are the exact `~ᵩ`-shadows of
--   Normal.Bubble's `bubbleν`, whose RHS now carries `renTel u (bubν s)`.
module BorrowedCF.Simulation.Support.Normal.FactorBase where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
  using (renTel; liftRen; renTel-id; innerOf)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift
  using (shift2; shift1; shift2-innerOf; shift1-innerOf; liftId-·; liftId-cong)
open import BorrowedCF.Simulation.Support.Normal.Endo
  using (liftId-id; renTel-idᵗ; liftId-liftRen)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (bubν; bubφ; bubbleν; bubbleφ; bubν-wkTel; bubφ-wkTel; map-⋯-cong; map-⋯-id; ≡→~; aswap-21-12;
         aswap12-lift; liftId-subst; liftId-renTel-cong; innerOf-substⁱ;
         renTel-substⁱ; liftRen-substⁱ; telMidᴺ; liftMid; aswap11-lift; aswap12-wk)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (aswap-22-inv; aswap-11-inv; aswap-12-21)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (map-fuse; NF-≡; subst-■; subst-tν; subst-tφ; subst-++ᵗ; renTel-renTel;
         renTel-cong; innerOf-renTel; innerOf-++ᵗ; renTel-++ᵗ; liftRen-++ᵗ;
         map-⋯-subst; liftRen-·; liftRen-cong)

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

  φφᵩ : ∀ {j k} (s : Tel n j) (x y : Flag) (c d : Tm j) (t : Tel (1 + (1 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t)) es
      ~ᵩ₁ mkNF (s ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t (assocSwapᵣ 1 1)))) (map (_⋯ liftRen t (assocSwapᵣ 1 1)) es)

  νφᵩ : ∀ {j k} (s : Tel n j) (x : Flag) (c : Tm j) (t : Tel (1 + (2 + j)) k) (es : List (Tm k)) →
    mkNF (s ++ᵗ tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t)) es
      ~ᵩ₁ mkNF (s ++ᵗ tφ x c (tν (renTel t (assocSwapᵣ 1 2)))) (map (_⋯ liftRen t (assocSwapᵣ 1 2)) es)

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
~ᵩ₁⇒~₁ (φφᵩ s x y c d t es) = perm-φφ s x y c d t es
~ᵩ₁⇒~₁ (νφᵩ s x c t es)     = perm-νφ s x c t es
~ᵩ₁⇒~₁ (thrᵩ t p)           = perm-thr t p
~ᵩ₁⇒~₁ (delᵩ t es)          = unit-del t es

~ᵩ⇒~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵩ N₂ → N₁ ~ N₂
~ᵩ⇒~ = Eq*.gmap (λ N → N) ~ᵩ₁⇒~₁

------------------------------------------------------------------------
-- Congruences, mirroring Normal.Equiv's.
------------------------------------------------------------------------

~ᵩ₁-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~ᵩ₁ N₂ → νNF N₁ ~ᵩ₁ νNF N₂
~ᵩ₁-νNF (φφᵩ s x y c d t es) = φφᵩ (tν s) x y c d t es
~ᵩ₁-νNF (νφᵩ s x c t es)     = νφᵩ (tν s) x c t es
~ᵩ₁-νNF (thrᵩ t p)           = thrᵩ (tν t) p
~ᵩ₁-νNF (delᵩ t es)          = delᵩ (tν t) es

~ᵩ₁-φNF : ∀ {n} {f} (cc : Tm n) {N₁ N₂ : NF (1 + n)} → N₁ ~ᵩ₁ N₂ → φNF f cc N₁ ~ᵩ₁ φNF f cc N₂
~ᵩ₁-φNF cc (φφᵩ s x y c d t es) = φφᵩ (tφ _ cc s) x y c d t es
~ᵩ₁-φNF cc (νφᵩ s x c t es)     = νφᵩ (tφ _ cc s) x c t es
~ᵩ₁-φNF cc (thrᵩ t p)           = thrᵩ (tφ _ cc t) p
~ᵩ₁-φNF cc (delᵩ t es)          = delᵩ (tφ _ cc t) es

~ᵩ-νNF : ∀ {n} {N₁ N₂ : NF (2 + n)} → N₁ ~ᵩ N₂ → νNF N₁ ~ᵩ νNF N₂
~ᵩ-νNF = Eq*.gmap νNF ~ᵩ₁-νNF

~ᵩ-φNF : ∀ {n} {f} (cc : Tm n) {N₁ N₂ : NF (1 + n)} → N₁ ~ᵩ N₂ → φNF f cc N₁ ~ᵩ φNF f cc N₂
~ᵩ-φNF {f = f} cc = Eq*.gmap (φNF f cc) (~ᵩ₁-φNF cc)

------------------------------------------------------------------------
-- Telescope binder counts, and their `~`-invariance.
------------------------------------------------------------------------

νcountᵗ : ∀ {n k} → Tel n k → ℕ
νcountᵗ []         = 0
νcountᵗ (tν t)     = suc (νcountᵗ t)
νcountᵗ (tφ _ _ t) = νcountᵗ t

φcountᵗ : ∀ {n k} → Tel n k → ℕ
φcountᵗ []         = 0
φcountᵗ (tν t)     = φcountᵗ t
φcountᵗ (tφ _ _ t) = suc (φcountᵗ t)

νcountᵗ-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
              νcountᵗ (t ++ᵗ s) ≡ νcountᵗ t + νcountᵗ s
νcountᵗ-++ᵗ []         s = refl
νcountᵗ-++ᵗ (tν t)     s = cong suc (νcountᵗ-++ᵗ t s)
νcountᵗ-++ᵗ (tφ f c t) s = νcountᵗ-++ᵗ t s

φcountᵗ-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
              φcountᵗ (t ++ᵗ s) ≡ φcountᵗ t + φcountᵗ s
φcountᵗ-++ᵗ []         s = refl
φcountᵗ-++ᵗ (tν t)     s = φcountᵗ-++ᵗ t s
φcountᵗ-++ᵗ (tφ f c t) s = cong suc (φcountᵗ-++ᵗ t s)

-- `renTel` preserves both binder counts (it only re-bases the channels).
νcountᵗ-renTel : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) → νcountᵗ (renTel t ρ) ≡ νcountᵗ t
νcountᵗ-renTel []         ρ = refl
νcountᵗ-renTel (tν t)     ρ = cong suc (νcountᵗ-renTel t (ρ ↑* 2))
νcountᵗ-renTel (tφ f c t) ρ = νcountᵗ-renTel t (ρ ↑)

φcountᵗ-renTel : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) → φcountᵗ (renTel t ρ) ≡ φcountᵗ t
φcountᵗ-renTel []         ρ = refl
φcountᵗ-renTel (tν t)     ρ = φcountᵗ-renTel t (ρ ↑* 2)
φcountᵗ-renTel (tφ f c t) ρ = cong suc (φcountᵗ-renTel t (ρ ↑))

-- Every `~₁` generator preserves both counts: the two ν-reindexing
-- generators only `renTel` the deep telescope, and the two φ movers carry a
-- binder across without creating or destroying one.
~₁-νcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → νcountᵗ (tel N₁) ≡ νcountᵗ (tel N₂)
~₁-νcountᵗ (perm-ν1 s t es) =
  νcountᵗ-++ᵗ s (tν t)
    ■ cong (νcountᵗ s +_) (cong suc (sym (νcountᵗ-renTel t (swapᵣ 1 1))))
    ■ sym (νcountᵗ-++ᵗ s (tν (renTel t (swapᵣ 1 1))))
~₁-νcountᵗ (perm-νν s t es) =
  νcountᵗ-++ᵗ s (tν (tν t))
    ■ cong (νcountᵗ s +_) (cong (λ z → suc (suc z)) (sym (νcountᵗ-renTel t (assocSwapᵣ 2 2))))
    ■ sym (νcountᵗ-++ᵗ s (tν (tν (renTel t (assocSwapᵣ 2 2)))))
~₁-νcountᵗ (perm-φφ s x y c d t es) =
  νcountᵗ-++ᵗ s (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t))
    ■ cong (νcountᵗ s +_) (sym (νcountᵗ-renTel t (assocSwapᵣ 1 1)))
    ■ sym (νcountᵗ-++ᵗ s (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t (assocSwapᵣ 1 1)))))
~₁-νcountᵗ (perm-νφ s x c t es) =
  νcountᵗ-++ᵗ s (tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t))
    ■ cong (νcountᵗ s +_) (cong suc (sym (νcountᵗ-renTel t (assocSwapᵣ 1 2))))
    ■ sym (νcountᵗ-++ᵗ s (tφ x c (tν (renTel t (assocSwapᵣ 1 2)))))
~₁-νcountᵗ (perm-thr t p)  = refl
~₁-νcountᵗ (unit-del t es) = refl

~₁-φcountᵗ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → φcountᵗ (tel N₁) ≡ φcountᵗ (tel N₂)
~₁-φcountᵗ (perm-ν1 s t es) =
  φcountᵗ-++ᵗ s (tν t)
    ■ cong (φcountᵗ s +_) (sym (φcountᵗ-renTel t (swapᵣ 1 1)))
    ■ sym (φcountᵗ-++ᵗ s (tν (renTel t (swapᵣ 1 1))))
~₁-φcountᵗ (perm-νν s t es) =
  φcountᵗ-++ᵗ s (tν (tν t))
    ■ cong (φcountᵗ s +_) (sym (φcountᵗ-renTel t (assocSwapᵣ 2 2)))
    ■ sym (φcountᵗ-++ᵗ s (tν (tν (renTel t (assocSwapᵣ 2 2)))))
~₁-φcountᵗ (perm-φφ s x y c d t es) =
  φcountᵗ-++ᵗ s (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t))
    ■ cong (φcountᵗ s +_) (cong (λ z → suc (suc z)) (sym (φcountᵗ-renTel t (assocSwapᵣ 1 1))))
    ■ sym (φcountᵗ-++ᵗ s (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t (assocSwapᵣ 1 1)))))
~₁-φcountᵗ (perm-νφ s x c t es) =
  φcountᵗ-++ᵗ s (tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t))
    ■ cong (φcountᵗ s +_) (cong suc (sym (φcountᵗ-renTel t (assocSwapᵣ 1 2))))
    ■ sym (φcountᵗ-++ᵗ s (tφ x c (tν (renTel t (assocSwapᵣ 1 2)))))
~₁-φcountᵗ (perm-thr t p)  = refl
~₁-φcountᵗ (unit-del t es) = refl

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
  rφ   : ∀ {n k} {f : Flag} {c : Tm n} {r : Tel (1 + n) k} → Run r → Run (tφ f c r)

-- BLOCK form: no leading φ.
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
headView []         = vrun rnil
headView (tν t)     = vν rnil t
headView (tφ f c t) with headView t
... | vrun r    = vrun (rφ r)
... | vν rs u   = vν (rφ rs) u

------------------------------------------------------------------------
-- Inverses of the bubble renamings.
------------------------------------------------------------------------

-- `bubν s` moves a ν from outside `s` to inside; `bubν⁻ s` is its pointwise
-- inverse, one inverse transposition per binder of `s`, in reverse order.
bubν⁻ : ∀ {n j} → Tel n j → 2 + j →ᵣ 2 + j
bubν⁻ []         = idₖ ⦃ Kᵣ ⦄
bubν⁻ (tν s)     = bubν⁻ s ·ₖ liftId (shift2 s) (assocSwapᵣ 2 2)
bubν⁻ (tφ f c s) = bubν⁻ s ·ₖ liftId (shift2 s) (assocSwapᵣ 2 1)

bubφ⁻ : ∀ {n j} → Tel n j → 1 + j →ᵣ 1 + j
bubφ⁻ []         = idₖ ⦃ Kᵣ ⦄
bubφ⁻ (tν s)     = bubφ⁻ s ·ₖ liftId (shift1 s) (assocSwapᵣ 1 2)
bubφ⁻ (tφ f c s) = bubφ⁻ s ·ₖ liftId (shift1 s) (assocSwapᵣ 1 1)

bubν-inv : ∀ {n j} (s : Tel n j) (x : 𝔽 (2 + j)) → bubν s (bubν⁻ s x) ≡ x
bubν-inv []         x = refl
bubν-inv (tν s)     x =
  cong (bubν s) ( liftId-· (shift2 s) (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) (bubν⁻ s x)
                ■ liftId-id (shift2 s) (λ y → aswap-22-inv y) (bubν⁻ s x) )
    ■ bubν-inv s x
bubν-inv (tφ f c s) x =
  cong (bubν s) ( liftId-· (shift2 s) (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) (bubν⁻ s x)
                ■ liftId-id (shift2 s) (λ y → aswap-21-12 y) (bubν⁻ s x) )
    ■ bubν-inv s x

bubφ-inv : ∀ {n j} (s : Tel n j) (x : 𝔽 (1 + j)) → bubφ s (bubφ⁻ s x) ≡ x
bubφ-inv []         x = refl
bubφ-inv (tν s)     x =
  cong (bubφ s) ( liftId-· (shift1 s) (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) (bubφ⁻ s x)
                ■ liftId-id (shift1 s) (λ y → aswap-12-21 y) (bubφ⁻ s x) )
    ■ bubφ-inv s x
bubφ-inv (tφ f c s) x =
  cong (bubφ s) ( liftId-· (shift1 s) (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) (bubφ⁻ s x)
                ■ liftId-id (shift1 s) (λ y → aswap-11-inv y) (bubφ⁻ s x) )
    ■ bubφ-inv s x

-- The reverse composites (`bubν⁻ ∘ bubν = id`, `bubφ⁻ ∘ bubφ = id`), and the
-- consequence the run-drag needs: weakening through `s` then bubbling inward is
-- weakening through the shifted `s` (inverse of `bubν-wkTel` / `bubφ-wkTel`).
bubν-inv′ : ∀ {n j} (s : Tel n j) (x : 𝔽 (2 + j)) → bubν⁻ s (bubν s x) ≡ x
bubν-inv′ []         x = refl
bubν-inv′ (tν s)     x =
  cong (liftId (shift2 s) (assocSwapᵣ 2 2)) (bubν-inv′ s (liftId (shift2 s) (assocSwapᵣ 2 2) x))
    ■ liftId-· (shift2 s) (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) x
    ■ liftId-id (shift2 s) (λ y → aswap-22-inv y) x
bubν-inv′ (tφ f c s) x =
  cong (liftId (shift2 s) (assocSwapᵣ 2 1)) (bubν-inv′ s (liftId (shift2 s) (assocSwapᵣ 1 2) x))
    ■ liftId-· (shift2 s) (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) x
    ■ liftId-id (shift2 s) (λ y → aswap-12-21 y) x

bubφ-inv′ : ∀ {n j} (s : Tel n j) (x : 𝔽 (1 + j)) → bubφ⁻ s (bubφ s x) ≡ x
bubφ-inv′ []         x = refl
bubφ-inv′ (tν s)     x =
  cong (liftId (shift1 s) (assocSwapᵣ 1 2)) (bubφ-inv′ s (liftId (shift1 s) (assocSwapᵣ 2 1) x))
    ■ liftId-· (shift1 s) (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) x
    ■ liftId-id (shift1 s) (λ y → aswap-21-12 y) x
bubφ-inv′ (tφ f c s) x =
  cong (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ-inv′ s (liftId (shift1 s) (assocSwapᵣ 1 1) x))
    ■ liftId-· (shift1 s) (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) x
    ■ liftId-id (shift1 s) (λ y → aswap-11-inv y) x

wkν-lemma : ∀ {p j} (S : Tel p j) (x : 𝔽 (2 + p)) →
            bubν⁻ S ((wkTel S ↑* 2) x) ≡ wkTel (shift2 S) x
wkν-lemma S x = cong (bubν⁻ S) (sym (bubν-wkTel S x)) ■ bubν-inv′ S (wkTel (shift2 S) x)

wkφ-lemma : ∀ {p j} (S : Tel p j) (x : 𝔽 (1 + p)) →
            bubφ⁻ S ((wkTel S ↑) x) ≡ wkTel (shift1 S) x
wkφ-lemma S x = cong (bubφ⁻ S) (sym (bubφ-wkTel S x)) ■ bubφ-inv′ S (wkTel (shift1 S) x)

------------------------------------------------------------------------
-- The `~ᵩ` bubble: a ν travelling through a RUN needs only `perm-νφ`.
-- This is the exact `~ᵩ`-shadow of Normal.Bubble's `bubbleν`, restricted to
-- a φ-run prefix (so the `tν` case — which would need `perm-νν` — never fires).
------------------------------------------------------------------------

bubbleνᵩ : ∀ {n j k} {s : Tel n j} (rs : Run s) (u : Tel (2 + j) k) (es : List (Tm k)) →
           mkNF (tν (shift2 s ++ᵗ u)) es
             ~ᵩ mkNF (s ++ᵗ tν (renTel u (bubν s))) (map (_⋯ liftRen u (bubν s)) es)

bubbleνᵩ rnil u es =
  ~ᵩ-sym (≡→~ᵩ (NF-≡ (renTel-id u)
    ( subst-tν (renTel-id u) (renTel u (idₖ ⦃ Kᵣ ⦄)) ■ cong tν (renTel-idᵗ u) )
    ( map-⋯-subst (renTel-id u)
        (λ x → liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x ■ liftId-id u (λ _ → refl) x) es
    ■ map-⋯-id (λ _ → refl) es )))

bubbleνᵩ {n} {j} (rφ {f = f} {c = c} {r = s} rs) u es =
  ~ᵩ-trans (≡→~ᵩ eqA)
    (~ᵩ-trans (Eq*.return (νφᵩ [] f c (Y ++ᵗ u) es))
      (~ᵩ-trans (≡→~ᵩ eqB)
        (~ᵩ-trans (~ᵩ-φNF c (bubbleνᵩ rs u-rec es-rec)) (≡→~ᵩ eqC))))
  where
    wν : n →ᵣ 2 + n
    wν = weaken* ⦃ Kᵣ ⦄ 2
    sh : innerOf s (2 + (1 + n)) ≡ 2 + j
    sh = shift2-innerOf s
    Y : Tel (2 + (1 + n)) (2 + j)
    Y = subst (Tel (2 + (1 + n))) sh (renTel s (wν ↑))
    u-rec : Tel (2 + j) (innerOf u (2 + j))
    u-rec = renTel u (liftId (shift2 s) (assocSwapᵣ 1 2))
    es-rec : List (Tm (innerOf u (2 + j)))
    es-rec = map (_⋯ liftRen u (liftId (shift2 s) (assocSwapᵣ 1 2))) es
    eqk : innerOf (Y ++ᵗ u) (2 + (1 + n)) ≡ innerOf u (2 + j)
    eqk = innerOf-++ᵗ Y u (2 + (1 + n)) ■ cong (innerOf u) (renTel-id Y)
    eqA : mkNF (tν (shift2 (tφ f c s) ++ᵗ u)) es
            ≡ mkNF (tν (tφ f (c ⋯ wν) (Y ++ᵗ u))) es
    eqA = cong (λ T → mkNF (tν T) es)
               (cong (_++ᵗ u) (subst-tφ sh f (c ⋯ wν) (renTel s (wν ↑))))
    a₀ : innerOf Y (2 + (1 + n)) ≡ innerOf (renTel s (wν ↑)) (2 + (1 + n))
    a₀ = innerOf-substⁱ sh (renTel s (wν ↑)) (2 + (1 + n))
    b₀ : innerOf (renTel s (wν ↑)) (2 + (1 + n)) ≡ innerOf s (2 + (1 + n))
    b₀ = innerOf-renTel s (wν ↑) (2 + (1 + n))
    pY : innerOf Y (2 + (1 + n)) ≡ 2 + j
    pY = a₀ ■ b₀ ■ sh
    P1 : subst (Tel (2 + (1 + n))) pY (renTel Y (assocSwapᵣ 1 2)) ≡ shift2 s
    P1 = subst-■ (Tel (2 + (1 + n))) a₀ (b₀ ■ sh) (renTel Y (assocSwapᵣ 1 2))
           ■ cong (subst (Tel (2 + (1 + n))) (b₀ ■ sh))
                  (renTel-substⁱ sh (renTel s (wν ↑)) (assocSwapᵣ 1 2))
           ■ subst-■ (Tel (2 + (1 + n))) b₀ sh (renTel (renTel s (wν ↑)) (assocSwapᵣ 1 2))
           ■ cong (subst (Tel (2 + (1 + n))) sh) (renTel-renTel s (wν ↑) (assocSwapᵣ 1 2))
           ■ cong (subst (Tel (2 + (1 + n))) sh) (renTel-cong s aswap12-lift)
    P1′ : subst (Tel (2 + (1 + n))) (renTel-id Y) (renTel Y (assocSwapᵣ 1 2)) ≡ shift2 s
    P1′ = cong (λ p → subst (Tel (2 + (1 + n))) p (renTel Y (assocSwapᵣ 1 2)))
               (≡-irrelevant (renTel-id Y) pY)
            ■ P1
    P2 : ∀ z → subst 𝔽 pY (liftRen Y (assocSwapᵣ 1 2) z) ≡ liftId (shift2 s) (assocSwapᵣ 1 2) z
    P2 z =
      subst-■ 𝔽 a₀ (b₀ ■ sh) (liftRen Y (assocSwapᵣ 1 2) z)
        ■ cong (subst 𝔽 (b₀ ■ sh)) (liftRen-substⁱ sh (renTel s (wν ↑)) (assocSwapᵣ 1 2) z)
        ■ subst-■ 𝔽 b₀ sh (liftRen (renTel s (wν ↑)) (assocSwapᵣ 1 2) (subst 𝔽 (sym sh) z))
        ■ cong (subst 𝔽 sh)
            ( cong (λ p → subst 𝔽 p (liftRen (renTel s (wν ↑)) (assocSwapᵣ 1 2) (subst 𝔽 (sym sh) z)))
                   (≡-irrelevant b₀ (renTel-id (renTel s (wν ↑))))
            ■ liftId-liftRen (renTel s (wν ↑)) (assocSwapᵣ 1 2) (subst 𝔽 (sym sh) z)
            ■ liftId-renTel-cong s (wν ↑) (weaken* ⦃ Kᵣ ⦄ 2) (assocSwapᵣ 1 2) (subst 𝔽 (sym sh) z) )
        ■ sym (liftId-subst sh (renTel s (weaken* ⦃ Kᵣ ⦄ 2)) (assocSwapᵣ 1 2) (subst 𝔽 (sym sh) z))
        ■ cong (liftId (shift2 s) (assocSwapᵣ 1 2)) (subst-subst-sym sh)
    hρ′ : ∀ z → subst 𝔽 (renTel-id Y) (liftRen Y (assocSwapᵣ 1 2) z)
                ≡ liftId (shift2 s) (assocSwapᵣ 1 2) z
    hρ′ z = cong (λ p → subst 𝔽 p (liftRen Y (assocSwapᵣ 1 2) z)) (≡-irrelevant (renTel-id Y) pY)
              ■ P2 z
    deepRecon : subst (Tel (2 + (1 + n))) eqk (renTel (Y ++ᵗ u) (assocSwapᵣ 1 2))
                  ≡ shift2 s ++ᵗ u-rec
    deepRecon =
      subst-■ (Tel (2 + (1 + n))) (innerOf-++ᵗ Y u (2 + (1 + n))) (cong (innerOf u) (renTel-id Y))
              (renTel (Y ++ᵗ u) (assocSwapᵣ 1 2))
        ■ cong (subst (Tel (2 + (1 + n))) (cong (innerOf u) (renTel-id Y)))
               (renTel-++ᵗ Y u (assocSwapᵣ 1 2))
        ■ telMidᴺ (renTel-id Y) (renTel Y (assocSwapᵣ 1 2)) u hρ′
        ■ cong (_++ᵗ u-rec) P1′
    hthrB : ∀ y → subst 𝔽 eqk (liftRen (Y ++ᵗ u) (assocSwapᵣ 1 2) y)
                  ≡ liftRen u (liftId (shift2 s) (assocSwapᵣ 1 2)) y
    hthrB y =
      subst-■ 𝔽 (innerOf-++ᵗ Y u (2 + (1 + n))) (cong (innerOf u) (renTel-id Y))
              (liftRen (Y ++ᵗ u) (assocSwapᵣ 1 2) y)
        ■ cong (subst 𝔽 (cong (innerOf u) (renTel-id Y)))
               (liftRen-++ᵗ Y u (assocSwapᵣ 1 2) y)
        ■ liftMid (renTel-id Y) u hρ′ y
    eqB : mkNF (tφ f c (tν (renTel (Y ++ᵗ u) (assocSwapᵣ 1 2))))
                 (map (_⋯ liftRen (Y ++ᵗ u) (assocSwapᵣ 1 2)) es)
            ≡ mkNF (tφ f c (tν (shift2 s ++ᵗ u-rec))) es-rec
    eqB = NF-≡ eqk
            ( subst-tφ eqk f c (tν (renTel (Y ++ᵗ u) (assocSwapᵣ 1 2)))
            ■ cong (tφ f c) ( subst-tν eqk (renTel (Y ++ᵗ u) (assocSwapᵣ 1 2))
                            ■ cong tν deepRecon ) )
            ( map-⋯-subst eqk hthrB es )
    eqCinner : innerOf (renTel u (liftId (shift2 s) (assocSwapᵣ 1 2))) (2 + j) ≡ innerOf u (2 + j)
    eqCinner = innerOf-renTel u (liftId (shift2 s) (assocSwapᵣ 1 2)) (2 + j)
    deepReconC : subst (Tel (2 + j)) eqCinner (renTel u-rec (bubν s)) ≡ renTel u (bubν (tφ f c s))
    deepReconC = renTel-renTel u (liftId (shift2 s) (assocSwapᵣ 1 2)) (bubν s)
    eqC : mkNF (tφ f c (s ++ᵗ tν (renTel u-rec (bubν s)))) (map (_⋯ liftRen u-rec (bubν s)) es-rec)
            ≡ mkNF (tφ f c s ++ᵗ tν (renTel u (bubν (tφ f c s))))
                   (map (_⋯ liftRen u (bubν (tφ f c s))) es)
    eqC = NF-≡ eqCinner
            ( subst-tφ eqCinner f c (s ++ᵗ tν (renTel u-rec (bubν s)))
            ■ cong (tφ f c) ( subst-++ᵗ s eqCinner (tν (renTel u-rec (bubν s)))
                            ■ cong (s ++ᵗ_) ( subst-tν eqCinner (renTel u-rec (bubν s))
                                            ■ cong tν deepReconC ) ) )
            ( cong (subst (λ z → List (Tm z)) eqCinner)
                   (map-fuse (liftRen u (liftId (shift2 s) (assocSwapᵣ 1 2)))
                             (liftRen u-rec (bubν s)) es)
            ■ map-⋯-subst eqCinner (liftRen-· u (liftId (shift2 s) (assocSwapᵣ 1 2)) (bubν s)) es )

------------------------------------------------------------------------
-- Bubbling a binder OUTWARD: the mirror of `bubbleν` / `bubbleνᵩ`, with the
-- inverse renaming `bubν⁻` / `bubφ⁻` on the natural side.
------------------------------------------------------------------------

private
  -- The telescope reconciliation shared by both outward `ν`-bubbles.
  ν⁻-telInner : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) →
                innerOf (renTel u (bubν⁻ s)) (2 + j) ≡ k
  ν⁻-telInner {j = j} s u = innerOf-renTel u (bubν⁻ s) (2 + j) ■ renTel-id u

  ν⁻-telRec : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) →
              subst (Tel (2 + j)) (ν⁻-telInner s u)
                    (renTel (renTel u (bubν⁻ s)) (bubν s)) ≡ u
  ν⁻-telRec {j = j} s u =
    subst-■ (Tel (2 + j)) (innerOf-renTel u (bubν⁻ s) (2 + j)) (renTel-id u)
            (renTel (renTel u (bubν⁻ s)) (bubν s))
      ■ cong (subst (Tel (2 + j)) (renTel-id u))
             (renTel-renTel u (bubν⁻ s) (bubν s) ■ renTel-cong u (λ x → bubν-inv s x))
      ■ renTel-idᵗ u

  ν⁻-thrInv : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (x : 𝔽 k) →
              subst 𝔽 (ν⁻-telInner s u)
                    (liftRen (renTel u (bubν⁻ s)) (bubν s) (liftRen u (bubν⁻ s) x)) ≡ x
  ν⁻-thrInv {j = j} s u x =
    subst-■ 𝔽 (innerOf-renTel u (bubν⁻ s) (2 + j)) (renTel-id u)
            (liftRen (renTel u (bubν⁻ s)) (bubν s) (liftRen u (bubν⁻ s) x))
      ■ cong (subst 𝔽 (renTel-id u))
             (liftRen-· u (bubν⁻ s) (bubν s) x ■ liftRen-cong u (λ y → bubν-inv s y) x)
      ■ liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x
      ■ liftId-id u (λ _ → refl) x

  ν⁻-eqR : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tν (renTel (renTel u (bubν⁻ s)) (bubν s)))
                (map (_⋯ liftRen (renTel u (bubν⁻ s)) (bubν s))
                     (map (_⋯ liftRen u (bubν⁻ s)) es))
             ≡ mkNF (s ++ᵗ tν u) es
  ν⁻-eqR s u es = NF-≡ (ν⁻-telInner s u)
    ( subst-++ᵗ s (ν⁻-telInner s u) (tν (renTel (renTel u (bubν⁻ s)) (bubν s)))
    ■ cong (s ++ᵗ_) ( subst-tν (ν⁻-telInner s u) (renTel (renTel u (bubν⁻ s)) (bubν s))
                    ■ cong tν (ν⁻-telRec s u) ) )
    ( cong (subst (λ z → List (Tm z)) (ν⁻-telInner s u))
           (map-fuse (liftRen u (bubν⁻ s)) (liftRen (renTel u (bubν⁻ s)) (bubν s)) es)
    ■ map-⋯-subst (ν⁻-telInner s u) (λ x → ν⁻-thrInv s u x) es
    ■ map-⋯-id (λ _ → refl) es )

bubbleν⁻ : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tν u) es
             ~ mkNF (tν (shift2 s ++ᵗ renTel u (bubν⁻ s))) (map (_⋯ liftRen u (bubν⁻ s)) es)
bubbleν⁻ s u es =
  ~-trans (≡→~ (sym (ν⁻-eqR s u es)))
          (~-sym (bubbleν s (renTel u (bubν⁻ s)) (map (_⋯ liftRen u (bubν⁻ s)) es)))

bubbleνᵩ⁻ : ∀ {n j k} {s : Tel n j} (rs : Run s) (u : Tel (2 + j) k) (es : List (Tm k)) →
            mkNF (s ++ᵗ tν u) es
              ~ᵩ mkNF (tν (shift2 s ++ᵗ renTel u (bubν⁻ s))) (map (_⋯ liftRen u (bubν⁻ s)) es)
bubbleνᵩ⁻ {s = s} rs u es =
  ~ᵩ-trans (≡→~ᵩ (sym (ν⁻-eqR s u es)))
           (~ᵩ-sym (bubbleνᵩ rs (renTel u (bubν⁻ s)) (map (_⋯ liftRen u (bubν⁻ s)) es)))

private
  -- The φ-analogue reconciliations.
  φ⁻-telInner : ∀ {n j k} (s : Tel n j) (u : Tel (1 + j) k) →
                innerOf (renTel u (bubφ⁻ s)) (1 + j) ≡ k
  φ⁻-telInner {j = j} s u = innerOf-renTel u (bubφ⁻ s) (1 + j) ■ renTel-id u

  φ⁻-telRec : ∀ {n j k} (s : Tel n j) (u : Tel (1 + j) k) →
              subst (Tel (1 + j)) (φ⁻-telInner s u)
                    (renTel (renTel u (bubφ⁻ s)) (bubφ s)) ≡ u
  φ⁻-telRec {j = j} s u =
    subst-■ (Tel (1 + j)) (innerOf-renTel u (bubφ⁻ s) (1 + j)) (renTel-id u)
            (renTel (renTel u (bubφ⁻ s)) (bubφ s))
      ■ cong (subst (Tel (1 + j)) (renTel-id u))
             (renTel-renTel u (bubφ⁻ s) (bubφ s) ■ renTel-cong u (λ x → bubφ-inv s x))
      ■ renTel-idᵗ u

  φ⁻-thrInv : ∀ {n j k} (s : Tel n j) (u : Tel (1 + j) k) (x : 𝔽 k) →
              subst 𝔽 (φ⁻-telInner s u)
                    (liftRen (renTel u (bubφ⁻ s)) (bubφ s) (liftRen u (bubφ⁻ s) x)) ≡ x
  φ⁻-thrInv {j = j} s u x =
    subst-■ 𝔽 (innerOf-renTel u (bubφ⁻ s) (1 + j)) (renTel-id u)
            (liftRen (renTel u (bubφ⁻ s)) (bubφ s) (liftRen u (bubφ⁻ s) x))
      ■ cong (subst 𝔽 (renTel-id u))
             (liftRen-· u (bubφ⁻ s) (bubφ s) x ■ liftRen-cong u (λ y → bubφ-inv s y) x)
      ■ liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x
      ■ liftId-id u (λ _ → refl) x

  φ⁻-eqR : ∀ {n j k} (f : Flag) (c : Tm n) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) (renTel (renTel u (bubφ⁻ s)) (bubφ s)))
                (map (_⋯ liftRen (renTel u (bubφ⁻ s)) (bubφ s))
                     (map (_⋯ liftRen u (bubφ⁻ s)) es))
             ≡ mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) u) es
  φ⁻-eqR f c s u es = NF-≡ (φ⁻-telInner s u)
    ( subst-++ᵗ s (φ⁻-telInner s u) (tφ f (c ⋯ wkTel s) (renTel (renTel u (bubφ⁻ s)) (bubφ s)))
    ■ cong (s ++ᵗ_) ( subst-tφ (φ⁻-telInner s u) f (c ⋯ wkTel s) (renTel (renTel u (bubφ⁻ s)) (bubφ s))
                    ■ cong (tφ f (c ⋯ wkTel s)) (φ⁻-telRec s u) ) )
    ( cong (subst (λ z → List (Tm z)) (φ⁻-telInner s u))
           (map-fuse (liftRen u (bubφ⁻ s)) (liftRen (renTel u (bubφ⁻ s)) (bubφ s)) es)
    ■ map-⋯-subst (φ⁻-telInner s u) (λ x → φ⁻-thrInv s u x) es
    ■ map-⋯-id (λ _ → refl) es )

bubbleφ⁻ : ∀ {n j k} (f : Flag) (c : Tm n) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) u) es
             ~ mkNF (tφ f c (shift1 s ++ᵗ renTel u (bubφ⁻ s))) (map (_⋯ liftRen u (bubφ⁻ s)) es)
bubbleφ⁻ f c s u es =
  ~-trans (≡→~ (sym (φ⁻-eqR f c s u es)))
          (~-sym (bubbleφ f c s (renTel u (bubφ⁻ s)) (map (_⋯ liftRen u (bubφ⁻ s)) es)))


------------------------------------------------------------------------
-- The `~ᵩ` φ-bubble, inward and outward (twins of `Bubble.bubbleφ` /
-- `bubbleφ⁻`, using only φ-only generators).
------------------------------------------------------------------------

bubbleφᵩ : ∀ {n j k} (f : Flag) (c : Tm n) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
          mkNF (tφ f c (shift1 s ++ᵗ u)) es
            ~ᵩ mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) (renTel u (bubφ s))) (map (_⋯ liftRen u (bubφ s)) es)
bubbleφᵩ f c [] u es =
  ~ᵩ-sym (≡→~ᵩ (NF-≡ (renTel-id u)
    ( subst-tφ (renTel-id u) f (c ⋯ idₖ ⦃ Kᵣ ⦄) (renTel u (idₖ ⦃ Kᵣ ⦄))
    ■ cong₂ (tφ f) (⋯-id c (λ _ → refl)) (renTel-idᵗ u) )
    ( map-⋯-subst (renTel-id u)
        (λ x → liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x ■ liftId-id u (λ _ → refl) x) es
    ■ map-⋯-id (λ _ → refl) es )))
bubbleφᵩ {n} {j} f c (tφ g d s) u es =
  ~ᵩ-trans (≡→~ᵩ eqA)
    (~ᵩ-trans (Eq*.return (φφᵩ [] f g c d (Y ++ᵗ u) es))
      (~ᵩ-trans (≡→~ᵩ eqB)
        (~ᵩ-trans (~ᵩ-φNF d (bubbleφᵩ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) s u-rec es-rec)) (≡→~ᵩ eqC))))
  where
    w1 : n →ᵣ 1 + n
    w1 = weaken* ⦃ Kᵣ ⦄ 1
    sh : innerOf s (2 + n) ≡ 1 + j
    sh = shift1-innerOf s
    Y : Tel (2 + n) (1 + j)
    Y = subst (Tel (2 + n)) sh (renTel s (w1 ↑))
    u-rec : Tel (1 + j) (innerOf u (1 + j))
    u-rec = renTel u (liftId (shift1 s) (assocSwapᵣ 1 1))
    es-rec : List (Tm (innerOf u (1 + j)))
    es-rec = map (_⋯ liftRen u (liftId (shift1 s) (assocSwapᵣ 1 1))) es
    eqk : innerOf (Y ++ᵗ u) (2 + n) ≡ innerOf u (1 + j)
    eqk = innerOf-++ᵗ Y u (2 + n) ■ cong (innerOf u) (renTel-id Y)
    eqA : mkNF (tφ f c (shift1 (tφ g d s) ++ᵗ u)) es
            ≡ mkNF (tφ f c (tφ g (d ⋯ w1) (Y ++ᵗ u))) es
    eqA = cong (λ T → mkNF (tφ f c T) es)
               (cong (_++ᵗ u) (subst-tφ sh g (d ⋯ w1) (renTel s (w1 ↑))))
    a₀ : innerOf Y (2 + n) ≡ innerOf (renTel s (w1 ↑)) (2 + n)
    a₀ = innerOf-substⁱ sh (renTel s (w1 ↑)) (2 + n)
    b₀ : innerOf (renTel s (w1 ↑)) (2 + n) ≡ innerOf s (2 + n)
    b₀ = innerOf-renTel s (w1 ↑) (2 + n)
    pY : innerOf Y (2 + n) ≡ 1 + j
    pY = a₀ ■ b₀ ■ sh
    P1 : subst (Tel (2 + n)) pY (renTel Y (assocSwapᵣ 1 1)) ≡ shift1 s
    P1 = subst-■ (Tel (2 + n)) a₀ (b₀ ■ sh) (renTel Y (assocSwapᵣ 1 1))
           ■ cong (subst (Tel (2 + n)) (b₀ ■ sh))
                  (renTel-substⁱ sh (renTel s (w1 ↑)) (assocSwapᵣ 1 1))
           ■ subst-■ (Tel (2 + n)) b₀ sh (renTel (renTel s (w1 ↑)) (assocSwapᵣ 1 1))
           ■ cong (subst (Tel (2 + n)) sh) (renTel-renTel s (w1 ↑) (assocSwapᵣ 1 1))
           ■ cong (subst (Tel (2 + n)) sh) (renTel-cong s aswap11-lift)
    P1′ : subst (Tel (2 + n)) (renTel-id Y) (renTel Y (assocSwapᵣ 1 1)) ≡ shift1 s
    P1′ = cong (λ p → subst (Tel (2 + n)) p (renTel Y (assocSwapᵣ 1 1)))
               (≡-irrelevant (renTel-id Y) pY)
            ■ P1
    P2 : ∀ z → subst 𝔽 pY (liftRen Y (assocSwapᵣ 1 1) z) ≡ liftId (shift1 s) (assocSwapᵣ 1 1) z
    P2 z =
      subst-■ 𝔽 a₀ (b₀ ■ sh) (liftRen Y (assocSwapᵣ 1 1) z)
        ■ cong (subst 𝔽 (b₀ ■ sh)) (liftRen-substⁱ sh (renTel s (w1 ↑)) (assocSwapᵣ 1 1) z)
        ■ subst-■ 𝔽 b₀ sh (liftRen (renTel s (w1 ↑)) (assocSwapᵣ 1 1) (subst 𝔽 (sym sh) z))
        ■ cong (subst 𝔽 sh)
            ( cong (λ p → subst 𝔽 p (liftRen (renTel s (w1 ↑)) (assocSwapᵣ 1 1) (subst 𝔽 (sym sh) z)))
                   (≡-irrelevant b₀ (renTel-id (renTel s (w1 ↑))))
            ■ liftId-liftRen (renTel s (w1 ↑)) (assocSwapᵣ 1 1) (subst 𝔽 (sym sh) z)
            ■ liftId-renTel-cong s (w1 ↑) (weaken* ⦃ Kᵣ ⦄ 1) (assocSwapᵣ 1 1) (subst 𝔽 (sym sh) z) )
        ■ sym (liftId-subst sh (renTel s (weaken* ⦃ Kᵣ ⦄ 1)) (assocSwapᵣ 1 1) (subst 𝔽 (sym sh) z))
        ■ cong (liftId (shift1 s) (assocSwapᵣ 1 1)) (subst-subst-sym sh)
    hρ′ : ∀ z → subst 𝔽 (renTel-id Y) (liftRen Y (assocSwapᵣ 1 1) z)
                ≡ liftId (shift1 s) (assocSwapᵣ 1 1) z
    hρ′ z = cong (λ p → subst 𝔽 p (liftRen Y (assocSwapᵣ 1 1) z)) (≡-irrelevant (renTel-id Y) pY)
              ■ P2 z
    deepRecon : subst (Tel (2 + n)) eqk (renTel (Y ++ᵗ u) (assocSwapᵣ 1 1))
                  ≡ shift1 s ++ᵗ u-rec
    deepRecon =
      subst-■ (Tel (2 + n)) (innerOf-++ᵗ Y u (2 + n)) (cong (innerOf u) (renTel-id Y))
              (renTel (Y ++ᵗ u) (assocSwapᵣ 1 1))
        ■ cong (subst (Tel (2 + n)) (cong (innerOf u) (renTel-id Y)))
               (renTel-++ᵗ Y u (assocSwapᵣ 1 1))
        ■ telMidᴺ (renTel-id Y) (renTel Y (assocSwapᵣ 1 1)) u hρ′
        ■ cong (_++ᵗ u-rec) P1′
    hthrB : ∀ y → subst 𝔽 eqk (liftRen (Y ++ᵗ u) (assocSwapᵣ 1 1) y)
                  ≡ liftRen u (liftId (shift1 s) (assocSwapᵣ 1 1)) y
    hthrB y =
      subst-■ 𝔽 (innerOf-++ᵗ Y u (2 + n)) (cong (innerOf u) (renTel-id Y))
              (liftRen (Y ++ᵗ u) (assocSwapᵣ 1 1) y)
        ■ cong (subst 𝔽 (cong (innerOf u) (renTel-id Y)))
               (liftRen-++ᵗ Y u (assocSwapᵣ 1 1) y)
        ■ liftMid (renTel-id Y) u hρ′ y
    eqB : mkNF (tφ g d (tφ f (c ⋯ w1) (renTel (Y ++ᵗ u) (assocSwapᵣ 1 1))))
                 (map (_⋯ liftRen (Y ++ᵗ u) (assocSwapᵣ 1 1)) es)
            ≡ mkNF (tφ g d (tφ f (c ⋯ w1) (shift1 s ++ᵗ u-rec))) es-rec
    eqB = NF-≡ eqk
            ( subst-tφ eqk g d (tφ f (c ⋯ w1) (renTel (Y ++ᵗ u) (assocSwapᵣ 1 1)))
            ■ cong (tφ g d) ( subst-tφ eqk f (c ⋯ w1) (renTel (Y ++ᵗ u) (assocSwapᵣ 1 1))
                            ■ cong (tφ f (c ⋯ w1)) deepRecon ) )
            ( map-⋯-subst eqk hthrB es )
    eqCinner : innerOf (renTel u (liftId (shift1 s) (assocSwapᵣ 1 1))) (1 + j) ≡ innerOf u (1 + j)
    eqCinner = innerOf-renTel u (liftId (shift1 s) (assocSwapᵣ 1 1)) (1 + j)
    deepReconC : subst (Tel (1 + j)) eqCinner (renTel u-rec (bubφ s)) ≡ renTel u (bubφ (tφ g d s))
    deepReconC = renTel-renTel u (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ s)
    eqC : mkNF (tφ g d (s ++ᵗ tφ f ((c ⋯ w1) ⋯ wkTel s) (renTel u-rec (bubφ s))))
               (map (_⋯ liftRen u-rec (bubφ s)) es-rec)
            ≡ mkNF (tφ g d s ++ᵗ tφ f (c ⋯ wkTel (tφ g d s)) (renTel u (bubφ (tφ g d s))))
                   (map (_⋯ liftRen u (bubφ (tφ g d s))) es)
    eqC = NF-≡ eqCinner
            ( subst-tφ eqCinner g d (s ++ᵗ tφ f ((c ⋯ w1) ⋯ wkTel s) (renTel u-rec (bubφ s)))
            ■ cong (tφ g d) ( subst-++ᵗ s eqCinner (tφ f ((c ⋯ w1) ⋯ wkTel s) (renTel u-rec (bubφ s)))
                            ■ cong (s ++ᵗ_) ( subst-tφ eqCinner f ((c ⋯ w1) ⋯ wkTel s) (renTel u-rec (bubφ s))
                                            ■ cong₂ (tφ f) (fusion c w1 (wkTel s)) deepReconC ) ) )
            ( cong (subst (λ z → List (Tm z)) eqCinner)
                   (map-fuse (liftRen u (liftId (shift1 s) (assocSwapᵣ 1 1)))
                             (liftRen u-rec (bubφ s)) es)
            ■ map-⋯-subst eqCinner (liftRen-· u (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ s)) es )
bubbleφᵩ {n} {j} {k} f c (tν s) u es =
  ~ᵩ-trans (≡→~ᵩ eqPre)
    (~ᵩ-trans (~ᵩ-sym (Eq*.return (νφᵩ [] f c (shift1 s ++ᵗ u-rec) es-rec)))
      (~ᵩ-trans (~ᵩ-νNF (bubbleφᵩ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) s u-rec es-rec)) (≡→~ᵩ eqC)))
  where
    u-rec : Tel (1 + j) (innerOf u (1 + j))
    u-rec = renTel u (liftId (shift1 s) (assocSwapᵣ 2 1))
    es-rec : List (Tm (innerOf u (1 + j)))
    es-rec = map (_⋯ liftRen u (liftId (shift1 s) (assocSwapᵣ 2 1))) es
    eqPre : mkNF (tφ f c (shift1 (tν s) ++ᵗ u)) es
              ≡ mkNF (tφ f c (tν (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2))))
                     (map (_⋯ liftRen (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2)) es-rec)
    eqPre = eqA₀ ■ sym eqA₁rev
      where
        α : (1 + j) →ᵣ 1 + j
        α = liftId (shift1 s) (assocSwapᵣ 2 1)
        wν : n →ᵣ 1 + n
        wν = weaken* ⦃ Kᵣ ⦄ 1
        sh1 : innerOf s (1 + (2 + n)) ≡ 1 + j
        sh1 = shift1-innerOf s
        Y : Tel (1 + (2 + n)) (1 + j)
        Y = subst (Tel (1 + (2 + n))) sh1 (renTel s (wν ↑* 2))
        ri : innerOf (shift1 s) (1 + (2 + n)) ≡ 1 + j
        ri = renTel-id (shift1 s)
        w1s : (2 + n) →ᵣ 1 + (2 + n)
        w1s = weaken* ⦃ Kᵣ ⦄ 1
        a₀φ : innerOf (shift1 s) (1 + (2 + n)) ≡ innerOf (renTel s w1s) (1 + (2 + n))
        a₀φ = innerOf-substⁱ sh1 (renTel s w1s) (1 + (2 + n))
        b₀φ : innerOf (renTel s w1s) (1 + (2 + n)) ≡ innerOf s (1 + (2 + n))
        b₀φ = innerOf-renTel s w1s (1 + (2 + n))
        P1φ : subst (Tel (1 + (2 + n))) ri (renTel (shift1 s) (assocSwapᵣ 1 2)) ≡ Y
        P1φ = cong (λ p → subst (Tel (1 + (2 + n))) p (renTel (shift1 s) (assocSwapᵣ 1 2)))
                   (≡-irrelevant ri (a₀φ ■ b₀φ ■ sh1))
                ■ subst-■ (Tel (1 + (2 + n))) a₀φ (b₀φ ■ sh1) (renTel (shift1 s) (assocSwapᵣ 1 2))
                ■ cong (subst (Tel (1 + (2 + n))) (b₀φ ■ sh1))
                       (renTel-substⁱ sh1 (renTel s w1s) (assocSwapᵣ 1 2))
                ■ subst-■ (Tel (1 + (2 + n))) b₀φ sh1 (renTel (renTel s w1s) (assocSwapᵣ 1 2))
                ■ cong (subst (Tel (1 + (2 + n))) sh1) (renTel-renTel s w1s (assocSwapᵣ 1 2))
                ■ cong (subst (Tel (1 + (2 + n))) sh1) (renTel-cong s aswap12-wk)
        ρ′ : (1 + j) →ᵣ 1 + j
        ρ′ = λ y → subst 𝔽 ri (liftRen (shift1 s) (assocSwapᵣ 1 2) y)
        invLift : ∀ y → subst 𝔽 ri (liftRen (shift1 s) (assocSwapᵣ 1 2) (α y)) ≡ y
        invLift y = liftId-liftRen (shift1 s) (assocSwapᵣ 1 2) (α y)
                      ■ liftId-· (shift1 s) (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) y
                      ■ liftId-cong (shift1 s) aswap-21-12 y
                      ■ liftId-id (shift1 s) (λ _ → refl) y
        invComp : (α ·ₖ ρ′) ≗ idₖ ⦃ Kᵣ ⦄
        invComp y = invLift y
        q₁ : innerOf (shift1 s ++ᵗ u-rec) (1 + (2 + n))
               ≡ innerOf u-rec (innerOf (shift1 s) (1 + (2 + n)))
        q₁ = innerOf-++ᵗ (shift1 s) u-rec (1 + (2 + n))
        riEq : innerOf u-rec (innerOf (shift1 s) (1 + (2 + n))) ≡ innerOf u-rec (1 + j)
        riEq = cong (innerOf u-rec) ri
        cinEq : innerOf u-rec (1 + j) ≡ innerOf u (1 + j)
        cinEq = innerOf-renTel u α (1 + j)
        ee : innerOf (shift1 s ++ᵗ u-rec) (1 + (2 + n)) ≡ k
        ee = q₁ ■ riEq ■ cinEq ■ renTel-id u
        uReconcile : subst (Tel (1 + j)) (cinEq ■ renTel-id u) (renTel u-rec ρ′) ≡ u
        uReconcile = subst-■ (Tel (1 + j)) cinEq (renTel-id u) (renTel u-rec ρ′)
                       ■ cong (subst (Tel (1 + j)) (renTel-id u))
                              (renTel-renTel u α ρ′ ■ renTel-cong u invComp)
                       ■ renTel-idᵗ u
        telCore′ : subst (Tel (1 + (2 + n))) ee (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2))
                     ≡ Y ++ᵗ u
        telCore′ =
          subst-■ (Tel (1 + (2 + n))) q₁ (riEq ■ cinEq ■ renTel-id u)
                  (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2))
            ■ cong (subst (Tel (1 + (2 + n))) (riEq ■ cinEq ■ renTel-id u))
                   (renTel-++ᵗ (shift1 s) u-rec (assocSwapᵣ 1 2))
            ■ subst-■ (Tel (1 + (2 + n))) riEq (cinEq ■ renTel-id u)
                   (renTel (shift1 s) (assocSwapᵣ 1 2) ++ᵗ renTel u-rec (liftRen (shift1 s) (assocSwapᵣ 1 2)))
            ■ cong (subst (Tel (1 + (2 + n))) (cinEq ■ renTel-id u))
                   (telMidᴺ ri (renTel (shift1 s) (assocSwapᵣ 1 2)) u-rec (λ y → refl))
            ■ subst-++ᵗ (subst (Tel (1 + (2 + n))) ri (renTel (shift1 s) (assocSwapᵣ 1 2)))
                        (cinEq ■ renTel-id u) (renTel u-rec ρ′)
            ■ cong₂ _++ᵗ_ P1φ uReconcile
        thrInv : ∀ x → subst 𝔽 ee
                         ((liftRen u α ·ₖ liftRen (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2)) x)
                         ≡ idₖ ⦃ Kᵣ ⦄ x
        thrInv x =
          subst-■ 𝔽 q₁ (riEq ■ cinEq ■ renTel-id u)
                  (liftRen (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2) (liftRen u α x))
            ■ cong (subst 𝔽 (riEq ■ cinEq ■ renTel-id u))
                   (liftRen-++ᵗ (shift1 s) u-rec (assocSwapᵣ 1 2) (liftRen u α x))
            ■ subst-■ 𝔽 riEq (cinEq ■ renTel-id u)
                   (liftRen u-rec (liftRen (shift1 s) (assocSwapᵣ 1 2)) (liftRen u α x))
            ■ cong (subst 𝔽 (cinEq ■ renTel-id u))
                   (liftMid ri u-rec (λ y → refl) (liftRen u α x))
            ■ subst-■ 𝔽 cinEq (renTel-id u) (liftRen u-rec ρ′ (liftRen u α x))
            ■ cong (subst 𝔽 (renTel-id u)) (liftRen-· u α ρ′ x ■ liftRen-cong u invComp x)
            ■ liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x
            ■ liftId-id u (λ _ → refl) x
        eqA₀ : mkNF (tφ f c (shift1 (tν s) ++ᵗ u)) es
                 ≡ mkNF (tφ f c (tν (Y ++ᵗ u))) es
        eqA₀ = cong (λ T → mkNF (tφ f c (T ++ᵗ u)) es) (subst-tν sh1 (renTel s (wν ↑* 2)))
        eqA₁rev : mkNF (tφ f c (tν (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2))))
                       (map (_⋯ liftRen (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2)) es-rec)
                    ≡ mkNF (tφ f c (tν (Y ++ᵗ u))) es
        eqA₁rev = NF-≡ ee
                    ( subst-tφ ee f c (tν (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2)))
                    ■ cong (tφ f c) ( subst-tν ee (renTel (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2))
                                    ■ cong tν telCore′ ) )
                    ( cong (subst (λ z → List (Tm z)) ee)
                           (map-fuse (liftRen u α)
                                     (liftRen (shift1 s ++ᵗ u-rec) (assocSwapᵣ 1 2)) es)
                    ■ map-⋯-subst ee thrInv es
                    ■ map-⋯-id (λ _ → refl) es )
    eqCinner : innerOf (renTel u (liftId (shift1 s) (assocSwapᵣ 2 1))) (1 + j) ≡ innerOf u (1 + j)
    eqCinner = innerOf-renTel u (liftId (shift1 s) (assocSwapᵣ 2 1)) (1 + j)
    deepReconC : subst (Tel (1 + j)) eqCinner (renTel u-rec (bubφ s)) ≡ renTel u (bubφ (tν s))
    deepReconC = renTel-renTel u (liftId (shift1 s) (assocSwapᵣ 2 1)) (bubφ s)
    eqC : mkNF (tν (s ++ᵗ tφ f ((c ⋯ weaken* ⦃ Kᵣ ⦄ 2) ⋯ wkTel s) (renTel u-rec (bubφ s))))
               (map (_⋯ liftRen u-rec (bubφ s)) es-rec)
            ≡ mkNF (tν s ++ᵗ tφ f (c ⋯ wkTel (tν s)) (renTel u (bubφ (tν s))))
                   (map (_⋯ liftRen u (bubφ (tν s))) es)
    eqC = NF-≡ eqCinner
            ( subst-tν eqCinner (s ++ᵗ tφ f ((c ⋯ weaken* ⦃ Kᵣ ⦄ 2) ⋯ wkTel s) (renTel u-rec (bubφ s)))
            ■ cong tν ( subst-++ᵗ s eqCinner (tφ f ((c ⋯ weaken* ⦃ Kᵣ ⦄ 2) ⋯ wkTel s) (renTel u-rec (bubφ s)))
                      ■ cong (s ++ᵗ_) ( subst-tφ eqCinner f ((c ⋯ weaken* ⦃ Kᵣ ⦄ 2) ⋯ wkTel s) (renTel u-rec (bubφ s))
                                      ■ cong₂ (tφ f) (fusion c (weaken* ⦃ Kᵣ ⦄ 2) (wkTel s)) deepReconC ) ) )
            ( cong (subst (λ z → List (Tm z)) eqCinner)
                   (map-fuse (liftRen u (liftId (shift1 s) (assocSwapᵣ 2 1)))
                             (liftRen u-rec (bubφ s)) es)
            ■ map-⋯-subst eqCinner (liftRen-· u (liftId (shift1 s) (assocSwapᵣ 2 1)) (bubφ s)) es )

bubbleφᵩ⁻ : ∀ {n j k} (f : Flag) (c : Tm n) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) u) es
             ~ᵩ mkNF (tφ f c (shift1 s ++ᵗ renTel u (bubφ⁻ s))) (map (_⋯ liftRen u (bubφ⁻ s)) es)
bubbleφᵩ⁻ f c s u es =
  ~ᵩ-trans (≡→~ᵩ (sym (φ⁻-eqR f c s u es)))
          (~ᵩ-sym (bubbleφᵩ f c s (renTel u (bubφ⁻ s)) (map (_⋯ liftRen u (bubφ⁻ s)) es)))

------------------------------------------------------------------------
-- Blockify: every normal form with enough νs is `~ᵩ`-equal to block form.
------------------------------------------------------------------------

blockify : ∀ {n} (N : NF n) →
           (νcountᵗ (tel N) ≡ 0 → φcountᵗ (tel N) ≡ 0) →
           Σ[ M ∈ NF n ] Block (tel M) × (N ~ᵩ M)
blockify (mkNF t es) hyp with headView t
... | vrun r =
  mkNF t es , run-Block r (hyp (run-νcountᵗ r)) , ~ᵩ-refl
... | vν {s = s} rs u =
  mkNF (tν (shift2 s ++ᵗ renTel u (bubν⁻ s))) (map (_⋯ liftRen u (bubν⁻ s)) es)
    , bν
    , bubbleνᵩ⁻ rs u es
