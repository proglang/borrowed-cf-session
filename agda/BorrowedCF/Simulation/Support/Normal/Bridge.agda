-- | REFUTATION: `BlockBridge` (Normal.Factor) is FALSE.
--
--   The candidate lemma was
--
--       BlockBridge : ∀ {n} {N₁ N₂ : NF n} →
--                     Block (tel N₁) → Block (tel N₂) → N₁ ~ N₂ → N₁ ~ᵇ N₂
--
--   Counterexample (ambient scope 0, five bound names).  Take
--
--       N₁ = mkNF (tν (tν (tφ drop [])))  [ e₀ ]      -- [ν][νφ]
--       N₂ = mkNF (tν (tφ drop (tν [])))  [ e₀ ⋯ assocSwapᵣ 1 2 ]
--                                                     -- [νφ][ν]
--
--   with e₀ = `0 ⊗ (`1 ⊗ (`2 ⊗ (`3 ⊗ `4))) a single live thread mentioning
--   all five names.  `perm-νφ` at prefix `s = tν []` relates N₁ ~₁ N₂ — the φ
--   cell leaves the INNER block's run and joins the OUTER block's run, while
--   both ν pairs stay put: the renaming is 0↦2, 1↦0, 2↦1 and FIXES 3, 4.
--
--   Why no `~ᵇ` chain can do this: every `~ᵇ₁` generator moves whole slots
--   with an explicit renaming — `bswpᵇ` transposes two complete blocks (each
--   ν travels WITH its φ-run), `ν1ᵇ` flips one ν pair in place, `φφᵇ` needs
--   two adjacent φ cells (none here), `thrᵇ`/`delᵇ` do not touch names.  So
--   along any chain between the two shapes above the composite renaming is
--   block-structured with RUN-SIZES PRESERVED: the run-1 block of [ν][νφ]
--   (names 1,2) must land on the run-1 slot of [νφ][ν] (names 3,4), and the
--   run-0 block (names 3,4) on the run-0 slot (names 0,1).  The generic
--   thread e₀ observes the composite exactly, and perm-νφ's renaming fixes
--   3,4 — outside the reachable set.  Formally: `Inv` below enumerates the
--   full `~ᵇ`-reachable class of N₁ (2 telescopes × 4 renamings each), is
--   closed under `~ᵇ₁` in both directions, holds at N₁, and fails at N₂.
--
--   Consequence: `factor`'s missing hypothesis cannot be discharged as
--   stated; the φ-migration across an interior ν boundary (`perm-νφ` under a
--   `tν` prefix) is precisely the `~`-move that block moves cannot imitate.
--   (On the φ-free fragment `φfree-bridge` stands; a single-block version of
--   BlockBridge is unaffected by this counterexample, which needs 2 blocks.)
module BorrowedCF.Simulation.Support.Normal.Bridge where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Flat using (live; live*)
open import BorrowedCF.Simulation.Support.Normal.Witness using (live*-map; live*-↭)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2)
open import BorrowedCF.Simulation.Support.Normal.Bubble using (map-⋯-id)
open import BorrowedCF.Simulation.Support.Normal.Nat using (map-fuse)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
open import BorrowedCF.Simulation.Support.Normal.Factor

open Fin.Patterns

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭-singleton-inv)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- The two block telescopes and the probe thread.
------------------------------------------------------------------------

T₁ᵗ T₂ᵗ : Tel 0 5
T₁ᵗ = tν (tν (tφ drop []))          -- [ν][νφ] : inner block owns the φ
T₂ᵗ = tν (tφ drop (tν []))          -- [νφ][ν] : outer block owns the φ

e₀ : Tm 5
e₀ = (` 0F) ⊗ ((` 1F) ⊗ ((` 2F) ⊗ ((` 3F) ⊗ (` 4F))))

-- The 4 renamings `~ᵇ` can realise out of T₁ᵗ (identity cells, ν flips):
-- images of e₀ under {id, flip inner pair {1,2}, flip outer pair {3,4}, both}.
a₁ a₂ a₃ a₄ : Tm 5
a₁ = e₀
a₂ = (` 0F) ⊗ ((` 2F) ⊗ ((` 1F) ⊗ ((` 3F) ⊗ (` 4F))))
a₃ = (` 0F) ⊗ ((` 1F) ⊗ ((` 2F) ⊗ ((` 4F) ⊗ (` 3F))))
a₄ = (` 0F) ⊗ ((` 2F) ⊗ ((` 1F) ⊗ ((` 4F) ⊗ (` 3F))))

-- ... and into T₂ᵗ (block swap σ₁₂ = {0↦2,1↦3,2↦4,3↦0,4↦1}, times flips).
b₁ b₂ b₃ b₄ : Tm 5
b₁ = (` 2F) ⊗ ((` 3F) ⊗ ((` 4F) ⊗ ((` 0F) ⊗ (` 1F))))
b₂ = (` 2F) ⊗ ((` 3F) ⊗ ((` 4F) ⊗ ((` 1F) ⊗ (` 0F))))
b₃ = (` 2F) ⊗ ((` 4F) ⊗ ((` 3F) ⊗ ((` 0F) ⊗ (` 1F))))
b₄ = (` 2F) ⊗ ((` 4F) ⊗ ((` 3F) ⊗ ((` 1F) ⊗ (` 0F))))

-- perm-νφ's image thread: {0↦2,1↦0,2↦1}, 3 and 4 FIXED — in none of the bᵢ.
x₂ : Tm 5
x₂ = (` 2F) ⊗ ((` 0F) ⊗ ((` 1F) ⊗ ((` 3F) ⊗ (` 4F))))

------------------------------------------------------------------------
-- The six renamings the generators can fire with, between/on T₁ᵗ and T₂ᵗ.
------------------------------------------------------------------------

fA₁ fB₁ fA₂ fB₂ σ₁₂ σ₂₁ : 5 →ᵣ 5
fA₁ = liftId (tν (tφ drop [])) (swapᵣ 1 1)     -- ν1ᵇ on T₁ᵗ, outer ν: swap 3,4
fB₁ = liftId (tφ drop [])      (swapᵣ 1 1)     -- ν1ᵇ on T₁ᵗ, inner ν: swap 1,2
fA₂ = liftId (tφ drop (tν [])) (swapᵣ 1 1)     -- ν1ᵇ on T₂ᵗ, outer ν: swap 3,4
fB₂ = liftId ([] {n = 5})      (swapᵣ 1 1)     -- ν1ᵇ on T₂ᵗ, inner ν: swap 0,1
σ₁₂ = bswapRen ([] {n = 2}) (rφ {f = drop} rnil) ([] {n = 5})  -- bswpᵇ T₁ᵗ→T₂ᵗ
σ₂₁ = bswapRen (tφ drop []) rnil ([] {n = 5})                  -- bswpᵇ T₂ᵗ→T₁ᵗ

private
  -- Orientation sanity checks (all definitional).
  _ : e₀ ⋯ assocSwapᵣ 1 2 ≡ x₂
  _ = refl
  _ : e₀ ⋯ fA₁ ≡ a₃
  _ = refl
  _ : e₀ ⋯ fB₁ ≡ a₂
  _ = refl
  _ : e₀ ⋯ σ₁₂ ≡ b₁
  _ = refl
  _ : b₁ ⋯ σ₂₁ ≡ a₁
  _ = refl
  _ : b₁ ⋯ fA₂ ≡ b₃
  _ = refl
  _ : b₁ ⋯ fB₂ ≡ b₂
  _ = refl

------------------------------------------------------------------------
-- The reachable thread predicate: a single live thread, drawn from the
-- 4 realisable images on each side.
------------------------------------------------------------------------

Ok4 : Tm 5 → Tm 5 → Tm 5 → Tm 5 → List (Tm 5) → Set
Ok4 p q r s es = (live* es ≡ p ∷ []) ⊎ (live* es ≡ q ∷ []) ⊎
                 (live* es ≡ r ∷ []) ⊎ (live* es ≡ s ∷ [])

OkA OkB : List (Tm 5) → Set
OkA = Ok4 a₁ a₂ a₃ a₄
OkB = Ok4 b₁ b₂ b₃ b₄

-- Pushing the singleton along a renaming, and pulling it back along the
-- pointwise inverse.
push : (ρ : 5 →ᵣ 5) (es : List (Tm 5)) {x : Tm 5} →
       live* es ≡ x ∷ [] → live* (map (_⋯ ρ) es) ≡ (x ⋯ ρ) ∷ []
push ρ es q = live*-map ρ es ■ cong (map (_⋯ ρ)) q

pull : (ρ ρ⁻ : 5 →ᵣ 5) → ((x : 𝔽 5) → ρ⁻ (ρ x) ≡ x) →
       (es : List (Tm 5)) {x : Tm 5} →
       live* (map (_⋯ ρ) es) ≡ x ∷ [] → live* es ≡ (x ⋯ ρ⁻) ∷ []
pull ρ ρ⁻ inv es q =
  sym (map-⋯-id {σ = ρ ·ₖ ρ⁻} inv (live* es))
    ■ sym (map-fuse ρ ρ⁻ (live* es))
    ■ cong (map (_⋯ ρ⁻)) (sym (live*-map ρ es) ■ q)

-- The pointwise inverse laws (finite, definitional).
inv-fA₁ : (x : 𝔽 5) → fA₁ (fA₁ x) ≡ x
inv-fA₁ 0F = refl; inv-fA₁ 1F = refl; inv-fA₁ 2F = refl
inv-fA₁ 3F = refl; inv-fA₁ 4F = refl

inv-fB₁ : (x : 𝔽 5) → fB₁ (fB₁ x) ≡ x
inv-fB₁ 0F = refl; inv-fB₁ 1F = refl; inv-fB₁ 2F = refl
inv-fB₁ 3F = refl; inv-fB₁ 4F = refl

inv-fA₂ : (x : 𝔽 5) → fA₂ (fA₂ x) ≡ x
inv-fA₂ 0F = refl; inv-fA₂ 1F = refl; inv-fA₂ 2F = refl
inv-fA₂ 3F = refl; inv-fA₂ 4F = refl

inv-fB₂ : (x : 𝔽 5) → fB₂ (fB₂ x) ≡ x
inv-fB₂ 0F = refl; inv-fB₂ 1F = refl; inv-fB₂ 2F = refl
inv-fB₂ 3F = refl; inv-fB₂ 4F = refl

inv-σᵃ : (x : 𝔽 5) → σ₂₁ (σ₁₂ x) ≡ x
inv-σᵃ 0F = refl; inv-σᵃ 1F = refl; inv-σᵃ 2F = refl
inv-σᵃ 3F = refl; inv-σᵃ 4F = refl

inv-σᵇ : (x : 𝔽 5) → σ₁₂ (σ₂₁ x) ≡ x
inv-σᵇ 0F = refl; inv-σᵇ 1F = refl; inv-σᵇ 2F = refl
inv-σᵇ 3F = refl; inv-σᵇ 4F = refl

------------------------------------------------------------------------
-- Transfer tables: how each realisable renaming permutes the 4 images.
------------------------------------------------------------------------

okA-fA₁ : ∀ (es : List (Tm 5)) → OkA es → OkA (map (_⋯ fA₁) es)
okA-fA₁ es (inj₁ q)               = inj₂ (inj₂ (inj₁ (push fA₁ es q)))
okA-fA₁ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₂ (push fA₁ es q)))
okA-fA₁ es (inj₂ (inj₂ (inj₁ q))) = inj₁ (push fA₁ es q)
okA-fA₁ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₁ (push fA₁ es q))

okA-fB₁ : ∀ (es : List (Tm 5)) → OkA es → OkA (map (_⋯ fB₁) es)
okA-fB₁ es (inj₁ q)               = inj₂ (inj₁ (push fB₁ es q))
okA-fB₁ es (inj₂ (inj₁ q))        = inj₁ (push fB₁ es q)
okA-fB₁ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₂ (push fB₁ es q)))
okA-fB₁ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₁ (push fB₁ es q)))

okB-fA₂ : ∀ (es : List (Tm 5)) → OkB es → OkB (map (_⋯ fA₂) es)
okB-fA₂ es (inj₁ q)               = inj₂ (inj₂ (inj₁ (push fA₂ es q)))
okB-fA₂ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₂ (push fA₂ es q)))
okB-fA₂ es (inj₂ (inj₂ (inj₁ q))) = inj₁ (push fA₂ es q)
okB-fA₂ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₁ (push fA₂ es q))

okB-fB₂ : ∀ (es : List (Tm 5)) → OkB es → OkB (map (_⋯ fB₂) es)
okB-fB₂ es (inj₁ q)               = inj₂ (inj₁ (push fB₂ es q))
okB-fB₂ es (inj₂ (inj₁ q))        = inj₁ (push fB₂ es q)
okB-fB₂ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₂ (push fB₂ es q)))
okB-fB₂ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₁ (push fB₂ es q)))

okA-σ₁₂ : ∀ (es : List (Tm 5)) → OkA es → OkB (map (_⋯ σ₁₂) es)
okA-σ₁₂ es (inj₁ q)               = inj₁ (push σ₁₂ es q)
okA-σ₁₂ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₁ (push σ₁₂ es q)))
okA-σ₁₂ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₁ (push σ₁₂ es q))
okA-σ₁₂ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (push σ₁₂ es q)))

okB-σ₂₁ : ∀ (es : List (Tm 5)) → OkB es → OkA (map (_⋯ σ₂₁) es)
okB-σ₂₁ es (inj₁ q)               = inj₁ (push σ₂₁ es q)
okB-σ₂₁ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₁ (push σ₂₁ es q)))
okB-σ₂₁ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₁ (push σ₂₁ es q))
okB-σ₂₁ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (push σ₂₁ es q)))

-- The same tables read backwards (the flips are involutions; the two block
-- swaps are mutually inverse).
okA-fA₁⁻ : ∀ (es : List (Tm 5)) → OkA (map (_⋯ fA₁) es) → OkA es
okA-fA₁⁻ es (inj₁ q)               = inj₂ (inj₂ (inj₁ (pull fA₁ fA₁ inv-fA₁ es q)))
okA-fA₁⁻ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₂ (pull fA₁ fA₁ inv-fA₁ es q)))
okA-fA₁⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₁ (pull fA₁ fA₁ inv-fA₁ es q)
okA-fA₁⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₁ (pull fA₁ fA₁ inv-fA₁ es q))

okA-fB₁⁻ : ∀ (es : List (Tm 5)) → OkA (map (_⋯ fB₁) es) → OkA es
okA-fB₁⁻ es (inj₁ q)               = inj₂ (inj₁ (pull fB₁ fB₁ inv-fB₁ es q))
okA-fB₁⁻ es (inj₂ (inj₁ q))        = inj₁ (pull fB₁ fB₁ inv-fB₁ es q)
okA-fB₁⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₂ (pull fB₁ fB₁ inv-fB₁ es q)))
okA-fB₁⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₁ (pull fB₁ fB₁ inv-fB₁ es q)))

okB-fA₂⁻ : ∀ (es : List (Tm 5)) → OkB (map (_⋯ fA₂) es) → OkB es
okB-fA₂⁻ es (inj₁ q)               = inj₂ (inj₂ (inj₁ (pull fA₂ fA₂ inv-fA₂ es q)))
okB-fA₂⁻ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₂ (pull fA₂ fA₂ inv-fA₂ es q)))
okB-fA₂⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₁ (pull fA₂ fA₂ inv-fA₂ es q)
okB-fA₂⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₁ (pull fA₂ fA₂ inv-fA₂ es q))

okB-fB₂⁻ : ∀ (es : List (Tm 5)) → OkB (map (_⋯ fB₂) es) → OkB es
okB-fB₂⁻ es (inj₁ q)               = inj₂ (inj₁ (pull fB₂ fB₂ inv-fB₂ es q))
okB-fB₂⁻ es (inj₂ (inj₁ q))        = inj₁ (pull fB₂ fB₂ inv-fB₂ es q)
okB-fB₂⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₂ (pull fB₂ fB₂ inv-fB₂ es q)))
okB-fB₂⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₁ (pull fB₂ fB₂ inv-fB₂ es q)))

okB-σ₁₂⁻ : ∀ (es : List (Tm 5)) → OkB (map (_⋯ σ₁₂) es) → OkA es
okB-σ₁₂⁻ es (inj₁ q)               = inj₁ (pull σ₁₂ σ₂₁ inv-σᵃ es q)
okB-σ₁₂⁻ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₁ (pull σ₁₂ σ₂₁ inv-σᵃ es q)))
okB-σ₁₂⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₁ (pull σ₁₂ σ₂₁ inv-σᵃ es q))
okB-σ₁₂⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (pull σ₁₂ σ₂₁ inv-σᵃ es q)))

okA-σ₂₁⁻ : ∀ (es : List (Tm 5)) → OkA (map (_⋯ σ₂₁) es) → OkB es
okA-σ₂₁⁻ es (inj₁ q)               = inj₁ (pull σ₂₁ σ₁₂ inv-σᵇ es q)
okA-σ₂₁⁻ es (inj₂ (inj₁ q))        = inj₂ (inj₂ (inj₁ (pull σ₂₁ σ₁₂ inv-σᵇ es q)))
okA-σ₂₁⁻ es (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₁ (pull σ₂₁ σ₁₂ inv-σᵇ es q))
okA-σ₂₁⁻ es (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (pull σ₂₁ σ₁₂ inv-σᵇ es q)))

-- Thread permutation preserves the singleton.
thr-live : ∀ {es es′ : List (Tm 5)} {x} →
           es ↭ es′ → live* es ≡ x ∷ [] → live* es′ ≡ x ∷ []
thr-live p q = ↭-singleton-inv (↭-sym (subst (_↭ _) q (live*-↭ p)))

ok4-thr : ∀ {p q r s} {es es′ : List (Tm 5)} →
          es ↭ es′ → Ok4 p q r s es → Ok4 p q r s es′
ok4-thr t (inj₁ q)               = inj₁ (thr-live t q)
ok4-thr t (inj₂ (inj₁ q))        = inj₂ (inj₁ (thr-live t q))
ok4-thr t (inj₂ (inj₂ (inj₁ q))) = inj₂ (inj₂ (inj₁ (thr-live t q)))
ok4-thr t (inj₂ (inj₂ (inj₂ q))) = inj₂ (inj₂ (inj₂ (thr-live t q)))

------------------------------------------------------------------------
-- Telescope equation toolkit.
------------------------------------------------------------------------

tν-inj : ∀ {n k} {t u : Tel (2 + n) k} → tν t ≡ tν u → t ≡ u
tν-inj refl = refl

tφ-inj : ∀ {n k} {f g : Flag} {t u : Tel (1 + n) k} →
         tφ f t ≡ tφ g u → (f ≡ g) × (t ≡ u)
tφ-inj refl = refl , refl

++ᵗ-tν≢[] : ∀ {n j} (s : Tel n j) {t : Tel (2 + j) n} → s ++ᵗ tν t ≡ [] → ⊥
++ᵗ-tν≢[] []       ()
++ᵗ-tν≢[] (tν s)   ()
++ᵗ-tν≢[] (tφ f s) ()

++ᵗ-tφ≢[] : ∀ {n j} (s : Tel n j) {f} {t : Tel (1 + j) n} → s ++ᵗ tφ f t ≡ [] → ⊥
++ᵗ-tφ≢[] []       ()
++ᵗ-tφ≢[] (tν s)   ()
++ᵗ-tφ≢[] (tφ f s) ()

¬Block-tφ : ∀ {n k f} {t : Tel (1 + n) k} → Block (tφ f t) → ⊥
¬Block-tφ ()

-- Splitting an NF equality into scope, telescope and thread equalities.
NF-inv : ∀ {n k k′} {t : Tel n k} {t′ : Tel n k′}
         {es : List (Tm k)} {es′ : List (Tm k′)} →
         mkNF t es ≡ mkNF t′ es′ →
         Σ[ eq ∈ k ≡ k′ ] (subst (Tel n) eq t ≡ t′)
                        × (subst (λ j → List (Tm j)) eq es ≡ es′)
NF-inv refl = refl , refl , refl

------------------------------------------------------------------------
-- Views: the COMPLETE lists of generator decompositions of T₁ᵗ and T₂ᵗ.
------------------------------------------------------------------------

-- `ν1ᵇ` on T₁ᵗ: outer or inner ν.
data ν1V₁ : ∀ {j} → Tel 0 j → Tel (2 + j) 5 → Set where
  v₁-out : ν1V₁ [] (tν (tφ drop []))
  v₁-in  : ν1V₁ (tν []) (tφ drop [])

ν1V₁? : ∀ {j} (s : Tel 0 j) (t : Tel (2 + j) 5) → s ++ᵗ tν t ≡ T₁ᵗ → ν1V₁ s t
ν1V₁? []                  _ refl = v₁-out
ν1V₁? (tν [])             _ refl = v₁-in
ν1V₁? (tν (tν []))        _ ()
ν1V₁? (tν (tν (tν s)))    _ ()
ν1V₁? (tν (tν (tφ f s)))  _ eq   =
  ⊥-elim (++ᵗ-tν≢[] s (proj₂ (tφ-inj (tν-inj (tν-inj eq)))))
ν1V₁? (tν (tφ f s))       _ ()
ν1V₁? (tφ f s)            _ ()

-- `ν1ᵇ` on T₂ᵗ: outer or inner ν.
data ν1V₂ : ∀ {j} → Tel 0 j → Tel (2 + j) 5 → Set where
  v₂-out : ν1V₂ [] (tφ drop (tν []))
  v₂-in  : ν1V₂ (tν (tφ drop [])) []

ν1V₂? : ∀ {j} (s : Tel 0 j) (t : Tel (2 + j) 5) → s ++ᵗ tν t ≡ T₂ᵗ → ν1V₂ s t
ν1V₂? []                  _ refl = v₂-out
ν1V₂? (tν [])             _ ()
ν1V₂? (tν (tν s))         _ ()
ν1V₂? (tν (tφ f []))      _ refl = v₂-in
ν1V₂? (tν (tφ f (tν s)))  _ eq   =
  ⊥-elim (++ᵗ-tν≢[] s (tν-inj (proj₂ (tφ-inj (tν-inj eq)))))
ν1V₂? (tν (tφ f (tφ g s))) _ ()
ν1V₂? (tφ f s)            _ ()

-- `φφᵇ` fires nowhere: neither telescope has two adjacent φ cells.
φφ¬₁ : ∀ {j} (s : Tel 0 j) (x y : Flag) (t : Tel (2 + j) 5) →
       s ++ᵗ tφ x (tφ y t) ≡ T₁ᵗ → ⊥
φφ¬₁ []                  x y t ()
φφ¬₁ (tν [])             x y t ()
φφ¬₁ (tν (tν []))        x y t ()
φφ¬₁ (tν (tν (tν s)))    x y t ()
φφ¬₁ (tν (tν (tφ f s)))  x y t eq =
  ++ᵗ-tφ≢[] s (proj₂ (tφ-inj (tν-inj (tν-inj eq))))
φφ¬₁ (tν (tφ f s))       x y t ()
φφ¬₁ (tφ f s)            x y t ()

φφ¬₂ : ∀ {j} (s : Tel 0 j) (x y : Flag) (t : Tel (2 + j) 5) →
       s ++ᵗ tφ x (tφ y t) ≡ T₂ᵗ → ⊥
φφ¬₂ []                   x y t ()
φφ¬₂ (tν [])              x y t ()
φφ¬₂ (tν (tν s))          x y t ()
φφ¬₂ (tν (tφ f []))       x y t ()
φφ¬₂ (tν (tφ f (tν s)))   x y t eq =
  ++ᵗ-tφ≢[] s (tν-inj (proj₂ (tφ-inj (tν-inj eq))))
φφ¬₂ (tν (tφ f (tφ g s))) x y t ()
φφ¬₂ (tφ f s)             x y t ()

-- `bswpᵇ` SOURCE decompositions: exactly one per telescope.
data BS₁ : ∀ {j i m} → Tel 0 j → Tel (2 + j) i → Tel (2 + i) m → Tel m 5 → Set where
  bs₁ : BS₁ [] [] (tφ drop []) []

bs₁? : ∀ {j i m} (s : Tel 0 j) (a : Tel (2 + j) i) (rb : Tel (2 + i) m)
       (t : Tel m 5) → Run a → Run rb → Block t →
       s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t)) ≡ T₁ᵗ → BS₁ s a rb t
bs₁? [] _ _ _ rnil (rφ rnil)     bt refl = bs₁
bs₁? [] _ _ _ rnil (rφ (rφ w″))  bt ()
bs₁? [] _ _ _ rnil rnil          bt refl = ⊥-elim (¬Block-tφ bt)
bs₁? [] _ _ _ (rφ ra′) w         bt ()
bs₁? (tν []) _ _ _ rnil w bt ()
bs₁? (tν []) _ _ _ (rφ {r = a′} ra′) w bt eq =
  ⊥-elim (++ᵗ-tν≢[] a′ (proj₂ (tφ-inj (tν-inj (tν-inj eq)))))
bs₁? (tν (tν []))       _ _ _ ra w bt ()
bs₁? (tν (tν (tν s)))   _ _ _ ra w bt ()
bs₁? (tν (tν (tφ f s))) _ _ _ ra w bt eq =
  ⊥-elim (++ᵗ-tν≢[] s (proj₂ (tφ-inj (tν-inj (tν-inj eq)))))
bs₁? (tν (tφ f s))      _ _ _ ra w bt ()
bs₁? (tφ f s)           _ _ _ ra w bt ()

data BS₂ : ∀ {j i m} → Tel 0 j → Tel (2 + j) i → Tel (2 + i) m → Tel m 5 → Set where
  bs₂ : BS₂ [] (tφ drop []) [] []

bs₂? : ∀ {j i m} (s : Tel 0 j) (a : Tel (2 + j) i) (rb : Tel (2 + i) m)
       (t : Tel m 5) → Run a → Run rb → Block t →
       s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t)) ≡ T₂ᵗ → BS₂ s a rb t
bs₂? [] _ _ _ rnil            w        bt ()
bs₂? [] _ _ _ (rφ rnil)       rnil     bt refl = bs₂
bs₂? [] _ _ _ (rφ rnil)       (rφ w′)  bt ()
bs₂? [] _ _ _ (rφ (rφ ra″))   w        bt ()
bs₂? (tν [])     _ _ _ ra w bt ()
bs₂? (tν (tν s)) _ _ _ ra w bt ()
bs₂? (tν (tφ f [])) a _ _ ra w bt eq =
  ⊥-elim (++ᵗ-tν≢[] a (tν-inj (proj₂ (tφ-inj (tν-inj eq)))))
bs₂? (tν (tφ f (tν s))) _ _ _ ra w bt eq =
  ⊥-elim (++ᵗ-tν≢[] s (tν-inj (proj₂ (tφ-inj (tν-inj eq)))))
bs₂? (tν (tφ f (tφ g s))) _ _ _ ra w bt ()
bs₂? (tφ f s)             _ _ _ ra w bt ()

-- `bswpᵇ` TARGET decompositions (`bswapTel a w t = tν (dragTel …)`).
data BT₁ : ∀ {j i m} → Tel 0 j → Tel (2 + j) i → Tel (2 + i) m → Tel m 5 → Set where
  bt₁v : BT₁ [] (tφ drop []) [] []

bt₁? : ∀ {j i m} (s : Tel 0 j) (a : Tel (2 + j) i) (rb : Tel (2 + i) m)
       (t : Tel m 5) → Run a → (w : Run rb) → Block t →
       s ++ᵗ tν (dragTel (tν (shift2 a)) w t) ≡ T₁ᵗ → BT₁ s a rb t
bt₁? [] _ _ _ rnil          rnil     bt refl = ⊥-elim (¬Block-tφ bt)
bt₁? [] _ _ _ (rφ rnil)     rnil     bt refl = bt₁v
bt₁? [] _ _ _ (rφ (rφ ra″)) rnil     bt ()
bt₁? [] _ _ _ ra            (rφ w′)  bt ()
bt₁? (tν []) _ _ _ ra rnil         bt ()
bt₁? (tν []) _ _ _ ra (rφ rnil)    bt ()
bt₁? (tν []) _ _ _ ra (rφ (rφ w″)) bt ()
bt₁? (tν (tν []))       _ _ _ ra w bt ()
bt₁? (tν (tν (tν s)))   _ _ _ ra w bt ()
bt₁? (tν (tν (tφ f s))) _ _ _ ra w bt eq =
  ⊥-elim (++ᵗ-tν≢[] s (proj₂ (tφ-inj (tν-inj (tν-inj eq)))))
bt₁? (tν (tφ f s))      _ _ _ ra w bt ()
bt₁? (tφ f s)           _ _ _ ra w bt ()

data BT₂ : ∀ {j i m} → Tel 0 j → Tel (2 + j) i → Tel (2 + i) m → Tel m 5 → Set where
  bt₂v : BT₂ [] [] (tφ drop []) []

bt₂? : ∀ {j i m} (s : Tel 0 j) (a : Tel (2 + j) i) (rb : Tel (2 + i) m)
       (t : Tel m 5) → Run a → (w : Run rb) → Block t →
       s ++ᵗ tν (dragTel (tν (shift2 a)) w t) ≡ T₂ᵗ → BT₂ s a rb t
bt₂? [] _ _ _ ra        rnil          bt ()
bt₂? [] _ _ _ rnil      (rφ rnil)     bt refl = bt₂v
bt₂? [] _ _ _ (rφ ra′)  (rφ rnil)     bt ()
bt₂? [] _ _ _ ra        (rφ (rφ w″))  bt ()
bt₂? (tν [])     _ _ _ ra w bt ()
bt₂? (tν (tν s)) _ _ _ ra w bt ()
bt₂? (tν (tφ f [])) _ _ _ ra rnil    bt ()
bt₂? (tν (tφ f [])) _ _ _ ra (rφ w′) bt ()
bt₂? (tν (tφ f (tν s))) _ _ _ ra w bt eq =
  ⊥-elim (++ᵗ-tν≢[] s (tν-inj (proj₂ (tφ-inj (tν-inj eq)))))
bt₂? (tν (tφ f (tφ g s))) _ _ _ ra w bt ()
bt₂? (tφ f s)             _ _ _ ra w bt ()

------------------------------------------------------------------------
-- The reachability invariant, closed under `~ᵇ₁` in both directions.
------------------------------------------------------------------------

Inv : NF 0 → Set
Inv N = (Σ[ es ∈ List (Tm 5) ] (N ≡ mkNF T₁ᵗ es) × OkA es)
      ⊎ (Σ[ es ∈ List (Tm 5) ] (N ≡ mkNF T₂ᵗ es) × OkB es)

step : ∀ {N N′ : NF 0} → N ~ᵇ₁ N′ → Inv N → Inv N′
step (ν1ᵇ s t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with ν1V₁? s t tEq
...   | v₁-out = inj₁ (map (_⋯ fA₁) es , refl , okA-fA₁ es (subst OkA (sym esEq) ok))
...   | v₁-in  = inj₁ (map (_⋯ fB₁) es , refl , okA-fB₁ es (subst OkA (sym esEq) ok))
step (ν1ᵇ s t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with ν1V₂? s t tEq
...   | v₂-out = inj₂ (map (_⋯ fA₂) es , refl , okB-fA₂ es (subst OkB (sym esEq) ok))
...   | v₂-in  = inj₂ (map (_⋯ fB₂) es , refl , okB-fB₂ es (subst OkB (sym esEq) ok))
step (φφᵇ s x y t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq = ⊥-elim (φφ¬₁ s x y t tEq)
step (φφᵇ s x y t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq = ⊥-elim (φφ¬₂ s x y t tEq)
step (thrᵇ t {es} {es′} p) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₁ (es′ , cong (λ u → mkNF u es′) tEq , ok4-thr p (subst OkA (sym esEq) ok))
step (thrᵇ t {es} {es′} p) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₂ (es′ , cong (λ u → mkNF u es′) tEq , ok4-thr p (subst OkB (sym esEq) ok))
step (delᵇ t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₁ (es , cong (λ u → mkNF u es) tEq , subst OkA (sym esEq) ok)
step (delᵇ t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₂ (es , cong (λ u → mkNF u es) tEq , subst OkB (sym esEq) ok)
step (bswpᵇ s {a} ra {rb} w {t} bt es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with bs₁? s a rb t ra w bt tEq
...   | bs₁ with w
...     | rφ rnil = inj₂ (map (_⋯ σ₁₂) es , refl , okA-σ₁₂ es (subst OkA (sym esEq) ok))
step (bswpᵇ s {a} ra {rb} w {t} bt es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with bs₂? s a rb t ra w bt tEq
...   | bs₂ with w
...     | rnil = inj₁ (map (_⋯ σ₂₁) es , refl , okB-σ₂₁ es (subst OkB (sym esEq) ok))

step⁻ : ∀ {N N′ : NF 0} → N ~ᵇ₁ N′ → Inv N′ → Inv N
step⁻ (ν1ᵇ s t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with ν1V₁? s t tEq
...   | v₁-out = inj₁ (es , refl , okA-fA₁⁻ es (subst OkA (sym esEq) ok))
...   | v₁-in  = inj₁ (es , refl , okA-fB₁⁻ es (subst OkA (sym esEq) ok))
step⁻ (ν1ᵇ s t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with ν1V₂? s t tEq
...   | v₂-out = inj₂ (es , refl , okB-fA₂⁻ es (subst OkB (sym esEq) ok))
...   | v₂-in  = inj₂ (es , refl , okB-fB₂⁻ es (subst OkB (sym esEq) ok))
step⁻ (φφᵇ s x y t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq = ⊥-elim (φφ¬₁ s y x t tEq)
step⁻ (φφᵇ s x y t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq = ⊥-elim (φφ¬₂ s y x t tEq)
step⁻ (thrᵇ t {es} {es′} p) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₁ (es , cong (λ u → mkNF u es) tEq , ok4-thr (↭-sym p) (subst OkA (sym esEq) ok))
step⁻ (thrᵇ t {es} {es′} p) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₂ (es , cong (λ u → mkNF u es) tEq , ok4-thr (↭-sym p) (subst OkB (sym esEq) ok))
step⁻ (delᵇ t es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₁ (K `unit ∷ es , cong (λ u → mkNF u (K `unit ∷ es)) tEq ,
        subst OkA (sym esEq) ok)
step⁻ (delᵇ t es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq =
  inj₂ (K `unit ∷ es , cong (λ u → mkNF u (K `unit ∷ es)) tEq ,
        subst OkB (sym esEq) ok)
step⁻ (bswpᵇ s {a} ra {rb} w {t} bt es) (inj₁ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with bt₁? s a rb t ra w bt tEq
...   | bt₁v with w | ra
...     | rnil | rφ rnil = inj₂ (es , refl , okA-σ₂₁⁻ es (subst OkA (sym esEq) ok))
step⁻ (bswpᵇ s {a} ra {rb} w {t} bt es) (inj₂ (es₀ , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with bt₂? s a rb t ra w bt tEq
...   | bt₂v with w | ra
...     | rφ rnil | rnil = inj₁ (es , refl , okB-σ₁₂⁻ es (subst OkB (sym esEq) ok))

chain : ∀ {N N′ : NF 0} → N ~ᵇ N′ → Inv N → Inv N′
chain ε           i = i
chain (fwd g ◅ c) i = chain c (step g i)
chain (bwd g ◅ c) i = chain c (step⁻ g i)

------------------------------------------------------------------------
-- The counterexample, and the refutation.
------------------------------------------------------------------------

N₁ N₂ : NF 0
N₁ = mkNF T₁ᵗ (e₀ ∷ [])
N₂ = mkNF T₂ᵗ ((e₀ ⋯ assocSwapᵣ 1 2) ∷ [])

-- One perm-νφ at prefix `tν []` relates the two block forms.
rel : N₁ ~ N₂
rel = Eq*.return (perm-νφ (tν []) drop [] (e₀ ∷ []))

invN₁ : Inv N₁
invN₁ = inj₁ ((e₀ ∷ []) , refl , inj₁ refl)

¬invN₂ : Inv N₂ → ⊥
¬invN₂ (inj₁ (es , eq , ok)) with NF-inv eq
... | refl , () , esEq
¬invN₂ (inj₂ (es , eq , ok)) with NF-inv eq
... | refl , tEq , esEq with subst OkB (sym esEq) ok
...   | inj₁ ()
...   | inj₂ (inj₁ ())
...   | inj₂ (inj₂ (inj₁ ()))
...   | inj₂ (inj₂ (inj₂ ()))

-- The refutation: no `~ᵇ` chain can join N₁ to N₂, yet N₁ ~ N₂ and both are
-- block forms.  Hence `BlockBridge` is false.
¬N₁~ᵇN₂ : N₁ ~ᵇ N₂ → ⊥
¬N₁~ᵇN₂ c = ¬invN₂ (chain c invN₁)

blockBridge-refuted : BlockBridge → ⊥
blockBridge-refuted bridge = ¬N₁~ᵇN₂ (bridge bν bν rel)
