-- | Coherence probe for Normal.Realise's stated-open hypotheses.
--
--   RESULT (machine-checked): the three `Set`s `BswpThreadCoh`,
--   `BswpThreadCohᵇ` and `FlipResidue` are UNINHABITABLE as stated.
--
--   Why.  Each statement quantifies over BOTH a positional decomposition of
--   the normal form (`s`/`v`, resp. `s`/`a`/`rb`/`t′`) AND a typed telescope
--   decomposition (`u`/`G₁`/`G₂`/…), related only by the record equality
--   `eq : mkNF … ≡ ImageOf … `.  That equality does NOT tie the two
--   decompositions to the SAME node: a telescope with two ν blocks admits a
--   `(s , v)` split at the second block while `(u , G₁ , G₂ , t₀)` names the
--   first.  On such a misaligned instance the conclusion relates a flip/swap
--   of one node to the image of a flip/swap of ANOTHER node, which fails:
--
--     * for the two `BswpThreadCoh`s the conclusion is a list equality whose
--       two sides normalise to lists mentioning DIFFERENT variables
--       (`` ` 4F `` versus `` ` 2F `` below) — refuted by an absurd match;
--     * for `FlipResidue` the conclusion is a `~ᵩ`; on a φ-free telescope a
--       `~ᵩ` chain can only permute threads and insert/delete spent units, so
--       the ℕ-valued observable `Σw` below is invariant — and it computes to
--       `1` on the left and `0` on the right.
--
--   At their call sites (`realise-bswp`, `realise-flip`) the two
--   decompositions ARE aligned: `locate-1` returns `pre≡ : BShape u ≡ shape s`
--   (and the `φν-split` run identifications), but `Realise` drops these before
--   invoking the hypotheses.  The intended coherences are the statements WITH
--   that alignment data added; as stated, they are false.
module BorrowedCF.Simulation.Support.Normal.RealiseCoh where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed using (BindGroup)
open import BorrowedCF.Simulation.Support.TypedPrenex using (TTel; []ᵗ; tνᵗ)
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; []; tν; tφ; _++ᵗ_; NF; mkNF; tel; thr)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
  using (Run; rnil; Block; bnil;
         _~ᵩ_; _~ᵩ₁_; φφᵩ; νφᵩ; thrᵩ; delᵩ; φcountᵗ; φcountᵗ-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (Bσ)
open import BorrowedCF.Simulation.Support.Normal.Realise
  using (BswpThreadCoh; BswpThreadCohᵇ; FlipResidue; ImageOf)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_) renaming (refl to ↭refl; prep to ↭prep; swap to ↭swap; trans to ↭tr)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

open Fin.Patterns

------------------------------------------------------------------------
-- A `~ᵩ`-invariant observable on φ-free normal forms.
--
--   `w` reads the data-channel variable out of a channel-triple-shaped
--   thread; `Σw` sums it over the thread list.  On a telescope with no φ
--   cells the two φ generators cannot fire (their both sides contain a
--   `tφ`), so a `~ᵩ` chain is thread permutation + unit insertion/deletion
--   only — and both preserve `Σw`.
------------------------------------------------------------------------

w[_] : ∀ {k} → Tm k → ℕ
w[ (e₁ ⊗ (` x)) ⊗ e₂ ] = Fin.toℕ x
w[ e ]                 = 0

Σw : ∀ {k} → List (Tm k) → ℕ
Σw []       = 0
Σw (e ∷ es) = w[ e ] + Σw es

Σw-↭ : ∀ {k} {es es′ : List (Tm k)} → es ↭ es′ → Σw es ≡ Σw es′
Σw-↭ ↭refl = refl
Σw-↭ (↭prep x p) = cong (w[ x ] +_) (Σw-↭ p)
Σw-↭ (↭swap {xs = xs} {ys = ys} x y p) =
  sym (+-assoc w[ x ] w[ y ] (Σw xs))
    ■ cong (_+ Σw xs) (Nat.+-comm w[ x ] w[ y ])
    ■ +-assoc w[ y ] w[ x ] (Σw xs)
    ■ cong (λ z → w[ y ] + (w[ x ] + z)) (Σw-↭ p)
Σw-↭ (↭tr p q) = Σw-↭ p ■ Σw-↭ q

private
  noφ : ∀ m n {A : Set} → m + suc n ≡ 0 → A
  noφ zero    n ()
  noφ (suc m) n ()

Σw-step : ∀ {n} {N M : NF n} → SymClosure _~ᵩ₁_ N M → φcountᵗ (tel N) ≡ 0 →
          (φcountᵗ (tel M) ≡ 0) × (Σw (thr N) ≡ Σw (thr M))
Σw-step (fwd (φφᵩ s x y t es)) z =
  noφ (φcountᵗ s) (suc (φcountᵗ t)) (sym (φcountᵗ-++ᵗ s (tφ x (tφ y t))) ■ z)
Σw-step (fwd (νφᵩ s x t es))   z =
  noφ (φcountᵗ s) (φcountᵗ t) (sym (φcountᵗ-++ᵗ s (tν (tφ x t))) ■ z)
Σw-step (fwd (thrᵩ t p))       z = z , Σw-↭ p
Σw-step (fwd (delᵩ t es))      z = z , refl
Σw-step (bwd (φφᵩ s x y t es)) z =
  noφ (φcountᵗ s) (suc (φcountᵗ t)) (sym (φcountᵗ-++ᵗ s (tφ y (tφ x t))) ■ z)
Σw-step (bwd (νφᵩ s x t es))   z =
  noφ (φcountᵗ s) (φcountᵗ t) (sym (φcountᵗ-++ᵗ s (tφ x (tν t))) ■ z)
Σw-step (bwd (thrᵩ t p))       z = z , sym (Σw-↭ p)
Σw-step (bwd (delᵩ t es))      z = z , refl

Σw-~ᵩ : ∀ {n} {N M : NF n} → N ~ᵩ M → φcountᵗ (tel N) ≡ 0 →
        Σw (thr N) ≡ Σw (thr M)
Σw-~ᵩ ε       _ = refl
Σw-~ᵩ (g ◅ c) z with Σw-step g z
... | z′ , e = e ■ Σw-~ᵩ c z′

------------------------------------------------------------------------
-- The misaligned instances.
--
--   All bind groups are the singleton `1 ∷ []` (sum 1, no syncs), so every
--   node's block is a bare `tν` and every index is a numeral: the image data
--   below is definitionally equal to its `ImageOf`, and `eq := refl`.
------------------------------------------------------------------------

private
  σ₀ : 0 →ₛ 0
  σ₀ ()

  B₁ : BindGroup
  B₁ = 1 ∷ []

  -- Two-node source for the flip; misaligned split: `s = tν []` places the
  -- flipped ν at the SECOND (inner) node, `u = []ᵗ` names the FIRST.
  tF : TTel 2 4
  tF = tνᵗ B₁ B₁ []ᵗ

  esF : List (Tm 4)
  esF = ` 0F ∷ []

  es₁F : List (Tm 4)
  es₁F = map (_⋯ Bσ (tνᵗ B₁ B₁ tF) σ₀) esF ++ (K `unit ∷ [])

  -- Three-node source for the block swaps; misaligned split: `s = tν []`
  -- places the swapped pair at nodes (2,3), `u = []ᵗ` names the pair (1,2).
  tS : TTel 4 6
  tS = tνᵗ B₁ B₁ []ᵗ

  esS : List (Tm 6)
  esS = ` 4F ∷ []

  es₁S : List (Tm 6)
  es₁S = map (_⋯ Bσ (tνᵗ B₁ B₁ (tνᵗ B₁ B₁ tS)) σ₀) esS ++ (K `unit ∷ [])

------------------------------------------------------------------------
-- The refutations.
------------------------------------------------------------------------

bswpThreadCoh-⊥ : BswpThreadCoh → ⊥
bswpThreadCoh-⊥ coh
  with coh []ᵗ B₁ B₁ B₁ B₁ tS esS σ₀ (tν []) [] rnil rnil [] bnil es₁S refl refl
... | ()

bswpThreadCohᵇ-⊥ : BswpThreadCohᵇ → ⊥
bswpThreadCohᵇ-⊥ coh
  with coh []ᵗ B₁ B₁ B₁ B₁ tS esS σ₀ (tν []) [] rnil rnil [] bnil es₁S refl refl
... | ()

flipResidue-⊥ : FlipResidue → ⊥
flipResidue-⊥ fl
  with Σw-~ᵩ (fl []ᵗ B₁ B₁ tF esF σ₀ (tν []) [] es₁F refl) refl
... | ()
