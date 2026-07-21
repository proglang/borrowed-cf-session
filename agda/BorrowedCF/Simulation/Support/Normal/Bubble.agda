-- | Moving a binder INWARDS past a telescope.
--
--   `combine` (Normal.Norm) is asymmetric: the SECOND argument's telescope ends
--   up outermost.  Extruding a binder out of the second argument is therefore an
--   outright equality (Normal.Sound's `combine-ν` / `combine-φ`); extruding one
--   out of the FIRST argument has to move that binder across the whole of the
--   second telescope, and that is only true up to `~`.
--
--   This module builds that move.  `bubbleν` / `bubbleφ` fire one adjacent
--   transposition per binder of the prefix telescope, so the composite renaming
--   is a concrete `liftId u (bubν s)` rather than an existential — which is what
--   the assembly needs, since both sides' thread lists are already determined.
module BorrowedCF.Simulation.Support.Normal.Bubble where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift
open import BorrowedCF.Simulation.Support.Normal.Endo
  using (liftId-id; liftId-liftRen; wkTel-idᵗ; renTel-idᵗ; ++ᵗ-idʳ)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; map-fuse; map-++ᴸ; liftRen-cong)

open import Data.List using (List; []; _∷_; _++_; map)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- The block transpositions, pointwise on names.
------------------------------------------------------------------------

-- `assocSwapᵣ a b` sends the first `a` names past the next `b` ones.  Every law
-- below is the interaction of one such block swap with a weakening, at the two
-- concrete block sizes the calculus uses (2 for a `ν`, 1 for a `φ`).

aswap22-wk : ∀ {n} (x : 𝔽 (2 + n)) →
             assocSwapᵣ 2 2 (weaken* ⦃ Kᵣ ⦄ 2 x) ≡ (weaken* ⦃ Kᵣ ⦄ 2 ↑* 2) x
aswap22-wk zero           = refl
aswap22-wk (suc zero)     = refl
aswap22-wk (suc (suc x))  = refl

aswap12-wk : ∀ {n} (x : 𝔽 (2 + n)) →
             assocSwapᵣ 1 2 (weaken* ⦃ Kᵣ ⦄ 1 x) ≡ (weaken* ⦃ Kᵣ ⦄ 1 ↑* 2) x
aswap12-wk zero           = refl
aswap12-wk (suc zero)     = refl
aswap12-wk (suc (suc x))  = refl

aswap22-lift : ∀ {n} (x : 𝔽 (2 + n)) →
               assocSwapᵣ 2 2 ((weaken* ⦃ Kᵣ ⦄ 2 {n} ↑* 2) x) ≡ weaken* ⦃ Kᵣ ⦄ 2 x
aswap22-lift zero           = refl
aswap22-lift (suc zero)     = refl
aswap22-lift (suc (suc x))  = refl

aswap12-lift : ∀ {n} (x : 𝔽 (1 + n)) →
               assocSwapᵣ 1 2 ((weaken* ⦃ Kᵣ ⦄ 2 {n} ↑* 1) x) ≡ weaken* ⦃ Kᵣ ⦄ 2 x
aswap12-lift zero     = refl
aswap12-lift (suc x)  = refl

aswap21-wk : ∀ {n} (x : 𝔽 (1 + n)) →
             assocSwapᵣ 2 1 (weaken* ⦃ Kᵣ ⦄ 2 x) ≡ (weaken* ⦃ Kᵣ ⦄ 2 ↑* 1) x
aswap21-wk zero     = refl
aswap21-wk (suc x)  = refl

aswap11-wk : ∀ {n} (x : 𝔽 (1 + n)) →
             assocSwapᵣ 1 1 (weaken* ⦃ Kᵣ ⦄ 1 x) ≡ (weaken* ⦃ Kᵣ ⦄ 1 ↑* 1) x
aswap11-wk zero     = refl
aswap11-wk (suc x)  = refl

aswap21-lift : ∀ {n} (x : 𝔽 (2 + n)) →
               assocSwapᵣ 2 1 ((weaken* ⦃ Kᵣ ⦄ 1 {n} ↑* 2) x) ≡ weaken* ⦃ Kᵣ ⦄ 1 x
aswap21-lift zero           = refl
aswap21-lift (suc zero)     = refl
aswap21-lift (suc (suc x))  = refl

aswap11-lift : ∀ {n} (x : 𝔽 (1 + n)) →
               assocSwapᵣ 1 1 ((weaken* ⦃ Kᵣ ⦄ 1 {n} ↑* 1) x) ≡ weaken* ⦃ Kᵣ ⦄ 1 x
aswap11-lift zero     = refl
aswap11-lift (suc x)  = refl

-- `assocSwapᵣ 2 1` is what undoes the νφ transposition — the one generator that
-- has to be used backwards (a `ν` inside the prefix of a `φ` bubble).
aswap-21-12 : ∀ {n} (x : 𝔽 (2 + (1 + n))) → assocSwapᵣ 1 2 (assocSwapᵣ 2 1 x) ≡ x
aswap-21-12 zero                  = refl
aswap-21-12 (suc zero)            = refl
aswap-21-12 (suc (suc zero))      = refl
aswap-21-12 (suc (suc (suc x)))   = refl

------------------------------------------------------------------------
-- The transport-free `liftRen` for a fixed scope shift.
------------------------------------------------------------------------

-- `liftRen t (weaken* 2)` lands in `innerOf t (2 + n)`; `liftRen2` lands in
-- `2 + k` directly, exactly as `shift2` does for the telescope itself.
liftRen2 : ∀ {n k} (t : Tel n k) → (n →ᵣ 2 + n) → k →ᵣ 2 + k
liftRen2 []       ρ = ρ
liftRen2 (tν t)   ρ = liftRen2 t (ρ ↑* 2)
liftRen2 (tφ _ t) ρ = liftRen2 t (ρ ↑)

liftRen1 : ∀ {n k} (t : Tel n k) → (n →ᵣ 1 + n) → k →ᵣ 1 + k
liftRen1 []       ρ = ρ
liftRen1 (tν t)   ρ = liftRen1 t (ρ ↑* 2)
liftRen1 (tφ _ t) ρ = liftRen1 t (ρ ↑)

liftRen2-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ 2 + n} →
                ρ₁ ≗ ρ₂ → liftRen2 t ρ₁ ≗ liftRen2 t ρ₂
liftRen2-cong []       eq = eq
liftRen2-cong (tν t)   eq = liftRen2-cong t (eq ~↑* 2)
liftRen2-cong (tφ f t) eq = liftRen2-cong t (eq ~↑)

liftRen1-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ 1 + n} →
                ρ₁ ≗ ρ₂ → liftRen1 t ρ₁ ≗ liftRen1 t ρ₂
liftRen1-cong []       eq = eq
liftRen1-cong (tν t)   eq = liftRen1-cong t (eq ~↑* 2)
liftRen1-cong (tφ f t) eq = liftRen1-cong t (eq ~↑)

-- The reconciliation, mirroring `shift2-renTel`.
liftRen2-liftRen : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 2 + n) (x : 𝔽 k) →
                   subst 𝔽 (shift2-innerOf t) (liftRen t ρ x) ≡ liftRen2 t ρ x
liftRen2-liftRen []       ρ x = refl
liftRen2-liftRen (tν t)   ρ x = liftRen2-liftRen t (ρ ↑* 2) x
liftRen2-liftRen (tφ f t) ρ x = liftRen2-liftRen t (ρ ↑)    x

liftRen1-liftRen : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 1 + n) (x : 𝔽 k) →
                   subst 𝔽 (shift1-innerOf t) (liftRen t ρ x) ≡ liftRen1 t ρ x
liftRen1-liftRen []       ρ x = refl
liftRen1-liftRen (tν t)   ρ x = liftRen1-liftRen t (ρ ↑* 2) x
liftRen1-liftRen (tφ f t) ρ x = liftRen1-liftRen t (ρ ↑)    x

-- Fusing an endo pushed under `shift2 t` into the shifted lift.
liftId-liftRen2 : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 2 + n) (σ : 2 + n →ᵣ 2 + n) (x : 𝔽 k) →
                  liftId (shift2 t) σ (liftRen2 t ρ x) ≡ liftRen2 t (ρ ·ₖ σ) x
liftId-liftRen2 []       ρ σ x = refl
liftId-liftRen2 (tν t)   ρ σ x =
  liftId-liftRen2 t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen2-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-liftRen2 (tφ f t) ρ σ x =
  liftId-liftRen2 t (ρ ↑) (σ ↑) x
    ■ liftRen2-cong t (λ y → sym (dist-↑-· ρ σ y)) x

liftId-liftRen1 : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 1 + n) (σ : 1 + n →ᵣ 1 + n) (x : 𝔽 k) →
                  liftId (shift1 t) σ (liftRen1 t ρ x) ≡ liftRen1 t (ρ ·ₖ σ) x
liftId-liftRen1 []       ρ σ x = refl
liftId-liftRen1 (tν t)   ρ σ x =
  liftId-liftRen1 t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen1-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-liftRen1 (tφ f t) ρ σ x =
  liftId-liftRen1 t (ρ ↑) (σ ↑) x
    ■ liftRen1-cong t (λ y → sym (dist-↑-· ρ σ y)) x

-- `liftId` after `liftRen` is a single `liftRen`: the re-based telescope is
-- exactly what lets the two lifts meet, with no transport (cf. Normal.Nat's
-- `liftRen-·`, which needs one because it re-bases twice).
liftId-liftRen-· : ∀ {n k b} (t : Tel n k) (ρ : n →ᵣ b) (σ : b →ᵣ b) (x : 𝔽 k) →
                   liftId (renTel t b) σ (liftRen t ρ x) ≡ liftRen t (ρ ·ₖ σ) x
liftId-liftRen-· []       ρ σ x = refl
liftId-liftRen-· (tν t)   ρ σ x =
  liftId-liftRen-· t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-liftRen-· (tφ f t) ρ σ x =
  liftId-liftRen-· t (ρ ↑) (σ ↑) x
    ■ liftRen-cong t (λ y → sym (dist-↑-· ρ σ y)) x

------------------------------------------------------------------------
-- Thread-list plumbing.
------------------------------------------------------------------------

≡→~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ N₂
≡→~ refl = ~-refl

map-⋯-cong : ∀ {a b} {σ σ′ : a →ᵣ b} → σ ≗ σ′ → (es : List (Tm a)) →
             map (_⋯ σ) es ≡ map (_⋯ σ′) es
map-⋯-cong eq []       = refl
map-⋯-cong eq (e ∷ es) = cong₂ _∷_ (⋯-cong e eq) (map-⋯-cong eq es)

map-⋯-id : ∀ {a} {σ : a →ᵣ a} → σ ≗ idₖ ⦃ Kᵣ ⦄ → (es : List (Tm a)) →
           map (_⋯ σ) es ≡ es
map-⋯-id eq []       = refl
map-⋯-id eq (e ∷ es) = cong₂ _∷_ (⋯-id e eq) (map-⋯-id eq es)

------------------------------------------------------------------------
-- The composite renaming a bubble produces.
------------------------------------------------------------------------

-- One transposition per binder of the prefix, each pushed under the prefix's own
-- tail by `liftId` — so `bubν` does not mention the telescope `u` the bubble
-- travels into, and the two characterisations below are statements about `s`
-- alone.
bubν : ∀ {n j} → Tel n j → 2 + j →ᵣ 2 + j
bubν []       = idₖ ⦃ Kᵣ ⦄
bubν (tν s)   = liftId (shift2 s) (assocSwapᵣ 2 2) ·ₖ bubν s
bubν (tφ f s) = liftId (shift2 s) (assocSwapᵣ 1 2) ·ₖ bubν s

bubφ : ∀ {n j} → Tel n j → 1 + j →ᵣ 1 + j
bubφ []       = idₖ ⦃ Kᵣ ⦄
bubφ (tν s)   = liftId (shift1 s) (assocSwapᵣ 2 1) ·ₖ bubφ s
bubφ (tφ f s) = liftId (shift1 s) (assocSwapᵣ 1 1) ·ₖ bubφ s

------------------------------------------------------------------------
-- Bubbling a binder inwards.
------------------------------------------------------------------------

bubbleν : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (es : List (Tm k)) →
          mkNF (tν (shift2 s ++ᵗ u)) es ~ mkNF (s ++ᵗ tν u) (map (_⋯ liftId u (bubν s)) es)

bubbleν [] u es = ≡→~ (cong (mkNF (tν u)) (sym (map-⋯-id (liftId-id u (λ _ → refl)) es)))

bubbleν (tν s) u es =
  ~-trans (Eq*.return (perm-νν [] (shift2 s ++ᵗ u) es))
    (~-trans (~-νNF (bubbleν s u (map (_⋯ liftId (shift2 s ++ᵗ u) (assocSwapᵣ 2 2)) es)))
             (≡→~ (cong (mkNF (tν (s ++ᵗ tν u)))
                        ( map-fuse (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 2 2))
                                   (liftId u (bubν s)) es
                        ■ map-⋯-cong fuse es ))))
  where
    fuse : ∀ x → liftId u (bubν s) (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 2 2) x)
                   ≡ liftId u (bubν (tν s)) x
    fuse x = cong (liftId u (bubν s)) (liftId-++ᵗ (shift2 s) u (assocSwapᵣ 2 2) x)
               ■ liftId-· u (liftId (shift2 s) (assocSwapᵣ 2 2)) (bubν s) x

bubbleν (tφ f s) u es =
  ~-trans (Eq*.return (perm-νφ [] f (shift2 s ++ᵗ u) es))
    (~-trans (~-φNF (bubbleν s u (map (_⋯ liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2)) es)))
             (≡→~ (cong (mkNF (tφ f (s ++ᵗ tν u)))
                        ( map-fuse (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2))
                                   (liftId u (bubν s)) es
                        ■ map-⋯-cong fuse es ))))
  where
    fuse : ∀ x → liftId u (bubν s) (liftId (shift2 s ++ᵗ u) (assocSwapᵣ 1 2) x)
                   ≡ liftId u (bubν (tφ f s)) x
    fuse x = cong (liftId u (bubν s)) (liftId-++ᵗ (shift2 s) u (assocSwapᵣ 1 2) x)
               ■ liftId-· u (liftId (shift2 s) (assocSwapᵣ 1 2)) (bubν s) x

-- The `tν` case is the only one that runs a generator BACKWARDS: `perm-νφ` only
-- pulls a φ out of a ν, and here a ν has to travel out of a φ.  `aswap-21-12`
-- is what supplies the inverse renaming.
bubbleφ : ∀ {n j k} (f : Flag) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
          mkNF (tφ f (shift1 s ++ᵗ u)) es ~ mkNF (s ++ᵗ tφ f u) (map (_⋯ liftId u (bubφ s)) es)

bubbleφ f [] u es = ≡→~ (cong (mkNF (tφ f u)) (sym (map-⋯-id (liftId-id u (λ _ → refl)) es)))

bubbleφ f (tν s) u es =
  ~-trans (~-trans (≡→~ (cong (mkNF (tφ f (tν X))) (sym undo)))
                   (~-sym (Eq*.return (perm-νφ [] f X es″))))
    (~-trans (~-νNF (bubbleφ f s u es″))
             (≡→~ (cong (mkNF (tν (s ++ᵗ tφ f u)))
                        ( map-fuse (liftId X (assocSwapᵣ 2 1)) (liftId u (bubφ s)) es
                        ■ map-⋯-cong fuse es ))))
  where
    X : Tel (1 + (2 + _)) _
    X = shift1 s ++ᵗ u

    es″ : List (Tm _)
    es″ = map (_⋯ liftId X (assocSwapᵣ 2 1)) es

    undo : map (_⋯ liftId X (assocSwapᵣ 1 2)) es″ ≡ es
    undo = map-fuse (liftId X (assocSwapᵣ 2 1)) (liftId X (assocSwapᵣ 1 2)) es
             ■ map-⋯-id (λ x → liftId-· X (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) x
                                 ■ liftId-id X aswap-21-12 x) es

    fuse : ∀ x → liftId u (bubφ s) (liftId X (assocSwapᵣ 2 1) x)
                   ≡ liftId u (bubφ (tν s)) x
    fuse x = cong (liftId u (bubφ s)) (liftId-++ᵗ (shift1 s) u (assocSwapᵣ 2 1) x)
               ■ liftId-· u (liftId (shift1 s) (assocSwapᵣ 2 1)) (bubφ s) x

bubbleφ f (tφ g s) u es =
  ~-trans (Eq*.return (perm-φφ [] f g (shift1 s ++ᵗ u) es))
    (~-trans (~-φNF (bubbleφ f s u (map (_⋯ liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1)) es)))
             (≡→~ (cong (mkNF (tφ g (s ++ᵗ tφ f u)))
                        ( map-fuse (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1))
                                   (liftId u (bubφ s)) es
                        ■ map-⋯-cong fuse es ))))
  where
    fuse : ∀ x → liftId u (bubφ s) (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1) x)
                   ≡ liftId u (bubφ (tφ g s)) x
    fuse x = cong (liftId u (bubφ s)) (liftId-++ᵗ (shift1 s) u (assocSwapᵣ 1 1) x)
               ■ liftId-· u (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ s) x
