-- | Moving a binder INWARDS past a telescope.
--
--   `combine` (Normal.Norm) is asymmetric: the SECOND argument's telescope ends
--   up outermost.  Extruding a binder out of the second argument is therefore an
--   outright equality (`combine-ν` / `combine-φ`, below); extruding one out of
--   the FIRST argument has to move that binder across the whole of the second
--   telescope, and that is only true up to `~`.
--
--   This module builds that move.  `bubbleν` / `bubbleφ` fire one adjacent
--   transposition per binder of the prefix telescope, so the composite renaming
--   is a concrete `bubν s` / `bubφ s` rather than an existential.
--
--   LINKED-φ: `shift2` / `shift1` are now the INSERTION RENAMING (they RENAME the
--   telescope's φ-channels), so `shift2 (tν s)` no longer reduces to `tν (shift2
--   s)`; and the four `~₁` generators now RENAME the deep telescope they travel
--   into.  Consequently the bubble's RHS carries a `renTel u (bubν s)` /
--   `liftRen u (bubν s)` renaming, and every proof about `shift2 (…)` is routed
--   through the `subst`/renaming reconciliations (`liftId-subst`, `subst-wkTel`,
--   `subst-tν`/`subst-tφ`) rather than through `shift2`'s (now defunct)
--   structural recursion.
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
  using (liftId-id; renTel-idᵗ; liftId-liftRen; wkTel-++ᵗ; ++ᵗ-assoc)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; map-fuse; map-++ᴸ; liftRen-cong; renTel-cong; map-⋯-subst; subst-++;
         subst-tν; subst-tφ; subst-wkTel; subst-++ᵗ; innerOf-renTel; innerOf-++ᵗ;
         renTel-renTel; renTel-++ᵗ; liftRen-++ᵗ; wkTel-renTel; wkTel-nat; liftRen-·;
         joinSubst; subst-■)

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
-- Pushing a scope transport under `liftId` (linked-φ: `shift2` is subst-wrapped).
------------------------------------------------------------------------

-- `liftId (shift2 t)` is stuck on the `subst` in `shift2`'s definition; this is
-- the by-J lemma that pushes it onto the structural `renTel t (weaken* 2)`.
liftId-subst : ∀ {n k k′} (eq : k ≡ k′) (T : Tel n k) (σ : n →ᵣ n) (x : 𝔽 k) →
               liftId (subst (Tel n) eq T) σ (subst 𝔽 eq x) ≡ subst 𝔽 eq (liftId T σ x)
liftId-subst refl T σ x = refl

------------------------------------------------------------------------
-- The transport-free `liftRen` for a fixed scope shift.
------------------------------------------------------------------------

-- `liftRen t (weaken* 2)` lands in `innerOf t (2 + n)`; `liftRen2` lands in
-- `2 + k` directly, exactly as `shift2` does for the telescope itself.
liftRen2 : ∀ {n k} (t : Tel n k) → (n →ᵣ 2 + n) → k →ᵣ 2 + k
liftRen2 []         ρ = ρ
liftRen2 (tν t)     ρ = liftRen2 t (ρ ↑* 2)
liftRen2 (tφ _ _ t) ρ = liftRen2 t (ρ ↑)

liftRen1 : ∀ {n k} (t : Tel n k) → (n →ᵣ 1 + n) → k →ᵣ 1 + k
liftRen1 []         ρ = ρ
liftRen1 (tν t)     ρ = liftRen1 t (ρ ↑* 2)
liftRen1 (tφ _ _ t) ρ = liftRen1 t (ρ ↑)

liftRen2-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ 2 + n} →
                ρ₁ ≗ ρ₂ → liftRen2 t ρ₁ ≗ liftRen2 t ρ₂
liftRen2-cong []         eq = eq
liftRen2-cong (tν t)     eq = liftRen2-cong t (eq ~↑* 2)
liftRen2-cong (tφ _ _ t) eq = liftRen2-cong t (eq ~↑)

liftRen1-cong : ∀ {n k} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ 1 + n} →
                ρ₁ ≗ ρ₂ → liftRen1 t ρ₁ ≗ liftRen1 t ρ₂
liftRen1-cong []         eq = eq
liftRen1-cong (tν t)     eq = liftRen1-cong t (eq ~↑* 2)
liftRen1-cong (tφ _ _ t) eq = liftRen1-cong t (eq ~↑)

-- The reconciliation, mirroring `shift2-renTel`.
liftRen2-liftRen : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 2 + n) (x : 𝔽 k) →
                   subst 𝔽 (shift2-innerOf t) (liftRen t ρ x) ≡ liftRen2 t ρ x
liftRen2-liftRen []         ρ x = refl
liftRen2-liftRen (tν t)     ρ x = liftRen2-liftRen t (ρ ↑* 2) x
liftRen2-liftRen (tφ _ _ t) ρ x = liftRen2-liftRen t (ρ ↑)    x

liftRen1-liftRen : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 1 + n) (x : 𝔽 k) →
                   subst 𝔽 (shift1-innerOf t) (liftRen t ρ x) ≡ liftRen1 t ρ x
liftRen1-liftRen []         ρ x = refl
liftRen1-liftRen (tν t)     ρ x = liftRen1-liftRen t (ρ ↑* 2) x
liftRen1-liftRen (tφ _ _ t) ρ x = liftRen1-liftRen t (ρ ↑)    x

-- `liftId (renTel t ρ₀) σ` reads only the SHAPE of `renTel t ρ₀`, so the
-- re-basing renaming `ρ₀` and the lifted renaming `ρ` are independent.  This is
-- `liftId-liftRen-·` with the two decoupled, needed because `shift2`'s
-- `weaken* 2` differs from the `liftRen2`'s renaming.
liftId-renTel-liftRen : ∀ {n k b} (t : Tel n k) (ρ₀ ρ : n →ᵣ b) (σ : b →ᵣ b) (x : 𝔽 k) →
                        liftId (renTel t ρ₀) σ (liftRen t ρ x) ≡ liftRen t (ρ ·ₖ σ) x
liftId-renTel-liftRen []         ρ₀ ρ σ x = refl
liftId-renTel-liftRen (tν t)     ρ₀ ρ σ x =
  liftId-renTel-liftRen t (ρ₀ ↑* 2) (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-renTel-liftRen (tφ _ _ t) ρ₀ ρ σ x =
  liftId-renTel-liftRen t (ρ₀ ↑) (ρ ↑) (σ ↑) x
    ■ liftRen-cong t (λ y → sym (dist-↑-· ρ σ y)) x

-- Fusing an endo pushed under `shift2 t` into the shifted lift.  Routed through
-- `liftId-subst` because `liftId (shift2 t)` is stuck on `shift2`'s `subst`.
liftId-liftRen2 : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 2 + n) (σ : 2 + n →ᵣ 2 + n) (x : 𝔽 k) →
                  liftId (shift2 t) σ (liftRen2 t ρ x) ≡ liftRen2 t (ρ ·ₖ σ) x
liftId-liftRen2 t ρ σ x =
  cong (liftId (shift2 t) σ) (sym (liftRen2-liftRen t ρ x))
    ■ liftId-subst (shift2-innerOf t) (renTel t (weaken* ⦃ Kᵣ ⦄ 2)) σ (liftRen t ρ x)
    ■ cong (subst 𝔽 (shift2-innerOf t)) (liftId-renTel-liftRen t (weaken* ⦃ Kᵣ ⦄ 2) ρ σ x)
    ■ liftRen2-liftRen t (ρ ·ₖ σ) x

liftId-liftRen1 : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ 1 + n) (σ : 1 + n →ᵣ 1 + n) (x : 𝔽 k) →
                  liftId (shift1 t) σ (liftRen1 t ρ x) ≡ liftRen1 t (ρ ·ₖ σ) x
liftId-liftRen1 t ρ σ x =
  cong (liftId (shift1 t) σ) (sym (liftRen1-liftRen t ρ x))
    ■ liftId-subst (shift1-innerOf t) (renTel t (weaken* ⦃ Kᵣ ⦄ 1)) σ (liftRen t ρ x)
    ■ cong (subst 𝔽 (shift1-innerOf t)) (liftId-renTel-liftRen t (weaken* ⦃ Kᵣ ⦄ 1) ρ σ x)
    ■ liftRen1-liftRen t (ρ ·ₖ σ) x

-- `liftId` after `liftRen` is a single `liftRen`: the re-based telescope is
-- exactly what lets the two lifts meet, with no transport (cf. Normal.Nat's
-- `liftRen-·`, which needs one because it re-bases twice).  `renTel` is now
-- STRUCTURAL, so this ports with only a pattern fix.
liftId-liftRen-· : ∀ {n k b} (t : Tel n k) (ρ : n →ᵣ b) (σ : b →ᵣ b) (x : 𝔽 k) →
                   liftId (renTel t ρ) σ (liftRen t ρ x) ≡ liftRen t (ρ ·ₖ σ) x
liftId-liftRen-· []         ρ σ x = refl
liftId-liftRen-· (tν t)     ρ σ x =
  liftId-liftRen-· t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftId-liftRen-· (tφ _ _ t) ρ σ x =
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
-- tail by `liftId`.
bubν : ∀ {n j} → Tel n j → 2 + j →ᵣ 2 + j
bubν []         = idₖ ⦃ Kᵣ ⦄
bubν (tν s)     = liftId (shift2 s) (assocSwapᵣ 2 2) ·ₖ bubν s
bubν (tφ _ _ s) = liftId (shift2 s) (assocSwapᵣ 1 2) ·ₖ bubν s

bubφ : ∀ {n j} → Tel n j → 1 + j →ᵣ 1 + j
bubφ []         = idₖ ⦃ Kᵣ ⦄
bubφ (tν s)     = liftId (shift1 s) (assocSwapᵣ 2 1) ·ₖ bubφ s
bubφ (tφ _ _ s) = liftId (shift1 s) (assocSwapᵣ 1 1) ·ₖ bubφ s

------------------------------------------------------------------------
-- `subst` on a telescope's inner index, pushed through `++ᵗ` / `renTel` (J).
------------------------------------------------------------------------

-- Moving an inner-index transport from the LEFT operand of `++ᵗ` to the right.
subst-++ᵗˡ : ∀ {n a b k} (eq : a ≡ b) (T : Tel n a) (u : Tel b k) →
             subst (Tel n) eq T ++ᵗ u ≡ T ++ᵗ subst (λ z → Tel z k) (sym eq) u
subst-++ᵗˡ refl T u = refl

-- `innerOf` reads only the shape, so an inner-index transport does not change it.
innerOf-substⁱ : ∀ {n k k′} (eq : k ≡ k′) (T : Tel n k) (m : ℕ) →
                 innerOf (subst (Tel n) eq T) m ≡ innerOf T m
innerOf-substⁱ refl T m = refl

-- `renTel` commutes with an inner-index transport.
renTel-substⁱ : ∀ {n k k′ m} (eq : k ≡ k′) (T : Tel n k) (ρ : n →ᵣ m) →
                subst (Tel m) (innerOf-substⁱ eq T m) (renTel (subst (Tel n) eq T) ρ) ≡ renTel T ρ
renTel-substⁱ refl T ρ = refl

-- `liftRen` commutes with an inner-index transport (pointwise).
liftRen-substⁱ : ∀ {n k k′ m} (eq : k ≡ k′) (T : Tel n k) (ρ : n →ᵣ m) (x : 𝔽 k′) →
                 subst 𝔽 (innerOf-substⁱ eq T m) (liftRen (subst (Tel n) eq T) ρ x)
                   ≡ liftRen T ρ (subst 𝔽 (sym eq) x)
liftRen-substⁱ refl T ρ x = refl

------------------------------------------------------------------------
-- The insertion renaming, generalised over the inserted renaming.
------------------------------------------------------------------------

-- `shift2` inserts `weaken* 2`; the bubble induction needs the SAME clean index
-- for an ARBITRARY inserted renaming, because firing a `~₁` generator threads a
-- lifted swap into it.  `shiftBy2 (weaken* 2) = shift2` definitionally, and —
-- crucially — `shiftBy2 ρ (tν s) = tν (shiftBy2 (ρ ↑* 2) s)` (which `shift2`
-- itself does NOT satisfy).
shiftBy2 : ∀ {n j} → (n →ᵣ 2 + n) → Tel n j → Tel (2 + n) (2 + j)
shiftBy2 {n} ρ s = subst (Tel (2 + n)) (shift2-innerOf s) (renTel s ρ)

shiftBy1 : ∀ {n j} → (n →ᵣ 1 + n) → Tel n j → Tel (1 + n) (1 + j)
shiftBy1 {n} ρ s = subst (Tel (1 + n)) (shift1-innerOf s) (renTel s ρ)

shiftBy2-tν : ∀ {n j} (ρ : n →ᵣ 2 + n) (s : Tel (2 + n) j) →
              shiftBy2 ρ (tν s) ≡ tν (shiftBy2 (ρ ↑* 2) s)
shiftBy2-tν ρ s = subst-tν (shift2-innerOf s) (renTel s (ρ ↑* 2))

shiftBy2-tφ : ∀ {n j} (ρ : n →ᵣ 2 + n) (f : Flag) (c : Tm n) (s : Tel (1 + n) j) →
              shiftBy2 ρ (tφ f c s) ≡ tφ f (c ⋯ ρ) (shiftBy2 (ρ ↑) s)
shiftBy2-tφ ρ f c s = subst-tφ (shift2-innerOf s) f (c ⋯ ρ) (renTel s (ρ ↑))

shiftBy1-tν : ∀ {n j} (ρ : n →ᵣ 1 + n) (s : Tel (2 + n) j) →
              shiftBy1 ρ (tν s) ≡ tν (shiftBy1 (ρ ↑* 2) s)
shiftBy1-tν ρ s = subst-tν (shift1-innerOf s) (renTel s (ρ ↑* 2))

shiftBy1-tφ : ∀ {n j} (ρ : n →ᵣ 1 + n) (f : Flag) (c : Tm n) (s : Tel (1 + n) j) →
              shiftBy1 ρ (tφ f c s) ≡ tφ f (c ⋯ ρ) (shiftBy1 (ρ ↑) s)
shiftBy1-tφ ρ f c s = subst-tφ (shift1-innerOf s) f (c ⋯ ρ) (renTel s (ρ ↑))

shift2≡shiftBy2 : ∀ {n j} (s : Tel n j) → shift2 s ≡ shiftBy2 (weaken* ⦃ Kᵣ ⦄ 2) s
shift2≡shiftBy2 s = refl

shift1≡shiftBy1 : ∀ {n j} (s : Tel n j) → shift1 s ≡ shiftBy1 (weaken* ⦃ Kᵣ ⦄ 1) s
shift1≡shiftBy1 s = refl

------------------------------------------------------------------------
-- Transport bookkeeping for the bubble induction.
------------------------------------------------------------------------

-- `liftId (renTel s ρ)` reads only the SHAPE of `renTel s ρ`.
liftId-renTel-cong : ∀ {n k m} (s : Tel n k) (ρ₀ ρ₁ : n →ᵣ m) (σ : m →ᵣ m) →
                     liftId (renTel s ρ₀) σ ≗ liftId (renTel s ρ₁) σ
liftId-renTel-cong []         ρ₀ ρ₁ σ x = refl
liftId-renTel-cong (tν s)     ρ₀ ρ₁ σ x = liftId-renTel-cong s (ρ₀ ↑* 2) (ρ₁ ↑* 2) (σ ↑* 2) x
liftId-renTel-cong (tφ _ _ s) ρ₀ ρ₁ σ x = liftId-renTel-cong s (ρ₀ ↑) (ρ₁ ↑) (σ ↑) x

-- Moving an inner-index transport out of a `liftRen` (the thread analogue of
-- `telMidᴺ`), by J.
liftMid : ∀ {c d a b} (eq : a ≡ b) (t : Tel c d) {ρ : c →ᵣ a} {ρ′ : c →ᵣ b} →
          (∀ y → subst 𝔽 eq (ρ y) ≡ ρ′ y) →
          ∀ x → subst 𝔽 (cong (innerOf t) eq) (liftRen t ρ x) ≡ liftRen t ρ′ x
liftMid refl t h x = liftRen-cong t h x

-- Moving a MID inner-index transport across a `++ᵗ`, by J.
telMidᴺ : ∀ {n m m′ c d} (p : m ≡ m′) (A : Tel n m) (u : Tel c d)
          {ρ : c →ᵣ m} {ρ′ : c →ᵣ m′} → (∀ y → subst 𝔽 p (ρ y) ≡ ρ′ y) →
          subst (Tel n) (cong (innerOf u) p) (A ++ᵗ renTel u ρ)
            ≡ subst (Tel n) p A ++ᵗ renTel u ρ′
telMidᴺ refl A u hρ = cong (A ++ᵗ_) (renTel-cong u hρ)

-- Moving an inner-index transport out of a `wkTel ∘ renTel`, by J.
wkMidᴺ : ∀ {c d m m′} (p : m ≡ m′) (t : Tel c d)
         {ρ : c →ᵣ m} {ρ′ : c →ᵣ m′} (hρ : ∀ w → subst 𝔽 p (ρ w) ≡ ρ′ w) (y : 𝔽 m) →
         subst 𝔽 (cong (innerOf t) p) (wkTel (renTel t ρ) y)
           ≡ wkTel (renTel t ρ′) (subst 𝔽 p y)
wkMidᴺ refl t hρ y = cong (λ T → wkTel T y) (renTel-cong t hρ)

------------------------------------------------------------------------
-- Bubbling a binder inwards.
------------------------------------------------------------------------

bubbleν : ∀ {n j k} (s : Tel n j) (u : Tel (2 + j) k) (es : List (Tm k)) →
          mkNF (tν (shift2 s ++ᵗ u)) es
            ~ mkNF (s ++ᵗ tν (renTel u (bubν s))) (map (_⋯ liftRen u (bubν s)) es)
bubbleν [] u es =
  ~-sym (≡→~ (NF-≡ (renTel-id u)
    ( subst-tν (renTel-id u) (renTel u (idₖ ⦃ Kᵣ ⦄)) ■ cong tν (renTel-idᵗ u) )
    ( map-⋯-subst (renTel-id u)
        (λ x → liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x ■ liftId-id u (λ _ → refl) x) es
    ■ map-⋯-id (λ _ → refl) es )))
bubbleν {n} {j} (tν s) u es =
  ~-trans (≡→~ eqA)
    (~-trans (Eq*.return (perm-νν [] (Y ++ᵗ u) es))
      (~-trans (≡→~ eqB)
        (~-trans (~-νNF (bubbleν s u-rec es-rec)) (≡→~ eqC))))
  where
    w2 : n →ᵣ 2 + n
    w2 = weaken* ⦃ Kᵣ ⦄ 2
    sh : innerOf s (2 + (2 + n)) ≡ 2 + j
    sh = shift2-innerOf s
    Y : Tel (2 + (2 + n)) (2 + j)
    Y = subst (Tel (2 + (2 + n))) sh (renTel s (w2 ↑* 2))
    u-rec : Tel (2 + j) (innerOf u (2 + j))
    u-rec = renTel u (liftId (shift2 s) (assocSwapᵣ 2 2))
    es-rec : List (Tm (innerOf u (2 + j)))
    es-rec = map (_⋯ liftRen u (liftId (shift2 s) (assocSwapᵣ 2 2))) es
    eqk : innerOf (Y ++ᵗ u) (2 + (2 + n)) ≡ innerOf u (2 + j)
    eqk = innerOf-++ᵗ Y u (2 + (2 + n)) ■ cong (innerOf u) (renTel-id Y)
    eqA : mkNF (tν (shift2 (tν s) ++ᵗ u)) es ≡ mkNF (tν (tν (Y ++ᵗ u))) es
    eqA = cong (λ T → mkNF (tν T) es) (cong (_++ᵗ u) (subst-tν sh (renTel s (w2 ↑* 2))))
    -- the swap `renTel Y (assocSwapᵣ 2 2)` re-bases `s` back down to `shift2 s`.
    a₀ : innerOf Y (2 + (2 + n)) ≡ innerOf (renTel s (w2 ↑* 2)) (2 + (2 + n))
    a₀ = innerOf-substⁱ sh (renTel s (w2 ↑* 2)) (2 + (2 + n))
    b₀ : innerOf (renTel s (w2 ↑* 2)) (2 + (2 + n)) ≡ innerOf s (2 + (2 + n))
    b₀ = innerOf-renTel s (w2 ↑* 2) (2 + (2 + n))
    pY : innerOf Y (2 + (2 + n)) ≡ 2 + j
    pY = a₀ ■ b₀ ■ sh
    P1 : subst (Tel (2 + (2 + n))) pY (renTel Y (assocSwapᵣ 2 2)) ≡ shift2 s
    P1 = subst-■ (Tel (2 + (2 + n))) a₀ (b₀ ■ sh) (renTel Y (assocSwapᵣ 2 2))
           ■ cong (subst (Tel (2 + (2 + n))) (b₀ ■ sh))
                  (renTel-substⁱ sh (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2))
           ■ subst-■ (Tel (2 + (2 + n))) b₀ sh (renTel (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2))
           ■ cong (subst (Tel (2 + (2 + n))) sh) (renTel-renTel s (w2 ↑* 2) (assocSwapᵣ 2 2))
           ■ cong (subst (Tel (2 + (2 + n))) sh) (renTel-cong s aswap22-lift)
    P1′ : subst (Tel (2 + (2 + n))) (renTel-id Y) (renTel Y (assocSwapᵣ 2 2)) ≡ shift2 s
    P1′ = cong (λ p → subst (Tel (2 + (2 + n))) p (renTel Y (assocSwapᵣ 2 2)))
               (≡-irrelevant (renTel-id Y) pY)
            ■ P1
    P2 : ∀ z → subst 𝔽 pY (liftRen Y (assocSwapᵣ 2 2) z) ≡ liftId (shift2 s) (assocSwapᵣ 2 2) z
    P2 z =
      subst-■ 𝔽 a₀ (b₀ ■ sh) (liftRen Y (assocSwapᵣ 2 2) z)
        ■ cong (subst 𝔽 (b₀ ■ sh)) (liftRen-substⁱ sh (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2) z)
        ■ subst-■ 𝔽 b₀ sh (liftRen (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2) (subst 𝔽 (sym sh) z))
        ■ cong (subst 𝔽 sh)
            ( cong (λ p → subst 𝔽 p (liftRen (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2) (subst 𝔽 (sym sh) z)))
                   (≡-irrelevant b₀ (renTel-id (renTel s (w2 ↑* 2))))
            ■ liftId-liftRen (renTel s (w2 ↑* 2)) (assocSwapᵣ 2 2) (subst 𝔽 (sym sh) z)
            ■ liftId-renTel-cong s (w2 ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2) (assocSwapᵣ 2 2) (subst 𝔽 (sym sh) z) )
        ■ sym (liftId-subst sh (renTel s (weaken* ⦃ Kᵣ ⦄ 2)) (assocSwapᵣ 2 2) (subst 𝔽 (sym sh) z))
        ■ cong (liftId (shift2 s) (assocSwapᵣ 2 2)) (subst-subst-sym sh)
    hρ′ : ∀ z → subst 𝔽 (renTel-id Y) (liftRen Y (assocSwapᵣ 2 2) z)
                ≡ liftId (shift2 s) (assocSwapᵣ 2 2) z
    hρ′ z = cong (λ p → subst 𝔽 p (liftRen Y (assocSwapᵣ 2 2) z)) (≡-irrelevant (renTel-id Y) pY)
              ■ P2 z
    deepRecon : subst (Tel (2 + (2 + n))) eqk (renTel (Y ++ᵗ u) (assocSwapᵣ 2 2))
                  ≡ shift2 s ++ᵗ u-rec
    deepRecon =
      subst-■ (Tel (2 + (2 + n))) (innerOf-++ᵗ Y u (2 + (2 + n))) (cong (innerOf u) (renTel-id Y))
              (renTel (Y ++ᵗ u) (assocSwapᵣ 2 2))
        ■ cong (subst (Tel (2 + (2 + n))) (cong (innerOf u) (renTel-id Y)))
               (renTel-++ᵗ Y u (assocSwapᵣ 2 2))
        ■ telMidᴺ (renTel-id Y) (renTel Y (assocSwapᵣ 2 2)) u hρ′
        ■ cong (_++ᵗ u-rec) P1′
    hthrB : ∀ y → subst 𝔽 eqk (liftRen (Y ++ᵗ u) (assocSwapᵣ 2 2) y)
                  ≡ liftRen u (liftId (shift2 s) (assocSwapᵣ 2 2)) y
    hthrB y =
      subst-■ 𝔽 (innerOf-++ᵗ Y u (2 + (2 + n))) (cong (innerOf u) (renTel-id Y))
              (liftRen (Y ++ᵗ u) (assocSwapᵣ 2 2) y)
        ■ cong (subst 𝔽 (cong (innerOf u) (renTel-id Y)))
               (liftRen-++ᵗ Y u (assocSwapᵣ 2 2) y)
        ■ liftMid (renTel-id Y) u hρ′ y
    eqB : mkNF (tν (tν (renTel (Y ++ᵗ u) (assocSwapᵣ 2 2))))
                 (map (_⋯ liftRen (Y ++ᵗ u) (assocSwapᵣ 2 2)) es)
            ≡ mkNF (tν (tν (shift2 s ++ᵗ u-rec))) es-rec
    eqB = NF-≡ eqk
            ( subst-tν eqk (tν (renTel (Y ++ᵗ u) (assocSwapᵣ 2 2)))
            ■ cong tν ( subst-tν eqk (renTel (Y ++ᵗ u) (assocSwapᵣ 2 2))
                      ■ cong tν deepRecon ) )
            ( map-⋯-subst eqk hthrB es )
    eqCinner : innerOf (renTel u (liftId (shift2 s) (assocSwapᵣ 2 2))) (2 + j) ≡ innerOf u (2 + j)
    eqCinner = innerOf-renTel u (liftId (shift2 s) (assocSwapᵣ 2 2)) (2 + j)
    deepReconC : subst (Tel (2 + j)) eqCinner (renTel u-rec (bubν s)) ≡ renTel u (bubν (tν s))
    deepReconC = renTel-renTel u (liftId (shift2 s) (assocSwapᵣ 2 2)) (bubν s)
    eqC : mkNF (tν (s ++ᵗ tν (renTel u-rec (bubν s)))) (map (_⋯ liftRen u-rec (bubν s)) es-rec)
            ≡ mkNF (tν s ++ᵗ tν (renTel u (bubν (tν s)))) (map (_⋯ liftRen u (bubν (tν s))) es)
    eqC = NF-≡ eqCinner
            ( subst-tν eqCinner (s ++ᵗ tν (renTel u-rec (bubν s)))
            ■ cong tν ( subst-++ᵗ s eqCinner (tν (renTel u-rec (bubν s)))
                      ■ cong (s ++ᵗ_) ( subst-tν eqCinner (renTel u-rec (bubν s))
                                      ■ cong tν deepReconC ) ) )
            ( cong (subst (λ z → List (Tm z)) eqCinner)
                   (map-fuse (liftRen u (liftId (shift2 s) (assocSwapᵣ 2 2)))
                             (liftRen u-rec (bubν s)) es)
            ■ map-⋯-subst eqCinner (liftRen-· u (liftId (shift2 s) (assocSwapᵣ 2 2)) (bubν s)) es )
bubbleν {n} {j} (tφ f c s) u es =
  ~-trans (≡→~ eqA)
    (~-trans (Eq*.return (perm-νφ [] f c (Y ++ᵗ u) es))
      (~-trans (≡→~ eqB)
        (~-trans (~-φNF c (bubbleν s u-rec es-rec)) (≡→~ eqC))))
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

bubbleφ : ∀ {n j k} (f : Flag) (c : Tm n) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
          mkNF (tφ f c (shift1 s ++ᵗ u)) es
            ~ mkNF (s ++ᵗ tφ f (c ⋯ wkTel s) (renTel u (bubφ s))) (map (_⋯ liftRen u (bubφ s)) es)
bubbleφ f c [] u es =
  ~-sym (≡→~ (NF-≡ (renTel-id u)
    ( subst-tφ (renTel-id u) f (c ⋯ idₖ ⦃ Kᵣ ⦄) (renTel u (idₖ ⦃ Kᵣ ⦄))
    ■ cong₂ (tφ f) (⋯-id c (λ _ → refl)) (renTel-idᵗ u) )
    ( map-⋯-subst (renTel-id u)
        (λ x → liftId-liftRen u (idₖ ⦃ Kᵣ ⦄) x ■ liftId-id u (λ _ → refl) x) es
    ■ map-⋯-id (λ _ → refl) es )))
bubbleφ {n} {j} f c (tφ g d s) u es =
  ~-trans (≡→~ eqA)
    (~-trans (Eq*.return (perm-φφ [] f g c d (Y ++ᵗ u) es))
      (~-trans (≡→~ eqB)
        (~-trans (~-φNF d (bubbleφ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) s u-rec es-rec)) (≡→~ eqC))))
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
bubbleφ f c (tν s) u es = ?

------------------------------------------------------------------------
-- Shape congruences and `wkTel ∘ shift·` bridges (linked-φ).
------------------------------------------------------------------------

-- `wkTel (renTel s ρ)` reads only the SHAPE of `renTel s ρ`, hence is
-- independent of the re-basing renaming `ρ`.
wkTel-renTel-cong : ∀ {n k m} (s : Tel n k) (ρ₀ ρ₁ : n →ᵣ m) →
                    wkTel (renTel s ρ₀) ≗ wkTel (renTel s ρ₁)
wkTel-renTel-cong []         ρ₀ ρ₁ x = refl
wkTel-renTel-cong (tν s)     ρ₀ ρ₁ x =
  wkTel-renTel-cong s (ρ₀ ↑* 2) (ρ₁ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-renTel-cong (tφ _ _ s) ρ₀ ρ₁ x =
  wkTel-renTel-cong s (ρ₀ ↑) (ρ₁ ↑) (weaken* ⦃ Kᵣ ⦄ 1 x)

-- `shift2 (tν s)` no longer reduces to `tν (shift2 s)`, but its WEAKENING does
-- agree with `shift2 s`'s (weakening reads shape only): both re-base `s`.
wkTel-shift2-tν : ∀ {n j} (s : Tel (2 + n) j) (x : 𝔽 (2 + n)) →
                  wkTel (shift2 (tν s)) x ≡ wkTel (shift2 s) (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-shift2-tν s x =
  sym (subst-wkTel (shift2-innerOf s) (tν (renTel s (weaken* ⦃ Kᵣ ⦄ 2 ↑* 2))) x)
    ■ cong (subst 𝔽 (shift2-innerOf s))
           (wkTel-renTel-cong s (weaken* ⦃ Kᵣ ⦄ 2 ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 2 x))
    ■ subst-wkTel (shift2-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 2)) (weaken* ⦃ Kᵣ ⦄ 2 x)

wkTel-shift2-tφ : ∀ {n j} (f : Flag) (c : Tm n) (s : Tel (1 + n) j) (x : 𝔽 (2 + n)) →
                  wkTel (shift2 (tφ f c s)) x ≡ wkTel (shift2 s) (weaken* ⦃ Kᵣ ⦄ 1 x)
wkTel-shift2-tφ f c s x =
  sym (subst-wkTel (shift2-innerOf s) (tφ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) (renTel s (weaken* ⦃ Kᵣ ⦄ 2 ↑))) x)
    ■ cong (subst 𝔽 (shift2-innerOf s))
           (wkTel-renTel-cong s (weaken* ⦃ Kᵣ ⦄ 2 ↑) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1 x))
    ■ subst-wkTel (shift2-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 2)) (weaken* ⦃ Kᵣ ⦄ 1 x)

wkTel-shift1-tν : ∀ {n j} (s : Tel (2 + n) j) (x : 𝔽 (1 + n)) →
                  wkTel (shift1 (tν s)) x ≡ wkTel (shift1 s) (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-shift1-tν s x =
  sym (subst-wkTel (shift1-innerOf s) (tν (renTel s (weaken* ⦃ Kᵣ ⦄ 1 ↑* 2))) x)
    ■ cong (subst 𝔽 (shift1-innerOf s))
           (wkTel-renTel-cong s (weaken* ⦃ Kᵣ ⦄ 1 ↑* 2) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 2 x))
    ■ subst-wkTel (shift1-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 1)) (weaken* ⦃ Kᵣ ⦄ 2 x)

wkTel-shift1-tφ : ∀ {n j} (f : Flag) (c : Tm n) (s : Tel (1 + n) j) (x : 𝔽 (1 + n)) →
                  wkTel (shift1 (tφ f c s)) x ≡ wkTel (shift1 s) (weaken* ⦃ Kᵣ ⦄ 1 x)
wkTel-shift1-tφ f c s x =
  sym (subst-wkTel (shift1-innerOf s) (tφ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel s (weaken* ⦃ Kᵣ ⦄ 1 ↑))) x)
    ■ cong (subst 𝔽 (shift1-innerOf s))
           (wkTel-renTel-cong s (weaken* ⦃ Kᵣ ⦄ 1 ↑) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 1 x))
    ■ subst-wkTel (shift1-innerOf s) (renTel s (weaken* ⦃ Kᵣ ⦄ 1)) (weaken* ⦃ Kᵣ ⦄ 1 x)

------------------------------------------------------------------------
-- What the bubble renaming does.
------------------------------------------------------------------------

-- Two facts, and exactly the two the extrusion needs: on names weakened in from
-- the base, `bubν s` is the base weakening lifted past the ν; on the ν's own two
-- names it is the weakening that puts them back at the front.

bubν-wkTel : ∀ {n j} (s : Tel n j) (x : 𝔽 (2 + n)) →
             bubν s (wkTel (shift2 s) x) ≡ (wkTel s ↑* 2) x
bubν-wkTel []         x = sym (id↑* 2 (λ _ → refl) x)
bubν-wkTel (tν s)     x =
  cong (bubν s) ( cong (liftId (shift2 s) (assocSwapᵣ 2 2)) (wkTel-shift2-tν s x)
                ■ liftId-wkTel (shift2 s) (assocSwapᵣ 2 2) (weaken* ⦃ Kᵣ ⦄ 2 x) )
    ■ bubν-wkTel s (assocSwapᵣ 2 2 (weaken* ⦃ Kᵣ ⦄ 2 x))
    ■ cong (wkTel s ↑* 2) (aswap22-wk x)
    ■ sym (dist-↑*-· 2 (weaken* ⦃ Kᵣ ⦄ 2) (wkTel s) x)
bubν-wkTel (tφ f c s) x =
  cong (bubν s) ( cong (liftId (shift2 s) (assocSwapᵣ 1 2)) (wkTel-shift2-tφ f c s x)
                ■ liftId-wkTel (shift2 s) (assocSwapᵣ 1 2) (weaken* ⦃ Kᵣ ⦄ 1 x) )
    ■ bubν-wkTel s (assocSwapᵣ 1 2 (weaken* ⦃ Kᵣ ⦄ 1 x))
    ■ cong (wkTel s ↑* 2) (aswap12-wk x)
    ■ sym (dist-↑*-· 2 (weaken* ⦃ Kᵣ ⦄ 1) (wkTel s) x)

bubν-liftRen2 : ∀ {n j} (s : Tel n j) (x : 𝔽 j) →
                bubν s (liftRen2 s (weaken* ⦃ Kᵣ ⦄ 2) x) ≡ weaken* ⦃ Kᵣ ⦄ 2 x
bubν-liftRen2 []         x = refl
bubν-liftRen2 (tν s)     x =
  cong (bubν s) ( liftId-liftRen2 s (weaken* ⦃ Kᵣ ⦄ 2 ↑* 2) (assocSwapᵣ 2 2) x
                ■ liftRen2-cong s aswap22-lift x )
    ■ bubν-liftRen2 s x
bubν-liftRen2 (tφ f c s) x =
  cong (bubν s) ( liftId-liftRen2 s (weaken* ⦃ Kᵣ ⦄ 2 ↑* 1) (assocSwapᵣ 1 2) x
                ■ liftRen2-cong s aswap12-lift x )
    ■ bubν-liftRen2 s x

bubφ-wkTel : ∀ {n j} (s : Tel n j) (x : 𝔽 (1 + n)) →
             bubφ s (wkTel (shift1 s) x) ≡ (wkTel s ↑* 1) x
bubφ-wkTel []         x = sym (id↑* 1 (λ _ → refl) x)
bubφ-wkTel (tν s)     x =
  cong (bubφ s) ( cong (liftId (shift1 s) (assocSwapᵣ 2 1)) (wkTel-shift1-tν s x)
                ■ liftId-wkTel (shift1 s) (assocSwapᵣ 2 1) (weaken* ⦃ Kᵣ ⦄ 2 x) )
    ■ bubφ-wkTel s (assocSwapᵣ 2 1 (weaken* ⦃ Kᵣ ⦄ 2 x))
    ■ cong (wkTel s ↑* 1) (aswap21-wk x)
    ■ sym (dist-↑*-· 1 (weaken* ⦃ Kᵣ ⦄ 2) (wkTel s) x)
bubφ-wkTel (tφ f c s) x =
  cong (bubφ s) ( cong (liftId (shift1 s) (assocSwapᵣ 1 1)) (wkTel-shift1-tφ f c s x)
                ■ liftId-wkTel (shift1 s) (assocSwapᵣ 1 1) (weaken* ⦃ Kᵣ ⦄ 1 x) )
    ■ bubφ-wkTel s (assocSwapᵣ 1 1 (weaken* ⦃ Kᵣ ⦄ 1 x))
    ■ cong (wkTel s ↑* 1) (aswap11-wk x)
    ■ sym (dist-↑*-· 1 (weaken* ⦃ Kᵣ ⦄ 1) (wkTel s) x)

bubφ-liftRen1 : ∀ {n j} (s : Tel n j) (x : 𝔽 j) →
                bubφ s (liftRen1 s (weaken* ⦃ Kᵣ ⦄ 1) x) ≡ weaken* ⦃ Kᵣ ⦄ 1 x
bubφ-liftRen1 []         x = refl
bubφ-liftRen1 (tν s)     x =
  cong (bubφ s) ( liftId-liftRen1 s (weaken* ⦃ Kᵣ ⦄ 1 ↑* 2) (assocSwapᵣ 2 1) x
                ■ liftRen1-cong s aswap21-lift x )
    ■ bubφ-liftRen1 s x
bubφ-liftRen1 (tφ f c s) x =
  cong (bubφ s) ( liftId-liftRen1 s (weaken* ⦃ Kᵣ ⦄ 1 ↑* 1) (assocSwapᵣ 1 1) x
                ■ liftRen1-cong s aswap11-lift x )
    ■ bubφ-liftRen1 s x

------------------------------------------------------------------------
-- Extruding a binder out of `combine`'s FIRST argument.
------------------------------------------------------------------------

combine-extrudeˡ-ν : ∀ {n} (N₁ : NF (2 + n)) (N₂ : NF n) →
  combine (νNF N₁) N₂ ~ νNF (combine N₁ (renNF N₂ (2 + n) (weaken* ⦃ Kᵣ ⦄ 2)))
combine-extrudeˡ-ν {n} (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  ~-trans (≡→~ (sym eqL)) (~-trans (~-sym (bubbleν t₂ u E)) (≡→~ (sym eqR)))
  where
    w2 : n →ᵣ 2 + n
    w2 = weaken* ⦃ Kᵣ ⦄ 2
    sh : innerOf t₂ (2 + n) ≡ 2 + j₂
    sh = shift2-innerOf t₂
    u : Tel (2 + j₂) (innerOf t₁ (2 + j₂))
    u = renTel t₁ (wkTel (shift2 t₂))
    E : List (Tm (innerOf t₁ (2 + j₂)))
    E =  map (_⋯ liftRen t₁ (wkTel (shift2 t₂)))    es₁
      ++ map (_⋯ (liftRen2 t₂ w2 ·ₖ wkTel u))       es₂
    -- eqR: the un-bubbled side is `combine` with `t₂` re-based by `w2`.
    h₁ : ∀ x → subst 𝔽 (cong (innerOf t₁) sh)
                 (liftRen t₁ (wkTel (renTel t₂ w2)) x) ≡ liftRen t₁ (wkTel (shift2 t₂)) x
    h₁ = liftMid sh t₁ (λ y → subst-wkTel sh (renTel t₂ w2) y)
    h₂ : ∀ x → subst 𝔽 (cong (innerOf t₁) sh)
                 ((liftRen t₂ w2 ·ₖ wkTel (renTel t₁ (wkTel (renTel t₂ w2)))) x)
                 ≡ (liftRen2 t₂ w2 ·ₖ wkTel u) x
    h₂ x = wkMidᴺ sh t₁ (λ w → subst-wkTel sh (renTel t₂ w2) w) (liftRen t₂ w2 x)
             ■ cong (wkTel u) (liftRen2-liftRen t₂ w2 x)
    eqR : νNF (combine (mkNF t₁ es₁) (renNF (mkNF t₂ es₂) (2 + n) w2))
            ≡ mkNF (tν (shift2 t₂ ++ᵗ u)) E
    eqR = NF-≡ (cong (innerOf t₁) sh)
            ( subst-tν (cong (innerOf t₁) sh) (renTel t₂ w2 ++ᵗ renTel t₁ (wkTel (renTel t₂ w2)))
            ■ cong tν (telMidᴺ sh (renTel t₂ w2) t₁ (λ y → subst-wkTel sh (renTel t₂ w2) y)) )
            ( cong (subst (λ z → List (Tm z)) (cong (innerOf t₁) sh))
                   (cong (map (_⋯ liftRen t₁ (wkTel (renTel t₂ w2))) es₁ ++_)
                         (map-fuse (liftRen t₂ w2)
                                   (wkTel (renTel t₁ (wkTel (renTel t₂ w2)))) es₂))
            ■ subst-++ (cong (innerOf t₁) sh) _ _
            ■ cong₂ _++_ (map-⋯-subst (cong (innerOf t₁) sh) h₁ es₁)
                         (map-⋯-subst (cong (innerOf t₁) sh) h₂ es₂) )
    -- eqL: the bubbled side is `combine (νNF …) …`.
    g₁ : ∀ x → subst 𝔽 (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂))
                 ((liftRen t₁ (wkTel (shift2 t₂)) ·ₖ liftRen u (bubν t₂)) x)
                 ≡ liftRen t₁ (wkTel t₂ ↑* 2) x
    g₁ x = liftRen-· t₁ (wkTel (shift2 t₂)) (bubν t₂) x
             ■ liftRen-cong t₁ (bubν-wkTel t₂) x
    g₂ : ∀ x → subst 𝔽 (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂))
                 (((liftRen2 t₂ w2 ·ₖ wkTel u) ·ₖ liftRen u (bubν t₂)) x)
                 ≡ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ wkTel (renTel t₁ (wkTel t₂ ↑* 2))) x
    g₂ x = cong (subst 𝔽 (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)))
                ( sym (wkTel-nat u (bubν t₂) (liftRen2 t₂ w2 x))
                ■ cong (wkTel (renTel u (bubν t₂))) (bubν-liftRen2 t₂ x) )
             ■ wkTel-renTel t₁ (wkTel (shift2 t₂)) (bubν t₂) (weaken* ⦃ Kᵣ ⦄ 2 x)
             ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 2 x)) (renTel-cong t₁ (bubν-wkTel t₂))
    eqL : mkNF (t₂ ++ᵗ tν (renTel u (bubν t₂))) (map (_⋯ liftRen u (bubν t₂)) E)
            ≡ combine (νNF (mkNF t₁ es₁)) (mkNF t₂ es₂)
    eqL = NF-≡ (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂))
            ( subst-++ᵗ t₂ (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)) (tν (renTel u (bubν t₂)))
            ■ cong (t₂ ++ᵗ_)
                ( subst-tν (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)) (renTel u (bubν t₂))
                ■ cong tν ( renTel-renTel t₁ (wkTel (shift2 t₂)) (bubν t₂)
                          ■ renTel-cong t₁ (bubν-wkTel t₂) ) ) )
            ( cong (subst (λ z → List (Tm z)) (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)))
                   ( map-++ᴸ (liftRen u (bubν t₂))
                       (map (_⋯ liftRen t₁ (wkTel (shift2 t₂))) es₁)
                       (map (_⋯ (liftRen2 t₂ w2 ·ₖ wkTel u)) es₂)
                   ■ cong₂ _++_ (map-fuse (liftRen t₁ (wkTel (shift2 t₂)))
                                          (liftRen u (bubν t₂)) es₁)
                                (map-fuse (liftRen2 t₂ w2 ·ₖ wkTel u)
                                          (liftRen u (bubν t₂)) es₂) )
            ■ subst-++ (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)) _ _
            ■ cong₂ _++_ (map-⋯-subst (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)) g₁ es₁)
                         (map-⋯-subst (innerOf-renTel t₁ (wkTel (shift2 t₂)) (2 + j₂)) g₂ es₂) )

combine-extrudeˡ-φ : ∀ {n} (f : Flag) (c : Tm n) (N₁ : NF (1 + n)) (N₂ : NF n) →
  combine (φNF f c N₁) N₂ ~ φNF f c (combine N₁ (renNF N₂ (1 + n) (weaken* ⦃ Kᵣ ⦄ 1)))
combine-extrudeˡ-φ {n} f c (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  ~-trans (≡→~ (sym eqL)) (~-trans (~-sym (bubbleφ f c t₂ u E)) (≡→~ (sym eqR)))
  where
    w1 : n →ᵣ 1 + n
    w1 = weaken* ⦃ Kᵣ ⦄ 1
    sh : innerOf t₂ (1 + n) ≡ 1 + j₂
    sh = shift1-innerOf t₂
    u : Tel (1 + j₂) (innerOf t₁ (1 + j₂))
    u = renTel t₁ (wkTel (shift1 t₂))
    E : List (Tm (innerOf t₁ (1 + j₂)))
    E =  map (_⋯ liftRen t₁ (wkTel (shift1 t₂)))    es₁
      ++ map (_⋯ (liftRen1 t₂ w1 ·ₖ wkTel u))       es₂
    h₁ : ∀ x → subst 𝔽 (cong (innerOf t₁) sh)
                 (liftRen t₁ (wkTel (renTel t₂ w1)) x) ≡ liftRen t₁ (wkTel (shift1 t₂)) x
    h₁ = liftMid sh t₁ (λ y → subst-wkTel sh (renTel t₂ w1) y)
    h₂ : ∀ x → subst 𝔽 (cong (innerOf t₁) sh)
                 ((liftRen t₂ w1 ·ₖ wkTel (renTel t₁ (wkTel (renTel t₂ w1)))) x)
                 ≡ (liftRen1 t₂ w1 ·ₖ wkTel u) x
    h₂ x = wkMidᴺ sh t₁ (λ w → subst-wkTel sh (renTel t₂ w1) w) (liftRen t₂ w1 x)
             ■ cong (wkTel u) (liftRen1-liftRen t₂ w1 x)
    eqR : φNF f c (combine (mkNF t₁ es₁) (renNF (mkNF t₂ es₂) (1 + n) w1))
            ≡ mkNF (tφ f c (shift1 t₂ ++ᵗ u)) E
    eqR = NF-≡ (cong (innerOf t₁) sh)
            ( subst-tφ (cong (innerOf t₁) sh) f c (renTel t₂ w1 ++ᵗ renTel t₁ (wkTel (renTel t₂ w1)))
            ■ cong (tφ f c) (telMidᴺ sh (renTel t₂ w1) t₁ (λ y → subst-wkTel sh (renTel t₂ w1) y)) )
            ( cong (subst (λ z → List (Tm z)) (cong (innerOf t₁) sh))
                   (cong (map (_⋯ liftRen t₁ (wkTel (renTel t₂ w1))) es₁ ++_)
                         (map-fuse (liftRen t₂ w1)
                                   (wkTel (renTel t₁ (wkTel (renTel t₂ w1)))) es₂))
            ■ subst-++ (cong (innerOf t₁) sh) _ _
            ■ cong₂ _++_ (map-⋯-subst (cong (innerOf t₁) sh) h₁ es₁)
                         (map-⋯-subst (cong (innerOf t₁) sh) h₂ es₂) )
    g₁ : ∀ x → subst 𝔽 (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂))
                 ((liftRen t₁ (wkTel (shift1 t₂)) ·ₖ liftRen u (bubφ t₂)) x)
                 ≡ liftRen t₁ (wkTel t₂ ↑* 1) x
    g₁ x = liftRen-· t₁ (wkTel (shift1 t₂)) (bubφ t₂) x
             ■ liftRen-cong t₁ (bubφ-wkTel t₂) x
    g₂ : ∀ x → subst 𝔽 (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂))
                 (((liftRen1 t₂ w1 ·ₖ wkTel u) ·ₖ liftRen u (bubφ t₂)) x)
                 ≡ (weaken* ⦃ Kᵣ ⦄ 1 ·ₖ wkTel (renTel t₁ (wkTel t₂ ↑* 1))) x
    g₂ x = cong (subst 𝔽 (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)))
                ( sym (wkTel-nat u (bubφ t₂) (liftRen1 t₂ w1 x))
                ■ cong (wkTel (renTel u (bubφ t₂))) (bubφ-liftRen1 t₂ x) )
             ■ wkTel-renTel t₁ (wkTel (shift1 t₂)) (bubφ t₂) (weaken* ⦃ Kᵣ ⦄ 1 x)
             ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 1 x)) (renTel-cong t₁ (bubφ-wkTel t₂))
    eqL : mkNF (t₂ ++ᵗ tφ f (c ⋯ wkTel t₂) (renTel u (bubφ t₂))) (map (_⋯ liftRen u (bubφ t₂)) E)
            ≡ combine (φNF f c (mkNF t₁ es₁)) (mkNF t₂ es₂)
    eqL = NF-≡ (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂))
            ( subst-++ᵗ t₂ (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂))
                       (tφ f (c ⋯ wkTel t₂) (renTel u (bubφ t₂)))
            ■ cong (t₂ ++ᵗ_)
                ( subst-tφ (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)) f (c ⋯ wkTel t₂)
                           (renTel u (bubφ t₂))
                ■ cong (tφ f (c ⋯ wkTel t₂)) ( renTel-renTel t₁ (wkTel (shift1 t₂)) (bubφ t₂)
                                             ■ renTel-cong t₁ (bubφ-wkTel t₂) ) ) )
            ( cong (subst (λ z → List (Tm z)) (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)))
                   ( map-++ᴸ (liftRen u (bubφ t₂))
                       (map (_⋯ liftRen t₁ (wkTel (shift1 t₂))) es₁)
                       (map (_⋯ (liftRen1 t₂ w1 ·ₖ wkTel u)) es₂)
                   ■ cong₂ _++_ (map-fuse (liftRen t₁ (wkTel (shift1 t₂)))
                                          (liftRen u (bubφ t₂)) es₁)
                                (map-fuse (liftRen1 t₂ w1 ·ₖ wkTel u)
                                          (liftRen u (bubφ t₂)) es₂) )
            ■ subst-++ (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)) _ _
            ■ cong₂ _++_ (map-⋯-subst (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)) g₁ es₁)
                         (map-⋯-subst (innerOf-renTel t₁ (wkTel (shift1 t₂)) (1 + j₂)) g₂ es₂) )

------------------------------------------------------------------------
-- Extruding a binder out of `combine`'s SECOND argument.
------------------------------------------------------------------------

-- The easy direction, an outright equality: both sides are `t₂` over `t₁`
-- re-based underneath it, and `renTel-renTel` says it does not matter WHERE `t₁`
-- gets re-based.  (Normal.Sound proves the same two lemmas; it is a consumer of
-- this module, not a dependency, so they are re-proved here.)
combine-ν : ∀ {n} (N₁ : NF n) (N₂ : NF (2 + n)) →
            νNF (combine (renNF N₁ (2 + n) (weaken* ⦃ Kᵣ ⦄ 2)) N₂) ≡ combine N₁ (νNF N₂)
combine-ν {n} (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  NF-≡ e
    ( subst-tν e (t₂ ++ᵗ renTel (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2)) (wkTel t₂))
    ■ cong tν ( subst-++ᵗ t₂ e (renTel (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2)) (wkTel t₂))
              ■ cong (t₂ ++ᵗ_) (renTel-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2) (wkTel t₂)) ) )
    ( cong (subst (λ j → List (Tm j)) e)
           (cong₂ _++_ (map-fuse (liftRen t₁ (weaken* ⦃ Kᵣ ⦄ 2))
                                 (liftRen (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2)) (wkTel t₂)) es₁)
                       refl)
    ■ subst-++ e _ _
    ■ cong₂ _++_ (map-⋯-subst e (liftRen-· t₁ (weaken* ⦃ Kᵣ ⦄ 2) (wkTel t₂)) es₁)
                 (map-⋯-subst e (wkTel-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2) (wkTel t₂)) es₂) )
  where
    e : innerOf (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2)) j₂ ≡ innerOf t₁ j₂
    e = innerOf-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 2) j₂

combine-φ : ∀ {n} (f : Flag) (c : Tm n) (N₁ : NF n) (N₂ : NF (1 + n)) →
            φNF f c (combine (renNF N₁ (1 + n) (weaken* ⦃ Kᵣ ⦄ 1)) N₂) ≡ combine N₁ (φNF f c N₂)
combine-φ {n} f c (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  NF-≡ e
    ( subst-tφ e f c (t₂ ++ᵗ renTel (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1)) (wkTel t₂))
    ■ cong (tφ f c) ( subst-++ᵗ t₂ e (renTel (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1)) (wkTel t₂))
                    ■ cong (t₂ ++ᵗ_) (renTel-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1) (wkTel t₂)) ) )
    ( cong (subst (λ j → List (Tm j)) e)
           (cong₂ _++_ (map-fuse (liftRen t₁ (weaken* ⦃ Kᵣ ⦄ 1))
                                 (liftRen (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1)) (wkTel t₂)) es₁)
                       refl)
    ■ subst-++ e _ _
    ■ cong₂ _++_ (map-⋯-subst e (liftRen-· t₁ (weaken* ⦃ Kᵣ ⦄ 1) (wkTel t₂)) es₁)
                 (map-⋯-subst e (wkTel-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1) (wkTel t₂)) es₂) )
  where
    e : innerOf (renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1)) j₂ ≡ innerOf t₁ j₂
    e = innerOf-renTel t₁ (weaken* ⦃ Kᵣ ⦄ 1) j₂
