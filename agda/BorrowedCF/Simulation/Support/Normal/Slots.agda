-- | Slot tracking for the repaired factorisation (Normal.Factor2).
--
--   `Bridge.blockBridge-refuted` killed the old cut: `blockify` built the
--   middle form from the N side, freezing N's φ-placement and dumping the
--   φ-migration onto `~ᵇ`, which is parity-locked.  The repair pushes the
--   ν-REINDEXING content of a `~` chain to the M side instead.  This module
--   supplies the data for that push:
--
--     * `gapρ a w` — the renaming that transposes two ν pairs separated by
--       the φ-run `a`, fixing the run and everything else.  Defined by
--       recursion on the run as a conjugate of `assocSwapᵣ 2 2` by the
--       νφ-transposition renamings, so it is transport-free and coincides
--       definitionally with `assocSwapᵣ 2 2` at `a = []`.
--     * `Res` — the RESIDUE relation: same telescope, threads renamed by a
--       single pair-flip (`flipᴿ` = `perm-ν1`'s renaming) or a single
--       gap-transposition (`swapᴿ`; at `a = []` this IS `perm-νν`'s
--       renaming).  These are exactly the conjugates of the two ν-reindexing
--       generators under φ-only moves.
--     * `push` / `push⁻` — commute a residue past one `~ᵩ` step: the step
--       fires on the residue's source too, and the residue survives,
--       conjugated.  This is the LOCATE half of the repair: a residue never
--       needs to know more than which ν slots it touches, and φ moves
--       preserve that.
--     * `Cmp`/`cmpᵗ` — the split-comparison view that aligns the residue's
--       telescope decomposition with the step's (the alignment premise the
--       Realise-layer refutation showed is indispensable).
--
--   Consumed by Normal.Factor2: `resolve` pushes a residue down a `~ᵩ`
--   chain and `realise` discharges it against a block form by one `bswpᵇ`
--   (or `ν1ᵇ`), with the run mismatch absorbed by `~ᵩ` — the lesson of the
--   Bridge counterexample, where `[ν][νφ] ~ᵩ [νφ][ν]` directly.
--
--   STATUS: see the OPEN markers (if any) above `push`/`push⁻`.
module BorrowedCF.Simulation.Support.Normal.Slots where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift
  using (liftId-·; liftId-++ᵗ; liftId-cong)
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id; ++ᵗ-assoc)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (map-⋯-cong; map-⋯-id; aswap-21-12)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (aswap-22-inv; aswap-11-inv; aswap-12-21; swap-11-inv)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; renTel-id; innerOf)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (map-fuse; NF-≡; subst-tν; subst-++ᵗ; subst-■; renTel-renTel; renTel-cong; innerOf-renTel;
         map-⋯-subst; liftRen-·; liftRen-cong)
open import BorrowedCF.Simulation.Support.Normal.Endo using (renTel-idᵗ; liftId-liftRen)
open import BorrowedCF.Simulation.Support.Normal.FactorBase

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- Telescope constructor injectivity, and the split-comparison view.
------------------------------------------------------------------------

tν-inj : ∀ {n k} {t₁ t₂ : Tel (2 + n) k} → tν t₁ ≡ tν t₂ → t₁ ≡ t₂
tν-inj refl = refl

tφ-inj₁ : ∀ {n k} {f g : Flag} {c₁ c₂ : Tm n} {t₁ t₂ : Tel (1 + n) k} → tφ f c₁ t₁ ≡ tφ g c₂ t₂ → f ≡ g
tφ-inj₁ refl = refl

tφ-inj-c : ∀ {n k} {f g : Flag} {c₁ c₂ : Tm n} {t₁ t₂ : Tel (1 + n) k} → tφ f c₁ t₁ ≡ tφ g c₂ t₂ → c₁ ≡ c₂
tφ-inj-c refl = refl

tφ-inj₂ : ∀ {n k} {f g : Flag} {c₁ c₂ : Tm n} {t₁ t₂ : Tel (1 + n) k} → tφ f c₁ t₁ ≡ tφ g c₂ t₂ → t₁ ≡ t₂
tφ-inj₂ refl = refl

-- Two splits of one telescope: one split point lies inside the other's
-- suffix, witnessed by the connecting telescope `d` and two equations.
data Cmp {n k} {j₁ j₂} (s₁ : Tel n j₁) (u₁ : Tel j₁ k)
                       (s₂ : Tel n j₂) (u₂ : Tel j₂ k) : Set where
  cmpˡ : (d : Tel j₁ j₂) → s₂ ≡ s₁ ++ᵗ d → u₁ ≡ d ++ᵗ u₂ → Cmp s₁ u₁ s₂ u₂
  cmpʳ : (d : Tel j₂ j₁) → s₁ ≡ s₂ ++ᵗ d → u₂ ≡ d ++ᵗ u₁ → Cmp s₁ u₁ s₂ u₂

cmpᵗ : ∀ {n k j₁ j₂} (s₁ : Tel n j₁) (u₁ : Tel j₁ k) (s₂ : Tel n j₂) (u₂ : Tel j₂ k) →
       s₁ ++ᵗ u₁ ≡ s₂ ++ᵗ u₂ → Cmp s₁ u₁ s₂ u₂
cmpᵗ []        u₁ s₂        u₂ eq = cmpˡ s₂ refl eq
cmpᵗ (tν s₁)   u₁ []        u₂ eq = cmpʳ (tν s₁) refl (sym eq)
cmpᵗ (tφ f c s₁) u₁ []        u₂ eq = cmpʳ (tφ f c s₁) refl (sym eq)
cmpᵗ (tν s₁)   u₁ (tν s₂)   u₂ eq with cmpᵗ s₁ u₁ s₂ u₂ (tν-inj eq)
... | cmpˡ d p q = cmpˡ d (cong tν p) q
... | cmpʳ d p q = cmpʳ d (cong tν p) q
cmpᵗ (tν s₁)   u₁ (tφ g c s₂) u₂ ()
cmpᵗ (tφ f c s₁) u₁ (tν s₂)   u₂ ()
cmpᵗ (tφ f c₁ s₁) u₁ (tφ g c₂ s₂) u₂ eq with tφ-inj₁ eq | tφ-inj-c eq | cmpᵗ s₁ u₁ s₂ u₂ (tφ-inj₂ eq)
... | refl | refl | cmpˡ d p q = cmpˡ d (cong (tφ f c₁) p) q
... | refl | refl | cmpʳ d p q = cmpʳ d (cong (tφ f c₁) p) q

------------------------------------------------------------------------
-- The gap transposition: swap two ν pairs across a φ-run, fixing the run.
------------------------------------------------------------------------

-- At `a = []` this is `assocSwapᵣ 2 2` — `perm-νν`'s renaming — on the
-- nose.  One run cell is peeled per step, as the conjugate by the
-- νφ-transposition renaming at the outer pair (`assocSwapᵣ 1 2` /
-- `assocSwapᵣ 2 1`, mutually inverse by `aswap-12-21`/`aswap-21-12`),
-- exactly as if the cell had first been moved out of the way by `perm-νφ`.
gapρ : ∀ {j i} (a : Tel (2 + j) i) → Run a → 2 + i →ᵣ 2 + i
gapρ []        rnil   = assocSwapᵣ 2 2
gapρ (tφ f c a′) (rφ w) =
  ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) ·ₖ gapρ a′ w) ·ₖ (liftId a′ (assocSwapᵣ 2 1) ↑* 2)

-- The two conjugating pieces are mutually inverse.
private
  peel-inv₁ : ∀ {j i} (a′ : Tel (1 + (2 + j)) i) (z : 𝔽 (2 + i)) →
              (liftId a′ (assocSwapᵣ 1 2) ↑* 2) ((liftId a′ (assocSwapᵣ 2 1) ↑* 2) z) ≡ z
  peel-inv₁ a′ z =
    sym (dist-↑*-· 2 (liftId a′ (assocSwapᵣ 2 1)) (liftId a′ (assocSwapᵣ 1 2)) z)
      ■ id↑* 2 (λ y → liftId-· a′ (assocSwapᵣ 2 1) (assocSwapᵣ 1 2) y
                        ■ liftId-id a′ (λ x → aswap-21-12 x) y) z

  peel-inv₂ : ∀ {j i} (a′ : Tel (1 + (2 + j)) i) (z : 𝔽 (2 + i)) →
              (liftId a′ (assocSwapᵣ 2 1) ↑* 2) ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) z) ≡ z
  peel-inv₂ a′ z =
    sym (dist-↑*-· 2 (liftId a′ (assocSwapᵣ 1 2)) (liftId a′ (assocSwapᵣ 2 1)) z)
      ■ id↑* 2 (λ y → liftId-· a′ (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) y
                        ■ liftId-id a′ (λ x → aswap-12-21 x) y) z

gapρ-invol : ∀ {j i} (a : Tel (2 + j) i) (w : Run a) (x : 𝔽 (2 + i)) →
             gapρ a w (gapρ a w x) ≡ x
gapρ-invol []        rnil   x = aswap-22-inv x
gapρ-invol (tφ f c a′) (rφ w) x =
  cong (λ z → (liftId a′ (assocSwapᵣ 2 1) ↑* 2) (gapρ a′ w z))
       (peel-inv₁ a′ (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x)))
    ■ cong (liftId a′ (assocSwapᵣ 2 1) ↑* 2)
           (gapρ-invol a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
    ■ peel-inv₂ a′ x

------------------------------------------------------------------------
-- Pointwise commutations: head block swaps vs far-lifted endos.
------------------------------------------------------------------------

-- A renaming lifted past the whole window of a block transposition fixes
-- the window pointwise and maps the remainder into itself, so the two
-- commute.  One lemma per (window size, lift depth) the development uses.

comm-↑²-swap11 : ∀ {m} (ζ : m →ᵣ m) (y : 𝔽 (1 + 1 + m)) →
                 swapᵣ 1 1 ((ζ ↑* 2) y) ≡ (ζ ↑* 2) (swapᵣ 1 1 y)
comm-↑²-swap11 ζ zero          = refl
comm-↑²-swap11 ζ (suc zero)    = refl
comm-↑²-swap11 ζ (suc (suc y)) = refl

comm-↑²-aswap11 : ∀ {m} (ζ : m →ᵣ m) (y : 𝔽 (1 + (1 + m))) →
                  assocSwapᵣ 1 1 ((ζ ↑* 2) y) ≡ (ζ ↑* 2) (assocSwapᵣ 1 1 y)
comm-↑²-aswap11 ζ zero          = refl
comm-↑²-aswap11 ζ (suc zero)    = refl
comm-↑²-aswap11 ζ (suc (suc y)) = refl

comm-↑³-aswap12 : ∀ {m} (ζ : m →ᵣ m) (y : 𝔽 (1 + (2 + m))) →
                  assocSwapᵣ 1 2 ((ζ ↑* 3) y) ≡ (ζ ↑* 3) (assocSwapᵣ 1 2 y)
comm-↑³-aswap12 ζ zero                = refl
comm-↑³-aswap12 ζ (suc zero)          = refl
comm-↑³-aswap12 ζ (suc (suc zero))    = refl
comm-↑³-aswap12 ζ (suc (suc (suc y))) = refl

comm-↑³-aswap21 : ∀ {m} (ζ : m →ᵣ m) (y : 𝔽 (2 + (1 + m))) →
                  assocSwapᵣ 2 1 ((ζ ↑* 3) y) ≡ (ζ ↑* 3) (assocSwapᵣ 2 1 y)
comm-↑³-aswap21 ζ zero                = refl
comm-↑³-aswap21 ζ (suc zero)          = refl
comm-↑³-aswap21 ζ (suc (suc zero))    = refl
comm-↑³-aswap21 ζ (suc (suc (suc y))) = refl

comm-↑⁴-aswap22 : ∀ {m} (ζ : m →ᵣ m) (y : 𝔽 (2 + (2 + m))) →
                  assocSwapᵣ 2 2 ((ζ ↑* 4) y) ≡ (ζ ↑* 4) (assocSwapᵣ 2 2 y)
comm-↑⁴-aswap22 ζ zero                      = refl
comm-↑⁴-aswap22 ζ (suc zero)                = refl
comm-↑⁴-aswap22 ζ (suc (suc zero))          = refl
comm-↑⁴-aswap22 ζ (suc (suc (suc zero)))    = refl
comm-↑⁴-aswap22 ζ (suc (suc (suc (suc y)))) = refl

-- The generic two-lift commutation: two endos on the same base that
-- commute pointwise still commute after `liftId` under a shared telescope
-- and a further two-name lift.
comm-lift² : ∀ {b i} (X : Tel b i) (ρ σ : b →ᵣ b) → (∀ z → σ (ρ z) ≡ ρ (σ z)) →
             ∀ (v : 𝔽 (2 + i)) →
             ((liftId X ρ) ↑* 2) (((liftId X σ) ↑* 2) v)
               ≡ ((liftId X σ) ↑* 2) (((liftId X ρ) ↑* 2) v)
comm-lift² X ρ σ h v =
  sym (dist-↑*-· 2 (liftId X σ) (liftId X ρ) v)
    ■ (pw ~↑* 2) v
    ■ dist-↑*-· 2 (liftId X ρ) (liftId X σ) v
  where
    pw : (liftId X σ ·ₖ liftId X ρ) ≗ (liftId X ρ ·ₖ liftId X σ)
    pw z = liftId-· X σ ρ z
             ■ liftId-cong X (λ y → sym (h y)) z
             ■ sym (liftId-· X ρ σ z)

------------------------------------------------------------------------
-- Run plumbing.
------------------------------------------------------------------------

run-++⁻ˡ : ∀ {n m k} (X : Tel n m) {Y : Tel m k} → Run (X ++ᵗ Y) → Run X
run-++⁻ˡ []       w      = rnil
run-++⁻ˡ (tφ f c X) (rφ w) = rφ (run-++⁻ˡ X w)

run-++⁻ʳ : ∀ {n m k} (X : Tel n m) {Y : Tel m k} → Run (X ++ᵗ Y) → Run Y
run-++⁻ʳ []       w      = w
run-++⁻ʳ (tφ f c X) (rφ w) = run-++⁻ʳ X w

run-++ : ∀ {n m k} {X : Tel n m} {Y : Tel m k} → Run X → Run Y → Run (X ++ᵗ Y)
run-++ rnil   wY = wY
run-++ (rφ w) wY = rφ (run-++ w wY)

------------------------------------------------------------------------
-- The residue relation: what is left of a ν-reindexing generator after
-- arbitrarily many φ-only moves have passed over it.
------------------------------------------------------------------------

-- The indices stay ABSTRACT (`T`, `es`, `es′`) and the constructor carries
-- the defining equations: pattern matching a residue against a `~ᵩ₁`
-- generator must unify the two telescope decompositions, and with baked
-- indices that unification is stuck on `_++ᵗ_`.  The equations feed `cmpᵗ`
-- instead — the alignment data the commutation cases consume.
data Res {n} : NF n → NF n → Set where

  -- swap the two names of one ν pair  (= perm-ν1, closed under φ moves).
  -- Linked-φ: the codomain carries the ν-reindexing `renTel t (swapᵣ 1 1)`.
  flipᴿ : ∀ {j k} (s : Tel n j) (t : Tel (2 + j) k)
          {T : Tel n k} {es : List (Tm k)} →
          T ≡ s ++ᵗ tν t →
          Res (mkNF T es)
              (mkNF (s ++ᵗ tν (renTel t (swapᵣ 1 1))) (map (_⋯ liftRen t (swapᵣ 1 1)) es))

  -- transpose two ν pairs separated by the run `a`, fixing the run
  -- (= perm-νν at `a = []`, and its conjugates under φ moves otherwise).
  swapᴿ : ∀ {j i k} (s : Tel n j) {a : Tel (2 + j) i} (w : Run a)
          (t : Tel (2 + i) k) {T : Tel n k} {es : List (Tm k)} →
          T ≡ s ++ᵗ tν (a ++ᵗ tν t) →
          Res (mkNF T es)
              (mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel t (gapρ a w)))) (map (_⋯ liftRen t (gapρ a w)) es))

-- The seeds: the two banned `~₁` generators are residues, verbatim.
res-seed : ∀ {n} {N K : NF n} → N ~₁ K → (N ~ᵩ₁ K) ⊎ Res N K
res-seed (perm-ν1 s t es)       = inj₂ (flipᴿ s t refl)
res-seed (perm-νν s t es)       = inj₂ (swapᴿ s rnil t refl)
res-seed (perm-φφ s x y c d t es) = inj₁ (φφᵩ s x y c d t es)
res-seed (perm-νφ s x c t es)   = inj₁ (νφᵩ s x c t es)
res-seed (perm-thr t p)         = inj₁ (thrᵩ t p)
res-seed (unit-del t es)        = inj₁ (delᵩ t es)

-- Both residue renamings are involutions, so `Res` is symmetric.
flip-undo : ∀ {j k} (t : Tel (2 + j) k) (es : List (Tm k)) →
            map (_⋯ liftId t (swapᵣ 1 1)) (map (_⋯ liftId t (swapᵣ 1 1)) es) ≡ es
flip-undo t es =
  map-fuse (liftId t (swapᵣ 1 1)) (liftId t (swapᵣ 1 1)) es
    ■ map-⋯-id (λ x → liftId-· t (swapᵣ 1 1) (swapᵣ 1 1) x
                        ■ liftId-id t (λ y → swap-11-inv y) x) es

gap-undo : ∀ {j i k} {a : Tel (2 + j) i} (w : Run a) (t : Tel (2 + i) k)
           (es : List (Tm k)) →
           map (_⋯ liftId t (gapρ a w)) (map (_⋯ liftId t (gapρ a w)) es) ≡ es
gap-undo {a = a} w t es =
  map-fuse (liftId t (gapρ a w)) (liftId t (gapρ a w)) es
    ■ map-⋯-id (λ x → liftId-· t (gapρ a w) (gapρ a w) x
                        ■ liftId-id t (λ y → gapρ-invol a w y) x) es

-- The double-rename of an involution collapses (telescope and threads).
private
  νReconTel : ∀ {p k} (t : Tel p k) (ρ : p →ᵣ p) → (∀ x → ρ (ρ x) ≡ x) →
              subst (Tel p) (innerOf-renTel t ρ p ■ renTel-id t) (renTel (renTel t ρ) ρ) ≡ t
  νReconTel t ρ inv =
    subst-■ (Tel _) (innerOf-renTel t ρ _) (renTel-id t) (renTel (renTel t ρ) ρ)
      ■ cong (subst (Tel _) (renTel-id t)) (renTel-renTel t ρ ρ ■ renTel-cong t (λ x → inv x))
      ■ renTel-idᵗ t

  νReconThr : ∀ {p k} (t : Tel p k) (ρ : p →ᵣ p) → (∀ x → ρ (ρ x) ≡ x) → (x : 𝔽 k) →
              subst 𝔽 (innerOf-renTel t ρ p ■ renTel-id t) (liftRen (renTel t ρ) ρ (liftRen t ρ x)) ≡ x
  νReconThr t ρ inv x =
    subst-■ 𝔽 (innerOf-renTel t ρ _) (renTel-id t) (liftRen (renTel t ρ) ρ (liftRen t ρ x))
      ■ cong (subst 𝔽 (renTel-id t)) (liftRen-· t ρ ρ x ■ liftRen-cong t (λ y → inv y) x)
      ■ liftId-liftRen t (idₖ ⦃ Kᵣ ⦄) x
      ■ liftId-id t (λ _ → refl) x

res-sym : ∀ {n} {N K : NF n} → Res N K → Res K N
res-sym (flipᴿ {j} s t {es = es} refl) =
  subst (Res (mkNF (s ++ᵗ tν (renTel t (swapᵣ 1 1))) (map (_⋯ liftRen t (swapᵣ 1 1)) es)))
        ( NF-≡ (innerOf-renTel t (swapᵣ 1 1) (2 + j) ■ renTel-id t)
            ( subst-++ᵗ s (innerOf-renTel t (swapᵣ 1 1) (2 + j) ■ renTel-id t)
                       (tν (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1)))
            ■ cong (s ++ᵗ_)
                   ( subst-tν (innerOf-renTel t (swapᵣ 1 1) (2 + j) ■ renTel-id t)
                              (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1))
                   ■ cong tν (νReconTel t (swapᵣ 1 1) (λ x → swap-11-inv x)) ) )
            ( cong (subst (λ z → List (Tm z)) (innerOf-renTel t (swapᵣ 1 1) (2 + j) ■ renTel-id t))
                   (map-fuse (liftRen t (swapᵣ 1 1)) (liftRen (renTel t (swapᵣ 1 1)) (swapᵣ 1 1)) es)
            ■ map-⋯-subst (innerOf-renTel t (swapᵣ 1 1) (2 + j) ■ renTel-id t)
                          (λ x → νReconThr t (swapᵣ 1 1) (λ y → swap-11-inv y) x) es
            ■ map-⋯-id (λ _ → refl) es ) )
        (flipᴿ s (renTel t (swapᵣ 1 1)) {es = map (_⋯ liftRen t (swapᵣ 1 1)) es} refl)
res-sym (swapᴿ {j} {i} s {a} w t {es = es} refl) =
  subst (Res (mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel t (gapρ a w)))) (map (_⋯ liftRen t (gapρ a w)) es)))
        ( NF-≡ (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
            ( subst-++ᵗ s (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
                       (tν (a ++ᵗ tν (renTel (renTel t (gapρ a w)) (gapρ a w))))
            ■ cong (s ++ᵗ_)
                   ( subst-tν (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
                              (a ++ᵗ tν (renTel (renTel t (gapρ a w)) (gapρ a w)))
                   ■ cong tν ( subst-++ᵗ a (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
                                        (tν (renTel (renTel t (gapρ a w)) (gapρ a w)))
                             ■ cong (a ++ᵗ_)
                                    ( subst-tν (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
                                               (renTel (renTel t (gapρ a w)) (gapρ a w))
                                    ■ cong tν (νReconTel t (gapρ a w) (λ x → gapρ-invol a w x)) ) ) ) )
            ( cong (subst (λ z → List (Tm z)) (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t))
                   (map-fuse (liftRen t (gapρ a w)) (liftRen (renTel t (gapρ a w)) (gapρ a w)) es)
            ■ map-⋯-subst (innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t)
                          (λ x → νReconThr t (gapρ a w) (λ y → gapρ-invol a w y) x) es
            ■ map-⋯-id (λ _ → refl) es ) )
        (swapᴿ s w (renTel t (gapρ a w)) {es = map (_⋯ liftRen t (gapρ a w)) es} refl)

-- The single-step commutation `push`/`push⁻` (a residue crosses one `~ᵩ`
-- step, conjugated) lives in Normal.Factor2, so that this module stays
-- hole-free while the factorisation is under construction.
