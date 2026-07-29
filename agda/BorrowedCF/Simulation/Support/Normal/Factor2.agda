-- | The REPAIRED factorisation: `factor′`, without `BlockBridge`.
--
--   `Bridge.blockBridge-refuted` shows the old cut (`Factor.factor`'s
--   hypothesis) is FALSE: two `~`-related block forms need not be
--   `~ᵇ`-related, because a `perm-νφ` under a `tν` prefix migrates a φ cell
--   between blocks while `~ᵇ` is parity-locked.  The factorisation THEOREM
--   survives with the cut moved to the M side:
--
--     factor′ : Block (tel M) → N ~ M →
--               Σ[ M′ ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
--
--   Proof shape (chain induction, right to left):
--     * a φ-only generator joins the `~ᵩ` leg;
--     * a ν-reindexing generator becomes a RESIDUE (Normal.Slots) that is
--       pushed through the remaining `~ᵩ` leg (`resolve`, via `push`) and
--       discharged against the block form (`realise`): a pair flip is
--       `ν1ᵇ` verbatim, and a gap transposition is one `bswpᵇ` — the two
--       blocks swap WITH their runs, and the run mismatch is repaid by a
--       `~ᵩ` run-exchange (`exchange`), which is precisely the move the
--       Bridge counterexample showed `~ᵇ` cannot make and `~ᵩ` can.
--
--   The `~ᵩ` run-exchange needs φ-only clones of the Bubble/Factor drag
--   machinery (`bubbleφᵩ`, `dragᵩ`): a φ cell may cross both φ and ν cells
--   inside `~ᵩ`, so the clones exist for ARBITRARY prefixes.
--
--   STATUS: see the OPEN markers (if any) above `exchange`.
module BorrowedCF.Simulation.Support.Normal.Factor2 where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift
  using (shift2; shift1; liftId-·; liftId-++ᵗ; liftId-cong)
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id; ++ᵗ-idʳ; ++ᵗ-assoc)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (bubφ; map-⋯-cong; map-⋯-id; aswap-21-12)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (aswap-12-21; aswap-22-inv; aswap-11-inv; swap-11-inv)
open import BorrowedCF.Simulation.Support.Normal.Nat using (map-fuse)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
open import BorrowedCF.Simulation.Support.Normal.Factor
open import BorrowedCF.Simulation.Support.Normal.Slots

open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- `~ᵩ` congruence for telescope prefixes (clone of Factor.~-prefix).
------------------------------------------------------------------------

~ᵩ-prefix : ∀ {n j} (s : Tel n j) {N₁ N₂ : NF j} → N₁ ~ᵩ N₂ →
            prefixNF s N₁ ~ᵩ prefixNF s N₂
~ᵩ-prefix []       c = c
~ᵩ-prefix (tν s)   c = ~ᵩ-νNF (~ᵩ-prefix s c)
~ᵩ-prefix (tφ f s) c = ~ᵩ-φNF (~ᵩ-prefix s c)

------------------------------------------------------------------------
-- The `~ᵩ` φ-bubble, for an ARBITRARY prefix (clone of Bubble.bubbleφ:
-- a φ crossing a ν is `νφᵩ` backwards, a φ crossing a φ is `φφᵩ`).
------------------------------------------------------------------------

bubbleφᵩ : ∀ {n j k} (f : Flag) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
           mkNF (tφ f (shift1 s ++ᵗ u)) es ~ᵩ
           mkNF (s ++ᵗ tφ f u) (map (_⋯ liftId u (bubφ s)) es)

bubbleφᵩ f [] u es =
  ≡→~ᵩ (cong (mkNF (tφ f u)) (sym (map-⋯-id (liftId-id u (λ _ → refl)) es)))

bubbleφᵩ f (tν s) u es =
  ~ᵩ-trans (~ᵩ-trans (≡→~ᵩ (cong (mkNF (tφ f (tν X))) (sym undo)))
                     (~ᵩ-sym (Eq*.return (νφᵩ [] f X es″))))
    (~ᵩ-trans (~ᵩ-νNF (bubbleφᵩ f s u es″))
              (≡→~ᵩ (cong (mkNF (tν (s ++ᵗ tφ f u)))
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

bubbleφᵩ f (tφ g s) u es =
  ~ᵩ-trans (Eq*.return (φφᵩ [] f g (shift1 s ++ᵗ u) es))
    (~ᵩ-trans (~ᵩ-φNF (bubbleφᵩ f s u (map (_⋯ liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1)) es)))
              (≡→~ᵩ (cong (mkNF (tφ g (s ++ᵗ tφ f u)))
                          ( map-fuse (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1))
                                     (liftId u (bubφ s)) es
                          ■ map-⋯-cong fuse es ))))
  where
    fuse : ∀ x → liftId u (bubφ s) (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1) x)
                   ≡ liftId u (bubφ (tφ g s)) x
    fuse x = cong (liftId u (bubφ s)) (liftId-++ᵗ (shift1 s) u (assocSwapᵣ 1 1) x)
               ■ liftId-· u (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ s) x

-- The outward direction (clone of FactorBase.bubbleφ⁻ inside `~ᵩ`).
bubbleφᵩ⁻ : ∀ {n j k} (f : Flag) (s : Tel n j) (u : Tel (1 + j) k) (es : List (Tm k)) →
            mkNF (s ++ᵗ tφ f u) es ~ᵩ
            mkNF (tφ f (shift1 s ++ᵗ u)) (map (_⋯ liftId u (bubφ⁻ s)) es)
bubbleφᵩ⁻ f s u es =
  ~ᵩ-trans (≡→~ᵩ (cong (mkNF (s ++ᵗ tφ f u)) (sym undo)))
           (~ᵩ-sym (bubbleφᵩ f s u (map (_⋯ liftId u (bubφ⁻ s)) es)))
  where
    undo : map (_⋯ liftId u (bubφ s)) (map (_⋯ liftId u (bubφ⁻ s)) es) ≡ es
    undo = map-fuse (liftId u (bubφ⁻ s)) (liftId u (bubφ s)) es
             ■ map-⋯-id (λ x → liftId-· u (bubφ⁻ s) (bubφ s) x
                                 ■ liftId-id u (bubφ-inv s) x) es

------------------------------------------------------------------------
-- Dragging a run outward, inside `~ᵩ` (clone of Factor.drag-sound).
------------------------------------------------------------------------

dragᵩ : ∀ {p j m k} (S : Tel p j) {r : Tel j m} (w : Run r) (t : Tel m k)
        (es : List (Tm k)) →
        mkNF (S ++ᵗ (r ++ᵗ t)) es ~ᵩ mkNF (dragTel S w t) (map (_⋯ dragRen S w t) es)
dragᵩ S rnil t es =
  ≡→~ᵩ (cong (mkNF (S ++ᵗ t)) (sym (map-⋯-id (λ _ → refl) es)))
dragᵩ S (rφ {f = f} {r = r} w) t es =
  ~ᵩ-trans (bubbleφᵩ⁻ f S (r ++ᵗ t) es)
    (~ᵩ-trans (~ᵩ-φNF (dragᵩ (shift1 S) w t (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)))
              (≡→~ᵩ (cong (mkNF (tφ f (dragTel (shift1 S) w t)))
                          (map-fuse (liftId (r ++ᵗ t) (bubφ⁻ S)) (dragRen (shift1 S) w t) es))))

------------------------------------------------------------------------
-- The intertwiner: `bubν⁻` conjugates a below-the-pair endo to its
-- shifted form.
------------------------------------------------------------------------

-- An endo `ζ` on the base, lifted under `s` and then past the pair, is
-- carried by the outward bubble to `ζ ↑* 2` lifted under `shift2 s`: the
-- bubble moves only the pair, and `ζ` does not touch it.
intertwine : ∀ {b j} (s : Tel b j) (ζ : b →ᵣ b) (x : 𝔽 (2 + j)) →
             bubν⁻ s ((liftId s ζ ↑* 2) x) ≡ liftId (shift2 s) (ζ ↑* 2) (bubν⁻ s x)
intertwine []       ζ x = refl
intertwine (tν s)   ζ x =
  cong (liftId (shift2 s) (assocSwapᵣ 2 2)) (intertwine s (ζ ↑* 2) x)
    ■ liftId-· (shift2 s) ((ζ ↑* 2) ↑* 2) (assocSwapᵣ 2 2) (bubν⁻ s x)
    ■ liftId-cong (shift2 s) (λ y → comm-↑⁴-aswap22 ζ y) (bubν⁻ s x)
    ■ sym (liftId-· (shift2 s) (assocSwapᵣ 2 2) ((ζ ↑* 2) ↑* 2) (bubν⁻ s x))
intertwine (tφ f s) ζ x =
  cong (liftId (shift2 s) (assocSwapᵣ 2 1)) (intertwine s (ζ ↑) x)
    ■ liftId-· (shift2 s) ((ζ ↑) ↑* 2) (assocSwapᵣ 2 1) (bubν⁻ s x)
    ■ liftId-cong (shift2 s) (λ y → comm-↑³-aswap21 ζ y) (bubν⁻ s x)
    ■ sym (liftId-· (shift2 s) (assocSwapᵣ 2 1) ((ζ ↑* 2) ↑) (bubν⁻ s x))

------------------------------------------------------------------------
-- The key renaming identity: `gapρ` is the bubble conjugate of aswap22.
------------------------------------------------------------------------

private
  liftId-invol22 : ∀ {b k} (X : Tel (2 + (2 + b)) k) (z : 𝔽 k) →
                   liftId X (assocSwapᵣ 2 2) (liftId X (assocSwapᵣ 2 2) z) ≡ z
  liftId-invol22 X z =
    liftId-· X (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) z
      ■ liftId-id X (λ y → aswap-22-inv y) z

  -- The five-name computation at the peeled cell: conjugating the gap swap
  -- by the νφ pieces and the outer aswaps collapses to `assocSwapᵣ 2 1`.
  key5 : ∀ {j} (y : 𝔽 (2 + (1 + (2 + j)))) →
         (assocSwapᵣ 2 2 ↑) (assocSwapᵣ 2 1 ((assocSwapᵣ 2 1 ↑* 2)
           (assocSwapᵣ 2 2 ((assocSwapᵣ 1 2 ↑* 2) y)))) ≡ assocSwapᵣ 2 1 y
  key5 zero                            = refl
  key5 (suc zero)                      = refl
  key5 (suc (suc zero))                = refl
  key5 (suc (suc (suc zero)))          = refl
  key5 (suc (suc (suc (suc zero))))    = refl
  key5 (suc (suc (suc (suc (suc y))))) = refl

-- Pulling the inner ν out through run-and-ν after the gap transposition
-- lands it exactly where pulling it out through the run alone would have.
gapρ-bub : ∀ {j i} (a : Tel (2 + j) i) (w : Run a) (x : 𝔽 (2 + i)) →
           bubν⁻ (tν a) (gapρ a w x) ≡ bubν⁻ a x
gapρ-bub []        rnil   x = aswap-22-inv x
gapρ-bub (tφ f a′) (rφ w) x =
  cong (λ z → liftId S (assocSwapᵣ 2 2 ↑) (liftId S (assocSwapᵣ 2 1) z))
       ( e₁
       ■ cong (liftId S (assocSwapᵣ 2 1 ↑* 2))
              ( e₂ ■ cong (liftId S (assocSwapᵣ 2 2)) e₃ ) )
    ■ cong (λ z → liftId S (assocSwapᵣ 2 2 ↑) (liftId S (assocSwapᵣ 2 1) (liftId S (assocSwapᵣ 2 1 ↑* 2) z)))
           (liftId-· S (assocSwapᵣ 1 2 ↑* 2) (assocSwapᵣ 2 2) (B x))
    ■ cong (λ z → liftId S (assocSwapᵣ 2 2 ↑) (liftId S (assocSwapᵣ 2 1) z))
           (liftId-· S ((assocSwapᵣ 1 2 ↑* 2) ·ₖ assocSwapᵣ 2 2) (assocSwapᵣ 2 1 ↑* 2) (B x))
    ■ cong (liftId S (assocSwapᵣ 2 2 ↑))
           (liftId-· S (((assocSwapᵣ 1 2 ↑* 2) ·ₖ assocSwapᵣ 2 2) ·ₖ (assocSwapᵣ 2 1 ↑* 2)) (assocSwapᵣ 2 1) (B x))
    ■ liftId-· S ((((assocSwapᵣ 1 2 ↑* 2) ·ₖ assocSwapᵣ 2 2) ·ₖ (assocSwapᵣ 2 1 ↑* 2)) ·ₖ assocSwapᵣ 2 1) (assocSwapᵣ 2 2 ↑) (B x)
    ■ liftId-cong S (λ y → key5 y) (B x)
  where
    S : Tel (2 + (1 + (2 + _))) (2 + _)
    S = shift2 a′

    B : 𝔽 (2 + _) → 𝔽 (2 + _)
    B = bubν⁻ a′

    e₁ : B (((liftId a′ (assocSwapᵣ 2 1)) ↑* 2) (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x)))
           ≡ liftId S (assocSwapᵣ 2 1 ↑* 2) (B (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x)))
    e₁ = intertwine a′ (assocSwapᵣ 2 1) (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))

    e₂ : B (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
           ≡ liftId S (assocSwapᵣ 2 2) (B ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
    e₂ = sym (liftId-invol22 S (B (gapρ a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))))
           ■ cong (liftId S (assocSwapᵣ 2 2))
                  (gapρ-bub a′ w ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))

    e₃ : B ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x)
           ≡ liftId S (assocSwapᵣ 1 2 ↑* 2) (B x)
    e₃ = intertwine a′ (assocSwapᵣ 1 2) x

------------------------------------------------------------------------
-- The `~ᵩ` run exchange, and the realisation of a residue at block form.
------------------------------------------------------------------------

-- From the residue's source, one ν-bubble (`bubbleνᵩ⁻`) plus one run drag
-- (`dragᵩ`) rebuilds `bswpᵇ`'s right-hand side, with composite renaming
-- `gapρ`-then-`bswapRen` (by `gapρ-bub`): the two blocks' runs trade
-- places inside `~ᵩ` while the pairs stay put.
exchange : ∀ {n j i m k} (s : Tel n j) (a : Tel (2 + j) i) (wa : Run a)
           {rb : Tel (2 + i) m} (wb : Run rb) (t : Tel m k) (es : List (Tm k)) →
           mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t))) es ~ᵩ
           mkNF (s ++ᵗ bswapTel a wb t)
                (map (_⋯ (liftId (rb ++ᵗ t) (gapρ a wa) ·ₖ bswapRen a wb t)) es)
exchange s a wa {rb} wb t es =
  ~ᵩ-trans (≡→~ᵩ (sym (prefixNF-++ᵗ s (mkNF (tν (a ++ᵗ tν (rb ++ᵗ t))) es))))
    (~ᵩ-trans (~ᵩ-prefix s core)
      (≡→~ᵩ (prefixNF-++ᵗ s
              (mkNF (bswapTel a wb t)
                    (map (_⋯ (liftId (rb ++ᵗ t) (gapρ a wa) ·ₖ bswapRen a wb t)) es)))))
  where
    pointwise : ∀ x → (liftId (rb ++ᵗ t) (bubν⁻ a) ·ₖ dragRen (tν (shift2 a)) wb t) x
                        ≡ (liftId (rb ++ᵗ t) (gapρ a wa) ·ₖ bswapRen a wb t) x
    pointwise x =
      sym (cong (dragRen (tν (shift2 a)) wb t)
                ( liftId-· (rb ++ᵗ t) (gapρ a wa) (bubν⁻ (tν a)) x
                ■ liftId-cong (rb ++ᵗ t) (λ y → gapρ-bub a wa y) x ))

    glue : map (_⋯ dragRen (tν (shift2 a)) wb t)
               (map (_⋯ liftId (rb ++ᵗ t) (bubν⁻ a)) es)
             ≡ map (_⋯ (liftId (rb ++ᵗ t) (gapρ a wa) ·ₖ bswapRen a wb t)) es
    glue = map-fuse (liftId (rb ++ᵗ t) (bubν⁻ a)) (dragRen (tν (shift2 a)) wb t) es
             ■ map-⋯-cong pointwise es

    core : mkNF (tν (a ++ᵗ tν (rb ++ᵗ t))) es ~ᵩ
           mkNF (bswapTel a wb t)
                (map (_⋯ (liftId (rb ++ᵗ t) (gapρ a wa) ·ₖ bswapRen a wb t)) es)
    core =
      ~ᵩ-trans (~ᵩ-νNF (bubbleνᵩ⁻ wa (rb ++ᵗ t) es))
        (~ᵩ-trans (~ᵩ-νNF (dragᵩ (tν (shift2 a)) wb t
                                 (map (_⋯ liftId (rb ++ᵗ t) (bubν⁻ a)) es)))
                  (≡→~ᵩ (cong (mkNF (bswapTel a wb t)) glue)))

-- Splitting a telescope at the end of its leading run.
record RunSplit {n k} (t : Tel n k) : Set where
  constructor mkRS
  field
    {mid}  : ℕ
    run    : Tel n mid
    rest   : Tel mid k
    wrun   : Run run
    brest  : Block rest
    splits : t ≡ run ++ᵗ rest

splitRun : ∀ {n k} (t : Tel n k) → RunSplit t
splitRun t with headView t
... | vrun r            = mkRS _ [] r bnil (sym (++ᵗ-idʳ _))
... | vν {s = s} rs u   = mkRS s (tν u) rs bν refl

-- Discharging a residue against a block form: a pair flip is `ν1ᵇ`
-- verbatim (M′ = N); a gap transposition is one `bswpᵇ` at the residue's
-- outer ν, with `exchange` paying the `~ᵩ` leg.
realise : ∀ {n} {N M : NF n} → Res N M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
realise (flipᴿ s t {es = es} refl refl) bM =
  mkNF (s ++ᵗ tν t) es , bM , ~ᵩ-refl , Eq*.return (ν1ᵇ s t es)
realise (swapᴿ s {a} w t {es = es} refl refl) bM with splitRun t
... | mkRS rb rest wb brest refl =
  mkNF (s ++ᵗ bswapTel a wb rest)
       (map (_⋯ (liftId (rb ++ᵗ rest) (gapρ a w) ·ₖ bswapRen a wb rest)) es)
    , Block-++ᵗ s (λ _ → bν) bM
    , exchange s a w wb rest es
    , ~ᵇ-sym (~ᵇ-trans
        (Eq*.return (bswpᵇ s w wb brest (map (_⋯ liftId (rb ++ᵗ rest) (gapρ a w)) es)))
        (≡→~ᵇ (cong (mkNF (s ++ᵗ bswapTel a wb rest))
                    (map-fuse (liftId (rb ++ᵗ rest) (gapρ a w)) (bswapRen a wb rest) es))))

------------------------------------------------------------------------
-- Pushing a residue past one `~ᵩ` step.
------------------------------------------------------------------------

-- Renaming reflects the spent unit: a renamed term is `K \`unit` only if
-- the term already was (heads are preserved, cf. Witness.live-⋯).
unit-⋯⁻¹ : ∀ {a b} (e : Tm a) (ρ : a →ᵣ b) → e ⋯ ρ ≡ K `unit → e ≡ K `unit
unit-⋯⁻¹ (K `unit) ρ eq = refl
unit-⋯⁻¹ (K `fork) ρ ()
unit-⋯⁻¹ (K `send) ρ ()
unit-⋯⁻¹ (K `recv) ρ ()
unit-⋯⁻¹ (K `drop) ρ ()
unit-⋯⁻¹ (K `acq) ρ ()
unit-⋯⁻¹ (K `discard) ρ ()
unit-⋯⁻¹ (K (`end p)) ρ ()
unit-⋯⁻¹ (K (`new s)) ρ ()
unit-⋯⁻¹ (K (`lsplit s)) ρ ()
unit-⋯⁻¹ (K (`rsplit s)) ρ ()
unit-⋯⁻¹ (K (`select b)) ρ ()
unit-⋯⁻¹ (K `branch) ρ ()
unit-⋯⁻¹ (` x) ρ ()
unit-⋯⁻¹ (ƛ e) ρ ()
unit-⋯⁻¹ (μ e) ρ ()
unit-⋯⁻¹ (e₁ ·⟨ d ⟩ e₂) ρ ()
unit-⋯⁻¹ (e₁ ; e₂) ρ ()
unit-⋯⁻¹ (e₁ ⊗ e₂) ρ ()
unit-⋯⁻¹ (`let e₁ `in e₂) ρ ()
unit-⋯⁻¹ (`let⊗ e₁ `in e₂) ρ ()
unit-⋯⁻¹ (`inj i e) ρ ()
unit-⋯⁻¹ (`case e `of⟨ e₁ ; e₂ ⟩) ρ ()

-- A `~ᵩ` step that does not touch the telescope crosses a residue by
-- conjugation with the residue's (involutive) renaming.
pushThr : ∀ {n k} {N : NF n} (T : Tel n k) (es₁ es₂ : List (Tm k)) → es₁ ↭ es₂ →
          Res N (mkNF T es₁) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushThr T es₁ es₂ p (flipᴿ s t {es = es} eqT eqE) =
  mkNF T (map (_⋯ liftId t (swapᵣ 1 1)) es₂)
    , Eq*.return (thrᵩ T (↭-trans (↭-reflexive (sym (flip-undo t es)))
        (map⁺ (_⋯ liftId t (swapᵣ 1 1)) (↭-trans (↭-reflexive (sym eqE)) p))))
    , flipᴿ s t eqT (sym (flip-undo t es₂))
pushThr T es₁ es₂ p (swapᴿ s {a} w t {es = es} eqT eqE) =
  mkNF T (map (_⋯ liftId t (gapρ a w)) es₂)
    , Eq*.return (thrᵩ T (↭-trans (↭-reflexive (sym (gap-undo w t es)))
        (map⁺ (_⋯ liftId t (gapρ a w)) (↭-trans (↭-reflexive (sym eqE)) p))))
    , swapᴿ s w t eqT (sym (gap-undo w t es₂))

pushDel : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T (K `unit ∷ es₂)) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushDel T es₂ (flipᴿ s t {es = []} eqT ())
pushDel T es₂ (flipᴿ s t {es = e₀ ∷ es₀} eqT eqE)
  with unit-⋯⁻¹ e₀ (liftId t (swapᵣ 1 1)) (sym (∷-injectiveˡ eqE))
... | refl = mkNF T es₀ , Eq*.return (delᵩ T es₀) , flipᴿ s t eqT (∷-injectiveʳ eqE)
pushDel T es₂ (swapᴿ s {a} w t {es = []} eqT ())
pushDel T es₂ (swapᴿ s {a} w t {es = e₀ ∷ es₀} eqT eqE)
  with unit-⋯⁻¹ e₀ (liftId t (gapρ a w)) (sym (∷-injectiveˡ eqE))
... | refl = mkNF T es₀ , Eq*.return (delᵩ T es₀) , swapᴿ s w t eqT (∷-injectiveʳ eqE)

pushIns : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T es₂) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T (K `unit ∷ es₂))
pushIns T es₂ (flipᴿ s t {es = es} eqT eqE) =
  mkNF T (K `unit ∷ es)
    , ~ᵩ-sym (Eq*.return (delᵩ T es))
    , flipᴿ s t eqT (cong (K `unit ∷_) eqE)
pushIns T es₂ (swapᴿ s {a} w t {es = es} eqT eqE) =
  mkNF T (K `unit ∷ es)
    , ~ᵩ-sym (Eq*.return (delᵩ T es))
    , swapᴿ s w t eqT (cong (K `unit ∷_) eqE)

-- OPEN (skeleton): the two telescope-rearranging generators, by the `Cmp`
-- alignment of the step's window against the residue's region.
pushφφ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x y : Flag)
         (t₂ : Tel (1 + (1 + j)) k) (es₂ : List (Tm k)) →
         Res N (mkNF (s₂ ++ᵗ tφ x (tφ y t₂)) es₂) →
         Σ[ N′ ∈ NF n ] (N ~ᵩ N′) ×
           Res N′ (mkNF (s₂ ++ᵗ tφ y (tφ x t₂)) (map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) es₂))
pushφφ = ?

pushνφ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x : Flag)
         (t₂ : Tel (1 + (2 + j)) k) (es₂ : List (Tm k)) →
         Res N (mkNF (s₂ ++ᵗ tν (tφ x t₂)) es₂) →
         Σ[ N′ ∈ NF n ] (N ~ᵩ N′) ×
           Res N′ (mkNF (s₂ ++ᵗ tφ x (tν t₂)) (map (_⋯ liftId t₂ (assocSwapᵣ 1 2)) es₂))
pushνφ = ?

pushνφ⁻ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x : Flag)
          (t₂ : Tel (1 + (2 + j)) k) (es₂ : List (Tm k)) →
          Res N (mkNF (s₂ ++ᵗ tφ x (tν t₂)) (map (_⋯ liftId t₂ (assocSwapᵣ 1 2)) es₂)) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF (s₂ ++ᵗ tν (tφ x t₂)) es₂)
pushνφ⁻ = ?

private
  aswap11-undo : ∀ {j k} (t₂ : Tel (1 + (1 + j)) k) (es : List (Tm k)) →
                 map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) (map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) es) ≡ es
  aswap11-undo t₂ es =
    map-fuse (liftId t₂ (assocSwapᵣ 1 1)) (liftId t₂ (assocSwapᵣ 1 1)) es
      ■ map-⋯-id (λ x → liftId-· t₂ (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) x
                          ■ liftId-id t₂ (λ y → aswap-11-inv y) x) es

push : ∀ {n} {N K L : NF n} → Res N K → K ~ᵩ₁ L →
       Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ L
push r (φφᵩ s₂ x y t₂ es₂)    = pushφφ s₂ x y t₂ es₂ r
push r (νφᵩ s₂ x t₂ es₂)      = pushνφ s₂ x t₂ es₂ r
push r (thrᵩ T {es₁} {es₂} p) = pushThr T es₁ es₂ p r
push r (delᵩ T es₂)           = pushDel T es₂ r

push⁻ : ∀ {n} {N K L : NF n} → Res N K → L ~ᵩ₁ K →
        Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ L
push⁻ r (φφᵩ s₂ x y t₂ es₃)
  with pushφφ s₂ y x t₂ (map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) es₃) r
... | N′ , c , r′ =
  N′ , c , subst (Res N′) (cong (mkNF (s₂ ++ᵗ tφ x (tφ y t₂))) (aswap11-undo t₂ es₃)) r′
push⁻ r (νφᵩ s₂ x t₂ es₃)     = pushνφ⁻ s₂ x t₂ es₃ r
push⁻ r (thrᵩ T {es₁} {es₂} p) = pushThr T es₂ es₁ (↭-sym p) r
push⁻ r (delᵩ T es₃)          = pushIns T es₃ r

------------------------------------------------------------------------
-- Pushing a residue down a `~ᵩ` chain, and the theorem.
------------------------------------------------------------------------

resolve : ∀ {n} {N K M : NF n} → Res N K → K ~ᵩ M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
resolve r ε           bM = realise r bM
resolve r (fwd h ◅ c) bM with push r h
... | N′ , cN , r′ with resolve r′ c bM
...   | M′ , b′ , c′ , cb = M′ , b′ , ~ᵩ-trans cN c′ , cb
resolve r (bwd h ◅ c) bM with push⁻ r h
... | N′ , cN , r′ with resolve r′ c bM
...   | M′ , b′ , c′ , cb = M′ , b′ , ~ᵩ-trans cN c′ , cb

factor′ : ∀ {n} {N M : NF n} → Block (tel M) → N ~ M →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
factor′ {M = M} bM ε = M , bM , ~ᵩ-refl , ~ᵇ-refl
factor′ bM (fwd g ◅ c) with factor′ bM c
... | M₁ , b₁ , cφ , cb with res-seed g
...   | inj₁ h = M₁ , b₁ , ~ᵩ-trans (Eq*.return h) cφ , cb
...   | inj₂ r with resolve r cφ b₁
...     | M₂ , b₂ , c₂ , cb₂ = M₂ , b₂ , c₂ , ~ᵇ-trans cb₂ cb
factor′ bM (bwd g ◅ c) with factor′ bM c
... | M₁ , b₁ , cφ , cb with res-seed g
...   | inj₁ h = M₁ , b₁ , ~ᵩ-trans (~ᵩ-sym (Eq*.return h)) cφ , cb
...   | inj₂ r with resolve (res-sym r) cφ b₁
...     | M₂ , b₂ , c₂ , cb₂ = M₂ , b₂ , c₂ , ~ᵇ-trans cb₂ cb
