-- | The realisation layer: a `~ᵇ` move OUT of an image block form is realised
--   by a TYPED structural congruence, with a `~ᵩ` residue.
--
--   `PrenexImage` shows every image normal form is `mkNF (BTel t n) thr` for a
--   typed prenex telescope `t`.  This module inverts Factor's block moves
--   against that presentation:
--
--     * `φφᵇ` / `thrᵇ` / `delᵇ` are `~ᵩ` generators verbatim — the typed side
--       does not move at all and the whole move lands in the residue (PROVEN);
--     * `bswpᵇ` is realised by `ν-comm′` on the located typed node pair
--       (`realise-bswp`): the position is inverted with `locate-1`, the typed
--       move is `swapHead-≋`, and the TELESCOPE coherence between Factor's
--       `bswapTel` and the swapped image's `BTel` is discharged by the shape
--       calculus (`shape-det`) — transport-free and fully proven.  The THREAD
--       coherence (`Bσ` versus `bswapRen`, through `σB`'s splitAt/subst
--       plumbing) is the stated-open `BswpThreadCoh` below;
--     * `ν1ᵇ` is realised by `ν-swap′` on the located node (`realise-flip`);
--       its residue — the within-run flag reordering `φTel B₁ ++ φTel B₂` →
--       `φTel B₂ ++ φTel B₁` (a `φφᵇ`-composite, `~ᵩ`) plus the matching
--       thread coherence — is the stated-open `FlipResidue`.
--
--   Backward steps at an exact image are also delivered: `realise-stepᵇ-ν1`
--   reduces a backward `ν1ᵇ` to the forward residue via the involution
--   `swapᵣ 1 1`, and `realise-bswpᵇ` inverts a backward block swap with the
--   same locate/shape-det machinery.  `realise-step-exact` is TOTAL over
--   `SymClosure _~ᵇ₁_` at an exact image.
--
--   Chains: `realise-~ᵇ` packages a whole `~ᵇ` chain, by induction, given the
--   strengthened per-step statement `RealiseStep` (input up to a `~ᵩ` gap).
--
--   OPEN (stated hypotheses, no holes / no postulates):
--     * `BswpThreadCoh` / `BswpThreadCohᵇ` — thread coherence of the block
--       swap (forward / backward orientation);
--     * `FlipResidue`   — the full residue of the endpoint flip (within-run
--       chunk reorder, a `φφᵩ` composite, plus its thread coherence);
--     * `RealiseStep`   — the `~ᵩ`-gap strengthening.  Given the three
--       hypotheses above, `realise-step-exact` discharges ALL its exact-image
--       instances; the sole residual content is commuting a nonempty `~ᵩ` gap
--       past a block move (the same φ-migration wall Factor's `BlockBridge`
--       quarantines).
module BorrowedCF.Simulation.Support.Normal.Realise where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; []; tν; tφ; _++ᵗ_; NF; mkNF; tel; thr; inner)
open import BorrowedCF.Simulation.Support.Normal.Image
  using (Slot; sν; sφ; shape; shape-subst; shape-++ᵗ; syncFlags)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Shift using (liftId-·)
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id)
open import BorrowedCF.Simulation.Support.Normal.Bubble using (map-⋯-id)
open import BorrowedCF.Simulation.Support.Normal.Nat using (map-fuse)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
  using (Run; rnil; rφ; Block; bnil; bν;
         _~ᵩ_; _~ᵩ₁_; φφᵩ; νφᵩ; thrᵩ; delᵩ;
         ~ᵩ-refl; ~ᵩ-sym; ~ᵩ-trans; ≡→~ᵩ)
open import BorrowedCF.Simulation.Support.Normal.Factor
  using (_~ᵇ_; _~ᵇ₁_; ν1ᵇ; φφᵇ; thrᵇ; delᵇ; bswpᵇ; bswapTel; bswapRen)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BTel; BScope; Bσ; BShape; blockShape; shape-prenex-image)
open import BorrowedCF.Simulation.Support.Normal.RealiseBase

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Image block forms and what it means to realise a move on one.
------------------------------------------------------------------------

ImageOf : ∀ {m k} (t : TTel m k) (es : List (Tm k)) (p : ℕ) (σ : m →ₛ p) → NF p
ImageOf t es p σ = mkNF (BTel t p) (map (_⋯ Bσ t σ) es ++ (K `unit ∷ []))

-- A realisation of a normal form `M` out of the image of `(t , es)`: new
-- typed prenex data whose plugging is ≋ the old one, and whose image absorbs
-- `M` up to the φ-only residue `~ᵩ`.
record Realised {m k p} (t : TTel m k) (es : List (Tm k))
                (σ : m →ₛ p) (M : NF p) : Set where
  constructor realised
  field
    {k†}  : ℕ
    t†    : TTel m k†
    es†   : List (Tm k†)
    moved : plugᵗ t (parsᵗ es) ≋ plugᵗ t† (parsᵗ es†)
    res   : M ~ᵩ ImageOf t† es† p σ

open Realised public

------------------------------------------------------------------------
-- Auxiliary: an empty block shape forces the empty typed telescope.
------------------------------------------------------------------------

BShape-[]ᵗ : ∀ {a b} (u : TTel a b) → BShape u ≡ [] →
             Σ[ eq ∈ b ≡ a ] subst (TTel a) eq u ≡ []ᵗ
BShape-[]ᵗ []ᵗ           _  = refl , refl
BShape-[]ᵗ (tνᵗ B₁ B₂ u) ()

------------------------------------------------------------------------
-- OPEN #1: thread coherence of the block swap.
--
--   Everything structural about `bswpᵇ` is proven below; what remains is that
--   the composite renaming `bswapRen` acts on the image threads exactly as
--   the typed `assocSwapᵣ` does under the accumulated substitution `Bσ` —
--   an unwinding of `σB`'s splitAt/subst plumbing (`Nat.agda`-style).
------------------------------------------------------------------------

BswpThreadCoh : Set
BswpThreadCoh =
  ∀ {m q k p} (u : TTel m q) (G₁ G₂ A₁ A₂ : BindGroup)
    (t₂ : TTel (sum A₁ + sum A₂ + (sum G₁ + sum G₂ + q)) k)
    (es : List (Tm k)) (σ : m →ₛ p)
    {j i m′ k′} (s : Tel p j) (a : Tel (2 + j) i) (ra : Run a)
    {rb : Tel (2 + i) m′} (w : Run rb) (t′ : Tel m′ k′) (bt : Block t′)
    (es₁ : List (Tm k′)) →
    (pre≡ : BShape u ≡ shape s) →
    (fl₁ : syncFlags G₁ ++ syncFlags G₂ ≡ runFlags ra) →
    (fl₂ : syncFlags A₁ ++ syncFlags A₂ ≡ runFlags w) →
    (X≡₂ : BShape t₂ ≡ shape t′) →
    mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t′))) es₁
      ≡ ImageOf (u ++ᵗᵗ tνᵗ G₁ G₂ (tνᵗ A₁ A₂ t₂)) es p σ →
    (eqk : k′ ≡ BScope (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                  (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) p) →
    subst (List ∘ Tm) eqk (map (_⋯ bswapRen a w t′) es₁)
      ≡ map (_⋯ Bσ (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                 (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) σ)
            (map (_⋯ (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))) es)
          ++ (K `unit ∷ [])

------------------------------------------------------------------------
-- OPEN #2: the residue of the endpoint flip.
--
--   The typed `ν-swap′` reverses the node's two φ-nests (`φTel G₁ ++ φTel G₂`
--   becomes `φTel G₂ ++ φTel G₁`) — an in-run reordering, i.e. a `φφᵩ`
--   composite — and renames threads by `swapᵣ (sum G₁) (sum G₂)` where `ν1ᵇ`
--   renames by `swapᵣ 1 1`; the residue packages both.
------------------------------------------------------------------------

FlipResidue : Set
FlipResidue =
  ∀ {m q k p} (u : TTel m q) (G₁ G₂ : BindGroup)
    (t₀ : TTel (sum G₁ + sum G₂ + q) k)
    (es : List (Tm k)) (σ : m →ₛ p)
    {j k′} (s : Tel p j) (v : Tel (2 + j) k′) (es₁ : List (Tm k′)) →
    (pre≡ : BShape u ≡ shape s) →
    (Y≡ : (map sφ (syncFlags G₁) ++ map sφ (syncFlags G₂)) ++ BShape t₀
            ≡ shape v) →
    mkNF (s ++ᵗ tν v) es₁ ≡ ImageOf (u ++ᵗᵗ tνᵗ G₁ G₂ t₀) es p σ →
    mkNF (s ++ᵗ tν v) (map (_⋯ liftId v (swapᵣ 1 1)) es₁)
      ~ᵩ ImageOf (u ++ᵗᵗ tνᵗ G₂ G₁ (t₀ ⋯ᵗᵉˡ swapᵣ (sum G₁) (sum G₂)))
                 (map (_⋯ (t₀ ↑ᵗᵉˡ swapᵣ (sum G₁) (sum G₂))) es) p σ

------------------------------------------------------------------------
-- Realising a block swap (modulo OPEN #1).
------------------------------------------------------------------------

realise-bswp :
  BswpThreadCoh →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {j i m′ k′} (s : Tel p j) {a : Tel (2 + j) i} (ra : Run a)
  {rb : Tel (2 + i) m′} (w : Run rb) {t′ : Tel m′ k′} (bt : Block t′)
  (es₁ : List (Tm k′))
  (eq : mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t′))) es₁ ≡ ImageOf t es p σ) →
  Realised t es σ (mkNF (s ++ᵗ bswapTel a w t′) (map (_⋯ bswapRen a w t′) es₁))
realise-bswp coh t es σ s {a} ra {rb} w {t′} bt es₁ eq
  with locate-1 t (shape s)
        (map sφ (runFlags ra) ++ (sν ∷ (map sφ (runFlags w) ++ shape t′)))
        ( sym (shape-prenex-image t _)
        ■ sym (cong shape (NF-tel eq))
        ■ shape-subst (NF-inner eq) (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t′)))
        ■ shape-++ᵗ s (tν (a ++ᵗ tν (rb ++ᵗ t′)))
        ■ cong (λ z → shape s ++ (sν ∷ z))
            ( shape-++ᵗ a (tν (rb ++ᵗ t′))
            ■ cong₂ (λ y z → y ++ (sν ∷ z)) (shape-run ra)
                (shape-++ᵗ rb t′ ■ cong (_++ shape t′) (shape-run w)) ) )
... | mkLoc1 u G₁ G₂ {t₀ = t₀} t≡ pre≡ Y≡ with t≡
... | refl
  with φν-split (syncFlags G₁ ++ syncFlags G₂) (runFlags ra)
        ( cong (_++ BShape t₀) (map-sφ-++ (syncFlags G₁) (syncFlags G₂))
        ■ Y≡ )
        (BShape-headν t₀) (inj₂ (_ , refl))
... | fl₁ , X≡
  with locate-1 t₀ [] (map sφ (runFlags w) ++ shape t′) X≡
... | mkLoc1 u₂ A₁ A₂ {t₀ = t₂} t≡₂ pre≡₂ Y≡₂
  with BShape-[]ᵗ u₂ pre≡₂
... | refl , refl with t≡₂
... | refl
  with φν-split (syncFlags A₁ ++ syncFlags A₂) (runFlags w)
        ( cong (_++ BShape t₂) (map-sφ-++ (syncFlags A₁) (syncFlags A₂))
        ■ Y≡₂ )
        (BShape-headν t₂) (Block-headν bt)
... | fl₂ , X≡₂
  with shape-det (s ++ᵗ bswapTel a w t′)
        (BTel (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
           (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) _)
        ( shape-++ᵗ s (bswapTel a w t′)
        ■ cong (shape s ++_) (shape-bswapTel a w t′)
        ■ sym
          ( shape-prenex-image
              (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                 (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) _
          ■ BShape-++ᵗᵗ u (tνᵗ A₁ A₂ (tνᵗ G₁ G₂
              (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))))
          ■ cong₂ (λ y z → y ++ (sν ∷ z)) pre≡
              ( cong₂ (λ y z → y ++ (sν ∷ z))
                  ( sym (map-sφ-++ (syncFlags A₁) (syncFlags A₂))
                  ■ cong (map sφ) fl₂ )
                  ( cong₂ _++_
                      ( sym (map-sφ-++ (syncFlags G₁) (syncFlags G₂))
                      ■ cong (map sφ) fl₁
                      ■ sym (shape-run ra) )
                      ( BShape-⋯ᵗᵉˡ t₂ (assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))
                      ■ X≡₂ ) ) ) ) )
... | eqk , telPart =
  realised
    (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
       (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))))
    (map (_⋯ (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))) es)
    ( move-≋ u
        ( swapHead-≋ G₁ G₂ A₁ A₂ t₂ (parsᵗ es)
        ◅◅ ≡→≋ᵗ (cong
             (plugᵗ (tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))))
             (pars-⋯ₚᵗ es (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) ) )
    (≡→~ᵩ (mkNF-cong eqk telPart
      (coh u G₁ G₂ A₁ A₂ t₂ es σ s a ra w t′ bt es₁ pre≡ fl₁ fl₂ X≡₂ eq eqk)))

------------------------------------------------------------------------
-- Realising an endpoint flip (modulo OPEN #2).
------------------------------------------------------------------------

realise-flip :
  FlipResidue →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {j k′} (s : Tel p j) (v : Tel (2 + j) k′) (es₁ : List (Tm k′))
  (eq : mkNF (s ++ᵗ tν v) es₁ ≡ ImageOf t es p σ) →
  Realised t es σ (mkNF (s ++ᵗ tν v) (map (_⋯ liftId v (swapᵣ 1 1)) es₁))
realise-flip flip t es σ s v es₁ eq
  with locate-1 t (shape s) (shape v)
        ( sym (shape-prenex-image t _)
        ■ sym (cong shape (NF-tel eq))
        ■ shape-subst (NF-inner eq) (s ++ᵗ tν v)
        ■ shape-++ᵗ s (tν v) )
... | mkLoc1 u G₁ G₂ {t₀ = t₀} t≡ pre≡ Y≡ with t≡
... | refl =
  realised
    (u ++ᵗᵗ tνᵗ G₂ G₁ (t₀ ⋯ᵗᵉˡ swapᵣ (sum G₁) (sum G₂)))
    (map (_⋯ (t₀ ↑ᵗᵉˡ swapᵣ (sum G₁) (sum G₂))) es)
    ( move-≋ u
        ( flipHead-≋ G₁ G₂ t₀ (parsᵗ es)
        ◅◅ ≡→≋ᵗ (cong
             (plugᵗ (tνᵗ G₂ G₁ (t₀ ⋯ᵗᵉˡ swapᵣ (sum G₁) (sum G₂))))
             (pars-⋯ₚᵗ es (t₀ ↑ᵗᵉˡ swapᵣ (sum G₁) (sum G₂)))) ) )
    (flip u G₁ G₂ t₀ es σ s v es₁ pre≡ Y≡ eq)

------------------------------------------------------------------------
-- The exact-image forward step: all five generators.
------------------------------------------------------------------------

realise-stepᶠ :
  BswpThreadCoh → FlipResidue →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {N M : NF p} → N ~ᵇ₁ M → N ≡ ImageOf t es p σ →
  Realised t es σ M
realise-stepᶠ coh fl t es σ (ν1ᵇ s v es₁) eq =
  realise-flip fl t es σ s v es₁ eq
realise-stepᶠ coh fl t es σ (φφᵇ s x y v es₁) eq =
  realised t es ε
    (~ᵩ-trans (~ᵩ-sym (Eq*.return (φφᵩ s x y v es₁))) (≡→~ᵩ eq))
realise-stepᶠ coh fl t es σ (thrᵇ v perm) eq =
  realised t es ε
    (~ᵩ-trans (~ᵩ-sym (Eq*.return (thrᵩ v perm))) (≡→~ᵩ eq))
realise-stepᶠ coh fl t es σ (delᵇ v es₁) eq =
  realised t es ε
    (~ᵩ-trans (~ᵩ-sym (Eq*.return (delᵩ v es₁))) (≡→~ᵩ eq))
realise-stepᶠ coh fl t es σ (bswpᵇ s ra w bt es₁) eq =
  realise-bswp coh t es σ s ra w bt es₁ eq

------------------------------------------------------------------------
-- OPEN #3: the strengthened per-step statement, and the chain.
--
--   A `~ᵇ` chain visits normal forms that are only `~ᵩ`-close to an image;
--   the per-step statement therefore takes the gap as input and must handle
--   both step orientations.  `realise-stepᶠ` discharges its exact-image
--   forward instances; the rest is (i) φ-gap commutation past a block move
--   and (ii) the backward `ν1ᵇ`/`bswpᵇ` steps.
------------------------------------------------------------------------

RealiseStep : Set
RealiseStep =
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {N N′ : NF p} →
  N ~ᵩ ImageOf t es p σ → SymClosure _~ᵇ₁_ N N′ →
  Realised t es σ N′

-- The φ-like steps of `RealiseStep` hold with the gap, in both orientations:
-- the move itself is a `~ᵩ` generator, so it only extends the residue.
realise-step-φφ :
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {N N′ : NF p} →
  N ~ᵩ ImageOf t es p σ → SymClosure _~ᵩ₁_ N N′ →
  Realised t es σ N′
realise-step-φφ t es σ gap (fwd g) =
  realised t es ε (~ᵩ-trans (~ᵩ-sym (Eq*.return g)) gap)
realise-step-φφ t es σ gap (bwd g) =
  realised t es ε (~ᵩ-trans (Eq*.return g) gap)

-- Chains, given the per-step statement: compose the typed moves by ≋
-- transitivity and hand the final residue through.
realise-chain :
  RealiseStep →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {N M : NF p} →
  N ~ᵩ ImageOf t es p σ → N ~ᵇ M →
  Realised t es σ M
realise-chain RS t es σ gap ε = realised t es ε gap
realise-chain RS t es σ gap (g ◅ c) with RS t es σ gap g
... | realised t₁ es₁ moved₁ res₁ with realise-chain RS t₁ es₁ σ res₁ c
...   | realised t₂ es₂ moved₂ res₂ = realised t₂ es₂ (moved₁ ◅◅ moved₂) res₂

-- The packaged realisation: a `~ᵇ` chain out of an image block form is a
-- typed ≋ plus a `~ᵩ` residue.
realise-~ᵇ :
  RealiseStep →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {M : NF p} →
  ImageOf t es p σ ~ᵇ M →
  Realised t es σ M
realise-~ᵇ RS t es σ c = realise-chain RS t es σ ~ᵩ-refl c

------------------------------------------------------------------------
-- Backward steps at an exact image.
------------------------------------------------------------------------

-- `swapᵣ 1 1` is an involution, so a backward `ν1ᵇ` step reduces to the
-- forward one: un-renaming the threads is renaming them once more.
private
  swapᵣ-11-inv : ∀ {n} (x : 𝔽 (1 + 1 + n)) → swapᵣ 1 1 (swapᵣ 1 1 x) ≡ x
  swapᵣ-11-inv 0F            = refl
  swapᵣ-11-inv 1F            = refl
  swapᵣ-11-inv (suc (suc x)) = refl

realise-stepᵇ-ν1 :
  FlipResidue →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {j k′} (s : Tel p j) (v : Tel (2 + j) k′) (es₁ : List (Tm k′))
  (eq : mkNF (s ++ᵗ tν v) (map (_⋯ liftId v (swapᵣ 1 1)) es₁) ≡ ImageOf t es p σ) →
  Realised t es σ (mkNF (s ++ᵗ tν v) es₁)
realise-stepᵇ-ν1 fl t es σ s v es₁ eq
  with realise-flip fl t es σ s v (map (_⋯ liftId v (swapᵣ 1 1)) es₁) eq
... | realised t† es† moved res =
  realised t† es† moved
    (~ᵩ-trans (≡→~ᵩ (cong (mkNF (s ++ᵗ tν v)) (sym undo))) res)
  where
    undo : map (_⋯ liftId v (swapᵣ 1 1)) (map (_⋯ liftId v (swapᵣ 1 1)) es₁) ≡ es₁
    undo = map-fuse (liftId v (swapᵣ 1 1)) (liftId v (swapᵣ 1 1)) es₁
         ■ map-⋯-id (λ x → liftId-· v (swapᵣ 1 1) (swapᵣ 1 1) x
                             ■ liftId-id v (λ y → swapᵣ-11-inv y) x) es₁

------------------------------------------------------------------------
-- OPEN #1ᵇ: thread coherence of the BACKWARD block swap — the mirror of
--   `BswpThreadCoh`, with the swapped form on the image side.
------------------------------------------------------------------------

BswpThreadCohᵇ : Set
BswpThreadCohᵇ =
  ∀ {m q k p} (u : TTel m q) (G₁ G₂ A₁ A₂ : BindGroup)
    (t₂ : TTel (sum A₁ + sum A₂ + (sum G₁ + sum G₂ + q)) k)
    (es : List (Tm k)) (σ : m →ₛ p)
    {j i m′ k′} (s : Tel p j) (a : Tel (2 + j) i) (ra : Run a)
    {rb : Tel (2 + i) m′} (w : Run rb) (t′ : Tel m′ k′) (bt : Block t′)
    (es₁ : List (Tm k′)) →
    (pre≡ : BShape u ≡ shape s) →
    (fl₁ : syncFlags G₁ ++ syncFlags G₂ ≡ runFlags w) →
    (fl₂ : syncFlags A₁ ++ syncFlags A₂ ≡ runFlags ra) →
    (X≡₂ : BShape t₂ ≡ shape t′) →
    mkNF (s ++ᵗ bswapTel a w t′) (map (_⋯ bswapRen a w t′) es₁)
      ≡ ImageOf (u ++ᵗᵗ tνᵗ G₁ G₂ (tνᵗ A₁ A₂ t₂)) es p σ →
    (eqk : k′ ≡ BScope (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                  (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) p) →
    subst (List ∘ Tm) eqk es₁
      ≡ map (_⋯ Bσ (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                 (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) σ)
            (map (_⋯ (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))) es)
          ++ (K `unit ∷ [])

------------------------------------------------------------------------
-- Realising a backward block swap (modulo OPEN #1ᵇ).  The located first
-- node now carries the MOVED block's run (`runFlags w`), the second the
-- stationary one — otherwise the inversion is the mirror image of the
-- forward case, and the typed move is the same `swapHead-≋`.
------------------------------------------------------------------------

realise-bswpᵇ :
  BswpThreadCohᵇ →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {j i m′ k′} (s : Tel p j) {a : Tel (2 + j) i} (ra : Run a)
  {rb : Tel (2 + i) m′} (w : Run rb) {t′ : Tel m′ k′} (bt : Block t′)
  (es₁ : List (Tm k′))
  (eq : mkNF (s ++ᵗ bswapTel a w t′) (map (_⋯ bswapRen a w t′) es₁)
          ≡ ImageOf t es p σ) →
  Realised t es σ (mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t′))) es₁)
realise-bswpᵇ coh t es σ s {a} ra {rb} w {t′} bt es₁ eq
  with locate-1 t (shape s)
        (map sφ (runFlags w) ++ (sν ∷ (shape a ++ shape t′)))
        ( sym (shape-prenex-image t _)
        ■ sym (cong shape (NF-tel eq))
        ■ shape-subst (NF-inner eq) (s ++ᵗ bswapTel a w t′)
        ■ shape-++ᵗ s (bswapTel a w t′)
        ■ cong (shape s ++_) (shape-bswapTel a w t′) )
... | mkLoc1 u G₁ G₂ {t₀ = t₀} t≡ pre≡ Y≡ with t≡
... | refl
  with φν-split (syncFlags G₁ ++ syncFlags G₂) (runFlags w)
        ( cong (_++ BShape t₀) (map-sφ-++ (syncFlags G₁) (syncFlags G₂))
        ■ Y≡ )
        (BShape-headν t₀) (inj₂ (_ , refl))
... | fl₁ , X≡
  with locate-1 t₀ [] (shape a ++ shape t′) X≡
... | mkLoc1 u₂ A₁ A₂ {t₀ = t₂} t≡₂ pre≡₂ Y≡₂
  with BShape-[]ᵗ u₂ pre≡₂
... | refl , refl with t≡₂
... | refl
  with Y≡₂ ■ cong (_++ shape t′) (shape-run ra)
... | Y≡₂′
  with φν-split (syncFlags A₁ ++ syncFlags A₂) (runFlags ra)
        {X = BShape t₂} {Y = shape t′}
        ( cong (_++ BShape t₂) (map-sφ-++ (syncFlags A₁) (syncFlags A₂))
        ■ Y≡₂′ )
        (BShape-headν t₂) (Block-headν bt)
... | fl₂ , X≡₂
  with shape-det (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t′)))
        (BTel (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
           (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) _)
        ( shape-++ᵗ s (tν (a ++ᵗ tν (rb ++ᵗ t′)))
        ■ cong (λ z → shape s ++ (sν ∷ z))
            ( shape-++ᵗ a (tν (rb ++ᵗ t′))
            ■ cong₂ (λ y z → y ++ (sν ∷ z)) (shape-run ra)
                (shape-++ᵗ rb t′ ■ cong (_++ shape t′) (shape-run w)) )
        ■ sym
          ( shape-prenex-image
              (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                 (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) _
          ■ BShape-++ᵗᵗ u (tνᵗ A₁ A₂ (tνᵗ G₁ G₂
              (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))))
          ■ cong₂ (λ y z → y ++ (sν ∷ z)) pre≡
              ( cong₂ (λ y z → y ++ (sν ∷ z))
                  ( sym (map-sφ-++ (syncFlags A₁) (syncFlags A₂))
                  ■ cong (map sφ) fl₂ )
                  ( cong₂ _++_
                      ( sym (map-sφ-++ (syncFlags G₁) (syncFlags G₂))
                      ■ cong (map sφ) fl₁ )
                      ( BShape-⋯ᵗᵉˡ t₂ (assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))
                      ■ X≡₂ ) ) ) ) )
... | eqk , telPart =
  realised
    (u ++ᵗᵗ tνᵗ A₁ A₂ (tνᵗ G₁ G₂
       (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))))
    (map (_⋯ (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))) es)
    ( move-≋ u
        ( swapHead-≋ G₁ G₂ A₁ A₂ t₂ (parsᵗ es)
        ◅◅ ≡→≋ᵗ (cong
             (plugᵗ (tνᵗ A₁ A₂ (tνᵗ G₁ G₂
                (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))))
             (pars-⋯ₚᵗ es (t₂ ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))) ) )
    (≡→~ᵩ (mkNF-cong eqk telPart
      (coh u G₁ G₂ A₁ A₂ t₂ es σ s a ra w t′ bt es₁ pre≡ fl₁ fl₂ X≡₂ eq eqk)))

------------------------------------------------------------------------
-- The exact-image step, TOTAL over both orientations.  With this, the
-- only content of `RealiseStep` not delivered here is commuting a
-- nonempty `~ᵩ` gap past a block move.
------------------------------------------------------------------------

realise-step-exact :
  BswpThreadCoh → BswpThreadCohᵇ → FlipResidue →
  ∀ {m k p} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ p)
  {N N′ : NF p} → SymClosure _~ᵇ₁_ N N′ → N ≡ ImageOf t es p σ →
  Realised t es σ N′
realise-step-exact coh cohᵇ fl t es σ (fwd g) eq =
  realise-stepᶠ coh fl t es σ g eq
realise-step-exact coh cohᵇ fl t es σ (bwd (ν1ᵇ s v es₁)) eq =
  realise-stepᵇ-ν1 fl t es σ s v es₁ eq
realise-step-exact coh cohᵇ fl t es σ (bwd (φφᵇ s x y v es₁)) eq =
  realised t es ε (~ᵩ-trans (Eq*.return (φφᵩ s x y v es₁)) (≡→~ᵩ eq))
realise-step-exact coh cohᵇ fl t es σ (bwd (thrᵇ v perm)) eq =
  realised t es ε (~ᵩ-trans (Eq*.return (thrᵩ v perm)) (≡→~ᵩ eq))
realise-step-exact coh cohᵇ fl t es σ (bwd (delᵇ v es₁)) eq =
  realised t es ε (~ᵩ-trans (Eq*.return (delᵩ v es₁)) (≡→~ᵩ eq))
realise-step-exact coh cohᵇ fl t es σ (bwd (bswpᵇ s ra w bt es₁)) eq =
  realise-bswpᵇ cohᵇ t es σ s ra w bt es₁ eq
