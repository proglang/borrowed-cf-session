-- | Foundation for the realisation layer (Normal.Realise): every `~ᵇ` move on
--   an image block form is realised by a TYPED structural congruence.
--
--   This module supplies the two ingredients that need no new theory:
--
--   * the TYPED move layer — adjacent-node transposition (`swapHead-≋`, from
--     `ν-comm′`), endpoint flip (`flipHead-≋`, from `ν-swap′`), thread
--     permutation (`pars-↭ᵗ`, the typed mirror of Normal.Flat's `pars-↭`) and
--     spent-unit deletion (`unit-delᵗ`), each stated on prenex data and lifted
--     to arbitrary telescope positions by `move-≋`;
--
--   * the SHAPE calculus — a `Tel` carries no data besides its binder sequence
--     and flags, so a telescope is determined by its base scope and its
--     `shape` (`shape-det`).  All telescope coherences between Factor's block
--     moves (`bswapTel`) and the image telescope `BTel` therefore reduce to
--     LIST equations on shapes, which is how Normal.Realise proves them
--     without a single scope transport.  The locator `locate-1` inverts a
--     shape-level block position back to a typed telescope decomposition.
module BorrowedCF.Simulation.Support.Normal.RealiseBase where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Processes.Untyped using (Flag)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; []; tν; tφ; _++ᵗ_; NF; mkNF; tel; thr; inner)
open import BorrowedCF.Simulation.Support.Normal.Image
  using (Slot; sν; sφ; shape; shape-subst; shape-++ᵗ; φTel; φTelᵣ; scope≡;
         syncFlags; shape-φTel)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift1; shift2)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
  using (Run; rnil; rφ; Block; bnil; bν)
open import BorrowedCF.Simulation.Support.Normal.Factor
  using (dragTel; bswapTel)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BTel; BScope; Bσ; BShape; blockShape; shape-prenex-image)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; prep; swap) renaming (refl to ↭refl; trans to ↭tr)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)

open Nat.Variables

------------------------------------------------------------------------
-- The typed move layer.
------------------------------------------------------------------------

-- Spent-unit deletion: definitionally `∥-unitˡ`.
unit-delᵗ : ∀ {n} {es : List (Tm n)} → parsᵗ (K `unit ∷ es) ≋ parsᵗ es
unit-delᵗ = ∥-unitˡ

-- Thread permutation, the typed mirror of Normal.Flat's `pars-↭`.
pars-↭ᵗ : ∀ {n} {xs ys : List (Tm n)} → xs ↭ ys → parsᵗ xs ≋ parsᵗ ys
pars-↭ᵗ ↭refl        = ε
pars-↭ᵗ (prep x p)   = ∥-cong ε (pars-↭ᵗ p)
pars-↭ᵗ (swap x y p) = ∥-assoc ◅◅ ∥-cong ∥-comm (pars-↭ᵗ p) ◅◅ ≋ᵗ-sym ∥-assoc
pars-↭ᵗ (↭tr p q)    = pars-↭ᵗ p ◅◅ pars-↭ᵗ q

-- The two thread moves, lifted under an arbitrary telescope.
pars-↭-≋ᵗ : ∀ {n k} (t : TTel n k) {xs ys : List (Tm k)} → xs ↭ ys →
            plugᵗ t (parsᵗ xs) ≋ plugᵗ t (parsᵗ ys)
pars-↭-≋ᵗ t p = plug-congᵗ t (pars-↭ᵗ p)

unit-del-≋ᵗ : ∀ {n k} (t : TTel n k) {es : List (Tm k)} →
              plugᵗ t (parsᵗ (K `unit ∷ es)) ≋ plugᵗ t (parsᵗ es)
unit-del-≋ᵗ t = plug-congᵗ t unit-delᵗ

-- A move under a telescope prefix: whatever holds of the pluggings holds
-- after prefixing both sides by the same outer telescope.
move-≋ : ∀ {m p k k′} (u : TTel m p) {t : TTel p k} {t′ : TTel p k′}
         {X : Proc k} {X′ : Proc k′} →
         plugᵗ t X ≋ plugᵗ t′ X′ →
         plugᵗ (u ++ᵗᵗ t) X ≋ plugᵗ (u ++ᵗᵗ t′) X′
move-≋ u {t} {t′} {X} {X′} c =
  ≡→≋ᵗ (plug-++ᵗᵗ u t X) ◅◅ plug-congᵗ u c ◅◅ ≋ᵗ-sym (≡→≋ᵗ (plug-++ᵗᵗ u t′ X′))

-- Adjacent-node transposition at the head of a telescope, from `ν-comm′`.
-- The tail telescope is renamed with the transport-free `_⋯ᵗᵉˡ_`, so the
-- statement needs no arithmetic.
swapHead-≋ :
  ∀ {n k} (B₁ B₂ A₁ A₂ : BindGroup)
    (t : TTel (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n)) k) (X : Proc k) →
  plugᵗ (tνᵗ B₁ B₂ (tνᵗ A₁ A₂ t)) X
    ≋ plugᵗ (tνᵗ A₁ A₂ (tνᵗ B₁ B₂
              (t ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))))
            (X ⋯ₚ (t ↑ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))
swapHead-≋ B₁ B₂ A₁ A₂ t X =
  ν-comm {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = plugᵗ t X}
    ◅◅ ν-cong (ν-cong (≡→≋ᵗ
         (plug-⋯ₚᵗ t X (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))))

-- Endpoint flip (B₁ ↔ B₂) at the head of a telescope, from `ν-swap′`.
flipHead-≋ :
  ∀ {n k} (B₁ B₂ : BindGroup) (t : TTel (sum B₁ + sum B₂ + n) k) (X : Proc k) →
  plugᵗ (tνᵗ B₁ B₂ t) X
    ≋ plugᵗ (tνᵗ B₂ B₁ (t ⋯ᵗᵉˡ swapᵣ (sum B₁) (sum B₂)))
            (X ⋯ₚ (t ↑ᵗᵉˡ swapᵣ (sum B₁) (sum B₂)))
flipHead-≋ B₁ B₂ t X =
  ν-swap {B₁ = B₁} {B₂ = B₂} {P = plugᵗ t X}
    ◅◅ ν-cong (≡→≋ᵗ (plug-⋯ₚᵗ t X (swapᵣ (sum B₁) (sum B₂))))

------------------------------------------------------------------------
-- NF equality plumbing.
------------------------------------------------------------------------

NF-inner : ∀ {n} {N M : NF n} → N ≡ M → inner N ≡ inner M
NF-inner refl = refl

NF-tel : ∀ {n} {N M : NF n} (eq : N ≡ M) →
         subst (Tel n) (NF-inner eq) (tel N) ≡ tel M
NF-tel refl = refl

NF-thr : ∀ {n} {N M : NF n} (eq : N ≡ M) →
         subst (List ∘ Tm) (NF-inner eq) (thr N) ≡ thr M
NF-thr refl = refl

mkNF-cong : ∀ {n k₁ k₂} (eq : k₁ ≡ k₂) {t₁ : Tel n k₁} {t₂ : Tel n k₂}
            {e₁ : List (Tm k₁)} {e₂ : List (Tm k₂)} →
            subst (Tel n) eq t₁ ≡ t₂ → subst (List ∘ Tm) eq e₁ ≡ e₂ →
            mkNF t₁ e₁ ≡ mkNF t₂ e₂
mkNF-cong refl refl refl = refl

------------------------------------------------------------------------
-- Slot-list injectivity.
------------------------------------------------------------------------

private
  sφ-inj : ∀ {f g : Flag} → sφ f ≡ sφ g → f ≡ g
  sφ-inj refl = refl

map-sφ-++ : ∀ (xs ys : List Flag) →
            map sφ (xs ++ ys) ≡ map sφ xs ++ map sφ ys
map-sφ-++ []       ys = refl
map-sφ-++ (x ∷ xs) ys = cong (sφ x ∷_) (map-sφ-++ xs ys)

------------------------------------------------------------------------
-- A telescope is determined by its base scope and its shape.
------------------------------------------------------------------------

shape-det : ∀ {n k₁ k₂} (t₁ : Tel n k₁) (t₂ : Tel n k₂) →
            shape t₁ ≡ shape t₂ →
            Σ[ eq ∈ k₁ ≡ k₂ ] subst (Tel n) eq t₁ ≡ t₂
shape-det []        []        _  = refl , refl
shape-det []        (tν t₂)   ()
shape-det []        (tφ f t₂) ()
shape-det (tν t₁)   []        ()
shape-det (tν t₁)   (tφ f t₂) ()
shape-det (tφ f t₁) []        ()
shape-det (tφ f t₁) (tν t₂)   ()
shape-det (tν t₁)   (tν t₂)   eq with shape-det t₁ t₂ (L.∷-injectiveʳ eq)
... | refl , refl = refl , refl
shape-det (tφ f t₁) (tφ g t₂) eq with shape-det t₁ t₂ (L.∷-injectiveʳ eq)
... | refl , refl = refl , cong (λ h → tφ h t₁) (sφ-inj (L.∷-injectiveˡ eq))

------------------------------------------------------------------------
-- Runs: flags, uniqueness, closure properties.
------------------------------------------------------------------------

runFlags : ∀ {n k} {r : Tel n k} → Run r → List Flag
runFlags rnil           = []
runFlags (rφ {f = f} w) = f ∷ runFlags w

shape-run : ∀ {n k} {r : Tel n k} (w : Run r) → shape r ≡ map sφ (runFlags w)
shape-run rnil           = refl
shape-run (rφ {f = f} w) = cong (sφ f ∷_) (shape-run w)

run-unique : ∀ {n k} {r : Tel n k} (w₁ w₂ : Run r) → w₁ ≡ w₂
run-unique rnil     rnil     = refl
run-unique (rφ w₁) (rφ w₂) = cong rφ (run-unique w₁ w₂)

run-subst : ∀ {n k k′} (eq : k ≡ k′) {t : Tel n k} → Run t →
            Run (subst (Tel n) eq t)
run-subst refl w = w

Run-++ᵗ : ∀ {n k j} {r₁ : Tel n k} {r₂ : Tel k j} →
          Run r₁ → Run r₂ → Run (r₁ ++ᵗ r₂)
Run-++ᵗ rnil     w₂ = w₂
Run-++ᵗ (rφ w₁) w₂ = rφ (Run-++ᵗ w₁ w₂)

Run-φTelᵣ : ∀ (B : BindGroup) (n : ℕ) → Run (φTelᵣ B n)
Run-φTelᵣ []              n = rnil
Run-φTelᵣ (_ ∷ [])        n = rnil
Run-φTelᵣ (b ∷ B@(_ ∷ _)) n = rφ (Run-φTelᵣ B (suc n))

Run-φTel : ∀ (B : BindGroup) (n : ℕ) → Run (φTel B n)
Run-φTel B n = run-subst (scope≡ B n) (Run-φTelᵣ B n)

Block-BTel : ∀ {a b} (t : TTel a b) (n : ℕ) → Block (BTel t n)
Block-BTel []ᵗ           n = bnil
Block-BTel (tνᵗ B₁ B₂ t) n = bν

------------------------------------------------------------------------
-- Shapes of shifts, drags, and block swaps.
------------------------------------------------------------------------

shape-shift1 : ∀ {n j} (s : Tel n j) → shape (shift1 s) ≡ shape s
shape-shift1 []       = refl
shape-shift1 (tν s)   = cong (sν   ∷_) (shape-shift1 s)
shape-shift1 (tφ f s) = cong (sφ f ∷_) (shape-shift1 s)

shape-shift2 : ∀ {n j} (s : Tel n j) → shape (shift2 s) ≡ shape s
shape-shift2 []       = refl
shape-shift2 (tν s)   = cong (sν   ∷_) (shape-shift2 s)
shape-shift2 (tφ f s) = cong (sφ f ∷_) (shape-shift2 s)

shape-dragTel : ∀ {p j m k} (S : Tel p j) {r : Tel j m} (w : Run r)
                (t : Tel m k) →
                shape (dragTel S w t) ≡ map sφ (runFlags w) ++ (shape S ++ shape t)
shape-dragTel S rnil t = shape-++ᵗ S t
shape-dragTel S (rφ {f = f} w) t =
  cong (sφ f ∷_)
    ( shape-dragTel (shift1 S) w t
    ■ cong (λ z → map sφ (runFlags w) ++ (z ++ shape t)) (shape-shift1 S) )

shape-bswapTel : ∀ {n i m k} (a : Tel (2 + n) i) {rb : Tel (2 + i) m}
                 (w : Run rb) (t : Tel m k) →
                 shape (bswapTel a w t)
                   ≡ sν ∷ (map sφ (runFlags w) ++ (sν ∷ (shape a ++ shape t)))
shape-bswapTel a w t =
  cong (sν ∷_)
    ( shape-dragTel (tν (shift2 a)) w t
    ■ cong (λ z → map sφ (runFlags w) ++ (sν ∷ (z ++ shape t))) (shape-shift2 a) )

------------------------------------------------------------------------
-- BShape under concatenation and telescope renaming.
------------------------------------------------------------------------

BShape-++ᵗᵗ : ∀ {a b c} (u : TTel a b) (v : TTel b c) →
              BShape (u ++ᵗᵗ v) ≡ BShape u ++ BShape v
BShape-++ᵗᵗ []ᵗ           v = refl
BShape-++ᵗᵗ (tνᵗ B₁ B₂ u) v =
  cong (blockShape B₁ B₂ ++_) (BShape-++ᵗᵗ u v)
    ■ sym (L.++-assoc (blockShape B₁ B₂) (BShape u) (BShape v))

BShape-⋯ᵗᵉˡ : ∀ {n k m} (t : TTel n k) (ρ : n →ᵣ m) →
              BShape (t ⋯ᵗᵉˡ ρ) ≡ BShape t
BShape-⋯ᵗᵉˡ []ᵗ           ρ = refl
BShape-⋯ᵗᵉˡ (tνᵗ B₁ B₂ t) ρ =
  cong (blockShape B₁ B₂ ++_) (BShape-⋯ᵗᵉˡ t (ρ ↑* (sum B₁ + sum B₂)))

------------------------------------------------------------------------
-- Head views: a shape starts with a ν slot or is empty.
------------------------------------------------------------------------

headν : List Slot → Set
headν X = (X ≡ []) ⊎ (Σ[ ys ∈ List Slot ] X ≡ sν ∷ ys)

BShape-headν : ∀ {a b} (t : TTel a b) → headν (BShape t)
BShape-headν []ᵗ           = inj₁ refl
BShape-headν (tνᵗ B₁ B₂ t) = inj₂ (_ , refl)

Block-headν : ∀ {n k} {t : Tel n k} → Block t → headν (shape t)
Block-headν bnil = inj₁ refl
Block-headν bν   = inj₂ (_ , refl)

------------------------------------------------------------------------
-- List-level locators.
------------------------------------------------------------------------

-- A φ-run prefix on the left of a ν slot is contained in the position prefix.
eat-run : ∀ (fs : List Flag) {rest pre Y : List Slot} →
          map sφ fs ++ rest ≡ pre ++ sν ∷ Y →
          Σ[ pre′ ∈ List Slot ] (pre ≡ map sφ fs ++ pre′) × (rest ≡ pre′ ++ sν ∷ Y)
eat-run []       {pre = pre} eq = pre , refl , eq
eat-run (f ∷ fs) {pre = []}  ()
eat-run (f ∷ fs) {pre = sν ∷ pre} ()
eat-run (f ∷ fs) {pre = sφ h ∷ pre} eq with eat-run fs (L.∷-injectiveʳ eq)
... | pre′ , pre-eq , t-eq =
  pre′ , cong₂ _∷_ (cong sφ (sym (sφ-inj (L.∷-injectiveˡ eq)))) pre-eq , t-eq

-- Two φ-run-then-ν-headed splittings of one list coincide.
φν-split : ∀ (xs ys : List Flag) {X Y : List Slot} →
           map sφ xs ++ X ≡ map sφ ys ++ Y → headν X → headν Y →
           (xs ≡ ys) × (X ≡ Y)
φν-split []       []       eq hX hY = refl , eq
φν-split []       (y ∷ ys) () (inj₁ refl)       _
φν-split []       (y ∷ ys) () (inj₂ (_ , refl)) _
φν-split (x ∷ xs) []       () _ (inj₁ refl)
φν-split (x ∷ xs) []       () _ (inj₂ (_ , refl))
φν-split (x ∷ xs) (y ∷ ys) eq hX hY
  with φν-split xs ys (L.∷-injectiveʳ eq) hX hY
... | xs≡ys , X≡Y = cong₂ _∷_ (sφ-inj (L.∷-injectiveˡ eq)) xs≡ys , X≡Y

------------------------------------------------------------------------
-- The locator: a shape-level ν position inverts to a typed decomposition.
------------------------------------------------------------------------

record Loc1 {m k : ℕ} (t : TTel m k) (pre Y : List Slot) : Set where
  constructor mkLoc1
  field
    {j}   : ℕ
    u     : TTel m j
    G₁ G₂ : BindGroup
    {t₀}  : TTel (sum G₁ + sum G₂ + j) k
    t≡    : t ≡ u ++ᵗᵗ tνᵗ G₁ G₂ t₀
    pre≡  : BShape u ≡ pre
    Y≡    : (map sφ (syncFlags G₁) ++ map sφ (syncFlags G₂)) ++ BShape t₀ ≡ Y

open Loc1 public

locate-1 : ∀ {m k} (t : TTel m k) (pre Y : List Slot) →
           BShape t ≡ pre ++ sν ∷ Y → Loc1 t pre Y
locate-1 []ᵗ [] Y ()
locate-1 []ᵗ (x ∷ pre) Y ()
locate-1 (tνᵗ B₁ B₂ t) [] Y eq =
  mkLoc1 []ᵗ B₁ B₂ refl refl (L.∷-injectiveʳ eq)
locate-1 (tνᵗ B₁ B₂ t) (sφ h ∷ pre) Y ()
locate-1 (tνᵗ B₁ B₂ t) (sν ∷ pre) Y eq
  with eat-run (syncFlags B₁ ++ syncFlags B₂)
        ( cong (_++ BShape t) (map-sφ-++ (syncFlags B₁) (syncFlags B₂))
        ■ L.∷-injectiveʳ eq )
...   | pre′ , pre-eq , t-eq with locate-1 t pre′ Y t-eq
...     | mkLoc1 u C₁ C₂ t≡ pre≡ Y≡ =
  mkLoc1 (tνᵗ B₁ B₂ u) C₁ C₂ (cong (tνᵗ B₁ B₂) t≡)
    (cong (sν ∷_)
      ( cong ((map sφ (syncFlags B₁) ++ map sφ (syncFlags B₂)) ++_) pre≡
      ■ cong (_++ pre′) (sym (map-sφ-++ (syncFlags B₁) (syncFlags B₂)))
      ■ sym pre-eq ))
    Y≡
