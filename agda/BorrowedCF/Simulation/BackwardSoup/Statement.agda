-- | The refined BACKWARD simulation `UntypedSoup → Typed`: the statement.
--
--   `BackwardSoup/PLAN.md` §5 records that, once the strict group rules of
--   §6/§7 have removed the F4 counterexamples, exactly ONE obstacle to the
--   naive backward proposition survives: F3, the slot chosen by
--   `RUS-RSplit`.  The soup rule may insert its new sync boundary at ANY
--   position `k = length before` of the split endpoint's flag list, while
--   the typed rule `R-RSplit` fixes `k` to the number of binder groups that
--   precede the split one.  Locally the soup cannot see that number, so the
--   honest statement quotients configurations by a renumbering of the phi
--   slots of one endpoint.
--
--   This module
--     1. defines the generator of that quotient -- an ADJACENT TRANSPOSITION
--        of two slots of one endpoint, applied consistently to the endpoint's
--        flag list and to every thread (`swapSlot`, `swapPhi`, `swapFlags`),
--        each shown involutive;
--     2. packages it as a one-step relation `_≈¹_` on configurations and its
--        equivalence closure `_≈ˢ_`;
--     3. STATES the refined backward simulation `Backward-Sim` and the
--        auxiliary `Slot-Bisim` theorem that reduces it to the case where
--        the image is exact;
--     4. validates the definitions on the F3 example of
--        `Examples/Splits.agda`: the canonical and the wrong-slot `RUS-RSplit`
--        reducts are related by a SINGLE `_≈¹_` step;
--     5. records the proof plan (also appended to `PLAN.md` as §8).
--
--   `SlotBisim.agda` proves the auxiliary theorem; `Simulation.agda` combines
--   it with exact reflection and exports `backward-sim : Backward-Sim`.
module BorrowedCF.Simulation.BackwardSoup.Statement where

import Data.Fin.Properties as FinP

open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.World using (GlobalImage)

open Typed using (_;_⊢ₚ_)
open Soup using (Config; config; Channel; Thread; Flag; channels; threads; endpoint)
open SoupReduction using (endpointFlags; setEndpointFlags)
open SoupTerm
  using ( Tm; PhiRef
        ; `_; `phi; K; ƛ; μ; _·⟨_⟩_; _;_; _⊗_
        ; `let_`in_; `let⊗_`in_; `inj; `case_`of⟨_;_⟩
        )

open Nat using (_<_; z≤n; s≤s)
open Nat.Variables
open Fin.Patterns

private
  cong₃ :
    {A B C D : Set} (f : A → B → C → D) {a a′ : A} {b b′ : B} {c c′ : C} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- 1.  The adjacent slot transposition.
--
-- `swapSlot k` exchanges the slot numbers `k` and `suc k` and fixes every
-- other slot.  It is the smallest renumbering that repairs an `RUS-RSplit`
-- fired one position off, and iterating it reaches every renumbering that
-- the soup can produce (see the comment on `_≈ˢ_` below).

swapSlot : ℕ → ℕ → ℕ
swapSlot zero zero = suc zero
swapSlot zero (suc zero) = zero
swapSlot zero (suc (suc l)) = suc (suc l)
swapSlot (suc k) zero = zero
swapSlot (suc k) (suc l) = suc (swapSlot k l)

swapSlot-involutive : (k l : ℕ) → swapSlot k (swapSlot k l) ≡ l
swapSlot-involutive zero zero = refl
swapSlot-involutive zero (suc zero) = refl
swapSlot-involutive zero (suc (suc l)) = refl
swapSlot-involutive (suc k) zero = refl
swapSlot-involutive (suc k) (suc l) = cong suc (swapSlot-involutive k l)

-- Renumber the phi cells of ONE endpoint inside a thread.  Structurally this
-- is `SoupReduction.insertPhi` / `SoupReduction.consumePhi` with `insertSlot`
-- / `shiftSlot` replaced by `swapSlot`; in particular the endpoint address is
-- weakened when passing under an expression binder.

swapPhi : 𝔽 n → ℕ → Tm n → Tm n
swapPhi x k (` y) = ` y
swapPhi x k (`phi (y , l)) with x FinP.≟ y
... | no _ = `phi (y , l)
... | yes refl = `phi (x , swapSlot k l)
swapPhi x k (K c) = K c
swapPhi x k (ƛ e) = ƛ (swapPhi (suc x) k e)
swapPhi x k (μ e) = μ (swapPhi (suc x) k e)
swapPhi x k (e₁ ·⟨ d ⟩ e₂) = swapPhi x k e₁ ·⟨ d ⟩ swapPhi x k e₂
swapPhi x k (e₁ ; e₂) = swapPhi x k e₁ ; swapPhi x k e₂
swapPhi x k (e₁ ⊗ e₂) = swapPhi x k e₁ ⊗ swapPhi x k e₂
swapPhi x k (`let e₁ `in e₂) =
  `let swapPhi x k e₁ `in swapPhi (suc x) k e₂
swapPhi x k (`let⊗ e₁ `in e₂) =
  `let⊗ swapPhi x k e₁ `in swapPhi (suc (suc x)) k e₂
swapPhi x k (`inj i e) = `inj i (swapPhi x k e)
swapPhi x k (`case e `of⟨ e₁ ; e₂ ⟩) =
  `case swapPhi x k e
    `of⟨ swapPhi (suc x) k e₁ ; swapPhi (suc x) k e₂ ⟩

swapPhi-hit :
  (x : 𝔽 n) (k l : ℕ) →
  swapPhi x k (`phi (x , l)) ≡ `phi (x , swapSlot k l)
swapPhi-hit x k l with x FinP.≟ x
... | yes refl = refl
... | no apart = ⊥-elim (apart refl)

swapPhi-miss :
  {x y : 𝔽 n} → x ≢ y → (k l : ℕ) →
  swapPhi x k (`phi (y , l)) ≡ `phi (y , l)
swapPhi-miss {x = x} {y = y} apart k l with x FinP.≟ y
... | no _ = refl
... | yes same = ⊥-elim (apart same)

swapPhi-involutive :
  (x : 𝔽 n) (k : ℕ) (e : Tm n) → swapPhi x k (swapPhi x k e) ≡ e
swapPhi-involutive x k (` y) = refl
swapPhi-involutive x k (`phi (y , l)) with x FinP.≟ y
... | no apart = swapPhi-miss apart k l
... | yes refl =
  swapPhi-hit x k (swapSlot k l)
  ■ cong (λ z → `phi (x , z)) (swapSlot-involutive k l)
swapPhi-involutive x k (K c) = refl
swapPhi-involutive x k (ƛ e) = cong ƛ (swapPhi-involutive (suc x) k e)
swapPhi-involutive x k (μ e) = cong μ (swapPhi-involutive (suc x) k e)
swapPhi-involutive x k (e₁ ·⟨ d ⟩ e₂) =
  cong₂ (_·⟨ d ⟩_) (swapPhi-involutive x k e₁) (swapPhi-involutive x k e₂)
swapPhi-involutive x k (e₁ ; e₂) =
  cong₂ _;_ (swapPhi-involutive x k e₁) (swapPhi-involutive x k e₂)
swapPhi-involutive x k (e₁ ⊗ e₂) =
  cong₂ _⊗_ (swapPhi-involutive x k e₁) (swapPhi-involutive x k e₂)
swapPhi-involutive x k (`let e₁ `in e₂) =
  cong₂ `let_`in_ (swapPhi-involutive x k e₁) (swapPhi-involutive (suc x) k e₂)
swapPhi-involutive x k (`let⊗ e₁ `in e₂) =
  cong₂ `let⊗_`in_
    (swapPhi-involutive x k e₁) (swapPhi-involutive (suc (suc x)) k e₂)
swapPhi-involutive x k (`inj i e) =
  cong (`inj i) (swapPhi-involutive x k e)
swapPhi-involutive x k (`case e `of⟨ e₁ ; e₂ ⟩) =
  cong₃ `case_`of⟨_;_⟩
    (swapPhi-involutive x k e)
    (swapPhi-involutive (suc x) k e₁)
    (swapPhi-involutive (suc x) k e₂)

-- The same transposition on a flag list.  Out of range (a list shorter than
-- `suc k + 1`) it is the identity, which keeps `swapAt` total; `_≈¹_` below
-- rules that case out by a length premise.

swapAt : ℕ → List Flag → List Flag
swapAt k [] = []
swapAt zero (f ∷ []) = f ∷ []
swapAt zero (f₀ ∷ f₁ ∷ fs) = f₁ ∷ f₀ ∷ fs
swapAt (suc k) (f ∷ fs) = f ∷ swapAt k fs

swapAt-involutive : (k : ℕ) (fs : List Flag) → swapAt k (swapAt k fs) ≡ fs
swapAt-involutive k [] = refl
swapAt-involutive zero (f ∷ []) = refl
swapAt-involutive zero (f₀ ∷ f₁ ∷ fs) = refl
swapAt-involutive (suc k) (f ∷ fs) = cong (f ∷_) (swapAt-involutive k fs)

swapAt-length : (k : ℕ) (fs : List Flag) → L.length (swapAt k fs) ≡ L.length fs
swapAt-length k [] = refl
swapAt-length zero (f ∷ []) = refl
swapAt-length zero (f₀ ∷ f₁ ∷ fs) = refl
swapAt-length (suc k) (f ∷ fs) = cong suc (swapAt-length k fs)

swapFlags : 𝔽 2 → ℕ → Channel → Channel
swapFlags side k ch =
  setEndpointFlags side (swapAt k (endpointFlags ch side)) ch

endpointFlags-swapFlags :
  (side : 𝔽 2) (k : ℕ) (ch : Channel) →
  endpointFlags (swapFlags side k ch) side ≡ swapAt k (endpointFlags ch side)
endpointFlags-swapFlags 0F k (o , fs₀ , fs₁) = refl
endpointFlags-swapFlags 1F k (o , fs₀ , fs₁) = refl

swapFlags-involutive :
  (side : 𝔽 2) (k : ℕ) (ch : Channel) →
  swapFlags side k (swapFlags side k ch) ≡ ch
swapFlags-involutive 0F k (o , fs₀ , fs₁) =
  cong (λ z → o , z , fs₁) (swapAt-involutive k fs₀)
swapFlags-involutive 1F k (o , fs₀ , fs₁) =
  cong (λ z → o , fs₀ , z) (swapAt-involutive k fs₁)

------------------------------------------------------------------------
-- 2.  Slot-renumbering equivalence on configurations.
--
-- One generator: transpose the slots `k` and `suc k` of endpoint
-- `endpoint i side`, in the endpoint's flag list AND in every thread.  Both
-- slots must exist (`suc k < length …`), so the transposition really is a
-- bijection of the endpoint's slot names.

infix 4 _≈¹_ _≈ˢ_

data _≈¹_ {n m : ℕ} : Config n m → Config n m → Set where
  swap :
    (cs : Vec Channel n) (ts : Vec (Thread n) m)
    (i : 𝔽 n) (side : 𝔽 2) (k : ℕ) →
    suc k < L.length (endpointFlags (lookup cs i) side) →
    config cs ts ≈¹
      config (V.updateAt cs i (swapFlags side k))
             (V.map (swapPhi (endpoint i side) k) ts)

-- `_≈¹_` is already symmetric (see `≈¹-sym` below), so the equivalence
-- closure could equally be taken to be the reflexive-transitive closure
-- `Star _≈¹_`.  `EqClosure` is used to match the treatment of `_≋_` in
-- `Processes/Typed.agda`, and because the symmetry proof is not definitional
-- (it goes through the three involution lemmas).

_≈ˢ_ : Rel (Config n m) 0ℓ
_≈ˢ_ {n} {m} = EqClosure (_≈¹_ {n} {m})

≈¹-sym : {C D : Config n m} → C ≈¹ D → D ≈¹ C
≈¹-sym (swap cs ts i side k lt) = subst (config cs′ ts′ ≈¹_) targetEq base
  where
  x = endpoint i side
  cs′ = V.updateAt cs i (swapFlags side k)
  ts′ = V.map (swapPhi (endpoint i side) k) ts

  lenEq :
    L.length (endpointFlags (lookup cs′ i) side) ≡
    L.length (endpointFlags (lookup cs i) side)
  lenEq =
    cong (λ ch → L.length (endpointFlags ch side)) (V.lookup∘updateAt i cs)
    ■ cong L.length (endpointFlags-swapFlags side k (lookup cs i))
    ■ swapAt-length k (endpointFlags (lookup cs i) side)

  lt′ : suc k < L.length (endpointFlags (lookup cs′ i) side)
  lt′ = subst (suc k <_) (sym lenEq) lt

  base :
    config cs′ ts′ ≈¹
      config (V.updateAt cs′ i (swapFlags side k))
             (V.map (swapPhi x k) ts′)
  base = swap cs′ ts′ i side k lt′

  csEq : V.updateAt cs′ i (swapFlags side k) ≡ cs
  csEq =
    V.updateAt-updateAt i cs
    ■ V.updateAt-id-local i cs (swapFlags-involutive side k (lookup cs i))

  tsEq : V.map (swapPhi x k) ts′ ≡ ts
  tsEq =
    sym (V.map-∘ (swapPhi x k) (swapPhi x k) ts)
    ■ V.map-cong (swapPhi-involutive x k) ts
    ■ V.map-id ts

  targetEq :
    config (V.updateAt cs′ i (swapFlags side k)) (V.map (swapPhi x k) ts′) ≡
    config cs ts
  targetEq = cong₂ config csEq tsEq

≈¹⇒≈ˢ : {C D : Config n m} → C ≈¹ D → C ≈ˢ D
≈¹⇒≈ˢ = Eq*.return

≈ˢ-refl : {C : Config n m} → C ≈ˢ C
≈ˢ-refl {n} {m} = Eq*.reflexive (_≈¹_ {n} {m})

≈ˢ-sym : {C D : Config n m} → C ≈ˢ D → D ≈ˢ C
≈ˢ-sym {n} {m} = Eq*.symmetric (_≈¹_ {n} {m})

≈ˢ-trans : {C D E : Config n m} → C ≈ˢ D → D ≈ˢ E → C ≈ˢ E
≈ˢ-trans {n} {m} = Eq*.transitive (_≈¹_ {n} {m})

------------------------------------------------------------------------
-- 3.  The refined backward simulation.
--
-- Mirrors `ForwardSoup/Local.agda`'s `sim-global`: `P` is closed and well
-- typed under the STRICT rules of this branch (`Terms/Base.agda`'s
-- `` `lsplit ``/`` `rsplit `` with `¬ Skips` on both components,
-- `Processes/Typed.agda`'s `BindCtx` with `¬ Skips s₂` and `AcqHeadCtx`;
-- see PLAN.md §6-7), and `GlobalImage` already absorbs the failure modes F1
-- (dead channels after `RUS-Close`) and F2 (channel/thread placement).  What
-- `_≈ˢ_` adds is exactly F3: `C` need only be an image of `P` UP TO a
-- renumbering of the phi slots of the individual endpoints, and the reduct
-- `C′` is likewise only required to be such a renumbering of an image of the
-- typed reduct `P′`.
--
-- The type lives in `Set`, not `Set₁`: unlike `Local-Sim`, which quantifies
-- over the `Set`-valued ambient predicates `aC`/`aT`, everything quantified
-- here is an element of a `Set`.  (`Set₁` would need `--cumulativity`.)

Backward-Sim : Set
Backward-Sim =
  ∀ {P : Typed.Proc 0} {n m : ℕ} {C C₀ : Soup.Config n m}
    {n′ m′ : ℕ} {C′ : Soup.Config n′ m′} →
  [] ; Context.[] ⊢ₚ P →
  GlobalImage P C₀ →
  C₀ ≈ˢ C →
  C SoupReduction.─→ₚ C′ →
  Σ[ P′ ∈ Typed.Proc 0 ] (P TypedReduction.─→ₚ P′) ×
  Σ[ C₀′ ∈ Soup.Config n′ m′ ] GlobalImage P′ C₀′ × C₀′ ≈ˢ C′

-- Auxiliary theorem.  Every soup rule addresses slots only through the phi
-- NAMES it matches (`RUS-Drop`, `RUS-Acquire`, `RUS-RSplit` via
-- `L.length before`) and through the two global sweeps `consumePhi` /
-- `insertPhi`; none of them inspects the ORDER of an endpoint's slots.  So a
-- renumbering is a strong bisimulation for `_─→ₚ_`:

Slot-Bisim : Set
Slot-Bisim =
  ∀ {n m : ℕ} {C D : Soup.Config n m}
    {n′ m′ : ℕ} {C′ : Soup.Config n′ m′} →
  C ≈ˢ D →
  C SoupReduction.─→ₚ C′ →
  Σ[ D′ ∈ Soup.Config n′ m′ ] (D SoupReduction.─→ₚ D′) × C′ ≈ˢ D′

-- With `Slot-Bisim`, `Backward-Sim` reduces to the case `C₀ ≡ C`: transport
-- the given step `C ─→ₚ C′` back along `≈ˢ-sym` to a step `C₀ ─→ₚ C₀″` with
-- `C₀″ ≈ˢ C′`, solve the exact case, and compose the two `≈ˢ`s with
-- `≈ˢ-trans`.  Conversely `Slot-Bisim` is the only place where the
-- commutation of `swapPhi` with `consumePhi`, `insertPhi` and the frame
-- algebra is proved; the rest of `Backward-Sim` never sees `_≈¹_`
-- except for the one `RUS-RSplit` slot that the typed rule does not offer.

------------------------------------------------------------------------
-- 4.  Validation on the F3 example of `Examples/Splits.agda`.
--
-- `Crs′` is the reduct of the canonical `RUS-RSplit` on the interior handle
-- (`before = drop ∷ []`, so `k = 1`) and `Crs″` the reduct of the
-- non-canonical one (`before = []`, so `k = 0`).  `Examples/Splits.agda`
-- records that no typed reduct flattens to `Crs″` and that the two agree
-- after deleting the freshly inserted slot.  Here is the sharper statement:
-- they are ONE adjacent transposition apart, on endpoint `0F` / side `0F`
-- at position 0.  Both sides hold by `refl`: the flag lists are
-- `drop ∷ drop ∷ []` on either side (so the flag component of the swap is the
-- identity), and `swapPhi 0F 0` maps the canonical threads exactly onto the
-- wrong-slot ones.

open import BorrowedCF.Simulation.BackwardSoup.Examples.Splits
  using (Crs; Crs′; Crs″; step-rsplit-canonical; step-rsplit-wrong-k)

rsplit-wrong-k-is-a-swap : Crs′ ≈¹ Crs″
rsplit-wrong-k-is-a-swap =
  swap (channels Crs′) (threads Crs′) 0F 0F 0 (s≤s (s≤s z≤n))

rsplit-wrong-k-is-a-renumbering : Crs′ ≈ˢ Crs″
rsplit-wrong-k-is-a-renumbering = ≈¹⇒≈ˢ rsplit-wrong-k-is-a-swap

-- ... hence `Backward-Sim` covers the non-canonical soup step out of `Crs`:
-- its typed partner is `red-rsplit-interior : Prs ─→ₚ Prs′` and the exact
-- image is `Crs′ ≡ 𝑪 Prs′` (`rsplit-interior-exact-flatten`).
f3-instance :
  Σ[ C₀′ ∈ Soup.Config 1 2 ] (Crs SoupReduction.─→ₚ C₀′) × C₀′ ≈ˢ Crs″
f3-instance = Crs′ , step-rsplit-canonical , rsplit-wrong-k-is-a-renumbering

------------------------------------------------------------------------
-- 5.  Proof plan (mirrored as §8 of `BackwardSoup/PLAN.md`).
--
-- (a) TRANSLATION INVERSION.  The reverse of `T[_]-plugᶠ*`
--     (`ForwardSoup/Expressions.agda`): for a value environment `σ`
--     (`ValueEnv`), `T[ e ] σ ≡ F [ K c ·¹ v ]*` implies `e ≡ E [ K c ·¹ w ]*`
--     with `Tᶠ*[ E ] Vσ ≡ F` and `T[ w ] σ ≡ v`.  Induction on `E`/`F` after
--     an inversion of `T[_]` on the head constructor; `σ` being a value
--     environment is what stops a variable from masquerading as a redex.
--     One instance per soup rule (`fork`, `new`, `lsplit`, `rsplit`, `drop`,
--     `acq`, `discard`, `end ‼/⁇`, `send`, `recv`, `select`, `branch`), plus
--     the `⋯→` inversion for `RUS-Exp` (already witnessed by
--     `Examples/Exp.agda`).  Reusable: `Expressions.agda`'s frame algebra,
--     `++ₛ-Value`, `UB-Value`.
--
-- (b) IMAGE INVERSION.  A non-garbage thread of `C₀` is
--     `lookup (proj₂ (flattenOriented P lc σ)) j` for a UNIQUE `j`, i.e. it is
--     the translation of a subterm `⟪ e ⟫` of `P` under its `ν`-binders, with
--     the environment `bindEnv B₁ B₂ channel …` built along the path.  The
--     forward development already provides the pieces in the other direction
--     (`LocalImage/Bind.agda`'s `res-split-image`,
--     `LocalImage/Parallel.agda`'s `par-split-left/right`); what is new is
--     that the thread INDEX determines the path, which follows from the
--     injectivity of the thread embedding (`LocalImage/Embedding.agda`).
--
-- (c) TYPED POSITION FACTS.  The strict rules of PLAN.md §6-7 make the typed
--     leaf rules complete for the soup's leaves:
--       * Drop/Discard: `drop-shape` (`Support/Theorems/DropShape.agda`)
--         together with `BindCtx`'s `¬ Skips s₂` shows the handle carrying a
--         `phi` at slot `L.length before` with `before ≡ []` is variable `0F`
--         of a NON-EMPTY first group, i.e. exactly `R-Drop`/`R-Discard`.
--       * Acquire: `⊢ᴮ` (`Allᴸ NonZero (L.drop 1 B)`) forbids an empty group
--         in non-first position, so an `acq` flag at slot `k` forces `k = 0`
--         and a first group of width `0`, i.e. `R-Acq` (PLAN.md §4, F4(c)).
--       * `AcqHeadCtx` supplies the missing premise of `cons-ret/acq` /
--         `cons-acq` when the group list is rebuilt after the step.
--     PLAN.md §7 records the two ex-counterexamples `Pf4`/`Pf4b` as checked
--     refutations of precisely these premises (`Examples/Probes.agda`).
--
-- (d) PER-RULE CONSTRUCTION.  For each soup rule, (a)+(b) produce the source
--     redex, (c) its typed position, and `P′` is the corresponding typed
--     reduct.  `R-Bind`/`R-Par` descend to the redex's position; the only use
--     of `R-Struct` is `∥-comm` when the redex sits in the RIGHT component of
--     a `_∥_` (and for `RUS-Com`/`RUS-Choice`, whose two partners may come in
--     either order -- both orders are already checked in `Examples/Sync.agda`).
--     No `≋` is needed for the IMAGE, because `GlobalImage` quantifies over
--     the channel placement (`logicalChannels`) and the thread embedding
--     (F1/F2 of PLAN.md §2).  `GlobalImage P′ C₀′` is then obtained by
--     applying the FORWARD leaf lemma of `ForwardSoup/Local/*.agda`
--     (`U-fork-local`, `U-new-local`, `U-lsplit-local`, `U-rsplit-local`,
--     `U-drop-local`, `U-discard-local`, `U-acq-local`, `U-close-local`,
--     `U-com-local`, `U-choice-local`, `U-exp-local`) to the typed step just
--     constructed: the leaf produces EXACTLY the soup step's configuration at
--     the canonical slot.  `_≈ˢ_` absorbs the one non-canonical
--     `RUS-RSplit` slot, and `Slot-Bisim` the renumbering that `C₀ ≈ˢ C`
--     already carried.
--
-- (e) SIZE.  Comparable to the forward proof: (a) and (b) are the two new
--     inversion lemmas and carry most of the weight; (c) is a handful of
--     lemmas about `BindCtx`/`⊢ᴮ`; (d) is a fourteen-case dispatcher that
--     REUSES the forward leaves wholesale instead of reproving them.
--     `Slot-Bisim` is an independent, self-contained induction over the
--     eleven soup rules, needing `swapPhi`'s commutation with `consumePhi`,
--     `insertPhi`, `_[_]*` and `_⋯ᵣ_` -- the exact analogues of
--     `Local/InsertSupport.agda` and `Local/AcqSupport.agda`, which are the
--     templates to copy.
