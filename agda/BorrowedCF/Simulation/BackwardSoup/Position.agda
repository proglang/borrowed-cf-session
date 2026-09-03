-- | Phase 3 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §9, P3): TYPING FACTS ABOUT A LOCATED REDEX.
--
--   Everything in this module is typed-side metatheory; no soup notion
--   occurs anywhere.  `Locate.agda` (P1) turns a soup thread into a source
--   expression `e` sitting at the hole of a `ProcessContext`, and
--   `Inversion.agda` (P2) turns the soup redex into a source redex
--   `E [ K c ·¹ w ]*`.  What Phase 5 still needs is:
--
--     1. the argument of a handle-consuming constant is a VARIABLE
--        (`handle-value-var`) -- values of handle type are variables;
--     2. `Inversion.LetPairOnVariable` never happens for a located thread
--        (`letpair-var-untypable`): a variable of a channel context has a
--        handle type, and `T-LetPair` wants a `⊗`;
--     3. `send`'s argument is a PAIR, never a variable
--        (`pair-arg-not-var`), which discharges the side condition of
--        `Inversion.pair-arg-inversion`;
--     4. BINDER RESOLUTION: which `ν` on the path binds a given hole
--        variable, and where in that binder's group list the variable sits
--        (`Binder`, `resolve`, `binderSide`, `binderGroup`, `binderPos`);
--     5. the CRUX: for an impure handle-consuming constant the handle is
--        the head of the FIRST group of its side (`HeadOfFirstGroup`,
--        `ImpureRedexHead`);
--     6. `focusTyping-binders`, the `inv-ν` payload of the resolved binder,
--        which Phase 5 needs in order to rebuild `TP-Res`.
--
--   `GroupOrder.agda`, re-exported below, lifts the general lemmas that
--   `Examples/Probes2.agda` §0 established for its concrete probes:
--   `NoAcq`/`¬mobile-noAcq`, `bindCtx′-¬mobile`, and the `;`-order `before`
--   with its monotonicity `before-mono-≼`.  (It is a separate module because
--   the session-level `_⋯_` of `Types/Substitution.agda` cannot be in scope
--   together with the term-level `_⋯_` of `Terms/Base.agda`.)  `Probes2`
--   keeps its own copies -- it is left untouched -- and could be simplified
--   to import them from here.
--
--   The crux itself (`impure-redex-head : ImpureRedexHead`) is NOT proved in
--   this module: it lives in `Position/Crux.agda`, which carries clearly
--   marked holes.  This module loads with 0 goals; only the STATEMENT is
--   needed downstream.
module BorrowedCF.Simulation.BackwardSoup.Position where

open import Data.Nat.ListAction using (sum)
open import Data.List.Relation.Unary.All as Allᴸ using () renaming (All to Allᴸ)
import Data.Vec.Relation.Unary.All as Allⱽ
open import Relation.Binary.Construct.Closure.Symmetric as Sym
  using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (AllCx; MobCx; UnrCx)
open import BorrowedCF.Reduction.Base

import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.Support.Confine
  using (count; unrCx⇒count0; count-≈′; count-≈; count-wk-suc)
open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( ProcessContext; hole; par-left; par-right; bind
        ; plug; compose; plug-compose; focusTyping )

-- Section 0: the two levers, lifted out of `Examples/Probes2.agda` §0 into
-- `GroupOrder.agda` (which must not import the term syntax) and re-exported.
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder public

open 𝐓 using (BindGroup; BindCtx; BindCtx′; AcqHeadCtx; structBinder; structNSeq)
open 𝐓 using (last; cons-ret/acq; cons-acq; nil; cons)
open 𝐓 using (_;_⊢ₚ_; inv-ν; inv-∥; inv-⟪⟫; bindCtx⇒chanCtx)

open Bin using (_Respects_)
open Nat.Variables
open Variables
open Fin.Patterns

private
  variable
    x y : 𝔽 n
    α β : Struct n

------------------------------------------------------------------------
-- 1.  A value of handle type is a variable.

private
  const-not-handle : ∀ {c} {T : 𝕋} {s : 𝕊 0} → ⊢ c ∶ T → ¬ (T ≃ ⟨ s ⟩)
  const-not-handle `unit ()
  const-not-handle `discard ()
  const-not-handle `fork ()
  const-not-handle (`new _) ()
  const-not-handle (`lsplit _ _ _ _) ()
  const-not-handle (`rsplit _ _ _ _) ()
  const-not-handle `drop ()
  const-not-handle `acq ()
  const-not-handle (`send _) ()
  const-not-handle (`recv _) ()
  const-not-handle `select ()
  const-not-handle `branch ()
  const-not-handle `end ()

-- The `≃`-generalised form: `T-Conv` walks a chain of type equivalences, so
-- the induction needs `T ≃ ⟨ s ⟩` rather than `T ≡ ⟨ s ⟩`.
handle-value-var-≃ :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {w : Tm n} {T : 𝕋} {s : 𝕊 0} {ϵ} →
  Γ ; γ ⊢ w ∶ T ∣ ϵ → T ≃ ⟨ s ⟩ → Value w →
  Σ[ x ∈ 𝔽 n ] w ≡ ` x
handle-value-var-≃ (T-Const ⊢c) eq V-K = ⊥-elim (const-not-handle ⊢c eq)
handle-value-var-≃ (T-Var x _) eq V-` = x , refl
handle-value-var-≃ (T-Abs _ _ _) () V-λ
handle-value-var-≃ (T-AbsRec _ _ _) eq ()
handle-value-var-≃ (T-AppUnr _ _ _ _) eq ()
handle-value-var-≃ (T-AppLin _ _ _ _) eq ()
handle-value-var-≃ (T-AppLeft _ _ _ _) eq ()
handle-value-var-≃ (T-AppRight _ _ _ _) eq ()
handle-value-var-≃ (T-Pair _ _ _ _) () (V-⊗ _ _)
handle-value-var-≃ (T-Let _ _ _) eq ()
handle-value-var-≃ (T-Seq _ _ _) eq ()
handle-value-var-≃ (T-LetPair _ _ _) eq ()
handle-value-var-≃ (T-Inj _) () (V-⊕ _)
handle-value-var-≃ (T-Case _ _ _ _) eq ()
handle-value-var-≃ (T-Conv T≃ _ d) eq V = handle-value-var-≃ d (≃-trans T≃ eq) V
handle-value-var-≃ (T-Weaken _ d) eq V = handle-value-var-≃ d eq V

handle-value-var :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {w : Tm n} {s : 𝕊 0} {ϵ} →
  Γ ; γ ⊢ w ∶ ⟨ s ⟩ ∣ ϵ → Value w →
  Σ[ x ∈ 𝔽 n ] w ≡ ` x
handle-value-var ⊢w V = handle-value-var-≃ ⊢w ≃-refl V

------------------------------------------------------------------------
-- 2.  `let⊗` on a variable of a channel context is untypable.
--
-- This is what refutes `Inversion.LetPairOnVariable` for a LOCATED thread:
-- `Locate.focusExprTyping` supplies both the typing and the `ChanCx`.

private
  handle-not-pair :
    ∀ {n} {Γ : Ctx n} {x : 𝔽 n} {T₁ T₂ : 𝕋} {d} →
    ChanCx Γ → (Γ ﹫ x) ≃ T₁ ⊗⟨ d ⟩ T₂ → ⊥
  handle-not-pair {x = x} Γ-S eq with chanCx-lookup Γ-S x
  ... | _ , lookupEq with subst (_≃ _) lookupEq eq
  ...   | ()

letpair-var-untypable :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {E : Frame* n} {x : 𝔽 n}
    {body : Tm (2 + n)} {T ϵ} →
  ChanCx Γ → Γ ; γ ⊢ E [ `let⊗ (` x) `in body ]* ∶ T ∣ ϵ → ⊥
letpair-var-untypable {E = E} {x = x} {body = body} Γ-S ⊢plug
  with ⊢[]*⁻¹ E (`let⊗ (` x) `in body) ⊢plug
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole
  with inv-`let⊗ ⊢hole
...   | _ , _ , _ , _ , _ , _ , _ , ⊢var , _ =
  handle-not-pair Γ-S (arg-type ⊢var)

------------------------------------------------------------------------
-- 3.  `send`'s argument is a pair, never a variable.

private
  fn-send-dom : ∀ {n} {Γ : Ctx n} {β : Struct n} {Tᵈ U a ϵ} →
    Γ ; β ⊢ K `send ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Σ[ T ∈ 𝕋 ] (T ⊗¹ ⟨ msg ‼ T ⟩ ≃ Tᵈ)
  fn-send-dom (T-Const (`send {T = T} _)) = T , ≃-refl
  fn-send-dom (T-Conv (dom≃ `→ _) _ d) =
    let T , eq = fn-send-dom d in T , ≃-trans eq dom≃
  fn-send-dom (T-Weaken _ d) = fn-send-dom d

  send-var-⊥ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {d} {T ϵ} →
    ChanCx Γ → Γ ; γ ⊢ K `send ·⟨ d ⟩ (` x) ∶ T ∣ ϵ → ⊥
  send-var-⊥ Γ-S (T-AppUnr _ _ ⊢fn ⊢arg) =
    let _ , eq = fn-send-dom ⊢fn in
    handle-not-pair Γ-S (≃-trans (arg-type ⊢arg) (≃-sym eq))
  send-var-⊥ Γ-S (T-AppLin _ _ ⊢fn ⊢arg) =
    let _ , eq = fn-send-dom ⊢fn in
    handle-not-pair Γ-S (≃-trans (arg-type ⊢arg) (≃-sym eq))
  send-var-⊥ Γ-S (T-AppLeft _ _ ⊢fn ⊢arg) =
    let _ , eq = fn-send-dom ⊢fn in
    handle-not-pair Γ-S (≃-trans (arg-type ⊢arg) (≃-sym eq))
  send-var-⊥ Γ-S (T-AppRight _ _ ⊢fn ⊢arg) =
    let _ , eq = fn-send-dom ⊢fn in
    handle-not-pair Γ-S (≃-trans (arg-type ⊢arg) (≃-sym eq))
  send-var-⊥ Γ-S (T-Conv _ _ d) = send-var-⊥ Γ-S d
  send-var-⊥ Γ-S (T-Weaken _ d) = send-var-⊥ Γ-S d

pair-arg-not-var :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {w : Tm n} {T ϵ} →
  ChanCx Γ → Γ ; γ ⊢ K `send ·¹ w ∶ T ∣ ϵ →
  ((x : 𝔽 n) → w ≢ ` x)
pair-arg-not-var Γ-S ⊢app x refl = send-var-⊥ Γ-S ⊢app

------------------------------------------------------------------------
-- 4.  Binder resolution.
--
-- For a CLOSED process context `ctx : ProcessContext k 0` and a variable
-- `x : 𝔽 k` of the hole, `resolve` names the `bind B₁ B₂ ctx′` node on the
-- path that binds `x`, together with `x`'s index in that node's local scope
-- `𝔽 (sum B₁ + sum B₂)`.  `binderSide`, `binderGroup` and `binderPos` then
-- read off the endpoint, the group index and the offset inside the group.

private
  splitAt-inj₁ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {l : 𝔽 p} →
    Fin.splitAt p i ≡ inj₁ l → l ↑ˡ q ≡ i
  splitAt-inj₁ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  splitAt-inj₂ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {r : 𝔽 q} →
    Fin.splitAt p i ≡ inj₂ r → p ↑ʳ r ≡ i
  splitAt-inj₂ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

-- The renaming a process context performs on its ambient variables: every
-- `bind` on the path shifts them past its own binder groups.
weakenThrough : ProcessContext k n → 𝔽 n → 𝔽 k
weakenThrough hole y = y
weakenThrough (par-left ctx Q) y = weakenThrough ctx y
weakenThrough (par-right Q ctx) y = weakenThrough ctx y
weakenThrough (bind B₁ B₂ ctx) y = weakenThrough ctx ((sum B₁ + sum B₂) ↑ʳ y)

record Binder {k n : ℕ} (ctx : ProcessContext k n) (x : 𝔽 k) : Set where
  constructor binder
  field
    {mid}         : ℕ
    B₁ B₂         : BindGroup
    above         : ProcessContext mid n
    below         : ProcessContext k (sum B₁ + sum B₂ + mid)
    decomposition : ctx ≡ compose above (bind B₁ B₂ below)
    local         : 𝔽 (sum B₁ + sum B₂)
    index-eq      : weakenThrough below (local ↑ˡ mid) ≡ x

-- The recursive form: either a binder on the path binds `x`, or `x` comes
-- from the ambient scope (impossible when that scope is empty).
resolve′ :
  (ctx : ProcessContext k n) (x : 𝔽 k) →
  Binder ctx x ⊎ Σ[ y ∈ 𝔽 n ] weakenThrough ctx y ≡ x
resolve′ hole x = inj₂ (x , refl)
resolve′ (par-left ctx Q) x with resolve′ ctx x
... | inj₁ (binder C₁ C₂ above below dec loc ieq) =
  inj₁ (binder C₁ C₂ (par-left above Q) below
         (cong (λ z → par-left z Q) dec) loc ieq)
... | inj₂ found = inj₂ found
resolve′ (par-right Q ctx) x with resolve′ ctx x
... | inj₁ (binder C₁ C₂ above below dec loc ieq) =
  inj₁ (binder C₁ C₂ (par-right Q above) below
         (cong (par-right Q) dec) loc ieq)
... | inj₂ found = inj₂ found
resolve′ (bind A₁ A₂ ctx) x with resolve′ ctx x
... | inj₁ (binder C₁ C₂ above below dec loc ieq) =
  inj₁ (binder C₁ C₂ (bind A₁ A₂ above) below
         (cong (bind A₁ A₂) dec) loc ieq)
... | inj₂ (y , eq) with Fin.splitAt (sum A₁ + sum A₂) y in splitEq
...   | inj₁ loc =
  inj₁ (binder A₁ A₂ hole ctx refl loc
         (cong (weakenThrough ctx) (splitAt-inj₁ (sum A₁ + sum A₂) splitEq) ■ eq))
...   | inj₂ z =
  inj₂ (z , (cong (weakenThrough ctx) (splitAt-inj₂ (sum A₁ + sum A₂) splitEq) ■ eq))

-- A closed process has no ambient variables, so every hole variable is bound.
resolve : (ctx : ProcessContext k 0) (x : 𝔽 k) → Binder ctx x
resolve ctx x with resolve′ ctx x
... | inj₁ found = found
... | inj₂ (() , _)

------------------------------------------------------------------------
-- 4a.  Reading off side, group and position.

data BinderSide : Set where
  side₁ side₂ : BinderSide

-- Which endpoint of the channel a local index belongs to.
data SideOf (B₁ B₂ : BindGroup) : 𝔽 (sum B₁ + sum B₂) → Set where
  inl : (i : 𝔽 (sum B₁)) → SideOf B₁ B₂ (i ↑ˡ sum B₂)
  inr : (i : 𝔽 (sum B₂)) → SideOf B₁ B₂ (sum B₁ ↑ʳ i)

sideOf : (B₁ B₂ : BindGroup) (i : 𝔽 (sum B₁ + sum B₂)) → SideOf B₁ B₂ i
sideOf B₁ B₂ i with Fin.splitAt (sum B₁) i in splitEq
... | inj₁ l = subst (SideOf B₁ B₂) (splitAt-inj₁ (sum B₁) splitEq) (inl l)
... | inj₂ r = subst (SideOf B₁ B₂) (splitAt-inj₂ (sum B₁) splitEq) (inr r)

-- Which group of ONE endpoint's group list, and at which offset.  Stated as
-- an inductive family so that no `Fin.cast` along `sum-++` is ever needed
-- (`Local/SplitCommon.agda`'s `blockAt` is the injection this inverts).
data GroupOf : (B : BindGroup) → 𝔽 (sum B) → Set where
  head-group : ∀ {b} (B : BindGroup) (j : 𝔽 b) → GroupOf (b L.∷ B) (j ↑ˡ sum B)
  next-group : ∀ b {B} {i : 𝔽 (sum B)} → GroupOf B i → GroupOf (b L.∷ B) (b ↑ʳ i)

groupOf : (B : BindGroup) (i : 𝔽 (sum B)) → GroupOf B i
groupOf L.[] ()
groupOf (b L.∷ B) i with Fin.splitAt b i in splitEq
... | inj₁ j = subst (GroupOf (b L.∷ B)) (splitAt-inj₁ b splitEq) (head-group B j)
... | inj₂ r =
  subst (GroupOf (b L.∷ B)) (splitAt-inj₂ b splitEq) (next-group b (groupOf B r))

groupIndex : ∀ {B i} → GroupOf B i → ℕ
groupIndex (head-group _ _) = 0
groupIndex (next-group _ g) = suc (groupIndex g)

groupWidth : ∀ {B i} → GroupOf B i → ℕ
groupWidth (head-group {b} _ _) = b
groupWidth (next-group _ g) = groupWidth g

groupOffset : ∀ {B i} → GroupOf B i → ℕ
groupOffset (head-group _ j) = Fin.toℕ j
groupOffset (next-group _ g) = groupOffset g

-- The tail of the group list after the group containing the index.
groupRest : ∀ {B i} → GroupOf B i → BindGroup
groupRest (head-group B _) = B
groupRest (next-group _ g) = groupRest g

module _ {k n : ℕ} {ctx : ProcessContext k n} {x : 𝔽 k} (bnd : Binder ctx x) where
  open Binder bnd

  -- The group list of the endpoint that binds `x`.
  binderGroups : BindGroup
  binderGroups with sideOf B₁ B₂ local
  ... | inl _ = B₁
  ... | inr _ = B₂

  binderSide : BinderSide
  binderSide with sideOf B₁ B₂ local
  ... | inl _ = side₁
  ... | inr _ = side₂

  binderGroup : ℕ
  binderGroup with sideOf B₁ B₂ local
  ... | inl i = groupIndex (groupOf B₁ i)
  ... | inr i = groupIndex (groupOf B₂ i)

  binderPos : ℕ
  binderPos with sideOf B₁ B₂ local
  ... | inl i = groupOffset (groupOf B₁ i)
  ... | inr i = groupOffset (groupOf B₂ i)

  binderWidth : ℕ
  binderWidth with sideOf B₁ B₂ local
  ... | inl i = groupWidth (groupOf B₁ i)
  ... | inr i = groupWidth (groupOf B₂ i)

  binderRest : BindGroup
  binderRest with sideOf B₁ B₂ local
  ... | inl i = groupRest (groupOf B₁ i)
  ... | inr i = groupRest (groupOf B₂ i)

------------------------------------------------------------------------
-- 5.  The `inv-ν` payload of the resolved binder.
--
-- `Locate.focusTyping` carries a typing derivation down to the hole and
-- forgets everything it passed on the way.  Phase 5 has to REBUILD the
-- `TP-Res` node of the binder that owns the redex handle, so it needs that
-- node's payload: the `New s`, the two `⊢ᴮ`s, the two `BindCtx`s, and the
-- body typing with the structure `TP-Res` prescribes.

focusTyping-binders :
  ∀ {k mid n} (B₁ B₂ : BindGroup)
    (above : ProcessContext mid n)
    (below : ProcessContext k (sum B₁ + sum B₂ + mid))
    (Q : 𝐓.Proc k) {Γ : Ctx n} {γ : Struct n} →
  ChanCx Γ → Γ ; γ ⊢ₚ plug (compose above (bind B₁ B₂ below)) Q →
  Σ[ Γ′ ∈ Ctx mid ] Σ[ γ′ ∈ Struct mid ]
  Σ[ Γ₁ ∈ Ctx (sum B₁) ] Σ[ Γ₂ ∈ Ctx (sum B₂) ] Σ[ s ∈ 𝕊 0 ] Σ[ p ∈ Pol ]
    ChanCx Γ′
      × New s
      × 𝐓.⊢ᴮ B₁
      × 𝐓.⊢ᴮ B₂
      × BindCtx (s      ; end p)           B₁ Γ₁
      × BindCtx (dual s ; end (dualPol p)) B₂ Γ₂
      × ((Γ₁ ⸴* Γ₂) ⸴* Γ′
           ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
             ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
             ∥ (γ′ 𝐂.⋯ᵣ 𝐂.weaken* _)
         ⊢ₚ plug below Q)
focusTyping-binders B₁ B₂ above below Q {γ = γ} Γ-S ⊢P
  with focusTyping above (𝐓.ν B₁ B₂ (plug below Q)) Γ-S
         (subst (_ ; γ ⊢ₚ_) (plug-compose above (bind B₁ B₂ below) Q) ⊢P)
... | Γ′ , γ′ , Γ′-S , ⊢ν with inv-ν ⊢ν
...   | Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body =
  Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body

-- The same, addressed through a resolved `Binder`.
binderTyping :
  ∀ {k} {ctx : ProcessContext k 0} {x : 𝔽 k}
    (bnd : Binder ctx x) (Q : 𝐓.Proc k) →
  let open Binder bnd in
  [] ; [] ⊢ₚ plug ctx Q →
  Σ[ Γ′ ∈ Ctx mid ] Σ[ γ′ ∈ Struct mid ]
  Σ[ Γ₁ ∈ Ctx (sum B₁) ] Σ[ Γ₂ ∈ Ctx (sum B₂) ] Σ[ s ∈ 𝕊 0 ] Σ[ p ∈ Pol ]
    ChanCx Γ′
      × New s
      × 𝐓.⊢ᴮ B₁
      × 𝐓.⊢ᴮ B₂
      × BindCtx (s      ; end p)           B₁ Γ₁
      × BindCtx (dual s ; end (dualPol p)) B₂ Γ₂
      × ((Γ₁ ⸴* Γ₂) ⸴* Γ′
           ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
             ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
             ∥ (γ′ 𝐂.⋯ᵣ 𝐂.weaken* _)
         ⊢ₚ plug below Q)
binderTyping (binder B₁ B₂ above below dec loc ieq) Q ⊢P =
  focusTyping-binders B₁ B₂ above below Q Allⱽ.[]
    (subst (λ z → [] ; [] ⊢ₚ plug z Q) dec ⊢P)

------------------------------------------------------------------------
-- 6.  The `;`-order that a binder PRESCRIBES.
--
-- `structBinder` sequences the handles of ONE group (`structNSeq`) and puts
-- distinct groups in PARALLEL:
--
--     structBinder (b ∷ B) = (structNSeq b ⋯ᵣ wkʳ (sum B))
--                          ∥ (structBinder B ⋯ᵣ wkˡ b)
--
-- so the prescribed `;`-order relates exactly the handles of one group, in
-- increasing offset.  Together with `before-mono-≼` and "no first-group
-- handle is mobile" this is the general form of the per-probe `f*-before`
-- facts of `Examples/Probes2.agda`.

private
  ↑ʳ-inj : (p : ℕ) {q : ℕ} {i j : 𝔽 q} → p ↑ʳ i ≡ p ↑ʳ j → i ≡ j
  ↑ʳ-inj zero equal = equal
  ↑ʳ-inj (suc p) equal = ↑ʳ-inj p (Fin.suc-injective equal)

  count-⋯ᵣ :
    ∀ {m n} (γ : Struct m) (ρ : m →ᵣ n) → (∀ {i j} → ρ i ≡ ρ j → i ≡ j) →
    (z : 𝔽 m) → count (ρ z) (γ 𝐂.⋯ᵣ ρ) ≡ count z γ
  count-⋯ᵣ (` w) ρ inj z with ρ z Fin.≟ ρ w | z Fin.≟ w
  ... | yes _  | yes _ = refl
  ... | no  _  | no  _ = refl
  ... | yes eq | no ¬p = ⊥-elim (¬p (inj eq))
  ... | no ¬eq | yes p = ⊥-elim (¬eq (cong ρ p))
  count-⋯ᵣ [] ρ inj z = refl
  count-⋯ᵣ (α ∥ β) ρ inj z = cong₂ _+_ (count-⋯ᵣ α ρ inj z) (count-⋯ᵣ β ρ inj z)
  count-⋯ᵣ (α ; β) ρ inj z = cong₂ _+_ (count-⋯ᵣ α ρ inj z) (count-⋯ᵣ β ρ inj z)

  mem-⋯ᵣ :
    ∀ {m n} (γ : Struct m) (ρ : m →ᵣ n) (inj : ∀ {i j} → ρ i ≡ ρ j → i ≡ j)
      (z : 𝔽 m) → z ∈ₘ γ → ρ z ∈ₘ (γ 𝐂.⋯ᵣ ρ)
  mem-⋯ᵣ γ ρ inj z z∈ eq = z∈ (sym (count-⋯ᵣ γ ρ inj z) ■ eq)

  before-⋯ᵣ :
    ∀ {m n} (γ : Struct m) (ρ : m →ᵣ n) (inj : ∀ {i j} → ρ i ≡ ρ j → i ≡ j)
      {i j : 𝔽 m} → before i j γ → before (ρ i) (ρ j) (γ 𝐂.⋯ᵣ ρ)
  before-⋯ᵣ (` w) ρ inj ()
  before-⋯ᵣ [] ρ inj ()
  before-⋯ᵣ (α ∥ β) ρ inj (inj₁ b) = inj₁ (before-⋯ᵣ α ρ inj b)
  before-⋯ᵣ (α ∥ β) ρ inj (inj₂ b) = inj₂ (before-⋯ᵣ β ρ inj b)
  before-⋯ᵣ (α ; β) ρ inj (inj₁ (i∈ , j∈)) =
    inj₁ (mem-⋯ᵣ α ρ inj _ i∈ , mem-⋯ᵣ β ρ inj _ j∈)
  before-⋯ᵣ (α ; β) ρ inj (inj₂ (inj₁ b)) = inj₂ (inj₁ (before-⋯ᵣ α ρ inj b))
  before-⋯ᵣ (α ; β) ρ inj (inj₂ (inj₂ b)) = inj₂ (inj₂ (before-⋯ᵣ β ρ inj b))

  mem-wk : (γ : Struct n) (z : 𝔽 n) → z ∈ₘ γ → suc z ∈ₘ 𝐂.wk γ
  mem-wk γ z z∈ eq = z∈ (sym (count-wk-suc γ z) ■ eq)

  before-wk :
    (γ : Struct n) {i j : 𝔽 n} → before i j γ → before (suc i) (suc j) (𝐂.wk γ)
  before-wk (` w) ()
  before-wk [] ()
  before-wk (α ∥ β) (inj₁ b) = inj₁ (before-wk α b)
  before-wk (α ∥ β) (inj₂ b) = inj₂ (before-wk β b)
  before-wk (α ; β) (inj₁ (i∈ , j∈)) = inj₁ (mem-wk α _ i∈ , mem-wk β _ j∈)
  before-wk (α ; β) (inj₂ (inj₁ b)) = inj₂ (inj₁ (before-wk α b))
  before-wk (α ; β) (inj₂ (inj₂ b)) = inj₂ (inj₂ (before-wk β b))

-- Every variable occurs in its group's chain.
structNSeq-mem : ∀ {b} (j : 𝔽 b) → j ∈ₘ structNSeq b
structNSeq-mem zero = λ ()
structNSeq-mem {suc b} (suc j) =
  mem-seqR {α = ` zero} {𝐂.wk (structNSeq b)} (mem-wk (structNSeq b) j (structNSeq-mem j))

-- ... and the chain is ordered by the offset.
structNSeq-before :
  ∀ {b} (i j : 𝔽 b) → Fin.toℕ i Nat.< Fin.toℕ j → before i j (structNSeq b)
structNSeq-before {suc b} zero (suc j) lt =
  inj₁ ( (λ ())
       , mem-wk (structNSeq b) j (structNSeq-mem j) )
structNSeq-before {suc b} (suc i) (suc j) lt =
  inj₂ (inj₂ (before-wk (structNSeq b) (structNSeq-before i j (Nat.s≤s⁻¹ lt))))

-- THE BINDER ORDER.  Two handles of the SAME group of one endpoint are
-- `;`-ordered by their offsets in `structBinder`.
structBinder-before :
  ∀ (B : BindGroup) {i j : 𝔽 (sum B)} (g : GroupOf B i) (h : GroupOf B j) →
  groupIndex g ≡ groupIndex h → groupOffset g Nat.< groupOffset h →
  before i j (structBinder B)
structBinder-before (b L.∷ B) (head-group .B p) (head-group .B q) idx off =
  inj₁ (before-⋯ᵣ (structNSeq b) (𝐂.wkʳ (sum B))
         (λ {i} {j} eq → Fin.↑ˡ-injective (sum B) i j eq)
         (structNSeq-before p q off))
structBinder-before (b L.∷ B) (next-group .b g) (next-group .b h) idx off =
  inj₂ (before-⋯ᵣ (structBinder B) (𝐂.wkˡ b) (↑ʳ-inj b)
         (structBinder-before B g h (suc⁻¹ idx) off))

-- The index of the HEAD of a group, and the fact that it precedes every
-- other handle of that group.
groupHeadIx : ∀ {B i} → GroupOf B i → 𝔽 (sum B)
groupHeadIx (head-group B zero) = zero ↑ˡ sum B
groupHeadIx (head-group B (suc j)) = zero ↑ˡ sum B
groupHeadIx (next-group b g) = b ↑ʳ groupHeadIx g

groupHeadOf : ∀ {B i} (g : GroupOf B i) → GroupOf B (groupHeadIx g)
groupHeadOf (head-group B zero) = head-group B zero
groupHeadOf (head-group B (suc j)) = head-group B zero
groupHeadOf (next-group b g) = next-group b (groupHeadOf g)

groupHead-index : ∀ {B i} (g : GroupOf B i) → groupIndex (groupHeadOf g) ≡ groupIndex g
groupHead-index (head-group B zero) = refl
groupHead-index (head-group B (suc j)) = refl
groupHead-index (next-group b g) = cong suc (groupHead-index g)

groupHead-offset : ∀ {B i} (g : GroupOf B i) → groupOffset (groupHeadOf g) ≡ 0
groupHead-offset (head-group B zero) = refl
groupHead-offset (head-group B (suc j)) = refl
groupHead-offset (next-group b g) = groupHead-offset g

-- Step (ii)/(iii) of the crux, in its purely combinatorial half: a handle
-- that is NOT at offset 0 of its group has the group's head `;`-before it.
group-head-before :
  ∀ (B : BindGroup) {i : 𝔽 (sum B)} (g : GroupOf B i) →
  0 Nat.< groupOffset g →
  before (groupHeadIx g) i (structBinder B)
group-head-before B g 0<off =
  structBinder-before B (groupHeadOf g) g (groupHead-index g)
    (subst (Nat._< groupOffset g) (sym (groupHead-offset g)) 0<off)


-- NO HANDLE OF THE FIRST GROUP IS MOBILE.  The general form of
-- `Probes2.f1-first-group-¬mobile` / `f3a-¬mob0`: the first group's front
-- block sits over a `≃`-factor of the `New`-derived session `s ; end p`,
-- which has no `acq` (§1), and `bindCtx′-¬mobile` walks the block.
-- (`cons-acq`, the empty first group, has no handle to speak of.)
first-group-¬mobile :
  ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
  New s → BindCtx (s ; end p) B Γ →
  ∀ {i} (g : GroupOf B i) → groupIndex g ≡ 0 → ¬ Mobile (Γ ﹫ i)
first-group-¬mobile N (last C) {i} g idx =
  bindCtx′-¬mobile (new-end⇒noAcq N) C i
first-group-¬mobile {Γ = Γ} N (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front _ _)
  (head-group B′ q) idx =
  subst (λ T → ¬ Mobile T) (sym (V.lookup-++ˡ Γ₁ Γ₂ q))
    (bindCtx′-¬mobile (noAcq-front (new-end⇒noAcq N) s≃) front q)
first-group-¬mobile N (cons-acq C _) (head-group B′ ()) idx

------------------------------------------------------------------------
-- 7.  THE CRUX: an impure handle-consuming redex sits at the head of the
--     first group of its side.
--
-- The statements below are what Phase 5 consumes.  `Position/Crux.agda`
-- carries the proof attempt; this module states them only, so that it loads
-- with 0 goals.
--
-- Proof sketch (`Examples/Probes2.agda` §0 and §7, in general):
--
--  (i)   LINEARITY.  No handle is `Unr` (`¬unr-handle`), so `≼` preserves
--        `count` exactly (`count-≼-eq`): a thread cannot silently also hold
--        a handle it does not use.
--  (ii)  If `x` is not the head of the first group of its side, there is a
--        handle `x′` of the same side that the binder puts `;`-BEFORE `x`:
--        either the head of `x`'s own group (`group-head-before`) or a
--        handle of an earlier group.
--  (iii) SAME GROUP.  `structBinder` prescribes `x′ ; x`
--        (`structBinder-before`).  The body's derived structure can only put
--        `x′ ∥ x` (different threads) or `x ; x′` / `x ∥ x′` (same thread:
--        the redex hole is evaluated first, and by `Probes2` §7(e) the only
--        frames that place resources `;`-before the hole -- `app₁ v L` and
--        `v ⊗□` -- force the hole to be PURE, contradicting
--        `ImpureHandleConst`).  `before-mono-≼` says `≼` cannot repair that,
--        because turning `∥` into `;` needs `∥′-tm-;`, i.e. a MOBILE handle,
--        and `x′` is not mobile: a first-group handle is `NoAcq`
--        (`bindCtx′-¬mobile` over `noAcq-front`), and a non-first group's
--        NON-head handle carries no `acq` either -- the head carries it
--        (`AcqHeadCtx` plus the `cons-ret/acq` chain equation).
--  (iv)  EARLIER GROUP.  If `x`'s group is not the first, its head carries
--        the group's `acq` (`AcqHeadCtx` and `acq ; s₂ ≃ s₁ ; rest`, via the
--        head-atom lemmas `atom-;-unsnoc` / `atomKind≢⇒≄-;ʳ` of
--        `Types/Equivalence.agda`).  If `x` IS that head, its session
--        `acq ; …` cannot be what an impure constant consumes (`discard`
--        wants `⟨ skip ⟩`, `drop` wants `⟨ ret ⟩`, `send` wants
--        `⟨ msg ‼ T ⟩`, ... -- each `≄ acq ; s`).  If `x` is not the head,
--        case (iii) applies inside the group.

-- The IMPURE handle-consuming constants: exactly the constants of effect `𝕀`
-- whose typed reduction rule pins the handle to variable `0F` of the FIRST
-- group.  The PURE ones (`fork`, `new`, `lsplit`, `rsplit`, `acq`) may sit in
-- a delayed position, and their rules impose no position (`Probes2` §7(e)).
data ImpureHandleConst : Const → Set where
  `discard : ImpureHandleConst `discard
  `drop    : ImpureHandleConst `drop
  `send    : ImpureHandleConst `send
  `recv    : ImpureHandleConst `recv
  `select  : ∀ {i} → ImpureHandleConst (`select i)
  `branch  : ImpureHandleConst `branch
  `end     : ∀ {p} → ImpureHandleConst (`end p)

-- `x` is the head of the first group of the endpoint that binds it.
HeadOfFirstGroup :
  {k n : ℕ} {ctx : ProcessContext k n} {x : 𝔽 k} → Binder ctx x → Set
HeadOfFirstGroup bnd = (binderGroup bnd ≡ 0) × (binderPos bnd ≡ 0)

-- The metatheorem, for a handle that is the DIRECT argument of the constant
-- (`discard`, `drop`, `select`, `branch`, `end p`, and `recv`).
ImpureRedexHead : Set
ImpureRedexHead =
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {c : Const} {x : 𝔽 k} →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
  ImpureHandleConst c →
  HeadOfFirstGroup (resolve ctx x)

-- ... and for a handle that is the SECOND COMPONENT of the argument pair,
-- which is how `send` receives it (`RUS-Com` fires on `send ·¹ (v ⊗ 𝓒[ … ])`).
PairArgRedexHead : Set
PairArgRedexHead =
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {c : Const}
    {w : Tm k} {x : 𝔽 k} →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ →
  ImpureHandleConst c →
  HeadOfFirstGroup (resolve ctx x)

-- `drop` pins the shape of the first group as well: width 1, with a second
-- group behind it.  This is `Support/Theorems/DropShape.agda`'s `drop-shape`
-- (`b₁ ≡ 0` and `B₁ ≡ c₀ ∷ B′` for `ν (suc b₁ ∷ B₁) B₂`) freed from the
-- canonical position.
DropFirstGroupSingleton : Set
DropFirstGroupSingleton =
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {x : 𝔽 k} →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
  (binderWidth (resolve ctx x) ≡ 1) × (binderRest (resolve ctx x) ≢ L.[])

-- `acq` is the mirror image: `⊢ᴮ` forbids an empty group in non-first
-- position, so an acquiring handle is the head of the SECOND group and the
-- FIRST group is empty (PLAN.md §4, F4(c)).
AcqSecondGroupHead : Set
AcqSecondGroupHead =
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {x : 𝔽 k} →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ →
  (binderGroup (resolve ctx x) ≡ 1)
    × (binderPos (resolve ctx x) ≡ 0)
    × (binderGroups (resolve ctx x)
         ≡ 0 L.∷ binderWidth (resolve ctx x) L.∷ binderRest (resolve ctx x))
