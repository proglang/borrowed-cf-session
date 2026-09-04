-- | Phase 4 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §9, P4): THE CANONICAL FORM.
--
--   `Locate.agda` (P1) presents a well-typed closed process as
--   `plug ctx ⟪ e ⟫`, and `Position.agda` (P3) names the `ν` that binds the
--   redex handle (`Binder`, `resolve`).  The typed reduction rules of
--   `Reduction/Processes/Typed.agda`, however, only fire when the thread is
--   the LEFT component of a `∥` sitting DIRECTLY under its own binder.
--   This module bridges the two with `_≋_`:
--
--     * `bubble`, the ∥-normalisation: every `par-left` / `par-right` node
--       between the binder and the thread is absorbed into a RESIDUAL
--       process, which `ν-ext′` pushes under the binders on the way
--       (`foldPar`);
--     * `push`, the binder extrusion: the binding `ν B₁ B₂` is commuted
--       (`ν-comm′`) past every `ν` that `bubble` collected, so that it ends
--       up innermost, with the collected binders forming the new context
--       ABOVE it;
--     * `canon`, which combines the two into
--
--          plug ctx ⟪ e ⟫ ≋ plug above′ (ν B₁ B₂ (⟪ e ⋯ ρ ⟫ ∥ Q))
--
--       together with `x-eq : ρ x ≡ local ↑ˡ mid`, i.e. the redex handle
--       lands on the SAME local index of the binder it started at;
--     * `canon-swap`, the side exchange (`ν-swap′`), for a handle bound by
--       the second endpoint;
--     * `canon-typing`, the transport of the typing derivation along
--       `≋` (`Processes/Congruence.agda`'s `_/_⊢-≋_`);
--     * the RULE-SHAPED corollaries `canon-discard` / `canon-drop`
--       (§9, with the strengthening of `Support/HeadConfine.agda`),
--       `canon-acq` (§10) and `canon-lsplit` / `canon-rsplit` (§11).
--       Each produces literally the left-hand side of its typed rule under
--       an arbitrary process context, so that Phase 5 only has to apply
--       `R-Struct` / `R-Bind` / `R-Par`.  The pair rules (`R-Com`,
--       `R-Choice`, `R-Close`) need TWO threads and live in
--       `Canonical/../CanonicalPair.agda`.
--
--   The rearrangement itself is purely structural: `bubble`, `push`, `canon`
--   and `canon-swap` need no typing derivation.  Typing enters only in
--   `canon-typing` and in the discard/drop strengthening.
module BorrowedCF.Simulation.BackwardSoup.Canonical where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Relation.Unary.All as Allⱽ using () renaming (All to Allⱽ)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)

open import BorrowedCF.Simulation.Support.Frames using (frame-plug₁)
open import BorrowedCF.Simulation.Support.HeadConfine
  using (HeadConfined; discard-confine; drop-confine)

open import BorrowedCF.Simulation.BackwardSoup.Locate
open import BorrowedCF.Simulation.BackwardSoup.Position

open 𝐓 using (BindGroup; _;_⊢ₚ_)

open Nat.Variables
open Fin.Patterns


------------------------------------------------------------------------
-- 0.  `≋` housekeeping.
--
-- `≋-sym`, `≡→≋` and `≋-plug` now live at the end of `Locate.agda`, which
-- this module opens above, so that `Tracks.agda` can reason about the very
-- same derivations without depending on this module.

------------------------------------------------------------------------
-- 1.  Bind stacks.
--
-- A `BindList` is a `ProcessContext` all of whose nodes are `bind`s.  It is
-- kept as a plain list (rather than as a `ProcessContext` with a predicate)
-- because its arity is then a FUNCTION of the base arity, so a renaming of
-- the base lifts to a renaming of the stack's scope (`liftL`) and the base
-- variables inject into it (`wkL`).

BindList : Set
BindList = List (BindGroup × BindGroup)

arity : BindList → ℕ → ℕ
arity L.[] n = n
arity ((B₁ , B₂) L.∷ bs) n = arity bs (sum B₁ + sum B₂ + n)

plugL : (bs : BindList) {n : ℕ} → 𝐓.Proc (arity bs n) → 𝐓.Proc n
plugL L.[] P = P
plugL ((B₁ , B₂) L.∷ bs) P = 𝐓.ν B₁ B₂ (plugL bs P)

ctxL : (bs : BindList) {n : ℕ} → ProcessContext (arity bs n) n
ctxL L.[] = hole
ctxL ((B₁ , B₂) L.∷ bs) = bind B₁ B₂ (ctxL bs)

plug-ctxL :
  (bs : BindList) {n : ℕ} (P : 𝐓.Proc (arity bs n)) →
  plug (ctxL bs) P ≡ plugL bs P
plug-ctxL L.[] P = refl
plug-ctxL ((B₁ , B₂) L.∷ bs) P = cong (𝐓.ν B₁ B₂) (plug-ctxL bs P)

-- The injection of the base scope into the stack's scope: exactly the
-- weakening that `ν-ext′` performs, iterated.
wkL : (bs : BindList) {n : ℕ} → n →ᵣ arity bs n
wkL L.[] y = y
wkL ((B₁ , B₂) L.∷ bs) y = wkL bs (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂) y)

-- The lifting of a base renaming through the stack.
liftL : (bs : BindList) {m n : ℕ} → (m →ᵣ n) → arity bs m →ᵣ arity bs n
liftL L.[] ϕ = ϕ
liftL ((B₁ , B₂) L.∷ bs) ϕ = liftL bs (ϕ ↑* (sum B₁ + sum B₂))

plugL-⋯ :
  (bs : BindList) {m n : ℕ} (P : 𝐓.Proc (arity bs m)) (ϕ : m →ᵣ n) →
  plugL bs P 𝐓.⋯ₚ ϕ ≡ plugL bs (P 𝐓.⋯ₚ liftL bs ϕ)
plugL-⋯ L.[] P ϕ = refl
plugL-⋯ ((B₁ , B₂) L.∷ bs) P ϕ =
  cong (𝐓.ν B₁ B₂) (plugL-⋯ bs P (ϕ ↑* (sum B₁ + sum B₂)))

liftL-wkL :
  (bs : BindList) {m n : ℕ} (ϕ : m →ᵣ n) (y : 𝔽 m) →
  liftL bs ϕ (wkL bs y) ≡ wkL bs (ϕ y)
liftL-wkL L.[] ϕ y = refl
liftL-wkL ((B₁ , B₂) L.∷ bs) ϕ y =
  liftL-wkL bs (ϕ ↑* (sum B₁ + sum B₂)) (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂) y)
  ■ cong (wkL bs) (sym (↑*-wk ⦃ Kᵣ ⦄ ϕ (sum B₁ + sum B₂) y))

≋-plugL :
  (bs : BindList) {n : ℕ} {P Q : 𝐓.Proc (arity bs n)} →
  P 𝐓.≋ Q → plugL bs P 𝐓.≋ plugL bs Q
≋-plugL L.[] eq = eq
≋-plugL ((B₁ , B₂) L.∷ bs) eq = 𝐓.ν-cong (≋-plugL bs eq)

------------------------------------------------------------------------
-- 2.  `ν-ext′`, iterated: absorbing a sibling into a bind stack.

foldPar :
  (bs : BindList) {n : ℕ} (X : 𝐓.Proc (arity bs n)) (Z₀ : 𝐓.Proc n) →
  (plugL bs X 𝐓.∥ Z₀) 𝐓.≋ plugL bs (X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL bs))
foldPar L.[] X Z₀ =
  subst (λ z → (X 𝐓.∥ Z₀) 𝐓.≋ (X 𝐓.∥ z))
    (sym (𝐓.⋯ₚ-id≗ Z₀ {ϕ = wkL L.[]} (λ _ → refl))) ≋-refl
foldPar ((A₁ , A₂) L.∷ bs) X Z₀ =
  subst
    (λ z →
      (𝐓.ν A₁ A₂ (plugL bs X) 𝐓.∥ Z₀) 𝐓.≋ 𝐓.ν A₁ A₂ (plugL bs (X 𝐓.∥ z)))
    (𝐓.fusionₚ Z₀ (weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (wkL bs)
      ■ 𝐓.⋯ₚ-cong Z₀ (λ _ → refl))
    (𝐓.∥-comm
     ◅◅ (fwd 𝐓.ν-ext′ ◅ ≋-refl)
     ◅◅ 𝐓.ν-cong 𝐓.∥-comm
     ◅◅ 𝐓.ν-cong
          (foldPar bs X (Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂))))

------------------------------------------------------------------------
-- 3.  ∥-bubbling: the thread to the front, the siblings into a residual.

record Bubble {k n : ℕ} (c : ProcessContext k n) : Set where
  constructor bubbled
  field
    binds : BindList
    ρ     : k →ᵣ arity binds n
    resid : 𝐓.Proc (arity binds n)
    ≋-eq  : (Z₀ : 𝐓.Proc k) →
            plug c Z₀ 𝐓.≋ plugL binds ((Z₀ 𝐓.⋯ₚ ρ) 𝐓.∥ resid)
    amb   : (y : 𝔽 n) → ρ (weakenThrough c y) ≡ wkL binds y

bubble : (c : ProcessContext k n) → Bubble c
bubble hole = bubbled L.[] (λ y → y) 𝐓.⟪ K `unit ⟫
  (λ Z₀ →
    subst (λ z → Z₀ 𝐓.≋ (z 𝐓.∥ 𝐓.⟪ K `unit ⟫))
      (sym (𝐓.⋯ₚ-id≗ Z₀ {ϕ = λ y → y} (λ _ → refl)))
      (≋-sym 𝐓.∥-unitʳ))
  (λ y → refl)
bubble (par-left c R₀) with bubble c
... | bubbled bs ρ Q eq amb =
  bubbled bs ρ (Q 𝐓.∥ (R₀ 𝐓.⋯ₚ wkL bs))
    (λ Z₀ →
      𝐓.∥-cong (eq Z₀) ≋-refl
      ◅◅ foldPar bs ((Z₀ 𝐓.⋯ₚ ρ) 𝐓.∥ Q) R₀
      ◅◅ ≋-plugL bs (≋-sym 𝐓.∥-assoc))
    amb
bubble (par-right R₀ c) with bubble c
... | bubbled bs ρ Q eq amb =
  bubbled bs ρ (Q 𝐓.∥ (R₀ 𝐓.⋯ₚ wkL bs))
    (λ Z₀ →
      𝐓.∥-cong ≋-refl (eq Z₀)
      ◅◅ 𝐓.∥-comm
      ◅◅ foldPar bs ((Z₀ 𝐓.⋯ₚ ρ) 𝐓.∥ Q) R₀
      ◅◅ ≋-plugL bs (≋-sym 𝐓.∥-assoc))
    amb
bubble (bind A₁ A₂ c) with bubble c
... | bubbled bs ρ Q eq amb =
  bubbled ((A₁ , A₂) L.∷ bs) ρ Q
    (λ Z₀ → 𝐓.ν-cong (eq Z₀))
    (λ y →
      amb ((sum A₁ + sum A₂) ↑ʳ y)
      ■ cong (wkL bs) (sym (weaken*~wkˡ ⦃ Kᵣ ⦄ (sum A₁ + sum A₂) y)))

------------------------------------------------------------------------
-- 4.  `ν-comm′`, iterated: pushing the binder past a bind stack.

private
  -- `assocSwapᵣ` on a variable of the SECOND block that belongs to the
  -- binder's own scope: the block moves to the front, the index is kept.
  assocSwap-mid :
    ∀ p w {n} (v : 𝔽 w) →
    assocSwapᵣ p w {n} (p ↑ʳ (v ↑ˡ n)) ≡ v ↑ˡ (p + n)
  assocSwap-mid p w {n} v
    rewrite Fin.splitAt-↑ʳ p (w + n) (v ↑ˡ n)
          | Fin.splitAt-↑ˡ w v n = refl

push :
  (bs : BindList) (B₁ B₂ : BindGroup) {mid : ℕ}
  (T : 𝐓.Proc (arity bs (sum B₁ + sum B₂ + mid))) →
  Σ[ σ ∈ (arity bs (sum B₁ + sum B₂ + mid) →ᵣ
            (sum B₁ + sum B₂ + arity bs mid)) ]
    ((𝐓.ν B₁ B₂ (plugL bs T) 𝐓.≋ plugL bs (𝐓.ν B₁ B₂ (T 𝐓.⋯ₚ σ)))
     × ((v : 𝔽 (sum B₁ + sum B₂)) →
          σ (wkL bs (v ↑ˡ mid)) ≡ v ↑ˡ arity bs mid))
push L.[] B₁ B₂ T =
  (λ y → y)
  , subst (λ z → 𝐓.ν B₁ B₂ T 𝐓.≋ 𝐓.ν B₁ B₂ z)
      (sym (𝐓.⋯ₚ-id≗ T {ϕ = λ y → y} (λ _ → refl))) ≋-refl
  , (λ v → refl)
push ((A₁ , A₂) L.∷ bs) B₁ B₂ {mid} T
  with push bs B₁ B₂ {sum A₁ + sum A₂ + mid}
         (T 𝐓.⋯ₚ liftL bs (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))
... | σ′ , ≋′ , hnd =
  (λ y → σ′ (liftL bs (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)) y))
  , (subst
      (λ z →
        𝐓.ν B₁ B₂ (𝐓.ν A₁ A₂ (plugL bs T)) 𝐓.≋
        𝐓.ν A₁ A₂ (plugL bs (𝐓.ν B₁ B₂ z)))
      (𝐓.fusionₚ T
         (liftL bs (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))) σ′
       ■ 𝐓.⋯ₚ-cong T (λ _ → refl))
      ((fwd 𝐓.ν-comm′ ◅ ≋-refl)
       ◅◅ 𝐓.ν-cong
            (𝐓.ν-cong
              (≡→≋ (plugL-⋯ bs T
                (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))))
       ◅◅ 𝐓.ν-cong ≋′))
  , (λ v →
      cong σ′
        (liftL-wkL bs (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))
           (weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂) (v ↑ˡ mid))
         ■ cong (wkL bs)
             (cong (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))
                (weaken*~wkˡ ⦃ Kᵣ ⦄ (sum A₁ + sum A₂) (v ↑ˡ mid))
              ■ assocSwap-mid (sum A₁ + sum A₂) (sum B₁ + sum B₂) v))
      ■ hnd v)

------------------------------------------------------------------------
-- 5.  The canonical form.
--
-- `Canon P e x C₁ C₂ hloc` says: `P` is `≋`-equal to a process in which the
-- thread `⟪ e ⟫` -- renamed by the accumulated `ρ` -- is the LEFT component
-- of a `∥` directly under the binder `ν C₁ C₂`, everything else having been
-- pushed either ABOVE that binder (`above′`, a `ProcessContext`) or into the
-- residual `resid`; and the redex handle sits at the binder's local index
-- `hloc`.  This is exactly the shape the typed reduction rules match on.

record Canon {k : ℕ} (P : 𝐓.Proc 0) (e : Tm k) (x : 𝔽 k)
             (C₁ C₂ : BindGroup) (hloc : 𝔽 (sum C₁ + sum C₂)) : Set where
  constructor canonical
  field
    {midᶜ}  : ℕ
    above′  : ProcessContext midᶜ 0
    ρ       : k →ᵣ (sum C₁ + sum C₂ + midᶜ)
    resid   : 𝐓.Proc (sum C₁ + sum C₂ + midᶜ)
    ≋-canon : P 𝐓.≋
              plug above′ (𝐓.ν C₁ C₂ (𝐓.⟪ e ⋯ ρ ⟫ 𝐓.∥ resid))
    x-eq    : ρ x ≡ hloc ↑ˡ midᶜ

-- The construction.  The binder's own groups and local index are kept -- no
-- reordering of the binder happens here (see `canon-swap` for that).
canon :
  {ctx : ProcessContext k 0} (e : Tm k) {x : 𝔽 k} (bnd : Binder ctx x) →
  Canon (plug ctx 𝐓.⟪ e ⟫) e x
    (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
canon {ctx = ctx} e (binder B₁ B₂ above below dec loc ieq)
  with bubble below
... | bubbled bs ρ₀ Q eq amb
  with push bs B₁ B₂ (𝐓.⟪ e ⋯ ρ₀ ⟫ 𝐓.∥ Q)
...  | σ , ≋push , hnd =
  canonical (compose above (ctxL bs))
    (λ y → σ (ρ₀ y)) (Q 𝐓.⋯ₚ σ)
    (≡→≋ (cong (λ z → plug z 𝐓.⟪ e ⟫) dec
          ■ plug-compose above (bind B₁ B₂ below) 𝐓.⟪ e ⟫)
     ◅◅ ≋-plug above (𝐓.ν-cong (eq 𝐓.⟪ e ⟫) ◅◅ ≋push)
     ◅◅ ≡→≋
          (cong
             (λ w →
               plug above
                 (plugL bs (𝐓.ν B₁ B₂ (𝐓.⟪ w ⟫ 𝐓.∥ (Q 𝐓.⋯ₚ σ)))))
             (fusion e ρ₀ σ ■ ⋯-cong e (λ _ → refl))
           ■ cong (plug above)
               (sym (plug-ctxL bs
                 (𝐓.ν B₁ B₂
                   (𝐓.⟪ e ⋯ (λ y → σ (ρ₀ y)) ⟫ 𝐓.∥ (Q 𝐓.⋯ₚ σ)))))
           ■ sym (plug-compose above (ctxL bs)
               (𝐓.ν B₁ B₂
                 (𝐓.⟪ e ⋯ (λ y → σ (ρ₀ y)) ⟫ 𝐓.∥ (Q 𝐓.⋯ₚ σ))))))
    (cong σ (cong ρ₀ (sym ieq) ■ amb (loc ↑ˡ _)) ■ hnd loc)

canon-typing :
  {ctx : ProcessContext k 0} {e : Tm k} {x : 𝔽 k}
  {C₁ C₂ : BindGroup} {hloc : 𝔽 (sum C₁ + sum C₂)}
  (cn : Canon (plug ctx 𝐓.⟪ e ⟫) e x C₁ C₂ hloc) →
  let open Canon cn in
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ e ⟫ →
  [] ; [] ⊢ₚ plug above′ (𝐓.ν C₁ C₂ (𝐓.⟪ e ⋯ ρ ⟫ 𝐓.∥ resid))
canon-typing cn ⊢P = Allⱽ.[] / ⊢P ⊢-≋ Canon.≋-canon cn

------------------------------------------------------------------------
-- 6.  `ν-swap′`: exchanging the two endpoints of the canonical binder.

private
  swapr-cross : ∀ p q {n} (v : 𝔽 (p + q)) →
    swapᵣ p q {n} (v ↑ˡ n) ≡ Fin.swap p v ↑ˡ n
  swapr-cross p q {n} v rewrite Fin.splitAt-↑ˡ (p + q) v n = refl

  swap-↑ʳ : ∀ p {q} (v : 𝔽 q) → Fin.swap p (p ↑ʳ v) ≡ v ↑ˡ p
  swap-↑ʳ p {q} v rewrite Fin.splitAt-↑ʳ p q v = refl

-- The handle moves from side 2 to side 1 (and back).
canon-swap :
  {P : 𝐓.Proc 0} {e : Tm k} {x : 𝔽 k}
  {C₁ C₂ : BindGroup} {hloc : 𝔽 (sum C₁ + sum C₂)} →
  Canon P e x C₁ C₂ hloc →
  Canon P e x C₂ C₁ (Fin.swap (sum C₁) hloc)
canon-swap {e = e} {C₁ = C₁} {C₂ = C₂} {hloc = hloc}
  (canonical above′ ρ resid ≋c xeq) =
  canonical above′
    (λ y → swapᵣ (sum C₁) (sum C₂) (ρ y))
    (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂))
    (≋c
     ◅◅ ≋-plug above′ (fwd 𝐓.ν-swap′ ◅ ≋-refl)
     ◅◅ ≡→≋
          (cong
            (λ w →
              plug above′
                (𝐓.ν C₂ C₁
                  (𝐓.⟪ w ⟫ 𝐓.∥ (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))))
            (fusion e ρ (swapᵣ (sum C₁) (sum C₂))
             ■ ⋯-cong e (λ _ → refl))))
    (cong (swapᵣ (sum C₁) (sum C₂)) xeq
     ■ swapr-cross (sum C₁) (sum C₂) hloc)

------------------------------------------------------------------------
-- 7.  The head-of-the-first-group shape.
--
-- `Position/Crux.agda` proves `HeadOfFirstGroup (resolve ctx x)` for every
-- impure handle-consuming redex.  `HeadShape` is the same information in a
-- form the canonical construction can pattern-match on: the binder's group
-- list has a NON-EMPTY first group and the handle is its head.

data FirstHead : (B : BindGroup) → 𝔽 (sum B) → Set where
  first-head : ∀ b (B′ : BindGroup) → FirstHead (suc b L.∷ B′) 0F

group-first-head :
  ∀ {B : BindGroup} {i : 𝔽 (sum B)} (g : GroupOf B i) →
  groupIndex g ≡ 0 → groupOffset g ≡ 0 → FirstHead B i
group-first-head (head-group {b = suc b} B′ zero) _ _ = first-head b B′
group-first-head (head-group {b = suc b} B′ (suc j)) _ ()

data HeadShape : (B₁ B₂ : BindGroup) → 𝔽 (sum B₁ + sum B₂) → Set where
  head-l : ∀ b (B′ B₂ : BindGroup) → HeadShape (suc b L.∷ B′) B₂ 0F
  head-r : ∀ (B₁ : BindGroup) b (B′ : BindGroup) →
           HeadShape B₁ (suc b L.∷ B′) (sum B₁ ↑ʳ 0F)

-- `HeadOfFirstGroup` is stated with the `with`-defined projections
-- `binderGroup` / `binderPos`; this is the view it induces.
headOfFirstGroup⇒shape :
  {ctx : ProcessContext k 0} {x : 𝔽 k} (bnd : Binder ctx x) →
  HeadOfFirstGroup bnd →
  HeadShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
headOfFirstGroup⇒shape (binder B₁ B₂ above below dec loc ieq) hd
  with sideOf B₁ B₂ loc | hd
... | inl i | grp , pos with group-first-head (groupOf B₁ i) grp pos
...   | first-head b B′ = head-l b B′ B₂
headOfFirstGroup⇒shape (binder B₁ B₂ above below dec loc ieq) hd
    | inr i | grp , pos with group-first-head (groupOf B₂ i) grp pos
...   | first-head b B′ = head-r B₁ b B′

------------------------------------------------------------------------
-- 8.  The rule-shaped canonical form: handle at `0F` of a non-empty first
--     group of the FIRST endpoint.  This is the left-hand side that
--     `R-Discard`, `R-Drop` and (after the `zero ∷_` refinement) `R-Acq`
--     match on, modulo the strengthening of `E` and the residual.

record CanonHead {k : ℕ} (P : 𝐓.Proc 0) (e : Tm k) (x : 𝔽 k) : Set where
  constructor canonHead
  field
    {midʰ}  : ℕ
    bh      : ℕ
    D₁ D₂   : BindGroup
    above′  : ProcessContext midʰ 0
    ρ       : k →ᵣ (sum (suc bh L.∷ D₁) + sum D₂ + midʰ)
    resid   : 𝐓.Proc (sum (suc bh L.∷ D₁) + sum D₂ + midʰ)
    ≋-canon : P 𝐓.≋
              plug above′
                (𝐓.ν (suc bh L.∷ D₁) D₂ (𝐓.⟪ e ⋯ ρ ⟫ 𝐓.∥ resid))
    x-eq    : ρ x ≡ 0F

canon-head :
  {ctx : ProcessContext k 0} (e : Tm k) {x : 𝔽 k} (bnd : Binder ctx x) →
  HeadShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  CanonHead (plug ctx 𝐓.⟪ e ⟫) e x
canon-head e bnd (head-l b B′ D₂) with canon e bnd
... | canonical ab ρ Q ≋c xeq = canonHead b B′ D₂ ab ρ Q ≋c xeq
canon-head e bnd (head-r D₁ b B′) with canon-swap (canon e bnd)
... | canonical {midᶜ = m₀} ab ρ Q ≋c xeq =
  canonHead b B′ D₁ ab ρ Q ≋c
    (xeq ■ cong (λ z → z ↑ˡ m₀) (swap-↑ʳ (sum D₁) {sum (suc b L.∷ B′)} 0F))

------------------------------------------------------------------------
-- 9.  The rule-shaped corollaries: `R-Discard` and `R-Drop`.
--
-- `CanonRedex P c` is LITERALLY the left-hand side of `R-Discard` (`c ≡
-- `discard`) / `R-Drop` (`c ≡ `drop`), sitting under an arbitrary process
-- context: the redex thread is the left component of a `∥` directly under
-- its own binder, the handle is variable `0F` of a non-empty first group,
-- and both the frame and the residual are weakenings that do not mention it.
-- `R-Struct ≋-redex (R-Bind* (R-Discard …)) …` is then immediate.

private
  plug*-⋯ᵣ : {m n′ : ℕ} (E : Frame* m) (t : Tm m) (ρ : m →ᵣ n′) →
    (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
  plug*-⋯ᵣ L.[] t ρ = refl
  plug*-⋯ᵣ (F L.∷ Es) t ρ =
    frame-plug₁ F ρ (λ _ → V-`)
    ■ cong ((F ⋯ᶠ ρ) [_]) (plug*-⋯ᵣ Es t ρ)

record CanonRedex (P : 𝐓.Proc 0) (c : Const) : Set where
  constructor canonRedex
  field
    {midʳ}  : ℕ
    bh      : ℕ
    D₁ D₂   : BindGroup
    above′  : ProcessContext midʳ 0
    E₀      : Frame* (sum (bh L.∷ D₁) + sum D₂ + midʳ)
    Q₀      : 𝐓.Proc (sum (bh L.∷ D₁) + sum D₂ + midʳ)
    ≋-redex : P 𝐓.≋
      plug above′
        (𝐓.ν (suc bh L.∷ D₁) D₂
          (𝐓.⟪ E₀ ⋯ᶠ* weakenᵣ [ K c ·¹ (` 0F) ]* ⟫
           𝐓.∥ (Q₀ 𝐓.⋯ₚ weakenᵣ)))

private
  canon-redex :
    {ctx : ProcessContext k 0} (c : Const) (E : Frame* k) {x : 𝔽 k}
    (bnd : Binder ctx x) →
    HeadShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
    (confine :
      ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
        {bh : ℕ} {D₁ D₂ : BindGroup}
        {F : Frame* (sum (suc bh L.∷ D₁) + sum D₂ + m)}
        {Pr : 𝐓.Proc (sum (suc bh L.∷ D₁) + sum D₂ + m)} →
        Γ ; γ ⊢ₚ
          𝐓.ν (suc bh L.∷ D₁) D₂ (𝐓.⟪ F [ K c ·¹ (` 0F) ]* ⟫ 𝐓.∥ Pr) →
        HeadConfined bh D₁ D₂ F Pr) →
    [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
    CanonRedex (plug ctx 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫) c
  canon-redex {ctx = ctx} c E {x = x} bnd hs confine ⊢P
    with canon-head (E [ K c ·¹ (` x) ]*) bnd hs
  ... | canonHead bh D₁ D₂ ab ρ Q ≋c xeq =
    let
      ≋c′ : plug ctx 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ 𝐓.≋
            plug ab
              (𝐓.ν (suc bh L.∷ D₁) D₂
                (𝐓.⟪ (E ⋯ᶠ* ρ) [ K c ·¹ (` 0F) ]* ⟫ 𝐓.∥ Q))
      ≋c′ = ≋c
        ◅◅ ≡→≋
             (cong
               (λ w →
                 plug ab (𝐓.ν (suc bh L.∷ D₁) D₂ (𝐓.⟪ w ⟫ 𝐓.∥ Q)))
               (plug*-⋯ᵣ E (K c ·¹ (` x)) ρ
                ■ cong (λ z → (E ⋯ᶠ* ρ) [ K c ·¹ (` z) ]*) xeq))
      ⊢c = Allⱽ.[] / ⊢P ⊢-≋ ≋c′
      Γ′ , γ′ , Γ′-S , ⊢ν =
        focusTyping ab
          (𝐓.ν (suc bh L.∷ D₁) D₂
            (𝐓.⟪ (E ⋯ᶠ* ρ) [ K c ·¹ (` 0F) ]* ⟫ 𝐓.∥ Q))
          Allⱽ.[] ⊢c
      E₀ , Eeq , Q₀ , Qeq = confine Γ′-S {F = E ⋯ᶠ* ρ} {Pr = Q} ⊢ν
    in canonRedex bh D₁ D₂ ab E₀ Q₀
         (≋c′
          ◅◅ ≡→≋
               (cong₂
                 (λ F Pr →
                   plug ab
                     (𝐓.ν (suc bh L.∷ D₁) D₂
                       (𝐓.⟪ F [ K c ·¹ (` 0F) ]* ⟫ 𝐓.∥ Pr)))
                 Eeq Qeq))

canon-discard :
  {ctx : ProcessContext k 0} (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  HeadShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K `discard ·¹ (` x) ]* ⟫ →
  CanonRedex (plug ctx 𝐓.⟪ E [ K `discard ·¹ (` x) ]* ⟫) `discard
canon-discard E bnd hs ⊢P =
  canon-redex `discard E bnd hs discard-confine ⊢P

canon-drop :
  {ctx : ProcessContext k 0} (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  HeadShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
  CanonRedex (plug ctx 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫) `drop
canon-drop E bnd hs ⊢P = canon-redex `drop E bnd hs drop-confine ⊢P

------------------------------------------------------------------------
-- 10.  `R-Acq`.
--
-- `R-Acq` needs no strengthening (it takes an arbitrary frame and residual),
-- but it does need the EMPTY first group: `ν (zero ∷ suc b₁ ∷ B₁) B₂`.  That
-- shape is a Phase-5 input (the soup's acquire flag plus `⊢ᴮ`, cf.
-- `Position.AcqNonFirstGroupHead`), so it enters here as a hypothesis.

data AcqShape : (B₁ B₂ : BindGroup) → 𝔽 (sum B₁ + sum B₂) → Set where
  acq-l : ∀ b (B′ B₂ : BindGroup) →
          AcqShape (zero L.∷ suc b L.∷ B′) B₂ 0F
  acq-r : ∀ (B₁ : BindGroup) b (B′ : BindGroup) →
          AcqShape B₁ (zero L.∷ suc b L.∷ B′) (sum B₁ ↑ʳ 0F)

record CanonAcq (P : 𝐓.Proc 0) : Set where
  constructor canonAcq
  field
    {midᵃ}  : ℕ
    ba      : ℕ
    D₁ D₂   : BindGroup
    above′  : ProcessContext midᵃ 0
    E₀      : Frame* (sum (zero L.∷ suc ba L.∷ D₁) + sum D₂ + midᵃ)
    Q₀      : 𝐓.Proc (sum (zero L.∷ suc ba L.∷ D₁) + sum D₂ + midᵃ)
    ≋-redex : P 𝐓.≋
      plug above′
        (𝐓.ν (zero L.∷ suc ba L.∷ D₁) D₂
          (𝐓.⟪ E₀ [ K `acq ·¹ (` 0F) ]* ⟫ 𝐓.∥ Q₀))

canon-acq :
  {ctx : ProcessContext k 0} (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  AcqShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  CanonAcq (plug ctx 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫)
canon-acq E {x = x} bnd (acq-l ba B′ D₂)
  with canon (E [ K `acq ·¹ (` x) ]*) bnd
... | canonical ab ρ Q ≋c xeq =
  canonAcq ba B′ D₂ ab (E ⋯ᶠ* ρ) Q
    (≋c
     ◅◅ ≡→≋
          (cong
            (λ w →
              plug ab (𝐓.ν (zero L.∷ suc ba L.∷ B′) D₂ (𝐓.⟪ w ⟫ 𝐓.∥ Q)))
            (plug*-⋯ᵣ E (K `acq ·¹ (` x)) ρ
             ■ cong (λ z → (E ⋯ᶠ* ρ) [ K `acq ·¹ (` z) ]*) xeq)))
canon-acq E {x = x} bnd (acq-r D₁ ba B′)
  with canon-swap (canon (E [ K `acq ·¹ (` x) ]*) bnd)
... | canonical {midᶜ = m₀} ab ρ Q ≋c xeq =
  canonAcq ba B′ D₁ ab (E ⋯ᶠ* ρ) Q
    (≋c
     ◅◅ ≡→≋
          (cong
            (λ w →
              plug ab (𝐓.ν (zero L.∷ suc ba L.∷ B′) D₁ (𝐓.⟪ w ⟫ 𝐓.∥ Q)))
            (plug*-⋯ᵣ E (K `acq ·¹ (` x)) ρ
             ■ cong (λ z → (E ⋯ᶠ* ρ) [ K `acq ·¹ (` z) ]*)
                 (xeq
                  ■ cong (λ z → z ↑ˡ m₀)
                      (swap-↑ʳ (sum D₁) {sum (zero L.∷ suc ba L.∷ B′)} 0F)))))

------------------------------------------------------------------------
-- 11.  `R-LSplit` / `R-RSplit`.
--
-- The split rules fire at ANY group of the first endpoint: the group list is
-- written `G₁ ++ (q + suc b) ∷ G₂` and the handle is `𝐒.atk (q ↑ʳ 0F)`.
-- `splitIx` is that index without the two trailing `↑ˡ`s, so that it can be
-- used as a `Canon`'s local index -- `atk-splitIx` is `refl`.

splitIx : (G₁ G₂ : BindGroup) (q b : ℕ) →
  𝔽 (sum (G₁ L.++ (q + suc b) L.∷ G₂))
splitIx G₁ G₂ q b =
  Fin.cast (sym (sum-++ G₁ ((q + suc b) L.∷ G₂)))
    (sum G₁ ↑ʳ ((q ↑ʳ (Fin.zero {b})) ↑ˡ sum G₂))

atk-splitIx :
  (G₁ G₂ : BindGroup) (q b m n′ : ℕ) →
  SplitRenamings.atk G₁ G₂ m {q + suc b} {n′} (q ↑ʳ 0F)
    ≡ splitIx G₁ G₂ q b ↑ˡ m ↑ˡ n′
atk-splitIx G₁ G₂ q b m n′ = refl

data SplitShape : (B₁ B₂ : BindGroup) → 𝔽 (sum B₁ + sum B₂) → Set where
  split-l : ∀ (G₁ G₂ : BindGroup) (q b : ℕ) (C : BindGroup) →
            SplitShape (G₁ L.++ (q + suc b) L.∷ G₂) C
              (splitIx G₁ G₂ q b ↑ˡ sum C)
  split-r : ∀ (C : BindGroup) (G₁ G₂ : BindGroup) (q b : ℕ) →
            SplitShape C (G₁ L.++ (q + suc b) L.∷ G₂)
              (sum C ↑ʳ splitIx G₁ G₂ q b)

record CanonSplit (P : 𝐓.Proc 0) (c : 𝕊 0 → Const) : Set where
  constructor canonSplit
  field
    {midˢ}  : ℕ
    G₁ G₂   : BindGroup
    q b     : ℕ
    C       : BindGroup
    sess    : 𝕊 0
    above′  : ProcessContext midˢ 0
    E₀      : Frame*
                (sum (G₁ L.++ (q + suc b) L.∷ G₂) + sum C + midˢ)
    Q₀      : 𝐓.Proc
                (sum (G₁ L.++ (q + suc b) L.∷ G₂) + sum C + midˢ)
    ≋-redex : P 𝐓.≋
      plug above′
        (𝐓.ν (G₁ L.++ (q + suc b) L.∷ G₂) C
          (𝐓.⟪ E₀ [ K (c sess)
                     ·¹ (` SplitRenamings.atk G₁ G₂ (sum C)
                            {q + suc b} {midˢ} (q ↑ʳ 0F)) ]* ⟫
           𝐓.∥ Q₀))

canon-split :
  {ctx : ProcessContext k 0} (c : 𝕊 0 → Const) (s₀ : 𝕊 0)
  (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  CanonSplit (plug ctx 𝐓.⟪ E [ K (c s₀) ·¹ (` x) ]* ⟫) c
canon-split c s₀ E {x = x} bnd (split-l G₁ G₂ q b C)
  with canon (E [ K (c s₀) ·¹ (` x) ]*) bnd
... | canonical ab ρ Q ≋c xeq =
  canonSplit G₁ G₂ q b C s₀ ab (E ⋯ᶠ* ρ) Q
    (≋c
     ◅◅ ≡→≋
          (cong
            (λ w →
              plug ab
                (𝐓.ν (G₁ L.++ (q + suc b) L.∷ G₂) C (𝐓.⟪ w ⟫ 𝐓.∥ Q)))
            (plug*-⋯ᵣ E (K (c s₀) ·¹ (` x)) ρ
             ■ cong (λ z → (E ⋯ᶠ* ρ) [ K (c s₀) ·¹ (` z) ]*) xeq)))
canon-split c s₀ E {x = x} bnd (split-r C G₁ G₂ q b)
  with canon-swap (canon (E [ K (c s₀) ·¹ (` x) ]*) bnd)
... | canonical {midᶜ = m₀} ab ρ Q ≋c xeq =
  canonSplit G₁ G₂ q b C s₀ ab (E ⋯ᶠ* ρ) Q
    (≋c
     ◅◅ ≡→≋
          (cong
            (λ w →
              plug ab
                (𝐓.ν (G₁ L.++ (q + suc b) L.∷ G₂) C (𝐓.⟪ w ⟫ 𝐓.∥ Q)))
            (plug*-⋯ᵣ E (K (c s₀) ·¹ (` x)) ρ
             ■ cong (λ z → (E ⋯ᶠ* ρ) [ K (c s₀) ·¹ (` z) ]*)
                 (xeq
                  ■ cong (λ z → z ↑ˡ m₀)
                      (swap-↑ʳ (sum C)
                        {sum (G₁ L.++ (q + suc b) L.∷ G₂)}
                        (splitIx G₁ G₂ q b))))))

canon-lsplit :
  {ctx : ProcessContext k 0} (s₀ : 𝕊 0)
  (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  CanonSplit (plug ctx 𝐓.⟪ E [ K (`lsplit s₀) ·¹ (` x) ]* ⟫) `lsplit
canon-lsplit s₀ E bnd sh = canon-split `lsplit s₀ E bnd sh

canon-rsplit :
  {ctx : ProcessContext k 0} (s₀ : 𝕊 0)
  (E : Frame* k) {x : 𝔽 k} (bnd : Binder ctx x) →
  SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  CanonSplit (plug ctx 𝐓.⟪ E [ K (`rsplit s₀) ·¹ (` x) ]* ⟫) `rsplit
canon-rsplit s₀ E bnd sh = canon-split `rsplit s₀ E bnd sh
