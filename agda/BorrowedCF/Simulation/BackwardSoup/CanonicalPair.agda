-- | Phase 4b, the PAIR corollary (`R-Com` / `R-Choice` / `R-Close`).
--
--   `Canonical.agda` canonicalises ONE located thread.  The synchronising
--   rules need TWO threads brought under the SAME binder, side by side and
--   in the right order:
--
--     ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
--       ((⟪ E₁ [ K c₁ ·¹ (` 0F) ]* ⟫ ∥ ⟪ E₂ [ K c₂ ·¹ (` y) ]* ⟫) ∥ Q)
--
--   with `y = wkʳ mid (wkˡ (suc b₁ + sum B₁) 0F)`, i.e. the head of the
--   first group of the SECOND endpoint.
--
--   This module supplies the two-hole process context that the construction
--   walks (`ProcessContext₂`, `plug₂`), the two-hole binder (`Binder₂`), and
--   the construction itself:
--
--     1. `bubble₂`, the two-hole analogue of `bubble`.  It produces a PAIR of
--        bind stacks, an OUTER `bsA` and an INNER `bsB`, rather than one
--        (appending the two branches' stacks would need a transport along
--        `arity (bs₁ ++ bs₂) n ≡ arity bs₂ (arity bs₁ n)`), together with two
--        renamings and a residual:
--            plug₂ c R₁ R₂ ≋
--            plugL bsA (plugL bsB (((R₁ ⋯ₚ ρ₁) ∥ (R₂ ⋯ₚ ρ₂)) ∥ resid)).
--        The `par₂`/`par₂ˢ` leaves are where the two holes meet (`bubblePar`,
--        `foldPar` + `plugL-⋯` to slide the second stack inside the first,
--        `∥-shuffle` to put the two threads leftmost and in order; `par₂ˢ`
--        needs one extra `∥-comm`); `left₂`/`right₂`/`bind₂` are handled
--        exactly as in `bubble` (`foldPar₂` for the siblings).
--     2. `push₂` -- `push`, once per level -- moves the binding `ν C₁ C₂`
--        inside both stacks, and its handle lemma gives both `ρ₁ x₁` and
--        `ρ₂ x₂` in the binder's local scope (`canon₂`).
--     3. `HeadShape₂` pins the two handles to the heads of the first groups of
--        OPPOSITE endpoints; `canon-pair` normalises the sides with at most
--        one `canon-swap₂` (`ν-swap′`), landing on `0F` and
--        `sum (suc b₁ ∷ B₁) ↑ʳ 0F`.
--     4. For `R-Com` / `R-Close` the two frames and the residual are
--        additionally strengthened w.r.t. BOTH head handles
--        (`Support/PairConfine.agda`'s `wkₚ` form).
module BorrowedCF.Simulation.BackwardSoup.CanonicalPair where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.BackwardSoup.Locate
open import BorrowedCF.Simulation.BackwardSoup.Position
open import BorrowedCF.Simulation.BackwardSoup.Canonical

open 𝐓 using (BindGroup; _;_⊢ₚ_)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  Two-hole process contexts.

data ProcessContext₂ : ℕ → ℕ → ℕ → Set where
  par₂  : ProcessContext k₁ n → ProcessContext k₂ n → ProcessContext₂ k₁ k₂ n
  par₂ˢ : ProcessContext k₂ n → ProcessContext k₁ n → ProcessContext₂ k₁ k₂ n
  left₂ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc n → ProcessContext₂ k₁ k₂ n
  right₂ : 𝐓.Proc n → ProcessContext₂ k₁ k₂ n → ProcessContext₂ k₁ k₂ n
  bind₂ : (B₁ B₂ : BindGroup) →
          ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n) →
          ProcessContext₂ k₁ k₂ n

plug₂ :
  ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₁ → 𝐓.Proc k₂ → 𝐓.Proc n
plug₂ (par₂ c₁ c₂) R₁ R₂ = plug c₁ R₁ 𝐓.∥ plug c₂ R₂
plug₂ (par₂ˢ c₂ c₁) R₁ R₂ = plug c₂ R₂ 𝐓.∥ plug c₁ R₁
plug₂ (left₂ c Q) R₁ R₂ = plug₂ c R₁ R₂ 𝐓.∥ Q
plug₂ (right₂ Q c) R₁ R₂ = Q 𝐓.∥ plug₂ c R₁ R₂
plug₂ (bind₂ B₁ B₂ c) R₁ R₂ = 𝐓.ν B₁ B₂ (plug₂ c R₁ R₂)

-- The one-hole context obtained by filling the second hole.
fill₂ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₂ → ProcessContext k₁ n
fill₂ (par₂ c₁ c₂) R₂ = par-left c₁ (plug c₂ R₂)
fill₂ (par₂ˢ c₂ c₁) R₂ = par-right (plug c₂ R₂) c₁
fill₂ (left₂ c Q) R₂ = par-left (fill₂ c R₂) Q
fill₂ (right₂ Q c) R₂ = par-right Q (fill₂ c R₂)
fill₂ (bind₂ B₁ B₂ c) R₂ = bind B₁ B₂ (fill₂ c R₂)

plug-fill₂ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  plug (fill₂ c R₂) R₁ ≡ plug₂ c R₁ R₂
plug-fill₂ (par₂ c₁ c₂) R₁ R₂ = refl
plug-fill₂ (par₂ˢ c₂ c₁) R₁ R₂ = refl
plug-fill₂ (left₂ c Q) R₁ R₂ = cong (𝐓._∥ Q) (plug-fill₂ c R₁ R₂)
plug-fill₂ (right₂ Q c) R₁ R₂ = cong (Q 𝐓.∥_) (plug-fill₂ c R₁ R₂)
plug-fill₂ (bind₂ B₁ B₂ c) R₁ R₂ =
  cong (𝐓.ν B₁ B₂) (plug-fill₂ c R₁ R₂)

-- ... and the one-hole context of the SECOND thread.
fill₁ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₁ → ProcessContext k₂ n
fill₁ (par₂ c₁ c₂) R₁ = par-right (plug c₁ R₁) c₂
fill₁ (par₂ˢ c₂ c₁) R₁ = par-left c₂ (plug c₁ R₁)
fill₁ (left₂ c Q) R₁ = par-left (fill₁ c R₁) Q
fill₁ (right₂ Q c) R₁ = par-right Q (fill₁ c R₁)
fill₁ (bind₂ B₁ B₂ c) R₁ = bind B₁ B₂ (fill₁ c R₁)

plug-fill₁ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  plug (fill₁ c R₁) R₂ ≡ plug₂ c R₁ R₂
plug-fill₁ (par₂ c₁ c₂) R₁ R₂ = refl
plug-fill₁ (par₂ˢ c₂ c₁) R₁ R₂ = refl
plug-fill₁ (left₂ c Q) R₁ R₂ = cong (𝐓._∥ Q) (plug-fill₁ c R₁ R₂)
plug-fill₁ (right₂ Q c) R₁ R₂ = cong (Q 𝐓.∥_) (plug-fill₁ c R₁ R₂)
plug-fill₁ (bind₂ B₁ B₂ c) R₁ R₂ =
  cong (𝐓.ν B₁ B₂) (plug-fill₁ c R₁ R₂)

------------------------------------------------------------------------
-- 1b.  Composing a one-hole context ABOVE a two-hole context, and the two
--      ambient renamings of a two-hole context.

compose₂ :
  ProcessContext m n → ProcessContext₂ k₁ k₂ m → ProcessContext₂ k₁ k₂ n
compose₂ hole inner = inner
compose₂ (par-left outer Q) inner = left₂ (compose₂ outer inner) Q
compose₂ (par-right Q outer) inner = right₂ Q (compose₂ outer inner)
compose₂ (bind B₁ B₂ outer) inner = bind₂ B₁ B₂ (compose₂ outer inner)

plug-compose₂ :
  (outer : ProcessContext m n) (inner : ProcessContext₂ k₁ k₂ m)
  (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  plug₂ (compose₂ outer inner) R₁ R₂ ≡ plug outer (plug₂ inner R₁ R₂)
plug-compose₂ hole inner R₁ R₂ = refl
plug-compose₂ (par-left outer Q) inner R₁ R₂ =
  cong (𝐓._∥ Q) (plug-compose₂ outer inner R₁ R₂)
plug-compose₂ (par-right Q outer) inner R₁ R₂ =
  cong (Q 𝐓.∥_) (plug-compose₂ outer inner R₁ R₂)
plug-compose₂ (bind B₁ B₂ outer) inner R₁ R₂ =
  cong (𝐓.ν B₁ B₂) (plug-compose₂ outer inner R₁ R₂)

fill₂-compose₂ :
  (outer : ProcessContext m n) (inner : ProcessContext₂ k₁ k₂ m)
  (R₂ : 𝐓.Proc k₂) →
  fill₂ (compose₂ outer inner) R₂ ≡ compose outer (fill₂ inner R₂)
fill₂-compose₂ hole inner R₂ = refl
fill₂-compose₂ (par-left outer Q) inner R₂ =
  cong (λ z → par-left z Q) (fill₂-compose₂ outer inner R₂)
fill₂-compose₂ (par-right Q outer) inner R₂ =
  cong (par-right Q) (fill₂-compose₂ outer inner R₂)
fill₂-compose₂ (bind B₁ B₂ outer) inner R₂ =
  cong (bind B₁ B₂) (fill₂-compose₂ outer inner R₂)

fill₁-compose₂ :
  (outer : ProcessContext m n) (inner : ProcessContext₂ k₁ k₂ m)
  (R₁ : 𝐓.Proc k₁) →
  fill₁ (compose₂ outer inner) R₁ ≡ compose outer (fill₁ inner R₁)
fill₁-compose₂ hole inner R₁ = refl
fill₁-compose₂ (par-left outer Q) inner R₁ =
  cong (λ z → par-left z Q) (fill₁-compose₂ outer inner R₁)
fill₁-compose₂ (par-right Q outer) inner R₁ =
  cong (par-right Q) (fill₁-compose₂ outer inner R₁)
fill₁-compose₂ (bind B₁ B₂ outer) inner R₁ =
  cong (bind B₁ B₂) (fill₁-compose₂ outer inner R₁)

-- The renaming a two-hole context performs on its ambient variables, once
-- per branch.  `wt₁ c ≗ weakenThrough (fill₂ c R₂)` and
-- `wt₂ c ≗ weakenThrough (fill₁ c R₁)` (`wt₁-fill₂` / `wt₂-fill₁`), so these
-- are the `Position.weakenThrough`s of the two threads, stated without
-- mentioning the process that fills the other hole.
wt₁ : ProcessContext₂ k₁ k₂ n → 𝔽 n → 𝔽 k₁
wt₁ (par₂ c₁ c₂) y = weakenThrough c₁ y
wt₁ (par₂ˢ c₂ c₁) y = weakenThrough c₁ y
wt₁ (left₂ c Q) y = wt₁ c y
wt₁ (right₂ Q c) y = wt₁ c y
wt₁ (bind₂ B₁ B₂ c) y = wt₁ c ((sum B₁ + sum B₂) ↑ʳ y)

wt₂ : ProcessContext₂ k₁ k₂ n → 𝔽 n → 𝔽 k₂
wt₂ (par₂ c₁ c₂) y = weakenThrough c₂ y
wt₂ (par₂ˢ c₂ c₁) y = weakenThrough c₂ y
wt₂ (left₂ c Q) y = wt₂ c y
wt₂ (right₂ Q c) y = wt₂ c y
wt₂ (bind₂ B₁ B₂ c) y = wt₂ c ((sum B₁ + sum B₂) ↑ʳ y)

wt₁-fill₂ :
  (c : ProcessContext₂ k₁ k₂ n) (R₂ : 𝐓.Proc k₂) (y : 𝔽 n) →
  weakenThrough (fill₂ c R₂) y ≡ wt₁ c y
wt₁-fill₂ (par₂ c₁ c₂) R₂ y = refl
wt₁-fill₂ (par₂ˢ c₂ c₁) R₂ y = refl
wt₁-fill₂ (left₂ c Q) R₂ y = wt₁-fill₂ c R₂ y
wt₁-fill₂ (right₂ Q c) R₂ y = wt₁-fill₂ c R₂ y
wt₁-fill₂ (bind₂ B₁ B₂ c) R₂ y = wt₁-fill₂ c R₂ ((sum B₁ + sum B₂) ↑ʳ y)

wt₂-fill₁ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (y : 𝔽 n) →
  weakenThrough (fill₁ c R₁) y ≡ wt₂ c y
wt₂-fill₁ (par₂ c₁ c₂) R₁ y = refl
wt₂-fill₁ (par₂ˢ c₂ c₁) R₁ y = refl
wt₂-fill₁ (left₂ c Q) R₁ y = wt₂-fill₁ c R₁ y
wt₂-fill₁ (right₂ Q c) R₁ y = wt₂-fill₁ c R₁ y
wt₂-fill₁ (bind₂ B₁ B₂ c) R₁ y = wt₂-fill₁ c R₁ ((sum B₁ + sum B₂) ↑ʳ y)

------------------------------------------------------------------------
-- 1c.  TWO-LEVEL bind stacks.
--
-- The `par₂` leaf glues the bind stacks of the two branches.  Appending them
-- would need a transport along `arity (bs₁ ++ bs₂) n ≡ arity bs₂ (arity bs₁ n)`
-- (true, but not judgmental for a variable `bs₁`), so the construction keeps
-- the two stacks as a PAIR -- an OUTER `bsA` and an INNER `bsB` -- and
-- iterates `foldPar` and `push` once per level.

wkL₂ : (bsA bsB : BindList) {n : ℕ} → n →ᵣ arity bsB (arity bsA n)
wkL₂ bsA bsB y = wkL bsB (wkL bsA y)

foldPar₂ :
  (bsA bsB : BindList) {n : ℕ}
  (X : 𝐓.Proc (arity bsB (arity bsA n))) (Z₀ : 𝐓.Proc n) →
  (plugL bsA (plugL bsB X) 𝐓.∥ Z₀) 𝐓.≋
  plugL bsA (plugL bsB (X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL₂ bsA bsB)))
foldPar₂ bsA bsB X Z₀ =
  foldPar bsA (plugL bsB X) Z₀
  ◅◅ ≋-plugL bsA (foldPar bsB X (Z₀ 𝐓.⋯ₚ wkL bsA))
  ◅◅ ≡→≋
       (cong (λ z → plugL bsA (plugL bsB (X 𝐓.∥ z)))
         (𝐓.fusionₚ Z₀ (wkL bsA) (wkL bsB) ■ 𝐓.⋯ₚ-cong Z₀ (λ _ → refl)))

-- `push`, twice: the binder is commuted past the OUTER stack first and then
-- past the INNER one, so it ends up below both.
push₂ :
  (bsA bsB : BindList) (C₁ C₂ : BindGroup) {mid : ℕ}
  (T : 𝐓.Proc (arity bsB (arity bsA (sum C₁ + sum C₂ + mid)))) →
  Σ[ σ ∈ (arity bsB (arity bsA (sum C₁ + sum C₂ + mid)) →ᵣ
            (sum C₁ + sum C₂ + arity bsB (arity bsA mid))) ]
    ((𝐓.ν C₁ C₂ (plugL bsA (plugL bsB T)) 𝐓.≋
      plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T 𝐓.⋯ₚ σ))))
     × ((v : 𝔽 (sum C₁ + sum C₂)) →
          σ (wkL₂ bsA bsB (v ↑ˡ mid)) ≡ v ↑ˡ arity bsB (arity bsA mid)))
push₂ bsA bsB C₁ C₂ {mid} T
  with push bsA C₁ C₂ {mid} (plugL bsB T)
... | σA , ≋A , hndA
  with push bsB C₁ C₂ {arity bsA mid} (T 𝐓.⋯ₚ liftL bsB σA)
...  | σB , ≋B , hndB =
  (λ y → σB (liftL bsB σA y))
  , ( ≋A
      ◅◅ ≋-plugL bsA (𝐓.ν-cong (≡→≋ (plugL-⋯ bsB T σA)))
      ◅◅ ≋-plugL bsA ≋B
      ◅◅ ≡→≋
           (cong (λ z → plugL bsA (plugL bsB (𝐓.ν C₁ C₂ z)))
             (𝐓.fusionₚ T (liftL bsB σA) σB
              ■ 𝐓.⋯ₚ-cong T (λ _ → refl))))
  , (λ v →
       cong σB
         (liftL-wkL bsB σA (wkL bsA (v ↑ˡ mid))
          ■ cong (wkL bsB) (hndA v))
       ■ hndB v)

------------------------------------------------------------------------
-- 1d.  ∥-bubbling for TWO holes.

private
  -- `(a ∥ b) ∥ (c ∥ d) ≋ (c ∥ a) ∥ (d ∥ b)`: the two threads to the front,
  -- the two residuals to the back.
  ∥-shuffle :
    {n : ℕ} (a b c d : 𝐓.Proc n) →
    ((a 𝐓.∥ b) 𝐓.∥ (c 𝐓.∥ d)) 𝐓.≋ ((c 𝐓.∥ a) 𝐓.∥ (d 𝐓.∥ b))
  ∥-shuffle a b c d =
    𝐓.∥-assoc
    ◅◅ 𝐓.∥-cong (≋-sym 𝐓.∥-assoc) ≋-refl
    ◅◅ 𝐓.∥-cong (𝐓.∥-cong ≋-refl 𝐓.∥-comm) ≋-refl
    ◅◅ 𝐓.∥-cong 𝐓.∥-assoc ≋-refl
    ◅◅ 𝐓.∥-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl) ≋-refl
    ◅◅ ≋-sym 𝐓.∥-assoc
    ◅◅ 𝐓.∥-cong ≋-refl 𝐓.∥-comm

record Bubble₂ {k₁ k₂ n : ℕ} (c : ProcessContext₂ k₁ k₂ n) : Set where
  constructor bubbled₂
  field
    bsA bsB : BindList
    ρ₁      : k₁ →ᵣ arity bsB (arity bsA n)
    ρ₂      : k₂ →ᵣ arity bsB (arity bsA n)
    resid   : 𝐓.Proc (arity bsB (arity bsA n))
    ≋-eq    : (Z₁ : 𝐓.Proc k₁) (Z₂ : 𝐓.Proc k₂) →
              plug₂ c Z₁ Z₂ 𝐓.≋
              plugL bsA
                (plugL bsB
                  (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ resid))
    amb₁    : (y : 𝔽 n) → ρ₁ (wt₁ c y) ≡ wkL₂ bsA bsB y
    amb₂    : (y : 𝔽 n) → ρ₂ (wt₂ c y) ≡ wkL₂ bsA bsB y

private
  -- The LEAF: the two branches meet.  `bubble` normalises each of them; the
  -- second stack is then pushed INSIDE the first (`foldPar`, `plugL-⋯`).
  bubblePar :
    (c₁ : ProcessContext k₁ n) (c₂ : ProcessContext k₂ n) →
    Bubble₂ (par₂ c₁ c₂)
  bubblePar c₁ c₂ with bubble c₁ | bubble c₂
  ... | bubbled bs₁ σ₁ Q₁ eq₁ am₁ | bubbled bs₂ σ₂ Q₂ eq₂ am₂ =
    bubbled₂ bs₁ bs₂
      (λ y → wkL bs₂ (σ₁ y))
      (λ y → liftL bs₂ (wkL bs₁) (σ₂ y))
      ((Q₁ 𝐓.⋯ₚ wkL bs₂) 𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
      (λ Z₁ Z₂ →
        𝐓.∥-cong (eq₁ Z₁) (eq₂ Z₂)
        ◅◅ foldPar bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)
             (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂))
        ◅◅ ≡→≋
             (cong (λ z → plugL bs₁ (((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) 𝐓.∥ z))
               (plugL-⋯ bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) (wkL bs₁)))
        ◅◅ ≋-plugL bs₁ 𝐓.∥-comm
        ◅◅ ≋-plugL bs₁
             (foldPar bs₂
               (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
               ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁))
        ◅◅ ≋-plugL bs₁
             (≋-plugL bs₂
               (∥-shuffle
                 (Z₂ 𝐓.⋯ₚ σ₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                 (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                 (Z₁ 𝐓.⋯ₚ σ₁ 𝐓.⋯ₚ wkL bs₂)
                 (Q₁ 𝐓.⋯ₚ wkL bs₂)))
        ◅◅ ≡→≋
             (cong₂
               (λ u₁ u₂ →
                 plugL bs₁
                   (plugL bs₂
                     ((u₁ 𝐓.∥ u₂)
                      𝐓.∥ ((Q₁ 𝐓.⋯ₚ wkL bs₂)
                           𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))))))
               (𝐓.fusionₚ Z₁ σ₁ (wkL bs₂) ■ 𝐓.⋯ₚ-cong Z₁ (λ _ → refl))
               (𝐓.fusionₚ Z₂ σ₂ (liftL bs₂ (wkL bs₁))
                ■ 𝐓.⋯ₚ-cong Z₂ (λ _ → refl))))
      (λ y → cong (wkL bs₂) (am₁ y))
      (λ y →
        cong (liftL bs₂ (wkL bs₁)) (am₂ y)
        ■ liftL-wkL bs₂ (wkL bs₁) y)

bubble₂ : (c : ProcessContext₂ k₁ k₂ n) → Bubble₂ c
bubble₂ (par₂ c₁ c₂) = bubblePar c₁ c₂
bubble₂ (par₂ˢ c₂ c₁) with bubblePar c₁ c₂
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ Q (λ Z₁ Z₂ → 𝐓.∥-comm ◅◅ eq Z₁ Z₂) am₁ am₂
bubble₂ (left₂ c Q₀) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB))
    (λ Z₁ Z₂ →
      𝐓.∥-cong (eq Z₁ Z₂) ≋-refl
      ◅◅ foldPar₂ bsA bsB
           (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀
      ◅◅ ≋-plugL bsA (≋-plugL bsB (≋-sym 𝐓.∥-assoc)))
    am₁ am₂
bubble₂ (right₂ Q₀ c) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB))
    (λ Z₁ Z₂ →
      𝐓.∥-cong ≋-refl (eq Z₁ Z₂)
      ◅◅ 𝐓.∥-comm
      ◅◅ foldPar₂ bsA bsB
           (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀
      ◅◅ ≋-plugL bsA (≋-plugL bsB (≋-sym 𝐓.∥-assoc)))
    am₁ am₂
bubble₂ (bind₂ A₁ A₂ c) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ =
  bubbled₂ ((A₁ , A₂) L.∷ bsA) bsB ρ₁ ρ₂ Q
    (λ Z₁ Z₂ → 𝐓.ν-cong (eq Z₁ Z₂))
    (λ y →
      am₁ ((sum A₁ + sum A₂) ↑ʳ y)
      ■ cong (λ z → wkL bsB (wkL bsA z))
          (sym (weaken*~wkˡ ⦃ Kᵣ ⦄ (sum A₁ + sum A₂) y)))
    (λ y →
      am₂ ((sum A₁ + sum A₂) ↑ʳ y)
      ■ cong (λ z → wkL bsB (wkL bsA z))
          (sym (weaken*~wkˡ ⦃ Kᵣ ⦄ (sum A₁ + sum A₂) y)))

------------------------------------------------------------------------
-- 1e.  The two-hole binder.
--
-- `canon-pair` needs the two handles to be bound by the SAME `ν` node --
-- otherwise no `≋`-rearrangement can put the two threads under one binder,
-- and the statement below is false (take `c = par₂ (bind B₁ B₂ hole)
-- (bind B₁′ B₂′ hole)`).  `Binder₂` is `Position.Binder` for a two-hole
-- context: ONE `bind₂` node on the common part of the two paths, with a local
-- index for each hole.  `binder₂⇒₁` / `binder₂⇒₂` project out the ordinary
-- one-hole `Binder`s, which is the form `Position/Crux.agda`'s
-- `HeadOfFirstGroup` is stated for.

record Binder₂ {k₁ k₂ n : ℕ} (c : ProcessContext₂ k₁ k₂ n)
               (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) : Set where
  constructor binder₂
  field
    {mid}         : ℕ
    C₁ C₂         : BindGroup
    above         : ProcessContext mid n
    below         : ProcessContext₂ k₁ k₂ (sum C₁ + sum C₂ + mid)
    decomposition : c ≡ compose₂ above (bind₂ C₁ C₂ below)
    local₁ local₂ : 𝔽 (sum C₁ + sum C₂)
    index-eq₁     : wt₁ below (local₁ ↑ˡ mid) ≡ x₁
    index-eq₂     : wt₂ below (local₂ ↑ˡ mid) ≡ x₂

binder₂⇒₁ :
  {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd : Binder₂ c x₁ x₂) (R₂ : 𝐓.Proc k₂) → Binder (fill₂ c R₂) x₁
binder₂⇒₁ (binder₂ C₁ C₂ above below dec l₁ l₂ ieq₁ ieq₂) R₂ =
  binder C₁ C₂ above (fill₂ below R₂)
    (cong (λ z → fill₂ z R₂) dec
     ■ fill₂-compose₂ above (bind₂ C₁ C₂ below) R₂)
    l₁ (wt₁-fill₂ below R₂ (l₁ ↑ˡ _) ■ ieq₁)

binder₂⇒₂ :
  {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd : Binder₂ c x₁ x₂) (R₁ : 𝐓.Proc k₁) → Binder (fill₁ c R₁) x₂
binder₂⇒₂ (binder₂ C₁ C₂ above below dec l₁ l₂ ieq₁ ieq₂) R₁ =
  binder C₁ C₂ above (fill₁ below R₁)
    (cong (λ z → fill₁ z R₁) dec
     ■ fill₁-compose₂ above (bind₂ C₁ C₂ below) R₁)
    l₂ (wt₂-fill₁ below R₁ (l₂ ↑ˡ _) ■ ieq₂)

------------------------------------------------------------------------
-- 2.  The statement.
--
-- Shaped exactly like the left-hand side of `R-Choice`; `R-Com` and
-- `R-Close` add the strengthening of the frames and the residual.

record CanonPair
  {k₁ k₂ : ℕ} (P : 𝐓.Proc 0) (e₁ : Tm k₁) (e₂ : Tm k₂)
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) : Set where
  constructor canonPair
  field
    {midᵖ}  : ℕ
    b₁ b₂   : ℕ
    B₁ B₂   : BindGroup
    above′  : ProcessContext midᵖ 0
    ρ₁      : k₁ →ᵣ
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    ρ₂      : k₂ →ᵣ
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    resid   : 𝐓.Proc
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    ≋-canon : P 𝐓.≋
      plug above′
        (𝐓.ν (suc b₁ L.∷ B₁) (suc b₂ L.∷ B₂)
          ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
    x₁-eq   : ρ₁ x₁ ≡ 0F
    x₂-eq   : ρ₂ x₂ ≡
              wkʳ ⦃ Kᵣ ⦄ midᵖ
                (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

------------------------------------------------------------------------
-- 3.  The two-hole canonical form, before the side normalisation.
--
-- `Canon₂` is `Canonical.Canon` for two threads: both are the left
-- components of the `∥`-pair directly under their common binder, and each
-- handle sits at the binder's own local index.

record Canon₂ {k₁ k₂ : ℕ} (P : 𝐓.Proc 0) (e₁ : Tm k₁) (e₂ : Tm k₂)
              (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) (C₁ C₂ : BindGroup)
              (l₁ l₂ : 𝔽 (sum C₁ + sum C₂)) : Set where
  constructor canonical₂
  field
    {midᵈ}  : ℕ
    above′  : ProcessContext midᵈ 0
    ρ₁      : k₁ →ᵣ (sum C₁ + sum C₂ + midᵈ)
    ρ₂      : k₂ →ᵣ (sum C₁ + sum C₂ + midᵈ)
    resid   : 𝐓.Proc (sum C₁ + sum C₂ + midᵈ)
    ≋-canon : P 𝐓.≋
      plug above′
        (𝐓.ν C₁ C₂ ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
    x₁-eq   : ρ₁ x₁ ≡ l₁ ↑ˡ midᵈ
    x₂-eq   : ρ₂ x₂ ≡ l₂ ↑ˡ midᵈ

canon₂ :
  {c : ProcessContext₂ k₁ k₂ 0} (e₁ : Tm k₁) (e₂ : Tm k₂)
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} (bnd : Binder₂ c x₁ x₂) →
  Canon₂ (plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) e₁ e₂ x₁ x₂
    (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
    (Binder₂.local₁ bnd) (Binder₂.local₂ bnd)
canon₂ e₁ e₂ (binder₂ C₁ C₂ above below dec l₁ l₂ ieq₁ ieq₂)
  with bubble₂ below
... | bubbled₂ bsA bsB ρ₁₀ ρ₂₀ Q eq am₁ am₂
  with push₂ bsA bsB C₁ C₂
         ((𝐓.⟪ e₁ ⋯ ρ₁₀ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂₀ ⟫) 𝐓.∥ Q)
...  | σ , ≋push , hnd =
  canonical₂ (compose above (compose (ctxL bsA) (ctxL bsB)))
    (λ y → σ (ρ₁₀ y)) (λ y → σ (ρ₂₀ y)) (Q 𝐓.⋯ₚ σ)
    (≡→≋ (cong (λ z → plug₂ z 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) dec
          ■ plug-compose₂ above (bind₂ C₁ C₂ below) 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫)
     ◅◅ ≋-plug above (𝐓.ν-cong (eq 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) ◅◅ ≋push)
     ◅◅ ≡→≋
          (cong₂
             (λ w₁ w₂ →
               plug above
                 (plugL bsA
                   (plugL bsB
                     (𝐓.ν C₁ C₂
                       ((𝐓.⟪ w₁ ⟫ 𝐓.∥ 𝐓.⟪ w₂ ⟫) 𝐓.∥ (Q 𝐓.⋯ₚ σ))))))
             (fusion e₁ ρ₁₀ σ ■ ⋯-cong e₁ (λ _ → refl))
             (fusion e₂ ρ₂₀ σ ■ ⋯-cong e₂ (λ _ → refl))
           ■ sym
               (plug-compose above (compose (ctxL bsA) (ctxL bsB))
                  (𝐓.ν C₁ C₂
                    ((𝐓.⟪ e₁ ⋯ (λ y → σ (ρ₁₀ y)) ⟫
                      𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → σ (ρ₂₀ y)) ⟫)
                     𝐓.∥ (Q 𝐓.⋯ₚ σ)))
                ■ cong (plug above)
                    (plug-compose (ctxL bsA) (ctxL bsB)
                       (𝐓.ν C₁ C₂
                         ((𝐓.⟪ e₁ ⋯ (λ y → σ (ρ₁₀ y)) ⟫
                           𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → σ (ρ₂₀ y)) ⟫)
                          𝐓.∥ (Q 𝐓.⋯ₚ σ)))
                     ■ cong (plug (ctxL bsA))
                         (plug-ctxL bsB
                           (𝐓.ν C₁ C₂
                             ((𝐓.⟪ e₁ ⋯ (λ y → σ (ρ₁₀ y)) ⟫
                               𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → σ (ρ₂₀ y)) ⟫)
                              𝐓.∥ (Q 𝐓.⋯ₚ σ))))
                     ■ plug-ctxL bsA
                         (plugL bsB
                           (𝐓.ν C₁ C₂
                             ((𝐓.⟪ e₁ ⋯ (λ y → σ (ρ₁₀ y)) ⟫
                               𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → σ (ρ₂₀ y)) ⟫)
                              𝐓.∥ (Q 𝐓.⋯ₚ σ))))))))
    (cong σ (cong ρ₁₀ (sym ieq₁) ■ am₁ (l₁ ↑ˡ _)) ■ hnd l₁)
    (cong σ (cong ρ₂₀ (sym ieq₂) ■ am₂ (l₂ ↑ˡ _)) ■ hnd l₂)

private
  swapr-cross₂ : ∀ p q {n} (v : 𝔽 (p + q)) →
    swapᵣ p q {n} (v ↑ˡ n) ≡ Fin.swap p v ↑ˡ n
  swapr-cross₂ p q {n} v rewrite Fin.splitAt-↑ˡ (p + q) v n = refl

  swap-↑ʳ₂ : ∀ p {q} (v : 𝔽 q) → Fin.swap p (p ↑ʳ v) ≡ v ↑ˡ p
  swap-↑ʳ₂ p {q} v rewrite Fin.splitAt-↑ʳ p q v = refl

  swap-↑ˡ₂ : ∀ {p} q (v : 𝔽 p) → Fin.swap p (v ↑ˡ q) ≡ q ↑ʳ v
  swap-↑ˡ₂ {p} q v rewrite Fin.splitAt-↑ˡ p v q = refl

-- The side exchange, for both handles at once.
canon-swap₂ :
  {P : 𝐓.Proc 0} {e₁ : Tm k₁} {e₂ : Tm k₂} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  {C₁ C₂ : BindGroup} {l₁ l₂ : 𝔽 (sum C₁ + sum C₂)} →
  Canon₂ P e₁ e₂ x₁ x₂ C₁ C₂ l₁ l₂ →
  Canon₂ P e₁ e₂ x₁ x₂ C₂ C₁
    (Fin.swap (sum C₁) l₁) (Fin.swap (sum C₁) l₂)
canon-swap₂ {e₁ = e₁} {e₂ = e₂} {C₁ = C₁} {C₂ = C₂} {l₁ = l₁} {l₂ = l₂}
  (canonical₂ above′ ρ₁ ρ₂ resid ≋c xeq₁ xeq₂) =
  canonical₂ above′
    (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₁ y))
    (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₂ y))
    (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂))
    (≋c
     ◅◅ ≋-plug above′ (fwd 𝐓.ν-swap′ ◅ ≋-refl)
     ◅◅ ≡→≋
          (cong₂
            (λ w₁ w₂ →
              plug above′
                (𝐓.ν C₂ C₁
                  ((𝐓.⟪ w₁ ⟫ 𝐓.∥ 𝐓.⟪ w₂ ⟫)
                   𝐓.∥ (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))))
            (fusion e₁ ρ₁ (swapᵣ (sum C₁) (sum C₂))
             ■ ⋯-cong e₁ (λ _ → refl))
            (fusion e₂ ρ₂ (swapᵣ (sum C₁) (sum C₂))
             ■ ⋯-cong e₂ (λ _ → refl))))
    (cong (swapᵣ (sum C₁) (sum C₂)) xeq₁
     ■ swapr-cross₂ (sum C₁) (sum C₂) l₁)
    (cong (swapᵣ (sum C₁) (sum C₂)) xeq₂
     ■ swapr-cross₂ (sum C₁) (sum C₂) l₂)

------------------------------------------------------------------------
-- 4.  The pair-shaped head condition, and `canon-pair`.
--
-- `Position/Crux.agda` proves `HeadOfFirstGroup` for BOTH handles of a
-- synchronising redex (`ImpureRedexHead` for the receiving side,
-- `PairArgRedexHead` for the sending one).  Linearity puts them on OPPOSITE
-- endpoints -- one handle per side -- which is the extra bit `HeadShape₂`
-- records; `headShapes⇒₂` builds it from the two one-sided shapes.

data HeadShape₂ : (C₁ C₂ : BindGroup) →
                  𝔽 (sum C₁ + sum C₂) → 𝔽 (sum C₁ + sum C₂) → Set where
  heads-lr : ∀ a (A : BindGroup) c (C : BindGroup) →
             HeadShape₂ (suc a L.∷ A) (suc c L.∷ C)
               0F (sum (suc a L.∷ A) ↑ʳ 0F)
  heads-rl : ∀ a (A : BindGroup) c (C : BindGroup) →
             HeadShape₂ (suc a L.∷ A) (suc c L.∷ C)
               (sum (suc a L.∷ A) ↑ʳ 0F) 0F

headShapes⇒₂ :
  {C₁ C₂ : BindGroup} {l₁ l₂ : 𝔽 (sum C₁ + sum C₂)} →
  HeadShape C₁ C₂ l₁ → HeadShape C₁ C₂ l₂ → l₁ ≢ l₂ →
  HeadShape₂ C₁ C₂ l₁ l₂
headShapes⇒₂ (head-l a A _) (head-l _ _ _) ne = ⊥-elim (ne refl)
headShapes⇒₂ (head-l a A _) (head-r _ c C) ne = heads-lr a A c C
headShapes⇒₂ (head-r _ c C) (head-l a A _) ne = heads-rl a A c C
headShapes⇒₂ (head-r _ c C) (head-r _ _ _) ne = ⊥-elim (ne refl)

-- The two threads resolve to the SAME binder (`Binder₂`), on OPPOSITE sides,
-- each at the head of its first group (`HeadShape₂`).  Exactly one `ν-swap′`
-- is needed: if `x₁` sits on the SECOND endpoint, the two sides are exchanged.
canon-pair :
  {c : ProcessContext₂ k₁ k₂ 0} (e₁ : Tm k₁) (e₂ : Tm k₂)
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} (bnd : Binder₂ c x₁ x₂) →
  HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
             (Binder₂.local₁ bnd) (Binder₂.local₂ bnd) →
  CanonPair (plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) e₁ e₂ x₁ x₂
canon-pair e₁ e₂ bnd (heads-lr a A c C) with canon₂ e₁ e₂ bnd
... | canonical₂ ab ρ₁ ρ₂ Q ≋c xeq₁ xeq₂ =
  canonPair a c A C ab ρ₁ ρ₂ Q ≋c xeq₁ xeq₂
canon-pair e₁ e₂ bnd (heads-rl a A c C) with canon-swap₂ (canon₂ e₁ e₂ bnd)
... | canonical₂ {midᵈ = m₀} ab ρ₁ ρ₂ Q ≋c xeq₁ xeq₂ =
  canonPair c a C A ab ρ₁ ρ₂ Q ≋c
    (xeq₁
     ■ cong (λ z → z ↑ˡ m₀)
         (swap-↑ʳ₂ (sum (suc a L.∷ A)) {sum (suc c L.∷ C)} 0F))
    (xeq₂
     ■ cong (λ z → z ↑ˡ m₀)
         (swap-↑ˡ₂ {suc a + sum A} (sum (suc c L.∷ C))
           (Fin.zero {a + sum A})))
