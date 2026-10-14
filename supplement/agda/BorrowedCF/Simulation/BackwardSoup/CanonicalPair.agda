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

import BorrowedCF.Processes.TranslationSoup as TranslationS

open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (processCount-rename)
open import BorrowedCF.Simulation.BackwardSoup.Locate
open import BorrowedCF.Simulation.BackwardSoup.Position
open import BorrowedCF.Simulation.BackwardSoup.Canonical
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using ( Tracks; track-ε
        ; tracks-◅◅; tracks-castℕ; tracks-gmap-ν
        ; tracks-∥-cong-l; tracks-∥-cong-r; tracks-∥-assoc
        ; tracks-≋-plug )

open 𝐓 using (BindGroup; _;_⊢ₚ_)

open TranslationS using () renaming (processCount to pc)

open Front using (idx; idx≡)

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
-- 1a.  Thread positions of the two holes (`PLAN.md` §12.2, P5.2b).
--
-- `thread₁ c R₁ R₂` and `thread₂ c R₁ R₂` are `Locate.threadInContext` for
-- a TWO-hole context: they say where a thread of the first (resp. the
-- second) filler ends up in `plug₂ c R₁ R₂`.  `thread₁-fill₂` /
-- `thread₂-fill₁` connect them to the ONE-hole positions of `fill₂ c R₂` /
-- `fill₁ c R₁`, which is the form `Located` and `Canonical.agda` use.  Those
-- equations are NUMERIC (`Fin.toℕ`): `plug (fill₂ c R₂) R₁ ≡ plug₂ c R₁ R₂`
-- holds only propositionally, so the two indices do not even share a type.

thread₁ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  𝔽 (pc R₁) → 𝔽 (pc (plug₂ c R₁ R₂))
thread₁ (par₂ c₁ c₂) R₁ R₂ t = threadInContext c₁ R₁ t ↑ˡ pc (plug c₂ R₂)
thread₁ (par₂ˢ c₂ c₁) R₁ R₂ t = pc (plug c₂ R₂) ↑ʳ threadInContext c₁ R₁ t
thread₁ (left₂ c Q) R₁ R₂ t = thread₁ c R₁ R₂ t ↑ˡ pc Q
thread₁ (right₂ Q c) R₁ R₂ t = pc Q ↑ʳ thread₁ c R₁ R₂ t
thread₁ (bind₂ B₁ B₂ c) R₁ R₂ t = thread₁ c R₁ R₂ t

thread₂ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  𝔽 (pc R₂) → 𝔽 (pc (plug₂ c R₁ R₂))
thread₂ (par₂ c₁ c₂) R₁ R₂ t = pc (plug c₁ R₁) ↑ʳ threadInContext c₂ R₂ t
thread₂ (par₂ˢ c₂ c₁) R₁ R₂ t = threadInContext c₂ R₂ t ↑ˡ pc (plug c₁ R₁)
thread₂ (left₂ c Q) R₁ R₂ t = thread₂ c R₁ R₂ t ↑ˡ pc Q
thread₂ (right₂ Q c) R₁ R₂ t = pc Q ↑ʳ thread₂ c R₁ R₂ t
thread₂ (bind₂ B₁ B₂ c) R₁ R₂ t = thread₂ c R₁ R₂ t

thread₁-fill₂ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂)
  (t : 𝔽 (pc R₁)) →
  Fin.toℕ (thread₁ c R₁ R₂ t) ≡
  Fin.toℕ (threadInContext (fill₂ c R₂) R₁ t)
thread₁-fill₂ (par₂ c₁ c₂) R₁ R₂ t = refl
thread₁-fill₂ (par₂ˢ c₂ c₁) R₁ R₂ t = refl
thread₁-fill₂ (left₂ c Q) R₁ R₂ t =
  Fin.toℕ-↑ˡ (thread₁ c R₁ R₂ t) (pc Q)
  ■ thread₁-fill₂ c R₁ R₂ t
  ■ sym (Fin.toℕ-↑ˡ (threadInContext (fill₂ c R₂) R₁ t) (pc Q))
thread₁-fill₂ (right₂ Q c) R₁ R₂ t =
  Fin.toℕ-↑ʳ (pc Q) (thread₁ c R₁ R₂ t)
  ■ cong (pc Q +_) (thread₁-fill₂ c R₁ R₂ t)
  ■ sym (Fin.toℕ-↑ʳ (pc Q) (threadInContext (fill₂ c R₂) R₁ t))
thread₁-fill₂ (bind₂ B₁ B₂ c) R₁ R₂ t = thread₁-fill₂ c R₁ R₂ t

thread₂-fill₁ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂)
  (t : 𝔽 (pc R₂)) →
  Fin.toℕ (thread₂ c R₁ R₂ t) ≡
  Fin.toℕ (threadInContext (fill₁ c R₁) R₂ t)
thread₂-fill₁ (par₂ c₁ c₂) R₁ R₂ t = refl
thread₂-fill₁ (par₂ˢ c₂ c₁) R₁ R₂ t = refl
thread₂-fill₁ (left₂ c Q) R₁ R₂ t =
  Fin.toℕ-↑ˡ (thread₂ c R₁ R₂ t) (pc Q)
  ■ thread₂-fill₁ c R₁ R₂ t
  ■ sym (Fin.toℕ-↑ˡ (threadInContext (fill₁ c R₁) R₂ t) (pc Q))
thread₂-fill₁ (right₂ Q c) R₁ R₂ t =
  Fin.toℕ-↑ʳ (pc Q) (thread₂ c R₁ R₂ t)
  ■ cong (pc Q +_) (thread₂-fill₁ c R₁ R₂ t)
  ■ sym (Fin.toℕ-↑ʳ (pc Q) (threadInContext (fill₁ c R₁) R₂ t))
thread₂-fill₁ (bind₂ B₁ B₂ c) R₁ R₂ t = thread₂-fill₁ c R₁ R₂ t

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

-- `Canonical.threadInContext-compose`, for the two-hole positions.
thread₁-compose₂ :
  {j : ℕ} (outer : ProcessContext j n) (inner : ProcessContext₂ k₁ k₂ j)
  (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) (t : 𝔽 (pc R₁)) →
  Fin.toℕ (thread₁ (compose₂ outer inner) R₁ R₂ t) ≡
  Fin.toℕ
    (threadInContext outer (plug₂ inner R₁ R₂) (thread₁ inner R₁ R₂ t))
thread₁-compose₂ hole inner R₁ R₂ t = refl
thread₁-compose₂ (par-left outer Q) inner R₁ R₂ t =
  Fin.toℕ-↑ˡ (thread₁ (compose₂ outer inner) R₁ R₂ t) (pc Q)
  ■ thread₁-compose₂ outer inner R₁ R₂ t
  ■ sym (Fin.toℕ-↑ˡ
          (threadInContext outer (plug₂ inner R₁ R₂) (thread₁ inner R₁ R₂ t))
          (pc Q))
thread₁-compose₂ (par-right Q outer) inner R₁ R₂ t =
  Fin.toℕ-↑ʳ (pc Q) (thread₁ (compose₂ outer inner) R₁ R₂ t)
  ■ cong (pc Q +_) (thread₁-compose₂ outer inner R₁ R₂ t)
  ■ sym (Fin.toℕ-↑ʳ (pc Q)
          (threadInContext outer (plug₂ inner R₁ R₂) (thread₁ inner R₁ R₂ t)))
thread₁-compose₂ (bind B₁ B₂ outer) inner R₁ R₂ t =
  thread₁-compose₂ outer inner R₁ R₂ t

thread₂-compose₂ :
  {j : ℕ} (outer : ProcessContext j n) (inner : ProcessContext₂ k₁ k₂ j)
  (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) (t : 𝔽 (pc R₂)) →
  Fin.toℕ (thread₂ (compose₂ outer inner) R₁ R₂ t) ≡
  Fin.toℕ
    (threadInContext outer (plug₂ inner R₁ R₂) (thread₂ inner R₁ R₂ t))
thread₂-compose₂ hole inner R₁ R₂ t = refl
thread₂-compose₂ (par-left outer Q) inner R₁ R₂ t =
  Fin.toℕ-↑ˡ (thread₂ (compose₂ outer inner) R₁ R₂ t) (pc Q)
  ■ thread₂-compose₂ outer inner R₁ R₂ t
  ■ sym (Fin.toℕ-↑ˡ
          (threadInContext outer (plug₂ inner R₁ R₂) (thread₂ inner R₁ R₂ t))
          (pc Q))
thread₂-compose₂ (par-right Q outer) inner R₁ R₂ t =
  Fin.toℕ-↑ʳ (pc Q) (thread₂ (compose₂ outer inner) R₁ R₂ t)
  ■ cong (pc Q +_) (thread₂-compose₂ outer inner R₁ R₂ t)
  ■ sym (Fin.toℕ-↑ʳ (pc Q)
          (threadInContext outer (plug₂ inner R₁ R₂) (thread₂ inner R₁ R₂ t)))
thread₂-compose₂ (bind B₁ B₂ outer) inner R₁ R₂ t =
  thread₂-compose₂ outer inner R₁ R₂ t

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

-- The SIBLING companion of `Canonical.tracks-foldPar`: `foldPar` keeps the
-- threads of the ABSORBED process `Z₀` where they are as well -- the layout
-- is `[X][Z₀]` on both sides.  (A generic `Canonical.agda` lemma; it lives
-- here because `Canonical.agda` is closed for this step.)
tracks-foldPar-sib :
  (bs : BindList) {n : ℕ} (X : 𝐓.Proc (arity bs n)) (Z₀ : 𝐓.Proc n)
  (t : 𝔽 (pc Z₀))
  {a : 𝔽 (pc (plugL bs X 𝐓.∥ Z₀))}
  {b : 𝔽 (pc (plugL bs (X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL bs))))} →
  Fin.toℕ a ≡ pc X + Fin.toℕ t → Fin.toℕ b ≡ pc X + Fin.toℕ t →
  Tracks (foldPar bs X Z₀) a b
tracks-foldPar-sib L.[] X Z₀ t {a} {b} ea eb =
  tracks-substℕ (sym (𝐓.⋯ₚ-id≗ Z₀ {ϕ = wkL L.[]} (λ _ → refl)))
    {L = X 𝐓.∥ Z₀} {R = λ z → X 𝐓.∥ z} (track-ε a) (eb ■ sym ea)
tracks-foldPar-sib ((A₁ , A₂) L.∷ bs) X Z₀ t {a} {b} ea eb =
  tracks-substℕ
    (𝐓.fusionₚ Z₀ (weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (wkL bs)
     ■ 𝐓.⋯ₚ-cong Z₀ (λ _ → refl))
    {L = 𝐓.ν A₁ A₂ (plugL bs X) 𝐓.∥ Z₀}
    {R = λ z → 𝐓.ν A₁ A₂ (plugL bs (X 𝐓.∥ z))}
    (tracks-◅◅
      (∥-commℕ-r {P = 𝐓.ν A₁ A₂ (plugL bs X)} {Q = Z₀} t
        {a = a} {b = t ↑ˡ pc (plugL bs X)}
        (ea ■ cong (_+ Fin.toℕ t) (sym (pc-plugL bs X)))
        (Fin.toℕ-↑ˡ t (pc (plugL bs X))))
      (tracks-◅◅
        (ν-ext′ℕ {P = Z₀} {B₁ = A₁} {B₂ = A₂} {Q = plugL bs X}
          (t ↑ˡ pc (plugL bs X)) {b = idx fZL}
          (idx≡ fZL ■ sym (Fin.toℕ-↑ˡ t (pc (plugL bs X)))))
        (tracks-◅◅
          (tracks-gmap-ν {B₁ = A₁} {B₂ = A₂}
            (∥-commℕ-l {P = Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)}
                       {Q = plugL bs X} (idx fZw)
              {a = idx fZL} {b = idx fXZ}
              (idx≡ fZL ■ sym (idx≡ fZw))
              (idx≡ fXZ ■ cong (pc (plugL bs X) +_) (sym (idx≡ fZw)))))
          (tracks-gmap-ν
            (tracks-foldPar-sib bs X
              (Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (idx fZw)
              {a = idx fXZ} {b = idx fRes}
              (idx≡ fXZ ■ cong₂ _+_ (pc-plugL bs X) (sym (idx≡ fZw)))
              (idx≡ fRes ■ cong (pc X +_) (sym (idx≡ fZw))))))))
    (eb ■ sym (idx≡ fRes))
  where
    fZw : Front (Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (Fin.toℕ t)
    fZw = front-⋯ Z₀ (weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (front t refl)

    fZL : Front ((Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) 𝐓.∥ plugL bs X)
                (Fin.toℕ t)
    fZL = front-∥ˡ (plugL bs X) fZw

    fXZ : Front (plugL bs X 𝐓.∥ (Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)))
                (pc (plugL bs X) + Fin.toℕ t)
    fXZ = front-∥ʳ (plugL bs X) fZw

    fRes :
      Front
        (plugL bs
          (X 𝐓.∥ ((Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) 𝐓.⋯ₚ wkL bs)))
        (pc X + Fin.toℕ t)
    fRes =
      front-plugL bs
        (front-∥ʳ X
          (front-⋯ (Z₀ 𝐓.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum A₁ + sum A₂)) (wkL bs) fZw))

-- Absorbing a sibling into a TWO-LEVEL stack keeps every thread of `X`.
tracks-foldPar₂ :
  (bsA bsB : BindList) {n : ℕ}
  (X : 𝐓.Proc (arity bsB (arity bsA n))) (Z₀ : 𝐓.Proc n) (t : 𝔽 (pc X))
  {a : 𝔽 (pc (plugL bsA (plugL bsB X) 𝐓.∥ Z₀))}
  {b : 𝔽 (pc (plugL bsA (plugL bsB (X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL₂ bsA bsB)))))} →
  Fin.toℕ a ≡ Fin.toℕ t → Fin.toℕ b ≡ Fin.toℕ t →
  Tracks (foldPar₂ bsA bsB X Z₀) a b
tracks-foldPar₂ bsA bsB X Z₀ t {a} {b} ea eb =
  tracks-◅◅
    (tracks-foldPar bsA (plugL bsB X) Z₀ (idx fB)
      {a = a} {b = idx h₁} (ea ■ sym (idx≡ fB)) (idx≡ h₁ ■ sym (idx≡ fB)))
    (tracks-◅◅
      (tracks-≋-plugL bsA
        (tracks-foldPar bsB X (Z₀ 𝐓.⋯ₚ wkL bsA) t
          {a = idx fBZ} {b = idx h₂′}
          (idx≡ fBZ) (idx≡ h₂′))
        (idx≡ h₁ ■ sym (idx≡ fBZ))
        (idx≡ h₂ ■ sym (idx≡ h₂′)))
      (tracks-≡→≋ℕ
        (cong (λ z → plugL bsA (plugL bsB (X 𝐓.∥ z)))
          (𝐓.fusionₚ Z₀ (wkL bsA) (wkL bsB) ■ 𝐓.⋯ₚ-cong Z₀ (λ _ → refl)))
        (idx h₂) {b = b} (eb ■ sym (idx≡ h₂))))
  where
    fB : Front (plugL bsB X) (Fin.toℕ t)
    fB = front-plugL bsB (front t refl)

    fBZ : Front (plugL bsB X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL bsA)) (Fin.toℕ t)
    fBZ = front-∥ˡ (Z₀ 𝐓.⋯ₚ wkL bsA) fB

    h₁ : Front (plugL bsA (plugL bsB X 𝐓.∥ (Z₀ 𝐓.⋯ₚ wkL bsA))) (Fin.toℕ t)
    h₁ = front-plugL bsA fBZ

    h₂′ : Front (plugL bsB (X 𝐓.∥ ((Z₀ 𝐓.⋯ₚ wkL bsA) 𝐓.⋯ₚ wkL bsB)))
                (Fin.toℕ t)
    h₂′ = front-plugL bsB
            (front-∥ˡ ((Z₀ 𝐓.⋯ₚ wkL bsA) 𝐓.⋯ₚ wkL bsB) (front t refl))

    h₂ : Front (plugL bsA
                 (plugL bsB (X 𝐓.∥ ((Z₀ 𝐓.⋯ₚ wkL bsA) 𝐓.⋯ₚ wkL bsB))))
               (Fin.toℕ t)
    h₂ = front-plugL bsA h₂′

-- `push`, twice: the binder is commuted past the OUTER stack first and then
-- past the INNER one, so it ends up below both.
push₂ :
  (bsA bsB : BindList) (C₁ C₂ : BindGroup) {mid : ℕ}
  (T : 𝐓.Proc (arity bsB (arity bsA (sum C₁ + sum C₂ + mid)))) →
  Σ[ σ ∈ (arity bsB (arity bsA (sum C₁ + sum C₂ + mid)) →ᵣ
            (sum C₁ + sum C₂ + arity bsB (arity bsA mid))) ]
  Σ[ d ∈ (𝐓.ν C₁ C₂ (plugL bsA (plugL bsB T)) 𝐓.≋
            plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T 𝐓.⋯ₚ σ)))) ]
    (((v : 𝔽 (sum C₁ + sum C₂)) →
        σ (wkL₂ bsA bsB (v ↑ˡ mid)) ≡ v ↑ˡ arity bsB (arity bsA mid))
     -- THREAD TRACKING: both extrusions are renamings, so every thread of
     -- `T` keeps its numeric position.
     × ((t : 𝔽 (pc T))
        {a : 𝔽 (pc (𝐓.ν C₁ C₂ (plugL bsA (plugL bsB T))))}
        {b : 𝔽 (pc (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T 𝐓.⋯ₚ σ)))))} →
        Fin.toℕ a ≡ Fin.toℕ t → Fin.toℕ b ≡ Fin.toℕ t → Tracks d a b))
push₂ bsA bsB C₁ C₂ {mid} T
  with push bsA C₁ C₂ {mid} (plugL bsB T)
... | σA , ≋A , hndA , trkA
  with push bsB C₁ C₂ {arity bsA mid} (T 𝐓.⋯ₚ liftL bsB σA)
...  | σB , ≋B , hndB , trkB =
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
  , (λ t {a} {b} ea eb →
      let f₀ : Front (plugL bsB T) (Fin.toℕ t)
          f₀ = front-plugL bsB (front t refl)

          f₀σ : Front (plugL bsB T 𝐓.⋯ₚ σA) (Fin.toℕ t)
          f₀σ = front-⋯ (plugL bsB T) σA f₀

          fA : Front (plugL bsA (𝐓.ν C₁ C₂ (plugL bsB T 𝐓.⋯ₚ σA)))
                     (Fin.toℕ t)
          fA = front-plugL bsA (front-ν f₀σ)

          fT′ : Front (T 𝐓.⋯ₚ liftL bsB σA) (Fin.toℕ t)
          fT′ = front-⋯ T (liftL bsB σA) (front t refl)

          fB : Front (plugL bsB (T 𝐓.⋯ₚ liftL bsB σA)) (Fin.toℕ t)
          fB = front-plugL bsB fT′

          fBν : Front
                  (plugL bsA
                    (𝐓.ν C₁ C₂ (plugL bsB (T 𝐓.⋯ₚ liftL bsB σA))))
                  (Fin.toℕ t)
          fBν = front-plugL bsA (front-ν fB)

          fC′ : Front
                  (plugL bsB
                    (𝐓.ν C₁ C₂ ((T 𝐓.⋯ₚ liftL bsB σA) 𝐓.⋯ₚ σB)))
                  (Fin.toℕ t)
          fC′ = front-plugL bsB
                  (front-ν (front-⋯ (T 𝐓.⋯ₚ liftL bsB σA) σB fT′))

          fC : Front
                 (plugL bsA
                   (plugL bsB
                     (𝐓.ν C₁ C₂ ((T 𝐓.⋯ₚ liftL bsB σA) 𝐓.⋯ₚ σB))))
                 (Fin.toℕ t)
          fC = front-plugL bsA fC′
      in
      tracks-◅◅
        (trkA (idx f₀) {a = a} {b = idx fA}
          (ea ■ sym (idx≡ f₀)) (idx≡ fA ■ sym (idx≡ f₀)))
        (tracks-◅◅
          (tracks-≋-plugL bsA
            (tracks-gmap-ν
              (tracks-≡→≋ℕ (plugL-⋯ bsB T σA) (idx f₀σ) {b = idx fB}
                (idx≡ fB ■ sym (idx≡ f₀σ))))
            (idx≡ fA ■ sym (idx≡ f₀σ))
            (idx≡ fBν ■ sym (idx≡ fB)))
          (tracks-◅◅
            (tracks-≋-plugL bsA
              (trkB (idx fT′) {a = idx fB} {b = idx fC′}
                (idx≡ fB ■ sym (idx≡ fT′)) (idx≡ fC′ ■ sym (idx≡ fT′)))
              (idx≡ fBν ■ sym (idx≡ fB)) (idx≡ fC ■ sym (idx≡ fC′)))
            (tracks-≡→≋ℕ
              (cong (λ z → plugL bsA (plugL bsB (𝐓.ν C₁ C₂ z)))
                (𝐓.fusionₚ T (liftL bsB σA) σB
                 ■ 𝐓.⋯ₚ-cong T (λ _ → refl)))
              (idx fC) {b = b} (eb ■ sym (idx≡ fC))))))

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

  -- The forward `∥-assoc` with numeric indices (`Canonical.agda` exports
  -- only the `≋-sym` form, `∥-assoc-symℕ`).
  ∥-assocℕ :
    {n : ℕ} {P₁ P₂ P₃ : 𝐓.Proc n} (ix : 𝔽 (pc P₁ + (pc P₂ + pc P₃)))
    {a : 𝔽 (pc P₁ + (pc P₂ + pc P₃))} {b : 𝔽 (pc P₁ + pc P₂ + pc P₃)} →
    Fin.toℕ a ≡ Fin.toℕ ix → Fin.toℕ b ≡ Fin.toℕ ix →
    Tracks (𝐓.∥-assoc {P₁ = P₁} {P₂ = P₂} {P₃ = P₃}) a b
  ∥-assocℕ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} ix ea eb =
    tracks-castℕ (tracks-∥-assoc {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} ix)
      (sym ea)
      (Fin.toℕ-cast (sym (+-assoc (pc P₁) (pc P₂) (pc P₃))) ix ■ sym eb)

  -- `∥-shuffle` moves the thread block of `c` to the FRONT and the block of
  -- `a` right behind it; `b` and `d` end up in the trailing pair.
  tracks-∥-shuffle-c :
    {n : ℕ} (a₀ b₀ c₀ d₀ : 𝐓.Proc n) (ix : 𝔽 (pc c₀))
    {a : 𝔽 (pc ((a₀ 𝐓.∥ b₀) 𝐓.∥ (c₀ 𝐓.∥ d₀)))}
    {b : 𝔽 (pc ((c₀ 𝐓.∥ a₀) 𝐓.∥ (d₀ 𝐓.∥ b₀)))} →
    Fin.toℕ a ≡ pc a₀ + pc b₀ + Fin.toℕ ix → Fin.toℕ b ≡ Fin.toℕ ix →
    Tracks (∥-shuffle a₀ b₀ c₀ d₀) a b
  tracks-∥-shuffle-c a₀ b₀ c₀ d₀ ix {a} {b} ea eb =
    tracks-◅◅
      (∥-assocℕ {P₁ = a₀ 𝐓.∥ b₀} {P₂ = c₀} {P₃ = d₀} (idx f0)
        {a = a} {b = idx f1} (ea ■ sym (idx≡ f0)) (idx≡ f1 ■ sym (idx≡ f0)))
      (tracks-◅◅
        (tracks-∥-cong-l {d₂ = ≋-refl}
          (∥-assoc-symℕ {P₁ = a₀} {P₂ = b₀} {P₃ = c₀} (idx g2)
            {a = idx g1} {b = idx g2}
            (idx≡ g1 ■ +-assoc (pc a₀) (pc b₀) (Fin.toℕ ix) ■ sym (idx≡ g2))
            refl))
        (tracks-◅◅
          (tracks-∥-cong-l {d₂ = ≋-refl}
            (tracks-∥-cong-r {d₁ = ≋-refl}
              (∥-commℕ-r {P = b₀} {Q = c₀} ix
                {a = pc b₀ ↑ʳ ix} {b = ix ↑ˡ pc b₀}
                (Fin.toℕ-↑ʳ (pc b₀) ix) (Fin.toℕ-↑ˡ ix (pc b₀)))))
          (tracks-◅◅
            (tracks-∥-cong-l {d₂ = ≋-refl}
              (∥-assocℕ {P₁ = a₀} {P₂ = c₀} {P₃ = b₀} (idx g3)
                {a = idx g3} {b = idx g4} refl
                (idx≡ g4 ■ sym (idx≡ g3))))
            (tracks-◅◅
              (tracks-∥-cong-l {d₂ = ≋-refl}
                (tracks-∥-cong-l {d₂ = ≋-refl}
                  (∥-commℕ-r {P = a₀} {Q = c₀} ix
                    {a = pc a₀ ↑ʳ ix} {b = ix ↑ˡ pc a₀}
                    (Fin.toℕ-↑ʳ (pc a₀) ix) (Fin.toℕ-↑ˡ ix (pc a₀)))))
              (tracks-◅◅
                (∥-assoc-symℕ {P₁ = c₀ 𝐓.∥ a₀} {P₂ = b₀} {P₃ = d₀}
                  (idx f6) {a = idx f5} {b = idx f6}
                  (idx≡ f5 ■ sym (idx≡ f6)) refl)
                (tracks-castℕ
                  (tracks-∥-cong-l {d₁ = ≋-refl} {d₂ = 𝐓.∥-comm}
                    (track-ε (idx h)))
                  refl (idx≡ f7 ■ sym eb)))))))
    where
      fc : Front c₀ (Fin.toℕ ix)
      fc = front ix refl

      f0 : Front ((a₀ 𝐓.∥ b₀) 𝐓.∥ (c₀ 𝐓.∥ d₀))
                 (pc (a₀ 𝐓.∥ b₀) + Fin.toℕ ix)
      f0 = front-∥ʳ (a₀ 𝐓.∥ b₀) (front-∥ˡ d₀ fc)

      g1 : Front ((a₀ 𝐓.∥ b₀) 𝐓.∥ c₀) (pc (a₀ 𝐓.∥ b₀) + Fin.toℕ ix)
      g1 = front-∥ʳ (a₀ 𝐓.∥ b₀) fc

      f1 : Front (((a₀ 𝐓.∥ b₀) 𝐓.∥ c₀) 𝐓.∥ d₀)
                 (pc (a₀ 𝐓.∥ b₀) + Fin.toℕ ix)
      f1 = front-∥ˡ d₀ g1

      g2 : Front (a₀ 𝐓.∥ (b₀ 𝐓.∥ c₀)) (pc a₀ + (pc b₀ + Fin.toℕ ix))
      g2 = front-∥ʳ a₀ (front-∥ʳ b₀ fc)

      g3 : Front (a₀ 𝐓.∥ (c₀ 𝐓.∥ b₀)) (pc a₀ + Fin.toℕ ix)
      g3 = front-∥ʳ a₀ (front-∥ˡ b₀ fc)

      g4 : Front ((a₀ 𝐓.∥ c₀) 𝐓.∥ b₀) (pc a₀ + Fin.toℕ ix)
      g4 = front-∥ˡ b₀ (front-∥ʳ a₀ fc)

      f5 : Front (((c₀ 𝐓.∥ a₀) 𝐓.∥ b₀) 𝐓.∥ d₀) (Fin.toℕ ix)
      f5 = front-∥ˡ d₀ (front-∥ˡ b₀ (front-∥ˡ a₀ fc))

      h : Front (c₀ 𝐓.∥ a₀) (Fin.toℕ ix)
      h = front-∥ˡ a₀ fc

      f6 : Front ((c₀ 𝐓.∥ a₀) 𝐓.∥ (b₀ 𝐓.∥ d₀)) (Fin.toℕ ix)
      f6 = front-∥ˡ (b₀ 𝐓.∥ d₀) h

      f7 : Front ((c₀ 𝐓.∥ a₀) 𝐓.∥ (d₀ 𝐓.∥ b₀)) (Fin.toℕ ix)
      f7 = front-∥ˡ (d₀ 𝐓.∥ b₀) h

  tracks-∥-shuffle-a :
    {n : ℕ} (a₀ b₀ c₀ d₀ : 𝐓.Proc n) (ix : 𝔽 (pc a₀))
    {a : 𝔽 (pc ((a₀ 𝐓.∥ b₀) 𝐓.∥ (c₀ 𝐓.∥ d₀)))}
    {b : 𝔽 (pc ((c₀ 𝐓.∥ a₀) 𝐓.∥ (d₀ 𝐓.∥ b₀)))} →
    Fin.toℕ a ≡ Fin.toℕ ix → Fin.toℕ b ≡ pc c₀ + Fin.toℕ ix →
    Tracks (∥-shuffle a₀ b₀ c₀ d₀) a b
  tracks-∥-shuffle-a a₀ b₀ c₀ d₀ ix {a} {b} ea eb =
    tracks-◅◅
      (∥-assocℕ {P₁ = a₀ 𝐓.∥ b₀} {P₂ = c₀} {P₃ = d₀} (idx p0)
        {a = a} {b = idx p1} (ea ■ sym (idx≡ p0)) (idx≡ p1 ■ sym (idx≡ p0)))
      (tracks-◅◅
        (tracks-∥-cong-l {d₂ = ≋-refl}
          (∥-assoc-symℕ {P₁ = a₀} {P₂ = b₀} {P₃ = c₀} (idx q2)
            {a = idx q1} {b = idx q2}
            (idx≡ q1 ■ sym (idx≡ q2)) refl))
        (tracks-◅◅
          (tracks-∥-cong-l {d₂ = ≋-refl}
            (tracks-∥-cong-l {d₁ = ≋-refl} {d₂ = 𝐓.∥-comm}
              (track-ε ix)))
          (tracks-◅◅
            (tracks-∥-cong-l {d₂ = ≋-refl}
              (∥-assocℕ {P₁ = a₀} {P₂ = c₀} {P₃ = b₀} (idx q3)
                {a = idx q3} {b = idx q4} refl
                (idx≡ q4 ■ sym (idx≡ q3))))
            (tracks-◅◅
              (tracks-∥-cong-l {d₂ = ≋-refl}
                (tracks-∥-cong-l {d₂ = ≋-refl}
                  (∥-commℕ-l {P = a₀} {Q = c₀} ix
                    {a = ix ↑ˡ pc c₀} {b = pc c₀ ↑ʳ ix}
                    (Fin.toℕ-↑ˡ ix (pc c₀)) (Fin.toℕ-↑ʳ (pc c₀) ix))))
              (tracks-◅◅
                (∥-assoc-symℕ {P₁ = c₀ 𝐓.∥ a₀} {P₂ = b₀} {P₃ = d₀}
                  (idx p6) {a = idx p5} {b = idx p6}
                  (idx≡ p5 ■ sym (idx≡ p6)) refl)
                (tracks-castℕ
                  (tracks-∥-cong-l {d₁ = ≋-refl} {d₂ = 𝐓.∥-comm}
                    (track-ε (idx hh)))
                  refl (idx≡ p7 ■ sym eb)))))))
    where
      fa : Front a₀ (Fin.toℕ ix)
      fa = front ix refl

      p0 : Front ((a₀ 𝐓.∥ b₀) 𝐓.∥ (c₀ 𝐓.∥ d₀)) (Fin.toℕ ix)
      p0 = front-∥ˡ (c₀ 𝐓.∥ d₀) (front-∥ˡ b₀ fa)

      q1 : Front ((a₀ 𝐓.∥ b₀) 𝐓.∥ c₀) (Fin.toℕ ix)
      q1 = front-∥ˡ c₀ (front-∥ˡ b₀ fa)

      p1 : Front (((a₀ 𝐓.∥ b₀) 𝐓.∥ c₀) 𝐓.∥ d₀) (Fin.toℕ ix)
      p1 = front-∥ˡ d₀ q1

      q2 : Front (a₀ 𝐓.∥ (b₀ 𝐓.∥ c₀)) (Fin.toℕ ix)
      q2 = front-∥ˡ (b₀ 𝐓.∥ c₀) fa

      q3 : Front (a₀ 𝐓.∥ (c₀ 𝐓.∥ b₀)) (Fin.toℕ ix)
      q3 = front-∥ˡ (c₀ 𝐓.∥ b₀) fa

      q4 : Front ((a₀ 𝐓.∥ c₀) 𝐓.∥ b₀) (Fin.toℕ ix)
      q4 = front-∥ˡ b₀ (front-∥ˡ c₀ fa)

      p5 : Front (((c₀ 𝐓.∥ a₀) 𝐓.∥ b₀) 𝐓.∥ d₀) (pc c₀ + Fin.toℕ ix)
      p5 = front-∥ˡ d₀ (front-∥ˡ b₀ (front-∥ʳ c₀ fa))

      hh : Front (c₀ 𝐓.∥ a₀) (pc c₀ + Fin.toℕ ix)
      hh = front-∥ʳ c₀ fa

      p6 : Front ((c₀ 𝐓.∥ a₀) 𝐓.∥ (b₀ 𝐓.∥ d₀)) (pc c₀ + Fin.toℕ ix)
      p6 = front-∥ˡ (b₀ 𝐓.∥ d₀) hh

      p7 : Front ((c₀ 𝐓.∥ a₀) 𝐓.∥ (d₀ 𝐓.∥ b₀)) (pc c₀ + Fin.toℕ ix)
      p7 = front-∥ˡ (d₀ 𝐓.∥ b₀) hh

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
    -- THREAD TRACKING (`PLAN.md` §12.2, P5.2b): the threads of the FIRST
    -- hole become the LEADING block of the bubbled process and those of the
    -- SECOND hole follow immediately behind them.
    tracks₁ : (Z₁ : 𝐓.Proc k₁) (Z₂ : 𝐓.Proc k₂) (t : 𝔽 (pc Z₁))
              {b : 𝔽 (pc (plugL bsA
                            (plugL bsB
                              (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂))
                               𝐓.∥ resid))))} →
              Fin.toℕ b ≡ Fin.toℕ t →
              Tracks (≋-eq Z₁ Z₂) (thread₁ c Z₁ Z₂ t) b
    tracks₂ : (Z₁ : 𝐓.Proc k₁) (Z₂ : 𝐓.Proc k₂) (t : 𝔽 (pc Z₂))
              {b : 𝔽 (pc (plugL bsA
                            (plugL bsB
                              (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂))
                               𝐓.∥ resid))))} →
              Fin.toℕ b ≡ pc Z₁ + Fin.toℕ t →
              Tracks (≋-eq Z₁ Z₂) (thread₂ c Z₁ Z₂ t) b

private
  -- The LEAF: the two branches meet.  `bubble` normalises each of them; the
  -- second stack is then pushed INSIDE the first (`foldPar`, `plugL-⋯`).
  bubblePar :
    (c₁ : ProcessContext k₁ n) (c₂ : ProcessContext k₂ n) →
    Bubble₂ (par₂ c₁ c₂)
  bubblePar c₁ c₂ with bubble c₁ | bubble c₂
  ... | bubbled bs₁ σ₁ Q₁ eq₁ am₁ tk₁ | bubbled bs₂ σ₂ Q₂ eq₂ am₂ tk₂ =
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
      -- THREAD TRACKING, first hole: `∥-shuffle` sends its `c` block --
      -- the threads of `Z₁` -- to the front.
      (λ Z₁ Z₂ t {b} eb →
        let u₁ = front-⋯ Z₁ σ₁ (front {P = Z₁} t refl)
            w₁ = front-∥ˡ Q₁ u₁
            a₁ = front-plugL bs₁ w₁
            e₂ = front-plugL bs₁
                   (front-∥ˡ
                     (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ wkL bs₁) w₁)
            e₃′ = front-∥ˡ
                    (plugL bs₂
                      (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
                    w₁
            e₃ = front-plugL bs₁ e₃′
            e₄′ = front-∥ʳ
                    (plugL bs₂
                      (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
                    w₁
            e₄ = front-plugL bs₁ e₄′
            e₅″ = front-∥ʳ
                    (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                    (front-⋯ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) (wkL bs₂) w₁)
            e₅′ = front-plugL bs₂ e₅″
            e₅ = front-plugL bs₁ e₅′
            uc = front-⋯ (Z₁ 𝐓.⋯ₚ σ₁) (wkL bs₂) u₁
            e₆″ = front-∥ˡ
                    ((Q₁ 𝐓.⋯ₚ wkL bs₂)
                     𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
                    (front-∥ˡ
                      ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)) uc)
            e₆′ = front-plugL bs₂ e₆″
            e₆ = front-plugL bs₁ e₆′
        in
        tracks-◅◅
          (tracks-∥-cong-l {d₂ = eq₂ Z₂} (tk₁ Z₁ t {idx a₁} (idx≡ a₁)))
          (tracks-◅◅
            (tracks-foldPar bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)
              (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)) (idx w₁)
              {a = idx a₁ ↑ˡ pc (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂))}
              {b = idx e₂}
              (Fin.toℕ-↑ˡ (idx a₁)
                 (pc (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)))
               ■ idx≡ a₁ ■ sym (idx≡ w₁))
              (idx≡ e₂ ■ sym (idx≡ w₁)))
            (tracks-◅◅
              (tracks-≡→≋ℕ
                (cong (λ z → plugL bs₁ (((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) 𝐓.∥ z))
                  (plugL-⋯ bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) (wkL bs₁)))
                (idx e₂) {b = idx e₃} (idx≡ e₃ ■ sym (idx≡ e₂)))
              (tracks-◅◅
                (tracks-≋-plugL bs₁
                  (∥-commℕ-l
                    {P = (Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁}
                    {Q = plugL bs₂
                           (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                            𝐓.⋯ₚ liftL bs₂ (wkL bs₁))}
                    (idx w₁) {a = idx e₃′} {b = idx e₄′}
                    (idx≡ e₃′ ■ sym (idx≡ w₁))
                    (idx≡ e₄′
                     ■ cong
                         (pc (plugL bs₂
                               (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                                𝐓.⋯ₚ liftL bs₂ (wkL bs₁))) +_)
                         (sym (idx≡ w₁))))
                  (idx≡ e₃ ■ sym (idx≡ e₃′)) (idx≡ e₄ ■ sym (idx≡ e₄′)))
                (tracks-◅◅
                  (tracks-≋-plugL bs₁
                    (tracks-foldPar-sib bs₂
                      (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                      ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) (idx w₁)
                      {a = idx e₄′} {b = idx e₅′}
                      (idx≡ e₄′
                       ■ cong₂ _+_
                           (pc-plugL bs₂
                             (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                              𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
                           (sym (idx≡ w₁)))
                      (idx≡ e₅′
                       ■ cong
                           (pc (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                                 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)) +_)
                           (sym (idx≡ w₁))))
                    (idx≡ e₄ ■ sym (idx≡ e₄′)) (idx≡ e₅ ■ sym (idx≡ e₅′)))
                  (tracks-◅◅
                    (tracks-≋-plugL bs₁
                      (tracks-≋-plugL bs₂
                        (tracks-∥-shuffle-c
                          ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                          (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                          ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.⋯ₚ wkL bs₂)
                          (Q₁ 𝐓.⋯ₚ wkL bs₂)
                          (idx uc) {a = idx e₅″} {b = idx e₆″}
                          (idx≡ e₅″
                           ■ cong
                               (pc (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                                     𝐓.⋯ₚ liftL bs₂ (wkL bs₁)) +_)
                               (sym (idx≡ uc)))
                          (idx≡ e₆″ ■ sym (idx≡ uc)))
                        (idx≡ e₅′ ■ sym (idx≡ e₅″))
                        (idx≡ e₆′ ■ sym (idx≡ e₆″)))
                      (idx≡ e₅ ■ sym (idx≡ e₅′)) (idx≡ e₆ ■ sym (idx≡ e₆′)))
                    (tracks-≡→≋ℕ
                      (cong₂
                        (λ u₁ u₂ →
                          plugL bs₁
                            (plugL bs₂
                              ((u₁ 𝐓.∥ u₂)
                               𝐓.∥ ((Q₁ 𝐓.⋯ₚ wkL bs₂)
                                    𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))))))
                        (𝐓.fusionₚ Z₁ σ₁ (wkL bs₂)
                         ■ 𝐓.⋯ₚ-cong Z₁ (λ _ → refl))
                        (𝐓.fusionₚ Z₂ σ₂ (liftL bs₂ (wkL bs₁))
                         ■ 𝐓.⋯ₚ-cong Z₂ (λ _ → refl)))
                      (idx e₆) {b = b} (eb ■ sym (idx≡ e₆)))))))))
      -- THREAD TRACKING, second hole: `∥-shuffle` sends its `a` block --
      -- the threads of `Z₂` -- immediately behind the `c` block.
      (λ Z₁ Z₂ t {b} eb →
        let u₂ = front-⋯ Z₂ σ₂ (front {P = Z₂} t refl)
            w₂ = front-∥ˡ Q₂ u₂
            a₂ = front-plugL bs₂ w₂
            g₂ = front-plugL bs₁
                   (front-∥ʳ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)
                     (front-⋯ (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂))
                       (wkL bs₁) a₂))
            aX = front-⋯ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) (liftL bs₂ (wkL bs₁)) w₂
            bX = front-plugL bs₂ aX
            g₃′ = front-∥ʳ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) bX
            g₃ = front-plugL bs₁ g₃′
            g₄′ = front-∥ˡ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) bX
            g₄ = front-plugL bs₁ g₄′
            g₅″ = front-∥ˡ (((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) 𝐓.⋯ₚ wkL bs₂) aX
            g₅′ = front-plugL bs₂ g₅″
            g₅ = front-plugL bs₁ g₅′
            uz = front-⋯ (Z₂ 𝐓.⋯ₚ σ₂) (liftL bs₂ (wkL bs₁)) u₂
            g₆″ = front-∥ˡ
                    ((Q₁ 𝐓.⋯ₚ wkL bs₂)
                     𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁)))
                    (front-∥ʳ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.⋯ₚ wkL bs₂) uz)
            g₆′ = front-plugL bs₂ g₆″
            g₆ = front-plugL bs₁ g₆′
        in
        tracks-◅◅
          (tracks-∥-cong-r {d₁ = eq₁ Z₁} (tk₂ Z₂ t {idx a₂} (idx≡ a₂)))
          (tracks-◅◅
            (tracks-foldPar-sib bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)
              (plugL bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)) (idx a₂)
              {a = pc (plugL bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)) ↑ʳ idx a₂}
              {b = idx g₂}
              (Fin.toℕ-↑ʳ (pc (plugL bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁))) (idx a₂)
               ■ cong (_+ Fin.toℕ (idx a₂))
                   (pc-plugL bs₁ ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁)))
              (idx≡ g₂
               ■ cong (pc ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) +_) (sym (idx≡ a₂))))
            (tracks-◅◅
              (tracks-≡→≋ℕ
                (cong (λ z → plugL bs₁ (((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) 𝐓.∥ z))
                  (plugL-⋯ bs₂ ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) (wkL bs₁)))
                (idx g₂) {b = idx g₃} (idx≡ g₃ ■ sym (idx≡ g₂)))
              (tracks-◅◅
                (tracks-≋-plugL bs₁
                  (∥-commℕ-r
                    {P = (Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁}
                    {Q = plugL bs₂
                           (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂)
                            𝐓.⋯ₚ liftL bs₂ (wkL bs₁))}
                    (idx bX) {a = idx g₃′} {b = idx g₄′}
                    (idx≡ g₃′
                     ■ cong (pc ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) +_)
                         (sym (idx≡ bX)))
                    (idx≡ g₄′ ■ sym (idx≡ bX)))
                  (idx≡ g₃ ■ sym (idx≡ g₃′)) (idx≡ g₄ ■ sym (idx≡ g₄′)))
                (tracks-◅◅
                  (tracks-≋-plugL bs₁
                    (tracks-foldPar bs₂
                      (((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.∥ Q₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                      ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.∥ Q₁) (idx aX)
                      {a = idx g₄′} {b = idx g₅′}
                      (idx≡ g₄′ ■ sym (idx≡ aX))
                      (idx≡ g₅′ ■ sym (idx≡ aX)))
                    (idx≡ g₄ ■ sym (idx≡ g₄′)) (idx≡ g₅ ■ sym (idx≡ g₅′)))
                  (tracks-◅◅
                    (tracks-≋-plugL bs₁
                      (tracks-≋-plugL bs₂
                        (tracks-∥-shuffle-a
                          ((Z₂ 𝐓.⋯ₚ σ₂) 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                          (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))
                          ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.⋯ₚ wkL bs₂)
                          (Q₁ 𝐓.⋯ₚ wkL bs₂)
                          (idx uz) {a = idx g₅″} {b = idx g₆″}
                          (idx≡ g₅″ ■ sym (idx≡ uz))
                          (idx≡ g₆″
                           ■ cong (pc ((Z₁ 𝐓.⋯ₚ σ₁) 𝐓.⋯ₚ wkL bs₂) +_)
                               (sym (idx≡ uz))))
                        (idx≡ g₅′ ■ sym (idx≡ g₅″))
                        (idx≡ g₆′ ■ sym (idx≡ g₆″)))
                      (idx≡ g₅ ■ sym (idx≡ g₅′)) (idx≡ g₆ ■ sym (idx≡ g₆′)))
                    (tracks-≡→≋ℕ
                      (cong₂
                        (λ u₁ u₂ →
                          plugL bs₁
                            (plugL bs₂
                              ((u₁ 𝐓.∥ u₂)
                               𝐓.∥ ((Q₁ 𝐓.⋯ₚ wkL bs₂)
                                    𝐓.∥ (Q₂ 𝐓.⋯ₚ liftL bs₂ (wkL bs₁))))))
                        (𝐓.fusionₚ Z₁ σ₁ (wkL bs₂)
                         ■ 𝐓.⋯ₚ-cong Z₁ (λ _ → refl))
                        (𝐓.fusionₚ Z₂ σ₂ (liftL bs₂ (wkL bs₁))
                         ■ 𝐓.⋯ₚ-cong Z₂ (λ _ → refl)))
                      (idx g₆) {b = b}
                      (eb
                       ■ cong (_+ Fin.toℕ t)
                           (sym (processCount-rename (Z₁ 𝐓.⋯ₚ σ₁) (wkL bs₂)
                                 ■ processCount-rename Z₁ σ₁))
                       ■ sym (idx≡ g₆)))))))))

bubble₂ : (c : ProcessContext₂ k₁ k₂ n) → Bubble₂ c
bubble₂ (par₂ c₁ c₂) = bubblePar c₁ c₂
bubble₂ (par₂ˢ c₂ c₁) with bubblePar c₁ c₂
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ tk₁ tk₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ Q (λ Z₁ Z₂ → 𝐓.∥-comm ◅◅ eq Z₁ Z₂) am₁ am₂
    (λ Z₁ Z₂ t {b} eb →
      tracks-◅◅
        (∥-commℕ-r {P = plug c₂ Z₂} {Q = plug c₁ Z₁}
          (threadInContext c₁ Z₁ t)
          {a = pc (plug c₂ Z₂) ↑ʳ threadInContext c₁ Z₁ t}
          {b = threadInContext c₁ Z₁ t ↑ˡ pc (plug c₂ Z₂)}
          (Fin.toℕ-↑ʳ (pc (plug c₂ Z₂)) (threadInContext c₁ Z₁ t))
          (Fin.toℕ-↑ˡ (threadInContext c₁ Z₁ t) (pc (plug c₂ Z₂))))
        (tk₁ Z₁ Z₂ t eb))
    (λ Z₁ Z₂ t {b} eb →
      tracks-◅◅
        (∥-commℕ-l {P = plug c₂ Z₂} {Q = plug c₁ Z₁}
          (threadInContext c₂ Z₂ t)
          {a = threadInContext c₂ Z₂ t ↑ˡ pc (plug c₁ Z₁)}
          {b = pc (plug c₁ Z₁) ↑ʳ threadInContext c₂ Z₂ t}
          (Fin.toℕ-↑ˡ (threadInContext c₂ Z₂ t) (pc (plug c₁ Z₁)))
          (Fin.toℕ-↑ʳ (pc (plug c₁ Z₁)) (threadInContext c₂ Z₂ t)))
        (tk₂ Z₁ Z₂ t eb))
bubble₂ (left₂ c Q₀) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ tk₁ tk₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB))
    (λ Z₁ Z₂ →
      𝐓.∥-cong (eq Z₁ Z₂) ≋-refl
      ◅◅ foldPar₂ bsA bsB
           (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀
      ◅◅ ≋-plugL bsA (≋-plugL bsB (≋-sym 𝐓.∥-assoc)))
    am₁ am₂
    (λ Z₁ Z₂ t {b} eb →
      let hd = front-∥ˡ (Z₂ 𝐓.⋯ₚ ρ₂)
                 (front-⋯ Z₁ ρ₁ (front {P = Z₁} t refl))
          fX = front-∥ˡ Q hd
          m = front-plugL bsA (front-plugL bsB fX)
          m₂′ = front-∥ˡ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB) fX
          m₂ᴮ = front-plugL bsB m₂′
          m₂ = front-plugL bsA m₂ᴮ
          m₃′ = front-∥ˡ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB)) hd
          m₃ᴮ = front-plugL bsB m₃′
      in
      tracks-◅◅
        (tracks-∥-cong-l {d₂ = ≋-refl} (tk₁ Z₁ Z₂ t {idx m} (idx≡ m)))
        (tracks-◅◅
          (tracks-foldPar₂ bsA bsB
            (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀ (idx fX)
            {a = idx m ↑ˡ pc Q₀} {b = idx m₂}
            (Fin.toℕ-↑ˡ (idx m) (pc Q₀) ■ idx≡ m ■ sym (idx≡ fX))
            (idx≡ m₂ ■ sym (idx≡ fX)))
          (tracks-≋-plugL bsA
            (tracks-≋-plugL bsB
              (∥-assoc-symℕ
                {P₁ = (Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)} {P₂ = Q}
                {P₃ = Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB}
                (idx m₃′) {a = idx m₂′} {b = idx m₃′}
                (idx≡ m₂′ ■ sym (idx≡ m₃′)) refl)
              (idx≡ m₂ᴮ ■ sym (idx≡ m₂′)) (idx≡ m₃ᴮ ■ sym (idx≡ m₃′)))
            (idx≡ m₂ ■ sym (idx≡ m₂ᴮ)) (eb ■ sym (idx≡ m₃ᴮ)))))
    (λ Z₁ Z₂ t {b} eb →
      let hd = front-∥ʳ (Z₁ 𝐓.⋯ₚ ρ₁)
                 (front-⋯ Z₂ ρ₂ (front {P = Z₂} t refl))
          fX = front-∥ˡ Q hd
          m = front-plugL bsA (front-plugL bsB fX)
          m₂′ = front-∥ˡ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB) fX
          m₂ᴮ = front-plugL bsB m₂′
          m₂ = front-plugL bsA m₂ᴮ
          m₃′ = front-∥ˡ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB)) hd
          m₃ᴮ = front-plugL bsB m₃′
      in
      tracks-◅◅
        (tracks-∥-cong-l {d₂ = ≋-refl}
          (tk₂ Z₁ Z₂ t {idx m}
            (idx≡ m ■ cong (_+ Fin.toℕ t) (processCount-rename Z₁ ρ₁))))
        (tracks-◅◅
          (tracks-foldPar₂ bsA bsB
            (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀ (idx fX)
            {a = idx m ↑ˡ pc Q₀} {b = idx m₂}
            (Fin.toℕ-↑ˡ (idx m) (pc Q₀) ■ idx≡ m ■ sym (idx≡ fX))
            (idx≡ m₂ ■ sym (idx≡ fX)))
          (tracks-≋-plugL bsA
            (tracks-≋-plugL bsB
              (∥-assoc-symℕ
                {P₁ = (Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)} {P₂ = Q}
                {P₃ = Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB}
                (idx m₃′) {a = idx m₂′} {b = idx m₃′}
                (idx≡ m₂′ ■ sym (idx≡ m₃′)) refl)
              (idx≡ m₂ᴮ ■ sym (idx≡ m₂′)) (idx≡ m₃ᴮ ■ sym (idx≡ m₃′)))
            (idx≡ m₂ ■ sym (idx≡ m₂ᴮ))
            (eb
             ■ cong (_+ Fin.toℕ t) (sym (processCount-rename Z₁ ρ₁))
             ■ sym (idx≡ m₃ᴮ)))))
bubble₂ (right₂ Q₀ c) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ tk₁ tk₂ =
  bubbled₂ bsA bsB ρ₁ ρ₂ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB))
    (λ Z₁ Z₂ →
      𝐓.∥-cong ≋-refl (eq Z₁ Z₂)
      ◅◅ 𝐓.∥-comm
      ◅◅ foldPar₂ bsA bsB
           (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀
      ◅◅ ≋-plugL bsA (≋-plugL bsB (≋-sym 𝐓.∥-assoc)))
    am₁ am₂
    (λ Z₁ Z₂ t {b} eb →
      let hd = front-∥ˡ (Z₂ 𝐓.⋯ₚ ρ₂)
                 (front-⋯ Z₁ ρ₁ (front {P = Z₁} t refl))
          fX = front-∥ˡ Q hd
          m = front-plugL bsA (front-plugL bsB fX)
          m₂′ = front-∥ˡ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB) fX
          m₂ᴮ = front-plugL bsB m₂′
          m₂ = front-plugL bsA m₂ᴮ
          m₃′ = front-∥ˡ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB)) hd
          m₃ᴮ = front-plugL bsB m₃′
      in
      tracks-◅◅
        (tracks-∥-cong-r {d₁ = ≋-refl} (tk₁ Z₁ Z₂ t {idx m} (idx≡ m)))
        (tracks-◅◅
          (∥-commℕ-r {P = Q₀}
            {Q = plugL bsA
                   (plugL bsB
                     (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q))}
            (idx m) {a = pc Q₀ ↑ʳ idx m} {b = idx m ↑ˡ pc Q₀}
            (Fin.toℕ-↑ʳ (pc Q₀) (idx m)) (Fin.toℕ-↑ˡ (idx m) (pc Q₀)))
          (tracks-◅◅
            (tracks-foldPar₂ bsA bsB
              (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀ (idx fX)
              {a = idx m ↑ˡ pc Q₀} {b = idx m₂}
              (Fin.toℕ-↑ˡ (idx m) (pc Q₀) ■ idx≡ m ■ sym (idx≡ fX))
              (idx≡ m₂ ■ sym (idx≡ fX)))
            (tracks-≋-plugL bsA
              (tracks-≋-plugL bsB
                (∥-assoc-symℕ
                  {P₁ = (Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)} {P₂ = Q}
                  {P₃ = Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB}
                  (idx m₃′) {a = idx m₂′} {b = idx m₃′}
                  (idx≡ m₂′ ■ sym (idx≡ m₃′)) refl)
                (idx≡ m₂ᴮ ■ sym (idx≡ m₂′)) (idx≡ m₃ᴮ ■ sym (idx≡ m₃′)))
              (idx≡ m₂ ■ sym (idx≡ m₂ᴮ)) (eb ■ sym (idx≡ m₃ᴮ))))))
    (λ Z₁ Z₂ t {b} eb →
      let hd = front-∥ʳ (Z₁ 𝐓.⋯ₚ ρ₁)
                 (front-⋯ Z₂ ρ₂ (front {P = Z₂} t refl))
          fX = front-∥ˡ Q hd
          m = front-plugL bsA (front-plugL bsB fX)
          m₂′ = front-∥ˡ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB) fX
          m₂ᴮ = front-plugL bsB m₂′
          m₂ = front-plugL bsA m₂ᴮ
          m₃′ = front-∥ˡ (Q 𝐓.∥ (Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB)) hd
          m₃ᴮ = front-plugL bsB m₃′
      in
      tracks-◅◅
        (tracks-∥-cong-r {d₁ = ≋-refl}
          (tk₂ Z₁ Z₂ t {idx m}
            (idx≡ m ■ cong (_+ Fin.toℕ t) (processCount-rename Z₁ ρ₁))))
        (tracks-◅◅
          (∥-commℕ-r {P = Q₀}
            {Q = plugL bsA
                   (plugL bsB
                     (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q))}
            (idx m) {a = pc Q₀ ↑ʳ idx m} {b = idx m ↑ˡ pc Q₀}
            (Fin.toℕ-↑ʳ (pc Q₀) (idx m)) (Fin.toℕ-↑ˡ (idx m) (pc Q₀)))
          (tracks-◅◅
            (tracks-foldPar₂ bsA bsB
              (((Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)) 𝐓.∥ Q) Q₀ (idx fX)
              {a = idx m ↑ˡ pc Q₀} {b = idx m₂}
              (Fin.toℕ-↑ˡ (idx m) (pc Q₀) ■ idx≡ m ■ sym (idx≡ fX))
              (idx≡ m₂ ■ sym (idx≡ fX)))
            (tracks-≋-plugL bsA
              (tracks-≋-plugL bsB
                (∥-assoc-symℕ
                  {P₁ = (Z₁ 𝐓.⋯ₚ ρ₁) 𝐓.∥ (Z₂ 𝐓.⋯ₚ ρ₂)} {P₂ = Q}
                  {P₃ = Q₀ 𝐓.⋯ₚ wkL₂ bsA bsB}
                  (idx m₃′) {a = idx m₂′} {b = idx m₃′}
                  (idx≡ m₂′ ■ sym (idx≡ m₃′)) refl)
                (idx≡ m₂ᴮ ■ sym (idx≡ m₂′)) (idx≡ m₃ᴮ ■ sym (idx≡ m₃′)))
              (idx≡ m₂ ■ sym (idx≡ m₂ᴮ))
              (eb
               ■ cong (_+ Fin.toℕ t) (sym (processCount-rename Z₁ ρ₁))
               ■ sym (idx≡ m₃ᴮ))))))
bubble₂ (bind₂ A₁ A₂ c) with bubble₂ c
... | bubbled₂ bsA bsB ρ₁ ρ₂ Q eq am₁ am₂ tk₁ tk₂ =
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
    (λ Z₁ Z₂ t {b} eb → tracks-gmap-ν (tk₁ Z₁ Z₂ t {b} eb))
    (λ Z₁ Z₂ t {b} eb → tracks-gmap-ν (tk₂ Z₁ Z₂ t {b} eb))

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
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) (src₁ src₂ : 𝔽 (pc P)) : Set where
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
    -- THREAD TRACKING (`PLAN.md` §12.2, P5.2b): the two source threads of
    -- `P` become the threads `0F` and `1F` of the canonical binder's body,
    -- i.e. the two synchronising redexes in the order the rule expects.
    tracks₁ : Tracks ≋-canon src₁
                (threadInContext above′
                  (𝐓.ν (suc b₁ L.∷ B₁) (suc b₂ L.∷ B₂)
                    ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
                  0F)
    tracks₂ : Tracks ≋-canon src₂
                (threadInContext above′
                  (𝐓.ν (suc b₁ L.∷ B₁) (suc b₂ L.∷ B₂)
                    ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
                  1F)

------------------------------------------------------------------------
-- 3.  The two-hole canonical form, before the side normalisation.
--
-- `Canon₂` is `Canonical.Canon` for two threads: both are the left
-- components of the `∥`-pair directly under their common binder, and each
-- handle sits at the binder's own local index.

record Canon₂ {k₁ k₂ : ℕ} (P : 𝐓.Proc 0) (e₁ : Tm k₁) (e₂ : Tm k₂)
              (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) (C₁ C₂ : BindGroup)
              (l₁ l₂ : 𝔽 (sum C₁ + sum C₂))
              (src₁ src₂ : 𝔽 (pc P)) : Set where
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
    -- THREAD TRACKING (`PLAN.md` §12.2, P5.2b), one clause per hole.
    tracks₁ : Tracks ≋-canon src₁
                (threadInContext above′
                  (𝐓.ν C₁ C₂
                    ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
                  0F)
    tracks₂ : Tracks ≋-canon src₂
                (threadInContext above′
                  (𝐓.ν C₁ C₂
                    ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
                  1F)

canon₂ :
  {c : ProcessContext₂ k₁ k₂ 0} (e₁ : Tm k₁) (e₂ : Tm k₂)
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} (bnd : Binder₂ c x₁ x₂) →
  Canon₂ (plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) e₁ e₂ x₁ x₂
    (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
    (Binder₂.local₁ bnd) (Binder₂.local₂ bnd)
    (thread₁ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
    (thread₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
canon₂ {c = c} e₁ e₂ (binder₂ C₁ C₂ above below dec l₁ l₂ ieq₁ ieq₂)
  with bubble₂ below
... | bubbled₂ bsA bsB ρ₁₀ ρ₂₀ Q eq am₁ am₂ tk₁ tk₂
  with push₂ bsA bsB C₁ C₂
         ((𝐓.⟪ e₁ ⋯ ρ₁₀ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂₀ ⟫) 𝐓.∥ Q)
...  | σ , ≋push , hnd , trkP =
  canonical₂ (compose above (compose (ctxL bsA) (ctxL bsB)))
    (λ y → σ (ρ₁₀ y)) (λ y → σ (ρ₂₀ y)) (Q 𝐓.⋯ₚ σ)
    (≡→≋ eqA
     ◅◅ ≋-plug above (𝐓.ν-cong (eq 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) ◅◅ ≋push)
     ◅◅ ≡→≋ eqC)
    (cong σ (cong ρ₁₀ (sym ieq₁) ■ am₁ (l₁ ↑ˡ _)) ■ hnd l₁)
    (cong σ (cong ρ₂₀ (sym ieq₂) ■ am₂ (l₂ ↑ˡ _)) ■ hnd l₂)
    (tracks-◅◅
      (tracks-≡→≋ℕ eqA (thread₁ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
        {b = threadInContext above
               (𝐓.ν C₁ C₂ (plug₂ below 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫))
               (thread₁ below 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)}
        (sym (cong (λ z → Fin.toℕ (thread₁ z 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)) dec
              ■ thread₁-compose₂ above (bind₂ C₁ C₂ below)
                  𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)))
      (tracks-◅◅
        (tracks-≋-plug above
          (tracks-◅◅
            (tracks-gmap-ν
              (tk₁ 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F {idx g₁} (idx≡ g₁)))
            (trkP 0F {a = idx g₁} {b = idx g₂} (idx≡ g₁) (idx≡ g₂))))
        (tracks-≡→≋ℕ eqC
          (threadInContext above
            (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) (idx g₂))
          {b = threadInContext
                 (compose above (compose (ctxL bsA) (ctxL bsB))) W 0F}
          (target-ℕ 0F (idx g₂) (sym (idx≡ g₂))))))
    (tracks-◅◅
      (tracks-≡→≋ℕ eqA (thread₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
        {b = threadInContext above
               (𝐓.ν C₁ C₂ (plug₂ below 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫))
               (thread₂ below 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)}
        (sym (cong (λ z → Fin.toℕ (thread₂ z 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)) dec
              ■ thread₂-compose₂ above (bind₂ C₁ C₂ below)
                  𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)))
      (tracks-◅◅
        (tracks-≋-plug above
          (tracks-◅◅
            (tracks-gmap-ν
              (tk₂ 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F {idx h₁} (idx≡ h₁)))
            (trkP 1F {a = idx h₁} {b = idx h₂} (idx≡ h₁) (idx≡ h₂))))
        (tracks-≡→≋ℕ eqC
          (threadInContext above
            (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) (idx h₂))
          {b = threadInContext
                 (compose above (compose (ctxL bsA) (ctxL bsB))) W 1F}
          (target-ℕ 1F (idx h₂) (sym (idx≡ h₂))))))
  where
    -- The body that `push₂` was applied to, and the fully renamed result.
    T₀ = (𝐓.⟪ e₁ ⋯ ρ₁₀ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂₀ ⟫) 𝐓.∥ Q

    W = 𝐓.ν C₁ C₂
          ((𝐓.⟪ e₁ ⋯ (λ y → σ (ρ₁₀ y)) ⟫
            𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → σ (ρ₂₀ y)) ⟫)
           𝐓.∥ (Q 𝐓.⋯ₚ σ))

    eqA : plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ ≡
          plug above (𝐓.ν C₁ C₂ (plug₂ below 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫))
    eqA =
      cong (λ z → plug₂ z 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) dec
      ■ plug-compose₂ above (bind₂ C₁ C₂ below) 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫

    eqC : plug above (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) ≡
          plug (compose above (compose (ctxL bsA) (ctxL bsB))) W
    eqC =
      cong₂
        (λ w₁ w₂ →
          plug above
            (plugL bsA
              (plugL bsB
                (𝐓.ν C₁ C₂
                  ((𝐓.⟪ w₁ ⟫ 𝐓.∥ 𝐓.⟪ w₂ ⟫) 𝐓.∥ (Q 𝐓.⋯ₚ σ))))))
        (fusion e₁ ρ₁₀ σ ■ ⋯-cong e₁ (λ _ → refl))
        (fusion e₂ ρ₂₀ σ ■ ⋯-cong e₂ (λ _ → refl))
      ■ sym
          (plug-compose above (compose (ctxL bsA) (ctxL bsB)) W
           ■ cong (plug above)
               (plug-compose (ctxL bsA) (ctxL bsB) W
                ■ cong (plug (ctxL bsA)) (plug-ctxL bsB W)
                ■ plug-ctxL bsA (plugL bsB W)))

    -- The two bind stacks are thread transparent, so a thread of `W` keeps
    -- its numeric position when read in the composed context `above′`.
    target-ℕ :
      (i : 𝔽 (pc W))
      (j : 𝔽 (pc (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))))) →
      Fin.toℕ i ≡ Fin.toℕ j →
      Fin.toℕ
        (threadInContext (compose above (compose (ctxL bsA) (ctxL bsB)))
          W i)
      ≡
      Fin.toℕ
        (threadInContext above
          (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) j)
    target-ℕ i j e =
      threadInContext-compose above (compose (ctxL bsA) (ctxL bsB)) W i
      ■ threadInContext-ℕ above
          (plug (compose (ctxL bsA) (ctxL bsB)) W)
          (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ))))
          (threadInContext (compose (ctxL bsA) (ctxL bsB)) W i) j
          (threadInContext-compose (ctxL bsA) (ctxL bsB) W i
           ■ threadInContext-ctxL bsA (plug (ctxL bsB) W)
               (threadInContext (ctxL bsB) W i)
           ■ threadInContext-ctxL bsB W i
           ■ e)

    g₁ : Front (plugL bsA (plugL bsB T₀)) 0
    g₁ =
      front-plugL bsA
        (front-plugL bsB
          (front-∥ˡ Q
            (front-∥ˡ 𝐓.⟪ e₂ ⋯ ρ₂₀ ⟫
              (front {P = 𝐓.⟪ e₁ ⋯ ρ₁₀ ⟫} 0F refl))))

    g₂ : Front (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) 0
    g₂ =
      front-plugL bsA
        (front-plugL bsB (front-ν (front-⋯ T₀ σ (front 0F refl))))

    h₁ : Front (plugL bsA (plugL bsB T₀)) 1
    h₁ =
      front-plugL bsA
        (front-plugL bsB
          (front-∥ˡ Q
            (front-∥ʳ 𝐓.⟪ e₁ ⋯ ρ₁₀ ⟫
              (front {P = 𝐓.⟪ e₂ ⋯ ρ₂₀ ⟫} 0F refl))))

    h₂ : Front (plugL bsA (plugL bsB (𝐓.ν C₁ C₂ (T₀ 𝐓.⋯ₚ σ)))) 1
    h₂ =
      front-plugL bsA
        (front-plugL bsB (front-ν (front-⋯ T₀ σ (front 1F refl))))

private
  swapr-cross₂ : ∀ p q {n} (v : 𝔽 (p + q)) →
    swapᵣ p q {n} (v ↑ˡ n) ≡ Fin.swap p v ↑ˡ n
  swapr-cross₂ p q {n} v rewrite Fin.splitAt-↑ˡ (p + q) v n = refl

  swap-↑ʳ₂ : ∀ p {q} (v : 𝔽 q) → Fin.swap p (p ↑ʳ v) ≡ v ↑ˡ p
  swap-↑ʳ₂ p {q} v rewrite Fin.splitAt-↑ʳ p q v = refl

  swap-↑ˡ₂ : ∀ {p} q (v : 𝔽 p) → Fin.swap p (v ↑ˡ q) ≡ q ↑ʳ v
  swap-↑ˡ₂ {p} q v rewrite Fin.splitAt-↑ˡ p v q = refl

-- The side exchange, for both handles at once.  `ν-swap′` is a renaming, so
-- both tracked positions survive it unchanged.
canon-swap₂ :
  {P : 𝐓.Proc 0} {e₁ : Tm k₁} {e₂ : Tm k₂} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  {C₁ C₂ : BindGroup} {l₁ l₂ : 𝔽 (sum C₁ + sum C₂)}
  {src₁ src₂ : 𝔽 (pc P)} →
  Canon₂ P e₁ e₂ x₁ x₂ C₁ C₂ l₁ l₂ src₁ src₂ →
  Canon₂ P e₁ e₂ x₁ x₂ C₂ C₁
    (Fin.swap (sum C₁) l₁) (Fin.swap (sum C₁) l₂) src₁ src₂
canon-swap₂ {e₁ = e₁} {e₂ = e₂} {C₁ = C₁} {C₂ = C₂} {l₁ = l₁} {l₂ = l₂}
  (canonical₂ above′ ρ₁ ρ₂ resid ≋c xeq₁ xeq₂ trk₁ trk₂) =
  canonical₂ above′
    (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₁ y))
    (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₂ y))
    (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂))
    (≋c
     ◅◅ ≋-plug above′ (fwd 𝐓.ν-swap′ ◅ ≋-refl)
     ◅◅ ≡→≋ eqS)
    (cong (swapᵣ (sum C₁) (sum C₂)) xeq₁
     ■ swapr-cross₂ (sum C₁) (sum C₂) l₁)
    (cong (swapᵣ (sum C₁) (sum C₂)) xeq₂
     ■ swapr-cross₂ (sum C₁) (sum C₂) l₂)
    (tracks-◅◅ trk₁
      (tracks-◅◅
        (tracks-≋-plug above′
          (ν-swap′ℕ {B₁ = C₁} {B₂ = C₂} {P = body} 0F
            {b = sqZ} (idx≡ sqZf)))
        (tracks-≡→≋ℕ eqS
          (threadInContext above′
            (𝐓.ν C₂ C₁ (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂))) sqZ)
          {b = threadInContext above′ Wˢ 0F}
          (threadInContext-ℕ above′ Wˢ
            (𝐓.ν C₂ C₁ (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))
            0F sqZ (sym (idx≡ sqZf))))))
    (tracks-◅◅ trk₂
      (tracks-◅◅
        (tracks-≋-plug above′
          (ν-swap′ℕ {B₁ = C₁} {B₂ = C₂} {P = body} 1F
            {b = sqO} (idx≡ sqOf)))
        (tracks-≡→≋ℕ eqS
          (threadInContext above′
            (𝐓.ν C₂ C₁ (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂))) sqO)
          {b = threadInContext above′ Wˢ 1F}
          (threadInContext-ℕ above′ Wˢ
            (𝐓.ν C₂ C₁ (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))
            1F sqO (sym (idx≡ sqOf))))))
  where
    body = (𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid

    Wˢ = 𝐓.ν C₂ C₁
           ((𝐓.⟪ e₁ ⋯ (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₁ y)) ⟫
             𝐓.∥ 𝐓.⟪ e₂ ⋯ (λ y → swapᵣ (sum C₁) (sum C₂) (ρ₂ y)) ⟫)
            𝐓.∥ (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))

    eqS : plug above′
            (𝐓.ν C₂ C₁ (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))
          ≡ plug above′ Wˢ
    eqS =
      cong₂
        (λ w₁ w₂ →
          plug above′
            (𝐓.ν C₂ C₁
              ((𝐓.⟪ w₁ ⟫ 𝐓.∥ 𝐓.⟪ w₂ ⟫)
               𝐓.∥ (resid 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)))))
        (fusion e₁ ρ₁ (swapᵣ (sum C₁) (sum C₂))
         ■ ⋯-cong e₁ (λ _ → refl))
        (fusion e₂ ρ₂ (swapᵣ (sum C₁) (sum C₂))
         ■ ⋯-cong e₂ (λ _ → refl))

    sqZf : Front (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)) 0
    sqZf = front-⋯ body (swapᵣ (sum C₁) (sum C₂)) (front 0F refl)

    sqZ = idx sqZf

    sqOf : Front (body 𝐓.⋯ₚ swapᵣ (sum C₁) (sum C₂)) 1
    sqOf = front-⋯ body (swapᵣ (sum C₁) (sum C₂)) (front 1F refl)

    sqO = idx sqOf

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
canonPair-lr :
  {P : 𝐓.Proc 0} {e₁ : Tm k₁} {e₂ : Tm k₂}
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} {src₁ src₂ : 𝔽 (pc P)}
  {a c : ℕ} {A C : BindGroup} →
  Canon₂ P e₁ e₂ x₁ x₂
    (suc a L.∷ A) (suc c L.∷ C)
    0F (sum (suc a L.∷ A) ↑ʳ 0F) src₁ src₂ →
  CanonPair P e₁ e₂ x₁ x₂ src₁ src₂
canonPair-lr (canonical₂ above′ ρ₁ ρ₂ Q ≋c xeq₁ xeq₂ trk₁ trk₂) =
  canonPair _ _ _ _ above′ ρ₁ ρ₂ Q ≋c xeq₁ xeq₂ trk₁ trk₂

canonPair-rl :
  {P : 𝐓.Proc 0} {e₁ : Tm k₁} {e₂ : Tm k₂}
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} {src₁ src₂ : 𝔽 (pc P)}
  {a c : ℕ} {A C : BindGroup} →
  Canon₂ P e₁ e₂ x₁ x₂
    (suc c L.∷ C) (suc a L.∷ A)
    (Fin.swap (sum (suc a L.∷ A)) (sum (suc a L.∷ A) ↑ʳ 0F))
    (Fin.swap (sum (suc a L.∷ A))
      (Fin.zero {a + sum A + sum (suc c L.∷ C)})) src₁ src₂ →
  CanonPair P e₁ e₂ x₁ x₂ src₁ src₂
canonPair-rl {a = a} {c = c} {A = A} {C = C}
  (canonical₂ {midᵈ = m₀} above′ ρ₁ ρ₂ Q ≋c xeq₁ xeq₂ trk₁ trk₂) =
  canonPair c a C A above′ ρ₁ ρ₂ Q ≋c
    (xeq₁
     ■ cong (λ z → z ↑ˡ m₀)
         (swap-↑ʳ₂ (sum (suc a L.∷ A)) {sum (suc c L.∷ C)} 0F))
    (xeq₂
     ■ cong (λ z → z ↑ˡ m₀)
         (swap-↑ˡ₂ {suc a + sum A} (sum (suc c L.∷ C))
           (Fin.zero {a + sum A})))
    trk₁ trk₂

canon-pair :
  {c : ProcessContext₂ k₁ k₂ 0} (e₁ : Tm k₁) (e₂ : Tm k₂)
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} (bnd : Binder₂ c x₁ x₂) →
  HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
             (Binder₂.local₁ bnd) (Binder₂.local₂ bnd) →
  CanonPair (plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) e₁ e₂ x₁ x₂
    (thread₁ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
    (thread₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫ 0F)
canon-pair e₁ e₂ bnd (heads-lr _ _ _ _) =
  canonPair-lr (canon₂ e₁ e₂ bnd)
canon-pair e₁ e₂ bnd (heads-rl _ _ _ _) =
  canonPair-rl (canon-swap₂ (canon₂ e₁ e₂ bnd))
