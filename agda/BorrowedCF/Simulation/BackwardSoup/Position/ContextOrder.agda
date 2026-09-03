-- | Phase 4a, PROCESS LEVEL (`BackwardSoup/PLAN.md` §9, P3 / §8(c)).
--
--   THE CONTEXT WALK.  `Position/ThreadOrder.agda` says that inside ONE
--   thread nothing is `;`-before the consumed handle.  This module walks the
--   `ProcessContext` that Phase 1 (`Locate.agda`) produced and lifts that to
--   the WHOLE derivation:
--
--     ctx-¬before-direct : ImpureHandleConst c →
--       Γ ; γ ⊢ₚ plug below ⟪ E [ K c ·¹ (` x) ]* ⟫ →
--       (y y′ : 𝔽 _) → weakenThrough below y ≡ x → y′ ≢ y →
--       ¬ Mobile (Γ ﹫ y) → ¬ Mobile (Γ ﹫ y′) →
--       count y γ ≤ 1 → ¬ before y′ y γ
--
--   The three process rules on the path are handled by
--
--     * `TP-Weaken` (inside `inv-∥` / `inv-ν`): `before-mono-≼` -- `≼` never
--       CREATES a `;`, because the only `≈` rule that turns a `∥` into a `;`
--       is `∥′-tm-;`, which needs a MOBILE handle;
--     * `TP-Par`: `before y′ y (α ∥ β)` puts both variables in the SAME
--       component; the redex thread already holds `y` (`ctx-count`), so
--       linearity (`count y γ ≤ 1`) forbids the other component from holding
--       it as well;
--     * `TP-Res`: the body structure is
--       `structBinder B₁ ⋯ ∥ structBinder B₂ ⋯ ∥ (γ ⋯ᵣ weaken*)`, and the
--       ambient variables live only in the renamed `γ` part -- `before-⋯ᵣ`
--       (`Position.agda`) transports the order there and
--       `StructDom.count-⋯ᵣwkʳ-↑ʳ` / `count-weaken*-shift` transport the
--       counts.
--
--   `ctx-count` is the companion "the redex thread really holds the handle".
module BorrowedCF.Simulation.BackwardSoup.Position.ContextOrder where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.StructDom
  using (count-⋯ᵣwkʳ-↑ʳ; count-weaken*-shift)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position
open import BorrowedCF.Simulation.BackwardSoup.Position.ThreadOrder

open 𝐓 using (_;_⊢ₚ_; inv-ν; inv-∥; inv-⟪⟫; structBinder; BindGroup)

open Nat using (_≤_; z≤n; s≤s)
open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 0.  Scaffolding for the `TP-Res` step.

private
  pos : ∀ {a} → a ≢ 0 → 1 ≤ a
  pos {zero}  ne = ⊥-elim (ne refl)
  pos {suc a} _  = s≤s z≤n

  two≰1 : ¬ (2 ≤ 1)
  two≰1 (s≤s ())

  ↑ʳ-inj : (p : ℕ) {q : ℕ} {i j : 𝔽 q} → p ↑ʳ i ≡ p ↑ʳ j → i ≡ j
  ↑ʳ-inj p {i = i} {j} = Fin.↑ʳ-injective p i j

  wk*≡↑ʳ : ∀ {n} k (y : 𝔽 n) → 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ k y ≡ k ↑ʳ y
  wk*≡↑ʳ k y = 𝐂.weaken*~wkˡ ⦃ 𝐂.Kᵣ ⦄ k y

  wkstar-inj : ∀ {n} k {i j : 𝔽 n} →
    𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ k i ≡ 𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ k j → i ≡ j
  wkstar-inj k {i} {j} eq = ↑ʳ-inj k (sym (wk*≡↑ʳ k i) ■ eq ■ wk*≡↑ʳ k j)

  -- The body structure prescribed by `TP-Res` counts an AMBIENT variable
  -- exactly as the ambient structure does: the two `structBinder` blocks live
  -- entirely below `sum B₁ + sum B₂`.
  bind-count : ∀ (B₁ B₂ : BindGroup) {n} (γ : Struct n) (y : 𝔽 n) →
    count ((sum B₁ + sum B₂) ↑ʳ y)
      ( (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) )
    ≡ count y γ
  bind-count B₁ B₂ {n} γ y =
    cong₂ _+_
      (cong₂ _+_
        (count-⋯ᵣwkʳ-↑ʳ n (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) y)
        (count-⋯ᵣwkʳ-↑ʳ n (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) y))
      (count-weaken*-shift (sum B₁ + sum B₂) γ y)

  -- ... and the `;`-order transports into it.
  bind-before : ∀ (B₁ B₂ : BindGroup) {n} (γ : Struct n) (y y′ : 𝔽 n) →
    before y′ y γ →
    before ((sum B₁ + sum B₂) ↑ʳ y′) ((sum B₁ + sum B₂) ↑ʳ y)
      ( (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) )
  bind-before B₁ B₂ {n} γ y y′ b =
    inj₂ (subst₂ (λ i j → before i j (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
                 (wk*≡↑ʳ (sum B₁ + sum B₂) y′)
                 (wk*≡↑ʳ (sum B₁ + sum B₂) y)
                 (before-⋯ᵣ γ (𝐂.weaken* (sum B₁ + sum B₂))
                            (wkstar-inj (sum B₁ + sum B₂)) b))

  bind-lookup : ∀ (B₁ B₂ : BindGroup) {n}
    (Γ₁ : Ctx (sum B₁)) (Γ₂ : Ctx (sum B₂)) (Γ : Ctx n) (y : 𝔽 n) →
    ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ ((sum B₁ + sum B₂) ↑ʳ y) ≡ Γ ﹫ y
  bind-lookup B₁ B₂ Γ₁ Γ₂ Γ y = V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ y

------------------------------------------------------------------------
-- 1.  The walk, abstracted over the redex thread.

module Walk
  {k : ℕ} (Q : 𝐓.Proc k) (x : 𝔽 k)
  (Q-count : ∀ {Γ : Ctx k} {γ : Struct k} →
             Γ ; γ ⊢ₚ Q → ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ)
  where

  ctx-count :
    ∀ {n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n} →
    Γ ; γ ⊢ₚ plug below Q →
    (y : 𝔽 n) → weakenThrough below y ≡ x → ¬ Unr (Γ ﹫ y) → 1 ≤ count y γ
  ctx-count hole ⊢P y refl ¬uy = Q-count ⊢P ¬uy
  ctx-count (par-left ctx P₂) ⊢P y eq ¬uy with inv-∥ ⊢P
  ... | α , β , ≤γ , ⊢left , _ =
    subst (1 ≤_) (count-≼-eq ¬uy ≤γ)
      (Nat.≤-trans (ctx-count ctx ⊢left y eq ¬uy)
                   (Nat.m≤m+n (count y α) (count y β)))
  ctx-count (par-right P₁ ctx) ⊢P y eq ¬uy with inv-∥ ⊢P
  ... | α , β , ≤γ , _ , ⊢right =
    subst (1 ≤_) (count-≼-eq ¬uy ≤γ)
      (Nat.≤-trans (ctx-count ctx ⊢right y eq ¬uy)
                   (Nat.m≤n+m (count y β) (count y α)))
  ctx-count (bind B₁ B₂ ctx) {Γ} {γ} ⊢P y eq ¬uy with inv-ν ⊢P
  ... | Γ₁ , Γ₂ , _ , _ , _ , _ , _ , _ , _ , ⊢body =
    subst (1 ≤_) (bind-count B₁ B₂ γ y)
      (ctx-count ctx ⊢body ((sum B₁ + sum B₂) ↑ʳ y) eq
        (subst (λ T → ¬ Unr T) (sym (bind-lookup B₁ B₂ Γ₁ Γ₂ Γ y)) ¬uy))

  module _
    (Q-¬before : ∀ {Γ : Ctx k} {γ : Struct k} {y′ : 𝔽 k} →
                 Γ ; γ ⊢ₚ Q → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) → y′ ≢ x →
                 count x γ ≤ 1 → ¬ before y′ x γ)
    where

    ctx-¬before :
      ∀ {n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n} →
      Γ ; γ ⊢ₚ plug below Q →
      (y y′ : 𝔽 n) → weakenThrough below y ≡ x → y′ ≢ y →
      ¬ Mobile (Γ ﹫ y) → ¬ Mobile (Γ ﹫ y′) →
      count y γ ≤ 1 → ¬ before y′ y γ
    ctx-¬before hole ⊢P y y′ refl y′≢y ¬my ¬my′ ≤1 =
      Q-¬before ⊢P ¬my ¬my′ y′≢y ≤1
    ctx-¬before (par-left ctx P₂) ⊢P y y′ eq y′≢y ¬my ¬my′ ≤1 b
      with inv-∥ ⊢P
    ... | α , β , ≤γ , ⊢left , _
      with before-mono-≼ ¬my′ ¬my ≤γ b
       | subst (_≤ 1) (sym (count-≼-eq (¬my ∘ unr⇒mobile) ≤γ)) ≤1
    ...   | inj₁ bα | ≤αβ =
      ctx-¬before ctx ⊢left y y′ eq y′≢y ¬my ¬my′
        (Nat.≤-trans (Nat.m≤m+n (count y α) (count y β)) ≤αβ) bα
    ...   | inj₂ bβ | ≤αβ =
      two≰1 (Nat.≤-trans
              (Nat.+-mono-≤ (ctx-count ctx ⊢left y eq (¬my ∘ unr⇒mobile))
                            (pos (proj₂ (before⇒mem β bβ))))
              ≤αβ)
    ctx-¬before (par-right P₁ ctx) ⊢P y y′ eq y′≢y ¬my ¬my′ ≤1 b
      with inv-∥ ⊢P
    ... | α , β , ≤γ , _ , ⊢right
      with before-mono-≼ ¬my′ ¬my ≤γ b
       | subst (_≤ 1) (sym (count-≼-eq (¬my ∘ unr⇒mobile) ≤γ)) ≤1
    ...   | inj₂ bβ | ≤αβ =
      ctx-¬before ctx ⊢right y y′ eq y′≢y ¬my ¬my′
        (Nat.≤-trans (Nat.m≤n+m (count y β) (count y α)) ≤αβ) bβ
    ...   | inj₁ bα | ≤αβ =
      two≰1 (Nat.≤-trans
              (Nat.+-mono-≤ (pos (proj₂ (before⇒mem α bα)))
                            (ctx-count ctx ⊢right y eq (¬my ∘ unr⇒mobile)))
              ≤αβ)
    ctx-¬before (bind B₁ B₂ ctx) {Γ} {γ} ⊢P y y′ eq y′≢y ¬my ¬my′ ≤1 b
      with inv-ν ⊢P
    ... | Γ₁ , Γ₂ , _ , _ , _ , _ , _ , _ , _ , ⊢body =
      ctx-¬before ctx ⊢body
        ((sum B₁ + sum B₂) ↑ʳ y) ((sum B₁ + sum B₂) ↑ʳ y′) eq
        (λ e → y′≢y (↑ʳ-inj (sum B₁ + sum B₂) e))
        (subst (λ T → ¬ Mobile T) (sym (bind-lookup B₁ B₂ Γ₁ Γ₂ Γ y)) ¬my)
        (subst (λ T → ¬ Mobile T) (sym (bind-lookup B₁ B₂ Γ₁ Γ₂ Γ y′)) ¬my′)
        (subst (_≤ 1) (sym (bind-count B₁ B₂ γ y)) ≤1)
        (bind-before B₁ B₂ γ y y′ b)

------------------------------------------------------------------------
-- 2.  The two instances.

ctx-count-direct :
  ∀ {k n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n}
    {E : Frame* k} {c : Const} {x : 𝔽 k} →
  Γ ; γ ⊢ₚ plug below 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
  (y : 𝔽 n) → weakenThrough below y ≡ x → ¬ Unr (Γ ﹫ y) → 1 ≤ count y γ
ctx-count-direct below {E = E} {c = c} {x = x} =
  Walk.ctx-count 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x
    (λ ⊢Q ¬u → thread-count {E = E} {c = c} {x = x} (inv-⟪⟫ ⊢Q) ¬u)
    below

ctx-¬before-direct :
  ∀ {k n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n}
    {E : Frame* k} {c : Const} {x : 𝔽 k} →
  ImpureHandleConst c →
  Γ ; γ ⊢ₚ plug below 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
  (y y′ : 𝔽 n) → weakenThrough below y ≡ x → y′ ≢ y →
  ¬ Mobile (Γ ﹫ y) → ¬ Mobile (Γ ﹫ y′) →
  count y γ ≤ 1 → ¬ before y′ y γ
ctx-¬before-direct below {E = E} {c = c} {x = x} ic =
  Walk.ctx-¬before 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x
    (λ ⊢Q ¬u → thread-count {E = E} {c = c} {x = x} (inv-⟪⟫ ⊢Q) ¬u)
    (λ ⊢Q m1 m2 ne bnd → thread-¬before {E = E} {c = c} {x = x} ic (inv-⟪⟫ ⊢Q) m1 m2 ne bnd)
    below

ctx-count-pair :
  ∀ {k n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n}
    {E : Frame* k} {c : Const} {w : Tm k} {x : 𝔽 k} →
  Γ ; γ ⊢ₚ plug below 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ →
  (y : 𝔽 n) → weakenThrough below y ≡ x → ¬ Unr (Γ ﹫ y) → 1 ≤ count y γ
ctx-count-pair below {E = E} {c = c} {w = w} {x = x} =
  Walk.ctx-count 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x
    (λ ⊢Q ¬u → thread-pair-count {E = E} {c = c} {w = w} {x = x} (inv-⟪⟫ ⊢Q) ¬u)
    below

ctx-¬before-pair :
  ∀ {k n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n}
    {E : Frame* k} {c : Const} {w : Tm k} {x : 𝔽 k} →
  ImpureHandleConst c →
  Γ ; γ ⊢ₚ plug below 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ →
  (y y′ : 𝔽 n) → weakenThrough below y ≡ x → y′ ≢ y →
  ¬ Mobile (Γ ﹫ y) → ¬ Mobile (Γ ﹫ y′) →
  count y γ ≤ 1 → ¬ before y′ y γ
ctx-¬before-pair below {E = E} {c = c} {w = w} {x = x} ic =
  Walk.ctx-¬before 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x
    (λ ⊢Q ¬u → thread-pair-count {E = E} {c = c} {w = w} {x = x} (inv-⟪⟫ ⊢Q) ¬u)
    (λ ⊢Q m1 m2 ne bnd → thread-pair-¬before {E = E} {c = c} {w = w} {x = x} ic (inv-⟪⟫ ⊢Q) m1 m2 ne bnd)
    below
