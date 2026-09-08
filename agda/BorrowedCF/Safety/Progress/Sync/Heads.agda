-- | The two head handles of a synchronising restriction carry DUAL heads.
--
--   `TP-Res` types `ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q` with a `New` session `s`,
--   a polarity `p` and two binder chains
--
--     BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ₁      -- endpoint 1
--     BindCtx (dual s ; end (dualPol p)) (suc b₂ ∷ B₂) Γ₂ .
--
--   `bindCtx-head` reads the FRONT KIND of the whole endpoint off the first
--   handle of the chain: `Γᵢ ﹫ 0F` is a prefix of the endpoint (with the
--   borrow's `ret` in the way when the group is followed by another one, which
--   is why the statement is phrased with `ConsK` and not with an explicit
--   suffix).  `Front.front-dual` then says the two kinds are dual, and
--   `head-kinds` packages the two steps.
--
--   `bc-shape` is the other half: a thread blocked on `x` fixes the head kind
--   of `x`'s session, via agent F's `arg-send` / `arg-recv` / `arg-select` /
--   `arg-branch` / `arg-end`.  Its `BCShape` is `_∈BCe_` with the head kind as
--   an INDEX and the application direction already normalised to `𝟙`
--   (`const-app-dir`), so that the main lemma can case-split on one thread and
--   have the other one determined.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Heads where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Safety.Blocked
open import BorrowedCF.Safety.Progress.Expr
open import BorrowedCF.Safety.Progress.Sync.Front

open Nat.Variables
open Variables
open Fin.Patterns

private variable
  hk hk₁ hk₂ : HKind
  t t₁ t₂ : 𝕊 0
  b : ℕ

------------------------------------------------------------------------
-- 1.  The front kind of an endpoint, read off its first handle.

bindCtx′-head : {Γ : Ctx (suc b)} →
  BindCtx′ s Γ → Γ ﹫ 0F ≡ ⟨ t ⟩ → ConsK hk t → ConsK hk s
bindCtx′-head (cons s₁ s₂ ¬skips s-split C) refl c = ≃-consK s-split (hd c)

bindCtx-head : {Γ : Ctx (sum (suc b ∷ B))} →
  BindCtx s (suc b ∷ B) Γ → Γ ﹫ 0F ≡ ⟨ t ⟩ → ConsK hk t → ConsK hk s
bindCtx-head (last x) eq c = bindCtx′-head x eq c
bindCtx-head {b = b} {t = t} {hk = hk}
             (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ ¬skips₂ x C ah) eq c
  with bindCtx′-head x (sym (V.lookup-++ˡ Γ₁ Γ₂ 0F) ■ eq) c
... | c₁ with consK-;⁻ c₁
...   | inj₁ c₂ = ≃-consK s≃ (hd c₂)
...   | inj₂ (_ , ())

------------------------------------------------------------------------
-- 2.  The two endpoints are dual.

head-kinds : {s : 𝕊 0} {p : Pol} {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  {Γ₁ : Ctx (sum (suc b₁ ∷ B₁))} {Γ₂ : Ctx (sum (suc b₂ ∷ B₂))} →
  BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ₁ →
  BindCtx (dual s ; end (dualPol p)) (suc b₂ ∷ B₂) Γ₂ →
  Γ₁ ﹫ 0F ≡ ⟨ t₁ ⟩ → Γ₂ ﹫ 0F ≡ ⟨ t₂ ⟩ →
  ConsK hk₁ t₁ → ConsK hk₂ t₂ →
  hk₂ ≡ dualKind hk₁
head-kinds C₁ C₂ eq₁ eq₂ c₁ c₂ =
  front-dual (bindCtx-head C₁ eq₁ c₁) (bindCtx-head C₂ eq₂ c₂)

------------------------------------------------------------------------
-- 3.  A blocked thread, with its head kind as an index.

data BCShape {n} (x : 𝔽 n) : HKind → Tm n → Set where
  send   : (E : Frame* n) {v : Tm n} → Value v →
           BCShape x (kmsg ‼) (E [ K `send ·¹ (v ⊗ (` x)) ]*)
  recv   : (E : Frame* n) → BCShape x (kmsg ⁇) (E [ K `recv ·¹ (` x) ]*)
  select : (E : Frame* n) (i : Side) →
           BCShape x (kbrn ‼) (E [ K (`select i) ·¹ (` x) ]*)
  branch : (E : Frame* n) → BCShape x (kbrn ⁇) (E [ K `branch ·¹ (` x) ]*)
  end    : (E : Frame* n) (p : Pol) → BCShape x (kend p) (E [ K (`end p) ·¹ (` x) ]*)

shape⇒∈BCe : {x : 𝔽 n} {e : Tm n} → BCShape x hk e → x ∈BCe e
shape⇒∈BCe (send E V)   = send E V
shape⇒∈BCe (recv E)     = recv E
shape⇒∈BCe (select E i) = select E i
shape⇒∈BCe (branch E)   = branch E
shape⇒∈BCe (end E p)    = end E p

module _ {n} {Γ : Ctx n} (Γ-S : ChanCx Γ) where

  bc-shape : {γ : Struct n} {x : 𝔽 n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
    Γ ; γ ⊢ e ∶ T ∣ ϵ → x ∈BCe e →
    Σ[ hk ∈ HKind ] Σ[ s ∈ 𝕊 0 ]
      BCShape x hk e × (Γ ﹫ x ≡ ⟨ s ⟩) × ConsK hk s
  bc-shape ⊢e (send E {d = d} V)
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with _ , _ , _ , _ , _ , refl , Γx , s≃ ← arg-send Γ-S (V-⊗ V V-`) ⊢r
    = _ , _ , send E V , Γx , ≃-consK (≃-sym s≃) hmsg
  bc-shape ⊢e (recv E {d = d})
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with _ , _ , _ , refl , Γx , s≃ ← arg-recv Γ-S V-` ⊢r
    = _ , _ , recv E , Γx , ≃-consK (≃-sym s≃) hmsg
  bc-shape ⊢e (select E {d = d} i)
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with _ , _ , _ , refl , Γx , s≃ ← arg-select Γ-S V-` ⊢r
    = _ , _ , select E i , Γx , ≃-consK (≃-sym s≃) hbrn
  bc-shape ⊢e (branch E {d = d})
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with _ , _ , _ , refl , Γx , s≃ ← arg-branch Γ-S V-` ⊢r
    = _ , _ , branch E , Γx , ≃-consK (≃-sym s≃) hbrn
  bc-shape ⊢e (end E {d = d} p)
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with _ , _ , refl , Γx , s≃ ← arg-end Γ-S V-` ⊢r
    = _ , _ , end E p , Γx , ≃-consK (≃-sym s≃) hend
