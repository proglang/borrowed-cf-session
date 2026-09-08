-- | A thread is blocked on AT MOST ONE channel.
--
--   `Safety/Blocked.agda` reads a blocked thread as `x ∈BCe e`, i.e.
--   `e ≡ E [ K c ·⟨ d ⟩ w ]*` with the handle `x` in the argument.  The
--   synchronisation lemma needs the two blocked threads under a `ν` to be
--   DIFFERENT threads, which is exactly the statement that the evaluation
--   position of a term is unique: if `x ∈BCe e` and `y ∈BCe e` then `x ≡ y`.
--   `Frame*` plugging is a stuck application, so the argument runs on agent
--   F's structural presentation `Plug` (`Progress/Expr/Plug.agda`).
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Unique where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base

open import BorrowedCF.Safety.Blocked
open import BorrowedCF.Safety.Progress.Expr.Plug

open Nat.Variables
open Variables

private variable
  x y : 𝔽 n

------------------------------------------------------------------------
-- 1.  A BC redex is a constant applied to a value.

bcRedex-fn : {r : Tm n} → BCRedex x r →
  Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ w ∈ Tm n ] (r ≡ K c ·⟨ d ⟩ w) × Value w
bcRedex-fn (bc-send V)   = _ , _ , _ , refl , V-⊗ V V-`
bcRedex-fn bc-recv       = _ , _ , _ , refl , V-`
bcRedex-fn (bc-select i) = _ , _ , _ , refl , V-`
bcRedex-fn bc-branch     = _ , _ , _ , refl , V-`
bcRedex-fn (bc-end p)    = _ , _ , _ , refl , V-`

bcRedex-unique : {r : Tm n} → BCRedex x r → BCRedex y r → x ≡ y
bcRedex-unique (bc-send _)   (bc-send _)   = refl
bcRedex-unique bc-recv       bc-recv       = refl
bcRedex-unique (bc-select i) (bc-select _) = refl
bcRedex-unique bc-branch     bc-branch     = refl
bcRedex-unique (bc-end p)    (bc-end _)    = refl

------------------------------------------------------------------------
-- 2.  No BC redex sits inside a value, a constant or a variable.

plug-value⊥ : {e : Tm n} → Value e → Plug (BCRedex x) e → ⊥
plug-value⊥ V-`           (here ())
plug-value⊥ V-K           (here ())
plug-value⊥ V-λ           (here ())
plug-value⊥ (V-⊗ V₁ V₂)   (here ())
plug-value⊥ (V-⊗ V₁ V₂)   (pairˡ p)    = plug-value⊥ V₁ p
plug-value⊥ (V-⊗ V₁ V₂)   (pairʳ _ p)  = plug-value⊥ V₂ p
plug-value⊥ (V-⊕ V)       (here ())
plug-value⊥ (V-⊕ V)       (injˡ p)     = plug-value⊥ V p

plug-K⊥ : {c : Const} → Plug (BCRedex x) (K {n} c) → ⊥
plug-K⊥ p = plug-value⊥ V-K p

------------------------------------------------------------------------
-- 3.  The two sides of an application cannot both hold a redex.

app-conflict : ∀ {d : Dir} {e₁ e₂ : Tm n} → (d ≡ L → Value e₂) → (d ≡ 𝟙 ⊎ d ≡ R → Value e₁) →
  Plug (BCRedex x) e₁ → Plug (BCRedex y) e₂ → ⊥
app-conflict {d = L} V? V?′ p q = plug-value⊥ (V? refl) q
app-conflict {d = R} V? V?′ p q = plug-value⊥ (V?′ (inj₂ refl)) p
app-conflict {d = 𝟙} V? V?′ p q = plug-value⊥ (V?′ (inj₁ refl)) p

------------------------------------------------------------------------
-- 4.  Determinism of the evaluation position.

plug-det : (e : Tm n) → Plug (BCRedex x) e → Plug (BCRedex y) e → x ≡ y
plug-det (` z) (here ()) q
plug-det (K c) (here ()) q
plug-det (ƛ e) (here ()) q
plug-det (μ e) (here ()) q
plug-det (e₁ ·⟨ d ⟩ e₂) (here bc) (here bc′) = bcRedex-unique bc bc′
plug-det (e₁ ·⟨ d ⟩ e₂) (here bc) (appˡ V? q)
  with _ , _ , _ , refl , Vw ← bcRedex-fn bc = ⊥-elim (plug-K⊥ q)
plug-det (e₁ ·⟨ d ⟩ e₂) (here bc) (appʳ V? q)
  with _ , _ , _ , refl , Vw ← bcRedex-fn bc = ⊥-elim (plug-value⊥ Vw q)
plug-det (e₁ ·⟨ d ⟩ e₂) (appˡ V? p) (here bc)
  with _ , _ , _ , refl , Vw ← bcRedex-fn bc = ⊥-elim (plug-K⊥ p)
plug-det (e₁ ·⟨ d ⟩ e₂) (appʳ V? p) (here bc)
  with _ , _ , _ , refl , Vw ← bcRedex-fn bc = ⊥-elim (plug-value⊥ Vw p)
plug-det (e₁ ·⟨ d ⟩ e₂) (appˡ _ p) (appˡ _ q) = plug-det e₁ p q
plug-det (e₁ ·⟨ d ⟩ e₂) (appʳ _ p) (appʳ _ q) = plug-det e₂ p q
plug-det (e₁ ·⟨ d ⟩ e₂) (appˡ V? p) (appʳ V?′ q) = ⊥-elim (app-conflict V? V?′ p q)
plug-det (e₁ ·⟨ d ⟩ e₂) (appʳ V?′ p) (appˡ V? q) = ⊥-elim (app-conflict V? V?′ q p)
plug-det (e₁ ⊗ e₂) (here ()) q
plug-det (e₁ ⊗ e₂) (pairˡ p) (here ())
plug-det (e₁ ⊗ e₂) (pairˡ p) (pairˡ q) = plug-det e₁ p q
plug-det (e₁ ⊗ e₂) (pairˡ p) (pairʳ V q) = ⊥-elim (plug-value⊥ V p)
plug-det (e₁ ⊗ e₂) (pairʳ V p) (here ())
plug-det (e₁ ⊗ e₂) (pairʳ V p) (pairˡ q) = ⊥-elim (plug-value⊥ V q)
plug-det (e₁ ⊗ e₂) (pairʳ _ p) (pairʳ _ q) = plug-det e₂ p q
plug-det (e₁ ; e₂) (here ()) q
plug-det (e₁ ; e₂) (seqˡ p) (here ())
plug-det (e₁ ; e₂) (seqˡ p) (seqˡ q) = plug-det e₁ p q
plug-det (`let e₁ `in e₂) (here ()) q
plug-det (`let e₁ `in e₂) (letˡ p) (here ())
plug-det (`let e₁ `in e₂) (letˡ p) (letˡ q) = plug-det e₁ p q
plug-det (`let⊗ e₁ `in e₂) (here ()) q
plug-det (`let⊗ e₁ `in e₂) (let⊗ˡ p) (here ())
plug-det (`let⊗ e₁ `in e₂) (let⊗ˡ p) (let⊗ˡ q) = plug-det e₁ p q
plug-det (`inj i e) (here ()) q
plug-det (`inj i e) (injˡ p) (here ())
plug-det (`inj i e) (injˡ p) (injˡ q) = plug-det e p q
plug-det (`case e `of⟨ e₁ ; e₂ ⟩) (here ()) q
plug-det (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) (here ())
plug-det (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) (caseˡ q) = plug-det e p q

------------------------------------------------------------------------
-- 5.  The payoff.

∈BCe-unique : {e : Tm n} → x ∈BCe e → y ∈BCe e → x ≡ y
∈BCe-unique p q = plug-det _ (∈BCe⇒plug p) (∈BCe⇒plug q)
