-- | Phase 1 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §9, P2): TRANSLATION INVERSION.
--
--   Everything here is the reverse of a lemma of
--   `ForwardSoup/Expressions.agda`.  The soup rules see a thread as
--   `F [ K c ·¹ v ]*`; to reflect the step we must turn that decomposition
--   into a decomposition of the SOURCE expression `e` whose translation the
--   thread is.  Two hypotheses on the environment do the work:
--
--     `ValueEnv σ`  -- every `σ x` is a soup value, so a source variable can
--                      never masquerade as a redex or as a `μ`, `;`, `let`,
--                      `let⊗` or `case`;
--     `PairEnv σ`   -- every `σ x` is a PAIR.  The environments the
--                      translation actually builds map every variable to a
--                      `chanTriple`, i.e. `(e₁ ⊗ ` c) ⊗ e₂`, so this holds;
--                      it additionally rules out a variable masquerading as
--                      `K c`, as a `ƛ` or as an `inj`.  It does NOT rule out
--                      a variable masquerading as a pair -- a chanTriple IS
--                      one -- which is exactly the residual `let⊗`-on-a-
--                      variable case of `step-inversion`.
--
--   Contents:
--     1. irreducibility of values (`value-irreducible`) and the fact that a
--        redex is never a value (`plug-app-not-value`);
--     2. `T-value-inv` and the head-shape inversions `T-app-inv`,
--        `T-seq-inv`, `T-let-inv`, `T-letpair-inv`, `T-case-inv`,
--        `T-mu-inv` (all discharged by `ValueEnv` alone) and `T-const-inv`,
--        `T-lam-inv`, `T-inj-inv`, `T-pair-inv` (which return a disjunction
--        because a variable can legitimately carry that shape);
--     3. `frame-inversion` / `plug-inversion` / `plug-inversion-K`, the
--        reverse of `T[_]-plugᶠ` and `T[_]-plugᶠ*`;
--     4. `step-inversion`, the reverse of `T[_]-⋯→`.
--
--   No frame is ever compared for equality: frames carry `Value` proofs as
--   functions, so `frame-inversion` and `plug-inversion` state the frame
--   correspondence as an equality of PLUGGED TERMS,
--   `∀ t → Tᶠ*[ E ] Vσ [ t ]* ≡ F [ t ]*`.
module BorrowedCF.Simulation.BackwardSoup.Inversion where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Reduction.Base as SourceBase
import BorrowedCF.Reduction.Expressions as SourceRed
import BorrowedCF.Reduction.ExpressionsSoup as SoupRed
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Types using (Dir)

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using ( ValueEnv; T[_]-Value; Tᶠ[_]; Tᶠ*[_]
        ; T[_]-plugᶠ; T[_]-plugᶠ*; T[_]-⦅⦆; T[_]-wk
        )

open Source
  using ( `_; K; ƛ; μ; _·⟨_⟩_; _;_; _⊗_
        ; `let_`in_; `let⊗_`in_; `inj; `case_`of⟨_;_⟩
        )

open Nat.Variables

private
  variable
    d : Dir
    i : Source.Side

------------------------------------------------------------------------
-- 1.  Values are irreducible, and a redex is not a value.

frame-value-inv :
  {n : ℕ} (F : SoupRed.Frame n) {u : SoupTerm.Tm n} →
  SoupRed.Value (F SoupRed.[ u ]) → SoupRed.Value u
frame-value-inv (SoupRed.app₁ _ _ _) ()
frame-value-inv (SoupRed.app₂ _ _ _) ()
frame-value-inv (SoupRed.□⊗ _) (SoupRed.V-⊗ V₁ V₂) = V₁
frame-value-inv (_ SoupRed.⊗□) (SoupRed.V-⊗ V₁ V₂) = V₂
frame-value-inv (SoupRed.□; _) ()
frame-value-inv (SoupRed.`let-`in _) ()
frame-value-inv (SoupRed.`let⊗-`in _) ()
frame-value-inv (SoupRed.`inj□ _) (SoupRed.V-⊕ V) = V
frame-value-inv SoupRed.`case□`of⟨ _ ; _ ⟩ ()

plug-value-inv :
  {n : ℕ} (F : SoupRed.Frame* n) {u : SoupTerm.Tm n} →
  SoupRed.Value (F SoupRed.[ u ]*) → SoupRed.Value u
plug-value-inv [] V = V
plug-value-inv (F ∷ Fs) V = plug-value-inv Fs (frame-value-inv F V)

not-value-app :
  {n : ℕ} {t₁ t₂ : SoupTerm.Tm n} {d : Dir} →
  ¬ SoupRed.Value (t₁ SoupTerm.·⟨ d ⟩ t₂)
not-value-app ()

-- A soup redex is never a value, so a source VARIABLE can never translate
-- to one: this is what breaks every `` ` x `` case below.
plug-app-not-value :
  {n : ℕ} (F : SoupRed.Frame* n) {t₁ t₂ : SoupTerm.Tm n} {d : Dir} →
  ¬ SoupRed.Value (F SoupRed.[ t₁ SoupTerm.·⟨ d ⟩ t₂ ]*)
plug-app-not-value F V = not-value-app (plug-value-inv F V)

step-not-value :
  {n : ℕ} {t t′ : SoupTerm.Tm n} →
  t SoupRed.⋯→ t′ → ¬ SoupRed.Value t
step-not-value (SoupRed.E-□ (SoupRed.E-App _)) ()
step-not-value (SoupRed.E-□ (SoupRed.E-Seq _)) ()
step-not-value (SoupRed.E-□ (SoupRed.E-Let _)) ()
step-not-value (SoupRed.E-□ (SoupRed.E-PairElim _ _)) ()
step-not-value (SoupRed.E-□ (SoupRed.E-SumElim _)) ()
step-not-value (SoupRed.E-□ SoupRed.E-Unfold) ()
step-not-value (SoupRed.E-Ctx (SoupRed.app₁ _ _ _) red) ()
step-not-value (SoupRed.E-Ctx (SoupRed.app₂ _ _ _) red) ()
step-not-value (SoupRed.E-Ctx (SoupRed.□⊗ _) red) (SoupRed.V-⊗ V₁ V₂) =
  step-not-value red V₁
step-not-value (SoupRed.E-Ctx (_ SoupRed.⊗□) red) (SoupRed.V-⊗ V₁ V₂) =
  step-not-value red V₂
step-not-value (SoupRed.E-Ctx (SoupRed.□; _) red) ()
step-not-value (SoupRed.E-Ctx (SoupRed.`let-`in _) red) ()
step-not-value (SoupRed.E-Ctx (SoupRed.`let⊗-`in _) red) ()
step-not-value (SoupRed.E-Ctx (SoupRed.`inj□ _) red) (SoupRed.V-⊕ V) =
  step-not-value red V
step-not-value (SoupRed.E-Ctx SoupRed.`case□`of⟨ _ ; _ ⟩ red) ()

value-irreducible :
  {n : ℕ} {t t′ : SoupTerm.Tm n} →
  SoupRed.Value t → ¬ (t SoupRed.⋯→ t′)
value-irreducible V red = step-not-value red V

value-head-irreducible :
  {n : ℕ} {t t′ : SoupTerm.Tm n} →
  SoupRed.Value t → ¬ (t SoupRed.─→ t′)
value-head-irreducible V red = value-irreducible V (SoupRed.E-□ red)

-- A value environment never carries an application.
env-not-app :
  {n n′ : ℕ} {σ : Translation.Env n n′} →
  ValueEnv σ → (x : 𝔽 n) →
  {t₁ t₂ : SoupTerm.Tm n′} {d : Dir} →
  σ x ≢ t₁ SoupTerm.·⟨ d ⟩ t₂
env-not-app Vσ x equal = not-value-app (subst SoupRed.Value equal (Vσ x))

------------------------------------------------------------------------
-- 2.  Inverting the translation on the head constructor.

T-value-inv :
  {n n′ : ℕ} (w : Source.Tm n) (σ : Translation.Env n n′) →
  ValueEnv σ → SoupRed.Value (Translation.T[ w ] σ) → SourceBase.Value w
T-value-inv (` x) σ Vσ V = SourceBase.V-`
T-value-inv (K c) σ Vσ V = SourceBase.V-K
T-value-inv (ƛ w) σ Vσ V = SourceBase.V-λ
T-value-inv (μ w) σ Vσ ()
T-value-inv (w₁ ·⟨ d ⟩ w₂) σ Vσ ()
T-value-inv (w₁ ; w₂) σ Vσ ()
T-value-inv (w₁ ⊗ w₂) σ Vσ (SoupRed.V-⊗ V₁ V₂) =
  SourceBase.V-⊗ (T-value-inv w₁ σ Vσ V₁) (T-value-inv w₂ σ Vσ V₂)
T-value-inv (`let w₁ `in w₂) σ Vσ ()
T-value-inv (`let⊗ w₁ `in w₂) σ Vσ ()
T-value-inv (`inj j w) σ Vσ (SoupRed.V-⊕ V) =
  SourceBase.V-⊕ (T-value-inv w σ Vσ V)
T-value-inv (`case w `of⟨ w₁ ; w₂ ⟩) σ Vσ ()

T-app-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u₁ u₂ : SoupTerm.Tm n′} {d : Dir} →
  Translation.T[ e ] σ ≡ u₁ SoupTerm.·⟨ d ⟩ u₂ →
  Σ[ e₁ ∈ Source.Tm n ] Σ[ e₂ ∈ Source.Tm n ]
    (e ≡ e₁ ·⟨ d ⟩ e₂) ×
    (Translation.T[ e₁ ] σ ≡ u₁) × (Translation.T[ e₂ ] σ ≡ u₂)
T-app-inv (` x) σ Vσ equal = ⊥-elim (env-not-app Vσ x equal)
T-app-inv (K c) σ Vσ ()
T-app-inv (ƛ e) σ Vσ ()
T-app-inv (μ e) σ Vσ ()
T-app-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ refl = e₁ , e₂ , refl , refl , refl
T-app-inv (e₁ ; e₂) σ Vσ ()
T-app-inv (e₁ ⊗ e₂) σ Vσ ()
T-app-inv (`let e₁ `in e₂) σ Vσ ()
T-app-inv (`let⊗ e₁ `in e₂) σ Vσ ()
T-app-inv (`inj j e) σ Vσ ()
T-app-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ Vσ ()

T-seq-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u₁ u₂ : SoupTerm.Tm n′} →
  Translation.T[ e ] σ ≡ u₁ SoupTerm.; u₂ →
  Σ[ e₁ ∈ Source.Tm n ] Σ[ e₂ ∈ Source.Tm n ]
    (e ≡ e₁ ; e₂) ×
    (Translation.T[ e₁ ] σ ≡ u₁) × (Translation.T[ e₂ ] σ ≡ u₂)
T-seq-inv (` x) σ Vσ equal
  with subst SoupRed.Value equal (Vσ x)
... | ()
T-seq-inv (K c) σ Vσ ()
T-seq-inv (ƛ e) σ Vσ ()
T-seq-inv (μ e) σ Vσ ()
T-seq-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ ()
T-seq-inv (e₁ ; e₂) σ Vσ refl = e₁ , e₂ , refl , refl , refl
T-seq-inv (e₁ ⊗ e₂) σ Vσ ()
T-seq-inv (`let e₁ `in e₂) σ Vσ ()
T-seq-inv (`let⊗ e₁ `in e₂) σ Vσ ()
T-seq-inv (`inj j e) σ Vσ ()
T-seq-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ Vσ ()

T-let-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u₁ : SoupTerm.Tm n′} {u₂ : SoupTerm.Tm (1 + n′)} →
  Translation.T[ e ] σ ≡ SoupTerm.`let u₁ `in u₂ →
  Σ[ e₁ ∈ Source.Tm n ] Σ[ e₂ ∈ Source.Tm (1 + n) ]
    (e ≡ `let e₁ `in e₂) ×
    (Translation.T[ e₁ ] σ ≡ u₁) ×
    (Translation.T[ e₂ ] (Translation.liftEnv σ) ≡ u₂)
T-let-inv (` x) σ Vσ equal
  with subst SoupRed.Value equal (Vσ x)
... | ()
T-let-inv (K c) σ Vσ ()
T-let-inv (ƛ e) σ Vσ ()
T-let-inv (μ e) σ Vσ ()
T-let-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ ()
T-let-inv (e₁ ; e₂) σ Vσ ()
T-let-inv (e₁ ⊗ e₂) σ Vσ ()
T-let-inv (`let e₁ `in e₂) σ Vσ refl = e₁ , e₂ , refl , refl , refl
T-let-inv (`let⊗ e₁ `in e₂) σ Vσ ()
T-let-inv (`inj j e) σ Vσ ()
T-let-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ Vσ ()

T-letpair-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u₁ : SoupTerm.Tm n′} {u₂ : SoupTerm.Tm (2 + n′)} →
  Translation.T[ e ] σ ≡ SoupTerm.`let⊗ u₁ `in u₂ →
  Σ[ e₁ ∈ Source.Tm n ] Σ[ e₂ ∈ Source.Tm (2 + n) ]
    (e ≡ `let⊗ e₁ `in e₂) ×
    (Translation.T[ e₁ ] σ ≡ u₁) ×
    (Translation.T[ e₂ ]
      (Translation.liftEnv (Translation.liftEnv σ)) ≡ u₂)
T-letpair-inv (` x) σ Vσ equal
  with subst SoupRed.Value equal (Vσ x)
... | ()
T-letpair-inv (K c) σ Vσ ()
T-letpair-inv (ƛ e) σ Vσ ()
T-letpair-inv (μ e) σ Vσ ()
T-letpair-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ ()
T-letpair-inv (e₁ ; e₂) σ Vσ ()
T-letpair-inv (e₁ ⊗ e₂) σ Vσ ()
T-letpair-inv (`let e₁ `in e₂) σ Vσ ()
T-letpair-inv (`let⊗ e₁ `in e₂) σ Vσ refl = e₁ , e₂ , refl , refl , refl
T-letpair-inv (`inj j e) σ Vσ ()
T-letpair-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ Vσ ()

T-case-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u : SoupTerm.Tm n′} {u₁ u₂ : SoupTerm.Tm (1 + n′)} →
  Translation.T[ e ] σ ≡ SoupTerm.`case u `of⟨ u₁ ; u₂ ⟩ →
  Σ[ e₀ ∈ Source.Tm n ] Σ[ e₁ ∈ Source.Tm (1 + n) ]
  Σ[ e₂ ∈ Source.Tm (1 + n) ]
    (e ≡ `case e₀ `of⟨ e₁ ; e₂ ⟩) ×
    (Translation.T[ e₀ ] σ ≡ u) ×
    (Translation.T[ e₁ ] (Translation.liftEnv σ) ≡ u₁) ×
    (Translation.T[ e₂ ] (Translation.liftEnv σ) ≡ u₂)
T-case-inv (` x) σ Vσ equal
  with subst SoupRed.Value equal (Vσ x)
... | ()
T-case-inv (K c) σ Vσ ()
T-case-inv (ƛ e) σ Vσ ()
T-case-inv (μ e) σ Vσ ()
T-case-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ ()
T-case-inv (e₁ ; e₂) σ Vσ ()
T-case-inv (e₁ ⊗ e₂) σ Vσ ()
T-case-inv (`let e₁ `in e₂) σ Vσ ()
T-case-inv (`let⊗ e₁ `in e₂) σ Vσ ()
T-case-inv (`inj j e) σ Vσ ()
T-case-inv (`case e₀ `of⟨ e₁ ; e₂ ⟩) σ Vσ refl =
  e₀ , e₁ , e₂ , refl , refl , refl , refl

T-mu-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′) → ValueEnv σ →
  {u : SoupTerm.Tm (1 + n′)} →
  Translation.T[ e ] σ ≡ SoupTerm.μ u →
  Σ[ b ∈ Source.Tm (1 + n) ]
    (e ≡ μ b) × (Translation.T[ b ] (Translation.liftEnv σ) ≡ u)
T-mu-inv (` x) σ Vσ equal
  with subst SoupRed.Value equal (Vσ x)
... | ()
T-mu-inv (K c) σ Vσ ()
T-mu-inv (ƛ e) σ Vσ ()
T-mu-inv (μ b) σ Vσ refl = b , refl , refl
T-mu-inv (e₁ ·⟨ d ⟩ e₂) σ Vσ ()
T-mu-inv (e₁ ; e₂) σ Vσ ()
T-mu-inv (e₁ ⊗ e₂) σ Vσ ()
T-mu-inv (`let e₁ `in e₂) σ Vσ ()
T-mu-inv (`let⊗ e₁ `in e₂) σ Vσ ()
T-mu-inv (`inj j e) σ Vσ ()
T-mu-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ Vσ ()

-- The four shapes a VALUE can have.  A variable of the environment may
-- legitimately carry them, so these return a disjunction.

T-const-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  {c : Source.Const} →
  Translation.T[ e ] σ ≡ SoupTerm.K c →
  (e ≡ K c) ⊎ (Σ[ x ∈ 𝔽 n ] (e ≡ ` x) × (σ x ≡ SoupTerm.K c))
T-const-inv (` x) σ equal = inj₂ (x , refl , equal)
T-const-inv (K c) σ refl = inj₁ refl
T-const-inv (ƛ e) σ ()
T-const-inv (μ e) σ ()
T-const-inv (e₁ ·⟨ d ⟩ e₂) σ ()
T-const-inv (e₁ ; e₂) σ ()
T-const-inv (e₁ ⊗ e₂) σ ()
T-const-inv (`let e₁ `in e₂) σ ()
T-const-inv (`let⊗ e₁ `in e₂) σ ()
T-const-inv (`inj j e) σ ()
T-const-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ ()

T-lam-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  {u : SoupTerm.Tm (1 + n′)} →
  Translation.T[ e ] σ ≡ SoupTerm.ƛ u →
  (Σ[ b ∈ Source.Tm (1 + n) ]
     (e ≡ ƛ b) × (Translation.T[ b ] (Translation.liftEnv σ) ≡ u)) ⊎
  (Σ[ x ∈ 𝔽 n ] (e ≡ ` x) × (σ x ≡ SoupTerm.ƛ u))
T-lam-inv (` x) σ equal = inj₂ (x , refl , equal)
T-lam-inv (K c) σ ()
T-lam-inv (ƛ b) σ refl = inj₁ (b , refl , refl)
T-lam-inv (μ e) σ ()
T-lam-inv (e₁ ·⟨ d ⟩ e₂) σ ()
T-lam-inv (e₁ ; e₂) σ ()
T-lam-inv (e₁ ⊗ e₂) σ ()
T-lam-inv (`let e₁ `in e₂) σ ()
T-lam-inv (`let⊗ e₁ `in e₂) σ ()
T-lam-inv (`inj j e) σ ()
T-lam-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ ()

T-inj-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  {j : Source.Side} {u : SoupTerm.Tm n′} →
  Translation.T[ e ] σ ≡ SoupTerm.`inj j u →
  (Σ[ e₀ ∈ Source.Tm n ]
     (e ≡ `inj j e₀) × (Translation.T[ e₀ ] σ ≡ u)) ⊎
  (Σ[ x ∈ 𝔽 n ] (e ≡ ` x) × (σ x ≡ SoupTerm.`inj j u))
T-inj-inv (` x) σ equal = inj₂ (x , refl , equal)
T-inj-inv (K c) σ ()
T-inj-inv (ƛ e) σ ()
T-inj-inv (μ e) σ ()
T-inj-inv (e₁ ·⟨ d ⟩ e₂) σ ()
T-inj-inv (e₁ ; e₂) σ ()
T-inj-inv (e₁ ⊗ e₂) σ ()
T-inj-inv (`let e₁ `in e₂) σ ()
T-inj-inv (`let⊗ e₁ `in e₂) σ ()
T-inj-inv (`inj j e₀) σ refl = inj₁ (e₀ , refl , refl)
T-inj-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ ()

T-pair-inv :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  {u₁ u₂ : SoupTerm.Tm n′} →
  Translation.T[ e ] σ ≡ u₁ SoupTerm.⊗ u₂ →
  (Σ[ e₁ ∈ Source.Tm n ] Σ[ e₂ ∈ Source.Tm n ]
     (e ≡ e₁ ⊗ e₂) ×
     (Translation.T[ e₁ ] σ ≡ u₁) × (Translation.T[ e₂ ] σ ≡ u₂)) ⊎
  (Σ[ x ∈ 𝔽 n ] (e ≡ ` x) × (σ x ≡ u₁ SoupTerm.⊗ u₂))
T-pair-inv (` x) σ equal = inj₂ (x , refl , equal)
T-pair-inv (K c) σ ()
T-pair-inv (ƛ e) σ ()
T-pair-inv (μ e) σ ()
T-pair-inv (e₁ ·⟨ d ⟩ e₂) σ ()
T-pair-inv (e₁ ; e₂) σ ()
T-pair-inv (e₁ ⊗ e₂) σ refl = inj₁ (e₁ , e₂ , refl , refl , refl)
T-pair-inv (`let e₁ `in e₂) σ ()
T-pair-inv (`let⊗ e₁ `in e₂) σ ()
T-pair-inv (`inj j e) σ ()
T-pair-inv (`case e `of⟨ e₁ ; e₂ ⟩) σ ()

------------------------------------------------------------------------
-- 3.  Pair environments.
--
-- Every environment the translation builds maps variables to `chanTriple`s,
-- so `PairEnv` holds for all of them.  It is what excludes a variable from
-- masquerading as a constant, a lambda or an injection.

PairEnv : {n n′ : ℕ} → Translation.Env n n′ → Set
PairEnv {n} {n′} σ =
  (x : 𝔽 n) →
  Σ[ t₁ ∈ SoupTerm.Tm n′ ] Σ[ t₂ ∈ SoupTerm.Tm n′ ]
    σ x ≡ t₁ SoupTerm.⊗ t₂

pair-not-const :
  {n n′ : ℕ} {σ : Translation.Env n n′} → PairEnv σ →
  (x : 𝔽 n) {c : Source.Const} → σ x ≢ SoupTerm.K c
pair-not-const Pσ x equal with Pσ x
... | t₁ , t₂ , pairEq with sym pairEq ■ equal
...   | ()

pair-not-lam :
  {n n′ : ℕ} {σ : Translation.Env n n′} → PairEnv σ →
  (x : 𝔽 n) {u : SoupTerm.Tm (1 + n′)} → σ x ≢ SoupTerm.ƛ u
pair-not-lam Pσ x equal with Pσ x
... | t₁ , t₂ , pairEq with sym pairEq ■ equal
...   | ()

pair-not-inj :
  {n n′ : ℕ} {σ : Translation.Env n n′} → PairEnv σ →
  (x : 𝔽 n) {j : Source.Side} {u : SoupTerm.Tm n′} →
  σ x ≢ SoupTerm.`inj j u
pair-not-inj Pσ x equal with Pσ x
... | t₁ , t₂ , pairEq with sym pairEq ■ equal
...   | ()

-- `PairEnv` really does hold for the environments the translation builds:
-- every binder-group entry is a `chanTriple`, and `chanTriple` is a pair.

chanTriple-Pair :
  {n : ℕ} {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  Σ[ t₁ ∈ SoupTerm.Tm n ] Σ[ t₂ ∈ SoupTerm.Tm n ]
    Translation.chanTriple (e₁ , c , e₂) ≡ t₁ SoupTerm.⊗ t₂
chanTriple-Pair {e₁ = e₁} {e₂ = e₂} {c = c} =
  (e₁ SoupTerm.⊗ (SoupTerm.` c)) , e₂ , refl

Ub-Pair :
  ∀ b {n} {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  PairEnv (Translation.Ub[ b ] (e₁ , c , e₂))
Ub-Pair zero ()
Ub-Pair (suc zero) zero = chanTriple-Pair
Ub-Pair (suc (suc b)) zero = chanTriple-Pair
Ub-Pair (suc (suc b)) (suc x) = Ub-Pair (suc b) x

UBFrom-Pair :
  ∀ k (B : Typed.BindGroup) {n} (r : 𝔽 n)
    {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  PairEnv (proj₁ (Translation.UBFrom k B r (e₁ , c , e₂)))
UBFrom-Pair k [] r ()
UBFrom-Pair k (b ∷ []) r {e₁} {e₂} {c} =
  subst (λ p → PairEnv (Translation.Ub[ p ] (e₁ , c , e₂)))
    (sym (+-identityʳ b)) (Ub-Pair b)
UBFrom-Pair k (b ∷ B@(b′ ∷ B′)) r {e₁} {e₂} {c} y
  with Translation.UBFrom (suc k) B r
         (SoupTerm.`phi (r , k) , c , e₂) in ubEq
     | UBFrom-Pair (suc k) B r
         {e₁ = SoupTerm.`phi (r , k)} {e₂ = e₂} {c = c}
... | sigma , flags | Psigma with Fin.splitAt b y
...   | inj₁ x = Ub-Pair b x
...   | inj₂ x = Psigma x

UB-Pair :
  ∀ (B : Typed.BindGroup) {n} (r : 𝔽 n)
    {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  PairEnv (proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)))
UB-Pair B r = UBFrom-Pair zero B r

++ₛ-Pair :
  {p q n : ℕ} {σ₁ : Translation.Env p n} {σ₂ : Translation.Env q n} →
  PairEnv σ₁ → PairEnv σ₂ → PairEnv (σ₁ Translation.++ₛ σ₂)
++ₛ-Pair {p = p} P₁ P₂ i with Fin.splitAt p i
... | inj₁ x = P₁ x
... | inj₂ x = P₂ x

------------------------------------------------------------------------
-- 4.  Inverting one frame and a frame stack.

frame-inversion :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (F₀ : SoupRed.Frame n′) (u : SoupTerm.Tm n′) →
  Translation.T[ e ] σ ≡ F₀ SoupRed.[ u ] →
  ¬ SoupRed.Value u →
  Σ[ E₀ ∈ SourceBase.Frame n ] Σ[ e′ ∈ Source.Tm n ]
    (e ≡ E₀ SourceBase.[ e′ ]) ×
    ((t : SoupTerm.Tm n′) →
      Tᶠ[ E₀ ] {σ = σ} Vσ SoupRed.[ t ] ≡ F₀ SoupRed.[ t ]) ×
    (Translation.T[ e′ ] σ ≡ u)
frame-inversion e σ Vσ (SoupRed.app₁ t dir V?) u equal notV
  with T-app-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  ( SourceBase.app₁ e₂ dir
      (λ dL → T-value-inv e₂ σ Vσ (subst SoupRed.Value (sym eq₂) (V? dL)))
  , e₁ , eEq
  , (λ t₀ → cong (λ z → t₀ SoupTerm.·⟨ dir ⟩ z) eq₂)
  , eq₁ )
frame-inversion e σ Vσ (SoupRed.app₂ t dir V?) u equal notV
  with T-app-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  ( SourceBase.app₂ e₁ dir
      (λ p → T-value-inv e₁ σ Vσ (subst SoupRed.Value (sym eq₁) (V? p)))
  , e₂ , eEq
  , (λ t₀ → cong (λ z → z SoupTerm.·⟨ dir ⟩ t₀) eq₁)
  , eq₂ )
frame-inversion e σ Vσ (SoupRed.□⊗ t) u equal notV
  with T-pair-inv e σ equal
... | inj₁ (e₁ , e₂ , eEq , eq₁ , eq₂) =
  ( SourceBase.□⊗ e₂ , e₁ , eEq
  , (λ t₀ → cong (λ z → t₀ SoupTerm.⊗ z) eq₂)
  , eq₁ )
... | inj₂ (x , _ , varEq) =
  ⊥-elim (notV (frame-value-inv (SoupRed.□⊗ t)
    (subst SoupRed.Value varEq (Vσ x))))
frame-inversion e σ Vσ (V′ SoupRed.⊗□) u equal notV
  with T-pair-inv e σ equal
... | inj₁ (e₁ , e₂ , eEq , eq₁ , eq₂) =
  ( T-value-inv e₁ σ Vσ (subst SoupRed.Value (sym eq₁) V′) SourceBase.⊗□
  , e₂ , eEq
  , (λ t₀ → cong (λ z → z SoupTerm.⊗ t₀) eq₁)
  , eq₂ )
... | inj₂ (x , _ , varEq) =
  ⊥-elim (notV (frame-value-inv (V′ SoupRed.⊗□)
    (subst SoupRed.Value varEq (Vσ x))))
frame-inversion e σ Vσ (SoupRed.□; t) u equal notV
  with T-seq-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  ( SourceBase.□; e₂ , e₁ , eEq
  , (λ t₀ → cong (λ z → t₀ SoupTerm.; z) eq₂)
  , eq₁ )
frame-inversion e σ Vσ (SoupRed.`let-`in t) u equal notV
  with T-let-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  ( SourceBase.`let-`in e₂ , e₁ , eEq
  , (λ t₀ → cong (λ z → SoupTerm.`let t₀ `in z) eq₂)
  , eq₁ )
frame-inversion e σ Vσ (SoupRed.`let⊗-`in t) u equal notV
  with T-letpair-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  ( SourceBase.`let⊗-`in e₂ , e₁ , eEq
  , (λ t₀ → cong (λ z → SoupTerm.`let⊗ t₀ `in z) eq₂)
  , eq₁ )
frame-inversion e σ Vσ (SoupRed.`inj□ j) u equal notV
  with T-inj-inv e σ equal
... | inj₁ (e₀ , eEq , eq₀) =
  SourceBase.`inj□ j , e₀ , eEq , (λ t₀ → refl) , eq₀
... | inj₂ (x , _ , varEq) =
  ⊥-elim (notV (frame-value-inv (SoupRed.`inj□ j)
    (subst SoupRed.Value varEq (Vσ x))))
frame-inversion e σ Vσ SoupRed.`case□`of⟨ t₁ ; t₂ ⟩ u equal notV
  with T-case-inv e σ Vσ equal
... | e₀ , e₁ , e₂ , eEq , eq₀ , eq₁ , eq₂ =
  ( SourceBase.`case□`of⟨ e₁ ; e₂ ⟩ , e₀ , eEq
  , (λ t₀ → cong₂ (λ z₁ z₂ → SoupTerm.`case t₀ `of⟨ z₁ ; z₂ ⟩) eq₁ eq₂)
  , eq₀ )

-- The reverse of `T[_]-plugᶠ*`.  The head of the source redex is returned as
-- an arbitrary term `h` with `T[ h ] σ ≡ K c`; `plug-inversion-K` below turns
-- it into the constant itself.
plug-inversion :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (F : SoupRed.Frame* n′)
  (c : Source.Const) (dir : Dir) (v : SoupTerm.Tm n′) →
  Translation.T[ e ] σ ≡
    F SoupRed.[ SoupTerm.K c SoupTerm.·⟨ dir ⟩ v ]* →
  Σ[ E ∈ SourceBase.Frame* n ] Σ[ h ∈ Source.Tm n ] Σ[ w ∈ Source.Tm n ]
    (e ≡ E SourceBase.[ h ·⟨ dir ⟩ w ]*) ×
    ((t : SoupTerm.Tm n′) →
      Tᶠ*[ E ] {σ = σ} Vσ SoupRed.[ t ]* ≡ F SoupRed.[ t ]*) ×
    (Translation.T[ h ] σ ≡ SoupTerm.K c) ×
    (Translation.T[ w ] σ ≡ v)
plug-inversion e σ Vσ [] c dir v equal
  with T-app-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  [] , e₁ , e₂ , eEq , (λ t₀ → refl) , eq₁ , eq₂
plug-inversion e σ Vσ (F₀ ∷ F′) c dir v equal
  with frame-inversion e σ Vσ F₀
         (F′ SoupRed.[ SoupTerm.K c SoupTerm.·⟨ dir ⟩ v ]*) equal
         (plug-app-not-value F′)
... | E₀ , e′ , eEq , frameEq , innerEq
  with plug-inversion e′ σ Vσ F′ c dir v innerEq
...   | E , h , w , e′Eq , plugEq , hEq , wEq =
  ( E₀ ∷ E , h , w
  , (eEq ■ cong (λ z → E₀ SourceBase.[ z ]) e′Eq)
  , (λ t₀ →
      cong (λ z → Tᶠ[ E₀ ] {σ = σ} Vσ SoupRed.[ z ]) (plugEq t₀) ■
      frameEq (F′ SoupRed.[ t₀ ]*))
  , hEq , wEq )

-- With a `PairEnv` the head is the constant itself.  Every soup rule fires
-- on `F [ K c ·¹ v ]*` with an arbitrary argument `v`, so this single lemma
-- covers all of them (`𝓒[ e₁ × x × e₂ ]` and `v ⊗ 𝓒[ … ]` are instances).
plug-inversion-K :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (Pσ : PairEnv σ) (F : SoupRed.Frame* n′)
  (c : Source.Const) (dir : Dir) (v : SoupTerm.Tm n′) →
  Translation.T[ e ] σ ≡
    F SoupRed.[ SoupTerm.K c SoupTerm.·⟨ dir ⟩ v ]* →
  Σ[ E ∈ SourceBase.Frame* n ] Σ[ w ∈ Source.Tm n ]
    (e ≡ E SourceBase.[ K c ·⟨ dir ⟩ w ]*) ×
    ((t : SoupTerm.Tm n′) →
      Tᶠ*[ E ] {σ = σ} Vσ SoupRed.[ t ]* ≡ F SoupRed.[ t ]*) ×
    (Translation.T[ w ] σ ≡ v)
plug-inversion-K e σ Vσ Pσ F c dir v equal
  with plug-inversion e σ Vσ F c dir v equal
... | E , h , w , eEq , plugEq , hEq , wEq
  with T-const-inv h σ hEq
...   | inj₁ refl = E , w , eEq , plugEq , wEq
...   | inj₂ (x , _ , varEq) = ⊥-elim (pair-not-const Pσ x varEq)

-- The argument of a soup redex is often a pair (`RUS-Com` sends
-- `v ⊗ 𝓒[ … ]`).  A source term translating to a pair is a pair UNLESS it is
-- a variable -- a `chanTriple` IS a pair -- so the honest statement is the
-- disjunction; `pair-arg-inversion` is the version for a non-variable
-- argument.
pair-arg-inversion :
  {n n′ : ℕ} (w : Source.Tm n) (σ : Translation.Env n n′) →
  ((x : 𝔽 n) → w ≢ ` x) →
  {v₁ v₂ : SoupTerm.Tm n′} →
  Translation.T[ w ] σ ≡ v₁ SoupTerm.⊗ v₂ →
  Σ[ w₁ ∈ Source.Tm n ] Σ[ w₂ ∈ Source.Tm n ]
    (w ≡ w₁ ⊗ w₂) ×
    (Translation.T[ w₁ ] σ ≡ v₁) × (Translation.T[ w₂ ] σ ≡ v₂)
pair-arg-inversion w σ notVar equal with T-pair-inv w σ equal
... | inj₁ found = found
... | inj₂ (x , varEq , _) = ⊥-elim (notVar x varEq)

------------------------------------------------------------------------
-- 5.  Inverting an expression step.
--
-- `LetPairOnVariable e` is the ONE soup step that is not a source step: the
-- soup reduces `let⊗ (σ x) in …` by `E-PairElim` because `σ x` is a
-- chanTriple, i.e. a pair, while the source `let⊗ (` x) in …` is stuck.
-- Phase 3 excludes it by typing: `x` has a handle type, not a pair type.

LetPairOnVariable : {n : ℕ} → Source.Tm n → Set
LetPairOnVariable {n} e =
  Σ[ E ∈ SourceBase.Frame* n ] Σ[ x ∈ 𝔽 n ] Σ[ body ∈ Source.Tm (2 + n) ]
    e ≡ E SourceBase.[ `let⊗ (` x) `in body ]*

head-inversion :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (Pσ : PairEnv σ) {t t′ : SoupTerm.Tm n′} →
  Translation.T[ e ] σ ≡ t → t SoupRed.─→ t′ →
  (Σ[ e′ ∈ Source.Tm n ]
     (e SourceRed.⋯→ e′) × (Translation.T[ e′ ] σ ≡ t′)) ⊎
  LetPairOnVariable e

step-inversion :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (Pσ : PairEnv σ) {t t′ : SoupTerm.Tm n′} →
  Translation.T[ e ] σ ≡ t → t SoupRed.⋯→ t′ →
  (Σ[ e′ ∈ Source.Tm n ]
     (e SourceRed.⋯→ e′) × (Translation.T[ e′ ] σ ≡ t′)) ⊎
  LetPairOnVariable e
step-inversion e σ Vσ Pσ equal (SoupRed.E-□ red) =
  head-inversion e σ Vσ Pσ equal red
step-inversion e σ Vσ Pσ equal (SoupRed.E-Ctx {e₁ = t₁} F₀ red)
  with frame-inversion e σ Vσ F₀ t₁ equal (step-not-value red)
... | E₀ , e′ , eEq , frameEq , innerEq
  with step-inversion e′ σ Vσ Pσ innerEq red
...   | inj₁ (e″ , srcRed , tEq) =
  inj₁
    ( E₀ SourceBase.[ e″ ]
    , subst (λ z → z SourceRed.⋯→ E₀ SourceBase.[ e″ ]) (sym eEq)
        (SourceRed.E-Ctx E₀ srcRed)
    , ( T[_]-plugᶠ E₀ {e = e″} {σ = σ} Vσ ■
        cong (λ z → Tᶠ[ E₀ ] {σ = σ} Vσ SoupRed.[ z ]) tEq ■
        frameEq _ ) )
...   | inj₂ (E , x , body , shape) =
  inj₂ (E₀ ∷ E , x , body ,
    (eEq ■ cong (λ z → E₀ SourceBase.[ z ]) shape))

head-inversion e σ Vσ Pσ equal (SoupRed.E-App V₂)
  with T-app-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ with T-lam-inv e₁ σ eq₁
...   | inj₂ (x , _ , varEq) = ⊥-elim (pair-not-lam Pσ x varEq)
...   | inj₁ (b , lamEq , bEq) =
  inj₁
    ( Source._⋯_ b (Source.⦅ e₂ ⦆)
    , subst (λ z → z SourceRed.⋯→ Source._⋯_ b (Source.⦅ e₂ ⦆))
        (sym (eEq ■ cong (λ z → z ·⟨ _ ⟩ e₂) lamEq))
        (SourceRed.E-□ (SourceRed.E-App
          (T-value-inv e₂ σ Vσ (subst SoupRed.Value (sym eq₂) V₂))))
    , ( T[_]-⦅⦆ b e₂ σ ■ cong₂ SoupRed.subst₀ eq₂ bEq ) )
head-inversion e σ Vσ Pσ equal (SoupRed.E-Seq V₁)
  with T-seq-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  inj₁
    ( e₂
    , subst (λ z → z SourceRed.⋯→ e₂) (sym eEq)
        (SourceRed.E-□ (SourceRed.E-Seq
          (T-value-inv e₁ σ Vσ (subst SoupRed.Value (sym eq₁) V₁))))
    , eq₂ )
head-inversion e σ Vσ Pσ equal (SoupRed.E-Let V₁)
  with T-let-inv e σ Vσ equal
... | e₁ , e₂ , eEq , eq₁ , eq₂ =
  inj₁
    ( Source._⋯_ e₂ (Source.⦅ e₁ ⦆)
    , subst (λ z → z SourceRed.⋯→ Source._⋯_ e₂ (Source.⦅ e₁ ⦆))
        (sym eEq)
        (SourceRed.E-□ (SourceRed.E-Let
          (T-value-inv e₁ σ Vσ (subst SoupRed.Value (sym eq₁) V₁))))
    , ( T[_]-⦅⦆ e₂ e₁ σ ■ cong₂ SoupRed.subst₀ eq₁ eq₂ ) )
head-inversion e σ Vσ Pσ equal (SoupRed.E-PairElim V₁ V₂)
  with T-letpair-inv e σ Vσ equal
... | a , body , eEq , aEq , bodyEq with T-pair-inv a σ aEq
...   | inj₂ (x , varShape , _) =
  inj₂ ( [] , x , body
       , (eEq ■ cong (λ z → `let⊗ z `in body) varShape) )
...   | inj₁ (a₁ , a₂ , aShape , a₁Eq , a₂Eq) =
  inj₁
    ( Source._⋯_ (Source._⋯_ body (Source.⦅ Source.wk a₁ ⦆))
        (Source.⦅ a₂ ⦆)
    , subst
        (λ z → z SourceRed.⋯→
          Source._⋯_ (Source._⋯_ body (Source.⦅ Source.wk a₁ ⦆))
            (Source.⦅ a₂ ⦆))
        (sym (eEq ■ cong (λ z → `let⊗ z `in body) aShape))
        (SourceRed.E-□ (SourceRed.E-PairElim
          (T-value-inv a₁ σ Vσ (subst SoupRed.Value (sym a₁Eq) V₁))
          (T-value-inv a₂ σ Vσ (subst SoupRed.Value (sym a₂Eq) V₂))))
    , pairStep )
  where
  pairStep :
    Translation.T[
      Source._⋯_ (Source._⋯_ body (Source.⦅ Source.wk a₁ ⦆))
        (Source.⦅ a₂ ⦆) ] σ ≡ _
  pairStep =
    T[_]-⦅⦆ (Source._⋯_ body (Source.⦅ Source.wk a₁ ⦆)) a₂ σ ■
    cong₂ SoupRed.subst₀ a₂Eq
      (T[_]-⦅⦆ body (Source.wk a₁) (Translation.liftEnv σ) ■
       cong₂ SoupRed.subst₀
         (T[_]-wk a₁ σ ■ cong SoupTerm.wk a₁Eq)
         bodyEq)
head-inversion e σ Vσ Pσ equal (SoupRed.E-SumElim {i = true} V)
  with T-case-inv e σ Vσ equal
... | a , e₁ , e₂ , eEq , aEq , eq₁ , eq₂ with T-inj-inv a σ aEq
...   | inj₂ (x , _ , varEq) = ⊥-elim (pair-not-inj Pσ x varEq)
...   | inj₁ (a₀ , aShape , a₀Eq) =
  inj₁
    ( Source._⋯_ e₁ (Source.⦅ a₀ ⦆)
    , subst (λ z → z SourceRed.⋯→ Source._⋯_ e₁ (Source.⦅ a₀ ⦆))
        (sym (eEq ■ cong (λ z → `case z `of⟨ e₁ ; e₂ ⟩) aShape))
        (SourceRed.E-□ (SourceRed.E-SumElim
          (T-value-inv a₀ σ Vσ (subst SoupRed.Value (sym a₀Eq) V))))
    , ( T[_]-⦅⦆ e₁ a₀ σ ■ cong₂ SoupRed.subst₀ a₀Eq eq₁ ) )
head-inversion e σ Vσ Pσ equal (SoupRed.E-SumElim {i = false} V)
  with T-case-inv e σ Vσ equal
... | a , e₁ , e₂ , eEq , aEq , eq₁ , eq₂ with T-inj-inv a σ aEq
...   | inj₂ (x , _ , varEq) = ⊥-elim (pair-not-inj Pσ x varEq)
...   | inj₁ (a₀ , aShape , a₀Eq) =
  inj₁
    ( Source._⋯_ e₂ (Source.⦅ a₀ ⦆)
    , subst (λ z → z SourceRed.⋯→ Source._⋯_ e₂ (Source.⦅ a₀ ⦆))
        (sym (eEq ■ cong (λ z → `case z `of⟨ e₁ ; e₂ ⟩) aShape))
        (SourceRed.E-□ (SourceRed.E-SumElim
          (T-value-inv a₀ σ Vσ (subst SoupRed.Value (sym a₀Eq) V))))
    , ( T[_]-⦅⦆ e₂ a₀ σ ■ cong₂ SoupRed.subst₀ a₀Eq eq₂ ) )
head-inversion e σ Vσ Pσ equal SoupRed.E-Unfold
  with T-mu-inv e σ Vσ equal
... | b , eEq , bEq =
  inj₁
    ( Source._⋯_ b (Source.⦅ μ b ⦆)
    , subst (λ z → z SourceRed.⋯→ Source._⋯_ b (Source.⦅ μ b ⦆))
        (sym eEq) (SourceRed.E-□ SourceRed.E-Unfold)
    , ( T[_]-⦅⦆ b (μ b) σ ■
        cong₂ SoupRed.subst₀ (cong SoupTerm.μ bEq) bEq ) )

-- The specialisation with `t` the translation itself.
step-inversion′ :
  {n n′ : ℕ} (e : Source.Tm n) (σ : Translation.Env n n′)
  (Vσ : ValueEnv σ) (Pσ : PairEnv σ) {t′ : SoupTerm.Tm n′} →
  Translation.T[ e ] σ SoupRed.⋯→ t′ →
  (Σ[ e′ ∈ Source.Tm n ]
     (e SourceRed.⋯→ e′) × (Translation.T[ e′ ] σ ≡ t′)) ⊎
  LetPairOnVariable e
step-inversion′ e σ Vσ Pσ red = step-inversion e σ Vσ Pσ refl red
