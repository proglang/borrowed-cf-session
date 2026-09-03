-- | Phase 3 helper for the ν-rule leaves (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   Every leaf rule that fires under a restriction sees its evaluation frames
--   weakened by the binder: the source process carries `E ⋯ᶠ* weaken* b`,
--   translated in the *body* environment, whereas the reduct carries `E`
--   itself, translated in the *ambient* environment.  The two agree because
--   the body environment extends the ambient one:
--
--     σ₁ (θ x) ≡ σ₂ x  ⟹  T[ e ⋯ θ ] σ₁ ≡ T[ e ] σ₂
--
--   These are the one-renaming versions of the two-renaming `*-ren-ren-coh`
--   lemmas of `Local/SplitCommon.agda`; `bindEnv-Value` is the companion
--   fact that a binder frame environment consists of values.
module BorrowedCF.Simulation.ForwardSoup.Local.Frames where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ[_]; Tᶠ*[_]; T[_]-⋯ᵣ; T[_]-Env-cong; T[_]-renEnv; wk-⋯ᵣ)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalEndpoint)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using (renameEnv)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-Value; UB-Value)

open Fin.Patterns

------------------------------------------------------------------------
-- Translating under one renaming.

T-ren-coh :
  ∀ {a b d : ℕ} (e : Source.Tm a) (θ : 𝔽 a → 𝔽 b)
    (σ₁ : Translation.Env b d) (σ₂ : Translation.Env a d) →
  ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ x) →
  Translation.T[ Source._⋯_ e θ ] σ₁ ≡ Translation.T[ e ] σ₂
T-ren-coh e θ σ₁ σ₂ coh =
  T[_]-⋯ᵣ e θ σ₁ ■ T[_]-Env-cong e coh

lift-ren-coh :
  ∀ {a b d : ℕ} (θ : 𝔽 a → 𝔽 b)
    (σ₁ : Translation.Env b d) (σ₂ : Translation.Env a d) →
  ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ x) →
  (x : 𝔽 (1 + a)) →
  Translation.liftEnv σ₁ ((θ Source.↑ᵣ) x) ≡ Translation.liftEnv σ₂ x
lift-ren-coh θ σ₁ σ₂ coh zero = refl
lift-ren-coh θ σ₁ σ₂ coh (suc x) = cong SoupTerm.wk (coh x)

------------------------------------------------------------------------
-- Plugging into a renamed frame.

Tᶠ-plug-ren-coh :
  ∀ {a b d : ℕ} (F₀ : SourceReduction.Frame a) (θ : 𝔽 a → 𝔽 b)
    (σ₁ : Translation.Env b d) (σ₂ : Translation.Env a d)
    (Vσ₁ : ValueEnv σ₁) (Vσ₂ : ValueEnv σ₂) →
  ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ x) →
  (t : SoupTerm.Tm d) →
  SoupExpression._[_] (Tᶠ[ SourceReduction._⋯ᶠ_ F₀ θ ] {σ = σ₁} Vσ₁) t ≡
  SoupExpression._[_] (Tᶠ[ F₀ ] {σ = σ₂} Vσ₂) t
Tᶠ-plug-ren-coh (SourceReduction.app₁ e d V?) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → t SoupTerm.·⟨ d ⟩ z) (T-ren-coh e θ σ₁ σ₂ coh)
Tᶠ-plug-ren-coh (SourceReduction.app₂ e d V?) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → z SoupTerm.·⟨ d ⟩ t) (T-ren-coh e θ σ₁ σ₂ coh)
Tᶠ-plug-ren-coh (SourceReduction.□⊗ e) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → t SoupTerm.⊗ z) (T-ren-coh e θ σ₁ σ₂ coh)
Tᶠ-plug-ren-coh (V SourceReduction.⊗□) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → z SoupTerm.⊗ t)
    (T-ren-coh (SourceReduction.vTm V) θ σ₁ σ₂ coh)
Tᶠ-plug-ren-coh (SourceReduction.□; e) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → t SoupTerm.; z) (T-ren-coh e θ σ₁ σ₂ coh)
Tᶠ-plug-ren-coh (SourceReduction.`let-`in e) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → SoupTerm.`let t `in z)
    (T-ren-coh e (θ Source.↑ᵣ)
      (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
      (lift-ren-coh θ σ₁ σ₂ coh))
Tᶠ-plug-ren-coh (SourceReduction.`let⊗-`in e) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong (λ z → SoupTerm.`let⊗ t `in z)
    (T-ren-coh e ((θ Source.↑ᵣ) Source.↑ᵣ)
      (Translation.liftEnv (Translation.liftEnv σ₁))
      (Translation.liftEnv (Translation.liftEnv σ₂))
      (lift-ren-coh (θ Source.↑ᵣ)
        (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
        (lift-ren-coh θ σ₁ σ₂ coh)))
Tᶠ-plug-ren-coh (SourceReduction.`inj□ i) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t = refl
Tᶠ-plug-ren-coh (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩)
  θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  cong₂ (λ z₁ z₂ → SoupTerm.`case t `of⟨ z₁ ; z₂ ⟩)
    (T-ren-coh e₁ (θ Source.↑ᵣ)
      (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
      (lift-ren-coh θ σ₁ σ₂ coh))
    (T-ren-coh e₂ (θ Source.↑ᵣ)
      (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
      (lift-ren-coh θ σ₁ σ₂ coh))

Tᶠ*-plug-ren-coh :
  ∀ {a b d : ℕ} (E : SourceReduction.Frame* a) (θ : 𝔽 a → 𝔽 b)
    (σ₁ : Translation.Env b d) (σ₂ : Translation.Env a d)
    (Vσ₁ : ValueEnv σ₁) (Vσ₂ : ValueEnv σ₂) →
  ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ x) →
  (t : SoupTerm.Tm d) →
  SoupExpression._[_]* (Tᶠ*[ SourceReduction._⋯ᶠ*_ E θ ] {σ = σ₁} Vσ₁) t ≡
  SoupExpression._[_]* (Tᶠ*[ E ] {σ = σ₂} Vσ₂) t
Tᶠ*-plug-ren-coh [] θ σ₁ σ₂ Vσ₁ Vσ₂ coh t = refl
Tᶠ*-plug-ren-coh (F₀ ∷ E) θ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
  Tᶠ-plug-ren-coh F₀ θ σ₁ σ₂ Vσ₁ Vσ₂ coh
    (SoupExpression._[_]*
      (Tᶠ*[ SourceReduction._⋯ᶠ*_ E θ ] {σ = σ₁} Vσ₁) t)
  ■ cong (SoupExpression._[_] (Tᶠ[ F₀ ] {σ = σ₂} Vσ₂))
      (Tᶠ*-plug-ren-coh E θ σ₁ σ₂ Vσ₁ Vσ₂ coh t)

------------------------------------------------------------------------
-- Translating in a physically renamed environment.
--
--   Renaming the *environment* of a translated frame is the same as renaming
--   the translated frame itself.  `R-New` needs this because the soup rule
--   states its result with `frames-rename`, whereas the image of the reduct
--   speaks about the translation in the renamed environment.

renameEnv-Value :
  ∀ {k a b : ℕ} {sigma : Translation.Env k a} (rho : 𝔽 a → 𝔽 b) →
  ValueEnv sigma → ValueEnv (renameEnv rho sigma)
renameEnv-Value rho Vsigma x = SoupExpression.value-rename (Vsigma x) rho

private
  T-renEnv-lift :
    ∀ {a d d′ : ℕ} (e : Source.Tm (1 + a))
      (σ : Translation.Env a d) (ρ : 𝔽 d → 𝔽 d′) →
    Translation.T[ e ] (Translation.liftEnv (renameEnv ρ σ)) ≡
    Translation.T[ e ] (Translation.liftEnv σ) SoupTerm.⋯ᵣ SoupTerm.liftRen ρ
  T-renEnv-lift {a = a} e σ ρ =
    T[_]-Env-cong e liftEq
    ■ T[_]-renEnv e (Translation.liftEnv σ) (SoupTerm.liftRen ρ)
    where
    liftEq :
      (x : 𝔽 (1 + a)) →
      Translation.liftEnv (renameEnv ρ σ) x ≡
      Translation.liftEnv σ x SoupTerm.⋯ᵣ SoupTerm.liftRen ρ
    liftEq zero = refl
    liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)

  T-renEnv-lift₂ :
    ∀ {a d d′ : ℕ} (e : Source.Tm (2 + a))
      (σ : Translation.Env a d) (ρ : 𝔽 d → 𝔽 d′) →
    Translation.T[ e ]
      (Translation.liftEnv (Translation.liftEnv (renameEnv ρ σ))) ≡
    Translation.T[ e ] (Translation.liftEnv (Translation.liftEnv σ))
      SoupTerm.⋯ᵣ SoupTerm.liftRen (SoupTerm.liftRen ρ)
  T-renEnv-lift₂ {a = a} e σ ρ =
    T[_]-Env-cong e liftEq
    ■ T[_]-renEnv e (Translation.liftEnv (Translation.liftEnv σ))
        (SoupTerm.liftRen (SoupTerm.liftRen ρ))
    where
    liftEq :
      (x : 𝔽 (2 + a)) →
      Translation.liftEnv (Translation.liftEnv (renameEnv ρ σ)) x ≡
      Translation.liftEnv (Translation.liftEnv σ) x
        SoupTerm.⋯ᵣ SoupTerm.liftRen (SoupTerm.liftRen ρ)
    liftEq zero = refl
    liftEq (suc zero) = refl
    liftEq (suc (suc x)) =
      sym
        (wk-⋯ᵣ (SoupTerm.wk (σ x)) (SoupTerm.liftRen ρ)
         ■ cong SoupTerm.wk (wk-⋯ᵣ (σ x) ρ))

Tᶠ-plug-renEnv :
  ∀ {a d d′ : ℕ} (F₀ : SourceReduction.Frame a)
    {σ : Translation.Env a d} (Vσ : ValueEnv σ)
    (ρ : 𝔽 d → 𝔽 d′) (t : SoupTerm.Tm d′) →
  SoupExpression._[_]
    (Tᶠ[ F₀ ] {σ = renameEnv ρ σ} (renameEnv-Value ρ Vσ)) t ≡
  SoupExpression._[_]
    (SoupExpression.frame-rename (Tᶠ[ F₀ ] {σ = σ} Vσ) ρ) t
Tᶠ-plug-renEnv (SourceReduction.app₁ e d V?) {σ = σ} Vσ ρ t =
  cong (λ z → t SoupTerm.·⟨ d ⟩ z) (T[_]-renEnv e σ ρ)
Tᶠ-plug-renEnv (SourceReduction.app₂ e d V?) {σ = σ} Vσ ρ t =
  cong (λ z → z SoupTerm.·⟨ d ⟩ t) (T[_]-renEnv e σ ρ)
Tᶠ-plug-renEnv (SourceReduction.□⊗ e) {σ = σ} Vσ ρ t =
  cong (λ z → t SoupTerm.⊗ z) (T[_]-renEnv e σ ρ)
Tᶠ-plug-renEnv (V SourceReduction.⊗□) {σ = σ} Vσ ρ t =
  cong (λ z → z SoupTerm.⊗ t)
    (T[_]-renEnv (SourceReduction.vTm V) σ ρ)
Tᶠ-plug-renEnv (SourceReduction.□; e) {σ = σ} Vσ ρ t =
  cong (λ z → t SoupTerm.; z) (T[_]-renEnv e σ ρ)
Tᶠ-plug-renEnv (SourceReduction.`let-`in e) {σ = σ} Vσ ρ t =
  cong (λ z → SoupTerm.`let t `in z) (T-renEnv-lift e σ ρ)
Tᶠ-plug-renEnv (SourceReduction.`let⊗-`in e) {σ = σ} Vσ ρ t =
  cong (λ z → SoupTerm.`let⊗ t `in z) (T-renEnv-lift₂ e σ ρ)
Tᶠ-plug-renEnv (SourceReduction.`inj□ i) Vσ ρ t = refl
Tᶠ-plug-renEnv (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) {σ = σ} Vσ ρ t =
  cong₂ (λ z₁ z₂ → SoupTerm.`case t `of⟨ z₁ ; z₂ ⟩)
    (T-renEnv-lift e₁ σ ρ) (T-renEnv-lift e₂ σ ρ)

Tᶠ*-plug-renEnv :
  ∀ {a d d′ : ℕ} (E : SourceReduction.Frame* a)
    {σ : Translation.Env a d} (Vσ : ValueEnv σ)
    (ρ : 𝔽 d → 𝔽 d′) (t : SoupTerm.Tm d′) →
  SoupExpression._[_]*
    (Tᶠ*[ E ] {σ = renameEnv ρ σ} (renameEnv-Value ρ Vσ)) t ≡
  SoupExpression._[_]*
    (SoupExpression.frames-rename (Tᶠ*[ E ] {σ = σ} Vσ) ρ) t
Tᶠ*-plug-renEnv [] Vσ ρ t = refl
Tᶠ*-plug-renEnv (F₀ ∷ E) {σ = σ} Vσ ρ t =
  Tᶠ-plug-renEnv F₀ Vσ ρ
    (SoupExpression._[_]*
      (Tᶠ*[ E ] {σ = renameEnv ρ σ} (renameEnv-Value ρ Vσ)) t)
  ■ cong
      (SoupExpression._[_]
        (SoupExpression.frame-rename (Tᶠ[ F₀ ] {σ = σ} Vσ) ρ))
      (Tᶠ*-plug-renEnv E Vσ ρ t)

------------------------------------------------------------------------
-- A binder frame environment consists of values.

bindEnv-Value :
  ∀ {k n : ℕ} {B₁ B₂ : Typed.BindGroup} {channel : OrientedChannel n}
    {sigma : Translation.Env k (2 *ℕ n)} →
  ValueEnv sigma → ValueEnv (bindEnv B₁ B₂ channel sigma)
bindEnv-Value {B₁ = B₁} {B₂ = B₂} {channel = channel} Vsigma =
  ++ₛ-Value
    (++ₛ-Value
      (UB-Value B₁ (physicalEndpoint channel 0F)
        SoupExpression.V-K SoupExpression.V-K)
      (UB-Value B₂ (physicalEndpoint channel 1F)
        SoupExpression.V-K SoupExpression.V-K))
    Vsigma
