module BorrowedCF.Simulation2.ReverseInv where

-- | Reusable inversion lemmas for the REVERSE simulation (sim←).
--
--   These are the SOUND, hole-free ingredients of the typed reflection of
--   expression reduction through a value substitution.  Substituting VALUES
--   into a term cannot create new head redexes EXCEPT possibly at a channel-
--   typed variable in head position — which the source typing rules out
--   (ChanCx forces every free variable to a channel type ⟨ s ⟩, never an arrow
--   / pair / sum, so it can never head an application / let⊗ / case).  Exports:
--     • value-no-head / value-step / value-⋯⁻¹ — a value never reduces; a step
--       through a VSub reflects the source-side Value side conditions,
--     • chanvar-not{Arr,Pair,Sum} / var-app-absurd — a channel variable can
--       never occupy a redex-head position.
--   (The full reflection that consumes these is blocked only by the frame-plug
--   non-invertibility of Agda's unifier; see Reverse.agda RU-Exp.)

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Context using (Ctx; Struct)

open import BorrowedCF.Types using (_≃_; ⟨_⟩; ≃-sym)

open Variables
open Fin.Patterns

-- A channel type is never equivalent to a function arrow.  ≃𝕋 is a head-
-- preserving congruence, so ⟨ s ⟩ ≃ (T ⟨ a ⟩→ U) has no constructor.
⟨⟩≄→ : ∀ {s T U a} → ¬ (⟨ s ⟩ ≃ (T ⟨ a ⟩→ U))
⟨⟩≄→ ()

⟨⟩≄⊗ : ∀ {s T U d} → ¬ (⟨ s ⟩ ≃ (T ⊗⟨ d ⟩ U))
⟨⟩≄⊗ ()

⟨⟩≄⊕ : ∀ {s T U} → ¬ (⟨ s ⟩ ≃ (T ⊕ U))
⟨⟩≄⊕ ()

-- A channel-typed variable cannot be typed at an arrow / pair / sum, so it can
-- never occupy the (function / scrutinee) head position of an application,
-- let⊗, or case.  These rule out a VSub manufacturing a head redex at a var.
chanvar-notArr : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U a ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⟨ a ⟩→ U) ∣ ϵ → ⊥
chanvar-notArr {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄→ (≃-sym (subst (_ ≃_) eq T≃))

chanvar-notPair : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U d ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⊗⟨ d ⟩ U) ∣ ϵ → ⊥
chanvar-notPair {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄⊗ (≃-sym (subst (_ ≃_) eq T≃))

chanvar-notSum : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⊕ U) ∣ ϵ → ⊥
chanvar-notSum {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄⊕ (≃-sym (subst (_ ≃_) eq T≃))

-- A channel-typed variable can never head a well-typed application: the
-- application rules type the function at an arrow, contradicting ChanCx.
var-app-absurd : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {e₂ T ϵ}
  → ChanCx Γ → Γ ; γ ⊢ (` x) · e₂ ∶ T ∣ ϵ → ⊥
var-app-absurd Γ-S (T-AppUnr _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppLin _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppLeft _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppRight _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-Conv _ _ d) = var-app-absurd Γ-S d
var-app-absurd Γ-S (T-Weaken _ d) = var-app-absurd Γ-S d

------------------------------------------------------------------------
-- Value reflection helpers (foundational; also re-used by Reverse).
------------------------------------------------------------------------

-- Value reflection through a VSub: a substituted term is a value iff the
-- source is.  (Recovers the source-side Value side conditions.)
value-⋯⁻¹ : (σ : m →ₛ n) → VSub σ → (e₀ : Tm m) → Value (e₀ ⋯ σ) → Value e₀
value-⋯⁻¹ σ Vσ (` x)               V = V-`
value-⋯⁻¹ σ Vσ (K c)               V = V-K
value-⋯⁻¹ σ Vσ (ƛ e)               V = V-λ
value-⋯⁻¹ σ Vσ (e₁ ⊗ e₂) (V-⊗ V₁ V₂) =
  V-⊗ (value-⋯⁻¹ σ Vσ e₁ V₁) (value-⋯⁻¹ σ Vσ e₂ V₂)
value-⋯⁻¹ σ Vσ (`inj i e)  (V-⊕ V)    = V-⊕ (value-⋯⁻¹ σ Vσ e V)

-- A value has no head reduction.
value-no-head : {t : Tm n} -> Value t -> {e2 : Tm n} -> ¬ (t ─→ e2)
value-no-head V-`         ()
value-no-head V-K         ()
value-no-head V-λ       ()
value-no-head (V-⊗ V1 V2) ()
value-no-head (V-⊕ V)   ()

-- A term that is a value never reduces.
value-step : {t : Tm n} -> Value t -> {e2 : Tm n} -> ¬ (t ⋯→ e2)
value-step V (E-□ hred)             = value-no-head V hred
value-step V (E-Ctx (□·  _)  red)    with V
... | ()
value-step V (E-Ctx (_ ·□)  red)    with V
... | ()
value-step V (E-Ctx (□⊗  _)  red)    with V
... | V-⊗ V1 V2 = value-step V1 red
value-step V (E-Ctx (_ ⊗□)  red)    with V
... | V-⊗ V1 V2 = value-step V2 red
value-step V (E-Ctx (□;  _)  red)    with V
... | ()
value-step V (E-Ctx (`let-`in  _)  red) with V
... | ()
value-step V (E-Ctx (`let⊗-`in _) red) with V
... | ()
value-step V (E-Ctx (`inj□  i) red)  with V
... | V-⊕ V' = value-step V' red
value-step V (E-Ctx `case□`of⟨ _ ; _ ⟩ red) with V
... | ()
