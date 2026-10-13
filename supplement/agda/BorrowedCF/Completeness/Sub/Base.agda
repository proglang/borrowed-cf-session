-- | Reflection of the two context predicates along a unification substitution.
--
--   `Unr` is reflected by `subTy` (it is ⊥ on every session type), so an
--   unrestrictedness premise survives the passage from the SOLVED context to the
--   context that still contains unification variables.  `Mobile` is NOT reflected
--   (`Mobile ⟨ s ⟩` is an existential modulo ≃, and a uvar leaf `` `` α `` never
--   matches `acq ; s′`), which is exactly why the mobility premises of the
--   subcontext relation have to become CONSTRAINTS.  This module provides the
--   replacement: a `MobCx` of the solved context becomes a solved constraint set
--   `allMobile Γ̂ α` of the uvar context.
module BorrowedCF.Completeness.Sub.Base where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Context.SubConstraint using (allMobile)
open import BorrowedCF.Algorithmic.Solved

open Nat.Variables
open Variables

private variable
  Γ̂ : Ctx n

------------------------------------------------------------------------
-- `Unr` is reflected along subTy, `Mobile` is not.

subTy-unr⁻¹ : {T : 𝕋} → Unr (subTy T σ) → Unr T
subTy-unr⁻¹ {T = `⊤}          `⊤        = `⊤
subTy-unr⁻¹ {T = T ⟨ a ⟩→ U}  (arr x)   = arr x
subTy-unr⁻¹ {T = T ⊗⟨ d ⟩ U}  (u₁ ⊗ u₂) = subTy-unr⁻¹ u₁ ⊗ subTy-unr⁻¹ u₂
subTy-unr⁻¹ {T = T ⊕ U}       (u₁ ⊕ u₂) = subTy-unr⁻¹ u₁ ⊕ subTy-unr⁻¹ u₂
subTy-unr⁻¹ {T = ⟨ s ⟩}       ⟨ () ⟩

------------------------------------------------------------------------
-- `Γ̂ approximates Γ under σ`: the uvar context becomes Γ after solving.

Approx : Ctx n → Ctx n → UV.Sub → Set
Approx Γ̂ Γ σ = ∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x

approx-⸴ : {T̂ T : 𝕋} → subTy T̂ σ ≃ T → Approx Γ̂ Γ σ → Approx (T̂ ⸴ Γ̂) (T ⸴ Γ) σ
approx-⸴ eq ap zero    = eq
approx-⸴ eq ap (suc x) = ap x

approx-id : SolvedΓ Γ σ → Approx Γ (subCtx Γ σ) σ
approx-id {Γ = Γ} {σ = σ} SΓ x =
  subst (subTy (Γ ﹫ x) σ ≃_) (sym (V.lookup-map x (λ t → subTy t σ) Γ)) ≃-refl

------------------------------------------------------------------------
-- Transfer of the two premises of the subcontext rules.

-- UnrCx transfers from the solved context to the uvar context (Unr is reflected).
unrCx-approx : Approx Γ̂ Γ σ → UnrCx Γ α → UnrCx Γ̂ α
unrCx-approx ap []            = []
unrCx-approx ap (U₁ ∥ U₂)     = unrCx-approx ap U₁ ∥ unrCx-approx ap U₂
unrCx-approx ap (U₁ ; U₂)     = unrCx-approx ap U₁ ; unrCx-approx ap U₂
unrCx-approx ap (`_ {x = x} u) = ` subTy-unr⁻¹ (unr-≃ (≃-sym (ap x)) u)

-- MobCx does NOT transfer; it becomes a SOLVED constraint set instead.
mobCx⇒solvedΔ : Approx Γ̂ Γ σ → MobCx Γ α → SolvedΔ (allMobile Γ̂ α) σ
mobCx⇒solvedΔ {α = ` x}   ap (` m)     = mobile-≃ (≃-sym (ap x)) m ∷ []
mobCx⇒solvedΔ {α = []}    ap []        = []
mobCx⇒solvedΔ {α = α ∥ β} ap (M₁ ∥ M₂) = AllP.++⁺ (mobCx⇒solvedΔ ap M₁) (mobCx⇒solvedΔ ap M₂)
mobCx⇒solvedΔ {α = α ; β} ap (M₁ ; M₂) = AllP.++⁺ (mobCx⇒solvedΔ ap M₁) (mobCx⇒solvedΔ ap M₂)

