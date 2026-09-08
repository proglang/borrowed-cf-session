-- | Support for agent C8's constraint-generating subcontext judgment.
--
--   `≼`/`≈` keep two side conditions that are CHECKED, not emitted: `∥′-dup`
--   and `≼-∅` need `UnrCx`.  For the fix to be complete these must be
--   REFLECTED by the unification substitution: a declarative derivation that
--   duplicates an unrestricted structure has to be mirrored under the
--   algorithmic (unsolved) context.  It is, because `subTy` never changes the
--   𝕋-shape and `Unr` looks only at that shape (no session type is `Unr`).
--   `subTy-unr` (Algorithmic.Solved) is the forward direction; this is the
--   converse, which the fix needs and which was not in the development.
module BorrowedCF.Completeness.Probe.UnrReflect where

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved using (subTy; subCtx; subTy-unr)

open Nat.Variables

subTy-unr⁻¹ : ∀ (T : 𝕋) {σ} → Unr (subTy T σ) → Unr T
subTy-unr⁻¹ ⟨ s ⟩ ⟨ () ⟩
subTy-unr⁻¹ `⊤ u = `⊤
subTy-unr⁻¹ (T ⟨ a ⟩→ U) (arr pa) = arr pa
subTy-unr⁻¹ (T ⊗⟨ d ⟩ U) (u₁ ⊗ u₂) = subTy-unr⁻¹ T u₁ ⊗ subTy-unr⁻¹ U u₂
subTy-unr⁻¹ (T ⊕ U) (u₁ ⊕ u₂) = subTy-unr⁻¹ T u₁ ⊕ subTy-unr⁻¹ U u₂

-- ... and pointwise on structures, which is the form the ≼ rules use.
unrCx-reflect : ∀ {n} {Γ : Ctx n} {γ : Struct n} {σ} →
                UnrCx (subCtx Γ σ) γ → UnrCx Γ γ
unrCx-reflect [] = []
unrCx-reflect (U₁ ∥ U₂) = unrCx-reflect U₁ ∥ unrCx-reflect U₂
unrCx-reflect (U₁ ; U₂) = unrCx-reflect U₁ ; unrCx-reflect U₂
unrCx-reflect {Γ = Γ} {σ = σ} (`_ {x} u) =
  ` subTy-unr⁻¹ (Γ ﹫ x) (subst Unr (V.lookup-map x (λ t → subTy t σ) Γ) u)

unrCx-sub : ∀ {n} {Γ : Ctx n} {γ : Struct n} {σ} →
            UnrCx Γ γ → UnrCx (subCtx Γ σ) γ
unrCx-sub [] = []
unrCx-sub (U₁ ∥ U₂) = unrCx-sub U₁ ∥ unrCx-sub U₂
unrCx-sub (U₁ ; U₂) = unrCx-sub U₁ ; unrCx-sub U₂
unrCx-sub {Γ = Γ} {σ = σ} (`_ {x} u) =
  ` subst Unr (sym (V.lookup-map x (λ t → subTy t σ) Γ)) (subTy-unr u)
