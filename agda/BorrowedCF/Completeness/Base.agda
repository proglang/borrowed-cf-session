-- | Shared definitions for algorithmic completeness (orchestrator-owned; agents import,
--   never edit).  The theorems are stated here as types so every agent targets the same
--   statement.
--   Annotation campaign (2026-10-07): the core syntax has `_⦂_` and A-Ann fires only
--   on `e ⦂ T`.  Completeness therefore produces an ANNOTATED term ê with `e ⊑ ê`
--   (relation `_⊑_` below) and types ê, not e:
--     Complete⇐ : … → Γ ; γ ⊢ e ∶ T ∣ ϵ → ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê × (Σ ϵ′ Δ k σ …
--                   × Γ ; γ / m ⊢ ê ⇐ T ∣ ϵ′ ↑ Δ / k)
--     Complete⇒ : the same with `subTy T̂ σ ≃ T × Γ ; γ / m ⊢ ê ⇒ T̂ ∣ ϵ′ ↑ Δ / k`.
--   `fv-⊑` transports every `γ ∣fv[ _ ]` restriction from e-subterms to ê-subterms.
module BorrowedCF.Completeness.Base where

open import Data.List.Relation.Unary.All using (All)
open import Data.Fin.Subset using (_∪_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Simulation.Support.Confine using (count)

open Nat.Variables

-- A structure is LINEAR for Γ when every variable whose type is not unrestricted
-- occurs at most once.  (Without it completeness is false: under γ = x ∥ x with a
-- linear x, the declarative T-AppUnr types `f x · g x`, but A-App restricts to
-- γ ∣fv[e₁] = x ∥ x and A-Var needs ` x ≼ x ∥ x, which is underivable: `count-≼-eq`
-- (Simulation/Support/BeforeOrder.agda) shows ≼ preserves the count of a linear variable;
-- mechanised refutation in Probe/LinNeeded.agda.)
LinStruct : Ctx n → Struct n → Set
LinStruct Γ γ = ∀ x → ¬ Unr (Γ ﹫ x) → count x γ Nat.≤ 1

-- A context / term without unification variables.
SolvedCtx : Ctx n → Set
SolvedCtx Γ = ∀ x → SolvedTy (Γ ﹫ x)

-- `e ⊑ ê` reads "ê annotates e": ê is e with zero or more type annotations `_⦂ T`
-- inserted at arbitrary subterms (on top of the annotations e already carries).  One
-- homomorphic congruence rule per Tm constructor (including `_⦂_` itself, so annotated
-- inputs are allowed), plus `ann`, which wraps an annotation around the right side.
infix 4 _⊑_

data _⊑_ {n : ℕ} : Tm n → Tm n → Set where
  ⊑-var  : ∀ {x} → ` x ⊑ ` x
  ⊑-K    : ∀ {c} → K c ⊑ K c
  ⊑-ƛ    : ∀ {e ê} → e ⊑ ê → ƛ e ⊑ ƛ ê
  ⊑-μ    : ∀ {e ê} → e ⊑ ê → μ e ⊑ μ ê
  ⊑-app  : ∀ {e₁ ê₁ e₂ ê₂} d → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → e₁ ·⟨ d ⟩ e₂ ⊑ ê₁ ·⟨ d ⟩ ê₂
  ⊑-seq  : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → (e₁ ; e₂) ⊑ (ê₁ ; ê₂)
  ⊑-⊗    : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → e₁ ⊗ e₂ ⊑ ê₁ ⊗ ê₂
  ⊑-let  : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → `let e₁ `in e₂ ⊑ `let ê₁ `in ê₂
  ⊑-let⊗ : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → `let⊗ e₁ `in e₂ ⊑ `let⊗ ê₁ `in ê₂
  ⊑-inj  : ∀ {e ê} i → e ⊑ ê → `inj i e ⊑ `inj i ê
  ⊑-case : ∀ {e ê e₁ ê₁ e₂ ê₂} → e ⊑ ê → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ →
           `case e `of⟨ e₁ ; e₂ ⟩ ⊑ `case ê `of⟨ ê₁ ; ê₂ ⟩
  ⊑-⦂    : ∀ {e ê} → e ⊑ ê → ∀ T → (e ⦂ T) ⊑ (ê ⦂ T)
  ann    : ∀ {e ê} → e ⊑ ê → ∀ T → e ⊑ (ê ⦂ T)

⊑-refl : ∀ {n} {e : Tm n} → e ⊑ e
⊑-refl {e = ` x} = ⊑-var
⊑-refl {e = K c} = ⊑-K
⊑-refl {e = ƛ e} = ⊑-ƛ ⊑-refl
⊑-refl {e = μ e} = ⊑-μ ⊑-refl
⊑-refl {e = e₁ ·⟨ d ⟩ e₂} = ⊑-app d ⊑-refl ⊑-refl
⊑-refl {e = e₁ ; e₂} = ⊑-seq ⊑-refl ⊑-refl
⊑-refl {e = e₁ ⊗ e₂} = ⊑-⊗ ⊑-refl ⊑-refl
⊑-refl {e = `let e₁ `in e₂} = ⊑-let ⊑-refl ⊑-refl
⊑-refl {e = `let⊗ e₁ `in e₂} = ⊑-let⊗ ⊑-refl ⊑-refl
⊑-refl {e = `inj i e} = ⊑-inj i ⊑-refl
⊑-refl {e = `case e `of⟨ e₁ ; e₂ ⟩} = ⊑-case ⊑-refl ⊑-refl ⊑-refl
⊑-refl {e = e ⦂ T} = ⊑-⦂ ⊑-refl T

-- Annotations do not change the free variables, so every restriction `γ ∣fv[ e ]`
-- transports from e to its annotated version ê.
fv-⊑ : ∀ {n} {e ê : Tm n} → e ⊑ ê → fv ê ≡ fv e
fv-⊑ ⊑-var = refl
fv-⊑ ⊑-K = refl
fv-⊑ (⊑-ƛ p) = cong fvClose (fv-⊑ p)
fv-⊑ (⊑-μ p) = cong fvClose (fv-⊑ p)
fv-⊑ (⊑-app d p₁ p₂) = cong₂ _∪_ (fv-⊑ p₁) (fv-⊑ p₂)
fv-⊑ (⊑-seq p₁ p₂) = cong₂ _∪_ (fv-⊑ p₁) (fv-⊑ p₂)
fv-⊑ (⊑-⊗ p₁ p₂) = cong₂ _∪_ (fv-⊑ p₁) (fv-⊑ p₂)
fv-⊑ (⊑-let p₁ p₂) = cong₂ _∪_ (fv-⊑ p₁) (cong fvClose (fv-⊑ p₂))
fv-⊑ (⊑-let⊗ p₁ p₂) = cong₂ _∪_ (fv-⊑ p₁) (cong (fvClose* 2) (fv-⊑ p₂))
fv-⊑ (⊑-inj i p) = fv-⊑ p
fv-⊑ (⊑-case p p₁ p₂) =
  cong₂ _∪_ (fv-⊑ p) (cong₂ _∪_ (cong fvClose (fv-⊑ p₁)) (cong fvClose (fv-⊑ p₂)))
fv-⊑ (⊑-⦂ p T) = fv-⊑ p
fv-⊑ (ann p T) = fv-⊑ p

-- Checking completeness: every declarative typing of a solved term e at a solved type
-- is reconstructed by the checking judgment for some annotated version ê of e
-- (`e ⊑ ê`: the algorithm needs `_⦂ T` at checking forms in inference position), with a
-- closing substitution for the generated constraints and an effect bounded by the
-- declarative one.  The components come in the order ê, `e ⊑ ê`, then the effect,
-- constraints, exit index, closing substitution and the derivation for ê.
Complete⇐ : Set
Complete⇐ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê ×
    (Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
      Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ ê ⇐ T ∣ ϵ′ ↑ Δ / k))

-- Inference completeness: as Complete⇐, and the synthesised type is the declarative
-- one up to ≃ after closing.
Complete⇒ : Set
Complete⇒ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê ×
    (Σ[ T̂ ∈ 𝕋 ] Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
      Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (subTy T̂ σ ≃ T) × (Γ ; γ / m ⊢ ê ⇒ T̂ ∣ ϵ′ ↑ Δ / k))
