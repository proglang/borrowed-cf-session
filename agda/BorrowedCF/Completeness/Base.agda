-- | Shared definitions for algorithmic completeness (orchestrator-owned; agents import,
--   never edit).  The theorems are stated here as types so every agent targets the same
--   statement.
module BorrowedCF.Completeness.Base where

open import Data.List.Relation.Unary.All using (All)

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

-- Checking completeness: every declarative typing of a solved term at a solved type
-- is reconstructed by the checking judgment, with a closing substitution for the
-- generated constraints and an effect bounded by the declarative one.
Complete⇐ : Set
Complete⇐ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
    Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / k)

-- Inference completeness: the synthesised type is the declarative one up to ≃ after
-- closing.
Complete⇒ : Set
Complete⇒ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ T̂ ∈ 𝕋 ] Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
    Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (subTy T̂ σ ≃ T) × (Γ ; γ / m ⊢ e ⇒ T̂ ∣ ϵ′ ↑ Δ / k)
