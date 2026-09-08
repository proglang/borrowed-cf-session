-- | Smoke test: `alg-weaken` is exported from Weaken.Instance with NO module
--   parameters and no assumptions, at exactly the statement below.  This module
--   contains nothing else; it exists so that a regression in the parameter list
--   shows up as a type error here.  The `Approx` premise is spelled out on purpose.
module BorrowedCF.Completeness.Weaken.Smoke where

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Context
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Weaken.Instance using (alg-weaken)

open Nat.Variables

alg-weaken-statement :
  ∀ {σ : UV.Sub} → Solving σ →
  ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {m k : ℕ} {ξ : Mode}
    {e : Tm n} {T : 𝕋} {ϵ : Eff} {Δ : CSet} →
  (∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x) →
  LinStruct Γ γ₂ →
  Γ ∶ γ₁ ≼ γ₂ →
  Γ̂ ; γ₁ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k →
  SolvedΔ Δ σ →
  Σ[ Δ′ ∈ CSet ] (Γ̂ ; γ₂ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ′ / k) × SolvedΔ Δ′ σ
alg-weaken-statement = alg-weaken
