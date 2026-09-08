-- Smoke test (temporary): are the exported statements usable with implicits?
module BorrowedCF.Completeness.Scope.Smoke where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope

open Nat.Variables

-- two premises, two solutions, one closing substitution
merge-use : ∀ {Δ₁ Δ₂ : CSet} {m k n : ℕ} {σ₁ σ₂ : UV.Sub} →
  UVarsInΔ m k Δ₁ → UVarsInΔ k n Δ₂ → Solving σ₁ → Solving σ₂ →
  SolvedΔ Δ₁ σ₁ → SolvedΔ Δ₂ σ₂ →
  Σ[ σ ∈ UV.Sub ] (Solving σ × SolvedΔ (Δ₁ ++ Δ₂) σ)
merge-use {k = k} {σ₁ = σ₁} {σ₂ = σ₂} u₁ u₂ S₁ S₂ s₁ s₂ =
  merge k σ₁ σ₂ , merge-solving k σ₁ σ₂ S₁ S₂ , solvedΔ-merge k σ₁ σ₂ u₁ u₂ s₁ s₂

-- the A-LSplit shape: solve the fresh variable with the second component
single-use : ∀ {s : 𝕊 0} (m : ℕ) (¬Ss : ¬ Skips s) → SolvedTy s →
  Σ[ σ ∈ UV.Sub ] (Solving σ × (UV.ap σ (UV.fresh m) ≡ s))
single-use {s = s} m ¬Ss Ss =
  single (UV.fresh m) s ¬Ss , single-solving (UV.fresh m) s ¬Ss Ss , single-ap (UV.fresh m) s ¬Ss

-- scope of an inference derivation under a solved context
scope-use : ∀ {N} {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {m n} →
  SolvedCtx Γ → (d : Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n) → GuessIn m d →
  m Nat.≤ n × UVarsIn m n T × UVarsInΔ m n Δ
scope-use SΓ d g = scope⇒ SΓ d g

-- A-Var has no guess obligation at all
guess-var : ∀ {N} {Γ : Ctx N} {γ : Struct N} {m : ℕ} {x : 𝔽 N} {Δ₀ : CSet}
  (≤γ : Γ ∶ ` x ≼ γ ↑ Δ₀) → GuessIn m (A-Var {Γ = Γ} {γ = γ} {m = m} ≤γ)
guess-var ≤γ = tt

-- and its output set is exactly the one emitted by the structural premise
var-scope : ∀ {N} {Γ : Ctx N} {γ : Struct N} {m : ℕ} {x : 𝔽 N} {Δ₀ : CSet} →
  SolvedCtx Γ → (≤γ : Γ ∶ ` x ≼ γ ↑ Δ₀) →
  m Nat.≤ m × UVarsIn m m (Γ ﹫ x) × UVarsInΔ m m Δ₀
var-scope SΓ ≤γ = scope⇒ SΓ (A-Var ≤γ) tt
