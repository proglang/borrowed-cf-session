-- | Inversions of `SolvedTm` / `SolvedTy` (both are data types, so every
--   lemma is a pattern match) and the `SolvedCtx` plumbing under binders.
module BorrowedCF.Completeness.Decl.Solved where

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Terms
open import BorrowedCF.Context
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base using (SolvedCtx)

open Nat.Variables

private variable
  e e₁ e₂ : Tm n

------------------------------------------------------------------------
-- Terms

-- (`solvedTm-K : SolvedTm (K c) → SolvedC c` is agent C2's, in
--  BorrowedCF.Completeness.Scope; not duplicated here.)

solvedTm-ƛ : {e : Tm (suc n)} → SolvedTm (ƛ e) → SolvedTm e
solvedTm-ƛ (ƛ s) = s

solvedTm-μ : {e : Tm (suc n)} → SolvedTm (μ e) → SolvedTm e
solvedTm-μ (μ s) = s

solvedTm-· : {e₁ e₂ : Tm n} {d : Dir} → SolvedTm (e₁ ·⟨ d ⟩ e₂) → SolvedTm e₁ × SolvedTm e₂
solvedTm-· (s₁ · s₂) = s₁ , s₂

solvedTm-; : {e₁ e₂ : Tm n} → SolvedTm (e₁ ; e₂) → SolvedTm e₁ × SolvedTm e₂
solvedTm-; (s₁ ; s₂) = s₁ , s₂

solvedTm-⊗ : {e₁ e₂ : Tm n} → SolvedTm (e₁ ⊗ e₂) → SolvedTm e₁ × SolvedTm e₂
solvedTm-⊗ (s₁ ⊗ s₂) = s₁ , s₂

solvedTm-let⊗ : {e₁ : Tm n} {e₂ : Tm (2 + n)} →
  SolvedTm (`let⊗ e₁ `in e₂) → SolvedTm e₁ × SolvedTm e₂
solvedTm-let⊗ (`let⊗ s₁ `in s₂) = s₁ , s₂

solvedTm-inj : {i : Side} {e : Tm n} → SolvedTm (`inj i e) → SolvedTm e
solvedTm-inj (`inj s) = s

solvedTm-case : {e : Tm n} {e₁ e₂ : Tm (suc n)} →
  SolvedTm `case e `of⟨ e₁ ; e₂ ⟩ → SolvedTm e × SolvedTm e₁ × SolvedTm e₂
solvedTm-case `case s `of⟨ s₁ ; s₂ ⟩ = s , s₁ , s₂

solvedTm-let : {e₁ : Tm n} {e₂ : Tm (suc n)} →
  SolvedTm (`let e₁ `in e₂) → SolvedTm e₁ × SolvedTm e₂
solvedTm-let (`let s₁ `in s₂) = s₁ , s₂

------------------------------------------------------------------------
-- Types

solvedTy-→ : SolvedTy (T ⟨ a ⟩→ U) → SolvedTy T × SolvedTy U
solvedTy-→ (t ⟨ _ ⟩→ u) = t , u

solvedTy-⊗ : SolvedTy (T ⊗⟨ d ⟩ U) → SolvedTy T × SolvedTy U
solvedTy-⊗ (t ⊗⟨ _ ⟩ u) = t , u

solvedTy-⊕ : SolvedTy (T ⊕ U) → SolvedTy T × SolvedTy U
solvedTy-⊕ (t ⊕ u) = t , u

solvedTy-⟨⟩ : SolvedTy ⟨ s ⟩ → SolvedTy s
solvedTy-⟨⟩ ⟨ x ⟩ = x

solvedTy-if : ∀ {i : Side} → SolvedTy T → SolvedTy U → SolvedTy (if i then T else U)
solvedTy-if {i = true}  t u = t
solvedTy-if {i = false} t u = u

------------------------------------------------------------------------
-- Contexts

solved-lookup : {Γ : Ctx n} → SolvedCtx Γ → (x : 𝔽 n) → SolvedTy (Γ ﹫ x)
solved-lookup sΓ x = sΓ x

solved-ctx-⸴ : {Γ : Ctx n} → SolvedTy T → SolvedCtx Γ → SolvedCtx (T ⸴ Γ)
solved-ctx-⸴ sT sΓ zero    = sT
solved-ctx-⸴ sT sΓ (suc x) = sΓ x
