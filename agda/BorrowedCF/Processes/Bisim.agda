{-# OPTIONS --rewriting #-}

module BorrowedCF.Processes.Bisim where

open import Data.Nat.ListAction using (sum)
open import Data.Maybe as May using (Maybe; just; nothing)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔

open Nat.Variables
open 𝐓.Proc
open 𝐔.Proc

UChan : ℕ → Set
UChan n = Tm n × 𝔽 n × Tm n

chanTriple : UChan n → Tm n
chanTriple (e₁ , c , e₂) = (e₁ ⊗ (` c)) ⊗ e₂

-- ϕ[_] : 𝐓.BindGroup → Maybe 𝐔.Flag
-- ϕ[_] = L.foldr (λ b → just ∘ May.fromMaybe (case b of λ{ zero → 𝐔.set; (suc _) → 𝐔.unset })) nothing

ϕ[_] : ℕ → 𝐔.Flag
ϕ[ zero  ] = 𝐔.set
ϕ[ suc _ ] = 𝐔.unset

Ub[_] : (b : ℕ) → UChan m → ((b →ₛ m) → 𝐔.Proc m) → 𝐔.Proc m
Ub[ zero ] c f = f λ()
Ub[ suc zero ] (e₁ , x , e₂) f = f (((e₁ ⊗ (` x)) ⊗ e₂) ∷ₛ λ())
Ub[ suc (suc b) ] (e₁ , x , e₂) f = Ub[ suc b ] (K `unit , x , e₂) λ σ →
  f (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ)

UB[_] : (B : 𝐓.BindGroup) → UChan (2 + n) → ((sum B →ₛ 2 + n) → 𝐔.Proc (2 + n)) → 𝐔.Proc n
UB[ [] ] c f = ν (f λ())
UB[ b ∷ [] ] c f = {!!}
UB[ b ∷ B@(_ ∷ _) ] c f = φ (zero ↦ ϕ[ b ] ∥ {!!})

U[_] : 𝐓.Proc m → m →ₛ n → 𝐔.Proc n
U[ ⟪ e ⟫     ] σ = ⟪ e ⋯ σ ⟫
U[ P ∥ Q     ] σ = U[ P ] σ ∥ U[ Q ] σ
U[ ν B₁ B₂ P ] σ = ν {!!}
