{-# OPTIONS --rewriting #-}

module BorrowedCF.Processes.Bisim where

open import Data.Nat.ListAction using (sum)
open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Sum using ([_,_]′)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔

open Nat.Variables
open Fin.Patterns
open 𝐓.Proc
open 𝐔.Proc

private
  module Draft where
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

    {-
    UB[_] : (B : 𝐓.BindGroup) → UChan (2 + n) → ((sum B →ₛ 2 + n) → 𝐔.Proc (2 + n)) → 𝐔.Proc n
    UB[ [] ] c f = ν (f λ())
    UB[ b ∷ [] ] c f = {!!}
    UB[ b ∷ B@(_ ∷ _) ] c f = φ (zero ↦ ϕ[ b ] ∥ {!!})

    U[_] : 𝐓.Proc m → m →ₛ n → 𝐔.Proc n
    U[ ⟪ e ⟫     ] σ = ⟪ e ⋯ σ ⟫
    U[ P ∥ Q     ] σ = U[ P ] σ ∥ U[ Q ] σ
    U[ ν B₁ B₂ P ] σ = ν {!!}
    -}

open Draft using (UChan; chanTriple; ϕ[_]; Ub[_]) public

syncs : 𝐓.BindGroup → ℕ
syncs [] = 0
syncs (_ ∷ []) = 0
syncs (_ ∷ B@(_ ∷ _)) = suc (syncs B)

infixr 5 _++ₛ_

_++ₛ_ : ∀ {a b N} → (a →ₛ N) → (b →ₛ N) → (a + b →ₛ N)
_++ₛ_ {a} σ₁ σ₂ i = [ σ₁ , σ₂ ]′ (Fin.splitAt a i)

UB[_] : (B : 𝐓.BindGroup) → UChan n → ((sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) → 𝐔.Proc n
UB[ [] ] cc f = f λ()
UB[ c ∷ [] ] (e₁ , x , e₂) f = Ub[ c ] (e₁ , x , e₂) (λ σh → f (σh ++ₛ λ()))
UB[ c ∷ B@(_ ∷ _) ] (e₁ , x , e₂) f =
  φ ( (0F ↦ ϕ[ c ])
    ∥ UB[ B ] ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
        (λ σt → Ub[ c ] ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
                        , weaken* ⦃ Kᵣ ⦄ (syncs B) (suc x)
                        , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) )
                        (λ σh → subst 𝐔.Proc (sym (+-suc (syncs B) _))
                                  (f (subst (sum (c ∷ B) →ₛ_) (+-suc (syncs B) _) (σh ++ₛ σt))))) )

U[_] : 𝐓.Proc m → m →ₛ n → 𝐔.Proc n
U[ ⟪ e ⟫     ] σ = ⟪ e ⋯ σ ⟫
U[ P ∥ Q     ] σ = U[ P ] σ ∥ U[ Q ] σ
U[ ν B₁ B₂ P ] σ =
  ν ( UB[ B₁ ] (K `unit , 0F , K `unit)
        (λ σ₁ → UB[ B₂ ] (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
          (λ σ₂ → U[ P ] ( ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ σ₂)
                         ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ))) )
