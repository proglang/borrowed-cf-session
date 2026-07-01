module BorrowedCF.Processes.Bisim where

open import Data.Nat.ListAction using (sum)
open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Sum using ([_,_]′)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import BorrowedCF.Reduction.Processes.Untyped as 𝐔

open Nat.Variables
open Fin.Patterns
open 𝐓.Proc
open 𝐔.Proc

UChan : ℕ → Set
UChan n = Tm n × 𝔽 n × Tm n

chanTriple : UChan n → Tm n
chanTriple (e₁ , c , e₂) = (e₁ ⊗ (` c)) ⊗ e₂

ϕ[_] : ℕ → 𝐔.Flag
ϕ[ zero  ] = 𝐔.acq
ϕ[ suc _ ] = 𝐔.drop

syncs : 𝐓.BindGroup → ℕ
syncs [] = 0
syncs (_ ∷ []) = 0
syncs (_ ∷ B@(_ ∷ _)) = suc (syncs B)

infixr 5 _++ₛ_

_++ₛ_ : ∀ {a b N} → (a →ₛ N) → (b →ₛ N) → (a + b →ₛ N)
_++ₛ_ {a} σ₁ σ₂ i = [ σ₁ , σ₂ ]′ (Fin.splitAt a i)

Ub[_] : (b : ℕ) → UChan n → b →ₛ n
Ub[ suc b ] (e₁ , c , e₂) zero = 𝐔.𝓒[ e₁ × c × * ]
Ub[ suc b ] (e₁ , c , e₂) (suc x) = Ub[ b ] (* , c , e₂) x

UB[_] : (B : 𝐓.BindGroup) → UChan n → ((sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) → 𝐔.Proc n
UB[ [] ] c f = f λ()
UB[ b ∷ [] ] c f = f λ _ → chanTriple c
UB[ b ∷ B@(_ ∷ _) ] (e₁ , x , e₂) f = φ ϕ[ b ] $ UB[ B ] (` 0F , suc x , wk e₂) λ σ →
  subst 𝐔.Proc (sym (+-suc (syncs B) _)) $ f λ y →
    subst Tm (+-suc (syncs B) _) $
      [ Ub[ b ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* (syncs B)
      , σ
      ]′ (splitAt b y)

U[_] : 𝐓.Proc m → m →ₛ n → 𝐔.Proc n
U[ ⟪ e ⟫     ] σ = ⟪ e ⋯ σ ⟫
U[ P ∥ Q     ] σ = U[ P ] σ ∥ U[ Q ] σ
U[ ν B₁ B₂ P ] σ =
  ν ( UB[ B₁ ] (* , 0F , *)
        (λ σ₁ → UB[ B₂ ] (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *)
          (λ σ₂ → U[ P ] ( ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ σ₂)
                         ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ))) )
