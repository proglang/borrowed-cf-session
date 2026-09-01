module BorrowedCF.Terms.BaseSoup.Properties where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup

open Nat.Variables

rename-commutes-phi :
  (e : Tm n m) (ρ : 𝔽 n → 𝔽 n′) (τ : 𝔽 m → 𝔽 m′) →
  (e ⋯ᵣ ρ) ⋯phi τ ≡ (e ⋯phi τ) ⋯ᵣ ρ
rename-commutes-phi (` x) ρ τ = refl
rename-commutes-phi (`phi r) ρ τ = refl
rename-commutes-phi (K c) ρ τ = refl
rename-commutes-phi (ƛ e) ρ τ =
  cong ƛ (rename-commutes-phi e (liftRen ρ) τ)
rename-commutes-phi (μ e) ρ τ =
  cong μ (rename-commutes-phi e (liftRen ρ) τ)
rename-commutes-phi (e₁ ·⟨ d ⟩ e₂) ρ τ =
  cong₂ _·⟨ d ⟩_
    (rename-commutes-phi e₁ ρ τ)
    (rename-commutes-phi e₂ ρ τ)
rename-commutes-phi (e₁ ; e₂) ρ τ =
  cong₂ _;_
    (rename-commutes-phi e₁ ρ τ)
    (rename-commutes-phi e₂ ρ τ)
rename-commutes-phi (e₁ ⊗ e₂) ρ τ =
  cong₂ _⊗_
    (rename-commutes-phi e₁ ρ τ)
    (rename-commutes-phi e₂ ρ τ)
rename-commutes-phi (`let e₁ `in e₂) ρ τ =
  cong₂ `let_`in_
    (rename-commutes-phi e₁ ρ τ)
    (rename-commutes-phi e₂ (liftRen ρ) τ)
rename-commutes-phi (`let⊗ e₁ `in e₂) ρ τ =
  cong₂ `let⊗_`in_
    (rename-commutes-phi e₁ ρ τ)
    (rename-commutes-phi e₂ (liftRen (liftRen ρ)) τ)
rename-commutes-phi (`inj i e) ρ τ =
  cong (`inj i) (rename-commutes-phi e ρ τ)
rename-commutes-phi (`case e `of⟨ e₁ ; e₂ ⟩) ρ τ
  rewrite rename-commutes-phi e ρ τ =
  cong₂ (`case _ `of⟨_;_⟩)
    (rename-commutes-phi e₁ (liftRen ρ) τ)
    (rename-commutes-phi e₂ (liftRen ρ) τ)
