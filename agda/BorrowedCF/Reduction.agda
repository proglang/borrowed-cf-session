module BorrowedCF.Reduction where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)

open import BorrowedCF.Prelude
open import BorrowedCF.TermsFinKits
open import BorrowedCF.Types

open Nat.Variables

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : 𝕋

data Value {n} : Tm n → Set where
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (λ[ d ] e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ,⟨ d ⟩ e₂)

infix 4 _–→_

data _–→_ {n} : Tm n → Tm n → Set where
  E-App : (V : Value e₂) → (λ[ d ] e₁) · e₂ –→ e₁ ⋯ ⦅ e₂ ⦆
  E-Seq : K `unit ; e –→ e
  E-Let : Value e₁ → `let e₁ `in e₂ –→ e₂ ⋯ ⦅ e₁ ⦆
  E-PairElim : (V₁ : Value e₁) (V₂ : Value e₂) → `let⊗ (e₁ ,⟨ d ⟩ e₂) `in e –→ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆
  E-Cx-·₁ : e₁ –→ e₂ → e₁ · e –→ e₂ · e
  E-Cx-·₂ : (V : Value e) → e₁ –→ e₂ → e · e₁ –→ e · e₂
  E-Cx-;  : e₁ –→ e₂ → e₁ ; e –→ e₂ ; e
  E-Cx-⊗₁ : e₁ –→ e₂ → e₁ ,⟨ d ⟩ e –→ e₂ ,⟨ d ⟩ e
  E-Cx-⊗₂ : (V : Value e) → e₁ –→ e₂ → e ,⟨ d ⟩ e₁ –→ e ,⟨ d ⟩ e₂
  E-Cx-let : e₁ –→ e₂ → `let e₁ `in e –→ `let e₂ `in e
  E-Cx-let⊗ : e₁ –→ e₂ → `let⊗ e₁ `in e –→ `let⊗ e₂ `in e

ChanCx : Ctx n → Set
ChanCx Γ = ∀ x → ∃ λ s → Γ x ≡ ⟨ s ⟩

module ≈ {n} = IsEquivalence (≈-isEquivalence n)

preservation : ChanCx Γ → Γ ; γ ⊢ e ∶ t ∣ ϵ → e –→ e′ → ∃ λ γ′ → γ ≈ γ′ × Γ ; γ′ ⊢ e′ ∶ t ∣ ϵ
preservation Γ-S (T-App s e₁ e₂) (E-App V-e₂) = {!!} , {!!} , {!!}
preservation Γ-S (T-App {d = d} s e₁ e₂) (E-Cx-·₁ x) =
  let γ′ , eq , e₁′ = preservation Γ-S e₁ x in
  _ , refl , T-App (s ◅◅ cong-joinDir d eq refl) e₁′ e₂
preservation Γ-S (T-App {d = d} s e₁ e₂) (E-Cx-·₂ V x) =
  let γ′ , eq , e₂′ = preservation Γ-S e₂ x in
  _ , refl , T-App (s ◅◅ cong-joinDir d refl eq) e₁ e₂′
preservation Γ-S (T-Let p/s s e₁ e₂) (E-Let x) = {!!}
preservation Γ-S (T-Let p/s s e₁ e₂) (E-Cx-let x) = {!!} --T-Let p/s s (preservation Γ-S e₁ x) e₂
preservation Γ-S (T-LetUnit p/s s e₁ e₂) (E-Cx-; x) = {!!} --T-LetUnit p/s s (preservation Γ-S e₁ x) e₂
preservation Γ-S (T-LetUnit p/s s (T-Const γ₁∼∅ _) e₂) E-Seq = _ , s ◅◅ joinP/S-∅₁ p/s γ₁∼∅ , e₂
preservation Γ-S (T-LetPair p/s s e₁ e₂) (E-Cx-let⊗ x) = {!!}
