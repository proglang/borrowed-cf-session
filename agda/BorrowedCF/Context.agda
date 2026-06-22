{-# OPTIONS --rewriting #-}

module BorrowedCF.Context where

open import BorrowedCF.Prelude
open import BorrowedCF.Types

open import BorrowedCF.Context.Base as B hiding (module Variables) public
open import BorrowedCF.Context.Equivalence public
open import BorrowedCF.Context.Join public
open import BorrowedCF.Context.Subcontext public

data Seq⇒Pure : ParSeq → Rel Eff 0ℓ where
  par : Seq⇒Pure par ϵ ϵ
  seq : Seq⇒Pure seq ϵ ℙ

seq⇒pure-ℙℙ : ∀ {p/s} → Seq⇒Pure p/s ℙ ℙ
seq⇒pure-ℙℙ {par} = par
seq⇒pure-ℙℙ {seq} = seq

seq⇒pure-ℙϵ⁻¹ : ∀ {p/s} → Seq⇒Pure p/s ℙ ϵ → ϵ ≡ ℙ
seq⇒pure-ℙϵ⁻¹ par = refl
seq⇒pure-ℙϵ⁻¹ seq = refl

mk-seq⇒pure : ∀ {p/s ϵ₁ ϵ₂} → (p/s ≡ seq → ϵ₂ ≡ ℙ) → ∃[ ϵ₁′ ] ∃[ ϵ₂′ ] ϵ₁ ≤ϵ ϵ₁′ × ϵ₂ ≤ϵ ϵ₂′ × ϵ₁′ ≤ϵ (ϵ₁ ⊔ϵ ϵ₂) × Seq⇒Pure p/s ϵ₁′ ϵ₂′
mk-seq⇒pure {p/s = par} {ϵ₁} {ϵ₂} seq⇒P = _ , _ , x≤x⊔y ϵ₁ ϵ₂ , x≤y⊔x ϵ₁ ϵ₂ , ≤ϵ-refl , par where open EffProperties
mk-seq⇒pure {p/s = seq} seq⇒P rewrite seq⇒P refl = _ , _ , ≤ϵ-refl , ℙ≤ϵ , x≤x⊔y _ _ , seq where open EffProperties
