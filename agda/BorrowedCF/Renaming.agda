module BorrowedCF.Renaming where

open import BorrowedCF.Prelude
open import Relation.Binary

open Nat.Variables

open Fin using (_↑ˡ_; _↑ʳ_) public

Ren : ℕ → ℕ → Set
Ren m n = 𝔽 m → 𝔽 n

variable ρ ρ₁ ρ₂ : Ren m n

Inj : ∀ m n → Pred (Ren m n) _
Inj _ _ = Injective _≡_ _≡_

Inj′ : Pred (Ren m n) _
Inj′ = Inj _ _

infixr 11 ↑_ _↑⋆_

↑_ : Ren m n → Ren (suc m) (suc n)
(↑ ρ) zero    = zero
(↑ ρ) (suc x) = suc (ρ x)

_↑⋆_ : (m : ℕ) → Ren n₁ n₂ → Ren (m + n₁) (m + n₂)
zero  ↑⋆ ρ = ρ
suc m ↑⋆ ρ = ↑ m ↑⋆ ρ

↑-injective : Inj m n ρ → Inj′ (↑ ρ)
↑-injective inj-ρ {zero}  {zero}  eq = refl
↑-injective inj-ρ {suc x} {suc y} eq = cong suc $ inj-ρ $ Fin.suc-injective eq

↑⋆-injective : Inj n₁ n₂ ρ → Inj′ (m ↑⋆ ρ)
↑⋆-injective {m = zero}  inj-ρ = inj-ρ
↑⋆-injective {m = suc m} inj-ρ = ↑-injective (↑⋆-injective inj-ρ)

↑-dist-∘ : (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) → ↑ ρ₂ ∘ ↑ ρ₁ ≗ ↑ (ρ₂ ∘ ρ₁)
↑-dist-∘ ρ₁ ρ₂ zero    = refl
↑-dist-∘ ρ₁ ρ₂ (suc x) = refl

↑-pres-≗ : ρ₁ ≗ ρ₂ → ↑ ρ₁ ≗ ↑ ρ₂
↑-pres-≗ eq zero    = refl
↑-pres-≗ eq (suc x) = cong suc (eq x)

↑⋆-pres-≗ : (n : ℕ) → ρ₁ ≗ ρ₂ → n ↑⋆ ρ₁ ≗ n ↑⋆ ρ₂
↑⋆-pres-≗ zero ρ≗ = ρ≗
↑⋆-pres-≗ (suc n) ρ≗ = ↑-pres-≗ (↑⋆-pres-≗ n ρ≗)

↑-id : ρ ≗ id → ↑ ρ ≗ id
↑-id eq zero    = refl
↑-id eq (suc x) = cong suc (eq x)

↑⋆-id : (n : ℕ) → ρ ≗ id → n ↑⋆ ρ ≗ id
↑⋆-id zero eq = eq
↑⋆-id (suc n) eq = ↑-id (↑⋆-id n eq)

wk : Ren n (suc n)
wk = suc

wk⋆ : (m : ℕ) → Ren n (m + n)
wk⋆ m x = m ↑ʳ x

wk-injective : Inj n (suc n) wk
wk-injective = Fin.suc-injective
