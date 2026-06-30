module BorrowedCF.Context.Pattern where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Join
open import BorrowedCF.Context.Substitution

open Nat.Variables
open Variables

CxPat : ℕ → Set
CxPat n = List (Dir × Struct n)

pattern 𝒫[_] x = x ∷ []

{-
data CxPat (n : ℕ) : Set where
  here  : CxPat n
  left  : (d : Dir) (p : CxPat n)  (γ : Struct n) → CxPat n
  right : (d : Dir) (γ : Struct n) (p : CxPat n)  → CxPat n
-}

variable
  P P₁ P₂ P₃ P′ : CxPat n

_⋯𝓅_ : ⦃ K : Kit 𝓕 ⦄ → CxPat m → m –[ K ]→ n → CxPat n
P ⋯𝓅 ϕ = L.map (Π.map₂ (_⋯ ϕ)) P
{-
here          ⋯𝓅 ϕ = here
left  p/s p γ ⋯𝓅 ϕ = left p/s (p ⋯𝓅 ϕ) (γ ⋯ ϕ)
right p/s γ p ⋯𝓅 ϕ = right p/s (γ ⋯ ϕ) (p ⋯𝓅 ϕ)
-}

foldPattern : Dir × Struct n → Struct n → Struct n
foldPattern (d , γ) γ′ = join d γ γ′

_[_]𝓅 : CxPat n → Struct n → Struct n
P [ γ ]𝓅 = L.foldr foldPattern γ P
{-
here          [ γ′ ]𝓅 = γ′
left  p/s p γ [ γ′ ]𝓅 = join p/s (p [ γ′ ]𝓅) γ
right p/s γ p [ γ′ ]𝓅 = join p/s γ (p [ γ′ ]𝓅)
-}

[-]𝓅-dist-++ : (P₁ P₂ : CxPat n) (γ : Struct n) → (P₁ ++ P₂) [ γ ]𝓅 ≡ P₁ [ P₂ [ γ ]𝓅 ]𝓅
[-]𝓅-dist-++ P₁ P₂ γ = L.foldr-++ foldPattern γ P₁ P₂

_∶_≈𝓅_ : Ctx n → Rel (CxPat n) _
Γ ∶ P₁ ≈𝓅 P₂ = ∀ {α β} → Γ ∶ α ≈ β → Γ ∶ P₁ [ α ]𝓅 ≈ P₂ [ β ]𝓅

≈𝓅-refl : (P : CxPat n) → Γ ∶ P ≈𝓅 P
≈𝓅-refl []            eq = eq
≈𝓅-refl ((d , γ) ∷ P) eq = ≈-join d refl (≈𝓅-refl P eq)
{-
≈𝓅-refl here            eq = eq
≈𝓅-refl (left  p/s P γ) eq = ≈-join p/s (≈𝓅-refl P eq) refl
≈𝓅-refl (right p/s γ P) eq = ≈-join p/s refl (≈𝓅-refl P eq)
-}

≈𝓅-sym : (P₁ P₂ : CxPat n) → Γ ∶ P₁ ≈𝓅 P₂ → Γ ∶ P₂ ≈𝓅 P₁
≈𝓅-sym _ _ p-eq γ-eq = ≈-sym (p-eq (≈-sym γ-eq))

≈𝓅-trans : (P₁ P₂ P₃ : CxPat n) → Γ ∶ P₁ ≈𝓅 P₂ → Γ ∶ P₂ ≈𝓅 P₃ → Γ ∶ P₁ ≈𝓅 P₃
≈𝓅-trans _ _ _ p₁₂ p₂₃ eq = ≈-trans (p₁₂ eq) (p₂₃ refl)

≈𝓅-isEquivalence : (Γ : Ctx n) → IsEquivalence (Γ ∶_≈𝓅_)
≈𝓅-isEquivalence Γ = record
  { refl  = λ {x}     → ≈𝓅-refl x
  ; sym   = λ {x y}   → ≈𝓅-sym x y
  ; trans = λ {x y z} → ≈𝓅-trans x y z
  }

≈𝓅-setoid : Ctx n → Setoid _ _
≈𝓅-setoid Γ = record { isEquivalence = ≈𝓅-isEquivalence Γ }
