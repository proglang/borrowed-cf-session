{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Domain where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables
open Variables

variable
  X X₁ X₂ X₃ : Subset n
  Y Y₁ Y₂ Y₃ : Subset n

dom : Struct n → Subset n
dom []      = ⁅⁆
dom (` x)   = ⁅ x ⁆
dom (α ∥ β) = dom α ∪ dom β
dom (α ; β) = dom α ∪ dom β

{-
infix 4 _≐_

_≐_ : Rel (Subset n) _
X ≐ Y = X ⊆ Y × Y ⊆ X

≐-isEquivalence : ∀ n → IsEquivalence (_≐_ {n})
≐-isEquivalence _ = record
  { refl  = id , id
  ; sym   = Π.swap
  ; trans = λ (ij , ji) (jk , kj) → ⊆-trans ij jk , ⊆-trans kj ji
  }

≐-setoid : ∀ n → Setoid _ _
≐-setoid n = record { isEquivalence = ≐-isEquivalence n }

module _ {n : ℕ} where
  open IsEquivalence (≐-isEquivalence n)
    using ()
    renaming (refl to ≐-refl; reflexive to ≐-reflexive; sym to ≐-sym; trans to ≐-trans)
    public

module ≐-Reasoning {n} = SetoidReasoning (≐-setoid n)
-}

⊆⁅⁆⇒Empty : X ⊆ ⁅⁆ → Empty X
⊆⁅⁆⇒Empty X⊆ (_ , x∈) = ∉⁅⁆ (X⊆ x∈)

⊆⁅⁆⇒≡⁅⁆ : X ⊆ ⁅⁆ → X ≡ ⁅⁆
⊆⁅⁆⇒≡⁅⁆ = Empty-unique ∘ ⊆⁅⁆⇒Empty

⊆⁅x⁆×y∈⇒≡⁅x⁆ : ∀ {x y} → X ⊆ ⁅ x ⁆ → y ∈ X → X ≡ ⁅ x ⁆
⊆⁅x⁆×y∈⇒≡⁅x⁆ X⊆ y∈ = ⊆-antisym X⊆ (λ x′∈⁅x⁆ → subst (_∈ _) (x∈⁅y⁆⇒x≡y _ (X⊆ y∈) ■ sym (x∈⁅y⁆⇒x≡y _ x′∈⁅x⁆)) y∈)

⊆⁅x⁆×x∉⇒Empty : ∀ {x} → X ⊆ ⁅ x ⁆ → x ∉ X → Empty X
⊆⁅x⁆×x∉⇒Empty X⊆ x∉ (y , y∈) = x∉ (subst (_∈ _) (x∈⁅y⁆⇒x≡y _ (X⊆ y∈)) y∈)

Empty-∩₁ : Empty X → (Y : Subset n) → Empty (X ∩ Y)
Empty-∩₁ {X = X} ⁅⁆≐X Y (x , x∈) = ⁅⁆≐X (_ , p∩q⊆p X Y x∈)

Empty-∩₂ : (X : Subset n) {Y : Subset n} → Empty Y → Empty (X ∩ Y)
Empty-∩₂ X {Y} ⁅⁆≐Y (x , x∈) = ⁅⁆≐Y (_ , p∩q⊆q X Y x∈)

Empty-⁅⁆ : Empty {n} ⁅⁆
Empty-⁅⁆ (_ , x∈) = ∉⁅⁆ x∈

Disjoint : Rel (Struct n) _
Disjoint α β = Empty (dom α ∩ dom β)

∪-mono-⊆ : Bin.Monotonic₂ (_⊆_ {n}) _⊆_ _⊆_ _∪_
∪-mono-⊆ p⊆q u⊆v x∈ = x∈p∪q⁺ (Sum.map p⊆q u⊆v (x∈p∪q⁻ _ _ x∈))

∩-mono-⊆ : Bin.Monotonic₂ (_⊆_ {n}) _⊆_ _⊆_ _∩_
∩-mono-⊆ p⊆q u⊆v x∈ = x∈p∩q⁺ (p⊆q (x∈p∩q⁻ _ _ x∈ .proj₁) , u⊆v (x∈p∩q⁻ _ _ x∈ .proj₂))

∩-identityˡ-⊆ : {X : Subset n} (Y : Subset n) → Y ⊆ X → X ∩ Y ≡ Y
∩-identityˡ-⊆ Y Y⊆X = ⊆-antisym (λ x∈ → x∈p∩q⁻ _ _ x∈ .proj₂) (λ x∈ → x∈p∩q⁺ (Y⊆X x∈ , x∈))

∩-identityʳ-⊆ : (X : Subset n) {Y : Subset n} → X ⊆ Y → X ∩ Y ≡ X
∩-identityʳ-⊆ X X⊆Y = ⊆-antisym (λ x∈ → x∈p∩q⁻ _ _ x∈ .proj₁) (λ x∈ → x∈p∩q⁺ (x∈ , X⊆Y x∈))
