{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Domain where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Substitution

open import Data.Bool.Properties
open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Nullary.Decidable

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

infixl 18 _↓_

_↓_ : Struct n → Subset n → Struct n
(` x)   ↓ X = if does (x ∈? X) then ` x else []
[]      ↓ X = []
(α ∥ β) ↓ X = α ↓ X ∥ β ↓ X
(α ; β) ↓ X = α ↓ X ; β ↓ X

↓-dom : (γ : Struct n) (X : Subset n) → dom (γ ↓ X) ⊆ X
↓-dom (` x) X z∈ with x ∈? X
... | yes x∈ rewrite x∈⁅y⁆⇒x≡y _ z∈ = x∈
... | no  x∉ = ⁅⁆⊆ z∈
↓-dom []      X = ⁅⁆⊆
↓-dom (α ∥ β) X = [ ↓-dom α X , ↓-dom β X ]′ ∘ x∈p∪q⁻ _ _
↓-dom (α ; β) X = [ ↓-dom α X , ↓-dom β X ]′ ∘ x∈p∪q⁻ _ _

↓-identity-⊆ : (γ : Struct n) {X : Subset n} → dom γ ⊆ X → γ ↓ X ≡ γ
↓-identity-⊆ (` x) {X} ⊆X rewrite dec-true (x ∈? X) (⊆X (x∈⁅x⁆ x)) = refl
↓-identity-⊆ [] ⊆X = refl
↓-identity-⊆ (α ∥ β) ⊆X = cong₂ _∥_ (↓-identity-⊆ α (⊆-trans (p⊆p∪q _) ⊆X)) (↓-identity-⊆ β (⊆-trans (q⊆p∪q _ _) ⊆X))
↓-identity-⊆ (α ; β) ⊆X = cong₂ _;_ (↓-identity-⊆ α (⊆-trans (p⊆p∪q _) ⊆X)) (↓-identity-⊆ β (⊆-trans (q⊆p∪q _ _) ⊆X))

↓-identity : (γ : Struct n) → γ ↓ S.⊤ ≡ γ
↓-identity γ = ↓-identity-⊆ γ ⊆⊤

↓-idempotent : (γ : Struct n) (X : Subset n) → γ ↓ X ↓ X ≡ γ ↓ X
↓-idempotent γ X = ↓-identity-⊆ (γ ↓ X) {X} (↓-dom γ X)

↓-empty : (γ : Struct n) → Γ ∶ γ ↓ ⁅⁆ ≈ []
↓-empty (` x) rewrite dec-false (x ∈? ⁅⁆) ∉⁅⁆ = refl
↓-empty [] = refl
↓-empty (α ∥ β) = ≈-trans (∥-cong (↓-empty α) (↓-empty β)) ∥-unit₂
↓-empty (α ; β) = ≈-trans (;-cong (↓-empty α) (↓-empty β)) ;-unit₂

≈⇒dom≡ : Γ ∶ α ≈ β → dom α ≡ dom β
≈⇒dom≡ = Eq*.gfold isEquivalence dom ≈′⇒dom≡
  where
  ≈′⇒dom≡ : Γ ∶ α ≈′ β → dom α ≡ dom β
  ≈′⇒dom≡ ;′-assoc = ∪-assoc _ _ _
  ≈′⇒dom≡ (;′-cong₁ x) = cong (_∪ _) (≈′⇒dom≡ x)
  ≈′⇒dom≡ (;′-cong₂ x) = cong (_ ∪_) (≈′⇒dom≡ x)
  ≈′⇒dom≡ ∥′-unit = ∪-identityʳ _
  ≈′⇒dom≡ ∥′-assoc = ∪-assoc _ _ _
  ≈′⇒dom≡ ∥′-comm = ∪-comm _ _
  ≈′⇒dom≡ (∥′-cong₁ x) = cong (_∪ _) (≈′⇒dom≡ x)
  ≈′⇒dom≡ (∥′-dup U) = sym (∪-idem _)
  ≈′⇒dom≡ (∥′-tm-; U) = refl

dom≢⇒≉ : dom α ≢ dom β → ¬ Γ ∶ α ≈ β
dom≢⇒≉ dom≢ a≈b = dom≢ (≈⇒dom≡ a≈b)

`x≉[] : ∀ {x} → ¬ Γ ∶ ` x ≈ []
`x≉[] {x = x} = dom≢⇒≉ λ ⁅x⁆≡⁅⁆ → ∉⁅⁆ (subst (x ∈_) ⁅x⁆≡⁅⁆ (x∈⁅x⁆ x))

dom⁅⁆⇒[] : (γ : Struct n) → dom γ ≡ ⁅⁆ → Γ ∶ γ ≈ []
dom⁅⁆⇒[] (` x) eq = contradiction (subst (x ∈_) eq (x∈⁅x⁆ x)) ∉⁅⁆
dom⁅⁆⇒[] [] eq = refl
dom⁅⁆⇒[] (α ∥ β) eq = ≈-trans (∥-cong (dom⁅⁆⇒[] α (⊆-antisym (⊆-trans (p⊆p∪q (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))
                                      (dom⁅⁆⇒[] β ((⊆-antisym (⊆-trans (q⊆p∪q (dom α) (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))))
                              ∥-unit₂
dom⁅⁆⇒[] (α ; β) eq = ≈-trans (;-cong (dom⁅⁆⇒[] α (⊆-antisym (⊆-trans (p⊆p∪q (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))
                                      (dom⁅⁆⇒[] β ((⊆-antisym (⊆-trans (q⊆p∪q (dom α) (dom β)) (⊆-reflexive eq))
                                                              (⊥-elim ∘ ∉⁅⁆)))))
                              ;-unit₂

↓-empty⁻¹ : (γ : Struct n) (X : Subset n) → Γ ∶ γ ↓ X ≈ [] → dom γ ∩ X ≡ ⁅⁆
↓-empty⁻¹ (` x) X eq with x ∈? X
... | yes x∈ = contradiction eq `x≉[]
... | no  x∉ = ⊆-antisym (⊥-elim ∘ x∉ ∘ (λ (y∈⁅x⁆ , y∈X) → subst (_∈ X) (x∈⁅y⁆⇒x≡y _ y∈⁅x⁆) y∈X) ∘ x∈p∩q⁻ ⁅ x ⁆ X)
                         (⊥-elim ∘ ∉⁅⁆)
↓-empty⁻¹ [] X eq = ∩-zeroˡ X
↓-empty⁻¹ {Γ = Γ} (α ∥ β) X eq =
  ∩-distribʳ-∪ X (dom α) (dom β)
    ■ cong₂ _∪_ (↓-empty⁻¹ {Γ = Γ} α X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
                (↓-empty⁻¹ {Γ = Γ} β X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
    ■ ∪-identityˡ ⁅⁆
↓-empty⁻¹ {Γ = Γ} (α ; β) X eq =
  ∩-distribʳ-∪ X (dom α) (dom β)
    ■ cong₂ _∪_ (↓-empty⁻¹ {Γ = Γ} α X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
                (↓-empty⁻¹ {Γ = Γ} β X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
    ■ ∪-identityˡ ⁅⁆

≼⇒dom⊆ : Γ ∶ α ≼ β → dom α ⊆ dom β
≼⇒dom⊆ (≼-refl x) = ⊆-reflexive (≈⇒dom≡ x)
≼⇒dom⊆ (≼-∅ x) = ⊥-elim ∘ ∉⁅⁆
≼⇒dom⊆ (≼-wk {α₁} {α₂} {β₁} {β₂}) = ⊆-reflexive $
  let open ≡-Reasoning in
  dom ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) ≡⟨⟩
  (dom α₁ ∪ dom α₂) ∪ (dom β₁ ∪ dom β₂)  ≡⟨ ∪-assoc (dom α₁ ∪ dom α₂) (dom β₁) (dom β₂) ⟨
  ((dom α₁ ∪ dom α₂) ∪ dom β₁) ∪ dom β₂  ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom α₂ ∪ dom β₁) ∪ dom β₂    ≡⟨ cong (λ X → (dom α₁ ∪ X) ∪ dom β₂) (∪-comm (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom β₁ ∪ dom α₂) ∪ dom β₂    ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom β₁) (dom α₂)) ⟨
  ((dom α₁ ∪ dom β₁) ∪ dom α₂) ∪ dom β₂  ≡⟨ ∪-assoc (dom α₁ ∪ dom β₁) (dom α₂) (dom β₂) ⟩
  (dom α₁ ∪ dom β₁) ∪ (dom α₂ ∪ dom β₂)  ≡⟨⟩
  dom ((α₁ ; β₁) ∥ (α₂ ; β₂)) ∎
≼⇒dom⊆ (≼-trans x y) = ⊆-trans (≼⇒dom⊆ x) (≼⇒dom⊆ y)
≼⇒dom⊆ (≼-cong-; x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _
≼⇒dom⊆ (≼-cong-∥ x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _

dom⊈⇒⋠ : dom α ⊈ dom β → ¬ Γ ∶ α ≼ β
dom⊈⇒⋠ dom⊈ α≼β = dom⊈ (≼⇒dom⊆ α≼β)

`x⋠[] : ∀ {x} → ¬ Γ ∶ ` x ≼ []
`x⋠[] {x = x} = dom⊈⇒⋠ λ ⁅x⁆⊆⁅⁆ → ∉⁅⁆ (⁅x⁆⊆⁅⁆ (x∈⁅x⁆ x))

↓-dist-wk : ∀ (γ : Struct n) {x X} → wk γ ↓ (x ∷ X) ≡ wk (γ ↓ X)
↓-dist-wk (` y) {x} {X} = sym (if-float wk (does (y ∈? X)))
↓-dist-wk []      = refl
↓-dist-wk (α ∥ β) = cong₂ _∥_ (↓-dist-wk α) (↓-dist-wk β)
↓-dist-wk (α ; β) = cong₂ _;_ (↓-dist-wk α) (↓-dist-wk β)

postulate
  ∩-∁ : (p q : Subset n) → p ∩ q ≡ ⁅⁆ → p ∩ ∁ q ≡ p




{-
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
-}
