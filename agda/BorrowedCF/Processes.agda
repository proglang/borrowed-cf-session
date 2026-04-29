module BorrowedCF.Processes where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

import BorrowedCF.Context as 𝐂

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open Nat.Variables

BindGroup : Set
BindGroup = List⁺ ℕ

sum⁺ : BindGroup → ℕ
sum⁺ = sum ∘ L⁺.toList

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : (B₁ B₂ : BindGroup) (P : Proc (sum⁺ B₁ + sum⁺ B₂ + n)) → Proc n

variable
  A A₁ A₂ A₃ A′ : BindGroup
  B B₁ B₂ B₃ B′ : BindGroup
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n

infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫ ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν B₁ B₂ P ⋯ₚ ϕ = ν B₁ B₂ (P ⋯ₚ ϕ ↑* (sum⁺ B₁ + sum⁺ B₂))

⋯ₚ-cong : ⦃ K : Kit 𝓕 ⦄ (P : Proc m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → P ⋯ₚ ϕ₁ ≡ P ⋯ₚ ϕ₂
⋯ₚ-cong ⟪ e ⟫ eq = cong ⟪_⟫ (⋯-cong e eq)
⋯ₚ-cong (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-cong P eq) (⋯ₚ-cong Q eq)
⋯ₚ-cong (ν B₁ B₂ P) eq = cong (ν B₁ B₂) (⋯ₚ-cong P (eq ~↑* _))

fusionₚ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄
          ⦃ C : CKit K₁ K₂ K ⦄ (P : Proc n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
          P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ ϕ₁ ·ₖ ϕ₂
fusionₚ ⟪ e ⟫ ϕ₁ ϕ₂ = cong ⟪_⟫ (fusion e ϕ₁ ϕ₂)
fusionₚ (P ∥ Q) ϕ₁ ϕ₂ = cong₂ _∥_ (fusionₚ P ϕ₁ ϕ₂) (fusionₚ Q ϕ₁ ϕ₂)
fusionₚ (ν B₁ B₂ P) ϕ₁ ϕ₂ = cong (ν B₁ B₂) (fusionₚ P (ϕ₁ ↑* _) (ϕ₂ ↑* _) ■ sym (⋯ₚ-cong P (dist-↑*-· _ ϕ₁ ϕ₂)))

postulate
  wkₚ : ∀ b₁ b₂ → b₁ + b₂ + n →ᵣ suc b₁ + suc b₂ + n

bindSwap : ∀ b₁ b₂ → b₁ + b₂ + n →ᵣ b₂ + b₁ + n
bindSwap {n} b₁ b₂ = Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁) ∘ Fin.splitAt (b₁ + b₂)

bindComm : ∀ a₁ a₂ b₁ b₂ → a₁ + a₂ + (b₁ + b₂ + n) →ᵣ b₁ + b₂ + (a₁ + a₂ + n)
bindComm {n} a₁ a₂ b₁ b₂ =
  Fin.cast (+-assoc (b₁ + b₂) (a₁ + a₂) n)
    ∘ bindSwap {n} (a₁ + a₂) (b₁ + b₂)
    ∘ Fin.cast (sym (+-assoc (a₁ + a₂) (b₁ + b₂) n))

weaken*-bindSwap-ex : ∀ a b → weaken* ⦃ Kᵣ ⦄ (a + b) ·ₖ bindSwap {n} a b ≗ weaken* (b + a)
weaken*-bindSwap-ex a b x
  rewrite weaken*~↑ʳ ⦃ Kᵣ ⦄ (a + b) x
        | Fin.splitAt-↑ʳ (a + b) _ x
        | weaken*~↑ʳ ⦃ Kᵣ ⦄ (b + a) x
        = refl

module _ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ {ϕ : m –[ K ]→ n} where
  bindSwap-exˡ : ∀ b₁ b₂ x →
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ m))
      ≡
    `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n) &/⋯ bindSwap b₁ b₂)
  bindSwap-exˡ b₁ b₂ x = let open ≡-Reasoning in
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ m))
      ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (Fin.swap b₁ x ↑ˡ m)) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n) , ϕ ·ₖ weaken* (b₂ + b₁) ] (splitAt (b₂ + b₁) (Fin.swap b₁ x ↑ˡ m)))
      ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ˡ (b₂ + b₁) (Fin.swap b₁ x) m) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n) , ϕ ·ₖ weaken* (b₂ + b₁) ]′ (inj₁ (Fin.swap b₁ x)))
      ≡⟨⟩
    `/id ⦃ K ⦄ (id/` (Fin.swap b₁ x ↑ˡ n))
      ≡⟨ `/`-is-` ⦃ K ⦄ (Fin.swap b₁ x ↑ˡ n) ⟩
    ` (Fin.swap b₁ x ↑ˡ n)
      ≡⟨⟩
    ` (Fin.join (b₂ + b₁) n (inj₁ (Fin.swap b₁ x)))
      ≡⟨ cong (`_ ∘ Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁)) (Fin.splitAt-↑ˡ (b₁ + b₂) x n) ⟨
    ` (Fin.join _ _ (Sum.map₁ (Fin.swap b₁) (Fin.splitAt (b₁ + b₂) (x ↑ˡ n))))
      ≡⟨⟩
    ` (bindSwap b₁ b₂ (x ↑ˡ n))
      ≡⟨ &/⋯-& ⦃ C ⦄ (x ↑ˡ n) (bindSwap b₁ b₂) ⟨
    `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n) &/⋯ bindSwap b₁ b₂) ∎

  bindSwap-exʳ : ∀ b₁ b₂ x →
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
      ≡
    `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (bindSwap b₁ b₂))
  bindSwap-exʳ b₁ b₂ x = let open ≡-Reasoning in
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
      ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (b₂ + b₁ ↑ʳ x)) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ] (Fin.splitAt (b₂ + b₁) (b₂ + b₁ ↑ʳ x)))
      ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ʳ (b₂ + b₁) m x) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ]′ (inj₂ x))
      ≡⟨⟩
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₂ + b₁))
      ≡⟨ &/⋯-⋯ (ϕ x) (weaken* (b₂ + b₁)) ⟩
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₂ + b₁)
      ≡⟨ ⋯-cong (`/id (ϕ x)) (weaken*-bindSwap-ex b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ·ₖ bindSwap b₁ b₂
      ≡⟨ fusion (`/id (ϕ x)) (weaken* (b₁ + b₂)) (bindSwap b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ⋯ bindSwap b₁ b₂
      ≡⟨ cong (_⋯ bindSwap b₁ b₂) (&/⋯-⋯ (ϕ x) (weaken* (b₁ + b₂))) ⟨
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂)) ⋯ bindSwap b₁ b₂
      ≡⟨ &/⋯-⋯ (ϕ x &/⋯ weaken* (b₁ + b₂)) (bindSwap b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂) &/⋯ bindSwap b₁ b₂)
      ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (bindSwap b₁ b₂)) ∎

  bindSwap-↑*-dist : (b₁ b₂ : ℕ) → bindSwap {m} b₁ b₂ ·[ Cᵣ ] ϕ ↑* (b₂ + b₁) ≗ ϕ ↑* (b₁ + b₂) ·ₖ bindSwap b₁ b₂
  bindSwap-↑*-dist b₁ b₂ x = `/id-injective $
    let open ≡-Reasoning in
    `/id ⦃ K ⦄ ((bindSwap b₁ b₂ ·[ Cᵣ ] ϕ ↑* (b₂ + b₁)) x) ≡⟨⟩
    `/id ⦃ K ⦄ (bindSwap b₁ b₂ x &/⋯ ϕ ↑* (b₂ + b₁))
      ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) z)) (Sum.map₁ (Fin.swap b₁) (Fin.splitAt (b₁ + b₂) x)) ⟩
    [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (y ↑ˡ m)))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) ((b₂ + b₁) ↑ʳ y)))
    ] (Sum.map₁ (Fin.swap b₁) (Fin.splitAt (b₁ + b₂) x))
      ≡⟨ [,]-map (Fin.splitAt (b₁ + b₂) x) ⟩
    [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ y ↑ˡ m)))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) ((b₂ + b₁) ↑ʳ y)))
    ] (Fin.splitAt (b₁ + b₂) x)
      ≡⟨ [,]-cong (bindSwap-exˡ b₁ b₂) (bindSwap-exʳ b₁ b₂) (Fin.splitAt (b₁ + b₂) x) ⟩
    [ (λ y → `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (y ↑ˡ _) &/⋯ bindSwap {n} b₁ b₂))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) y &/⋯ bindSwap {n} b₁ b₂))
    ] (Fin.splitAt (b₁ + b₂) x)
      ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ (CKit._&/⋯_ C z (bindSwap {n} b₁ b₂))) (Fin.splitAt (b₁ + b₂) x) ⟨
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ _) , ϕ ·ₖ weaken* (b₁ + b₂) ] (Fin.splitAt (b₁ + b₂) x) &/⋯ bindSwap {n} b₁ b₂)
      ≡⟨ cong (λ z → `/id (z &/⋯ bindSwap b₁ b₂)) (↑*∼id/wk-splitAt ϕ (b₁ + b₂) x) ⟨
    `/id ⦃ K ⦄ ((ϕ ↑* (b₁ + b₂)) x &/⋯ bindSwap b₁ b₂) ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ↑* (b₁ + b₂) ·ₖ bindSwap b₁ b₂) x) ∎

  bindSwap-↑*-dist-⋯ : ∀ (b₁ b₂ : ℕ) P → P ⋯ₚ bindSwap {m} b₁ b₂ ⋯ₚ ϕ ↑* (b₂ + b₁) ≡ P ⋯ₚ ϕ ↑* (b₁ + b₂) ⋯ₚ bindSwap b₁ b₂
  bindSwap-↑*-dist-⋯ b₁ b₂ P = fusionₚ P _ _ ■ ⋯ₚ-cong P (bindSwap-↑*-dist b₁ b₂) ■ sym (fusionₚ P _ _)

  postulate bindComm-↑*-dist : ∀ a₁ a₂ b₁ b₂ → bindComm a₁ a₂ b₁ b₂ ·ₖ ϕ ↑* (a₁ + a₂) ↑* (b₁ + b₂) ≗ ϕ ↑* (b₁ + b₂) ↑* (a₁ + a₂) ·ₖ bindComm a₁ a₂ b₁ b₂
{-
  bindComm-↑*-dist a₁ a₂ b₁ b₂ x = `/id-injective $
    let open ≡-Reasoning in
    `/id ⦃ K ⦄ ((bindComm a₁ a₂ b₁ b₂ ·ₖ ϕ ↑* (a₁ + a₂) ↑* (b₁ + b₂)) x)   ≡⟨⟩
    `/id ⦃ K ⦄ (bindComm a₁ a₂ b₁ b₂ x &/⋯ ϕ ↑* (a₁ + a₂) ↑* (b₁ + b₂))    ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ↑* (a₁ + a₂) ↑* (b₁ + b₂)) (bindComm a₁ a₂ b₁ b₂ x))
      ≡⟨ {!!} ⟩
    `/id ⦃ K ⦄ ((ϕ ↑* (b₁ + b₂) ↑* (a₁ + a₂)) x &/⋯ bindComm a₁ a₂ b₁ b₂)  ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ↑* (b₁ + b₂) ↑* (a₁ + a₂) ·ₖ bindComm a₁ a₂ b₁ b₂) x)   ∎
-}

  bindComm-↑*-dist-⋯ : ∀ a₁ a₂ b₁ b₂ P → P ⋯ₚ bindComm a₁ a₂ b₁ b₂ ⋯ₚ ϕ ↑* (a₁ + a₂) ↑* (b₁ + b₂) ≡ P ⋯ₚ ϕ ↑* (b₁ + b₂) ↑* (a₁ + a₂) ⋯ₚ bindComm a₁ a₂ b₁ b₂
  bindComm-↑*-dist-⋯ a₁ a₂ b₁ b₂ P = fusionₚ P _ _ ■ ⋯ₚ-cong P (bindComm-↑*-dist a₁ a₂ b₁ b₂) ■ sym (fusionₚ P _ _)

infix 4 _≋′_

data _≋′_ {n} : Rel (Proc n) 0ℓ where
  ∥-comm′ : P ∥ Q ≋′ Q ∥ P
  ∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃
  ∥-unit′ : ⟪ K `unit ⟫ ∥ P ≋′ P
  ν-swap′ : ν B₁ B₂ P ≋′ ν B₂ B₁ (P ⋯ₚ bindSwap (sum⁺ B₁) (sum⁺ B₂))
  ν-comm′ : ν B₁ B₂ (ν A₁ A₂ P) ≋′ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ bindComm (sum⁺ A₁) (sum⁺ A₂) (sum⁺ B₁) (sum⁺ B₂)))
  ν-ext′ : P ∥ ν B₁ B₂ Q ≋′ ν B₁ B₂ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum⁺ B₁ + sum⁺ B₂)) ∥ Q)
  ∥-cong′ : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q
  ν-cong′ : P ≋′ Q → ν B₁ B₂ P ≋′ ν B₁ B₂ Q

module _ where
  open Eq*

  infix 4 _≋_

  _≋_ : Rel (Proc n) _
  _≋_ = EqClosure _≋′_

  ∥-comm : P ∥ Q ≋ Q ∥ P
  ∥-comm = return ∥-comm′

  ∥-unitˡ : ⟪ K `unit ⟫ ∥ P ≋ P
  ∥-unitˡ = return ∥-unit′

  ∥-unitʳ : P ∥ ⟪ K `unit ⟫ ≋ P
  ∥-unitʳ = ∥-comm ◅◅ ∥-unitˡ

  ∥-assoc : P₁ ∥ (P₂ ∥ P₃) ≋ (P₁ ∥ P₂) ∥ P₃
  ∥-assoc = return ∥-assoc′

  ∥-cong : P₁ ≋ P₂ → Q₁ ≋ Q₂ → P₁ ∥ Q₁ ≋ P₂ ∥ Q₂
  ∥-cong ps qs = gmap (_∥ _) ∥-cong′ ps ◅◅ ∥-comm ◅◅ gmap (_∥ _) ∥-cong′ qs ◅◅ ∥-comm

  ν-swap : ν {n = n} B₁ B₂ P ≋ ν B₂ B₁ (P ⋯ₚ _)
  ν-swap = return ν-swap′

  ν-comm : ν B₁ B₂ (ν A₁ A₂ P) ≋ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ _))
  ν-comm = return ν-comm′

  ν-cong : P ≋ Q → ν B₁ B₂ P ≋ ν B₁ B₂ Q
  ν-cong = gmap (ν _ _) ν-cong′

  ⋯-preserves-≋′ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ {ϕ : m –[ K ]→ n} → (_⋯ₚ ϕ) Bin.Preserves _≋′_ ⟶ _≋′_
  ⋯-preserves-≋′ ∥-comm′ = ∥-comm′
  ⋯-preserves-≋′ ∥-assoc′ = ∥-assoc′
  ⋯-preserves-≋′ ∥-unit′ = ∥-unit′
  ⋯-preserves-≋′ (ν-swap′ {B₁} {B₂}) =
    subst₂ _≋′_ refl (cong (ν _ _) (sym (bindSwap-↑*-dist-⋯ (sum⁺ B₁) (sum⁺ B₂) _))) ν-swap′
  ⋯-preserves-≋′ (ν-comm′ {A₁} {A₂} {B₁} {B₂}) =
    subst₂ _≋′_ refl
      (cong (ν B₁ B₂ ∘ ν _ _) (sym (bindComm-↑*-dist-⋯ (sum⁺ B₁) (sum⁺ B₂) (sum⁺ A₁) (sum⁺ A₂) _)))
      ν-comm′
  ⋯-preserves-≋′ ν-ext′ =
    let eq = fusionₚ _ _ _ ■ ⋯ₚ-cong _ (↑*-wk _ _) ■ sym (fusionₚ _ _ _) in
    subst₂ _≋′_ refl (cong (ν _ _) (cong₂ _∥_ eq refl)) ν-ext′
  ⋯-preserves-≋′ (∥-cong′ x) = ∥-cong′ (⋯-preserves-≋′ x)
  ⋯-preserves-≋′ (ν-cong′ x) = ν-cong′ (⋯-preserves-≋′ x)

  infix 5 _≋-⋯_

  _≋-⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ → P ≋ Q → (ϕ : m –[ K ]→ n) → P ⋯ₚ ϕ ≋ Q ⋯ₚ ϕ
  eq ≋-⋯ ϕ = gmap (_⋯ₚ ϕ) ⋯-preserves-≋′ eq
