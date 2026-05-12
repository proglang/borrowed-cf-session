{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module BorrowedCF.Processes where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

import Data.Vec.Functional as F

open Nat.Variables

BindGroup : Set
BindGroup = List ℕ

data Proc (n : ℕ) : Set where
  ⟪_⟫ : (e : Tm n) → Proc n
  _∥_ : (P Q : Proc n) → Proc n
  ν   : (B₁ B₂ : BindGroup) (P : Proc (sum B₁ + sum B₂ + n)) → Proc n

variable
  A A₁ A₂ A₃ A′ : BindGroup
  B B₁ B₂ B₃ B′ : BindGroup
  P P₁ P₂ P₃ P′ : Proc n
  Q Q₁ Q₂ Q₃ Q′ : Proc n

infixl 5 _⋯ₚ_

_⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ → Proc m → m –[ K ]→ n → Proc n
⟪ e ⟫ ⋯ₚ ϕ = ⟪ e ⋯ ϕ ⟫
P ∥ Q ⋯ₚ ϕ = (P ⋯ₚ ϕ) ∥ (Q ⋯ₚ ϕ)
ν B₁ B₂ P ⋯ₚ ϕ = ν B₁ B₂ (P ⋯ₚ ϕ ↑* (sum B₁ + sum B₂))

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

≡-fusedₚ : ∀ {𝓕₁ 𝓕₂ 𝓕₃ 𝓕₄ : Scoped} {a b} →
  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K₃ : Kit 𝓕₃ ⦄ ⦃ K₄ : Kit 𝓕₄ ⦄ ⦃ K : Kit 𝓕 ⦄ →
  ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₃ : WkKit K₃ ⦄ ⦃ Ca : CKit K₁ K₂ K ⦄ ⦃ Cb : CKit K₃ K₄ K ⦄ →
  (P : Proc m) (ϕ₁ : m –[ K₁ ]→ a) (ϕ₂ : a –[ K₂ ]→ n) (ϕ₃ : m –[ K₃ ]→ b) (ϕ₄ : b –[ K₄ ]→ n) →
  ϕ₁ ·[ Ca ] ϕ₂ ≗ ϕ₃ ·[ Cb ] ϕ₄ →
  P ⋯ₚ ϕ₁ ⋯ₚ ϕ₂ ≡ P ⋯ₚ ϕ₃ ⋯ₚ ϕ₄
≡-fusedₚ P ϕ₁ ϕ₂ ϕ₃ ϕ₄ eq = fusionₚ P ϕ₁ ϕ₂ ■ ⋯ₚ-cong P eq ■ sym (fusionₚ P ϕ₃ ϕ₄)

postulate
  wkₚ : ∀ b₁ b₂ → b₁ + b₂ + n →ᵣ suc b₁ + suc b₂ + n

infix 4 _≋′_

data _≋′_ {n} : Rel (Proc n) 0ℓ where
  ∥-comm′ : P ∥ Q ≋′ Q ∥ P
  ∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃
  ∥-unit′ : ⟪ K `unit ⟫ ∥ P ≋′ P
  ν-swap′ : ν B₁ B₂ P ≋′ ν B₂ B₁ (P ⋯ₚ swapᵣ (sum B₁) (sum B₂))
  ν-comm′ : ν B₁ B₂ (ν A₁ A₂ P) ≋′ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))
  ν-ext′ : P ∥ ν B₁ B₂ Q ≋′ ν B₁ B₂ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) ∥ Q)
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
  ⋯-preserves-≋′ {ϕ = ϕ} (ν-swap′ {B₁} {B₂}) =
    subst₂ _≋′_ refl (cong (ν _ _) (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-swap (sum B₁) (sum B₂) ϕ))) ν-swap′
  ⋯-preserves-≋′ {ϕ = ϕ} (ν-comm′ {A₁} {A₂} {B₁} {B₂}) =
    subst₂ _≋′_ refl
      (cong (ν B₁ B₂ ∘ ν _ _) (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-assocSwap (sum B₁ + sum B₂) (sum A₁ + sum A₂) ϕ)))
      ν-comm′
  ⋯-preserves-≋′ ν-ext′ =
    let eq = fusionₚ _ _ _ ■ ⋯ₚ-cong _ (↑*-wk _ _) ■ sym (fusionₚ _ _ _) in
    subst₂ _≋′_ refl (cong (ν _ _) (cong₂ _∥_ eq refl)) ν-ext′
  ⋯-preserves-≋′ (∥-cong′ x) = ∥-cong′ (⋯-preserves-≋′ x)
  ⋯-preserves-≋′ (ν-cong′ x) = ν-cong′ (⋯-preserves-≋′ x)

  infix 5 _≋-⋯_

  _≋-⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ → P ≋ Q → (ϕ : m –[ K ]→ n) → P ⋯ₚ ϕ ≋ Q ⋯ₚ ϕ
  eq ≋-⋯ ϕ = gmap (_⋯ₚ ϕ) ⋯-preserves-≋′ eq

open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂

structNSeq : ∀ m → Struct (m + n)
structNSeq zero    = []
structNSeq (suc m) = ` zero ; 𝐂.wk (structNSeq m)

structBinder : (B : BindGroup) → Struct (sum B)
structBinder [] = []
structBinder (b ∷ B) = structNSeq b ∥ (structBinder B 𝐂.⋯ 𝐂.weaken* b)

data BindCtx : 𝕊 0 → Ctx n → Set where
  []  : BindCtx skip F.[]
  -∷_ : BindCtx s₂ Γ → BindCtx (s₁ ; s₂) (⟨ s₁ ⟩ F.∷ Γ)

infix 4 _;_⊢ₚ_

data _;_⊢ₚ_ (Γ : Ctx n) : Struct n → Proc n → Set where
  TP-Expr : ∀ {e} →
    Γ ; γ ⊢ e ∶ `⊤ ∣ 𝕀 →
    Γ ; γ ⊢ₚ ⟪ e ⟫

  TP-Par :
    Γ ; γ₁ ⊢ₚ P →
    Γ ; γ₂ ⊢ₚ Q →
    Γ ; γ₁ ∥ γ₂ ⊢ₚ P ∥ Q

  TP-Res :
    BindCtx {sum B₁} s Γ₁ →
    BindCtx {sum B₂} (dual s) Γ₂ →
    (Γ₁ F.++ Γ₂) F.++ Γ ; ({!!} ∥ {!!}) ∥ (γ 𝐂.⋯ 𝐂.weaken* _) ⊢ₚ P →
    Γ ; γ ⊢ₚ ν B₁ B₂ P
