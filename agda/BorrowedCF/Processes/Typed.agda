{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module BorrowedCF.Processes.Typed where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd; symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions using (inv-`⊤)

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

open import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂

structNSeq : ∀ m → Struct m
structNSeq zero    = []
structNSeq (suc m) = ` zero ; 𝐂.wk (structNSeq m)

structBinder : (B : BindGroup) → Struct (sum B)
structBinder [] = []
structBinder (b ∷ B) = (structNSeq b 𝐂.⋯ᵣ 𝐂.wkʳ (sum B)) ∥ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ b)

data BindCtx : 𝕊 0 → Ctx n → Set where
  []  : BindCtx skip F.[]
  -∷_ : BindCtx s₂ Γ → BindCtx (s₁ ; s₂) (⟨ s₁ ⟩ ⸴ Γ)

bindCtx⇒chanCtx : BindCtx s Γ → ChanCx Γ
bindCtx⇒chanCtx (-∷ C) zero    = _ , refl
bindCtx⇒chanCtx (-∷ C) (suc x) = bindCtx⇒chanCtx C x

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
    (C : BindCtx {sum B₁} s Γ₁) →
    (C′ : BindCtx {sum B₂} (dual s) Γ₂) →
    (Γ₁ ⸴* Γ₂) ⸴* Γ ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                    ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                    ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* _)
      ⊢ₚ P →
    Γ ; γ ⊢ₚ ν B₁ B₂ P

  TP-Weaken :
    (γ≤ : Γ ∶ γ₁ ≼ γ₂) →
    Γ ; γ₁ ⊢ₚ P →
    Γ ; γ₂ ⊢ₚ P


subst-γₚ : γ₁ ≡ γ₂ → Γ ; γ₁ ⊢ₚ P → Γ ; γ₂ ⊢ₚ P
subst-γₚ refl x = x

inv-⟪⟫ : ∀ {e} → Γ ; γ ⊢ₚ ⟪ e ⟫ → Γ ; γ ⊢ e ∶ `⊤ ∣ 𝕀
inv-⟪⟫ (TP-Expr e) = e
inv-⟪⟫ (TP-Weaken γ≤ p) = T-Weaken γ≤ (inv-⟪⟫ p)

inv-∥ : Γ ; γ ⊢ₚ P ∥ Q →
  ∃[ α ] ∃[ β ] Γ ∶ α ∥ β ≼ γ
    × Γ ; α ⊢ₚ P
    × Γ ; β ⊢ₚ Q
inv-∥ (TP-Par p q) = _ , _ , ≼-refl ≈-refl , p , q
inv-∥ (TP-Weaken γ≤ p) =
  let _ , _ , γ≤′ , x = inv-∥ p in
  _ , _ , ≼-trans γ≤′ γ≤ , x

inv-ν : {Γ : Ctx n} → Γ ; γ ⊢ₚ ν B₁ B₂ P →
  ∃[ Γ₁ ] ∃[ Γ₂ ] ∃[ s ]
     BindCtx {sum B₁} s Γ₁
      × BindCtx {sum B₂} (dual s) Γ₂
      × (Γ₁ ⸴* Γ₂) ⸴* Γ ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                        ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                        ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* _)
                        ⊢ₚ P
inv-ν (TP-Res C C′ p) = _ , _ , _ , C , C′ , p
inv-ν (TP-Weaken γ≤ p) =
  let Γ₁ , Γ₂ , _ , C , C′ , p′ = inv-ν p in
  _ , _ , _ , C , C′ , TP-Weaken (≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves (Γ₁ ⸴* Γ₂)) γ≤)) p′

infixl 5 _⊢⋯ₚ_

_⊢⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ →
        {ϕ : m –[ K ]→ n} {σ : _} →
        Γ₁ ; γ ⊢ₚ P →
        ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ →
        Γ₂ ; γ 𝐂.⋯ σ ⊢ₚ P ⋯ₚ ϕ
TP-Expr e ⊢⋯ₚ ⊢ϕ = TP-Expr (e ⊢⋯ ⊢ϕ)
TP-Par p q ⊢⋯ₚ ⊢ϕ = TP-Par (p ⊢⋯ₚ ⊢ϕ) (q ⊢⋯ₚ ⊢ϕ)
_⊢⋯ₚ_ {γ = γ} {σ = σ} (TP-Res {B₁ = B₁} {B₂ = B₂} C C′ p) ⊢ϕ =
  TP-Res C C′
    $ subst-γₚ (cong₂ _∥_ (cong₂ _∥_
        (𝐂.fusion (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ _) (σ 𝐂.↑* (sum B₁ + sum B₂))
          ■ 𝐂.⋯-cong (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ (sum B₁ + sum B₂) σ)
          ■ 𝐂.conv-⋯ᵣₛ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)))
        (𝐂.fusion (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ _) (σ 𝐂.↑* (sum B₁ + sum B₂))
          ■ 𝐂.⋯-cong (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ (sum B₁ + sum B₂) σ)
          ■ 𝐂.conv-⋯ᵣₛ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁))))
        (sym (𝐂.⋯-↑*-wk γ σ (sum B₁ + sum B₂))))
    $ p ⊢⋯ₚ ⊢↑* _ ⊢ϕ
TP-Weaken γ≤ p ⊢⋯ₚ ⊢ϕ = TP-Weaken (𝐂.≼-⋯ (&-unr ⊢ϕ) γ≤) (p ⊢⋯ₚ ⊢ϕ)

postulate
  _⊢⋯ₚ⁻¹_ : {ϕ : m →ᵣ n} {σ : _} → Γ₂ ; γ ⊢ₚ P ⋯ₚ ϕ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
    ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ₚ P

{-
_⊢⋯ₚ⁻¹_ {P = ⟪ e ⟫} p ⊢ϕ
  with ⊢e ← inv-⟪⟫ p
  with γ′ , ≤γ , ⊢e′ ← ⊢e ⊢⋯⁻¹ ⊢ϕ
  = γ′ , ≤γ , TP-Expr ⊢e′
_⊢⋯ₚ⁻¹_ {P = P ∥ P₁} p ⊢ϕ
  with α , β , ≤ , p₁ , p₂ ← inv-∥ p
  with α′ , ≤α , p₁′ ← p₁ ⊢⋯ₚ⁻¹ ⊢ϕ
  with β′ , ≤β , p₂′ ← p₂ ⊢⋯ₚ⁻¹ ⊢ϕ
  = α′ ∥ β′ , ≼-trans (≼-cong-∥ ≤α ≤β) ≤ , TP-Par p₁′ p₂′
_⊢⋯ₚ⁻¹_ {γ = γ} {P = ν B₁ B₂ P} p ⊢ϕ
  with Γ₁ , Γ₂ , _ , C , C′ , p′ ← inv-ν p
  with γ′ , ≤γ , p″ ← p′ ⊢⋯ₚ⁻¹ ⊢↑* (Γ₁ ⸴* Γ₂) ⊢ϕ
  = {!γ!} , {!!} , TP-Res C C′ (TP-Weaken {!≤γ!} p″)
-}

postulate
  ⊢-≋ : ChanCx Γ → P ≋ Q → Γ ; γ ⊢ₚ P → Γ ; γ ⊢ₚ Q

{-
⊢-≋ Γ-S refl     = id
⊢-≋ Γ-S (x ◅ xs) = ⊢-≋ Γ-S xs ∘ go Γ-S x where
  go : ChanCx Γ → SymClosure _≋′_ P Q → Γ ; γ ⊢ₚ P → Γ ; γ ⊢ₚ Q
  go Γ-S (fwd ∥-comm′) p₀
    with _ , _ , γ≤ , p , q ← inv-∥ p₀
    = TP-Weaken (≼-respˡ-≈ 𝐂.∥-comm γ≤) (TP-Par q p)
  go Γ-S (fwd ∥-assoc′) p₀
    with γ₁ , γ′ , ≤₁ , p₁ , p′ ← inv-∥ p₀
    with γ₂ , γ₃ , ≤₂ , p₂ , p₃ ← inv-∥ p′
    = let open ≼-Reasoning in
      let ≤γ = begin (γ₁ ∥ γ₂) ∥ γ₃  ≈⟨ 𝐂.∥-assoc ⟩
                     γ₁ ∥ (γ₂ ∥ γ₃)  ≲⟨ ≼-cong-∥ (≼-refl refl) ≤₂ ⟩
                     γ₁ ∥ γ′         ≲⟨ ≤₁ ⟩
                     _               ∎
      in TP-Weaken ≤γ (TP-Par (TP-Par p₁ p₂) p₃)
  go Γ-S (fwd ∥-unit′) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    with _ , []≤  ← inv-`⊤ Γ-S V-K (inv-⟪⟫ p)
    = let open ≼-Reasoning in
      let ≤γ = begin γ₂       ≈⟨ 𝐂.∥-unit₁ ⟨
                     [] ∥ γ₂  ≲⟨ ≼-cong-∥ []≤ (≼-refl refl) ⟩
                     γ₁ ∥ γ₂  ≲⟨ ≤γ ⟩
                     _        ∎
      in TP-Weaken ≤γ q
  go {n} {γ = γ} Γ-S (fwd (ν-swap′ {B₁ = B₁} {B₂})) p₀
    with Γ₁ , Γ₂ , _ , C , C′ , p ← inv-ν p₀ =
    let open ≡-Reasoning in
    let eq₁ =
          structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ₛ `_ ∘ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ 𝐂.⋯-congᶜ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n) (λ _ → refl) ⟩
          structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ (cong (𝐂._⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)) (𝐂.fusion (structBinder B₂) _ _) ■ 𝐂.fusion (structBinder B₂) _ _) ⟩
          structBinder B₂ 𝐂.⋯ᵣ (𝐂.wkˡ (sum B₁) ·ₖ 𝐂.wkʳ n) ·ₖ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ 𝐂.⋯-cong (structBinder B₂) (𝐂.wkˡ-swap≗wkʳ (sum B₁) (sum B₂)) ⟩
          structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) ·ₖ 𝐂.wkʳ n
            ≡⟨ 𝐂.fusion (structBinder B₂) _ _ ⟨
          structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n ∎
        eq₂ =
          structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ₛ `_ ∘ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ 𝐂.⋯-congᶜ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n) (λ _ → refl) ⟩
          structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ (cong (𝐂._⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)) (𝐂.fusion (structBinder B₁) _ _) ■ 𝐂.fusion (structBinder B₁) _ _) ⟩
          structBinder B₁ 𝐂.⋯ᵣ (𝐂.wkʳ (sum B₂) ·ₖ 𝐂.wkʳ n) ·ₖ 𝐂.swapᵣ (sum B₁) (sum B₂)
            ≡⟨ 𝐂.⋯-cong (structBinder B₁) (𝐂.wkʳ-swap≗wkˡ (sum B₁) (sum B₂)) ⟩
          structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₂) ·ₖ 𝐂.wkʳ n
            ≡⟨ 𝐂.fusion (structBinder B₁) _ _ ⟨
          structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n ∎
        eq = 𝐂.∥-cong
               (≈-trans 𝐂.∥-comm (𝐂.∥-cong (≈-reflexive eq₁) (≈-reflexive eq₂)))
               (≈-reflexive (𝐂.conv-⋯ᵣₛ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ■ 𝐂.weaken*-swap-⋯ γ (sum B₁) (sum B₂)))
    in TP-Res C′ C $ TP-Weaken (≼-refl eq) $ p ⊢⋯ₚ ⊢swapᵣ Γ₁ Γ₂
  go Γ-S (fwd ν-comm′) p₀
    with Γ₁ , Γ₂ , _ , X , X′ , pˣ ← inv-ν p₀
    with Γ₃ , Γ₄ , _ , Y , Y′ , pʸ ← inv-ν pˣ
    = let
      open ≈-Reasoning
      eq = ≈-trans (≈-sym 𝐂.∥-assoc)
             $ ≈-trans (𝐂.∥-cong 𝐂.∥-comm ≈-refl)
             $ ≈-trans (𝐂.∥-cong (𝐂.∥-cong (𝐂.∥-cong {!!} {!!}) (𝐂.∥-cong {!!} {!!})) {!!})
             𝐂.∥-assoc
    in TP-Res Y Y′ $ TP-Res X X′ $ TP-Weaken (≼-refl eq) $ pʸ ⊢⋯ₚ ⊢assocSwapᵣ (Γ₃ ⸴* Γ₄) (Γ₁ ⸴* Γ₂)
  go {γ = γ} Γ-S (fwd (ν-ext′ {B₁ = B₁} {B₂})) p₀
    with γ₁ , γ₂ , ≤γ , p₁ , p′ ← inv-∥ p₀
    with Γ₁ , Γ₂ , _ , C , C′ , p₂ ← inv-ν p′
    = let
      open ≼-Reasoning
      ≤ = begin
            (γ₁ 𝐂.⋯ₛ 𝐂.weaken* (sum B₁ + sum B₂))
              ∥ ((structBinder B₁ 𝐂.⋯ 𝐂.wkʳ (sum B₂) 𝐂.⋯ 𝐂.wkʳ _)
                   ∥ (structBinder B₂ 𝐂.⋯ 𝐂.wkˡ (sum B₁) 𝐂.⋯ 𝐂.wkʳ _)
                   ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≡⟨ cong (_∥ _) (𝐂.⋯-congᶜ ⦃ 𝐂.Kₛ ⦄ ⦃ 𝐂.Kᵣ ⦄ γ₁ λ y → 𝐂.weaken*~wkˡ _ y ■ cong `_ (sym (𝐂.weaken*~wkˡ _ y))) ⟩
            (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
             ∥ ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≈⟨ 𝐂.∥-assoc ⟨
            (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
             ∥ ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _))
             ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ≈⟨ 𝐂.∥-cong 𝐂.∥-comm ≈-refl ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
              ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ≈⟨ 𝐂.∥-assoc ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ ((γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves (Γ₁ ⸴* Γ₂)) ≤γ) ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ∎
    in TP-Res C C′ $ TP-Weaken ≤ $ TP-Par (p₁ ⊢⋯ₚ ⊢weaken* _ _) p₂
  go Γ-S (fwd (∥-cong′ eq)) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    = TP-Weaken ≤γ (TP-Par (go Γ-S (fwd eq) p) q)
  go Γ-S (fwd (ν-cong′ eq)) p₀
    with _ , _ , _ , C , C′ , p ← inv-ν p₀
    = TP-Res C C′ (go (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) (fwd eq) p)
  go Γ-S (bwd ∥-comm′) p₀
    with _ , _ , γ≤ , p , q ← inv-∥ p₀
    = TP-Weaken (≼-respˡ-≈ 𝐂.∥-comm γ≤) (TP-Par q p)
  go Γ-S (bwd ∥-assoc′) p₀
    with γ′ , γ₃ , ≤₁ , p′ , p₃ ← inv-∥ p₀
    with γ₁ , γ₂ , ≤₂ , p₁ , p₂ ← inv-∥ p′
    = let open ≼-Reasoning in
      let ≤γ = begin γ₁ ∥ (γ₂ ∥ γ₃)  ≈⟨ 𝐂.∥-assoc ⟨
                     (γ₁ ∥ γ₂) ∥ γ₃  ≲⟨ ≼-cong-∥ ≤₂ (≼-refl refl) ⟩
                     γ′ ∥ γ₃         ≲⟨ ≤₁ ⟩
                     _               ∎
      in TP-Weaken ≤γ (TP-Par p₁ (TP-Par p₂ p₃))
  go Γ-S (bwd ∥-unit′) p₀ = TP-Weaken (≼-refl 𝐂.∥-unit₁) (TP-Par (TP-Expr (T-Conv `⊤ ℙ≤ϵ (T-Const `unit))) p₀)
  go Γ-S (bwd ν-swap′) p₀ = {!!}
  go Γ-S (bwd ν-comm′) p₀ = {!!}
  go Γ-S (bwd (ν-ext′ {B₁ = B₁} {B₂})) p₀
    with Γ₁ , Γ₂ , _ , C , C′ , p′ ← inv-ν p₀
    with γ₁ , γ₂ , ≤ , p₁ , p₂ ← inv-∥ p′
    with γ₁′ , γ₁≡ , p₁′ ← p₁ ⊢⋯ₚ⁻¹ ⊢weaken* (Γ₁ ⸴* Γ₂) _
    = TP-Weaken {!≤γ!} $ TP-Par p₁′ (TP-Res C C′ (TP-Weaken {!!} p₂))
  go Γ-S (bwd (∥-cong′ eq)) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    = TP-Weaken ≤γ (TP-Par (go Γ-S (bwd eq) p) q)
  go Γ-S (bwd (ν-cong′ eq)) p₀
    with _ , _ , _ , C , C′ , p ← inv-ν p₀
    = TP-Res C C′ (go (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) (bwd eq) p)
-}
