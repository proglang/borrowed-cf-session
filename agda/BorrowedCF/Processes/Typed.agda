module BorrowedCF.Processes.Typed where

open import Data.Fin.Subset using (_⊆_)
open import Data.Fin.Subset.Properties using (x∈p∪q⁻)
open import Data.List.Relation.Unary.All as Allᴸ using ([]; _∷_) renaming (All to Allᴸ)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Relation.Unary.All as Allⱽ using ([]; _∷_) renaming (All to Allⱽ)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd; symmetric)

import Data.Vec.Relation.Unary.All.Properties as Allⱽ
import Data.List.Relation.Unary.All.Properties as Allᴸ

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Terms.DescendK
open import BorrowedCF.Terms.SubstitutionInversion
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomSnoc using (atomKind≢⇒≄-;ʳ)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)

open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions using (inv-`⊤)

open Nat using (_<_; z<s; _≤_; z≤n; s≤s; s≤s⁻¹)
open Nat.Variables
open Fin.Patterns

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
open import BorrowedCF.Context.Domain using (dom)
import BorrowedCF.Context.Substitution as 𝐂

structNSeq : ∀ m → Struct m
structNSeq zero    = []
structNSeq (suc m) = ` zero ; 𝐂.wk (structNSeq m)

structBinder : (B : BindGroup) → Struct (sum B)
structBinder [] = []
structBinder (b ∷ B) = (structNSeq b 𝐂.⋯ᵣ 𝐂.wkʳ (sum B)) ∥ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ b)

data BindCtx′ (s : 𝕊 0) : Ctx n → Set where
  nil : Skips s → BindCtx′ s []
  cons : ∀ (s₁ s₂ : 𝕊 0) →
    (¬skips : ¬ Skips s) →
    (s-split : s₁ ; s₂ ≃ s) →
    BindCtx′ s₂ Γ → BindCtx′ s (⟨ s₁ ⟩ ∷ Γ)

data BindCtx (s : 𝕊 0) : (B : BindGroup) → Ctx (sum B) → Set where
  last :
    BindCtx′ s Γ →
    --------------------------
    BindCtx s L.[ n ] Γ

  cons-ret/acq :
    (s₁ : 𝕊 0) {s₂ : 𝕊 0} {Γ₁ : Ctx n} {Γ₂ : Ctx (sum B)} →
    (s≃ : s₁ ; s₂ ≃ s) →
    BindCtx′ (s₁ ; ret) Γ₁ →
    BindCtx  (acq ; s₂) B Γ₂ →
    ----------------------------
    BindCtx s (n ∷ B) (Γ₁ ⸴* Γ₂)

  cons-acq :
    BindCtx (acq ; s) B Γ →
    -----------------------
    BindCtx s (0 ∷ B) Γ

bindCtx′⇒chanCtx : BindCtx′ s Γ → ChanCx Γ
bindCtx′⇒chanCtx (nil x) = []
bindCtx′⇒chanCtx (cons s₁ s₂ ¬skips s-split b) = (_ , refl) ∷ bindCtx′⇒chanCtx b

bindCtx⇒chanCtx : ∀ {B Γ} → BindCtx s B Γ → ChanCx Γ
bindCtx⇒chanCtx (last x) = bindCtx′⇒chanCtx x
bindCtx⇒chanCtx (cons-ret/acq s₁ s≃ x C) = Allⱽ.++⁺ (bindCtx′⇒chanCtx x) (bindCtx⇒chanCtx C)
bindCtx⇒chanCtx (cons-acq C) = bindCtx⇒chanCtx C

bindCtx-B≢[] : ¬ BindCtx s [] Γ
bindCtx-B≢[] ()

bindCtx′-≃ : s₁ ≃ s₂ → BindCtx′ s₁ Γ → BindCtx′ s₂ Γ
bindCtx′-≃ eq (nil x) = nil (≃-skips eq x)
bindCtx′-≃ eq (cons _ _ ¬skips s≃ C) = cons _ _ (¬skips ∘ ≃-skips (≃-sym eq)) (≃-trans s≃ eq) C

bindCtx-≃ : s₁ ≃ s₂ → BindCtx s₁ B Γ → BindCtx s₂ B Γ
bindCtx-≃ eq (last x) = last (bindCtx′-≃ eq x)
bindCtx-≃ eq (cons-ret/acq _ s≃ x C) = cons-ret/acq _ (≃-trans s≃ eq) x C
bindCtx-≃ eq (cons-acq C) = cons-acq (bindCtx-≃ (≃-; refl eq) C)

bindCtx-inv-cons : ∀ {b Γ} → .(0 < L.length B) → BindCtx s (b ∷ B) Γ →
  ∃[ s₁ ] ∃[ s₂ ] ∃[ Γ₁ ] ∃[ Γ₂ ]
    s₁ ; s₂ ≃ s
      × Γ₁ ⸴* Γ₂ ≡ Γ
      × BindCtx′ (s₁ ; ret) Γ₁
      × BindCtx (acq ; s₂) B Γ₂
  ⊎
  Σ[ b≡0 ∈ b ≡ 0 ] BindCtx (acq ; s) B (V.drop b Γ)
bindCtx-inv-cons 0< (cons-ret/acq s₁ s≃ x C) = inj₁ (s₁ , _ , _ , _ , s≃ , refl , x , C)
bindCtx-inv-cons {Γ = Γ} 0< (cons-acq C) = inj₂ (refl , C)

bindCtx-inv-msg : s′ ≃ msg p T′ → BindCtx s (suc n ∷ B) (⟨ s′ ⟩ ∷ Γ) →
  ∃[ s₂ ] msg p T′ ; s₂ ≃ s × BindCtx s₂ (n ∷ B) Γ
bindCtx-inv-msg {s′} {Γ = Γ} isMsg C with ⟨ s′ ⟩ ∷ Γ in Γ-eq
bindCtx-inv-msg isMsg (last (cons s₁ s₂ ¬skips s-split x)) | Γ′
  with (refl , refl) ← V.∷-injective Γ-eq =
  s₂ , ≃-trans (≃-; ((≃-sym isMsg)) refl) s-split , last x
bindCtx-inv-msg isMsg (cons-ret/acq s′ {s″} s≃ (cons s₁ s₂ ¬skips s-split x) C) | Γ′
  with (refl , refl) ← V.∷-injective Γ-eq
  with atom-;-unsnoc ret s-split
... | inj₂ (s₂′ , s₁s₂′ , s₂′ret) =
  (s₂′ ; s″)
    , ≃-trans (≃-trans (≃-sym ≃-assoc-;) (≃-; (≃-trans (≃-; (≃-sym isMsg) refl) s₁s₂′) refl)) s≃
    , cons-ret/acq s₂′ refl (bindCtx′-≃ (≃-sym s₂′ret) x) C
... | inj₁ Ss₂ = ⊥-elim $ atomKind≢⇒≄-;ʳ msg ret (λ()) $
  ≃-trans ≃-skipˡ
    $ ≃-trans (≃-sym ≃-skipʳ)
    $ ≃-trans (≃-; (≃-sym isMsg) (skips⇒skip≃ Ss₂)) s-split

⊢ᴮ_ : Pred BindGroup _
⊢ᴮ B = Allᴸ NonZero (L.drop 1 B)

⊢ᴮ-lsplit : ∀ B₁ m {n} {B₂} → ⊢ᴮ (B₁ ++ (m + 1 + n) ∷ B₂) → ⊢ᴮ (B₁ ++ (m + 2 + n) ∷ B₂)
⊢ᴮ-lsplit [] m x = x
⊢ᴮ-lsplit (_ ∷ B₁) m {n} x with y ∷ x′ ← Allᴸ.++⁻ʳ B₁ x =
  let eq = +-assoc (suc m) 1 n ■ sym (+-suc m (suc n)) ■ sym (+-assoc m 2 n) in
  Allᴸ.++⁺ (Allᴸ.++⁻ˡ B₁ x) (Nat.>-nonZero (subst (0 Nat.<_) eq (Nat.m<n⇒m<1+n (Nat.>-nonZero⁻¹ _ ⦃ y ⦄))) ∷ x′)

⊢ᴮ-rsplit : ∀ B₁ {B₂} → ⊢ᴮ (B₁ ++ suc n ∷ B₂) → ⊢ᴮ (B₁ ++ 1 ∷ suc n ∷ B₂)
⊢ᴮ-rsplit [] x = _ ∷ x
⊢ᴮ-rsplit (_ ∷ B₁) x = Allᴸ.++⁺ (Allᴸ.++⁻ˡ B₁ x) (_ ∷ Allᴸ.++⁻ʳ B₁ x)

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
    ∀ (N : New s) (p : Pol) (⊢B₁ : ⊢ᴮ B₁) (⊢B₂ : ⊢ᴮ B₂) {Γ₁ Γ₂} →
      (C  : BindCtx (s      ; end p)           B₁ Γ₁) →
      (C′ : BindCtx (dual s ; end (dualPol p)) B₂ Γ₂) →
      (Γ₁ ⸴* Γ₂) ⸴* Γ ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n) -- ` 0F
                      ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n) -- ` 1F
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
  ∃[ Γ₁ ] ∃[ Γ₂ ] ∃[ s ] ∃[ p ]
    New s × ⊢ᴮ B₁ × ⊢ᴮ B₂
      × BindCtx (s      ; end p)           B₁ Γ₁
      × BindCtx (dual s ; end (dualPol p)) B₂ Γ₂
      × (Γ₁ ⸴* Γ₂) ⸴* Γ ; (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                        ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
                        ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* _)
                        ⊢ₚ P
inv-ν (TP-Res N p ⊢B₁ ⊢B₂ C C′ P) = _ , _ , _ , _ , N , ⊢B₁ , ⊢B₂ , C , C′ , P
inv-ν {Γ = Γ} (TP-Weaken γ≤ p) =
  let Γ₁ , Γ₂ , _ , _ , N , ⊢B₁ , ⊢B₂ , C , C′ , p′ = inv-ν p in
  _ , _ , _ , _ , N , ⊢B₁ , ⊢B₂ , C , C′
    , TP-Weaken (≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.⇔→⇒  ⦃ 𝐂.Kᵣ ⦄ {Γ} (𝐂.wk*-⇔ ⦃ 𝐂.Kᵣ ⦄ (Γ₁ ⸴* Γ₂))) γ≤)) p′

infixl 5 _⊢⋯ₚ_

_⊢⋯ₚ_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ →
        {ϕ : m –[ K ]→ n} {σ : _} →
        Γ₁ ; γ ⊢ₚ P →
        ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ →
        Γ₂ ; γ 𝐂.⋯ σ ⊢ₚ P ⋯ₚ ϕ
TP-Expr e ⊢⋯ₚ ⊢ϕ = TP-Expr (e ⊢⋯ ⊢ϕ)
TP-Par p q ⊢⋯ₚ ⊢ϕ = TP-Par (p ⊢⋯ₚ ⊢ϕ) (q ⊢⋯ₚ ⊢ϕ)
_⊢⋯ₚ_ {γ = γ} {σ = σ} (TP-Res {B₁ = B₁} {B₂ = B₂} N p ⊢B₁ ⊢B₂ C C′ P) ⊢ϕ =
  TP-Res N p ⊢B₁ ⊢B₂ C C′
    $ subst-γₚ (cong₂ _∥_ (cong₂ _∥_
        (𝐂.fusion (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ _) (σ 𝐂.↑* (sum B₁ + sum B₂))
          ■ 𝐂.⋯-cong (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ (sum B₁ + sum B₂) σ)
          ■ 𝐂.conv-⋯ᵣₛ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)))
        (𝐂.fusion (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ _) (σ 𝐂.↑* (sum B₁ + sum B₂))
          ■ 𝐂.⋯-cong (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ (sum B₁ + sum B₂) σ)
          ■ 𝐂.conv-⋯ᵣₛ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁))))
        (sym (𝐂.⋯-↑*-wk γ σ (sum B₁ + sum B₂))))
    $ P ⊢⋯ₚ ⊢↑* _ ⊢ϕ
TP-Weaken γ≤ p ⊢⋯ₚ ⊢ϕ = TP-Weaken (𝐂.≼-⋯ (TKit.&-⇒ ⊢ϕ) γ≤) (p ⊢⋯ₚ ⊢ϕ)

lift-disg* : (k : ℕ) {ρ : m →ᵣ n} {σ : m 𝐂.→ₛ n} →
  (∀ x → ` ρ x ≡ σ x) →
  (∀ x → ` (ρ 𝐂.↑* k) x ≡ (σ 𝐂.↑* k) x)
lift-disg* zero    eq = eq
lift-disg* (suc k) {ρ} {σ} eq = lift-disg (lift-disg* k eq)

brₛ↑* : (k : ℕ) {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (k + m)) →
  γ 𝐂.⋯ᵣ ϕ 𝐂.↑* k ≡ γ 𝐂.⋯ σ 𝐂.↑* k
brₛ↑* k ⊢ϕ γ = sym (𝐂.conv-⋯ᵣₛ γ) ■ 𝐂.⋯-cong γ (lift-disg* k (⊢ren-ϕ≗σ ⊢ϕ))

infixl 5 _⊢⋯ₚ⁻¹_/_

_⊢⋯ₚ⁻¹_/_ : ∀ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {γ} {ϕ : m →ᵣ n} {σ} →
  Γ₂ ; γ ⊢ₚ P ⋯ₚ ϕ →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  𝐂.Inj ϕ →
  ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ₚ P
_⊢⋯ₚ⁻¹_/_ {P = ⟪ e ⟫} p ⊢ϕ inj =
  let γ′ , ≤γ , ⊢e′ = ⊢⋯⁻¹ inj (inv-⟪⟫ p) ⊢ϕ
  in γ′ , ≤γ , TP-Expr ⊢e′
_⊢⋯ₚ⁻¹_/_ {P = P ∥ Q} p ⊢ϕ inj =
  let α , β , ≤ , p₁ , p₂ = inv-∥ p
      α′ , ≤α , p₁′ = p₁ ⊢⋯ₚ⁻¹ ⊢ϕ / inj
      β′ , ≤β , p₂′ = p₂ ⊢⋯ₚ⁻¹ ⊢ϕ / inj
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≤α ≤β) ≤ , TP-Par p₁′ p₂′
_⊢⋯ₚ⁻¹_/_ {n = n} {P = ν B₁ B₂ P} p ⊢ϕ inj =
  let Γ₁ᵥ , Γ₂ᵥ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p′ = inv-ν p
      k = sum B₁ + sum B₂
      Δ = Γ₁ᵥ ⸴* Γ₂ᵥ
      Fr′ = (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
          ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n)
      γ′ , ≤γ , p″ = p′ ⊢⋯ₚ⁻¹ ⊢↑* Δ ⊢ϕ / ↑*-inj k inj
      ≤γᵣ = subst (_ ∶_≼ _) (sym (brₛ↑* k ⊢ϕ γ′)) ≤γ
      Frinv = cong₂ _∥_
               (𝐂.fusion (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) _ _
                 ■ 𝐂.⋯-cong (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ k _))
               (𝐂.fusion (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) _ _
                 ■ 𝐂.⋯-cong (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ-cancels-↑* ⦃ 𝐂.Kᵣ ⦄ k _))
      Frdom : dom Fr′ ⊆ fresh n k
      Frdom z∈ = [ dom⋯wkʳ⊆fresh _ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂))
                 , dom⋯wkʳ⊆fresh _ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁))
                 ]′
                 (x∈p∪q⁻ _ _ z∈)
      γr , part1 , part2 = descend-absK k Δ inj (⊢ren-ϕ⇔ ⊢ϕ) 𝟙 _ _ γ′ _ Frinv Frdom ≤γᵣ
  in γr
   , ≼-respˡ-≈ (≈-reflexive (brₛ ⊢ϕ γr)) part2
   , TP-Res N pol ⊢B₁ ⊢B₂ C C′ (TP-Weaken part1 p″)
