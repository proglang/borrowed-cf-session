module BorrowedCF.Context.Substitution where

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext

open import BorrowedCF.FinKits as Kits hiding (Syntax)

open Nat.Variables
open Variables

open module Syntax = Kits.Syntax record
  { Tm = Struct
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Tm; `_; Traversal)
  renaming (id to idₖ)
  public

infixl 5 _⋯_

_⋯_ : ⦃ K : Kit 𝓕 ⦄ → Struct m → m –[ K ]→ n → Struct n
` x   ⋯ σ = `/id (σ x)
[]    ⋯ σ = []
α ∥ β ⋯ σ = (α ⋯ σ) ∥ (β ⋯ σ)
α ; β ⋯ σ = (α ⋯ σ) ; (β ⋯ σ)

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (γ : Struct m) {σ₁ σ₂ : m –[ K ]→ n} → σ₁ ≗ σ₂ → γ ⋯ σ₁ ≡ γ ⋯ σ₂
⋯-cong (` x)    eq = cong `/id (eq x)
⋯-cong []       eq = refl
⋯-cong (x ∥ x₁) eq = cong₂ _∥_ (⋯-cong x eq) (⋯-cong x₁ eq)
⋯-cong (x ; x₁) eq = cong₂ _;_ (⋯-cong x eq) (⋯-cong x₁ eq)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (γ : Struct n) {σ : n –[ K ]→ n} → σ ≗ idₖ → γ ⋯ σ ≡ γ
⋯-id (` x)    eq rewrite eq x = `/`-is-` x
⋯-id []       eq = refl
⋯-id (x ∥ x₁) eq = cong₂ _∥_ (⋯-id x eq) (⋯-id x₁ eq)
⋯-id (x ; x₁) eq = cong₂ _;_ (⋯-id x eq) (⋯-id x₁ eq)

open module Traversal = Syntax.Traversal record
  { _⋯_    = _⋯_
  ; ⋯-var  = λ x ϕ → refl
  ; ⋯-id   = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-var; ⋯-id; ⋯-cong)
  public

fusion :  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄
          ⦃ C : CKit K₁ K₂ K ⦄ (γ : Struct n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
          γ ⋯ ϕ₁ ⋯ ϕ₂ ≡ γ ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x)   ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion []      ϕ₁ ϕ₂ = refl
fusion (α ∥ β) ϕ₁ ϕ₂ = cong₂ _∥_ (fusion α _ _) (fusion β _ _)
fusion (α ; β) ϕ₁ ϕ₂ = cong₂ _;_ (fusion α _ _) (fusion β _ _)

open CTraversal record { fusion = fusion } hiding (fusion) public

Inj : m →ᵣ n → Set
Inj = Injective _≡_ _≡_

∥-injective : α₁ ∥ α₂ ≡ β₁ ∥ β₂ → α₁ ≡ β₁ × α₂ ≡ β₂
∥-injective refl = refl , refl

;-injective : α₁ ; α₂ ≡ β₁ ; β₂ → α₁ ≡ β₁ × α₂ ≡ β₂
;-injective refl = refl , refl

⋯-injective : {ϕ : m →ᵣ n} → Inj ϕ → α ⋯ ϕ ≡ β ⋯ ϕ → α ≡ β
⋯-injective {α = ` x} {` y} ϕ-inj eq = cong `_ (ϕ-inj (`-injective eq))
⋯-injective {α = []} {[]} ϕ-inj eq = refl
⋯-injective {α = _ ∥ _} {_ ∥ _} ϕ-inj eq = cong₂ _∥_ (⋯-injective ϕ-inj (∥-injective eq .proj₁)) (⋯-injective ϕ-inj (∥-injective eq .proj₂))
⋯-injective {α = _ ; _} {_ ; _} ϕ-inj eq = cong₂ _;_ (⋯-injective ϕ-inj (;-injective eq .proj₁)) (⋯-injective ϕ-inj (;-injective eq .proj₂))

_Preserves[_]_⇒_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
σ Preserves[ P ] Γ₁ ⇒ Γ₂ = ∀ {x} → P (Γ₁ x) → AllCx P Γ₂ (`/id (σ x))

_Preserves[_]_⇐_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
σ Preserves[ P ] Γ₁ ⇐ Γ₂ = ∀ {x} → AllCx P Γ₂ (`/id (σ x)) → P (Γ₁ x)

module _ {ℓ} {P : Pred 𝕋 ℓ} where
  allCx-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇒ Γ₂ → AllCx P Γ₁ γ → AllCx P Γ₂ (γ ⋯ ϕ)
  allCx-⋯ P⇒ΠP []      = []
  allCx-⋯ P⇒ΠP (x ∥ y) = allCx-⋯ P⇒ΠP x ∥ allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (x ; y) = allCx-⋯ P⇒ΠP x ; allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (` Px)  = P⇒ΠP Px

  allCx-⋯⁻¹ : {ϕ : m →ᵣ n} → ϕ Preserves[ P ] Γ₁ ⇐ Γ₂ → AllCx P Γ₂ (γ ⋯ ϕ) → AllCx P Γ₁ γ
  allCx-⋯⁻¹ {γ = ` _} Pϕ⇒P x = ` Pϕ⇒P x
  allCx-⋯⁻¹ {γ = []} Pϕ⇒P x = []
  allCx-⋯⁻¹ {γ = α ∥ β} Pϕ⇒P (x ∥ y) = allCx-⋯⁻¹ Pϕ⇒P x ∥ allCx-⋯⁻¹ Pϕ⇒P y
  allCx-⋯⁻¹ {γ = α ; β} Pϕ⇒P (x ; y) = allCx-⋯⁻¹ Pϕ⇒P x ; allCx-⋯⁻¹ Pϕ⇒P y

  wk-preserves : {Γ : Ctx n} → weakenᵣ Preserves[ P ] Γ ⇒ (T ⸴ Γ)
  wk-preserves px = ` px

  allCx-wk : {Γ : Ctx n} → AllCx P Γ γ → AllCx P (T ⸴ Γ) (wk γ)
  allCx-wk = allCx-⋯ wk-preserves

  wk*-preserves : (Γ : Ctx m) {Γ′ : Ctx n} → weaken* ⦃ Kᵣ ⦄ m Preserves[ P ] Γ′ ⇒ (Γ ⸴* Γ′)
  wk*-preserves {zero}  Γ px = ` px
  wk*-preserves {suc m} Γ px = allCx-≗ ⸴-⸴*-cons (allCx-wk (wk*-preserves (Γ ∘ suc) px))

  ↑-preserves : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇒ Γ₂ → (ϕ ↑) Preserves[ P ] (T ⸴ Γ₁) ⇒ (T ⸴ Γ₂)
  ↑-preserves ⦃ K ⦄ p⇒ {zero}  px = subst (AllCx P _) (sym (`/`-is-` ⦃ K ⦄ zero)) (` px)
  ↑-preserves ⦃ K ⦄ p⇒ {suc x} px = subst (AllCx P _) (wk-`/id _) (allCx-wk (p⇒ px))

≈′-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ →
  ϕ Preserves[ Mobile ] Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≈′ β →
  Γ₂ ∶ α ⋯ ϕ ≈′ β ⋯ ϕ
≈′-⋯ σ-unr σ-mob ;′-assoc = ;′-assoc
≈′-⋯ σ-unr σ-mob (;′-cong₁ x) = ;′-cong₁ (≈′-⋯ σ-unr σ-mob x)
≈′-⋯ σ-unr σ-mob (;′-cong₂ x) = ;′-cong₂ (≈′-⋯ σ-unr σ-mob x)
≈′-⋯ σ-unr σ-mob ∥′-unit = ∥′-unit
≈′-⋯ σ-unr σ-mob ∥′-assoc = ∥′-assoc
≈′-⋯ σ-unr σ-mob ∥′-comm = ∥′-comm
≈′-⋯ σ-unr σ-mob (∥′-cong₁ x) = ∥′-cong₁ (≈′-⋯ σ-unr σ-mob x)
≈′-⋯ σ-unr σ-mob (∥′-dup U) = ∥′-dup (allCx-⋯ σ-unr U)
≈′-⋯ σ-unr σ-mob (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-⋯ σ-mob) (allCx-⋯ σ-mob) U)

≈-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ →
  ϕ Preserves[ Mobile ] Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≈ β →
  Γ₂ ∶ α ⋯ ϕ ≈ β ⋯ ϕ
≈-⋯ ϕ-unr ϕ-mob = Eq*.gmap _ (≈′-⋯ ϕ-unr ϕ-mob)

≈′-inv-[] : Γ ∶ α ∥ β ≈′ [] → Γ ∶ α ≈ [] × Γ ∶ β ≈ []
≈′-inv-[] ∥′-unit = refl , refl

∥′-unit⁻¹ : ∀ {x y} → Γ ∶ (` x) ∥ [] ≈′ (` y) → x ≡ y
∥′-unit⁻¹ ∥′-unit = refl

∥′-dup⁻¹ : ∀ {x y z} → Γ ∶ ` x ≈′ (` y) ∥ (` z) → x ≡ y × x ≡ z × Unr (Γ x)
∥′-dup⁻¹ (∥′-dup (` U)) = refl , refl , U

≈′-⋯⁻¹ : {ϕ : m →ᵣ n} →
  Inj ϕ →
  ϕ Preserves[ Unr ] Γ₁ ⇐ Γ₂ →
  ϕ Preserves[ Mobile ] Γ₁ ⇐ Γ₂ →
  Γ₂ ∶ α ⋯ ϕ ≈′ β ⋯ ϕ →
  Γ₁ ∶ α ≈′ β
≈′-⋯⁻¹ {α = α} {β} {ϕ = ϕ} inj-ϕ unr-ϕ mob-ϕ x with α ⋯ ϕ in eqᵃ | β ⋯ ϕ in eqᵇ

≈′-⋯⁻¹ {α = α₁ ; α₂} {β₁ ; β₂} inj-ϕ unr-ϕ mob-ϕ (;′-cong₁ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₂} {β₂} inj-ϕ (;-injective eqᵃ .proj₂ ■ sym (;-injective eqᵇ .proj₂))
  = ;′-cong₁ (≈′-⋯⁻¹ inj-ϕ unr-ϕ mob-ϕ (subst₂ (_ ∶_≈′_) (sym (;-injective eqᵃ .proj₁)) (sym (;-injective eqᵇ .proj₁)) x))

≈′-⋯⁻¹ {α = α₁ ; α₂} {β₁ ; β₂} inj-ϕ unr-ϕ mob-ϕ (;′-cong₂ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₁} {β₁} inj-ϕ (;-injective eqᵃ .proj₁ ■ sym (;-injective eqᵇ .proj₁))
  = ;′-cong₂ (≈′-⋯⁻¹ inj-ϕ unr-ϕ mob-ϕ (subst₂ (_ ∶_≈′_) (sym (;-injective eqᵃ .proj₂)) (sym (;-injective eqᵇ .proj₂)) x))

≈′-⋯⁻¹ {α = (α₁ ; β₁) ; γ₁} {α₂ ; (β₂ ; γ₂)} inj-ϕ unr-ϕ mob-ϕ ;′-assoc | ϕα | ϕβ
  with eqᵃ′ , refl ← ;-injective eqᵃ
  with refl , refl ← ;-injective eqᵃ′
  rewrite ⋯-injective {α = α₂} {α₁} inj-ϕ (;-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {β₁} inj-ϕ (;-injective (;-injective eqᵇ .proj₂) .proj₁)
  rewrite ⋯-injective {α = γ₂} {γ₁} inj-ϕ (;-injective (;-injective eqᵇ .proj₂) .proj₂)
  = ;′-assoc

≈′-⋯⁻¹ {α = α ∥ []} {β} inj-ϕ unr-ϕ mob-ϕ ∥′-unit | ϕα | ϕβ
  rewrite ⋯-injective {α = α} {β} inj-ϕ (∥-injective eqᵃ .proj₁ ■ sym eqᵇ)
  = ∥′-unit

≈′-⋯⁻¹ {α = (α₁ ∥ β₁) ∥ γ₁} {α₂ ∥ (β₂ ∥ γ₂)} inj-ϕ unr-ϕ mob-ϕ ∥′-assoc | ϕα | ϕβ
  with eqᵃ′ , refl ← ∥-injective eqᵃ
  with refl , refl ← ∥-injective eqᵃ′
  rewrite ⋯-injective {α = α₂} {α₁} inj-ϕ (∥-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {β₁} inj-ϕ (∥-injective (∥-injective eqᵇ .proj₂) .proj₁)
  rewrite ⋯-injective {α = γ₂} {γ₁} inj-ϕ (∥-injective (∥-injective eqᵇ .proj₂) .proj₂)
  = ∥′-assoc

≈′-⋯⁻¹ {α = α₁ ∥ α₂} {β₁ ∥ β₂} inj-ϕ unr-ϕ mob-ϕ ∥′-comm | ϕα | ϕβ
  using α₁≡α , α₂≡β ← ∥-injective eqᵃ
  using β₁≡β , β₂≡α ← ∥-injective eqᵇ
  rewrite ⋯-injective {α = α₁} {β₂} inj-ϕ (α₁≡α ■ sym β₂≡α)
  rewrite ⋯-injective {α = α₂} {β₁} inj-ϕ (α₂≡β ■ sym β₁≡β)
  = ∥′-comm

≈′-⋯⁻¹ {α = α₁ ∥ α₂} {β₁ ∥ β₂} inj-ϕ unr-ϕ mob-ϕ (∥′-cong₁ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₂} {β₂} inj-ϕ (∥-injective eqᵃ .proj₂ ■ sym (∥-injective eqᵇ .proj₂))
  = ∥′-cong₁ (≈′-⋯⁻¹ inj-ϕ unr-ϕ mob-ϕ (subst₂ (_ ∶_≈′_) (sym (∥-injective eqᵃ .proj₁)) (sym (∥-injective eqᵇ .proj₁)) x))

≈′-⋯⁻¹ {α = α} {β₁ ∥ β₂} {ϕ = ϕ} inj-ϕ unr-ϕ mob-ϕ (∥′-dup U) | ϕα | ϕβ
  rewrite sym eqᵃ
  rewrite ⋯-injective {α = β₁} {α} inj-ϕ (∥-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {α} inj-ϕ (∥-injective eqᵇ .proj₂)
  = ∥′-dup (allCx-⋯⁻¹ unr-ϕ U)

≈′-⋯⁻¹ {α = α₁ ∥ α₂} {β₁ ; β₂} {ϕ = ϕ} inj-ϕ unr-ϕ mob-ϕ (∥′-tm-; U) | ϕα | ϕβ
  with refl , refl ← ∥-injective eqᵃ
  rewrite ⋯-injective {α = β₁} {α₁} inj-ϕ (;-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {α₂} inj-ϕ (;-injective eqᵇ .proj₂)
  = ∥′-tm-; (Sum.map (allCx-⋯⁻¹ mob-ϕ) (allCx-⋯⁻¹ mob-ϕ) U)

-- ≈-⋯⁻¹ and ≼-⋯⁻¹ (inverse renaming for ≈ / ≼) are proven in
-- BorrowedCF.Context.Domain, which has the `dom` machinery they need.

≼-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ →
  ϕ Preserves[ Mobile ] Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≼ β →
  Γ₂ ∶ α ⋯ ϕ ≼ β ⋯ ϕ
≼-⋯ σ-unr σ-mob (≼-refl eq)    = ≼-refl (≈-⋯ σ-unr σ-mob eq)
≼-⋯ σ-unr σ-mob ≼-wk           = ≼-wk
≼-⋯ σ-unr σ-mob (≼-∅ U)        = ≼-∅ (allCx-⋯ σ-unr U)
≼-⋯ σ-unr σ-mob (≼-trans  x y) = ≼-trans (≼-⋯ σ-unr σ-mob x) (≼-⋯ σ-unr σ-mob y)
≼-⋯ σ-unr σ-mob (≼-cong-; x y) = ≼-cong-; (≼-⋯ σ-unr σ-mob x) (≼-⋯ σ-unr σ-mob y)
≼-⋯ σ-unr σ-mob (≼-cong-∥ x y) = ≼-cong-∥ (≼-⋯ σ-unr σ-mob x) (≼-⋯ σ-unr σ-mob y)


