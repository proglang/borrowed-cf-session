module BorrowedCF.Context.Substitution where

import Data.Vec.Functional as F
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext

open Nat.Variables
open Variables

_→ₛ_ : ℕ → ℕ → Set
m →ₛ n = 𝔽 m → Struct n

variable
  σ σ₁ σ₂ σ′ : m →ₛ n

idₛ : n →ₛ n
idₛ x = ` x

infixr 6 _∷ₛ_

_∷ₛ_ : Struct n → m →ₛ n → suc m →ₛ n
(α ∷ₛ σ) zero    = α
(α ∷ₛ σ) (suc x) = σ x

wk : Struct n → Struct (suc n)
wk (` x)   = ` suc x
wk []      = []
wk (α ∥ β) = wk α ∥ wk β
wk (α ; β) = wk α ; wk β

wkₛ : m →ₛ n → m →ₛ suc n
wkₛ σ x = wk (σ x)

weaken : n →ₛ suc n
weaken = wkₛ idₛ

_↑ : m →ₛ n → suc m →ₛ suc n
σ ↑ = ` zero ∷ₛ wkₛ σ

⦅_⦆ : Struct n → suc n →ₛ n
⦅ α ⦆ = α ∷ₛ idₛ

infixl 5 _⋯_

_⋯_ : Struct m → m →ₛ n → Struct n
` x   ⋯ σ = σ x
[]    ⋯ σ = []
α ∥ β ⋯ σ = (α ⋯ σ) ∥ (β ⋯ σ)
α ; β ⋯ σ = (α ⋯ σ) ; (β ⋯ σ)

cong-⋯ : σ₁ ≗ σ₂ → _⋯ σ₁ ≗ _⋯ σ₂
cong-⋯ eq (` x) = eq x
cong-⋯ eq [] = refl
cong-⋯ eq (x ∥ x₁) = cong₂ _∥_ (cong-⋯ eq x) (cong-⋯ eq x₁)
cong-⋯ eq (x ; x₁) = cong₂ _;_ (cong-⋯ eq x) (cong-⋯ eq x₁)

id-⋯ : σ ≗ idₛ → _⋯ σ ≗ id
id-⋯ eq (` x) = eq x
id-⋯ eq [] = refl
id-⋯ eq (x ∥ x₁) = cong₂ _∥_ (id-⋯ eq x) (id-⋯ eq x₁)
id-⋯ eq (x ; x₁) = cong₂ _;_ (id-⋯ eq x) (id-⋯ eq x₁)

weaken/wk : (γ : Struct n) → γ ⋯ weaken ≡ wk γ
weaken/wk (` x) = refl
weaken/wk [] = refl
weaken/wk (γ ∥ γ₁) = cong₂ _∥_ (weaken/wk γ) (weaken/wk γ₁)
weaken/wk (γ ; γ₁) = cong₂ _;_ (weaken/wk γ) (weaken/wk γ₁)

⋯-↑-weaken : (γ : Struct m) (σ : m →ₛ n) → γ ⋯ σ ⋯ weaken ≡ γ ⋯ weaken ⋯ σ ↑
⋯-↑-weaken (` x) σ = weaken/wk (σ x)
⋯-↑-weaken [] σ = refl
⋯-↑-weaken (α ∥ β) σ = cong₂ _∥_ (⋯-↑-weaken α σ) (⋯-↑-weaken β σ)
⋯-↑-weaken (α ; β) σ = cong₂ _;_ (⋯-↑-weaken α σ) (⋯-↑-weaken β σ)

⋯-↑-wk : (γ : Struct m) (σ : m →ₛ n) → wk (γ ⋯ σ) ≡ wk γ ⋯ σ ↑
⋯-↑-wk γ σ rewrite sym (weaken/wk γ) | sym (weaken/wk (γ ⋯ σ)) = ⋯-↑-weaken γ σ

_⋯-weaken-cancels-⦅_⦆ : (α : Struct n) (γ : Struct n) → α ⋯ weaken ⋯ ⦅ γ ⦆ ≡ α
(` x) ⋯-weaken-cancels-⦅ γ ⦆ = refl
[] ⋯-weaken-cancels-⦅ γ ⦆ = refl
(α ∥ β) ⋯-weaken-cancels-⦅ γ ⦆ = cong₂ _∥_ (α ⋯-weaken-cancels-⦅ γ ⦆) (β ⋯-weaken-cancels-⦅ γ ⦆)
(α ; β) ⋯-weaken-cancels-⦅ γ ⦆ = cong₂ _;_ (α ⋯-weaken-cancels-⦅ γ ⦆) (β ⋯-weaken-cancels-⦅ γ ⦆)

_⋯-wk-cancels-⦅_⦆ : (α : Struct n) (γ : Struct n) → wk α ⋯ ⦅ γ ⦆ ≡ α
(` x) ⋯-wk-cancels-⦅ γ ⦆ = refl
[] ⋯-wk-cancels-⦅ γ ⦆ = refl
(α ∥ β) ⋯-wk-cancels-⦅ γ ⦆ = cong₂ _∥_ (α ⋯-wk-cancels-⦅ γ ⦆) (β ⋯-wk-cancels-⦅ γ ⦆)
(α ; β) ⋯-wk-cancels-⦅ γ ⦆ = cong₂ _;_ (α ⋯-wk-cancels-⦅ γ ⦆) (β ⋯-wk-cancels-⦅ γ ⦆)

_Preserves[_]_⇒_ : ∀ {ℓ} → m →ₛ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
σ Preserves[ P ] Γ₁ ⇒ Γ₂ = ∀ {x} → P (Γ₁ x) → AllCx P Γ₂ (σ x)

module _ {ℓ} {P : Pred 𝕋 ℓ} where
  allCx-⋯ : σ Preserves[ P ] Γ₁ ⇒ Γ₂ → AllCx P Γ₁ γ → AllCx P Γ₂ (γ ⋯ σ)
  allCx-⋯ P⇒ΠP []      = []
  allCx-⋯ P⇒ΠP (x ∥ y) = allCx-⋯ P⇒ΠP x ∥ allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (x ; y) = allCx-⋯ P⇒ΠP x ; allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (` Px)  = P⇒ΠP Px

  allCx-wk : AllCx P Γ γ → AllCx P (T F.∷ Γ) (wk γ)
  allCx-wk [] = []
  allCx-wk (x ∥ y) = allCx-wk x ∥ allCx-wk y
  allCx-wk (x ; y) = allCx-wk x ; allCx-wk y
  allCx-wk (` x) = ` x

  ↑-preserves : σ Preserves[ P ] Γ₁ ⇒ Γ₂ → (σ ↑) Preserves[ P ] (T F.∷ Γ₁) ⇒ (T F.∷ Γ₂)
  ↑-preserves p⇒ {zero}  px = ` px
  ↑-preserves p⇒ {suc x} px = allCx-wk (p⇒ px)

≈′-⋯ : σ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → (_⋯ σ) Bin.Preserves (Γ₁ ∶_≈′_) ⟶ (Γ₂ ∶_≈′_)
≈′-⋯ σ-unr ;′-assoc = ;′-assoc
≈′-⋯ σ-unr (;′-cong₁ x) = ;′-cong₁ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr (;′-cong₂ x) = ;′-cong₂ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr ∥′-unit = ∥′-unit
≈′-⋯ σ-unr ∥′-assoc = ∥′-assoc
≈′-⋯ σ-unr ∥′-comm = ∥′-comm
≈′-⋯ σ-unr (∥′-cong₁ x) = ∥′-cong₁ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr (∥′-dup U) = ∥′-dup (allCx-⋯ σ-unr U)
≈′-⋯ σ-unr (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-⋯ σ-unr) (allCx-⋯ σ-unr) U)

≈-⋯ : σ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → (_⋯ σ) Bin.Preserves (Γ₁ ∶_≈_) ⟶ (Γ₂ ∶_≈_)
≈-⋯ = Eq*.gmap _ ∘ ≈′-⋯

≈-wk : Γ ∶ α ≈ β → T F.∷ Γ ∶ wk α ≈ wk β
≈-wk {α = α} {β} eq rewrite sym (weaken/wk α) | sym (weaken/wk β) = ≈-⋯ `_ eq

≼-⋯ : σ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → Γ₁ ∶ α ≼ β → Γ₂ ∶ α ⋯ σ ≼ β ⋯ σ
≼-⋯ σ-unr (≼-refl eq)    = ≼-refl (≈-⋯ σ-unr eq)
≼-⋯ σ-unr ≼-wk           = ≼-wk
≼-⋯ σ-unr (≼-∅ U)        = ≼-∅ (allCx-⋯ σ-unr U)
≼-⋯ σ-unr (≼-trans  x y) = ≼-trans (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
≼-⋯ σ-unr (≼-cong-; x y) = ≼-cong-; (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
≼-⋯ σ-unr (≼-cong-∥ x y) = ≼-cong-∥ (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
