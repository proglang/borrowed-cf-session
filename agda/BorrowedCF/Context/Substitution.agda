{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Substitution where

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import BorrowedCF.Prelude
open import BorrowedCF.Types hiding (α; α₁; α₂; α₃; α′)
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

{-
_→ₛ_ : ℕ → ℕ → Set
m →ₛ n = 𝔽 m → Struct n

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

weaken* : ∀ m → n →ₛ (m + n)
weaken* zero = idₛ
weaken* (suc m) = wkₛ (weaken* m)

wkʳ : ∀ n → m →ₛ (m + n)
wkʳ n x = ` (x ↑ˡ n)

_↑ : m →ₛ n → suc m →ₛ suc n
σ ↑ = ` zero ∷ₛ wkₛ σ

_↑*_ : n₁ →ₛ n₂ → ∀ m → (m + n₁) →ₛ (m + n₂)
σ ↑* zero  = σ
σ ↑* suc m = (σ ↑* m) ↑

⦅_⦆ : Struct n → suc n →ₛ n
⦅ α ⦆ = α ∷ₛ idₛ

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

wk-⋯ : (γ : Struct m) (σ : m →ₛ n) → wk (γ ⋯ σ) ≡ γ ⋯ wk ∘ σ
wk-⋯ (` x) σ = refl
wk-⋯ [] σ = refl
wk-⋯ (α ∥ β) σ = cong₂ _∥_ (wk-⋯ α σ) (wk-⋯ β σ)
wk-⋯ (α ; β) σ = cong₂ _;_ (wk-⋯ α σ) (wk-⋯ β σ)

⋯-↑-weaken* : ∀ m (γ : Struct n₁) (σ : n₁ →ₛ n₂) → γ ⋯ weaken* m ⋯ σ ↑* m ≡ γ ⋯ σ ⋯ weaken* m
⋯-↑-weaken* m [] σ = refl
⋯-↑-weaken* m (α ∥ β) σ = cong₂ _∥_ (⋯-↑-weaken* m α σ) (⋯-↑-weaken* m β σ)
⋯-↑-weaken* m (α ; β) σ = cong₂ _;_ (⋯-↑-weaken* m α σ) (⋯-↑-weaken* m β σ)
⋯-↑-weaken* zero (` x) σ = sym (⋯-id (λ _ → refl) (σ x))
⋯-↑-weaken* (suc m) (` x) σ =
  let open ≡-Reasoning in
  (` x) ⋯ weaken* (suc m) ⋯ (σ ↑* suc m) ≡⟨⟩
  wk (weaken* m x) ⋯ (σ ↑* m) ↑ ≡⟨ cong (λ γ → γ ⋯ (σ ↑* m) ↑) (weaken/wk (weaken* m x)) ⟨
  weaken* m x ⋯ weaken ⋯ (σ ↑* m) ↑ ≡⟨ ⋯-↑-weaken (weaken* m x) (σ ↑* m) ⟨
  weaken* m x ⋯ σ ↑* m ⋯ weaken ≡⟨ cong (λ γ → γ ⋯ weaken) (⋯-↑-weaken* m (` x) σ) ⟩
  σ x ⋯ weaken* m ⋯ weaken ≡⟨ weaken/wk (σ x ⋯ weaken* m) ⟩
  wk (σ x ⋯ weaken* m) ≡⟨ wk-⋯ (σ x) (weaken* m) ⟩
  σ x ⋯ wk ∘ weaken* m ≡⟨⟩
  (` x) ⋯ σ ⋯ weaken* (suc m) ∎

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
-}

_Preserves[_]_⇒_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
σ Preserves[ P ] Γ₁ ⇒ Γ₂ = ∀ {x} → P (Γ₁ x) → AllCx P Γ₂ (`/id (σ x))

module _ {ℓ} {P : Pred 𝕋 ℓ} where
  allCx-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇒ Γ₂ → AllCx P Γ₁ γ → AllCx P Γ₂ (γ ⋯ ϕ)
  allCx-⋯ P⇒ΠP []      = []
  allCx-⋯ P⇒ΠP (x ∥ y) = allCx-⋯ P⇒ΠP x ∥ allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (x ; y) = allCx-⋯ P⇒ΠP x ; allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (` Px)  = P⇒ΠP Px

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

≈′-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → Γ₁ ∶ α ≈′ β → Γ₂ ∶ α ⋯ ϕ ≈′ β ⋯ ϕ
≈′-⋯ σ-unr ;′-assoc = ;′-assoc
≈′-⋯ σ-unr (;′-cong₁ x) = ;′-cong₁ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr (;′-cong₂ x) = ;′-cong₂ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr ∥′-unit = ∥′-unit
≈′-⋯ σ-unr ∥′-assoc = ∥′-assoc
≈′-⋯ σ-unr ∥′-comm = ∥′-comm
≈′-⋯ σ-unr (∥′-cong₁ x) = ∥′-cong₁ (≈′-⋯ σ-unr x)
≈′-⋯ σ-unr (∥′-dup U) = ∥′-dup (allCx-⋯ σ-unr U)
≈′-⋯ σ-unr (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-⋯ σ-unr) (allCx-⋯ σ-unr) U)

≈-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → Γ₁ ∶ α ≈ β → Γ₂ ∶ α ⋯ ϕ ≈ β ⋯ ϕ
≈-⋯ ϕ-unr = Eq*.gmap _ (≈′-⋯ ϕ-unr)

≼-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ Unr ] Γ₁ ⇒ Γ₂ → Γ₁ ∶ α ≼ β → Γ₂ ∶ α ⋯ ϕ ≼ β ⋯ ϕ
≼-⋯ σ-unr (≼-refl eq)    = ≼-refl (≈-⋯ σ-unr eq)
≼-⋯ σ-unr ≼-wk           = ≼-wk
≼-⋯ σ-unr (≼-∅ U)        = ≼-∅ (allCx-⋯ σ-unr U)
≼-⋯ σ-unr (≼-trans  x y) = ≼-trans (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
≼-⋯ σ-unr (≼-cong-; x y) = ≼-cong-; (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
≼-⋯ σ-unr (≼-cong-∥ x y) = ≼-cong-∥ (≼-⋯ σ-unr x) (≼-⋯ σ-unr y)
