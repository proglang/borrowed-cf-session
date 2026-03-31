module BorrowedCF.Terms where

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (ε; _◅_; _◅◅_; kleisliStar)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Modes
open import BorrowedCF.Types
import BorrowedCF.Kits as Kits

open Nat.Variables

data Sort : Set where
  𝕖 𝕥 : Sort

Scope = List Sort

variable
  s s₁ s₂ s₃ s′ s₁′ s₂′ s₃′ : Sort
  S S₁ S₂ S₃ S′ : Scope
  x y z x₁ x₂ : s ∈ S

infix 12 _∥_ _;_

data Struct (S : Scope) : Set where
  `_  : 𝕖 ∈ S → Struct S
  []  : Struct S
  _∥_ : Struct S → Struct S → Struct S
  _;_ : Struct S → Struct S → Struct S

variable
  α α₁ α₂ α₃ α′ : Struct S
  β β₁ β₂ β₃ β′ : Struct S
  γ γ₁ γ₂ γ₃ γ′ : Struct S

infix 4 _≈′_

data _≈′_ {S} : Rel (Struct S) 0ℓ where
  ;′-unit  : α ; [] ≈′ α
  ;′-assoc : (α ; β) ; γ ≈′ α ; (β ; γ)
  ;′-cong₁ : α ≈′ α′ → α ; β ≈′ α′ ; β
  ;′-cong₂ : β ≈′ β′ → α ; β ≈′ α ; β′

  ∥′-unit  : α ∥ [] ≈′ α
  ∥′-assoc : (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ)
  ∥′-comm  : α ∥ β ≈′ β ∥ α
  ∥′-cong₁ : α ≈′ α′ → α ∥ β ≈′ α′ ∥ β

infix 4 _≈_

_≈_ : Rel (Struct S) _
_≈_ = EqClosure _≈′_

;-unit : α ; [] ≈ α
;-unit = Eq*.return ;′-unit

;-assoc : (α ; β) ; γ ≈ α ; (β ; γ)
;-assoc = Eq*.return ;′-assoc

;-cong : α ≈ α′ → β ≈ β′ → α ; β ≈ α′ ; β′
;-cong xs ys = Eq*.gmap (_; _) ;′-cong₁ xs ◅◅ Eq*.gmap (_ ;_) ;′-cong₂ ys

∥-unit : α ∥ [] ≈ α
∥-unit = Eq*.return ∥′-unit

∥-assoc : (α ∥ β) ∥ γ ≈ α ∥ (β ∥ γ)
∥-assoc = Eq*.return ∥′-assoc

∥-comm : α ∥ β ≈ β ∥ α
∥-comm = Eq*.return ∥′-comm

∥-cong : α ≈ α′ → β ≈ β′ → α ∥ β ≈ α′ ∥ β′
∥-cong xs ys = Eq*.gmap (_∥ _) ∥′-cong₁ xs ◅◅ ∥-comm ◅◅ Eq*.gmap (_∥ _) ∥′-cong₁ ys ◅◅ ∥-comm

data Const : Set where
  `new `fork `close `wait `send `recv `lsplit `rsplit `drop `acq : Const

infix 4 _⊢_

data _⊢_ (S : Scope) : Sort → Set where
  `_ : s ∈ S → S ⊢ s

  -- Terms
  K : (c : Const) → S ⊢ 𝕖
  λ[_] : (d : Dir) (e : 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖
  _·_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
  _;_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
  _,⟨_⟩_ : (e₁ : S ⊢ 𝕖) (d : Dir) (e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
  `let_`in_ : (e₁ : S ⊢ 𝕖) (e₂ : 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖
  `let⊗_`in_ : (e₁ : S ⊢ 𝕖) (e₂ : 𝕖 ∷ 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖

  -- Types
  ⟨_⟩ : (t : 𝕋) → S ⊢ 𝕥

open module Syntax = Kits.Syntax record
  { Sort = Sort
  ; _⊢_ = λ S s → S ⊢ s
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Sort; _⊢_; `_; Traversal)
  renaming (id to idₖ)
  public

infix 5 _⋯_

_⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
` x ⋯ ϕ = `/id (ϕ _ x)
x₁ ; x₂ ⋯ ϕ = (x₁ ⋯ ϕ) ; (x₂ ⋯ ϕ)
K c ⋯ ϕ = K c
λ[ d ] e ⋯ ϕ = λ[ d ] (e ⋯ ϕ ↑ 𝕖)
e₁ · e₂ ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
e₁ ,⟨ d ⟩ e₂ ⋯ ϕ = (e₁ ⋯ ϕ) ,⟨ d ⟩ (e₂ ⋯ ϕ)
`let e₁ `in e₂ ⋯ ϕ = `let (e₁ ⋯ ϕ) `in (e₂ ⋯ ϕ ↑ 𝕖)
`let⊗ e₁ `in e₂ ⋯ ϕ = `let⊗ (e₁ ⋯ ϕ) `in (e₂ ⋯ ϕ ↑ 𝕖 ↑ 𝕖)
⟨ t ⟩ ⋯ ϕ = ⟨ t ⟩

⋯-id : ⦃ K : Kit _∋/⊢_ ⦄ (x : S ⊢ s) → x ⋯ idₖ ≡ x
⋯-id (` x) = `/`-is-` x
⋯-id (x₁ ; x₂) = cong₂ _;_ (⋯-id x₁) (⋯-id x₂)
⋯-id (K x) = refl
⋯-id (λ[ d ] e) = cong λ[ d ] (cong (e ⋯_) (~-ext id↑~id) ■ ⋯-id e)
⋯-id (e₁ · e₂) = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
⋯-id (e₁ ,⟨ d ⟩ e₂) = cong₂ (_,⟨ d ⟩_) (⋯-id e₁) (⋯-id e₂)
⋯-id (`let e₁ `in e₂) = cong₂ `let_`in_ (⋯-id e₁) (cong (e₂ ⋯_) (~-ext id↑~id) ■ ⋯-id e₂)
⋯-id (`let⊗ e₁ `in e₂) = cong₂ `let⊗_`in_ (⋯-id e₁) (cong (e₂ ⋯_) (~-ext (id↑*~id (𝕖 ∷ 𝕖 ∷ []))) ■ ⋯-id e₂)
⋯-id ⟨ t ⟩ = refl

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  }
  hiding (_⋯_; ⋯-id; CTraversal)
  public

fusion :
  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
  (x : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → (x ⋯ ϕ₁) ⋯ ϕ₂ ≡ x ⋯ (ϕ₁ ·ₖ ϕ₂)
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
fusion (x₁ ; x₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x₁ ϕ₁ ϕ₂) (fusion x₂ ϕ₁ ϕ₂)
fusion (K c) ϕ₁ ϕ₂ = refl
fusion (λ[ d ] e) ϕ₁ ϕ₂ = cong λ[ d ] $
  fusion e (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ■ cong (e ⋯_) (sym (~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂)))
fusion (e₁ · e₂) ϕ₁ ϕ₂ = cong₂ _·_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (e₁ ,⟨ d ⟩ e₂) ϕ₁ ϕ₂ = cong₂ (_,⟨ d ⟩_) (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (`let e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖)
    ■ (cong (e₂ ⋯_) (sym (~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))))
fusion (`let⊗ e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑ 𝕖 ↑ 𝕖) (ϕ₂ ↑ 𝕖 ↑ 𝕖)
    ■ cong (e₂ ⋯_) (sym (~-ext (dist-↑*-· (𝕖 ∷ 𝕖 ∷ []) ϕ₁ ϕ₂)))
fusion ⟨ t ⟩ ϕ₁ ϕ₂ = refl

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion; Types)
  public

open module Types = CTraversal.Types record { ↑ᵗ = λ x → 𝕥}
  hiding (Typing)
  public

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx S
  T T₁ T₂ T₃ T′ : S ∶⊢ s

infixl 5 _⋯𝓢_

_⋯𝓢_ : Struct S → S →ᵣ S′ → Struct S′
` x ⋯𝓢 ρ = ` ρ _ x
[] ⋯𝓢 ρ = []
x ∥ y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ∥ (y ⋯𝓢 ρ)
x ; y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ; (y ⋯𝓢 ρ)

infix 4 _;_⊢_∶_∣_

data _;_⊢_∶_∣_ {S} : Ctx S → Struct S → S ⊢ 𝕖 → 𝕋 → Eff → Set where
--  T-Var : ∀ {x} →
--    Γ ; α ⊢ ` x : ? ∣

  T-AbsLin : ∀ {e t u} →
    ⟨ t ⟩ ∷ Γ ; (α ⋯𝓢 weaken _) ∥ ` here refl ⊢ e ∶ u ∣ ϵ′ →
    -------------------------------------
    Γ ; α ⊢ λ[ 𝟙 ] e ∶ arr 𝓂 𝟙 ϵ′ t u ∣ ϵ

-- data Const : Set where
--   `new `fork `close `wait `send `recv `lsplit `rsplit `drop `acq : Const

-- data Tm (n : ℕ) : Set where
--   ⟨_⟩ : Const → Tm n
--   `_ : (x : 𝔽 n) → Tm n
--   λ[_] : Dir → Tm (suc n) → Tm n
--   _·_ : Tm n → Tm n → Tm n
--   _;_ : Tm n → Tm n → Tm n
--   _,⟨_⟩_ : Tm n → Dir → Tm n → Tm n
--   `let_`in_ : Tm n → Tm (1 + n) → Tm n
--   `let⊗_`in_ : Tm n → Tm (2 + n) → Tm n
