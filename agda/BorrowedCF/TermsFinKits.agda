{-# OPTIONS --allow-unsolved-metas #-}

module BorrowedCF.TermsFinKits where

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Vec.Functional as F using (Vector)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Modes
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)

import BorrowedCF.FinKits as Kits

open Nat.Variables

data ParSeq : Set where
  par seq : ParSeq

infix 12 _∥_ _;_

data Struct (n : ℕ) : Set where
  `_  : 𝔽 n → Struct n
  []  : Struct n
  _∥_ : Struct n → Struct n → Struct n
  _;_ : Struct n → Struct n → Struct n

variable
  α α₁ α₂ α₃ α′ : Struct n
  β β₁ β₂ β₃ β′ : Struct n
  γ γ₁ γ₂ γ₃ γ′ : Struct n

infix 4 _≈′_

data _≈′_ {n} : Rel (Struct n) 0ℓ where
  ;′-unit₁ : [] ; α ≈′ α
  ;′-unit₂ : α ; [] ≈′ α
  ;′-assoc : (α ; β) ; γ ≈′ α ; (β ; γ)
  ;′-cong₁ : α ≈′ α′ → α ; β ≈′ α′ ; β
  ;′-cong₂ : β ≈′ β′ → α ; β ≈′ α ; β′

  ∥′-unit  : α ∥ [] ≈′ α
  ∥′-assoc : (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ)
  ∥′-comm  : α ∥ β ≈′ β ∥ α
  ∥′-cong₁ : α ≈′ α′ → α ∥ β ≈′ α′ ∥ β

infix 4 _≈_

_≈_ : Rel (Struct n) _
_≈_ = EqClosure _≈′_

;-unit₁ : [] ; α ≈ α
;-unit₁ = Eq*.return ;′-unit₁

;-unit₂ : α ; [] ≈ α
;-unit₂ = Eq*.return ;′-unit₂

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

≈-isEquivalence : ∀ n → IsEquivalence (_≈_ {n})
≈-isEquivalence _ = Eq*.isEquivalence _≈′_

private module ≈-Equivalence {n} = IsEquivalence (≈-isEquivalence n)
open ≈-Equivalence
  using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  public

infix 4 _∈ₛ_

data _∈ₛ_ (x : 𝔽 n) : Struct n → Set where
  ∈-`  : x ∈ₛ ` x
  ∈-∥₁ : x ∈ₛ α₁ → x ∈ₛ α₁ ∥ α₂
  ∈-∥₂ : x ∈ₛ α₂ → x ∈ₛ α₁ ∥ α₂
  ∈-;₁ : x ∈ₛ α₁ → x ∈ₛ α₁ ; α₂
  ∈-;₂ : x ∈ₛ α₂ → x ∈ₛ α₁ ; α₂

≈′-pres¹-∈ : ∀ {x} → α ≈′ β → x ∈ₛ α → x ∈ₛ β
≈′-pres¹-∈ ;′-unit₁ (∈-;₂ x∈) = x∈
≈′-pres¹-∈ ;′-unit₂ (∈-;₁ x∈) = x∈
≈′-pres¹-∈ ;′-assoc (∈-;₁ (∈-;₁ x∈)) = ∈-;₁ x∈
≈′-pres¹-∈ ;′-assoc (∈-;₁ (∈-;₂ x∈)) = ∈-;₂ (∈-;₁ x∈)
≈′-pres¹-∈ ;′-assoc (∈-;₂ x∈) = ∈-;₂ (∈-;₂ x∈)
≈′-pres¹-∈ ∥′-unit (∈-∥₁ x∈) = x∈
≈′-pres¹-∈ ∥′-assoc (∈-∥₁ (∈-∥₁ x∈)) = ∈-∥₁ x∈
≈′-pres¹-∈ ∥′-assoc (∈-∥₁ (∈-∥₂ x∈)) = ∈-∥₂ (∈-∥₁ x∈)
≈′-pres¹-∈ ∥′-assoc (∈-∥₂ x∈) = ∈-∥₂ (∈-∥₂ x∈)
≈′-pres¹-∈ ∥′-comm (∈-∥₁ x∈) = ∈-∥₂ x∈
≈′-pres¹-∈ ∥′-comm (∈-∥₂ x∈) = ∈-∥₁ x∈
≈′-pres¹-∈ (;′-cong₁ eq) (∈-;₁ x∈) = ∈-;₁ (≈′-pres¹-∈ eq x∈)
≈′-pres¹-∈ (;′-cong₁ eq) (∈-;₂ x∈) = ∈-;₂ x∈
≈′-pres¹-∈ (;′-cong₂ eq) (∈-;₁ x∈) = ∈-;₁ x∈
≈′-pres¹-∈ (;′-cong₂ eq) (∈-;₂ x∈) = ∈-;₂ (≈′-pres¹-∈ eq x∈)
≈′-pres¹-∈ (∥′-cong₁ eq) (∈-∥₁ x∈) = ∈-∥₁ (≈′-pres¹-∈ eq x∈)
≈′-pres¹-∈ (∥′-cong₁ eq) (∈-∥₂ x∈) = ∈-∥₂ x∈

≈′-pres²-∈ : ∀ {x} → α ≈′ β → x ∈ₛ β → x ∈ₛ α
≈′-pres²-∈ ;′-unit₁ x∈ = ∈-;₂ x∈
≈′-pres²-∈ ;′-unit₂ x∈ = ∈-;₁ x∈
≈′-pres²-∈ ;′-assoc (∈-;₁ x∈) = ∈-;₁ (∈-;₁ x∈)
≈′-pres²-∈ ;′-assoc (∈-;₂ (∈-;₁ x∈)) = ∈-;₁ (∈-;₂ x∈)
≈′-pres²-∈ ;′-assoc (∈-;₂ (∈-;₂ x∈)) = ∈-;₂ x∈
≈′-pres²-∈ ∥′-unit x∈ = ∈-∥₁ x∈
≈′-pres²-∈ ∥′-assoc (∈-∥₁ x∈) = ∈-∥₁ (∈-∥₁ x∈)
≈′-pres²-∈ ∥′-assoc (∈-∥₂ (∈-∥₁ x∈)) = ∈-∥₁ (∈-∥₂ x∈)
≈′-pres²-∈ ∥′-assoc (∈-∥₂ (∈-∥₂ x∈)) = ∈-∥₂ x∈
≈′-pres²-∈ ∥′-comm (∈-∥₁ x∈) = ∈-∥₂ x∈
≈′-pres²-∈ ∥′-comm (∈-∥₂ x∈) = ∈-∥₁ x∈
≈′-pres²-∈ (;′-cong₁ eq) (∈-;₁ x∈) = ∈-;₁ (≈′-pres²-∈ eq x∈)
≈′-pres²-∈ (;′-cong₁ eq) (∈-;₂ x∈) = ∈-;₂ x∈
≈′-pres²-∈ (;′-cong₂ eq) (∈-;₁ x∈) = ∈-;₁ x∈
≈′-pres²-∈ (;′-cong₂ eq) (∈-;₂ x∈) = ∈-;₂ (≈′-pres²-∈ eq x∈)
≈′-pres²-∈ (∥′-cong₁ eq) (∈-∥₁ x∈) = ∈-∥₁ (≈′-pres²-∈ eq x∈)
≈′-pres²-∈ (∥′-cong₁ eq) (∈-∥₂ x∈) = ∈-∥₂ x∈

≈-pres-∈ : ∀ {x} → α ≈ β → x ∈ₛ α → x ∈ₛ β
≈-pres-∈ refl x∈ = x∈
≈-pres-∈ (Sym.fwd y ◅ ys) x∈ = ≈-pres-∈ ys (≈′-pres¹-∈ y x∈)
≈-pres-∈ (Sym.bwd y ◅ ys) x∈ = ≈-pres-∈ ys (≈′-pres²-∈ y x∈)

γ≈`x⇒`x∈γ : ∀ {x} → γ ≈ ` x → x ∈ₛ γ
γ≈`x⇒`x∈γ eq = ≈-pres-∈ (≈-sym eq) ∈-`

data Const : Set where
  `unit `fork `send `recv `drop `acq `end : Const
  `new : 𝕊 0 → Const
  `lsplit `rsplit : (s₁ s₂ : 𝕊 0) → Const

data Tm (n : ℕ) : Set where
  `_ : 𝔽 n → Tm n
  K : (c : Const) → Tm n
  λ[_] : (d : Dir) (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _,⟨_⟩_ : (e₁ : Tm n) (d : Dir) (e₂ : Tm n) → Tm n
  `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  `let⊗_`in_ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n

open module Syntax = Kits.Syntax record
  { Tm = Tm
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Tm; `_; Traversal)
  renaming (id to idₖ)
  public

infixl 5 _⋯_

_⋯_ : ⦃ K : Kit 𝓕 ⦄ → Tm m → m –[ K ]→ n → Tm n
(` x) ⋯ ϕ = `/id (ϕ x)
K c ⋯ ϕ = K c
λ[ d ] e ⋯ ϕ = λ[ d ] (e ⋯ ϕ ↑)
(e · e₁) ⋯ ϕ = (e ⋯ ϕ) · (e₁ ⋯ ϕ)
(e ; e₁) ⋯ ϕ =  (e ⋯ ϕ) ; (e₁ ⋯ ϕ)
(e ,⟨ d ⟩ e₁) ⋯ ϕ =  (e ⋯ ϕ) ,⟨ d ⟩ (e₁ ⋯ ϕ)
(`let e `in e₁) ⋯ ϕ = `let (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑)
(`let⊗ e `in e₁) ⋯ ϕ = `let⊗ (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑ ↑)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (e : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → e ⋯ ϕ ≡ e
⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
⋯-id (K c) eq = refl
⋯-id (λ[ d ] e) eq = cong λ[ d ] (⋯-id e (id↑ eq))
⋯-id (e · e₁) eq = cong₂ _·_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ; e₁) eq = cong₂ _;_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ,⟨ d ⟩ e₁) eq = cong₂ (_,⟨ d ⟩_) (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-id e eq) (⋯-id e₁ (id↑ eq))
⋯-id (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-id e eq) (⋯-id e₁ (id↑* 2 eq))

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (e : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → e ⋯ ϕ₁ ≡ e ⋯ ϕ₂
⋯-cong (` x) eq = cong `/id (eq x)
⋯-cong (K c) eq = refl
⋯-cong (λ[ d ] e) eq = cong λ[ d ] (⋯-cong e (eq ~↑))
⋯-cong (e · e₁) eq = cong₂ _·_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ; e₁) eq = cong₂ _;_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ,⟨ d ⟩ e₁) eq = cong₂ (_,⟨ d ⟩_) (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑))
⋯-cong (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑* 2))

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-id; ⋯-cong; CTraversal)

fusion :
  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
  (x : Tm n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) → x ⋯ ϕ₁ ⋯ ϕ₂ ≡ x ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion (x₁ ; x₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x₁ ϕ₁ ϕ₂) (fusion x₂ ϕ₁ ϕ₂)
fusion (K c) ϕ₁ ϕ₂ = refl
fusion (λ[ d ] e) ϕ₁ ϕ₂ = cong λ[ d ] $
  fusion e (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (e₁ · e₂) ϕ₁ ϕ₂ = cong₂ _·_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (e₁ ,⟨ d ⟩ e₂) ϕ₁ ϕ₂ = cong₂ (_,⟨ d ⟩_) (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (`let e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e₂ (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (`let⊗ e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑* 2) (ϕ₂ ↑* 2) ■ ⋯-cong e₂ (sym ∘ dist-↑*-· 2 ϕ₁ ϕ₂)

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

Ctx = Vector 𝕋

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx n

infixl 5 _⋯𝓢_

_⋯𝓢_ : Struct m → m →ᵣ n → Struct n
` x ⋯𝓢 ρ = ` ρ x
[] ⋯𝓢 ρ = []
x ∥ y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ∥ (y ⋯𝓢 ρ)
x ; y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ; (y ⋯𝓢 ρ)

data MobCx (Γ : Ctx n) : Struct n → Set where
  []  : MobCx Γ []
  _∥_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ∥ α₂)
  _;_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ; α₂)
  `_  : ∀ {x} → Mobile (Γ x) → MobCx Γ (` x)

joinP/S : ParSeq → Struct n → Struct n → Struct n
joinP/S par = _∥_
joinP/S seq = _;_

joinP/S-∅₁ : ∀ p/s → γ₁ ≈ [] → joinP/S p/s γ₁ γ₂ ≈ γ₂
joinP/S-∅₁ par eq = ∥-cong eq refl ◅◅ ∥-comm ◅◅ ∥-unit
joinP/S-∅₁ seq eq = ;-cong eq refl ◅◅ ;-unit₁

joinDir : Dir → Struct n → Struct n → Struct n
joinDir 𝟙 = _∥_
joinDir L = _;_
joinDir R = flip _;_

cong-joinDir : (d : Dir) → α₁ ≈ α₂ → β₁ ≈ β₂ → joinDir d α₁ β₁ ≈ joinDir d α₂ β₂
cong-joinDir L eq-α eq-β = ;-cong eq-α eq-β
cong-joinDir R eq-α eq-β = ;-cong eq-β eq-α
cong-joinDir 𝟙 eq-α eq-β = ∥-cong eq-α eq-β

Split : Dir → Struct n → Struct n → Struct n → Set
Split d α α₁ α₂ = α ≈ joinDir d α₁ α₂

SeqIsPure : ParSeq → Eff → Eff → Set
SeqIsPure par ϵ₁ ϵ₂ = ϵ₁ ≡ ϵ₂
SeqIsPure seq ϵ₁ ϵ₂ = ϵ₂ ≡ ℙ

pairDir : ParSeq → Dir
pairDir par = 𝟙
pairDir seq = L

infix 4 ⊢_∶_

private
  _→m,1_∣_ : 𝕋 → 𝕋 → Eff → 𝕋
  t →m,1 u ∣ ϵ = arr mob 𝟙 ϵ t u

data ⊢_∶_ : Const → 𝕋 → Set where
  `unit : ⊢ `unit ∶ unit
  `new : ∀ {s} → ⊢ `new s ∶ arr mob 𝟙 ϵ unit (pair 𝟙 ⟨ acq ; s ⟩ ⟨ acq ; dual s ⟩)
  `lsplit : ∀ {s₁ s₂} → ⊢ `lsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair L ⟨ s₁ ⟩ ⟨ s₂ ⟩)
  `rsplit : ∀ {s₁ s₂} → ⊢ `rsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair 𝟙 ⟨ s₁ ; ret ⟩ ⟨ acq ; s₂ ⟩)
  `drop : ⊢ `drop ∶ arr mob 𝟙 ϵ ⟨ ret ⟩ unit
  `acq : ∀ {s} → ⊢ `acq ∶ ⟨ acq ; s ⟩ →m,1 ⟨ s ⟩ ∣ ϵ
  `fork : ⊢ `fork ∶ (unit →m,1 unit ∣ 𝕀) →m,1 unit ∣ ϵ
  `send : ∀ {t} → Mobile t → ⊢ `send ∶ pair 𝟙 t ⟨ msg ‼ t ⟩ →m,1 unit ∣ 𝕀
  `recv : ∀ {t} → Mobile t → ⊢ `recv ∶ ⟨ msg ⁇ t ⟩ →m,1 t ∣ 𝕀
  `end : ⊢ `end ∶ ⟨ end p ⟩ →m,1 unit ∣ 𝕀


private variable
  e e₁ e₂ : Tm n

infix 4 _;_⊢_∶_∣_

data _;_⊢_∶_∣_ (Γ : Ctx n) (γ : Struct n) : Tm n → 𝕋 → Eff → Set where
  T-Const : ∀ {c} →
    γ ≈ [] →
    ⊢ c ∶ T →
    -------------------
    Γ ; γ ⊢ K c ∶ T ∣ ℙ

  T-Var : ∀ {x} →
    γ ≈ ` x →
    Γ x ≡ T →
    -------------------
    Γ ; γ ⊢ ` x ∶ T ∣ ℙ

  T-Abs :
    (𝓂 ≡ mob → MobCx Γ α) →
    T F.∷ Γ ; joinDir d (` zero) (γ ⋯𝓢 weaken) ⊢ e ∶ U ∣ ϵ →
    --------------------------------------------------------
    Γ ; γ ⊢ λ[ d ] e ∶ arr 𝓂 d ϵ T U ∣ ℙ

  T-App :
    Split d γ γ₁ γ₂                 →
    Γ ; γ₁ ⊢ e₁ ∶ arr 𝓂 d ϵ T U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T             ∣ ϵ →
    ---------------------------------
    Γ ; γ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-Pair : (p/s : ParSeq) →
    γ ≈ joinP/S p/s γ₁ γ₂ →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    SeqIsPure p/s ϵ₁ ϵ₂ →
    ------------------------------------------------------------
    Γ ; γ ⊢ e₁ ,⟨ pairDir p/s ⟩ e₂ ∶ pair (pairDir p/s) T U ∣ ϵ₁

  T-Let : (p/s : ParSeq) →
    γ ≈ joinP/S p/s γ₁ γ₂ →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ →
    T F.∷ Γ ; joinP/S p/s (` zero) (γ₂ ⋯𝓢 weaken) ⊢ e₂ ∶ U ∣ ϵ →
    ------------------------------------------------------------
    Γ ; γ ⊢ `let e₁ `in e₂ ∶ U ∣ ϵ

  T-LetUnit : (p/s : ParSeq) →
    γ ≈ joinP/S p/s γ₁ γ₂ →
    Γ ; γ₁ ⊢ e₁ ∶ unit ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T    ∣ ϵ →
    ------------------------
    Γ ; γ ⊢ e₁ ; e₂ ∶ T ∣ ϵ

  T-LetPair : (p/s : ParSeq) →
    γ ≈ joinP/S p/s γ₁ γ₂ →
    Γ ; γ₁ ⊢ e₁ ∶ pair d T₁ T₂ ∣ ϵ →
    T₁ F.∷ T₂ F.∷ Γ ;
      joinP/S p/s (joinDir d (` zero) (` suc zero))
                  (γ₂ ⋯𝓢 weaken* 2)
      ⊢ e₂ ∶ U ∣ ϵ →
    -----------------------------------------------
    Γ ; γ ⊢ `let⊗ e₁ `in e₂ ∶ U ∣ ϵ

  T-WeakEff :
    Γ ; γ ⊢ e ∶ T ∣ ℙ →
    -------------------
    Γ ; γ ⊢ e ∶ T ∣ 𝕀


record TKit (K : Kit 𝓕) (CK : CKit K Kᵣ K) : Set₁ where
  private instance _ = K; _ = CK

  infix 4 _;_⊢_∶_ _∶_;_⇒ₖ_
  field
    _;_⊢_∶_ : Ctx n → Struct n → 𝓕 n → 𝕋 → Set
    id/⊢` : (x : 𝔽 n) → Γ ; ` x ⊢ id/` x ∶ Γ x
    ⊢`/id : {x/t : 𝓕 n} → Γ ; γ ⊢ x/t ∶ T → Γ ; γ ⊢ `/id x/t ∶ T ∣ ℙ
    ⊢wk : (T : 𝕋) (e : 𝓕 n) → Γ ; γ ⊢ e ∶ T′ → T F.∷ Γ ; γ ⋯𝓢 wk ⊢ wk e ∶ T′



  _∶_;_⇒ₖ_ : m –[ K ]→ n → Ctx m → Struct m → Ctx n → Set
  ϕ ∶ Γ₁ ; γ₁ ⇒ₖ Γ₂ = ∀ x → x ∈ₛ γ₁ → ∃ λ γ₂ → Γ₂ ; γ₂ ⊢ ϕ x ∶ Γ₁ x

  ⊢↑ : {ϕ : m –[ K ]→ n} → ϕ ∶ Γ₁ ; γ ⇒ₖ Γ₂ → (∀ {x} → suc x ∈ₛ γ′ → x ∈ₛ γ) → ϕ ↑ ∶ T F.∷ Γ₁ ; γ′ ⇒ₖ T F.∷ Γ₂
  ⊢↑ ⊢ϕ γ≼ zero x∈ = _ , id/⊢` zero
  ⊢↑ ⊢ϕ γ≼ (suc x) x∈ = {!⊢ϕ x (γ≼ x∈)!}

{-
  data _∶_;_⇒ₖ_;_ : m –[ K ]→ n → Ctx m → Struct m → Ctx n → Struct n → Set where
    ϕ-id : ∀ {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ  → ϕ ∶ Γ ; γ ⇒ₖ Γ ; γ

    ϕ-↑ : ∀ {ϕ′ : m –[ K ]→ n} {ϕ} p/s →
      ϕ ≗ ϕ′ ↑ →
      γ ≈ joinP/S p/s (γ₁ ⋯𝓢 wk) (` zero) →
      γ′ ≈ joinP/S p/s (γ₂ ⋯𝓢 wk) (` zero) →
      ϕ′ ∶ Γ₁ ; γ₁ ⇒ₖ Γ₂ ; γ₂ →
      ϕ ∶ T F.∷ Γ₁ ; γ ⇒ₖ T F.∷ Γ₂ ; γ′

    ϕ-wk : ∀ {ϕ′ : m –[ K ]→ n} {ϕ : m –[ K ]→ suc n} (p/s : ParSeq) →
      ϕ ≗ ϕ′ ·ₖ wk →
      γ₂ ⋯𝓢 wk ≈ γ′ →
      ϕ′ ∶ Γ₁ ; γ₁ ⇒ₖ Γ₂ ; γ₂ →
      ϕ ∶ Γ₁ ; γ₁ ⇒ₖ T F.∷ Γ₂ ; γ′

  _&_ : {ϕ : m –[ K ]→ n} (x : 𝔽 m) → ϕ ∶ Γ ; ` x ⇒ₖ Γ′ ; γ′ → Γ′ ; γ′ ⊢ ϕ x ∶ Γ x
  x & ϕ-id eq rewrite eq x = id/⊢` x
  zero & ϕ-↑ p/s eq s₁ s₂ ⊢ϕ rewrite eq zero = {!!}
  suc x & ϕ-↑ p/s eq s₁ s₂ ⊢ϕ = {!!}
  x & ϕ-wk p/s x₁ x₂ ⊢ϕ = {!!}

  ⊢ϕ-pres-∅ : {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ; γ ⇒ₖ Γ′ ; γ′ → γ ≈ [] → γ′ ≈ []
  ⊢ϕ-pres-∅ (ϕ-id x) eq = eq
  ⊢ϕ-pres-∅ (ϕ-↑ p/s eq-↑ s₁ s₂ ⊢ϕ) eq = {!!}
  ⊢ϕ-pres-∅ (ϕ-wk p/s x x₁ ⊢ϕ) eq = {!!}
-}

instance
  TKᵣ : TKit Kᵣ it
  TKᵣ = record
    { _;_⊢_∶_ = λ Γ γ x T → γ ≈ ` x × Γ x ≡ T
    ; id/⊢` = λ x → refl , refl
    ; ⊢`/id = uncurry T-Var
    }

  TKₛ : TKit Kₛ it
  TKₛ = record
    { _;_⊢_∶_ = λ Γ γ x T → Γ ; γ ⊢ x ∶ T ∣ ℙ
    ; id/⊢` = λ x → T-Var refl refl
    ; ⊢`/id = λ x → x
    }

open TKit ⦃ … ⦄

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ →
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ ⦃ TK : TKit K C₁ ⦄ →
       {e : Tm m} {ϕ : m –[ K ]→ n} →
       Γ₁ ; γ₁ ⊢ e ∶ T ∣ ϵ →
       ϕ ∶ Γ₁ ; γ₁ ⇒ₖ Γ₂ →
       ∃ λ γ₂ → Γ₂ ; γ₂ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
T-Const γ≈∅ c ⊢⋯ ⊢ϕ = [] , T-Const refl c
_⊢⋯_ ⦃ TK = TK ⦄ (T-Var {x = x} γ≈` refl) ⊢ϕ = Π.map₂ (⊢`/id ⦃ TK ⦄) (⊢ϕ x (γ≈`x⇒`x∈γ γ≈`))
T-Abs x e ⊢⋯ ⊢ϕ = {!e ⊢⋯ ?!}
T-App x e₁ e₂ ⊢⋯ ⊢ϕ with e₁ ⊢⋯ {!!} | e₂ ⊢⋯ {!!}
... | γ₁ , e₁′ | γ₂ , e₂′ = _ , T-App refl e₁′ e₂′
T-Pair p/s x x₁ x₂ x₃ ⊢⋯ ⊢ϕ = {!!}
T-Let p/s x e e₁ ⊢⋯ ⊢ϕ = {!!}
T-LetUnit p/s x e e₁ ⊢⋯ ⊢ϕ = {!!}
T-LetPair p/s x e e₁ ⊢⋯ ⊢ϕ = {!!}
T-WeakEff x ⊢⋯ ⊢ϕ = {!!}

-- record TKit (K : Kit _∋/⊢_) : Set₁ where
--   private instance _ = K
--   infix 4 _∋/⊢_∶_ _∶_;_⇒_;_
--   infixl 6 _⊢↑_

-- --  field _∋/⊢_∶_

--   _∶_;_⇒_;_ : S₁ –[ K ]→ S₂ → Ctx S₁ → Struct S₁ → Ctx S₂ → Struct S₂ → Set
--   _∶_;_⇒_;_ {S₁} {S₂} ϕ Γ₁ γ₁ Γ₂ γ₂ = {!(x : 𝕖 ∈ S₁) (t : 𝕋) → Γ₁ !}

-- -- infix 4 _⊢_∶_

-- -- data _⊢_∶_ (Γ : Ctx S) : S ⊢ s → S ∶⊢ s → Set where
-- --   ⟨_⟩ : ∀ {e t} → Γ ; γ ⊢ e ∶ t ∣ ϵ → Γ ⊢ e ∶ ⟨ t ⟩

-- -- open module Typing = Types.Typing record
-- --   { _⊢_∶_ = λ Γ e t → Γ ⊢ e ∶ t
-- --   ; ⊢` = λ{ {s = 𝕖} {Γ = Γ} {x} refl →
-- --                subst (λ t → Γ ⊢ ` x ∶ t)
-- --                      (sym (lookupCx≡⟨lookup-𝕋⟩ Γ x))
-- --                      ⟨ T-Var {ϵ = ℙ} (Eq*.reflexive _) (lookupCx≡⟨lookup-𝕋⟩ Γ x) ⟩
-- --          }
-- --   }
-- --   hiding (_⊢_∶_)
-- --   public

-- -- ⟨_⟩⊢⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
-- --        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
-- --        {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
-- --        {e : S₁ ⊢ 𝕖} {t : 𝕋} {ϕ : S₁ –[ K ]→ S₂} →
-- --        Γ₁ ; γ₁ ⊢ e ∶ t ∣ ϵ →
-- --        ϕ ∶ Γ₁ ⇒ₖ Γ₂ →
-- --        Γ₂ ; γ₂ ⊢ e ⋯ ϕ ∶ t ∣ ϵ
-- -- ⟨ T-Const x x₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-Var x x₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-Abs x e ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-App γ e₁ e₂ ⟩⊢⋯ ⊢ϕ = T-App {!!} {!!} {!!}
-- -- ⟨ T-Let p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-LetUnit p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-LetPair p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}

-- -- _⊢⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
-- --        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
-- --        {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
-- --        {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
-- --        Γ₁ ⊢ e ∶ t →
-- --        ϕ ∶ Γ₁ ⇒ₖ Γ₂ →
-- --        Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
-- -- ⟨ e ⟩ ⊢⋯ ⊢ϕ = ⟨ {!⟨ e ⟩ ⊢⋯ ⊢ϕ!} ⟩
