module BorrowedCF.Context where

open import Data.Vec.Functional as F using (Vector)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)
open import Relation.Binary.Construct.Union as U using (_∪_)

import Relation.Binary.Reasoning.Setoid as Reasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Modes
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)

open Nat.Variables

data ParSeq : Set where
  par seq : ParSeq

infix 12 _∥_ _;_

data Struct (n : ℕ) : Set where
  `_  : 𝔽 n → Struct n
  []  : Struct n
  _∥_ : Struct n → Struct n → Struct n
  _;_ : Struct n → Struct n → Struct n

private variable
  α α₁ α₂ α₃ α′ α₁′ α₂′ : Struct n
  β β₁ β₂ β₃ β′ β₁′ β₂′ : Struct n

variable
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
  renaming (refl to ≈-refl; reflexive to ≈-reflexive; sym to ≈-sym; trans to ≈-trans)
  public

module ≈-Reasoning {n} = Reasoning record { isEquivalence = ≈-isEquivalence n }

{-
≈⁻¹-[];[] : α ; β ≈ [] → α ≈ [] × β ≈ []
≈⁻¹-[];[] {α = ` x} (x₁ ◅ eq) = {!!}
≈⁻¹-[];[] {α = []} eq = refl , ≈-trans (≈-sym ;-unit₁) eq
≈⁻¹-[];[] {α = α ∥ α₁} eq = {!!}
≈⁻¹-[];[] {α = α ; α₁} eq = {!!}

≈⁻¹-; : α ≈ β ; γ → (α ≈ β × [] ≈ γ) ⊎ (α ≈ γ × [] ≈ β) ⊎ ∃[ α₁ ] ∃[ α₂ ] α ≡ α₁ ; α₂ × α₁ ≈ β × α₂ ≈ γ
≈⁻¹-; refl = inj₂ (inj₂ (_ , _ , refl , refl , refl))
≈⁻¹-; (x ◅ eq) with ≈⁻¹-; eq
... | inj₁ (α≈β , []≈γ) = inj₁ (x ◅ α≈β , []≈γ)
... | inj₂ (inj₁ (α≈γ , []≈β)) = inj₂ (inj₁ (x ◅ α≈γ , []≈β))
≈⁻¹-; (Sym.fwd ;′-unit₁ ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = inj₂ (inj₂ (_ , _ , refl , {!!} , {!!}))
≈⁻¹-; (Sym.fwd ;′-unit₂ ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.fwd ;′-assoc ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.fwd (;′-cong₁ x) ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.fwd (;′-cong₂ x) ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.fwd ∥′-unit ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.bwd ;′-unit₁ ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = inj₂ (inj₁ (γ≈ , β≈))
≈⁻¹-; (Sym.bwd ;′-unit₂ ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = inj₁ (β≈ , γ≈)
≈⁻¹-; (Sym.bwd ;′-assoc ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.bwd (;′-cong₁ x) ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
≈⁻¹-; (Sym.bwd (;′-cong₂ x) ◅ eq) | inj₂ (inj₂ (α₁ , α₂ , refl , β≈ , γ≈)) = {!!}
-}

biasedDir : ParSeq → Dir
biasedDir par = 𝟙
biasedDir seq = L

record Join (A : Set) : Set where
  field joinDir : A → Dir

  join : A → Struct n → Struct n → Struct n
  join a with joinDir a
  ... | 𝟙 = _∥_
  ... | L = _;_
  ... | R = flip _;_

  cong-join : ∀ a → α₁ ≈ α₂ → β₁ ≈ β₂ → join a α₁ β₁ ≈ join a α₂ β₂
  cong-join a with joinDir a
  ... | 𝟙 = ∥-cong
  ... | L = ;-cong
  ... | R = flip ;-cong

open Join ⦃ ... ⦄ public

instance
  join-dir : Join Dir
  join-dir = record { joinDir = id }

  join-p/s : Join ParSeq
  join-p/s = record { joinDir = biasedDir }

-- joinP/S-∅₁ : ∀ p/s → γ₁ ≈ [] → joinP/S p/s γ₁ γ₂ ≈ γ₂
-- joinP/S-∅₁ par eq = ∥-cong eq refl ◅◅ ∥-comm ◅◅ ∥-unit
-- joinP/S-∅₁ seq eq = ;-cong eq refl ◅◅ ;-unit₁

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


infix 4 _≼_

data _≼_ {n} : Rel (Struct n) 0ℓ where
  refl : α ≈ β → α ≼ β
  ≼-trans : α ≼ β → β ≼ γ → α ≼ γ
  ≼-wk : (α₁ ∥ α₂) ; (β₁ ∥ β₂) ≼ (α₁ ; β₁) ∥ (α₂ ; β₂)
  ≼-cong-; : α ≼ α′ → β ≼ β′ → α ; β ≼ α′ ; β′
  ≼-cong-∥ : α ≼ α′ → β ≼ β′ → α ∥ β ≼ α′ ∥ β′

≼-isPreorder : ∀ n → Bin.IsPreorder (_≈_ {n}) _≼_
≼-isPreorder n = record
  { isEquivalence = ≈-isEquivalence n
  ; reflexive = refl
  ; trans = ≼-trans
  }

{-
infix 4 _≺_ _≼_

data _≺_ : Struct n → Struct n → Set where
  ≺-wk : (α₁ ∥ α₂) ; (β₁ ∥ β₂) ≺ (α₁ ; β₁) ∥ (α₂ ; β₂)
  ;′-cong₁ : α ≺ α′ → α₁ ; β₁ ≺ α′ ; β
  ;′-cong₂ : β ≺ β′ → α ; β ≺ α ; β′
  ∥′-cong₁ : α ≺ α′ → α ∥ β ≺ α′ ∥ β

≺-irrefl : Bin.Irreflexive (_≈_ {n}) _≺_
≺-irrefl eq ≺-wk = {!!}
≺-irrefl eq (;′-cong₁ x) = {!!}
≺-irrefl eq (;′-cong₂ x) = {!!}
≺-irrefl eq (∥′-cong₁ x) = {!!}

_≼_ : Rel (Struct n) _
_≼_ = Star (_≈_ ∪ _≺_)

≼-antisym : Bin.Antisymmetric (_≈_ {n}) _≼_
≼-antisym x x₁ = {!!}

≼-isPartialOrder : ∀ n → Bin.IsPartialOrder (_≈_ {n}) _≼_
≼-isPartialOrder n = record
  { isPreorder = record
    { isEquivalence = ≈-isEquivalence n
    ; reflexive = Star.return ∘ inj₁
    ; trans = _◅◅_
    }
  ; antisym = ≼-antisym
  }

≼-respects-≈ : α₁ ≼ β₂ → α₁ ≈ α₂ → β₁ ≈ β₂ → α₂ ≼ β₂
≼-respects-≈ α≼β eq-α eq-β = {!!}
-}

module Substitution where

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

  ⋯-preserves-≈′ : (_⋯ σ) Bin.Preserves _≈′_ ⟶ _≈′_
  ⋯-preserves-≈′ ;′-unit₁ = ;′-unit₁
  ⋯-preserves-≈′ ;′-unit₂ = ;′-unit₂
  ⋯-preserves-≈′ ;′-assoc = ;′-assoc
  ⋯-preserves-≈′ (;′-cong₁ x) = ;′-cong₁ (⋯-preserves-≈′ x)
  ⋯-preserves-≈′ (;′-cong₂ x) = ;′-cong₂ (⋯-preserves-≈′ x)
  ⋯-preserves-≈′ ∥′-unit = ∥′-unit
  ⋯-preserves-≈′ ∥′-assoc = ∥′-assoc
  ⋯-preserves-≈′ ∥′-comm = ∥′-comm
  ⋯-preserves-≈′ (∥′-cong₁ x) = ∥′-cong₁ (⋯-preserves-≈′ x)

  ⋯-preserves-≈ : (_⋯ σ) Bin.Preserves _≈_ ⟶ _≈_
  ⋯-preserves-≈ refl = refl
  ⋯-preserves-≈ (x ◅ xs) = Sym.gmap (_⋯ _) ⋯-preserves-≈′ x ◅ ⋯-preserves-≈ xs

  join-⋯ : ∀ {A} ⦃ J : Join A ⦄ (a : A) (α β : Struct n) → join a α β ⋯ σ ≡ join a (α ⋯ σ) (β ⋯ σ)
  join-⋯ a α β with joinDir a
  ... | L = refl
  ... | R = refl
  ... | 𝟙 = refl

  cong-wk : α ≈ β → wk α ≈ wk β
  cong-wk {α = α} {β} eq rewrite sym (weaken/wk α) | sym (weaken/wk β) = ⋯-preserves-≈ eq

  ≼-⋯ : α ≼ β → α ⋯ σ ≼ β ⋯ σ
  ≼-⋯ (refl x) = refl (⋯-preserves-≈ x)
  ≼-⋯ (≼-trans x y) = ≼-trans (≼-⋯ x) (≼-⋯ y)
  ≼-⋯ ≼-wk = ≼-wk
  ≼-⋯ (≼-cong-; x y) = ≼-cong-; (≼-⋯ x) (≼-⋯ y)
  ≼-⋯ (≼-cong-∥ x y) = ≼-cong-∥ (≼-⋯ x) (≼-⋯ y)

open Substitution using
  ( ⋯-preserves-≈
  ; cong-wk
  ; join-⋯
  ; ≼-⋯
  ) public

Split : ∀ {A} → ⦃ Join A ⦄ → A → Struct n → Struct n → Struct n → Set
Split a α β γ = α ≈ join a β γ

SeqIsPure : ParSeq → Eff → Eff → Set
SeqIsPure par ϵ₁ ϵ₂ = ϵ₁ ≡ ϵ₂
SeqIsPure seq ϵ₁ ϵ₂ = ϵ₂ ≡ ℙ

pairDir : ParSeq → Dir
pairDir par = 𝟙
pairDir seq = L

Ctx = Vector 𝕋

data MobCx (Γ : Ctx n) : Struct n → Set where
  []  : MobCx Γ []
  _∥_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ∥ α₂)
  _;_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ; α₂)
  `_  : ∀ {x} → Mobile (Γ x) → MobCx Γ (` x)

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx n

mobCx-≈-fwd : MobCx Γ Bin.Respects _≈′_
mobCx-≈-fwd ∥′-unit (C ∥ C₁) = C
mobCx-≈-fwd ∥′-assoc ((C ∥ C₂) ∥ C₁) = C ∥ (C₂ ∥ C₁)
mobCx-≈-fwd ∥′-comm (C ∥ C₁) = C₁ ∥ C
mobCx-≈-fwd (∥′-cong₁ eq) (C ∥ C₁) = mobCx-≈-fwd eq C ∥ C₁
mobCx-≈-fwd ;′-unit₁ (C ; C₁) = C₁
mobCx-≈-fwd ;′-unit₂ (C ; C₁) = C
mobCx-≈-fwd ;′-assoc ((C ; C₂) ; C₁) = C ; (C₂ ; C₁)
mobCx-≈-fwd (;′-cong₁ eq) (C ; C₁) = mobCx-≈-fwd eq C ; C₁
mobCx-≈-fwd (;′-cong₂ eq) (C ; C₁) = C ; mobCx-≈-fwd eq C₁

mobCx-≈-bwd : MobCx Γ Bin.Respects (flip _≈′_)
mobCx-≈-bwd ;′-unit₁ [] = [] ; []
mobCx-≈-bwd ;′-unit₂ [] = [] ; []
mobCx-≈-bwd ∥′-unit [] = [] ∥ []
mobCx-≈-bwd ;′-unit₁ (C ∥ C₁) = [] ; (C ∥ C₁)
mobCx-≈-bwd ;′-unit₂ (C ∥ C₁) = (C ∥ C₁) ; []
mobCx-≈-bwd ∥′-unit (C ∥ C₁) = (C ∥ C₁) ∥ []
mobCx-≈-bwd ∥′-assoc (C ∥ (C₁ ∥ C₂)) = (C ∥ C₁) ∥ C₂
mobCx-≈-bwd ∥′-comm (C ∥ C₁) = C₁ ∥ C
mobCx-≈-bwd (∥′-cong₁ eq) (C ∥ C₁) = mobCx-≈-bwd eq C ∥ C₁
mobCx-≈-bwd ;′-unit₁ (C ; C₁) = [] ; (C ; C₁)
mobCx-≈-bwd ;′-unit₂ (C ; C₁) = (C ; C₁) ; []
mobCx-≈-bwd ;′-assoc (C ; (C₁ ; C₂)) = (C ; C₁) ; C₂
mobCx-≈-bwd (;′-cong₁ eq) (C ; C₁) = mobCx-≈-bwd eq C ; C₁
mobCx-≈-bwd (;′-cong₂ eq) (C ; C₁) = C ; mobCx-≈-bwd eq C₁
mobCx-≈-bwd ∥′-unit  (C ; C₁) = (C ; C₁) ∥ []
mobCx-≈-bwd ;′-unit₁ (` x) = [] ; (` x)
mobCx-≈-bwd ;′-unit₂ (` x) = (` x) ; []
mobCx-≈-bwd ∥′-unit  (` x) = (` x) ∥ []

mobCx-≈ : MobCx Γ Bin.Respects _≈_
mobCx-≈ refl C = C
mobCx-≈ (Sym.fwd x ◅ eq) C = mobCx-≈ eq (mobCx-≈-fwd x C)
mobCx-≈ (Sym.bwd x ◅ eq) C = mobCx-≈ eq (mobCx-≈-bwd x C)
