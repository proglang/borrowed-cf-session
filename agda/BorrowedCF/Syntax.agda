{-# OPTIONS --rewriting #-}

module BorrowedCF.Syntax where

open import Data.Bool using () renaming (Bool to Flag; true to set; false to unset) public
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)

open import BorrowedCF.Prelude
open import BorrowedCF.Kits as Kits hiding (module Syntax)

variable st : SortTy

data ProcKind : Set where
  ty un : ProcKind

variable pk : ProcKind

data Sort : SortTy → Set where
  𝕜 : Sort NoVar
  𝕥 : Sort NoVar
  𝕤 : Sort Var
  𝕖 : Sort Var
  𝕡 : ProcKind → Sort NoVar
  𝕗 : Sort Var

variable 𝔰 𝔰₁ 𝔰₂ 𝔰₃ 𝔰′ : Sort st

data Pol : Set where
  ‼ ⁇ : Pol

variable p p₁ p₂ p′ : Pol

data Dir : Set where
  L R 𝟙 : Dir

variable d d₁ d₂ : Dir

data Mob : Set where
  𝓜 𝓢 : Mob

data Eff : Set where
  ℙ 𝕀 : Eff

variable ϵ ϵ₁ ϵ₂ ϵ₃ ϵ′ : Eff

data _≤ϵ_ : Rel Eff 0ℓ where
  ℙ≤ϵ : ℙ ≤ϵ ϵ
  𝕀≤𝕀 : 𝕀 ≤ϵ 𝕀

≤ϵ-refl : ϵ ≤ϵ ϵ
≤ϵ-refl {ℙ} = ℙ≤ϵ
≤ϵ-refl {𝕀} = 𝕀≤𝕀

data Lin : Set where
  𝟙 unr : Lin

record Arr : Set where
  constructor arr
  field
    lin : Lin
    dir : Dir
    mob : Mob
    eff : Eff

  Mobile = mob ≡ 𝓜
  Unr = lin ≡ unr
  Par = dir ≡ 𝟙

  field
    ω⇒M : Unr → Mobile
    ω⇒𝟙 : Unr → Par

variable
   a a₁ a₂ : Arr

Scope = List (Sort Var)

variable
  S S₁ S₂ S₃ S′ : Scope

BindGroup = List ℕ

bgScope : BindGroup → Scope
bgScope = L.concatMap (flip L.replicate 𝕖)

record 𝕖⊎𝕤 (𝔰 : Sort Var) : Set where
  field ev : 𝔰 ≡ 𝕖 ⊎ 𝔰 ≡ 𝕤

instance
  𝕖⊎𝕤-𝕖 : 𝕖⊎𝕤 𝕖
  𝕖⊎𝕤-𝕖 = record { ev = inj₁ refl }

  𝕖⊎𝕤-𝕤 : 𝕖⊎𝕤 𝕤
  𝕖⊎𝕤-𝕤 = record { ev = inj₂ refl }

infix 4 _⊢_

infix  13 `_
infix  12 _↦_
infixl 12 _·_ _;_
infix  12 _;₁_ _;₂_ _;₁-
infixr 12 _⟨_⟩→_ _⊗⟨_⟩_ _⊗¹_ _⊗ᴸ_ _⊗_ _→1𝓜_∣_ _`→_
infixr 11 `let⊗_`in_
infixl 10 _∥_

mutual
  data Const : Set where
    `unit `fork `send `recv `drop `acq : Const
    `end : Pol → Const
    `new : [] ⊢ 𝕤 → Const
    `lsplit `rsplit : [] ⊢ 𝕤 → Const

  data _⊢_ (S : Scope) : Sort st → Set where
    `_ : 𝔰 ∈ S → S ⊢ 𝔰

    ⋆ : S ⊢ 𝕜

    ⟨_⟩ : (s : S ⊢ 𝕤) → S ⊢ 𝕥
    `⊤  : S ⊢ 𝕥
    _⟨_⟩→_ : (t : S ⊢ 𝕥) (a : Arr) (u : S ⊢ 𝕥) → S ⊢ 𝕥
    _⊗⟨_⟩_ : (t : S ⊢ 𝕥) (d : Dir) (u : S ⊢ 𝕥) → S ⊢ 𝕥

    end : (p : Pol) → S ⊢ 𝕤
    msg : (p : Pol) (t : [] ⊢ 𝕥) → S ⊢ 𝕤
    brn : (p : Pol) (s₁ s₂ : S ⊢ 𝕤) → S ⊢ 𝕤
    skip ret acq : S ⊢ 𝕤

    μ : .⦃ 𝕖⊎𝕤 𝔰 ⦄ → 𝔰 ∷ S ⊢ 𝔰 → S ⊢ 𝔰
    _;_ : .⦃ 𝕖⊎𝕤 𝔰 ⦄ → (x₁ x₂ : S ⊢ 𝔰) → S ⊢ 𝔰

    K : (c : Const) → S ⊢ 𝕖
    ƛ : (e : 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖
    _⊗_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
    _·_ : (e₁ e₂ : S ⊢ 𝕖) → S ⊢ 𝕖
    `let⊗_`in_ : (e₁ : S ⊢ 𝕖) (e₂ : 𝕖 ∷ 𝕖 ∷ S ⊢ 𝕖) → S ⊢ 𝕖

    ⟪_⟫ : (e : S ⊢ 𝕖) → S ⊢ 𝕡 pk
    _∥_ : (P Q : S ⊢ 𝕡 pk) → S ⊢ 𝕡 pk

    ν[_][_] : (B₁ B₂ : List ℕ) (P : bgScope B₁ ++ bgScope B₂ ++ S ⊢ 𝕡 ty) → S ⊢ 𝕡 ty

    ν : (P : 𝕖 ∷ 𝕖 ∷ S ⊢ 𝕡 un) → S ⊢ 𝕡 un
    φ : (P : 𝕗 ∷ S ⊢ 𝕡 un) → S ⊢ 𝕡 un
    _↦_ : (x : S ⊢ 𝕗) (⁰/₁ : Flag) → S ⊢ 𝕡 un

  pattern _⊗¹_ T U = T ⊗⟨ 𝟙 ⟩ U
  pattern _⊗ᴸ_ T U = T ⊗⟨ L ⟩ U

  _→1𝓜_∣_ : S ⊢ 𝕥 → S ⊢ 𝕥 → Eff → S ⊢ 𝕥
  _→1𝓜_∣_ T U e = T ⟨ arr unr 𝟙 𝓜 e (λ _ → refl) (λ _ → refl) ⟩→ U

variable
  s s₁ s₂ s₃ s′ : S ⊢ 𝕤
  e e₁ e₂ e₃ e′ : S ⊢ 𝕥
  T T₁ T₂ T₃ T′ : S ⊢ 𝕥
  U U₁ U₂ U₃ U′ : S ⊢ 𝕥

open module Syntax = Kits.Syntax record
  { Sort = Sort
  ; _⊢_ = λ S 𝔰 → S ⊢ 𝔰
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Sort; _⊢_; `_; Traversal)
  renaming (id to idₖ)
  public

infixl 15 _⋯_

_⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ → S ⊢ 𝔰 → S –[ K ]→ S′ → S′ ⊢ 𝔰
(` x) ⋯ ϕ = `/id (ϕ _ x)
⋆ ⋯ ϕ = ⋆
⟨ s ⟩ ⋯ ϕ = ⟨ s ⋯ ϕ ⟩
`⊤ ⋯ ϕ = `⊤
(T ⟨ a ⟩→ U) ⋯ ϕ = T ⋯ ϕ ⟨ a ⟩→ U ⋯ ϕ
(T ⊗⟨ d ⟩ U) ⋯ ϕ = T ⋯ ϕ ⊗⟨ d ⟩ U ⋯ ϕ
end p ⋯ ϕ = end p
msg p T ⋯ ϕ = msg p T
brn p s₁ s₂ ⋯ ϕ = brn p (s₁ ⋯ ϕ) (s₂ ⋯ ϕ)
skip ⋯ ϕ = skip
ret ⋯ ϕ = ret
acq ⋯ ϕ = acq
μ s ⋯ ϕ = μ (s ⋯ ϕ ↑ _)
(x/t₁ ; x/t₂) ⋯ ϕ = (x/t₁ ⋯ ϕ) ; (x/t₂ ⋯ ϕ)
K c ⋯ ϕ = K c
ƛ x/t ⋯ ϕ = ƛ (x/t ⋯ ϕ ↑ _)
(x/t₁ ⊗ x/t₂) ⋯ ϕ = x/t₁ ⋯ ϕ ⊗ x/t₂ ⋯ ϕ
(x/t₁ · x/t₂) ⋯ ϕ = x/t₁ ⋯ ϕ · x/t₂ ⋯ ϕ
(`let⊗ x/t `in x/t′) ⋯ ϕ = `let⊗ x/t ⋯ ϕ `in x/t′ ⋯ ϕ ↑ _ ↑ _
⟪ x/t ⟫ ⋯ ϕ = ⟪ x/t ⋯ ϕ ⟫
(x/t₁ ∥ x/t₂) ⋯ ϕ = (x/t₁ ⋯ ϕ) ∥ (x/t₂ ⋯ ϕ)
ν[ B₁ ][ B₂ ] x/t ⋯ ϕ = ν[ B₁ ][ B₂ ] (x/t ⋯ ϕ ↑* bgScope B₂ ↑* bgScope B₁)
ν x/t ⋯ ϕ = ν (x/t ⋯ ϕ ↑ _ ↑ _)
φ x/t ⋯ ϕ = φ (x/t ⋯ ϕ ↑ _)
(x/t ↦ ⁰/₁) ⋯ ϕ = x/t ⋯ ϕ ↦ ⁰/₁

⋯-id : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S ⊢ 𝔰) → x/t ⋯ idₖ ≡ x/t
⋯-id (` x) = `/`-is-` x
⋯-id ⋆ = refl
⋯-id ⟨ s ⟩ = cong ⟨_⟩ (⋯-id s)
⋯-id `⊤ = refl
⋯-id (T ⟨ a ⟩→ U) = cong₂ _⟨ a ⟩→_ (⋯-id T) (⋯-id U)
⋯-id (T ⊗⟨ d ⟩ U) = cong₂ _⊗⟨ d ⟩_ (⋯-id T) (⋯-id U)
⋯-id (end p) = refl
⋯-id (msg p T) = refl
⋯-id (brn p s₁ s₂) = cong₂ (brn p) (⋯-id s₁) (⋯-id s₂)
⋯-id skip = refl
⋯-id ret = refl
⋯-id acq = refl
⋯-id (μ s) = cong μ (cong (s ⋯_) (∼-ext id↑∼id) ■ ⋯-id s)
⋯-id (x/t₁ ; x/t₂) = cong₂ _;_ (⋯-id x/t₁) (⋯-id x/t₂)
⋯-id (K c) = refl
⋯-id (ƛ x/t) = cong ƛ (cong (x/t ⋯_) (∼-ext id↑∼id) ■ ⋯-id x/t)
⋯-id (x/t₁ ⊗ x/t₂) = cong₂ _⊗_ (⋯-id x/t₁) (⋯-id x/t₂)
⋯-id (x/t₁ · x/t₂) = cong₂ _·_ (⋯-id x/t₁) (⋯-id x/t₂)
⋯-id (`let⊗ x/t `in x/t′) = cong₂ `let⊗_`in_ (⋯-id x/t) (cong (x/t′ ⋯_) (∼-ext (id↑*∼id (_ ∷ L.[ _ ]))) ■ ⋯-id x/t′)
⋯-id ⟪ x/t ⟫ = cong ⟪_⟫ (⋯-id x/t)
⋯-id (x/t₁ ∥ x/t₂) = cong₂ _∥_ (⋯-id x/t₁) (⋯-id x/t₂)
⋯-id (ν[ B₁ ][ B₂ ] x/t) = cong ν[ B₁ ][ B₂ ] $
  cong (λ ϕ → x/t ⋯ ϕ ↑* bgScope B₁) (∼-ext (id↑*∼id (bgScope B₂)))
    ■ cong (x/t ⋯_) (∼-ext (id↑*∼id (bgScope B₁)))
    ■ ⋯-id x/t
⋯-id (ν x/t) = cong ν (cong (x/t ⋯_) (∼-ext (id↑*∼id (_ ∷ L.[ _ ]))) ■ ⋯-id x/t)
⋯-id (φ x/t) = cong φ (cong (x/t ⋯_) (∼-ext id↑∼id) ■ ⋯-id x/t)
⋯-id (x/t ↦ ⁰/₁) = cong (_↦ ⁰/₁) (⋯-id x/t)

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  }
  hiding (_⋯_; ⋯-id; CTraversal)
  public

fusion :
  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
  ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
  (x/t : S₁ ⊢ 𝔰) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
    x/t ⋯ ϕ₁ ⋯ ϕ₂ ≡ x/t ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
fusion ⋆ ϕ₁ ϕ₂ = refl
fusion ⟨ x/t ⟩ ϕ₁ ϕ₂ = cong ⟨_⟩ (fusion x/t ϕ₁ ϕ₂)
fusion `⊤ ϕ₁ ϕ₂ = refl
fusion (x/t ⟨ a ⟩→ x/t₁) ϕ₁ ϕ₂ = cong₂ _⟨ a ⟩→_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (x/t ⊗⟨ d ⟩ x/t₁) ϕ₁ ϕ₂ = cong₂ _⊗⟨ d ⟩_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (end p) ϕ₁ ϕ₂ = refl
fusion (msg p x/t) ϕ₁ ϕ₂ = refl
fusion (brn p x/t x/t₁) ϕ₁ ϕ₂ = cong₂ (brn p) (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion skip ϕ₁ ϕ₂ = refl
fusion ret ϕ₁ ϕ₂ = refl
fusion acq ϕ₁ ϕ₂ = refl
fusion (μ x/t) ϕ₁ ϕ₂ = cong μ $
  fusion x/t (ϕ₁ ↑ _) (ϕ₂ ↑ _) ■ sym (⋯-cong x/t (dist-↑-· _ ϕ₁ ϕ₂))
fusion (x/t ; x/t₁) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (K c) ϕ₁ ϕ₂ = refl
fusion (ƛ x/t) ϕ₁ ϕ₂ = cong ƛ $
  (fusion x/t (ϕ₁ ↑ _) (ϕ₂ ↑ _) ■ sym (⋯-cong x/t (dist-↑-· _ ϕ₁ ϕ₂)))
fusion (x/t ⊗ x/t₁) ϕ₁ ϕ₂ = cong₂ _⊗_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (x/t · x/t₁) ϕ₁ ϕ₂ = cong₂ _·_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (`let⊗ x/t `in x/t₁) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion x/t ϕ₁ ϕ₂) $
  fusion x/t₁ (ϕ₁ ↑* _) (ϕ₂ ↑* _) ■ sym (⋯-cong x/t₁ (dist-↑*-· _ ϕ₁ ϕ₂))
fusion ⟪ x/t ⟫ ϕ₁ ϕ₂ = cong ⟪_⟫ (fusion x/t ϕ₁ ϕ₂)
fusion (x/t ∥ x/t₁) ϕ₁ ϕ₂ = cong₂ _∥_ (fusion x/t ϕ₁ ϕ₂) (fusion x/t₁ ϕ₁ ϕ₂)
fusion (ν[ B₁ ][ B₂ ] x/t) ϕ₁ ϕ₂ = cong ν[ B₁ ][ B₂ ] $
  fusion x/t (ϕ₁ ↑* bgScope B₂ ↑* bgScope B₁) (ϕ₂ ↑* bgScope B₂ ↑* bgScope B₁)
    ■ sym (⋯-cong x/t (dist-↑*-· (bgScope B₁) (ϕ₁ ↑* _) (ϕ₂ ↑* _)))
    ■ cong (λ ϕ → x/t ⋯ ϕ ↑* bgScope B₁) (sym (∼-ext (dist-↑*-· (bgScope B₂) ϕ₁ ϕ₂)))
fusion (ν x/t) ϕ₁ ϕ₂ = cong ν $
  fusion x/t (ϕ₁ ↑* _) (ϕ₂ ↑* _) ■ sym (⋯-cong x/t (dist-↑*-· _ ϕ₁ ϕ₂))
fusion (φ x/t) ϕ₁ ϕ₂ = cong φ $
  fusion x/t (ϕ₁ ↑ _) (ϕ₂ ↑ _) ■ sym (⋯-cong x/t (dist-↑-· _ ϕ₁ ϕ₂))
fusion (x/t ↦ ⁰/₁) ϕ₁ ϕ₂ = cong (_↦ _) (fusion x/t ϕ₁ ϕ₂)

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

dualPol : Pol → Pol
dualPol ‼ = ⁇
dualPol ⁇ = ‼

dualPol-involutive : dualPol ∘ dualPol ≗ id
dualPol-involutive ‼ = refl
dualPol-involutive ⁇ = refl

{-# REWRITE dualPol-involutive #-}

dual : S ⊢ 𝕤 → S ⊢ 𝕤
dual (` x) = ` x
dual (end p) = end (dualPol p)
dual (msg p T) = msg (dualPol p) T
dual (brn p s₁ s₂) = brn (dualPol p) (dual s₁) (dual s₂)
dual skip = skip
dual ret = ret
dual acq = acq
dual (μ s) = μ (dual s)
dual (s₁ ; s₂) = dual s₁ ; dual s₂

dual-involutive : dual {S} ∘ dual ≗ id
dual-involutive (` x) = refl
dual-involutive (end p) = refl
dual-involutive (msg p t) = refl
dual-involutive (brn p s₁ s₂) = cong₂ (brn p) (dual-involutive s₁) (dual-involutive s₂)
dual-involutive (μ s) = cong μ (dual-involutive s)
dual-involutive (s₁ ; s₂) = cong₂ _;_ (dual-involutive s₁) (dual-involutive s₂)
dual-involutive skip = refl
dual-involutive ret = refl
dual-involutive acq = refl

{-# REWRITE dual-involutive #-}

data Skips {S} : S ⊢ 𝕤 → Set where
  skip : Skips skip
  _;_ : (S₁ : Skips s₁) (S₂ : Skips s₂) → Skips (s₁ ; s₂)
  μ : (S : Skips s) → Skips (μ s)

data Bounded {S} : S ⊢ 𝕤 → Set where
  `_   : ∀ x → Bounded (` x)
  end  : Bounded (end p)
  ret  : Bounded ret
  _;₁_ : (B : Bounded s₁) (S : Skips s₂) → Bounded (s₁ ; s₂)
  _;₂_ : (B : Bounded s₂) → Bounded (s₁ ; s₂)
  μ    : (B : Bounded s) → Bounded (μ s)
  brn  : (B₁ : Bounded s₁) (B₂ : Bounded s₂) → Bounded (s₁ ; s₂)

data Mobile {S} : S ⊢ 𝕥 → Set where
  `⊤ : Mobile `⊤
  arr : (M : Arr.Mobile a) → Mobile (T ⟨ a ⟩→ U)
  acq : (B : Bounded s) → Mobile ⟨ acq ; s ⟩
  skip : (S : Skips s) → Mobile ⟨ s ⟩
  _⊗_ : (M₁ : Mobile T) (M₂ : Mobile U) → Mobile (T ⊗⟨ d ⟩ U)

data Unr {S} : S ⊢ 𝕥 → Set where
  `⊤  : Unr `⊤
  arr : (unr : Arr.Unr a) → Unr (T ⟨ a ⟩→ U)
  ⟨_⟩ : (S : Skips s) → Unr ⟨ s ⟩
  _⊗_ : (unr₁ : Unr T) (unr₂ : Unr U) → Unr (T ⊗⟨ d ⟩ U)

data New {S} : S ⊢ 𝕤 → Set where
  `_ : ∀ x → New (` x)
  end : New (end p)
  skip : New skip
  msg : New (msg p T)
  μ : New s → New (μ s)
  _;_ : New s₁ → New s₂ → New (s₁ ; s₂)
  brn : New s₁ → New s₂ → New (brn p s₁ s₂)

infix 4 ⊢_∶_

data ⊢_∶_ : Const → [] ⊢ 𝕥 → Set where
  `unit : ⊢ `unit ∶ `⊤

  `fork : ⊢ `fork ∶ (`⊤ →1𝓜 `⊤ ∣ 𝕀) →1𝓜 `⊤ ∣ ℙ

  `new  : New s → Bounded s →
    ⊢ `new s ∶ `⊤ →1𝓜 ⟨ acq ; s ⟩ ⊗¹ ⟨ acq ; dual s ⟩ ∣ ℙ

  `lsplit : ⊢ `lsplit s ∶ ⟨ s ; s′ ⟩ →1𝓜 ⟨ s ⟩       ⊗ᴸ ⟨ s′ ⟩       ∣ ℙ
  `rsplit : ⊢ `rsplit s ∶ ⟨ s ; s′ ⟩ →1𝓜 ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; s′ ⟩ ∣ ℙ

  `drop : ⊢ `drop ∶ ⟨ ret ⟩     →1𝓜 `⊤    ∣ ℙ
  `acq  : ⊢ `acq  ∶ ⟨ acq ; s ⟩ →1𝓜 ⟨ s ⟩ ∣ ℙ

  `send : Mobile T → ⊢ `send ∶ T ⊗¹ ⟨ msg ‼ T ⟩ →1𝓜 `⊤ ∣ 𝕀
  `recv : Mobile T → ⊢ `recv ∶ ⟨ msg ⁇ T ⟩ →1𝓜 T ∣ 𝕀

  `end  : ⊢ `end p ∶ ⟨ end p ⟩ →1𝓜 `⊤ ∣ 𝕀

infix 4 𝓒_·_

data 𝓒_·_ (x : 𝕤 ∈ S) : S ⊢ 𝕤 → Set where
  `_ : ∀ {y : 𝕤 ∈ S} → .(x ≢ y) → 𝓒 x · ` y
  μ : 𝓒 there x · s → 𝓒 x · μ s
  _;₁- : ¬ Skips s₁ × 𝓒 x · s₁ → 𝓒 x · s₁ ; s₂
  _;₂_ : Skips s₁ → 𝓒 x · s₂ → 𝓒 x · s₁ ; s₂
  msg : 𝓒 x · msg p T
  brn : 𝓒 x · brn p s₁ s₂
  skip : 𝓒 x · skip

infix 4 ⊢_⋆

data ⊢_⋆ {S} : S ⊢ 𝕥 → Set where
  `⊤ : ⊢ `⊤ ⋆
  _`→_ : ⊢ T ⋆ → ⊢ U ⋆ → ⊢ T ⟨ a ⟩→ U ⋆
  _⊗_  : ⊢ T ⋆ → ⊢ U ⋆ → ⊢ T ⊗⟨ d ⟩ U ⋆

open Un

unr⇒mobile : Unr {S} ⊆ Mobile
unr⇒mobile `⊤ = `⊤
unr⇒mobile (arr {a} U) = arr (Arr.ω⇒M a U)
unr⇒mobile ⟨ S ⟩ = skip S
unr⇒mobile (x ⊗ x₁) = unr⇒mobile x ⊗ unr⇒mobile x₁

skips? : Decidable (Skips {S})
skips? (` x) = no λ()
skips? (end p) = no λ()
skips? (msg p s) = no λ()
skips? (brn p s s₁) = no λ()
skips? skip = yes skip
skips? ret = no λ()
skips? acq = no λ()
skips? (μ s) = map′ μ (λ{ (μ S) → S }) (skips? s)
skips? (s₁ ; s₂) = map′ (uncurry _;_) (λ{ (S₁ ; S₂) → (S₁ , S₂) }) (skips? s₁ ×-dec skips? s₂)

unr? : Decidable (Unr {S})
unr? ⟨ s ⟩ = map′ ⟨_⟩ (λ{ ⟨ S ⟩ → S }) (skips? s)
unr? `⊤ = yes `⊤
unr? (T ⟨ record { lin = 𝟙   } ⟩→ U) = no λ{ (arr ()) }
unr? (T ⟨ record { lin = unr } ⟩→ U) = yes (arr refl)
unr? (T ⊗⟨ d ⟩ U) = map′ (uncurry _⊗_) (λ{ (unrT ⊗ unrU) → unrT , unrU }) (unr? T ×-dec unr? U)
