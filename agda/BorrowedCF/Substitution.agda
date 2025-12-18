module BorrowedCF.Substitution where

open import Data.List.Membership.Propositional
open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected; just; just-nothing; nothing-just; nothing)
open import Data.Tree.Binary as T using (Tree; leaf; node)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Unary.AllPairs as Pairs using (AllPairs; []; _∷_)
open import Data.Bool using (Bool; true; false)

open import BorrowedCF.Prelude
open Bin using (Reflexive; Symmetric)

open Nat.Variables

variable
  α α₁ α₂ α₃ α′ : 𝔽 n

data Const : Set where
  ⟨⟩ `new `fork
     `close `wait
     `send `recv
     `lsplit `rsplit
     `drop `acquire
       : Const

infix 9 `_

data Tm n : Set where
  K   : Const → Tm n
  `_  : (α : 𝔽 n) → Tm n
  `λ  : (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _⊗_ : (e₁ e₂ : Tm n) → Tm n
  let-` : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  let-⊗ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n
  `inl `inr : (e : Tm n) → Tm n
  `case_of[_⇒_,_⇒_] : (e : Tm n) (e₁ : Tm (1 + n)) (e₂ : Tm (1 + n)) → Tm n

data Dir : Set where
  ‼ ⁇ : Dir

data Mode : Set where
  owned borrowed : Mode

data Mobility : Set where
  mobile static : Mobility

data Direction : Set where
  L R 𝟙 : Direction

data Effect : Set where
  ℙ 𝕀 : Effect

data Ty : Set

data 𝕊 n : Set where
  ε : 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  end : (⁉ : Dir) (m : Mode) → 𝕊 n
  msg : (⁉ : Dir) (t : Ty) → 𝕊 n
  branch : (⁉ : Dir) (s₁ s₂ : 𝕊 n) → 𝕊 n
  `_  : (α : 𝔽 n) → 𝕊 n
  μ   : (s : 𝕊 (1 + n)) → 𝕊 n

data Ty where
  `⊤ : Ty
  arr : (m : Mobility) (d : Direction) (ℯ : Effect) (t₁ t₂ : Ty) → Ty
  _`+_ : (t₁ t₂ : Ty) → Ty
  S  : (s : 𝕊 0) → Ty

Ctxt : ℕ → Set
Ctxt n = (α : 𝔽 n) → Maybe Ty

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : Ty
  s s₁ s₂ s₃ s′ : 𝕊 n
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctxt n

data ParSeq : Set where
  par seq : ParSeq

T : ℕ → Set
T n = Tree ParSeq (𝔽 n)

data _≃_ {n} : Rel (T n) 0ℓ where
  leaf : leaf α ≃ leaf α
  node : ∀ {l l′ x r r′} → l ≃ l′ → r ≃ r′ → node l x r ≃ node l′ x r′
  assoc : ∀ {t₁ t₂ t₃ x} → node (node t₁ x t₂) x t₃ ≃ node t₁ x (node t₂ x t₃)
  par-sym : ∀ {t₁ t₂} → node t₁ par t₂ ≃ node t₂ par t₁

-- Unique : ∀ {a} {A : Set a} → List (Maybe A) → Set _
-- Unique = AllPairs (Connected _≢_)

-- Structure : T n → Set
-- Structure t = Unique (T.Leaves.toList t)

-- data Split {n} : ParSeq → T n → T n → T n → Set where
--   left : ∀ {ps t} → Split ps t t (leaf nothing)
--   right : ∀ {ps t} → Split ps (leaf nothing) t t
--   seq : ∀ {l r} → Split seq (node l seq r) l r
--   --par

-- infix 4 _⊢_∶_ _∋_∶_

-- _∋_∶_ : Ctxt n → 𝔽 n → Ty → Set
-- Γ ∋ α ∶ t = Γ α ≡ just t

-- data _⊢_∶_ (Γ : Ctxt n) : Tm n → Ty → Set where
--   ⊢` :
--     Γ ∋ α ∶ t →
--     -----------
--     Γ ⊢ ` α ∶ t
