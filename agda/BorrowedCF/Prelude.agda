module BorrowedCF.Prelude where

import Level as StdlibLevel
import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality

open module ≡ = Relation.Binary.PropositionalEquality
  renaming (trans to infixr 1 _■_)
  hiding ([_])
  public

open module ≅ = Relation.Binary.HeterogeneousEquality
  using (_≅_; refl; ≅-to-≡; ≡-to-≅; ≅-to-type-≡; ≅-to-subst-≡; module ≅-Reasoning)
  public

open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant) public

module Level = StdlibLevel
open Level
  using (Level; 0ℓ)
  renaming (_⊔_ to _⊔ℓ_)
  public

open import Function
  hiding (id; seq)
  public

import Data.Unit
import Data.Unit.Polymorphic
open module Unit  = Data.Unit
  using (⊤; tt) public
open module ↑Unit = Data.Unit.Polymorphic
  using () renaming (⊤ to ↑⊤; tt to ↑tt) public

open import Data.Empty
  using (⊥; ⊥-elim; ⊥-elim-irr)
  public

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public

  module Variables where
    variable m m₁ m₂ m₃ n n₁ n₂ n₃ k k₁ k₂ m′ n′ : ℕ

open Nat
  using (ℕ; zero; suc; _+_; +-identityʳ; +-suc; +-assoc)
  renaming (suc-injective to suc⁻¹)
  public

module Fin where
  open import Data.Fin public
  open import Data.Fin.Properties public

  ↑ˡ≢↑ʳ : ∀ {m} {x : Fin m} {n} {y : Fin n} → x ↑ˡ n ≢ m ↑ʳ y
  ↑ˡ≢↑ʳ {suc m} {suc x} {suc n} {y} eq = ↑ˡ≢↑ʳ (suc-injective eq)

  cast-swap : ∀ {m n} .(eq : m ≡ n) i j → cast eq i ≡ j → i ≡ cast (sym eq) j
  cast-swap m≡n i j eq = sym (cast-involutive (sym m≡n) m≡n i) ■ cong (cast (sym m≡n)) eq

open Fin
  using ( zero; suc; _↑ˡ_; _↑ʳ_; ↑ˡ≢↑ʳ
        ; ↑ˡ-injective; ↑ʳ-injective
        ; splitAt; join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
        )
  renaming (Fin to 𝔽) public

module L where
  open import Data.List public
  open import Data.List.Properties public

open L using (List; []; _∷_; _++_) public

module V where
  open import Data.Vec public
  open import Data.Vec.Properties public

  record IsMapOp {a b c} {A : Set a} {B : Set b} {C : Set c}
                 (f* : ∀ {k} → Vec A k → B → Vec C k)
                 (f : A → B → C)
                 : Set (a ⊔ℓ b ⊔ℓ c)
    where
    field
      cong-[] : ∀ b → f* [] b ≡ []
      cong-∷  : ∀ {k} a as b → f* {suc k} (a ∷ as) b ≡ f a b ∷ f* as b

    map-≡ : ∀ {k} as b → f* {k} as b ≡ map (_⟨ f ⟩ b) as
    map-≡ []       b = cong-[] b
    map-≡ (a ∷ as) b = cong-∷ a as b ■ cong (_ ∷_) (map-≡ as b)

    lookup-map′ : ∀ {k} as b (i : 𝔽 k) → lookup (f* as b) i ≡ f (lookup as i) b
    lookup-map′ as b i = cong (λ as′ → lookup as′ i) (map-≡ as b) ■ lookup-map i (_⟨ f ⟩ b) as

open V using (Vec; []; _∷_; lookup; lookup-map; ∷-injective; IsMapOp) public
open V.IsMapOp ⦃ … ⦄ using (map-≡; lookup-map′) public

module Π where
  open import Data.Product public
  open import Data.Product.Properties public

open Π using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∄; curry; uncurry) public

module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

open Sum
  using ( _⊎_; inj₁; inj₂; inj₁-injective; inj₂-injective
        ; [_,_]; [_,_]′; [,]-∘; [,]-cong; [-,]-cong; [,-]-cong; [,]-map
        )
  public

import Relation.Binary
import Relation.Unary

open module Bin = Relation.Binary
  using (REL; Rel; DecidableEquality; IsEquivalence; Setoid; DecSetoid; Symmetric; Transitive)
  public

open module Un = Relation.Unary
  using (Pred)
  public

open import Data.Bool using (true; false) public
open import Relation.Nullary public

Π/+ : ℕ × ℕ → ℕ
Π/+ (m , n) = m + n

IsMapOp₁ : ∀ {a b} {A : Set a} {B : Set b} → (∀ {k} → Vec A k → Vec B k) → (A → B) → Set _
IsMapOp₁ f* f = ∀ {k} → f* {k} ≗ V.map f

IsMapOp₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (∀ {k} → Vec A k → B → Vec C k) → (A → B → C) → Set _
IsMapOp₂ f* f = ∀ {k} as b → f* {k} as b ≡ V.map (_⟨ f ⟩ b) as

infix 1 IsMapOp₁ IsMapOp₂

syntax IsMapOp₂ {A = A} {B} f* f = f* Lifts f on A × B
