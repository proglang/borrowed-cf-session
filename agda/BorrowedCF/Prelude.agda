{-# OPTIONS --rewriting #-}
module BorrowedCF.Prelude where

open import Agda.Builtin.Equality.Rewrite public

import Level as StdlibLevel
import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality

open module ≡ = Relation.Binary.PropositionalEquality
  renaming (trans to infixr 1 _■_)
  hiding ([_]; J)
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
  hiding (seq; _⟨_⟩_)
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

module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

  private variable ℓ : Level
  private variable A B C : Set ℓ

  [,]-swap : {f : A → C} {g : B → C} → [ f , g ] ∘ swap ≗ [ g , f ]
  [,]-swap (inj₁ x) = refl
  [,]-swap (inj₂ y) = refl

open Sum
  using ( _⊎_; inj₁; inj₂; inj₁-injective; inj₂-injective
        ; [_,_]; [_,_]′; [,]-∘; [,]-cong; [-,]-cong; [,-]-cong; [,]-map; [,]-swap
        )
  public

module Fin where
  open import Data.Fin public
  open import Data.Fin.Properties public

  import Data.Fin.Patterns
  module Patterns = Data.Fin.Patterns

  open Nat using () renaming (_+_ to _+ℕ_)
  open Nat.Variables

  ↑ˡ≢↑ʳ : ∀ {m} {x : Fin m} {n} {y : Fin n} → x ↑ˡ n ≢ m ↑ʳ y
  ↑ˡ≢↑ʳ {suc m} {suc x} {suc n} {y} eq = ↑ˡ≢↑ʳ (suc-injective eq)

  cast-swap : ∀ {m n} .(eq : m ≡ n) i j → cast eq i ≡ j → i ≡ cast (sym eq) j
  cast-swap m≡n i j eq = sym (cast-involutive (sym m≡n) m≡n i) ■ cong (cast (sym m≡n)) eq

  swap : ∀ m {n} → Fin (m +ℕ n) → Fin (n +ℕ m)
  swap m = join _ _ ∘ Sum.swap ∘ splitAt m

  swap-involutive : ∀ m {n} (x : Fin (m +ℕ n)) → swap n (swap m x) ≡ x
  swap-involutive m {n} x = let open ≡-Reasoning in
    swap n (swap m x)
      ≡⟨⟩
    join m n (Sum.swap (splitAt n (join n m (Sum.swap (splitAt m x)))))
      ≡⟨ cong (join m n ∘ Sum.swap) (splitAt-join n m (Sum.swap (splitAt m x))) ⟩
    join m n (Sum.swap (Sum.swap (splitAt m x)))
      ≡⟨ cong (join m n) (Sum.swap-involutive (splitAt m x)) ⟩
    join m n (splitAt m x)
      ≡⟨ join-splitAt m n x ⟩
    x ∎

{-
  assocˡ : ∀ n₁ n₂ {n₃} → Fin (n₁ +ℕ (n₂ +ℕ n₃)) → Fin ((n₁ +ℕ n₂) +ℕ n₃)
  assocˡ n₁ n₂ = [ {!!} ∘ {!!} , join (n₁ +ℕ n₂) _ ∘ Sum.map₁ (n₁ ↑ʳ_) ∘ splitAt n₂ ]′ ∘ splitAt n₁

  assocʳ : ∀ n₁ n₂ {n₃} → Fin ((n₁ +ℕ n₂) +ℕ n₃) → Fin (n₁ +ℕ (n₂ +ℕ n₃))
  assocʳ = {!!}

  assocˡʳ-id : ∀ n₁ n₂ {n₃} → assocˡ n₁ n₂ {n₃} ∘ assocʳ n₁ n₂ ≗ id
  assocˡʳ-id = {!!}
-}

open Fin
  using ( zero; suc; _↑ˡ_; _↑ʳ_; ↑ˡ≢↑ʳ
        ; ↑ˡ-injective; ↑ʳ-injective
        ; splitAt; join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
        )
  renaming (Fin to 𝔽) public

module L where
  open import Data.List public
  open import Data.List.Properties public

  [2*_] : ∀ {a} {A : Set a} → A → List A
  [2* x ] = x ∷ x ∷ []

open L using (List; []; _∷_; _++_; [2*_]) public

module L⁺ where
  open import Data.List.NonEmpty public
  open import Data.List.NonEmpty.Properties public

open L⁺ using (List⁺; _∷_; _∷⁺_) public

module V where
  open import Data.Vec public
  open import Data.Vec.Properties public

open V using (Vec; []; _∷_; lookup; lookup-map; ∷-injective) public

module Π where
  open import Data.Product public
  open import Data.Product.Properties public

open Π using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∄; ∃-syntax; curry; uncurry) public

import Relation.Binary
import Relation.Unary

open module Bin = Relation.Binary
  using (REL; Rel; DecidableEquality; IsEquivalence; Setoid; DecSetoid; Symmetric; Transitive)
  public

open module Un = Relation.Unary
  using (Pred)
  public

open import Data.Bool using (if_then_else_; Bool; true; false) public
open import Relation.Nullary public

if[_]_then_else_ : ∀ {a p} {A : Set a} (P : A → Set p) (b : Bool) {a₁ a₂} → P a₁ → P a₂ → P (if b then a₁ else a₂)
if[ P ] true  then x else y = x
if[ P ] false then x else y = y
