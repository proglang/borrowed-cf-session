module BorrowedCF.Context.Equivalence where

open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd; symmetric)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import BorrowedCF.Prelude hiding (_⟶_)
open import BorrowedCF.Context.Base
open import BorrowedCF.Types

open Nat.Variables
open Bin

open Variables

open Star using (_◅◅_) renaming (ε to refl) public
open Star using (Star; _◅_; kleisliStar)

infix 4 _∶_≈′_

data _∶_≈′_ (Γ : Ctx n) : Struct n → Struct n → Set where
  ;′-unit₁ : Γ ∶ [] ; α ≈′ α
  ;′-unit₂ : Γ ∶ α ; [] ≈′ α
  ;′-assoc : Γ ∶ (α ; β) ; γ ≈′ α ; (β ; γ)
  ;′-cong₁ : Γ ∶ α ≈′ α′ → Γ ∶ α ; β ≈′ α′ ; β
  ;′-cong₂ : Γ ∶ β ≈′ β′ → Γ ∶ α ; β ≈′ α ; β′

  ∥′-unit  : Γ ∶ α ∥ [] ≈′ α
  ∥′-assoc : Γ ∶ (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ)
  ∥′-comm  : Γ ∶ α ∥ β ≈′ β ∥ α
  ∥′-cong₁ : Γ ∶ α ≈′ α′ → Γ ∶ α ∥ β ≈′ α′ ∥ β
  ∥′-dup   : (U : UnrCx Γ α) → Γ ∶ α ≈′ α ∥ α
  ∥′-tm-;  : (U₁ : UnrCx Γ α) (U₂ : UnrCx Γ β) → Γ ∶ α ∥ β ≈′ α ; β

infix 4 _∶_≈_

_∶_≈_ : Ctx n → Rel (Struct n) _
_∶_≈_ Γ = EqClosure (Γ ∶_≈′_)

;-unit₁ : Γ ∶ [] ; α ≈ α
;-unit₁ = Eq*.return ;′-unit₁

;-unit₂ : Γ ∶ α ; [] ≈ α
;-unit₂ = Eq*.return ;′-unit₂

;-assoc : Γ ∶ (α ; β) ; γ ≈ α ; (β ; γ)
;-assoc = Eq*.return ;′-assoc

;-cong : Γ ∶ α ≈ α′ → Γ ∶ β ≈ β′ → Γ ∶ α ; β ≈ α′ ; β′
;-cong xs ys = Eq*.gmap (_; _) ;′-cong₁ xs ◅◅ Eq*.gmap (_ ;_) ;′-cong₂ ys

∥-unit : Γ ∶ α ∥ [] ≈ α
∥-unit = Eq*.return ∥′-unit

∥-assoc : Γ ∶ (α ∥ β) ∥ γ ≈ α ∥ (β ∥ γ)
∥-assoc = Eq*.return ∥′-assoc

∥-comm : Γ ∶ α ∥ β ≈ β ∥ α
∥-comm = Eq*.return ∥′-comm

∥-cong : Γ ∶ α ≈ α′ → Γ ∶ β ≈ β′ → Γ ∶ α ∥ β ≈ α′ ∥ β′
∥-cong xs ys = Eq*.gmap (_∥ _) ∥′-cong₁ xs ◅◅ ∥-comm ◅◅ Eq*.gmap (_∥ _) ∥′-cong₁ ys ◅◅ ∥-comm

∥/;-transmute : UnrCx Γ α → UnrCx Γ β → Γ ∶ α ∥ β ≈ α ; β
∥/;-transmute U₁ U₂ = Eq*.return (∥′-tm-; U₁ U₂)

≈-isEquivalence : (Γ : Ctx n) → IsEquivalence (Γ ∶_≈_)
≈-isEquivalence Γ = Eq*.isEquivalence (Γ ∶_≈′_)

≈-setoid : Ctx n → Setoid _ _
≈-setoid Γ = record { isEquivalence = ≈-isEquivalence Γ }

private module ≈-Equivalence {n} {Γ : Ctx n} = IsEquivalence (≈-isEquivalence Γ)
open ≈-Equivalence
  using ()
  renaming (refl to ≈-refl; reflexive to ≈-reflexive; sym to ≈-sym; trans to ≈-trans)
  public

module ≈-Reasoning {n} {Γ : Ctx n} = SetoidReasoning (≈-setoid Γ)

module _ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} where
  private
    go-fwd : AllCx P Γ Respects (Γ ∶_≈′_)
    go-fwd ;′-unit₁ (ΠP ; ΠP₁) = ΠP₁
    go-fwd ;′-unit₂ (ΠP ; ΠP₁) = ΠP
    go-fwd ;′-assoc ((ΠP ; ΠP₂) ; ΠP₁) = ΠP ; (ΠP₂ ; ΠP₁)
    go-fwd (;′-cong₁ x) (ΠP ; ΠP₁) = go-fwd x ΠP ; ΠP₁
    go-fwd (;′-cong₂ x) (ΠP ; ΠP₁) = ΠP ; go-fwd x ΠP₁
    go-fwd ∥′-unit (ΠP ∥ ΠP₁) = ΠP
    go-fwd ∥′-assoc ((ΠP ∥ ΠP₂) ∥ ΠP₁) = ΠP ∥ (ΠP₂ ∥ ΠP₁)
    go-fwd ∥′-comm (ΠP ∥ ΠP₁) = ΠP₁ ∥ ΠP
    go-fwd (∥′-cong₁ x) (ΠP ∥ ΠP₁) = go-fwd x ΠP ∥ ΠP₁
    go-fwd (∥′-dup x) ΠP = ΠP ∥ ΠP
    go-fwd (∥′-tm-; x x₁) (ΠP ∥ ΠP₁) = ΠP ; ΠP₁

    go-bwd : AllCx P Γ Respects (flip (Γ ∶_≈′_))
    go-bwd ;′-unit₁ [] = [] ; []
    go-bwd ;′-unit₁ (ΠP ∥ ΠP₁) = [] ; (ΠP ∥ ΠP₁)
    go-bwd ;′-unit₁ (ΠP ; ΠP₁) = [] ; (ΠP ; ΠP₁)
    go-bwd ;′-unit₁ (` x) = [] ; (` x)
    go-bwd ;′-unit₂ [] = [] ; []
    go-bwd ;′-unit₂ (ΠP ∥ ΠP₁) = (ΠP ∥ ΠP₁) ; []
    go-bwd ;′-unit₂ (ΠP ; ΠP₁) = (ΠP ; ΠP₁) ; []
    go-bwd ;′-unit₂ (` x) = (` x) ; []
    go-bwd ;′-assoc (ΠP ; (ΠP₁ ; ΠP₂)) = (ΠP ; ΠP₁) ; ΠP₂
    go-bwd (;′-cong₁ x) (ΠP ; ΠP₁) = go-bwd x ΠP ; ΠP₁
    go-bwd (;′-cong₂ x) (ΠP ; ΠP₁) = ΠP ; go-bwd x ΠP₁
    go-bwd ∥′-unit [] = [] ∥ []
    go-bwd ∥′-unit (ΠP ∥ ΠP₁) = (ΠP ∥ ΠP₁) ∥ []
    go-bwd ∥′-unit (ΠP ; ΠP₁) = (ΠP ; ΠP₁) ∥ []
    go-bwd ∥′-unit (` x) = (` x) ∥ []
    go-bwd ∥′-assoc (ΠP ∥ (ΠP₁ ∥ ΠP₂)) = (ΠP ∥ ΠP₁) ∥ ΠP₂
    go-bwd ∥′-comm (ΠP ∥ ΠP₁) = ΠP₁ ∥ ΠP
    go-bwd (∥′-cong₁ x) (ΠP ∥ ΠP₁) = go-bwd x ΠP ∥ ΠP₁
    go-bwd (∥′-dup x) (ΠP ∥ _) = ΠP
    go-bwd (∥′-tm-; x x₁) (ΠP ; ΠP₁) = ΠP ∥ ΠP₁

  allCx-≈ : AllCx P Γ Respects (Γ ∶_≈_)
  allCx-≈ refl         ΠP = ΠP
  allCx-≈ (fwd x ◅ xs) ΠP = allCx-≈ xs (go-fwd x ΠP)
  allCx-≈ (bwd x ◅ xs) ΠP = allCx-≈ xs (go-bwd x ΠP)
