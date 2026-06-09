{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Equivalence where

open import Algebra
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd; symmetric)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import BorrowedCF.Prelude hiding (_⟶_)
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Types hiding (α; α₁; α₂; α₃; α′)

open Nat.Variables
open Bin
open Un using (_⊆_)

open Variables

open Star using (_◅◅_) renaming (ε to refl) public
open Star using (Star; _◅_; kleisliStar)

infix 4 _∶_≈′_

data _∶_≈′_ (Γ : Ctx n) : Struct n → Struct n → Set where
  ;′-assoc : Γ ∶ (α ; β) ; γ ≈′ α ; (β ; γ)
  ;′-cong₁ : Γ ∶ α ≈′ α′ → Γ ∶ α ; β ≈′ α′ ; β
  ;′-cong₂ : Γ ∶ β ≈′ β′ → Γ ∶ α ; β ≈′ α ; β′

  ∥′-unit  : Γ ∶ α ∥ [] ≈′ α
  ∥′-assoc : Γ ∶ (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ)
  ∥′-comm  : Γ ∶ α ∥ β ≈′ β ∥ α
  ∥′-cong₁ : Γ ∶ α ≈′ α′ → Γ ∶ α ∥ β ≈′ α′ ∥ β
  ∥′-dup   : (U : UnrCx Γ α) → Γ ∶ α ≈′ α ∥ α
  ∥′-tm-;  : (U : UnrCx Γ α ⊎ UnrCx Γ β) → Γ ∶ α ∥ β ≈′ α ; β

infix 4 _∶_≈_

_∶_≈_ : Ctx n → Rel (Struct n) _
_∶_≈_ Γ = EqClosure (Γ ∶_≈′_)

≈-isEquivalence : (Γ : Ctx n) → IsEquivalence (Γ ∶_≈_)
≈-isEquivalence Γ = Eq*.isEquivalence (Γ ∶_≈′_)

≈-setoid : Ctx n → Setoid _ _
≈-setoid Γ = record { isEquivalence = ≈-isEquivalence Γ }

private module ≈-Equivalence {n} {Γ : Ctx n} = IsEquivalence (≈-isEquivalence Γ)
open ≈-Equivalence
  using ()
  renaming (refl to ≈-refl; reflexive to ≈-reflexive; sym to ≈-sym; trans to ≈-trans)
  public

∥-assoc : Γ ∶ (α ∥ β) ∥ γ ≈ α ∥ (β ∥ γ)
∥-assoc = Eq*.return ∥′-assoc

∥-comm : Γ ∶ α ∥ β ≈ β ∥ α
∥-comm = Eq*.return ∥′-comm

∥-unit₂ : Γ ∶ α ∥ [] ≈ α
∥-unit₂ = Eq*.return ∥′-unit

∥-unit₁ : Γ ∶ [] ∥ α ≈ α
∥-unit₁ = ∥-comm ◅◅ Eq*.return ∥′-unit

∥-dup : UnrCx Γ α → Γ ∶ α ≈ α ∥ α
∥-dup = Eq*.return ∘ ∥′-dup

∥-cong : Γ ∶ α ≈ α′ → Γ ∶ β ≈ β′ → Γ ∶ α ∥ β ≈ α′ ∥ β′
∥-cong xs ys = Eq*.gmap (_∥ _) ∥′-cong₁ xs ◅◅ ∥-comm ◅◅ Eq*.gmap (_∥ _) ∥′-cong₁ ys ◅◅ ∥-comm

∥/;-transmute : UnrCx Γ α ⊎ UnrCx Γ β → Γ ∶ α ∥ β ≈ α ; β
∥/;-transmute U = Eq*.return (∥′-tm-; U)

;-unit₁ : Γ ∶ [] ; α ≈ α
;-unit₁ = ≈-sym (∥/;-transmute (inj₁ [])) ◅◅ ∥-unit₁

;-unit₂ : Γ ∶ α ; [] ≈ α
;-unit₂ = ≈-sym (∥/;-transmute (inj₂ [])) ◅◅ ∥-unit₂

;-commUnr : UnrCx Γ α ⊎ UnrCx Γ β → Γ ∶ α ; β ≈ β ; α
;-commUnr Uα/Uβ = ≈-sym (∥/;-transmute Uα/Uβ) ◅◅ ∥-comm ◅◅ ∥/;-transmute (Sum.swap Uα/Uβ)

;-assoc : Γ ∶ (α ; β) ; γ ≈ α ; (β ; γ)
;-assoc = Eq*.return ;′-assoc

;-cong : Γ ∶ α ≈ α′ → Γ ∶ β ≈ β′ → Γ ∶ α ; β ≈ α′ ; β′
;-cong xs ys = Eq*.gmap (_; _) ;′-cong₁ xs ◅◅ Eq*.gmap (_ ;_) ;′-cong₂ ys


module ≈-Reasoning {n} {Γ : Ctx n} = SetoidReasoning (≈-setoid Γ)

≈-map⁺ : {f : 𝕋 → 𝕋} → (Unr ⊆ Unr ∘ f) → Γ ∶ α ≈ β → f ∘ Γ ∶ α ≈ β
≈-map⁺ {f = f} Uf = Eq*.map go
  where
  go : (Γ ∶_≈′_) ⇒ (f ∘ Γ ∶_≈′_)
  go ;′-assoc = ;′-assoc
  go (;′-cong₁ x) = ;′-cong₁ (go x)
  go (;′-cong₂ x) = ;′-cong₂ (go x)
  go ∥′-unit = ∥′-unit
  go ∥′-assoc = ∥′-assoc
  go ∥′-comm = ∥′-comm
  go (∥′-cong₁ x) = ∥′-cong₁ (go x)
  go (∥′-dup U) = ∥′-dup (allCx-gmap Uf U)
  go (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-gmap Uf) (allCx-gmap Uf) U)

≈⇒dom≡ : Γ ∶ α ≈ β → dom α ≡ dom β
≈⇒dom≡ = Eq*.gfold isEquivalence dom ≈′⇒dom≡
  where
  open import Data.Fin.Subset
  open import Data.Fin.Subset.Properties

  ≈′⇒dom≡ : Γ ∶ α ≈′ β → dom α ≡ dom β
  ≈′⇒dom≡ ;′-assoc = ∪-assoc _ _ _
  ≈′⇒dom≡ (;′-cong₁ x) = cong (_∪ _) (≈′⇒dom≡ x)
  ≈′⇒dom≡ (;′-cong₂ x) = cong (_ ∪_) (≈′⇒dom≡ x)
  ≈′⇒dom≡ ∥′-unit = ∪-identityʳ _
  ≈′⇒dom≡ ∥′-assoc = ∪-assoc _ _ _
  ≈′⇒dom≡ ∥′-comm = ∪-comm _ _
  ≈′⇒dom≡ (∥′-cong₁ x) = cong (_∪ _) (≈′⇒dom≡ x)
  ≈′⇒dom≡ (∥′-dup U) = sym (∪-idem _)
  ≈′⇒dom≡ (∥′-tm-; U) = refl

≈-≗ : Γ₁ ≗ Γ₂ → Γ₁ ∶ α ≈ β → Γ₂ ∶ α ≈ β
≈-≗ {Γ₁ = Γ₁} {Γ₂ = Γ₂} eq = Eq*.map go where
  go : Γ₁ ∶ α ≈′ β → Γ₂ ∶ α ≈′ β
  go ;′-assoc = ;′-assoc
  go (;′-cong₁ x) = ;′-cong₁ (go x)
  go (;′-cong₂ x) = ;′-cong₂ (go x)
  go ∥′-unit = ∥′-unit
  go ∥′-assoc = ∥′-assoc
  go ∥′-comm = ∥′-comm
  go (∥′-cong₁ x) = ∥′-cong₁ (go x)
  go (∥′-dup U) = ∥′-dup (allCx-≗ eq U)
  go (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-≗ eq) (allCx-≗ eq) U)

dom≢⇒≉ : dom α ≢ dom β → ¬ Γ ∶ α ≈ β
dom≢⇒≉ dom≢ a≈b = dom≢ (≈⇒dom≡ a≈b)

`x≉[] : ∀ {x} → ¬ Γ ∶ ` x ≈ []
`x≉[] {x = x} = dom≢⇒≉ λ ⁅x⁆≡⁅⁆ → ∉⊥ (subst (x ∈_) ⁅x⁆≡⁅⁆ (x∈⁅x⁆ x))
  where
  open import Data.Fin.Subset
  open import Data.Fin.Subset.Properties

∥-isCommutativeMonoid : (Γ : Ctx n) → IsCommutativeMonoid (Γ ∶_≈_) _∥_ []
∥-isCommutativeMonoid Γ = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-isEquivalence Γ
        ; ∙-cong = ∥-cong
        }
      ; assoc = λ _ _ _ → ∥-assoc
      }
    ; identity = (λ _ → ∥-unit₁) , (λ _ → ∥-unit₂)
    }
  ; comm = λ _ _ → ∥-comm
  }

;-isMonoid : (Γ : Ctx n) → IsMonoid (Γ ∶_≈_) _;_ []
;-isMonoid Γ = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≈-isEquivalence Γ
      ; ∙-cong = ;-cong
      }
    ; assoc = λ _ _ _ → ;-assoc
    }
  ; identity = (λ _ → ;-unit₁) , (λ _ → ;-unit₂)
  }

module _ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} where
  private
    go-fwd : AllCx P Γ Respects (Γ ∶_≈′_)
    go-fwd ;′-assoc ((ΠP ; ΠP₂) ; ΠP₁) = ΠP ; (ΠP₂ ; ΠP₁)
    go-fwd (;′-cong₁ x) (ΠP ; ΠP₁) = go-fwd x ΠP ; ΠP₁
    go-fwd (;′-cong₂ x) (ΠP ; ΠP₁) = ΠP ; go-fwd x ΠP₁
    go-fwd ∥′-unit (ΠP ∥ ΠP₁) = ΠP
    go-fwd ∥′-assoc ((ΠP ∥ ΠP₂) ∥ ΠP₁) = ΠP ∥ (ΠP₂ ∥ ΠP₁)
    go-fwd ∥′-comm (ΠP ∥ ΠP₁) = ΠP₁ ∥ ΠP
    go-fwd (∥′-cong₁ x) (ΠP ∥ ΠP₁) = go-fwd x ΠP ∥ ΠP₁
    go-fwd (∥′-dup U) ΠP = ΠP ∥ ΠP
    go-fwd (∥′-tm-; U) (ΠP ∥ ΠP₁) = ΠP ; ΠP₁

    go-bwd : AllCx P Γ Respects (flip (Γ ∶_≈′_))
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
    go-bwd (∥′-dup U) (ΠP ∥ _) = ΠP
    go-bwd (∥′-tm-; U) (ΠP ; ΠP₁) = ΠP ∥ ΠP₁

  allCx-≈ : AllCx P Γ Respects (Γ ∶_≈_)
  allCx-≈ refl         ΠP = ΠP
  allCx-≈ (fwd x ◅ xs) ΠP = allCx-≈ xs (go-fwd x ΠP)
  allCx-≈ (bwd x ◅ xs) ΠP = allCx-≈ xs (go-bwd x ΠP)

unjoinUnr : (Γ : Ctx n) (γ : Struct n) → ∃[ α ] ∃[ β ] Γ ∶ α ∥ β ≈ γ × AllCx Unr Γ α × AllCx (Un.∁ Unr) Γ β
unjoinUnr Γ (` x) with unr? (Γ x)
... | yes Ux = _ , _ , ∥-unit₂ , (` Ux) , []
... | no ¬Ux = _ , _ , ∥-unit₁ , [] , (` ¬Ux)
unjoinUnr Γ [] = _ , _ , ∥-unit₁ , [] , []
unjoinUnr Γ (α ∥ β) =
  let open ≈-Reasoning in
  let α₁ , α₂ , α₁₂≈α , uα₁ , ¬uα₂ = unjoinUnr Γ α in
  let β₁ , β₂ , β₁₂≈β , uβ₁ , ¬uβ₂ = unjoinUnr Γ β in
  let eq = begin (α₁ ∥ β₁) ∥ (α₂ ∥ β₂)  ≈⟨ ∥-assoc ⟨
                 α₁ ∥ β₁ ∥ α₂ ∥ β₂      ≈⟨ ∥-cong ∥-assoc refl ⟩
                 α₁ ∥ (β₁ ∥ α₂) ∥ β₂    ≈⟨ ∥-cong (∥-cong refl ∥-comm) refl ⟩
                 α₁ ∥ (α₂ ∥ β₁) ∥ β₂    ≈⟨ ∥-cong ∥-assoc refl ⟨
                 α₁ ∥ α₂ ∥ β₁ ∥ β₂      ≈⟨ ∥-assoc ⟩
                 (α₁ ∥ α₂) ∥ (β₁ ∥ β₂)  ≈⟨ ∥-cong α₁₂≈α β₁₂≈β ⟩
                 α ∥ β ∎
  in
  α₁ ∥ β₁ , α₂ ∥ β₂ , eq , (uα₁ ∥ uβ₁) , (¬uα₂ ∥ ¬uβ₂)
unjoinUnr Γ (α ; β) =
  let open ≈-Reasoning in
  let α₁ , α₂ , α₁₂≈α , uα₁ , ¬uα₂ = unjoinUnr Γ α in
  let β₁ , β₂ , β₁₂≈β , uβ₁ , ¬uβ₂ = unjoinUnr Γ β in
  let eq = begin (α₁ ; β₁) ∥ (α₂ ; β₂)  ≈⟨ ∥/;-transmute (inj₁ (uα₁ ; uβ₁)) ⟩
                 (α₁ ; β₁) ; (α₂ ; β₂)  ≈⟨ ;-assoc ⟨
                 α₁ ; β₁ ; α₂ ; β₂      ≈⟨ ;-cong ;-assoc refl ⟩
                 α₁ ; (β₁ ; α₂) ; β₂    ≈⟨ ;-cong (;-cong refl (;-commUnr (inj₁ uβ₁))) refl ⟩
                 α₁ ; (α₂ ; β₁) ; β₂    ≈⟨ ;-cong ;-assoc refl ⟨
                 α₁ ; α₂ ; β₁ ; β₂      ≈⟨ ;-assoc ⟩
                 (α₁ ; α₂) ; (β₁ ; β₂)  ≈⟨ ;-cong (∥/;-transmute (inj₁ uα₁)) (∥/;-transmute (inj₁ uβ₁)) ⟨
                 (α₁ ∥ α₂) ; (β₁ ∥ β₂)  ≈⟨ ;-cong α₁₂≈α β₁₂≈β ⟩
                 α ; β ∎
  in
  α₁ ; β₁ , α₂ ; β₂ , eq , (uα₁ ; uβ₁) , (¬uα₂ ; ¬uβ₂)

Empty⇒UnrCx : Γ ∶ γ ≈ [] → UnrCx Γ γ
Empty⇒UnrCx γ≈[] = allCx-≈ (≈-sym γ≈[]) []
