module BorrowedCF.Context.Domain where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext

open import Data.Bool.Properties
open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
open import Relation.Nullary.Decidable

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables
open Variables

variable
  X X₁ X₂ X₃ : Subset n
  Y Y₁ Y₂ Y₃ : Subset n

dom : Struct n → Subset n
dom []      = ⁅⁆
dom (` x)   = ⁅ x ⁆
dom (α ∥ β) = dom α ∪ dom β
dom (α ; β) = dom α ∪ dom β

infixl 18 _↓_

_↓_ : Struct n → Subset n → Struct n
(` x)   ↓ X = if does (x ∈? X) then ` x else []
[]      ↓ X = []
(α ∥ β) ↓ X = α ↓ X ∥ β ↓ X
(α ; β) ↓ X = α ↓ X ; β ↓ X

↓-dom : (γ : Struct n) (X : Subset n) → dom (γ ↓ X) ⊆ X
↓-dom (` x) X z∈ with x ∈? X
... | yes x∈ rewrite x∈⁅y⁆⇒x≡y _ z∈ = x∈
... | no  x∉ = ⁅⁆⊆ z∈
↓-dom []      X = ⁅⁆⊆
↓-dom (α ∥ β) X = [ ↓-dom α X , ↓-dom β X ]′ ∘ x∈p∪q⁻ _ _
↓-dom (α ; β) X = [ ↓-dom α X , ↓-dom β X ]′ ∘ x∈p∪q⁻ _ _

↓-identity-⊆ : (γ : Struct n) {X : Subset n} → dom γ ⊆ X → γ ↓ X ≡ γ
↓-identity-⊆ (` x) {X} ⊆X rewrite dec-true (x ∈? X) (⊆X (x∈⁅x⁆ x)) = refl
↓-identity-⊆ [] ⊆X = refl
↓-identity-⊆ (α ∥ β) ⊆X = cong₂ _∥_ (↓-identity-⊆ α (⊆-trans (p⊆p∪q _) ⊆X)) (↓-identity-⊆ β (⊆-trans (q⊆p∪q _ _) ⊆X))
↓-identity-⊆ (α ; β) ⊆X = cong₂ _;_ (↓-identity-⊆ α (⊆-trans (p⊆p∪q _) ⊆X)) (↓-identity-⊆ β (⊆-trans (q⊆p∪q _ _) ⊆X))

↓-identity : (γ : Struct n) → γ ↓ S.⊤ ≡ γ
↓-identity γ = ↓-identity-⊆ γ ⊆⊤

↓-idempotent : (γ : Struct n) (X : Subset n) → γ ↓ X ↓ X ≡ γ ↓ X
↓-idempotent γ X = ↓-identity-⊆ (γ ↓ X) {X} (↓-dom γ X)

↓-empty : (γ : Struct n) → Γ ∶ γ ↓ ⁅⁆ ≈ []
↓-empty (` x) rewrite dec-false (x ∈? ⁅⁆) ∉⁅⁆ = refl
↓-empty [] = refl
↓-empty (α ∥ β) = ≈-trans (∥-cong (↓-empty α) (↓-empty β)) ∥-unit₂
↓-empty (α ; β) = ≈-trans (;-cong (↓-empty α) (↓-empty β)) ;-unit₂

≈⇒dom≡ : Γ ∶ α ≈ β → dom α ≡ dom β
≈⇒dom≡ = Eq*.gfold isEquivalence dom ≈′⇒dom≡
  where
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

dom≢⇒≉ : dom α ≢ dom β → ¬ Γ ∶ α ≈ β
dom≢⇒≉ dom≢ a≈b = dom≢ (≈⇒dom≡ a≈b)

`x≉[] : ∀ {x} → ¬ Γ ∶ ` x ≈ []
`x≉[] {x = x} = dom≢⇒≉ λ ⁅x⁆≡⁅⁆ → ∉⁅⁆ (subst (x ∈_) ⁅x⁆≡⁅⁆ (x∈⁅x⁆ x))

dom⁅⁆⇒[] : (γ : Struct n) → dom γ ≡ ⁅⁆ → Γ ∶ γ ≈ []
dom⁅⁆⇒[] (` x) eq = contradiction (subst (x ∈_) eq (x∈⁅x⁆ x)) ∉⁅⁆
dom⁅⁆⇒[] [] eq = refl
dom⁅⁆⇒[] (α ∥ β) eq = ≈-trans (∥-cong (dom⁅⁆⇒[] α (⊆-antisym (⊆-trans (p⊆p∪q (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))
                                      (dom⁅⁆⇒[] β ((⊆-antisym (⊆-trans (q⊆p∪q (dom α) (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))))
                              ∥-unit₂
dom⁅⁆⇒[] (α ; β) eq = ≈-trans (;-cong (dom⁅⁆⇒[] α (⊆-antisym (⊆-trans (p⊆p∪q (dom β)) (⊆-reflexive eq))
                                                             (⊥-elim ∘ ∉⁅⁆)))
                                      (dom⁅⁆⇒[] β ((⊆-antisym (⊆-trans (q⊆p∪q (dom α) (dom β)) (⊆-reflexive eq))
                                                              (⊥-elim ∘ ∉⁅⁆)))))
                              ;-unit₂

↓-empty⁻¹ : (γ : Struct n) (X : Subset n) → Γ ∶ γ ↓ X ≈ [] → dom γ ∩ X ≡ ⁅⁆
↓-empty⁻¹ (` x) X eq with x ∈? X
... | yes x∈ = contradiction eq `x≉[]
... | no  x∉ = ⊆-antisym (⊥-elim ∘ x∉ ∘ (λ (y∈⁅x⁆ , y∈X) → subst (_∈ X) (x∈⁅y⁆⇒x≡y _ y∈⁅x⁆) y∈X) ∘ x∈p∩q⁻ ⁅ x ⁆ X)
                         (⊥-elim ∘ ∉⁅⁆)
↓-empty⁻¹ [] X eq = ∩-zeroˡ X
↓-empty⁻¹ {Γ = Γ} (α ∥ β) X eq =
  ∩-distribʳ-∪ X (dom α) (dom β)
    ■ cong₂ _∪_ (↓-empty⁻¹ {Γ = Γ} α X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
                (↓-empty⁻¹ {Γ = Γ} β X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
    ■ ∪-identityˡ ⁅⁆
↓-empty⁻¹ {Γ = Γ} (α ; β) X eq =
  ∩-distribʳ-∪ X (dom α) (dom β)
    ■ cong₂ _∪_ (↓-empty⁻¹ {Γ = Γ} α X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
                (↓-empty⁻¹ {Γ = Γ} β X (dom⁅⁆⇒[] _ (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive (≈⇒dom≡ eq)))
                                                              (⊥-elim ∘ ∉⁅⁆))))
    ■ ∪-identityˡ ⁅⁆

≼⇒dom⊆ : Γ ∶ α ≼ β → dom α ⊆ dom β
≼⇒dom⊆ (≼-refl x) = ⊆-reflexive (≈⇒dom≡ x)
≼⇒dom⊆ (≼-∅ x) = ⊥-elim ∘ ∉⁅⁆
≼⇒dom⊆ (≼-wk {α₁} {α₂} {β₁} {β₂}) = ⊆-reflexive $
  let open ≡-Reasoning in
  dom ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) ≡⟨⟩
  (dom α₁ ∪ dom α₂) ∪ (dom β₁ ∪ dom β₂)  ≡⟨ ∪-assoc (dom α₁ ∪ dom α₂) (dom β₁) (dom β₂) ⟨
  ((dom α₁ ∪ dom α₂) ∪ dom β₁) ∪ dom β₂  ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom α₂ ∪ dom β₁) ∪ dom β₂    ≡⟨ cong (λ X → (dom α₁ ∪ X) ∪ dom β₂) (∪-comm (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom β₁ ∪ dom α₂) ∪ dom β₂    ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom β₁) (dom α₂)) ⟨
  ((dom α₁ ∪ dom β₁) ∪ dom α₂) ∪ dom β₂  ≡⟨ ∪-assoc (dom α₁ ∪ dom β₁) (dom α₂) (dom β₂) ⟩
  (dom α₁ ∪ dom β₁) ∪ (dom α₂ ∪ dom β₂)  ≡⟨⟩
  dom ((α₁ ; β₁) ∥ (α₂ ; β₂)) ∎
≼⇒dom⊆ (≼-trans x y) = ⊆-trans (≼⇒dom⊆ x) (≼⇒dom⊆ y)
≼⇒dom⊆ (≼-cong-; x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _
≼⇒dom⊆ (≼-cong-∥ x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _

dom⊈⇒⋠ : dom α ⊈ dom β → ¬ Γ ∶ α ≼ β
dom⊈⇒⋠ dom⊈ α≼β = dom⊈ (≼⇒dom⊆ α≼β)

`x⋠[] : ∀ {x} → ¬ Γ ∶ ` x ≼ []
`x⋠[] {x = x} = dom⊈⇒⋠ λ ⁅x⁆⊆⁅⁆ → ∉⁅⁆ (⁅x⁆⊆⁅⁆ (x∈⁅x⁆ x))

-- ↓ (context restriction) interacts with AllCx / ≈ / ≼ (all renaming-free).

allCx-↓ : ∀ {ℓ}{P : Pred 𝕋 ℓ}{X} → AllCx P Γ γ → AllCx P Γ (γ ↓ X)
allCx-↓ {γ = ` y} {X = X} (` p) with y ∈? X
... | yes _ = ` p
... | no _ = []
allCx-↓ []      = []
allCx-↓ (a ∥ b) = allCx-↓ a ∥ allCx-↓ b
allCx-↓ (a ; b) = allCx-↓ a ; allCx-↓ b

↓-⊆ : ∀ {ℓ}{P : Pred 𝕋 ℓ}{Y X}(γ : Struct n) → Y ⊆ X → AllCx P Γ (γ ↓ X) → AllCx P Γ (γ ↓ Y)
↓-⊆ {Y = Y}{X} (` y) Y⊆X a with y ∈? Y | y ∈? X
... | yes _    | yes _  = a
... | yes y∈Y  | no y∉X = contradiction (Y⊆X y∈Y) y∉X
... | no _     | _      = []
↓-⊆ [] Y⊆X a = []
↓-⊆ (α ∥ β) Y⊆X (a ∥ b) = ↓-⊆ α Y⊆X a ∥ ↓-⊆ β Y⊆X b
↓-⊆ (α ; β) Y⊆X (a ; b) = ↓-⊆ α Y⊆X a ; ↓-⊆ β Y⊆X b

∁-∪-⊆ˡ : (X Y : Subset n) → ∁ (X ∪ Y) ⊆ ∁ X
∁-∪-⊆ˡ X Y x∈ = x∉p⇒x∈∁p (λ x∈X → x∈∁p⇒x∉p x∈ (x∈p∪q⁺ (Sum.inj₁ x∈X)))

∁-∪-⊆ʳ : (X Y : Subset n) → ∁ (X ∪ Y) ⊆ ∁ Y
∁-∪-⊆ʳ X Y x∈ = x∉p⇒x∈∁p (λ x∈Y → x∈∁p⇒x∉p x∈ (x∈p∪q⁺ (Sum.inj₂ x∈Y)))

≈′-↓ : ∀ {X} → Γ ∶ α ≈′ β → Γ ∶ α ↓ X ≈′ β ↓ X
≈′-↓ ;′-assoc = ;′-assoc
≈′-↓ (;′-cong₁ e) = ;′-cong₁ (≈′-↓ e)
≈′-↓ (;′-cong₂ e) = ;′-cong₂ (≈′-↓ e)
≈′-↓ ∥′-unit = ∥′-unit
≈′-↓ ∥′-assoc = ∥′-assoc
≈′-↓ ∥′-comm = ∥′-comm
≈′-↓ (∥′-cong₁ e) = ∥′-cong₁ (≈′-↓ e)
≈′-↓ (∥′-dup U) = ∥′-dup (allCx-↓ U)
≈′-↓ (∥′-tm-; U) = ∥′-tm-; (Sum.map allCx-↓ allCx-↓ U)

↓-mono-≈ : ∀ {X} → Γ ∶ α ≈ β → Γ ∶ α ↓ X ≈ β ↓ X
↓-mono-≈ = Eq*.gmap _ ≈′-↓

↓-mono-≼ : ∀ {X} → Γ ∶ α ≼ β → Γ ∶ α ↓ X ≼ β ↓ X
↓-mono-≼ (≼-refl e) = ≼-refl (↓-mono-≈ e)
↓-mono-≼ (≼-∅ U) = ≼-∅ (allCx-↓ U)
↓-mono-≼ ≼-wk = ≼-wk
↓-mono-≼ (≼-trans x y) = ≼-trans (↓-mono-≼ x) (↓-mono-≼ y)
↓-mono-≼ (≼-cong-; x y) = ≼-cong-; (↓-mono-≼ x) (↓-mono-≼ y)
↓-mono-≼ (≼-cong-∥ x y) = ≼-cong-∥ (↓-mono-≼ x) (↓-mono-≼ y)

↓-strip≼ : (γ : Struct n) {X : Subset n} → AllCx Unr Γ (γ ↓ (∁ X)) → Γ ∶ γ ↓ X ≼ γ
↓-strip≼ (` y) {X} u with y ∈? X | y ∈? ∁ X
... | yes _   | _       = ≼-refl refl
... | no _    | yes _   = ≼-∅ u
... | no y∉X  | no y∉∁X = contradiction (x∉∁p⇒x∈p y∉∁X) y∉X
↓-strip≼ [] u = ≼-refl refl
↓-strip≼ (α ∥ β) (u ∥ v) = ≼-cong-∥ (↓-strip≼ α u) (↓-strip≼ β v)
↓-strip≼ (α ; β) (u ; v) = ≼-cong-; (↓-strip≼ α u) (↓-strip≼ β v)

-- The "extra" in β beyond α's domain (when α ≼ β) is all Unr.

↓-dom⊆dom : ∀ (γ : Struct n) {X} → dom (γ ↓ X) ⊆ dom γ
↓-dom⊆dom (` y) {X} z∈ with y ∈? X
... | yes _ = z∈
... | no _  = ⁅⁆⊆ z∈
↓-dom⊆dom [] z∈ = z∈
↓-dom⊆dom (α ∥ β) z∈ = x∈p∪q⁺ (Sum.map (↓-dom⊆dom α) (↓-dom⊆dom β) (x∈p∪q⁻ _ _ z∈))
↓-dom⊆dom (α ; β) z∈ = x∈p∪q⁺ (Sum.map (↓-dom⊆dom α) (↓-dom⊆dom β) (x∈p∪q⁻ _ _ z∈))

emptyDom⇒AllCx : ∀ {ℓ} {P : Pred 𝕋 ℓ} (γ : Struct n) → dom γ ≡ ⁅⁆ → AllCx P Γ γ
emptyDom⇒AllCx (` y) eq = contradiction (subst (y ∈_) eq (x∈⁅x⁆ y)) ∉⁅⁆
emptyDom⇒AllCx [] eq = []
emptyDom⇒AllCx (α ∥ β) eq =
  emptyDom⇒AllCx α (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive eq)) (⊥-elim ∘ ∉⁅⁆))
  ∥ emptyDom⇒AllCx β (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive eq)) (⊥-elim ∘ ∉⁅⁆))
emptyDom⇒AllCx (α ; β) eq =
  emptyDom⇒AllCx α (⊆-antisym (⊆-trans (p⊆p∪q _) (⊆-reflexive eq)) (⊥-elim ∘ ∉⁅⁆))
  ; emptyDom⇒AllCx β (⊆-antisym (⊆-trans (q⊆p∪q _ _) (⊆-reflexive eq)) (⊥-elim ∘ ∉⁅⁆))

extra-Unr-domeq : (α β : Struct n) → dom α ≡ dom β → AllCx Unr Γ (β ↓ ∁ (dom α))
extra-Unr-domeq α β eq = emptyDom⇒AllCx (β ↓ ∁ (dom α)) (⊆-antisym elim ⁅⁆⊆)
  where elim : dom (β ↓ ∁ (dom α)) ⊆ ⁅⁆
        elim z∈ = ⊥-elim (x∈∁p⇒x∉p (↓-dom β (∁ (dom α)) z∈) (subst (_ ∈_) (sym eq) (↓-dom⊆dom β z∈)))

dom-wk-eq : (α₁ α₂ β₁ β₂ : Struct n) →
  dom ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) ≡ dom ((α₁ ; β₁) ∥ (α₂ ; β₂))
dom-wk-eq α₁ α₂ β₁ β₂ =
  let open ≡-Reasoning in
  (dom α₁ ∪ dom α₂) ∪ (dom β₁ ∪ dom β₂)  ≡⟨ ∪-assoc (dom α₁ ∪ dom α₂) (dom β₁) (dom β₂) ⟨
  ((dom α₁ ∪ dom α₂) ∪ dom β₁) ∪ dom β₂  ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom α₂ ∪ dom β₁) ∪ dom β₂    ≡⟨ cong (λ z → (dom α₁ ∪ z) ∪ dom β₂) (∪-comm (dom α₂) (dom β₁)) ⟩
  (dom α₁ ∪ dom β₁ ∪ dom α₂) ∪ dom β₂    ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom β₁) (dom α₂)) ⟨
  ((dom α₁ ∪ dom β₁) ∪ dom α₂) ∪ dom β₂  ≡⟨ ∪-assoc (dom α₁ ∪ dom β₁) (dom α₂) (dom β₂) ⟩
  (dom α₁ ∪ dom β₁) ∪ (dom α₂ ∪ dom β₂)  ∎

≼⇒extra-Unr : Γ ∶ α ≼ β → AllCx Unr Γ (β ↓ ∁ (dom α))
≼⇒extra-Unr {α = α} {β} (≼-refl e) = extra-Unr-domeq α β (≈⇒dom≡ e)
≼⇒extra-Unr {β = β} (≼-∅ U) =
  subst (AllCx Unr _) (sym (↓-identity-⊆ β (λ _ → x∉p⇒x∈∁p ∉⁅⁆))) U
≼⇒extra-Unr (≼-wk {α₁} {α₂} {β₁} {β₂}) =
  extra-Unr-domeq ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) ((α₁ ; β₁) ∥ (α₂ ; β₂)) (dom-wk-eq α₁ α₂ β₁ β₂)
≼⇒extra-Unr (≼-trans x y) = allCx-weaken (λ u → u) (↓-mono-≼ y) (≼⇒extra-Unr x)
≼⇒extra-Unr (≼-cong-∥ {α = a} {α′ = a′} {β = b} {β′ = b′} x y) =
  ↓-⊆ a′ (∁-∪-⊆ˡ (dom a) (dom b)) (≼⇒extra-Unr x) ∥ ↓-⊆ b′ (∁-∪-⊆ʳ (dom a) (dom b)) (≼⇒extra-Unr y)
≼⇒extra-Unr (≼-cong-; {α = a} {α′ = a′} {β = b} {β′ = b′} x y) =
  ↓-⊆ a′ (∁-∪-⊆ˡ (dom a) (dom b)) (≼⇒extra-Unr x) ; ↓-⊆ b′ (∁-∪-⊆ʳ (dom a) (dom b)) (≼⇒extra-Unr y)

open V using (tail; drop)

-- Subset properties for `tail`

tail-∁ : (X : Subset (suc n)) → tail (∁ X) ≡ ∁ (tail X)
tail-∁ (x ∷ X) = refl

tail-∪⁅0⁆ : (X : Subset (suc n)) → tail (X ∪ ⁅ zero ⁆) ≡ tail X
tail-∪⁅0⁆ (x ∷ X) = ∪-identityʳ X

∈tail⁻ : ∀ {x} {X : Subset (suc n)} → x ∈ tail X → suc x ∈ X
∈tail⁻ {X = _ ∷ _} x∈ = there x∈

⊆-tail⁺ : {X Y : Subset (suc n)} → X ⊆ Y → tail X ⊆ tail Y
⊆-tail⁺ {X = _ ∷ _} {Y = _ ∷ _} X⊆Y x∈ = case X⊆Y (there x∈) of λ{ (there x∈′) → x∈′ }

-- Subset properties for `drop`.

drop-∁ : ∀ m (X : Subset (m + n)) → drop m (∁ X) ≡ ∁ (drop m X)
drop-∁ zero    X       = refl
drop-∁ (suc m) (x ∷ X) = drop-∁ m X

∈drop⁻ : ∀ m {x} {X : Subset (m + n)} → x ∈ drop m X → m ↑ʳ x ∈ X
∈drop⁻ zero                x∈ = x∈
∈drop⁻ (suc m) {X = y ∷ X} x∈ = there (∈drop⁻ m x∈)

⊆-drop⁺ : ∀ m {X Y : Subset (m + n)} → X ⊆ Y → drop m X ⊆ drop m Y
⊆-drop⁺ zero                    X⊆Y    = X⊆Y
⊆-drop⁺ (suc m) {_ ∷ _} {_ ∷ _} X⊆Y x∈ = ⊆-drop⁺ m ((λ{ (there x∈′) → x∈′ }) ∘ X⊆Y ∘ there) x∈

-- Additional subset properties for `∁`.

⊆-∁⁺ : {X Y : Subset n} → X ⊆ Y → ∁ Y ⊆ ∁ X
⊆-∁⁺ X⊆Y x∈∁Y = x∉p⇒x∈∁p λ x∈X → x∈∁p⇒x∉p x∈∁Y (X⊆Y x∈X)

-- Subset extension.
