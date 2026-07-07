module BorrowedCF.Context.Domain where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Substitution

open import Data.Bool.Properties
open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
open import Relation.Nullary.Decidable

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

↓-dist-wk : ∀ (γ : Struct n) {x X} → wk γ ↓ (x ∷ X) ≡ wk (γ ↓ X)
↓-dist-wk (` y) {x} {X} = sym (if-float wk (does (y ∈? X)))
↓-dist-wk []      = refl
↓-dist-wk (α ∥ β) = cong₂ _∥_ (↓-dist-wk α) (↓-dist-wk β)
↓-dist-wk (α ; β) = cong₂ _;_ (↓-dist-wk α) (↓-dist-wk β)

postulate
  ∩-∁ : (p q : Subset n) → p ∩ q ≡ ⁅⁆ → p ∩ ∁ q ≡ p




{-
⊆⁅⁆⇒Empty : X ⊆ ⁅⁆ → Empty X
⊆⁅⁆⇒Empty X⊆ (_ , x∈) = ∉⁅⁆ (X⊆ x∈)

⊆⁅⁆⇒≡⁅⁆ : X ⊆ ⁅⁆ → X ≡ ⁅⁆
⊆⁅⁆⇒≡⁅⁆ = Empty-unique ∘ ⊆⁅⁆⇒Empty

⊆⁅x⁆×y∈⇒≡⁅x⁆ : ∀ {x y} → X ⊆ ⁅ x ⁆ → y ∈ X → X ≡ ⁅ x ⁆
⊆⁅x⁆×y∈⇒≡⁅x⁆ X⊆ y∈ = ⊆-antisym X⊆ (λ x′∈⁅x⁆ → subst (_∈ _) (x∈⁅y⁆⇒x≡y _ (X⊆ y∈) ■ sym (x∈⁅y⁆⇒x≡y _ x′∈⁅x⁆)) y∈)

⊆⁅x⁆×x∉⇒Empty : ∀ {x} → X ⊆ ⁅ x ⁆ → x ∉ X → Empty X
⊆⁅x⁆×x∉⇒Empty X⊆ x∉ (y , y∈) = x∉ (subst (_∈ _) (x∈⁅y⁆⇒x≡y _ (X⊆ y∈)) y∈)

Empty-∩₁ : Empty X → (Y : Subset n) → Empty (X ∩ Y)
Empty-∩₁ {X = X} ⁅⁆≐X Y (x , x∈) = ⁅⁆≐X (_ , p∩q⊆p X Y x∈)

Empty-∩₂ : (X : Subset n) {Y : Subset n} → Empty Y → Empty (X ∩ Y)
Empty-∩₂ X {Y} ⁅⁆≐Y (x , x∈) = ⁅⁆≐Y (_ , p∩q⊆q X Y x∈)

Empty-⁅⁆ : Empty {n} ⁅⁆
Empty-⁅⁆ (_ , x∈) = ∉⁅⁆ x∈

Disjoint : Rel (Struct n) _
Disjoint α β = Empty (dom α ∩ dom β)

∪-mono-⊆ : Bin.Monotonic₂ (_⊆_ {n}) _⊆_ _⊆_ _∪_
∪-mono-⊆ p⊆q u⊆v x∈ = x∈p∪q⁺ (Sum.map p⊆q u⊆v (x∈p∪q⁻ _ _ x∈))

∩-mono-⊆ : Bin.Monotonic₂ (_⊆_ {n}) _⊆_ _⊆_ _∩_
∩-mono-⊆ p⊆q u⊆v x∈ = x∈p∩q⁺ (p⊆q (x∈p∩q⁻ _ _ x∈ .proj₁) , u⊆v (x∈p∩q⁻ _ _ x∈ .proj₂))

∩-identityˡ-⊆ : {X : Subset n} (Y : Subset n) → Y ⊆ X → X ∩ Y ≡ Y
∩-identityˡ-⊆ Y Y⊆X = ⊆-antisym (λ x∈ → x∈p∩q⁻ _ _ x∈ .proj₂) (λ x∈ → x∈p∩q⁺ (Y⊆X x∈ , x∈))

∩-identityʳ-⊆ : (X : Subset n) {Y : Subset n} → X ⊆ Y → X ∩ Y ≡ X
∩-identityʳ-⊆ X X⊆Y = ⊆-antisym (λ x∈ → x∈p∩q⁻ _ _ x∈ .proj₁) (λ x∈ → x∈p∩q⁺ (x∈ , X⊆Y x∈))
-}


-- Inverse renaming for context relations (≈ / ≼) along injective renamings.

InImage : (m →ᵣ n) → 𝔽 n → Set
InImage ϕ y = ∃[ x ] ϕ x ≡ y

dom-⋯-InImage : (α : Struct m) {ϕ : m →ᵣ n} {y : 𝔽 n} → y ∈ dom (α ⋯ ϕ) → InImage ϕ y
dom-⋯-InImage (` x)   {ϕ} y∈ = x , sym (x∈⁅y⁆⇒x≡y _ y∈)
dom-⋯-InImage []          y∈ = ⊥-elim (∉⁅⁆ y∈)
dom-⋯-InImage (α ∥ β)     y∈ = [ dom-⋯-InImage α , dom-⋯-InImage β ]′ (x∈p∪q⁻ _ _ y∈)
dom-⋯-InImage (α ; β)  y∈ = [ dom-⋯-InImage α , dom-⋯-InImage β ]′ (x∈p∪q⁻ _ _ y∈)

preimage : {ϕ : m →ᵣ n} (Z : Struct n) → (∀ {y} → y ∈ dom Z → InImage ϕ y) → ∃[ γ ] γ ⋯ ϕ ≡ Z
preimage []       f = [] , refl
preimage (` y)    f = let x , eq = f (x∈⁅x⁆ y) in ` x , cong `_ eq
preimage (α ∥ β)  f =
  let γ₁ , e₁ = preimage α (λ y∈ → f (x∈p∪q⁺ (Sum.inj₁ y∈)))
      γ₂ , e₂ = preimage β (λ y∈ → f (x∈p∪q⁺ (Sum.inj₂ y∈)))
  in γ₁ ∥ γ₂ , cong₂ _∥_ e₁ e₂
preimage (α ; β) f =
  let γ₁ , e₁ = preimage α (λ y∈ → f (x∈p∪q⁺ (Sum.inj₁ y∈)))
      γ₂ , e₂ = preimage β (λ y∈ → f (x∈p∪q⁺ (Sum.inj₂ y∈)))
  in γ₁ ; γ₂ , cong₂ _;_ e₁ e₂

⋯≡[]⁻¹ : (α : Struct m) {ϕ : m →ᵣ n} → α ⋯ ϕ ≡ [] → α ≡ []
⋯≡[]⁻¹ []         eq = refl
⋯≡[]⁻¹ (` x)      ()
⋯≡[]⁻¹ (α ∥ β)    ()
⋯≡[]⁻¹ (α ; β) ()

⋯≡∥⁻¹ : (α : Struct m) {ϕ : m →ᵣ n} {γ₁ γ₂ : Struct n} →
  α ⋯ ϕ ≡ γ₁ ∥ γ₂ → ∃[ α₁ ] ∃[ α₂ ] α ≡ α₁ ∥ α₂ × α₁ ⋯ ϕ ≡ γ₁ × α₂ ⋯ ϕ ≡ γ₂
⋯≡∥⁻¹ (α₁ ∥ α₂)  refl = _ , _ , refl , refl , refl
⋯≡∥⁻¹ (` x)       ()
⋯≡∥⁻¹ []          ()
⋯≡∥⁻¹ (α ; β)  ()

⋯≡seq⁻¹ : (α : Struct m) {ϕ : m →ᵣ n} {γ₁ γ₂ : Struct n} →
  α ⋯ ϕ ≡ γ₁ ; γ₂ → ∃[ α₁ ] ∃[ α₂ ] α ≡ α₁ ; α₂ × α₁ ⋯ ϕ ≡ γ₁ × α₂ ⋯ ϕ ≡ γ₂
⋯≡seq⁻¹ (α₁ ; α₂) refl = _ , _ , refl , refl , refl
⋯≡seq⁻¹ (` x)        ()
⋯≡seq⁻¹ []           ()
⋯≡seq⁻¹ (α ∥ β)      ()

private
  symstep-⋯⁻¹ : {ϕ : m →ᵣ n} → Inj ϕ → ϕ Preserves[ Unr ] Γ₁ ⇐ Γ₂ → ϕ Preserves[ Mobile ] Γ₁ ⇐ Γ₂ →
    SymClosure (Γ₂ ∶_≈′_) (α ⋯ ϕ) (β ⋯ ϕ) → Γ₁ ∶ α ≈ β
  symstep-⋯⁻¹ inj pu pm (fwd r) = fwd (≈′-⋯⁻¹ inj pu pm r) ◅ ε
  symstep-⋯⁻¹ inj pu pm (bwd r) = bwd (≈′-⋯⁻¹ inj pu pm r) ◅ ε

  ≈-⋯⁻¹-gen : {ϕ : m →ᵣ n} → Inj ϕ → ϕ Preserves[ Unr ] Γ₁ ⇐ Γ₂ → ϕ Preserves[ Mobile ] Γ₁ ⇐ Γ₂ →
    ∀ {α : Struct m} {B} → Γ₂ ∶ α ⋯ ϕ ≈ B → ∀ {β} → B ≡ β ⋯ ϕ → Γ₁ ∶ α ≈ β
  ≈-⋯⁻¹-gen inj pu pm ε eqb = ≈-reflexive (⋯-injective inj eqb)
  ≈-⋯⁻¹-gen {ϕ = ϕ} inj pu pm {α = α} (_◅_ {j = Y} s rest) eqb
    with preimage Y (λ {z} z∈ → dom-⋯-InImage α (subst (z ∈_) (sym (≈⇒dom≡ (s ◅ ε))) z∈))
  ... | pre , eqm rewrite sym eqm =
        ≈-trans (symstep-⋯⁻¹ {α = α} {β = pre} inj pu pm s) (≈-⋯⁻¹-gen inj pu pm {α = pre} rest eqb)

≈-⋯⁻¹ : {ϕ : m →ᵣ n} → Inj ϕ → ϕ Preserves[ Unr ] Γ₁ ⇐ Γ₂ → ϕ Preserves[ Mobile ] Γ₁ ⇐ Γ₂ → Γ₂ ∶ α ⋯ ϕ ≈ β ⋯ ϕ → Γ₁ ∶ α ≈ β
≈-⋯⁻¹ inj pu pm H = ≈-⋯⁻¹-gen inj pu pm H refl

≼-⋯⁻¹ : {ϕ : m →ᵣ n} → Inj ϕ → ϕ Preserves[ Unr ] Γ₁ ⇐ Γ₂ → ϕ Preserves[ Mobile ] Γ₁ ⇐ Γ₂ → Γ₂ ∶ α ⋯ ϕ ≼ β ⋯ ϕ → Γ₁ ∶ α ≼ β
≼-⋯⁻¹ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} inj pu pm H = go H refl refl
  where
  go : ∀ {A B} → Γ₂ ∶ A ≼ B → ∀ {α β} → A ≡ α ⋯ ϕ → B ≡ β ⋯ ϕ → Γ₁ ∶ α ≼ β
  go (≼-refl x) eqa eqb = ≼-refl (≈-⋯⁻¹ inj pu pm (subst₂ (_ ∶_≈_) eqa eqb x))
  go (≼-∅ U) {α} eqa eqb rewrite ⋯≡[]⁻¹ α (sym eqa) = ≼-∅ (allCx-⋯⁻¹ pu (subst (UnrCx _) eqb U))
  go (≼-trans {β = Mid} x y) {α} {β} eqa eqb
    with preimage Mid (λ {z} z∈ → dom-⋯-InImage β (subst (z ∈_) (cong dom eqb) (≼⇒dom⊆ y z∈)))
  ... | pre , eqm = ≼-trans (go x {β = pre} eqa (sym eqm)) (go y {α = pre} (sym eqm) eqb)
  go (≼-wk {α₁} {α₂} {β₁} {β₂}) {α} {β} eqa eqb
    with ⋯≡seq⁻¹ α (sym eqa)
  ... | p , q , α≡ , ep , eq
    with ⋯≡∥⁻¹ p ep | ⋯≡∥⁻¹ q eq
  ... | p₁ , p₂ , p≡ , ep₁ , ep₂ | q₁ , q₂ , q≡ , eq₁ , eq₂
    with ⋯≡∥⁻¹ β (sym eqb)
  ... | s₁ , s₂ , β≡ , es₁ , es₂
    with ⋯≡seq⁻¹ s₁ es₁ | ⋯≡seq⁻¹ s₂ es₂
  ... | c₁ , d₁ , s₁≡ , ec₁ , ed₁ | c₂ , d₂ , s₂≡ , ec₂ , ed₂
    rewrite α≡ | p≡ | q≡ | β≡ | s₁≡ | s₂≡
          | ⋯-injective {α = p₁} {β = c₁} inj (ep₁ ■ sym ec₁)
          | ⋯-injective {α = p₂} {β = c₂} inj (ep₂ ■ sym ec₂)
          | ⋯-injective {α = q₁} {β = d₁} inj (eq₁ ■ sym ed₁)
          | ⋯-injective {α = q₂} {β = d₂} inj (eq₂ ■ sym ed₂)
    = ≼-wk
  go (≼-cong-; x y) {α} {β} eqa eqb
    with ⋯≡seq⁻¹ α (sym eqa) | ⋯≡seq⁻¹ β (sym eqb)
  ... | α₁ , α₂ , α≡ , ea₁ , ea₂ | β₁ , β₂ , β≡ , eb₁ , eb₂ rewrite α≡ | β≡ =
        ≼-cong-; (go x {α = α₁} {β = β₁} (sym ea₁) (sym eb₁)) (go y {α = α₂} {β = β₂} (sym ea₂) (sym eb₂))
  go (≼-cong-∥ x y) {α} {β} eqa eqb
    with ⋯≡∥⁻¹ α (sym eqa) | ⋯≡∥⁻¹ β (sym eqb)
  ... | α₁ , α₂ , α≡ , ea₁ , ea₂ | β₁ , β₂ , β≡ , eb₁ , eb₂ rewrite α≡ | β≡ =
        ≼-cong-∥ (go x {α = α₁} {β = β₁} (sym ea₁) (sym eb₁)) (go y {α = α₂} {β = β₂} (sym ea₂) (sym eb₂))


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
