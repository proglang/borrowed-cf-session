module BorrowedCF.Context.Base where

open import BorrowedCF.Prelude
open import BorrowedCF.Types

open Nat.Variables

open import Data.Vec using () renaming (_∷_ to _⸴_; _++_ to _⸴*_; lookup to infix 6 _﹫_) public

Ctx = Vec 𝕋

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx n

data ParSeq : Set where
  par seq : ParSeq

infixl 17 _∥_ _;_

data Struct (n : ℕ) : Set where
  `_  : 𝔽 n → Struct n
  []  : Struct n
  _∥_ : Struct n → Struct n → Struct n
  _;_ : Struct n → Struct n → Struct n

variable
  γ γ₁ γ₂ γ₃ γ′ : Struct n

module Variables where
  variable
    α α₁ α₂ α₃ α′ α₁′ α₂′ : Struct n
    β β₁ β₂ β₃ β′ β₁′ β₂′ : Struct n

open Variables
open Un

cast : .(m ≡ n) → Struct m → Struct n
cast eq (` x) = ` Fin.cast eq x
cast eq [] = []
cast eq (α ∥ β) = cast eq α ∥ cast eq β
cast eq (α ; β) = cast eq α ; cast eq β

cast-trans : .(eq₁ : n₁ ≡ n₂) .(eq₂ : n₂ ≡ n₃) →
  cast eq₂ ∘ cast eq₁ ≗ cast (eq₁ ■ eq₂)
cast-trans eq₁ eq₂ (` x) = cong `_ (Fin.cast-trans eq₁ eq₂ x)
cast-trans eq₁ eq₂ [] = refl
cast-trans eq₁ eq₂ (α ∥ β) = cong₂ _∥_ (cast-trans _ _ α) (cast-trans _ _ β)
cast-trans eq₁ eq₂ (α ; β) = cong₂ _;_ (cast-trans _ _ α) (cast-trans _ _ β)

cast-is-id : .{eq : n ≡ n} → cast eq ≗ id
cast-is-id (` x) = cong `_ (Fin.cast-is-id _ x)
cast-is-id [] = refl
cast-is-id (α ∥ β) = cong₂ _∥_ (cast-is-id α) (cast-is-id β)
cast-is-id (α ; β) = cong₂ _;_ (cast-is-id α) (cast-is-id β)

cast-involutive : .(eq₁ : m ≡ n) .(eq₂ : n ≡ m) →
  cast eq₁ ∘ cast eq₂ ≗ id
cast-involutive eq₁ eq₂ x = cast-trans eq₂ eq₁ x ■ cast-is-id x

subst-is-cast : (eq : m ≡ n) → subst Struct eq ≗ cast eq
subst-is-cast refl (` x) = cong `_ (sym (Fin.cast-is-id refl x))
subst-is-cast refl [] = refl
subst-is-cast refl (x ∥ y) = cong₂ _∥_ (subst-is-cast refl x) (subst-is-cast refl y)
subst-is-cast refl (x ; y) = cong₂ _;_ (subst-is-cast refl x) (subst-is-cast refl y)

module _ {ℓ} (P : Pred 𝕋 ℓ) (Γ : Ctx n) where
  data AllCx : Struct n → Set ℓ where
    []  : AllCx []
    _∥_ : AllCx α → AllCx β → AllCx (α ∥ β)
    _;_ : AllCx α → AllCx β → AllCx (α ; β)
    `_  : ∀ {x} → P (lookup Γ x) → AllCx (` x)

module _ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} where
  allCx-`-injective : ∀ {x} {p q : P (Γ ﹫ x)} → (AllCx P Γ (` x) ∋ (` p)) ≡ (` q) → p ≡ q
  allCx-`-injective refl = refl

  allCx-`⁻¹ : ∀ {x} → AllCx P Γ (` x) → P (Γ ﹫ x)
  allCx-`⁻¹ (` px) = px

  allCx-`⁻¹-injective : ∀ {x} {p q : AllCx P Γ (` x)} → allCx-`⁻¹ p ≡ allCx-`⁻¹ q → p ≡ q
  allCx-`⁻¹-injective {p = ` _} {` _} eq = cong `_ eq

  allCx-∥⁻¹ : AllCx P Γ (α ∥ β) → AllCx P Γ α × AllCx P Γ β
  allCx-∥⁻¹ (x ∥ y) = x , y

  allCx-;⁻¹ : AllCx P Γ (α ; β) → AllCx P Γ α × AllCx P Γ β
  allCx-;⁻¹ (x ; y) = x , y

  allCx? : Decidable P → Decidable (AllCx P Γ)
  allCx? P? (` x) = map′ `_ (λ{ (` Px) → Px }) (P? (lookup Γ x))
  allCx? P? [] = yes []
  allCx? P? (α ∥ β) = map′ (uncurry _∥_) allCx-∥⁻¹ (allCx? P? α ×-dec allCx? P? β)
  allCx? P? (α ; β) = map′ (uncurry _;_) allCx-;⁻¹ (allCx? P? α ×-dec allCx? P? β)

module _ {p q} {P : Pred 𝕋 p} {Q : Pred 𝕋 q} where
  allCx-map⁺ : {f : 𝕋 → 𝕋} → P ⊆ Q ∘ f → AllCx P Γ ⊆ AllCx Q (V.map f Γ)
  allCx-map⁺ p⊆q [] = []
  allCx-map⁺ p⊆q (α ∥ β) = allCx-map⁺ p⊆q α ∥ allCx-map⁺ p⊆q β
  allCx-map⁺ p⊆q (α ; β) = allCx-map⁺ p⊆q α ; allCx-map⁺ p⊆q β
  allCx-map⁺ {Γ = Γ} {f = f} p⊆q (` px) = ` subst Q (sym (V.lookup-map _ f Γ)) (p⊆q px)

  allCx-map : (P ⊆ Q) → AllCx P Γ ⊆ AllCx Q Γ
  allCx-map p⊆q = subst (λ Γ → AllCx Q Γ _) (V.map-id _) ∘ allCx-map⁺ {f = id} p⊆q

UnrCx : REL (Ctx n) (Struct n) _
UnrCx = AllCx Unr

MobCx : REL (Ctx n) (Struct n) _
MobCx = AllCx Mobile

unrCx? : Un.Decidable (UnrCx Γ)
unrCx? = allCx? unr?

UnrCx⇒MobCx : UnrCx Γ ⊆ MobCx Γ
UnrCx⇒MobCx = allCx-map unr⇒mobile
