module BorrowedCF.Context.Substitution where

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import Data.Bool.Properties
open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
open import Function.Related.Propositional
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)

open import BorrowedCF.Prelude
open import BorrowedCF.Types hiding (Kind)
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext

open import BorrowedCF.FinKits as Kits hiding (Syntax)

open Nat.Variables
open Variables

open module Syntax = Kits.Syntax record
  { Tm = Struct
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Tm; `_; Traversal)
  renaming (id to idₖ)
  public

infixl 5 _⋯_

_⋯_ : ⦃ K : Kit 𝓕 ⦄ → Struct m → m –[ K ]→ n → Struct n
` x   ⋯ σ = `/id (σ x)
[]    ⋯ σ = []
α ∥ β ⋯ σ = (α ⋯ σ) ∥ (β ⋯ σ)
α ; β ⋯ σ = (α ⋯ σ) ; (β ⋯ σ)

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (γ : Struct m) {σ₁ σ₂ : m –[ K ]→ n} → σ₁ ≗ σ₂ → γ ⋯ σ₁ ≡ γ ⋯ σ₂
⋯-cong (` x)    eq = cong `/id (eq x)
⋯-cong []       eq = refl
⋯-cong (x ∥ x₁) eq = cong₂ _∥_ (⋯-cong x eq) (⋯-cong x₁ eq)
⋯-cong (x ; x₁) eq = cong₂ _;_ (⋯-cong x eq) (⋯-cong x₁ eq)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (γ : Struct n) {σ : n –[ K ]→ n} → σ ≗ idₖ → γ ⋯ σ ≡ γ
⋯-id (` x)    eq rewrite eq x = `/`-is-` x
⋯-id []       eq = refl
⋯-id (x ∥ x₁) eq = cong₂ _∥_ (⋯-id x eq) (⋯-id x₁ eq)
⋯-id (x ; x₁) eq = cong₂ _;_ (⋯-id x eq) (⋯-id x₁ eq)

open module Traversal = Syntax.Traversal record
  { _⋯_    = _⋯_
  ; ⋯-var  = λ x ϕ → refl
  ; ⋯-id   = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-var; ⋯-id; ⋯-cong)
  public

fusion :  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄
          ⦃ C : CKit K₁ K₂ K ⦄ (γ : Struct n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
          γ ⋯ ϕ₁ ⋯ ϕ₂ ≡ γ ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x)   ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion []      ϕ₁ ϕ₂ = refl
fusion (α ∥ β) ϕ₁ ϕ₂ = cong₂ _∥_ (fusion α _ _) (fusion β _ _)
fusion (α ; β) ϕ₁ ϕ₂ = cong₂ _;_ (fusion α _ _) (fusion β _ _)

open CTraversal record { fusion = fusion } hiding (fusion) public

∥-injective : α₁ ∥ α₂ ≡ β₁ ∥ β₂ → α₁ ≡ β₁ × α₂ ≡ β₂
∥-injective refl = refl , refl

;-injective : α₁ ; α₂ ≡ β₁ ; β₂ → α₁ ≡ β₁ × α₂ ≡ β₂
;-injective refl = refl , refl

⋯-injective : {ϕ : m →ᵣ n} → Inj ϕ → α ⋯ ϕ ≡ β ⋯ ϕ → α ≡ β
⋯-injective {α = ` x} {` y} ϕ-inj eq = cong `_ (ϕ-inj (`-injective eq))
⋯-injective {α = []} {[]} ϕ-inj eq = refl
⋯-injective {α = _ ∥ _} {_ ∥ _} ϕ-inj eq = cong₂ _∥_ (⋯-injective ϕ-inj (∥-injective eq .proj₁)) (⋯-injective ϕ-inj (∥-injective eq .proj₂))
⋯-injective {α = _ ; _} {_ ; _} ϕ-inj eq = cong₂ _;_ (⋯-injective ϕ-inj (;-injective eq .proj₁)) (⋯-injective ϕ-inj (;-injective eq .proj₂))

data PhiKind : Set where
  implication : PhiKind
  equivalence : PhiKind

⌊_⌋ϕ : PhiKind → Kind
⌊ implication ⌋ϕ = implication
⌊ equivalence ⌋ϕ = bijection

infix 4 _∶_∼[_]_ _∶_⇒_ _∶_⇔_

_∶_∼[_]_ : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Ctx m → PhiKind → Ctx n → Set
ϕ ∶ Γ ∼[ implication ] Γ′ = ∀ x → (Unr (Γ ﹫ x) → UnrCx Γ′ (`/id (ϕ x))) × (Mobile (Γ ﹫ x) → MobCx Γ′ (`/id (ϕ x)))
ϕ ∶ Γ ∼[ equivalence ] Γ′ = ∀ x → ∃[ y ] `/id (ϕ x) ≡ ` y × Γ ﹫ x ≡ Γ′ ﹫ y

_∶_⇒_ : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Ctx m → Ctx n → Set
_∶_⇒_ = _∶_∼[ implication ]_

_∶_⇔_ : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Ctx m → Ctx n → Set
_∶_⇔_ = _∶_∼[ equivalence ]_

infix 4 _Preserves[_]_∼⟨_⟩_ _Preserves[_]_⇒_ _Preserves[_]_⇐_ _Preserves[_]_⇔_

_Preserves[_]_∼⟨_⟩_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Kind → Ctx n → Set _
ϕ Preserves[ P ] Γ₁ ∼⟨ k ⟩ Γ₂ = ∀ x → P (lookup Γ₁ x) ∼[ k ] AllCx P Γ₂ (`/id (ϕ x))

_Preserves[_]_⇒_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
_Preserves[_]_⇒_ = _Preserves[_]_∼⟨ implication ⟩_

_Preserves[_]_⇐_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
_Preserves[_]_⇐_ = _Preserves[_]_∼⟨ reverseImplication ⟩_

_Preserves[_]_⇔_ : ∀ {ℓ} ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Pred 𝕋 ℓ → Ctx m → Ctx n → Set _
_Preserves[_]_⇔_ = _Preserves[_]_∼⟨ bijection ⟩_

preserves-unr : ⦃ K : Kit 𝓕 ⦄ (Γ : Ctx m) {Γ′ : Ctx n} {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ⇒ Γ′ → ϕ Preserves[ Unr ] Γ ⇒ Γ′
preserves-unr Γ ϕ-⇒ x = mk⟶ (ϕ-⇒ x .proj₁)

preserves-mob : ⦃ K : Kit 𝓕 ⦄ (Γ : Ctx m) {Γ′ : Ctx n} {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ⇒ Γ′ → ϕ Preserves[ Mobile ] Γ ⇒ Γ′
preserves-mob Γ ϕ-⇒ x = mk⟶ (ϕ-⇒ x .proj₂)

⇔-preserves : ∀ {p} {P : Pred 𝕋 p} ⦃ K : Kit 𝓕 ⦄ (Γ : Ctx m) {Γ′ : Ctx n} {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ⇔ Γ′ → ϕ Preserves[ P ] Γ ⇔ Γ′
⇔-preserves {P = P} Γ {Γ′} ϕ-⇔ x =
  let _ , eq-`/id , eq-T = ϕ-⇔ x in
  let subst-AllCx = subst (AllCx P Γ′) in
  mk↔ₛ′ (subst-AllCx (sym eq-`/id) ∘ `_ ∘ subst P eq-T)
        (subst P (sym eq-T) ∘ allCx-`⁻¹ ∘ subst-AllCx eq-`/id)
        (λ y → cong (subst-AllCx (sym eq-`/id) ∘ `_) (subst-subst-sym {P = P} eq-T)
                 ■ cong (subst-AllCx (sym eq-`/id)) (allCx-`⁻¹-injective refl)
                 ■ subst-sym-subst eq-`/id)
        (λ y → cong (subst P (sym eq-T) ∘ allCx-`⁻¹) (subst-subst-sym {P = AllCx P Γ′} eq-`/id)
                 ■ subst-sym-subst eq-T)

⇔-preserves[_] : ∀ k {p} {P : Pred 𝕋 p} ⦃ K : Kit 𝓕 ⦄ (Γ : Ctx m) {Γ′ : Ctx n} {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ⇔ Γ′ → ϕ Preserves[ P ] Γ ∼⟨ k ⟩ Γ′
⇔-preserves[ k ] ⦃ K ⦄ Γ ϕ-⇔ x = ↔⇒ {k = k} (⇔-preserves ⦃ K ⦄ Γ ϕ-⇔ x)

⇔→⇒ : ⦃ K : Kit 𝓕 ⦄ {Γ : Ctx m} {Γ′ : Ctx n} {ϕ : m –[ K ]→ n} → ϕ ∶ Γ ⇔ Γ′ → ϕ ∶ Γ ⇒ Γ′
⇔→⇒ ⦃ K ⦄ {Γ} ϕ-⇔ x = Inverse.to (⇔-preserves ⦃ K ⦄ Γ ϕ-⇔ x) , Inverse.to (⇔-preserves ⦃ K ⦄ Γ ϕ-⇔ x)

id-⇔ : ⦃ K : Kit 𝓕 ⦄ (Γ : Ctx n) → idₖ ⦃ K ⦄ ∶ Γ ⇔ Γ
id-⇔ ⦃ K ⦄ _ x = _ , `/`-is-` ⦃ K ⦄ x , refl

wk-⇔ : ⦃ K : Kit 𝓕 ⦄ {Γ : Ctx n} → weaken ⦃ K ⦄ ∶ Γ ⇔ T ∷ Γ
wk-⇔ ⦃ K ⦄ x = _ , (cong (`/id ⦃ K ⦄) (wk-id/` x) ■ `/`-is-` ⦃ K ⦄ (suc x)) , refl

wk*-⇔ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ (Γ : Ctx m) {Γ′ : Ctx n} → weaken* ⦃ K ⦄ m ∶ Γ′ ⇔ Γ ⸴* Γ′
wk*-⇔ ⦃ K ⦄ []      {Γ′} = id-⇔ ⦃ K ⦄ Γ′
wk*-⇔ ⦃ K ⦄ (T ∷ Γ) {Γ′} = Π.map suc (Π.map₁ λ eq → sym (wk-`/id _) ■ cong wk eq ) ∘ wk*-⇔ ⦃ K ⦄ Γ {Γ′}

module _ {ℓ} {P : Pred 𝕋 ℓ} where
  allCx-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇒ Γ₂ → AllCx P Γ₁ γ → AllCx P Γ₂ (γ ⋯ ϕ)
  allCx-⋯ P⇒ΠP []      = []
  allCx-⋯ P⇒ΠP (x ∥ y) = allCx-⋯ P⇒ΠP x ∥ allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (x ; y) = allCx-⋯ P⇒ΠP x ; allCx-⋯ P⇒ΠP y
  allCx-⋯ P⇒ΠP (` Px)  = P⇒ΠP _ ⟨$⟩ Px

  allCx-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇐ Γ₂ → AllCx P Γ₂ (γ ⋯ ϕ) → AllCx P Γ₁ γ
  allCx-⋯⁻¹ {γ = ` _}   ϕ-pres x = ` ϕ-pres _ .Func.to x
  allCx-⋯⁻¹ {γ = []}    ϕ-pres x = []
  allCx-⋯⁻¹ {γ = _ ∥ _} ϕ-pres (x ∥ y) = allCx-⋯⁻¹ ϕ-pres x ∥ allCx-⋯⁻¹ ϕ-pres y
  allCx-⋯⁻¹ {γ = _ ; _} ϕ-pres (x ; y) = allCx-⋯⁻¹ ϕ-pres x ; allCx-⋯⁻¹ ϕ-pres y

  allCx-⋯± : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ϕ Preserves[ P ] Γ₁ ⇔ Γ₂ → AllCx P Γ₁ γ ⇔ AllCx P Γ₂ (γ ⋯ ϕ)
  allCx-⋯± ϕ-pres = mk⇔ (allCx-⋯ (↔⇒ {k = implication} ∘ ϕ-pres)) (allCx-⋯⁻¹ (↔⇒ {k = reverseImplication} ∘ ϕ-pres))

  allCx-wk : ⦃ K : Kit 𝓕 ⦄ {Γ : Ctx n} → AllCx P Γ γ → AllCx P (T ⸴ Γ) (γ ⋯ weaken ⦃ K ⦄)
  allCx-wk ⦃ K ⦄ {Γ} = allCx-⋯ (⇔-preserves[ implication ] ⦃ K ⦄ Γ (wk-⇔ ⦃ K ⦄))

↑-⇒ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → ϕ ∶ Γ₁ ⇒ Γ₂ → ϕ ↑ ∶ T ∷ Γ₁ ⇒ T ∷ Γ₂
↑-⇒ ⦃ K ⦄ ϕ-⇒ zero =
  subst (UnrCx _) (sym (`/`-is-` ⦃ K ⦄ zero)) ∘ `_
    , subst (MobCx _) (sym (`/`-is-` ⦃ K ⦄ zero)) ∘ `_
↑-⇒ {Γ₂ = Γ₂} ϕ-⇒ (suc x) =
  Π.map (λ uϕ ux → subst (UnrCx _) (wk-`/id _) (allCx-wk (uϕ ux)))
        (λ mϕ mx → subst (MobCx _) (wk-`/id _) (allCx-wk (mϕ mx)))
        (ϕ-⇒ x)

↑-⇔ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → ϕ ∶ Γ₁ ⇔ Γ₂ → ϕ ↑ ∶ T ∷ Γ₁ ⇔ T ∷ Γ₂
↑-⇔ ⦃ K = K ⦄ ϕ⇔ zero    = zero , `/`-is-` ⦃ K ⦄ zero , refl
↑-⇔ ⦃ K = K ⦄ ϕ⇔ (suc x) = Π.map suc (Π.map₁ (λ eq → sym (wk-`/id _) ■ cong wk eq)) (ϕ⇔ x)

↑*-⇒ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ (Γ : Ctx m) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {ϕ : n₁ –[ K ]→ n₂} →
  ϕ ∶ Γ₁ ⇒ Γ₂ → ϕ ↑* m ∶ Γ ⸴* Γ₁ ⇒ Γ ⸴* Γ₂
↑*-⇒ []      ϕ-⇒ = ϕ-⇒
↑*-⇒ (T ⸴ Γ) ϕ-⇒ = ↑-⇒ (↑*-⇒ Γ ϕ-⇒)

↑*-⇔ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ (Γ : Ctx m) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {ϕ : n₁ –[ K ]→ n₂} →
  ϕ ∶ Γ₁ ⇔ Γ₂ → ϕ ↑* m ∶ Γ ⸴* Γ₁ ⇔ Γ ⸴* Γ₂
↑*-⇔ []      ϕ⇔ = ϕ⇔
↑*-⇔ (T ⸴ Γ) ϕ⇔ = ↑-⇔ (↑*-⇔ Γ ϕ⇔)

≈′-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ ∶ Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≈′ β →
  Γ₂ ∶ α ⋯ ϕ ≈′ β ⋯ ϕ
≈′-⋯ ϕ⇒ ;′-assoc     = ;′-assoc
≈′-⋯ ϕ⇒ (;′-cong₁ x) = ;′-cong₁ (≈′-⋯ ϕ⇒ x)
≈′-⋯ ϕ⇒ (;′-cong₂ x) = ;′-cong₂ (≈′-⋯ ϕ⇒ x)
≈′-⋯ ϕ⇒ ∥′-unit      = ∥′-unit
≈′-⋯ ϕ⇒ ∥′-assoc     = ∥′-assoc
≈′-⋯ ϕ⇒ ∥′-comm      = ∥′-comm
≈′-⋯ ϕ⇒ (∥′-cong₁ x) = ∥′-cong₁ (≈′-⋯ ϕ⇒ x)
≈′-⋯ {Γ₁ = Γ₁} ⦃ K ⦄ ϕ⇒ (∥′-dup U) =
  ∥′-dup (allCx-⋯ (preserves-unr ⦃ K ⦄ Γ₁ ϕ⇒) U)
≈′-⋯ {Γ₁ = Γ₁} ⦃ K ⦄ ϕ⇒ (∥′-tm-; U) =
  ∥′-tm-; (Sum.map (allCx-⋯ (preserves-mob ⦃ K ⦄ Γ₁ ϕ⇒))
                   (allCx-⋯ (preserves-mob ⦃ K ⦄ Γ₁ ϕ⇒)) U)

≈-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ ∶ Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≈ β →
  Γ₂ ∶ α ⋯ ϕ ≈ β ⋯ ϕ
≈-⋯ ϕ⇒ = Eq*.gmap _ (≈′-⋯ ϕ⇒)

≈′-inv-[] : Γ ∶ α ∥ β ≈′ [] → Γ ∶ α ≈ [] × Γ ∶ β ≈ []
≈′-inv-[] ∥′-unit = refl , refl

∥′-unit⁻¹ : ∀ {x y} → Γ ∶ (` x) ∥ [] ≈′ (` y) → x ≡ y
∥′-unit⁻¹ ∥′-unit = refl

∥′-dup⁻¹ : ∀ {x y z} → Γ ∶ ` x ≈′ (` y) ∥ (` z) → x ≡ y × x ≡ z × Unr (lookup Γ x)
∥′-dup⁻¹ (∥′-dup (` U)) = refl , refl , U

≈′-⋯⁻¹ : {ϕ : m →ᵣ n} →
  Inj ϕ →
  ϕ ∶ Γ₁ ⇔ Γ₂ →
  Γ₂ ∶ α ⋯ ϕ ≈′ β ⋯ ϕ →
  Γ₁ ∶ α ≈′ β
≈′-⋯⁻¹ {α = α} {β} {ϕ = ϕ} inj-ϕ ϕ⇔ x with α ⋯ ϕ in eqᵃ | β ⋯ ϕ in eqᵇ

≈′-⋯⁻¹ {α = α₁ ; α₂} {β₁ ; β₂} inj-ϕ ϕ⇔ (;′-cong₁ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₂} {β₂} inj-ϕ (;-injective eqᵃ .proj₂ ■ sym (;-injective eqᵇ .proj₂))
  = ;′-cong₁ (≈′-⋯⁻¹ inj-ϕ ϕ⇔ (subst₂ (_ ∶_≈′_) (sym (;-injective eqᵃ .proj₁)) (sym (;-injective eqᵇ .proj₁)) x))

≈′-⋯⁻¹ {α = α₁ ; α₂} {β₁ ; β₂} inj-ϕ ϕ⇔ (;′-cong₂ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₁} {β₁} inj-ϕ (;-injective eqᵃ .proj₁ ■ sym (;-injective eqᵇ .proj₁))
  = ;′-cong₂ (≈′-⋯⁻¹ inj-ϕ ϕ⇔ (subst₂ (_ ∶_≈′_) (sym (;-injective eqᵃ .proj₂)) (sym (;-injective eqᵇ .proj₂)) x))

≈′-⋯⁻¹ {α = (α₁ ; β₁) ; γ₁} {α₂ ; (β₂ ; γ₂)} inj-ϕ ϕ⇔ ;′-assoc | ϕα | ϕβ
  with eqᵃ′ , refl ← ;-injective eqᵃ
  with refl , refl ← ;-injective eqᵃ′
  rewrite ⋯-injective {α = α₂} {α₁} inj-ϕ (;-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {β₁} inj-ϕ (;-injective (;-injective eqᵇ .proj₂) .proj₁)
  rewrite ⋯-injective {α = γ₂} {γ₁} inj-ϕ (;-injective (;-injective eqᵇ .proj₂) .proj₂)
  = ;′-assoc

≈′-⋯⁻¹ {α = α ∥ []} {β} inj-ϕ ϕ⇔ ∥′-unit | ϕα | ϕβ
  rewrite ⋯-injective {α = α} {β} inj-ϕ (∥-injective eqᵃ .proj₁ ■ sym eqᵇ)
  = ∥′-unit

≈′-⋯⁻¹ {α = (α₁ ∥ β₁) ∥ γ₁} {α₂ ∥ (β₂ ∥ γ₂)} inj-ϕ ϕ⇔ ∥′-assoc | ϕα | ϕβ
  with eqᵃ′ , refl ← ∥-injective eqᵃ
  with refl , refl ← ∥-injective eqᵃ′
  rewrite ⋯-injective {α = α₂} {α₁} inj-ϕ (∥-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {β₁} inj-ϕ (∥-injective (∥-injective eqᵇ .proj₂) .proj₁)
  rewrite ⋯-injective {α = γ₂} {γ₁} inj-ϕ (∥-injective (∥-injective eqᵇ .proj₂) .proj₂)
  = ∥′-assoc

≈′-⋯⁻¹ {α = α₁ ∥ α₂} {β₁ ∥ β₂} inj-ϕ ϕ⇔ ∥′-comm | ϕα | ϕβ
  using α₁≡α , α₂≡β ← ∥-injective eqᵃ
  using β₁≡β , β₂≡α ← ∥-injective eqᵇ
  rewrite ⋯-injective {α = α₁} {β₂} inj-ϕ (α₁≡α ■ sym β₂≡α)
  rewrite ⋯-injective {α = α₂} {β₁} inj-ϕ (α₂≡β ■ sym β₁≡β)
  = ∥′-comm

≈′-⋯⁻¹ {α = α₁ ∥ α₂} {β₁ ∥ β₂} inj-ϕ ϕ⇔ (∥′-cong₁ x) | ϕα | ϕβ
  rewrite ⋯-injective {α = α₂} {β₂} inj-ϕ (∥-injective eqᵃ .proj₂ ■ sym (∥-injective eqᵇ .proj₂))
  = ∥′-cong₁ (≈′-⋯⁻¹ inj-ϕ ϕ⇔ (subst₂ (_ ∶_≈′_) (sym (∥-injective eqᵃ .proj₁)) (sym (∥-injective eqᵇ .proj₁)) x))

≈′-⋯⁻¹ {Γ₁ = Γ₁} {α = α} {β₁ ∥ β₂} {ϕ = ϕ} inj-ϕ ϕ⇔ (∥′-dup U) | ϕα | ϕβ
  rewrite sym eqᵃ
  rewrite ⋯-injective {α = β₁} {α} inj-ϕ (∥-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {α} inj-ϕ (∥-injective eqᵇ .proj₂)
  = ∥′-dup (allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₁ ϕ⇔) U)

≈′-⋯⁻¹ {Γ₁ = Γ₁} {α = α₁ ∥ α₂} {β₁ ; β₂} {ϕ = ϕ} inj-ϕ ϕ⇔ (∥′-tm-; U) | ϕα | ϕβ
  with refl , refl ← ∥-injective eqᵃ
  rewrite ⋯-injective {α = β₁} {α₁} inj-ϕ (;-injective eqᵇ .proj₁)
  rewrite ⋯-injective {α = β₂} {α₂} inj-ϕ (;-injective eqᵇ .proj₂)
  = ∥′-tm-; (Sum.map (allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₁ ϕ⇔))
                     (allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₁ ϕ⇔)) U)

≼-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} →
  ϕ ∶ Γ₁ ⇒ Γ₂ →
  Γ₁ ∶ α ≼ β →
  Γ₂ ∶ α ⋯ ϕ ≼ β ⋯ ϕ
≼-⋯ ϕ⇒ (≼-refl eq)    = ≼-refl (≈-⋯ ϕ⇒ eq)
≼-⋯ ϕ⇒ ≼-wk           = ≼-wk
≼-⋯ ϕ⇒ (≼-trans  x y) = ≼-trans  (≼-⋯ ϕ⇒ x) (≼-⋯ ϕ⇒ y)
≼-⋯ ϕ⇒ (≼-cong-; x y) = ≼-cong-; (≼-⋯ ϕ⇒ x) (≼-⋯ ϕ⇒ y)
≼-⋯ ϕ⇒ (≼-cong-∥ x y) = ≼-cong-∥ (≼-⋯ ϕ⇒ x) (≼-⋯ ϕ⇒ y)
≼-⋯ {Γ₁ = Γ₁} ⦃ K ⦄ ϕ⇒ (≼-∅ U) = ≼-∅ (allCx-⋯ (preserves-unr ⦃ K ⦄ Γ₁ ϕ⇒) U)

-- Properties about _↓_ and substitutions.
↓-dist-wk : ∀ (γ : Struct n) {x X} → wk γ ↓ (x ∷ X) ≡ wk (γ ↓ X)
↓-dist-wk (` y) {x} {X} = sym (if-float wk (does (y ∈? X)))
↓-dist-wk []      = refl
↓-dist-wk (α ∥ β) = cong₂ _∥_ (↓-dist-wk α) (↓-dist-wk β)
↓-dist-wk (α ; β) = cong₂ _;_ (↓-dist-wk α) (↓-dist-wk β)

↓-dist-wk-tail : ∀ (γ : Struct n) X → wk γ ↓ X ≡ wk (γ ↓ V.tail X)
↓-dist-wk-tail γ (x ∷ X) = ↓-dist-wk γ

↓-dist-wk* : (γ : Struct n) (X : Subset m) {Y : Subset n} → (γ ⋯ᵣ weaken* m) ↓ (X V.++ Y) ≡ (γ ↓ Y) ⋯ᵣ weaken* m
↓-dist-wk* γ [] {Y} =
  cong (_↓ Y) (⋯-id ⦃ Kᵣ ⦄ γ (λ _ → refl))
    ■ sym (⋯-id ⦃ Kᵣ ⦄ (γ ↓ Y) λ _ → refl)
↓-dist-wk* γ (x ⸴ X) {Y} =
  cong (_↓ (x ⸴ X ⸴* Y)) (sym (fusion γ (weaken* _) weakenᵣ))
    ■ ↓-dist-wk (γ ⋯ᵣ weaken* _)
    ■ cong wk (↓-dist-wk* γ X)
    ■ fusion (γ ↓ Y) (weaken* _) weakenᵣ


infix 4 _∈img_

-- The set of variables in the image of the renaming.
_∈img_ : 𝔽 n → m →ᵣ n → Set
y ∈img ρ = ∃[ x ] ρ x ≡ y

∈img-↑*⁻ : ∀ m {ρ : n₁ →ᵣ n₂} x →
  m ↑ʳ x ∈img ρ ↑* m → x ∈img ρ
∈img-↑*⁻ zero    x ↑x∈          = ↑x∈
∈img-↑*⁻ (suc m) x (suc y , eq) = ∈img-↑*⁻ m x (y , Fin.suc-injective eq)

∈dom⋯⇒∈img : (α : Struct m) {ϕ : m →ᵣ n} {y : 𝔽 n} → y ∈ dom (α ⋯ ϕ) → y ∈img ϕ
∈dom⋯⇒∈img (` x)   y∈ = x , sym (x∈⁅y⁆⇒x≡y _ y∈)
∈dom⋯⇒∈img []      y∈ = ⊥-elim (∉⁅⁆ y∈)
∈dom⋯⇒∈img (α ∥ β) y∈ = [ ∈dom⋯⇒∈img α , ∈dom⋯⇒∈img β ]′ (x∈p∪q⁻ _ _ y∈)
∈dom⋯⇒∈img (α ; β) y∈ = [ ∈dom⋯⇒∈img α , ∈dom⋯⇒∈img β ]′ (x∈p∪q⁻ _ _ y∈)

⋯-preimage : {ρ : m →ᵣ n} (γ : Struct n) → (∀ {y} → y ∈ dom γ → y ∈img ρ) → ∃[ γ′ ] γ′ ⋯ ρ ≡ γ
⋯-preimage []       f = [] , refl
⋯-preimage (` y)    f = let x , eq = f (x∈⁅x⁆ y) in ` x , cong `_ eq
⋯-preimage (α ∥ β)  f =
  let γ₁ , e₁ = ⋯-preimage α (f ∘ x∈p∪q⁺ ∘ inj₁)
      γ₂ , e₂ = ⋯-preimage β (f ∘ x∈p∪q⁺ ∘ inj₂)
  in γ₁ ∥ γ₂ , cong₂ _∥_ e₁ e₂
⋯-preimage (α ; β) f =
  let γ₁ , e₁ = ⋯-preimage α (f ∘ x∈p∪q⁺ ∘ inj₁)
      γ₂ , e₂ = ⋯-preimage β (f ∘ x∈p∪q⁺ ∘ inj₂)
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

⋯≡;⁻¹ : (α : Struct m) {ϕ : m →ᵣ n} {γ₁ γ₂ : Struct n} →
  α ⋯ ϕ ≡ γ₁ ; γ₂ → ∃[ α₁ ] ∃[ α₂ ] α ≡ α₁ ; α₂ × α₁ ⋯ ϕ ≡ γ₁ × α₂ ⋯ ϕ ≡ γ₂
⋯≡;⁻¹ (α₁ ; α₂) refl = _ , _ , refl , refl , refl
⋯≡;⁻¹ (` x)        ()
⋯≡;⁻¹ []           ()
⋯≡;⁻¹ (α ∥ β)      ()

≈-⋯⁻¹ : {ϕ : m →ᵣ n} → Inj ϕ → ϕ ∶ Γ₁ ⇔ Γ₂ → Γ₂ ∶ α ⋯ ϕ ≈ β ⋯ ϕ → Γ₁ ∶ α ≈ β
≈-⋯⁻¹ {Γ₁ = Γ₁} {Γ₂} {ϕ = ϕ} inj ϕ⇔ eq = go _ eq refl
  where
  sym-map⁻¹-⋯ : SymClosure (Γ₂ ∶_≈′_) (α ⋯ ϕ) (β ⋯ ϕ) → SymClosure (Γ₁ ∶_≈′_) α β
  sym-map⁻¹-⋯ (fwd x) = fwd (≈′-⋯⁻¹ inj ϕ⇔ x)
  sym-map⁻¹-⋯ (bwd x) = bwd (≈′-⋯⁻¹ inj ϕ⇔ x)

  go : ∀ α → Γ₂ ∶ α ⋯ ϕ ≈ γ → γ ≡ β ⋯ ϕ → Γ₁ ∶ α ≈ β
  go α refl eq = ≈-reflexive (⋯-injective inj eq)
  go α (_◅_ {j = γ} x xs) eq
    with γ′ , refl ← ⋯-preimage γ (∈dom⋯⇒∈img α ∘ subst (_ ∈_) (sym (≈⇒dom≡ (Star.return x))))
    = sym-map⁻¹-⋯ x ◅ go γ′ xs eq

≼-⋯⁻¹ : {ϕ : m →ᵣ n} → Inj ϕ → ϕ ∶ Γ₁ ⇔ Γ₂ → Γ₂ ∶ α ⋯ ϕ ≼ β ⋯ ϕ → Γ₁ ∶ α ≼ β
≼-⋯⁻¹ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ϕ = ϕ} inj ϕ⇔ H = go H refl refl
  where
  go : ∀ {A B} → Γ₂ ∶ A ≼ B → ∀ {α β} → A ≡ α ⋯ ϕ → B ≡ β ⋯ ϕ → Γ₁ ∶ α ≼ β
  go (≼-refl x) eqa eqb = ≼-refl (≈-⋯⁻¹ inj ϕ⇔ (subst₂ (_ ∶_≈_) eqa eqb x))
  go (≼-∅ U) {α} eqa eqb rewrite ⋯≡[]⁻¹ α (sym eqa) =
    ≼-∅ (allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₁ ϕ⇔) (subst (UnrCx _) eqb U))
  go (≼-trans {β = Mid} x y) {α} {β} eqa eqb
    with ⋯-preimage Mid (λ {z} z∈ → ∈dom⋯⇒∈img β (subst (z ∈_) (cong dom eqb) (≼⇒dom⊆ y z∈)))
  ... | pre , eqm = ≼-trans (go x {β = pre} eqa (sym eqm)) (go y {α = pre} (sym eqm) eqb)
  go (≼-wk {α₁} {α₂} {β₁} {β₂}) {α} {β} eqa eqb
    with ⋯≡;⁻¹ α (sym eqa)
  ... | p , q , α≡ , ep , eq
    with ⋯≡∥⁻¹ p ep | ⋯≡∥⁻¹ q eq
  ... | p₁ , p₂ , p≡ , ep₁ , ep₂ | q₁ , q₂ , q≡ , eq₁ , eq₂
    with ⋯≡∥⁻¹ β (sym eqb)
  ... | s₁ , s₂ , β≡ , es₁ , es₂
    with ⋯≡;⁻¹ s₁ es₁ | ⋯≡;⁻¹ s₂ es₂
  ... | c₁ , d₁ , s₁≡ , ec₁ , ed₁ | c₂ , d₂ , s₂≡ , ec₂ , ed₂
    rewrite α≡ | p≡ | q≡ | β≡ | s₁≡ | s₂≡
          | ⋯-injective {α = p₁} {β = c₁} inj (ep₁ ■ sym ec₁)
          | ⋯-injective {α = p₂} {β = c₂} inj (ep₂ ■ sym ec₂)
          | ⋯-injective {α = q₁} {β = d₁} inj (eq₁ ■ sym ed₁)
          | ⋯-injective {α = q₂} {β = d₂} inj (eq₂ ■ sym ed₂)
    = ≼-wk
  go (≼-cong-; x y) {α} {β} eqa eqb
    with ⋯≡;⁻¹ α (sym eqa) | ⋯≡;⁻¹ β (sym eqb)
  ... | α₁ , α₂ , α≡ , ea₁ , ea₂ | β₁ , β₂ , β≡ , eb₁ , eb₂ rewrite α≡ | β≡ =
        ≼-cong-; (go x {α = α₁} {β = β₁} (sym ea₁) (sym eb₁)) (go y {α = α₂} {β = β₂} (sym ea₂) (sym eb₂))
  go (≼-cong-∥ x y) {α} {β} eqa eqb
    with ⋯≡∥⁻¹ α (sym eqa) | ⋯≡∥⁻¹ β (sym eqb)
  ... | α₁ , α₂ , α≡ , ea₁ , ea₂ | β₁ , β₂ , β≡ , eb₁ , eb₂ rewrite α≡ | β≡ =
        ≼-cong-∥ (go x {α = α₁} {β = β₁} (sym ea₁) (sym eb₁)) (go y {α = α₂} {β = β₂} (sym ea₂) (sym eb₂))
