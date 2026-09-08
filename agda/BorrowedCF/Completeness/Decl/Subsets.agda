-- | Subset / domain plumbing used by the declarative facts in
--   `BorrowedCF.Completeness.Decl`.  Everything here is about `dom`, `_↓_`
--   and `AllCx`; no typing derivation is mentioned.
module BorrowedCF.Completeness.Decl.Subsets where

open import Data.Fin.Subset as S using (Subset; Side; inside; outside; _∈_; _∉_; _⊆_; _∪_; ∁; ⁅_⁆) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
  using ( _∈?_; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x≢y⇒x∉⁅y⁆; x∈p∪q⁺; x∈p∪q⁻
        ; p⊆p∪q; q⊆p∪q; x∈p⇒x∉∁p; x∈∁p⇒x∉p; x∉p⇒x∈∁p; x∉∁p⇒x∈p
        ; ⊆-refl; ⊆-trans )
  renaming (∉⊥ to ∉⁅⁆)
open import Relation.Nullary.Decidable using (dec-true; dec-false)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

private variable
  α β : Struct n

------------------------------------------------------------------------
-- tail / drop on subsets (the ⁻ directions are in Context.Domain)

∈tail⁺ : {x : 𝔽 n} {X : Subset (suc n)} → suc x ∈ X → x ∈ V.tail X
∈tail⁺ {X = _ ∷ _} (there x∈) = x∈

∈drop⁺ : ∀ m {n} {x : 𝔽 n} {X : Subset (m + n)} → (m ↑ʳ x) ∈ X → x ∈ V.drop m X
∈drop⁺ zero            x∈         = x∈
∈drop⁺ (suc m) {X = _ ∷ _} (there x∈) = ∈drop⁺ m x∈

-- The two bound variables of a binder block are never the image of a
-- weakened variable.
suc∉⁅zero⁆ : {x : 𝔽 n} → suc x ∉ ⁅ zero ⁆
suc∉⁅zero⁆ (there p) = ∉⁅⁆ p

suc²∉⁅zero⁆ : {x : 𝔽 n} → suc (suc x) ∉ ⁅ zero ⁆
suc²∉⁅zero⁆ (there p) = ∉⁅⁆ p

suc²∉⁅suc-zero⁆ : {x : 𝔽 n} → suc (suc x) ∉ ⁅ suc zero ⁆
suc²∉⁅suc-zero⁆ (there (there p)) = ∉⁅⁆ p

------------------------------------------------------------------------
-- dom under weakening

∈dom-wk⁺ : (γ : Struct n) {x : 𝔽 n} → x ∈ dom γ → suc x ∈ dom (𝐂.wk γ)
∈dom-wk⁺ (` y) x∈ with refl ← x∈⁅y⁆⇒x≡y y x∈ = x∈⁅x⁆ (suc y)
∈dom-wk⁺ []    x∈ = ⊥-elim (∉⁅⁆ x∈)
∈dom-wk⁺ (α ∥ β) x∈ =
  x∈p∪q⁺ (Sum.map (∈dom-wk⁺ α) (∈dom-wk⁺ β) (x∈p∪q⁻ (dom α) (dom β) x∈))
∈dom-wk⁺ (α ; β) x∈ =
  x∈p∪q⁺ (Sum.map (∈dom-wk⁺ α) (∈dom-wk⁺ β) (x∈p∪q⁻ (dom α) (dom β) x∈))

∈dom-wk⁻ : (γ : Struct n) {x : 𝔽 n} → suc x ∈ dom (𝐂.wk γ) → x ∈ dom γ
∈dom-wk⁻ (` y) sx∈ with refl ← Fin.suc-injective (x∈⁅y⁆⇒x≡y (suc y) sx∈) = x∈⁅x⁆ y
∈dom-wk⁻ []    sx∈ = ⊥-elim (∉⁅⁆ sx∈)
∈dom-wk⁻ (α ∥ β) sx∈ =
  x∈p∪q⁺ (Sum.map (∈dom-wk⁻ α) (∈dom-wk⁻ β) (x∈p∪q⁻ (dom (𝐂.wk α)) (dom (𝐂.wk β)) sx∈))
∈dom-wk⁻ (α ; β) sx∈ =
  x∈p∪q⁺ (Sum.map (∈dom-wk⁻ α) (∈dom-wk⁻ β) (x∈p∪q⁻ (dom (𝐂.wk α)) (dom (𝐂.wk β)) sx∈))

∈dom-wk²⁺ : (γ : Struct n) {x : 𝔽 n} → x ∈ dom γ → suc (suc x) ∈ dom (𝐂.wk (𝐂.wk γ))
∈dom-wk²⁺ γ = ∈dom-wk⁺ (𝐂.wk γ) ∘ ∈dom-wk⁺ γ

∈dom-wk²⁻ : (γ : Struct n) {x : 𝔽 n} → suc (suc x) ∈ dom (𝐂.wk (𝐂.wk γ)) → x ∈ dom γ
∈dom-wk²⁻ γ = ∈dom-wk⁻ γ ∘ ∈dom-wk⁻ (𝐂.wk γ)

------------------------------------------------------------------------
-- dom of a join

∈-join⁻ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (α β : Struct n) {x : 𝔽 n} →
  x ∈ dom (join a α β) → x ∈ dom α ⊎ x ∈ dom β
∈-join⁻ a α β x∈ = x∈p∪q⁻ (dom α) (dom β) (subst (_ ∈_) (dom-join a α β) x∈)

∈-join⁺ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (α β : Struct n) {x : 𝔽 n} →
  x ∈ dom α ⊎ x ∈ dom β → x ∈ dom (join a α β)
∈-join⁺ a α β x∈ = subst (_ ∈_) (sym (dom-join a α β)) (x∈p∪q⁺ x∈)

------------------------------------------------------------------------
-- AllCx over a restricted structure, pointwise

module _ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} where

  allCx-↓⁻ : (γ : Struct n) {X : Subset n} → AllCx P Γ (γ ↓ X) →
             ∀ {y} → y ∈ dom γ → y ∈ X → P (Γ ﹫ y)
  allCx-↓⁻ (` z) {X} a {y} y∈ y∈X with z ∈? X | a
  ... | yes _  | (` pz) = subst (λ w → P (Γ ﹫ w)) (sym (x∈⁅y⁆⇒x≡y z y∈)) pz
  ... | no  z∉ | _      = ⊥-elim (z∉ (subst (_∈ X) (x∈⁅y⁆⇒x≡y z y∈) y∈X))
  allCx-↓⁻ []      a       y∈ y∈X = ⊥-elim (∉⁅⁆ y∈)
  allCx-↓⁻ (α ∥ β) (a ∥ b) y∈ y∈X =
    [ (λ y∈α → allCx-↓⁻ α a y∈α y∈X) , (λ y∈β → allCx-↓⁻ β b y∈β y∈X) ]′
      (x∈p∪q⁻ (dom α) (dom β) y∈)
  allCx-↓⁻ (α ; β) (a ; b) y∈ y∈X =
    [ (λ y∈α → allCx-↓⁻ α a y∈α y∈X) , (λ y∈β → allCx-↓⁻ β b y∈β y∈X) ]′
      (x∈p∪q⁻ (dom α) (dom β) y∈)

  allCx-↓⁺ : (γ : Struct n) {X : Subset n} →
             (∀ {y} → y ∈ dom γ → y ∈ X → P (Γ ﹫ y)) → AllCx P Γ (γ ↓ X)
  allCx-↓⁺ (` z) {X} h with z ∈? X
  ... | yes z∈ = ` h (x∈⁅x⁆ z) z∈
  ... | no  _  = []
  allCx-↓⁺ []      h = []
  allCx-↓⁺ (α ∥ β) h =
    allCx-↓⁺ α (λ y∈ y∈X → h (x∈p∪q⁺ (inj₁ y∈)) y∈X) ∥
    allCx-↓⁺ β (λ y∈ y∈X → h (x∈p∪q⁺ (inj₂ y∈)) y∈X)
  allCx-↓⁺ (α ; β) h =
    allCx-↓⁺ α (λ y∈ y∈X → h (x∈p∪q⁺ (inj₁ y∈)) y∈X) ;
    allCx-↓⁺ β (λ y∈ y∈X → h (x∈p∪q⁺ (inj₂ y∈)) y∈X)

------------------------------------------------------------------------
-- Growing the restriction set: the variables that are added must be
-- unrestricted, and then the smaller restriction is a subcontext.

↓-≼-↓ : {Γ : Ctx n} (γ : Struct n) {Y X : Subset n} → Y ⊆ X →
        (∀ {z} → z ∈ dom γ → z ∉ Y → Unr (Γ ﹫ z)) →
        Γ ∶ γ ↓ Y ≼ γ ↓ X
↓-≼-↓ (` z) {Y} {X} Y⊆X u with z ∈? Y | z ∈? X
... | yes _  | yes _  = ≼-refl ≈-refl
... | yes z∈ | no  z∉ = ⊥-elim (z∉ (Y⊆X z∈))
... | no  z∉ | yes _  = ≼-∅ (` u (x∈⁅x⁆ z) z∉)
... | no  _  | no  _  = ≼-refl ≈-refl
↓-≼-↓ []      Y⊆X u = ≼-refl ≈-refl
↓-≼-↓ (α ∥ β) Y⊆X u =
  ≼-cong-∥ (↓-≼-↓ α Y⊆X (λ z∈ z∉ → u (x∈p∪q⁺ (inj₁ z∈)) z∉))
           (↓-≼-↓ β Y⊆X (λ z∈ z∉ → u (x∈p∪q⁺ (inj₂ z∈)) z∉))
↓-≼-↓ (α ; β) Y⊆X u =
  ≼-cong-; (↓-≼-↓ α Y⊆X (λ z∈ z∉ → u (x∈p∪q⁺ (inj₁ z∈)) z∉))
           (↓-≼-↓ β Y⊆X (λ z∈ z∉ → u (x∈p∪q⁺ (inj₂ z∈)) z∉))

------------------------------------------------------------------------
-- Binder blocks: the structures the declarative rules build under a
-- binder, restricted to a set that keeps every bound variable.

module _ where
  private
    keep0 : (X : Subset n) → (Struct (suc n) ∋ ` zero) ↓ (inside ∷ X) ≡ ` zero
    keep0 X rewrite dec-true (zero ∈? (inside ∷ X)) here = refl

    keep0² : (X : Subset n) → (Struct (2 + n) ∋ ` zero) ↓ (inside ∷ inside ∷ X) ≡ ` zero
    keep0² X rewrite dec-true (zero ∈? (inside ∷ inside ∷ X)) here = refl

    keep1² : (X : Subset n) → (Struct (2 + n) ∋ ` suc zero) ↓ (inside ∷ inside ∷ X) ≡ ` suc zero
    keep1² X rewrite dec-true (suc zero ∈? (inside ∷ inside ∷ X)) (there here) = refl

    wk²-↓ : (γ : Struct n) {b₁ b₂ : Side} {X : Subset n} →
            𝐂.wk (𝐂.wk γ) ↓ (b₁ ∷ b₂ ∷ X) ≡ 𝐂.wk (𝐂.wk (γ ↓ X))
    wk²-↓ γ = 𝐂.↓-dist-wk (𝐂.wk γ) ■ cong 𝐂.wk (𝐂.↓-dist-wk γ)

  -- One binder (T-Abs, T-Let, T-Case, and the algorithmic A-Let).
  ↓-bind : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (γ : Struct n) (X : Subset n) →
    join a (` zero) (𝐂.wk γ) ↓ (inside ∷ X) ≡ join a (` zero) (𝐂.wk (γ ↓ X))
  ↓-bind a γ X = join-↓ a (` zero) (𝐂.wk γ) ■ cong₂ (join a) (keep0 X) (𝐂.↓-dist-wk γ)

  -- Two binders (T-LetPair).
  ↓-bind² : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B) (γ : Struct n) (X : Subset n) →
    join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)) ↓ (inside ∷ inside ∷ X)
      ≡ join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk (γ ↓ X)))
  ↓-bind² a b γ X =
    join-↓ a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ))
      ■ cong₂ (join a)
          (join-↓ b (` zero) (` suc zero) ■ cong₂ (join b) (keep0² X) (keep1² X))
          (wk²-↓ γ)

  -- Two binders, both parallel (T-AbsRec).
  ↓-absrec : (γ : Struct n) (X : Subset n) →
    (Struct (2 + n) ∋ ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ)) ↓ (inside ∷ inside ∷ X)
      ≡ ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk (γ ↓ X))
  ↓-absrec γ X = cong₂ _∥_ (cong₂ _∥_ (keep0² X) (keep1² X)) (wk²-↓ γ)

------------------------------------------------------------------------
-- Sets that keep every bound variable

⊆-inside∷ : {Z : Subset (suc n)} {X : Subset n} → V.tail Z ⊆ X → Z ⊆ inside ∷ X
⊆-inside∷ h here        = here
⊆-inside∷ h (there y∈)  = there (h y∈)

⊆-inside²∷-tail : {Z : Subset (2 + n)} {X : Subset n} → V.tail (V.tail Z) ⊆ X → Z ⊆ inside ∷ inside ∷ X
⊆-inside²∷-tail h here               = here
⊆-inside²∷-tail h (there here)       = there here
⊆-inside²∷-tail h (there (there y∈)) = there (there (h y∈))

⊆-inside²∷ : {Z : Subset (2 + n)} {X : Subset n} → V.drop 2 Z ⊆ X → Z ⊆ inside ∷ inside ∷ X
⊆-inside²∷ h here                 = here
⊆-inside²∷ h (there here)         = there here
⊆-inside²∷ h (there (there y∈))   = there (there (h y∈))

------------------------------------------------------------------------
-- Membership in the domain of a binder block

∈-bind⁻ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (γ : Struct n) {x : 𝔽 n} →
  suc x ∈ dom (join a (` zero) (𝐂.wk γ)) → x ∈ dom γ
∈-bind⁻ a γ sx∈ =
  [ (λ p → ⊥-elim (suc∉⁅zero⁆ p)) , ∈dom-wk⁻ γ ]′ (∈-join⁻ a (` zero) (𝐂.wk γ) sx∈)

∈-bind⁺ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (γ : Struct n) {x : 𝔽 n} →
  x ∈ dom γ → suc x ∈ dom (join a (` zero) (𝐂.wk γ))
∈-bind⁺ a γ x∈ = ∈-join⁺ a (` zero) (𝐂.wk γ) (inj₂ (∈dom-wk⁺ γ x∈))

∈-bind²⁻ : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B) (γ : Struct n) {x : 𝔽 n} →
  suc (suc x) ∈ dom (join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ))) → x ∈ dom γ
∈-bind²⁻ a b γ sx∈ =
  [ (λ p → [ (λ q → ⊥-elim (suc²∉⁅zero⁆ q)) , (λ q → ⊥-elim (suc²∉⁅suc-zero⁆ q)) ]′
             (∈-join⁻ b (` zero) (` suc zero) p))
  , ∈dom-wk²⁻ γ
  ]′ (∈-join⁻ a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)) sx∈)

∈-bind²⁺ : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B) (γ : Struct n) {x : 𝔽 n} →
  x ∈ dom γ → suc (suc x) ∈ dom (join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)))
∈-bind²⁺ a b γ x∈ =
  ∈-join⁺ a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)) (inj₂ (∈dom-wk²⁺ γ x∈))

∈-absrec⁻ : (γ : Struct n) {x : 𝔽 n} →
  suc (suc x) ∈ dom (Struct (2 + n) ∋ ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ)) → x ∈ dom γ
∈-absrec⁻ γ sx∈ =
  [ (λ p → [ (λ q → ⊥-elim (suc²∉⁅zero⁆ q)) , (λ q → ⊥-elim (suc²∉⁅suc-zero⁆ q)) ]′
             (x∈p∪q⁻ ⁅ zero ⁆ ⁅ suc zero ⁆ p))
  , ∈dom-wk²⁻ γ
  ]′ (x∈p∪q⁻ (⁅ zero ⁆ ∪ ⁅ suc zero ⁆) (dom (𝐂.wk (𝐂.wk γ))) sx∈)

∈-absrec⁺ : (γ : Struct n) {x : 𝔽 n} →
  x ∈ dom γ → suc (suc x) ∈ dom (Struct (2 + n) ∋ ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ))
∈-absrec⁺ γ x∈ = x∈p∪q⁺ (inj₂ (∈dom-wk²⁺ γ x∈))
