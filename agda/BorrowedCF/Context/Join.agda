module BorrowedCF.Context.Join where

import Data.Fin.Subset as S
import Data.Fin.Subset.Properties as S

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Substitution

open Nat.Variables
open Variables

biasedDir : ParSeq → Dir
biasedDir par = 𝟙
biasedDir seq = L

record Join (A : Set) : Set where
  field joinDir : A → Dir

  join : A → Struct n → Struct n → Struct n
  join a with joinDir a
  ... | 𝟙 = _∥_
  ... | L = _;_
  ... | R = flip _;_

  ≈-join : ∀ a → Γ ∶ α₁ ≈ α₂ → Γ ∶ β₁ ≈ β₂ → Γ ∶ join a α₁ β₁ ≈ join a α₂ β₂
  ≈-join a with joinDir a
  ... | 𝟙 = ∥-cong
  ... | L = ;-cong
  ... | R = flip ;-cong

  ≼-join : ∀ a → Γ ∶ α₁ ≼ α₂ → Γ ∶ β₁ ≼ β₂ → Γ ∶ join a α₁ β₁ ≼ join a α₂ β₂
  ≼-join a with joinDir a
  ... | 𝟙 = ≼-cong-∥
  ... | L = ≼-cong-;
  ... | R = flip ≼-cong-;

  join-distr-∥ : ∀ a α₁ α₂ β₁ β₂ → Γ ∶ join a (α₁ ∥ β₁) (α₂ ∥ β₂) ≼ join a α₁ α₂ ∥ join a β₁ β₂
  join-distr-∥ a α₁ α₂ β₁ β₂ with joinDir a
  ... | 𝟙 = let open ≈-Reasoning in
            ≼-refl $ begin
              (α₁ ∥ β₁) ∥ (α₂ ∥ β₂)  ≈⟨ ∥-assoc ⟨
              α₁ ∥ β₁ ∥ α₂ ∥ β₂      ≈⟨ ∥-cong ∥-assoc refl ⟩
              α₁ ∥ (β₁ ∥ α₂) ∥ β₂    ≈⟨ ∥-cong (∥-cong refl ∥-comm) refl ⟩
              α₁ ∥ (α₂ ∥ β₁) ∥ β₂    ≈⟨ ∥-cong ∥-assoc refl ⟨
              α₁ ∥ α₂ ∥ β₁ ∥ β₂      ≈⟨ ∥-assoc ⟩
              (α₁ ∥ α₂) ∥ (β₁ ∥ β₂)  ∎
  ... | L = ≼-wk
  ... | R = ≼-wk

{-
  join-dist-; : ∀ a α₁ α₂ β → Γ ∶ join a α₁ (join a α₂ β) ≼ join a (join a α₁ α₂) β
  join-dist-; a α₁ α₂ β with joinDir a
  ... | 𝟙 = {!!}
  ... | L = ≼-refl {!!} --(≈-sym ;-assoc)
  ... | R = ≼-refl {!!}
-}

  join-[]₁ : ∀ a → Γ ∶ join a [] β ≈ β
  join-[]₁ a with joinDir a
  ... | 𝟙 = ∥-unit₁
  ... | L = ;-unit₁
  ... | R = ;-unit₂

  join-[]₂ : ∀ a → Γ ∶ join a α [] ≈ α
  join-[]₂ a with joinDir a
  ... | 𝟙 = ∥-unit₂
  ... | L = ;-unit₂
  ... | R = ;-unit₁

  join-⋯ : ∀ a ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} (α β : Struct m) → join a α β ⋯ ϕ ≡ join a (α ⋯ ϕ) (β ⋯ ϕ)
  join-⋯ a α β with joinDir a
  ... | L = refl
  ... | R = refl
  ... | 𝟙 = refl

  allCx-join⁺ : ∀ {ℓ} {P : Pred 𝕋 ℓ} a → AllCx P Γ α → AllCx P Γ β → AllCx P Γ (join a α β)
  allCx-join⁺ a with joinDir a
  ... | L = _;_
  ... | R = flip _;_
  ... | 𝟙 = _∥_

  allCx-join⁻ : ∀ {ℓ} {P : Pred 𝕋 ℓ} a → AllCx P Γ (join a α β) → AllCx P Γ α × AllCx P Γ β
  allCx-join⁻ a with joinDir a
  ... | L = allCx-;⁻¹
  ... | R = Π.swap ∘ allCx-;⁻¹
  ... | 𝟙 = allCx-∥⁻¹

  join-↓ : ∀ a (α β : Struct n) {X} → join a α β ↓ X ≡ join a (α ↓ X) (β ↓ X)
  join-↓ a α β with joinDir a
  ... | 𝟙 = refl
  ... | L = refl
  ... | R = refl

  dom-join : ∀ a (α β : Struct n) → dom (join a α β) ≡ dom α S.∪ dom β
  dom-join a α β with joinDir a
  ... | 𝟙 = refl
  ... | L = refl
  ... | R = S.∪-comm _ _

{-
  module _ where
    open import Data.Fin.Subset.Properties

    unjoin : ∀ a (γ : Struct n) {𝓧 : Subset n} → 𝓧 ⊆ dom γ → ∃[ α ] ∃[ β ] dom α ≡ 𝓧 × Empty (dom α ∩ dom β) × Γ ∶ join a α β ≼ γ
    unjoin a (` x) {X} X⊆ with x ∈? X
    ... | yes x∈ = (` x) , [] , sym (⊆⁅x⁆×y∈⇒≡⁅x⁆ X⊆ x∈) , Empty-∩₂ ⁅ x ⁆ Empty-⁅⁆ , ≼-refl (join-[]₂ a)
    ... | no  x∉ = [] , (` x) , sym (Empty-unique (⊆⁅x⁆×x∉⇒Empty X⊆ x∉)) , Empty-∩₁ Empty-⁅⁆ _ , ≼-refl (join-[]₁ a)
    unjoin a [] X⊆ = [] , [] , sym (⊆⁅⁆⇒≡⁅⁆ X⊆) , Empty-∩₁ Empty-⁅⁆ _ , ≼-refl (join-[]₁ a)
    unjoin a (α ∥ β) {X} X⊆ =
      let α₁ , α₂ , dom-α₁ , disj-α , α₁₂ = unjoin a α (p∩q⊆q X (dom α)) in
      let β₁ , β₂ , dom-β₁ , disj-β , β₁₂ = unjoin a β (p∩q⊆q X (dom β)) in
      (α₁ ∥ β₁) , (α₂ ∥ β₂)
        , ( let open ≡-Reasoning in
            dom (α₁ ∥ β₁)              ≡⟨⟩
            dom α₁ ∪ dom β₁            ≡⟨ cong₂ _∪_ dom-α₁ dom-β₁ ⟩
            (X ∩ dom α) ∪ (X ∩ dom β)  ≡⟨ ∩-distribˡ-∪ X (dom α) (dom β) ⟨
            X ∩ (dom α ∪ dom β)        ≡⟨ ∩-identityʳ-⊆ X X⊆ ⟩
            X ∎
          )
        , (λ (x , x∈) → disj-α (x , x∈p∩q⁺ {!x∈p∪q⁻ _ _ (x∈p∩q⁻ _ _ x∈ .proj₁)!})) -- requires unique variables
        , ≼-trans (join-distr-∥ a _ _ _ _) (≼-cong-∥ α₁₂ β₁₂)
    unjoin a (α ; β) {X} X⊆ with nonempty? (dom β ∩ X)
    ... | yes dom[β]∩X≢∅ = {!!}
    ... | no dom[β]∩X≡∅ =
      let α₁ , α₂ , dom-α₁ , disj-α , α₁₂ = unjoin a α (p∩q⊆q X (dom α)) in
      α₁ , α₂ ; β
        , ( let open ≡-Reasoning in
            dom α₁     ≡⟨ dom-α₁ ⟩
            X ∩ dom α  ≡⟨ ∩-identityʳ-⊆ X {!!} ⟩ -- ((Sum.fromInj₁ λ x∈ → ⊥-elim (dom[β]∩X≡∅ ?)) ∘ x∈p∪q⁻ _ _ ∘ X⊆)
            X ∎)
        , (λ (x , x∈) → {!!}) -- requires unique vars
        , {!!} --≼-trans {!!} (≼-cong-; α₁₂ (≼-refl refl))
-}

open Join ⦃ ... ⦄ public

instance
  join-dir : Join Dir
  join-dir = record { joinDir = id }

  join-p/s : Join ParSeq
  join-p/s = record { joinDir = biasedDir }

join-flip : ∀ d → Γ ∶ join (flipDir d) β α ≈ join d α β
join-flip L = refl
join-flip R = refl
join-flip 𝟙 = ∥-comm

;-≼-join : (p/s : ParSeq) → Γ ∶ α ; β ≼ join p/s α β
;-≼-join par = ;-≼-∥
;-≼-join seq = ≼-refl refl

join-≼-∥ : (p/s : ParSeq) → Γ ∶ join p/s α β ≼ α ∥ β
join-≼-∥ par = ≼-refl refl
join-≼-∥ seq = ;-≼-∥

postulate parOrSeq? : Γ ∶ α ; β ≼ γ → Σ[ p/s ∈ ParSeq ] Γ ∶ join p/s α β ≼ γ
