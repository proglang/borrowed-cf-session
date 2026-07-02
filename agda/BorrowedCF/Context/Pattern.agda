module BorrowedCF.Context.Pattern where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Join
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Substitution

open Nat.Variables
open Variables

CxPat : ℕ → Set
CxPat n = List (Dir × Struct n)

pattern 𝒫[_] x = x ∷ []

variable
  𝒫 𝒫₁ 𝒫₂ 𝒫₃ 𝒫′ : CxPat n

infixl 5 _⋯𝓅_

_⋯𝓅_ : ⦃ K : Kit 𝓕 ⦄ → CxPat m → m –[ K ]→ n → CxPat n
P ⋯𝓅 ϕ = L.map (Π.map₂ (_⋯ ϕ)) P

⋯𝓅-dist-++ : ⦃ K : Kit 𝓕 ⦄ (P₁ P₂ : CxPat m) (ϕ : m –[ K ]→ n) → (P₁ ++ P₂) ⋯𝓅 ϕ ≡ (P₁ ⋯𝓅 ϕ) ++ (P₂ ⋯𝓅 ϕ)
⋯𝓅-dist-++ P₁ P₂ ϕ = L.map-++ (Π.map₂ (_⋯ ϕ)) P₁ P₂

--foldPattern : Struct n → Dir × Struct n → Struct n
--foldPattern γ′ (d , γ) = join d γ γ′
foldPattern : Dir × Struct n → Struct n → Struct n
foldPattern (d , γ) γ′ = join d γ γ′

_[_]𝓅 : CxPat n → Struct n → Struct n
P [ γ ]𝓅 = L.foldr foldPattern γ P

[-]𝓅-dist-++ : (P₁ P₂ : CxPat n) (γ : Struct n) → (P₁ ++ P₂) [ γ ]𝓅 ≡ P₁ [ P₂ [ γ ]𝓅 ]𝓅
[-]𝓅-dist-++ P₁ P₂ γ = L.foldr-++ foldPattern γ P₁ P₂

[-]𝓅-≈ : (P : CxPat n) → Γ ∶ α ≈ β → Γ ∶ P [ α ]𝓅 ≈ P [ β ]𝓅
[-]𝓅-≈ [] x = x
[-]𝓅-≈ ((d , γ) ∷ P) x = ≈-join d refl ([-]𝓅-≈ P x)

[-]𝓅-≼ : (P : CxPat n) → Γ ∶ α ≼ β → Γ ∶ P [ α ]𝓅 ≼ P [ β ]𝓅
[-]𝓅-≼ [] x = x
[-]𝓅-≼ ((d , γ) ∷ P) x = ≼-join d (≼-refl refl) ([-]𝓅-≼ P x)

[-]-dist-⋯ : ⦃ K : Kit 𝓕 ⦄ (P : CxPat m) (γ : Struct m) (ϕ : m –[ K ]→ n) → P [ γ ]𝓅 ⋯ ϕ ≡ (P ⋯𝓅 ϕ) [ γ ⋯ ϕ ]𝓅
[-]-dist-⋯ [] γ ϕ = refl
[-]-dist-⋯ ⦃ K ⦄ ((d , γ′) ∷ P) γ ϕ =
  let open ≡-Reasoning in
  join d γ′ (P [ γ ]𝓅) ⋯ ϕ               ≡⟨ join-⋯ d γ′ (P [ γ ]𝓅) ⟩
  join d (γ′ ⋯ ϕ) (P [ γ ]𝓅 ⋯ ϕ)         ≡⟨ cong (join d _) ([-]-dist-⋯ P γ ϕ) ⟩
  join d (γ′ ⋯ ϕ) ((P ⋯𝓅 ϕ) [ γ ⋯ ϕ ]𝓅)  ∎

_∶_≈𝓅_ : Ctx n → Rel (CxPat n) _
Γ ∶ P₁ ≈𝓅 P₂ = ∀ {α β} → Γ ∶ α ≈ β → Γ ∶ P₁ [ α ]𝓅 ≈ P₂ [ β ]𝓅

≈𝓅-refl : (P : CxPat n) → Γ ∶ P ≈𝓅 P
≈𝓅-refl P = [-]𝓅-≈ P

≈𝓅-sym : (P₁ P₂ : CxPat n) → Γ ∶ P₁ ≈𝓅 P₂ → Γ ∶ P₂ ≈𝓅 P₁
≈𝓅-sym _ _ p-eq γ-eq = ≈-sym (p-eq (≈-sym γ-eq))

≈𝓅-trans : (P₁ P₂ P₃ : CxPat n) → Γ ∶ P₁ ≈𝓅 P₂ → Γ ∶ P₂ ≈𝓅 P₃ → Γ ∶ P₁ ≈𝓅 P₃
≈𝓅-trans _ _ _ p₁₂ p₂₃ eq = ≈-trans (p₁₂ eq) (p₂₃ refl)

≈𝓅-isEquivalence : (Γ : Ctx n) → IsEquivalence (Γ ∶_≈𝓅_)
≈𝓅-isEquivalence Γ = record
  { refl  = λ {x}     → ≈𝓅-refl x
  ; sym   = λ {x y}   → ≈𝓅-sym x y
  ; trans = λ {x y z} → ≈𝓅-trans x y z
  }

≈𝓅-setoid : Ctx n → Setoid _ _
≈𝓅-setoid Γ = record { isEquivalence = ≈𝓅-isEquivalence Γ }

_∶_≼𝓅_ : Ctx n → Rel (CxPat n) _
Γ ∶ P₁ ≼𝓅 P₂ = ∀ {α β} → Γ ∶ α ≼ β → Γ ∶ P₁ [ α ]𝓅 ≼ P₂ [ β ]𝓅

≼𝓅-refl : (P : CxPat n) → Γ ∶ P ≼𝓅 P
≼𝓅-refl [] x = x
≼𝓅-refl ((d , γ) ∷ P) x = ≼-join d (≼-refl refl) (≼𝓅-refl P x)

≼𝓅-trans : (P₁ P₂ P₃ : CxPat n) → Γ ∶ P₁ ≼𝓅 P₂ → Γ ∶ P₂ ≼𝓅 P₃ → Γ ∶ P₁ ≼𝓅 P₃
≼𝓅-trans _ _ _ ≤₁₂ ≤₂₃ x = ≼-trans (≤₁₂ (≼-refl refl)) (≤₂₃ x)

≼𝓅-reflexive : (P Q : CxPat n) → Γ ∶ P ≈𝓅 Q → Γ ∶ P ≼𝓅 Q
≼𝓅-reflexive P Q P≈Q x = ≼-trans (≼-refl (P≈Q refl)) (≼𝓅-refl Q x)

≼𝓅-isPreorder : (Γ : Ctx n) → Bin.IsPreorder (Γ ∶_≈𝓅_) (Γ ∶_≼𝓅_)
≼𝓅-isPreorder Γ = record
  { isEquivalence = ≈𝓅-isEquivalence Γ
  ; reflexive = λ {x y} → ≼𝓅-reflexive x y
  ; trans     = λ {x y z} → ≼𝓅-trans x y z
  }

≼𝓅-preorder : (Γ : Ctx n) → Bin.Preorder _ _ _
≼𝓅-preorder Γ = record { isPreorder = ≼𝓅-isPreorder Γ }

-- LeftPat: hole is on the left, d specifies the side γ goes
LeftPat : CxPat n → Set
LeftPat = All λ (d , γ) → d ≡ 𝟙 ⊎ d ≡ R

{-
leftPat-pullOut-∥ : LeftPat 𝒫 → Γ ∶ 𝒫 [ α ∥ β ]𝓅 ≈ α ∥ 𝒫 [ β ]𝓅
leftPat-pullOut-∥ [] = refl
leftPat-pullOut-∥ (inj₁ refl ∷ L𝒫) = {!!}
leftPat-pullOut-∥ (inj₂ refl ∷ L𝒫) = {!!}
-}

open ≼-Reasoning

restrictContext : (𝒫 : CxPat n) (γ : Struct n) → Γ ∶ 𝒫 [ γ ]𝓅 ≼ γ ∥ 𝒫 [ [] ]𝓅
restrictContext [] γ = ≼-refl (≈-sym ∥-unit₂)
restrictContext ((L , α) ∷ 𝒫) γ =
  let IH = restrictContext 𝒫 γ in begin
  α ; 𝒫 [ γ ]𝓅                ≲⟨ ≼-cong-; (≼-refl refl) IH ⟩
  α ; (γ ∥ 𝒫 [ [] ]𝓅)         ≈⟨ ;-cong ∥-unit₁ refl ⟨
  ([] ∥ α) ; (γ ∥ 𝒫 [ [] ]𝓅)  ≲⟨ ≼-wk ⟩
  ([] ; γ) ∥ (α ; 𝒫 [ [] ]𝓅)  ≈⟨ ∥-cong ;-unit₁ refl ⟩
  γ ∥ (α ; 𝒫 [ [] ]𝓅)         ∎
restrictContext ((R , α) ∷ 𝒫) γ =
  let IH = restrictContext 𝒫 γ in begin
  𝒫 [ γ ]𝓅 ; α                ≲⟨ ≼-cong-; IH (≼-refl refl) ⟩
  (γ ∥ 𝒫 [ [] ]𝓅) ; α         ≈⟨ ;-cong ∥-comm ∥-unit₂ ⟨
  (𝒫 [ [] ]𝓅 ∥ γ) ; (α ∥ [])  ≲⟨ ≼-wk ⟩
  (𝒫 [ [] ]𝓅 ; α) ∥ (γ ; [])  ≈⟨ ∥-cong refl ;-unit₂ ⟩
  (𝒫 [ [] ]𝓅 ; α) ∥ γ         ≈⟨ ∥-comm ⟩
  γ ∥ (𝒫 [ [] ]𝓅 ; α)         ∎
restrictContext ((𝟙 , α) ∷ 𝒫) γ =
  let IH = restrictContext 𝒫 γ in begin
  α ∥ 𝒫 [ γ ]𝓅         ≲⟨ ≼-cong-∥ (≼-refl refl) IH ⟩
  α ∥ (γ ∥ 𝒫 [ [] ]𝓅)  ≈⟨ ≈-trans (≈-sym ∥-assoc) (≈-trans (∥-cong ∥-comm refl) ∥-assoc) ⟩
  γ ∥ (α ∥ 𝒫 [ [] ]𝓅)  ∎
