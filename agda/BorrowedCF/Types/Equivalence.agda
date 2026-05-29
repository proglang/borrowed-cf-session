{-# OPTIONS --rewriting #-}
module BorrowedCF.Types.Equivalence where

open import Data.Maybe using (Maybe)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.Preorder as PreorderReasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax

open Bin
open Nat.Variables

infix 4 _≃𝕊_ _≃𝕋_

data _≃𝕊_ {n} : Rel (𝕊 n) 0ℓ where
  ≃𝕊-;₁ : s₁ ≃𝕊 s₂ → s₁ ; s ≃𝕊 s₂ ; s
  ≃𝕊-;₂ : s₁ ≃𝕊 s₂ → s ; s₁ ≃𝕊 s ; s₂

  ≃𝕊-skipˡ : skip ; s ≃𝕊 s
  ≃𝕊-skipʳ : s ; skip ≃𝕊 s

  ≃𝕊-μ : mu s ≃𝕊 unfold s

  ≃𝕊-assoc : (s₁ ; s₂) ; s₃ ≃𝕊 s₁ ; (s₂ ; s₃)
  ≃𝕊-distr : brn p s₁ s₂ ; s ≃𝕊 brn p (s₁ ; s) (s₂ ; s)

data _≃𝕋_ : Rel 𝕋 0ℓ where
  `⊤ : `⊤ ≃𝕋 `⊤
  _⊗_ : T₁ ≃𝕋 T₂ → U₁ ≃𝕋 U₂ → T₁ ⊗⟨ d ⟩ U₁ ≃𝕋 T₂ ⊗⟨ d ⟩ U₂
  _`→_ : T₁ ≃𝕋 T₂ → U₁ ≃𝕋 U₂ → T₁ ⟨ a ⟩→ U₁ ≃𝕋 T₂ ⟨ a ⟩→ U₂
  ⟨_⟩ : EqClosure _≃𝕊_ s₁ s₂ → ⟨ s₁ ⟩ ≃𝕋 ⟨ s₂ ⟩

infix 4 _≃_

_≃_ : ∀ {κ x} → Rel (Ty κ x) 0ℓ
_≃_ {𝕤} = EqClosure _≃𝕊_
_≃_ {𝕥} = _≃𝕋_

≃-refl : ∀ {κ x} {t : Ty κ x} → t ≃ t
≃-refl {𝕤} = refl
≃-refl {𝕥} {t = ⟨ s ⟩} = ⟨ ≃-refl ⟩
≃-refl {𝕥} {t = `⊤} = `⊤
≃-refl {𝕥} {t = t ⟨ a ⟩→ u} = ≃-refl `→ ≃-refl
≃-refl {𝕥} {t = t ⊗⟨ d ⟩ u} = ≃-refl ⊗ ≃-refl

≃-sym : ∀ {κ x} {t u : Ty κ x} → t ≃ u → u ≃ t
≃-sym {𝕤} eq = Eq*.symmetric _≃𝕊_ eq
≃-sym {𝕥} `⊤ = `⊤
≃-sym {𝕥} (eq₁ ⊗ eq₂) = ≃-sym eq₁ ⊗ ≃-sym eq₂
≃-sym {𝕥} (eq₁ `→ eq₂) = ≃-sym eq₁ `→ ≃-sym eq₂
≃-sym {𝕥} ⟨ eq ⟩ = ⟨ ≃-sym eq ⟩

≃-trans :  ∀ {κ x} {u v w : Ty κ x} → u ≃ v → v ≃ w → u ≃ w
≃-trans {𝕤} uv vw = uv ◅◅ vw
≃-trans {𝕥} `⊤ `⊤ = `⊤
≃-trans {𝕥} (uv ⊗ uv₁) (vw ⊗ vw₁) = ≃-trans uv vw ⊗ ≃-trans uv₁ vw₁
≃-trans {𝕥} (uv `→ uv₁) (vw `→ vw₁) = ≃-trans uv vw `→ ≃-trans uv₁ vw₁
≃-trans {𝕥} ⟨ uv ⟩ ⟨ vw ⟩ = ⟨ ≃-trans uv vw ⟩

≃-isEquivalence : ∀ κ x → IsEquivalence (_≃_ {κ} {x})
≃-isEquivalence _ _ = record { refl = ≃-refl; sym = ≃-sym; trans = ≃-trans }

≃-setoid : ∀ κ x → Setoid _ _
≃-setoid κ x = record { isEquivalence = ≃-isEquivalence κ x }

module ≃-Reasoning {κ x} = SetoidReasoning (≃-setoid κ x)

≃-; : s₁ ≃ s₁′ → s₂ ≃ s₂′ → s₁ ; s₂ ≃ s₁′ ; s₂′
≃-; eq₁ eq₂ = Eq*.gmap (_; _) ≃𝕊-;₁ eq₁ ◅◅ Eq*.gmap (_ ;_) ≃𝕊-;₂ eq₂

≃-skipˡ : skip ; s ≃ s
≃-skipˡ = fwd ≃𝕊-skipˡ ◅ refl

-- ≃-skips : Skips {n} Respects _≃_
-- ≃-skips refl s = s
-- ≃-skips (fwd x ◅ eq) s = ≃-skips eq (go x s) where
--   go : Skips {n} Respects _≃𝕊_
--   go (≃𝕊-;₁ eq) (s₁ ; s₂) = go eq s₁ ; s₂
--   go (≃𝕊-;₂ eq) (s₁ ; s₂) = s₁ ; go eq s₂
--   go ≃𝕊-skipˡ (s₁ ; s₂) = s₂
--   go ≃𝕊-skipʳ (s₁ ; s₂) = s₁
--   go ≃𝕊-assoc ((s₁ ; s₂) ; s₃) = s₁ ; (s₂ ; s₃)
--   go ≃𝕊-distr (() ; _)
-- ≃-skips (bwd x ◅ eq) s = ≃-skips eq (go x s) where
--   go : Skips {n} Respects (flip _≃𝕊_)
--   go (≃𝕊-;₁ eq) (s₁ ; s₂) = go eq s₁ ; s₂
--   go (≃𝕊-;₂ eq) (s₁ ; s₂) = s₁ ; go eq s₂
--   go ≃𝕊-skipˡ s = skip ; s
--   go ≃𝕊-skipʳ s = s ; skip
--   go ≃𝕊-assoc (s₁ ; (s₂ ; s₃)) = (s₁ ; s₂) ; s₃

-- ≃-unr : Unr Respects _≃_
-- ≃-unr `⊤ `⊤ = `⊤
-- ≃-unr (eq₁ ⊗ eq₂) (U₁ ⊗ U₂) = ≃-unr eq₁ U₁ ⊗ ≃-unr eq₂ U₂
-- ≃-unr (eq₁ `→ eq₂) (arr x) = arr x
-- ≃-unr ⟨ eq ⟩ ⟨ s ⟩ = ⟨ ≃-skips eq s ⟩

-- ≃-mobile : Mobile Respects _≃_
-- ≃-mobile `⊤ `⊤ = `⊤
-- ≃-mobile (eq₁ ⊗ eq₂) (m₁ ⊗ m₂) = ≃-mobile eq₁ m₁ ⊗ ≃-mobile eq₂ m₂
-- ≃-mobile (eq₁ `→ eq₂) (arr x) = arr x
-- ≃-mobile ⟨ eq ⟩ (acq x₁) = {!acq!}
-- ≃-mobile ⟨ eq ⟩ (skip s) = skip (≃-skips eq s)

-- -- open Bin

-- -- infix 4 _≊_ _≲_

-- -- postulate
-- --   _≊_ : ∀ {κ x} → Rel (Ty κ x) 0ℓ
-- --   _≲_ : ∀ {κ x} → Rel (Ty κ x) 0ℓ

-- --   _≊?_ : ∀ {κ x} → Decidable (_≊_ {κ} {x})
-- --   _≲?_ : ∀ {κ x} (t u : Ty κ x) → Maybe (t ≲ u)

-- --   ≲-isPartialOrder : ∀ κ x → IsPartialOrder (_≊_ {κ} {x}) _≲_

-- -- ≊-isEquivalence : ∀ κ x → IsEquivalence (_≊_ {κ} {x})
-- -- ≊-isEquivalence = IsPartialOrder.isEquivalence ∘₂ ≲-isPartialOrder

-- -- ≊-setoid : ∀ κ x → Setoid _ _
-- -- ≊-setoid κ x = record { isEquivalence = ≊-isEquivalence κ x }

-- -- ≲-poset : ∀ κ x → Poset _ _ _
-- -- ≲-poset κ x = record { isPartialOrder = ≲-isPartialOrder κ x }

-- -- module ≊-Reasoning {κ x} = SetoidReasoning (≊-setoid κ x)
-- -- module ≲-Reasoning {κ x} = PreorderReasoning (Poset.preorder (≲-poset κ x))

-- -- module _ {κ x} where
-- --   open IsEquivalence (≊-isEquivalence κ x) using () renaming
-- --     ( refl to ≊-refl
-- --     ; reflexive to ≊-reflexive
-- --     ; sym to ≊-sym
-- --     ; trans to ≊-trans
-- --     ) public

-- --   open IsPartialOrder (≲-isPartialOrder κ x) using () renaming
-- --     ( refl to ≲-refl
-- --     ; reflexive to ≲-reflexive
-- --     ; trans to ≲-trans
-- --     ; antisym to ≲-antisym
-- --     ) public


-- -- infix 4 _≤⃗_

-- -- data _≤⃗_ (a : Arr) : Arr → Set where
-- --   arr : Arr.eff a ≤ϵ ϵ → a ≤⃗ record a { eff = ϵ }

-- -- ≤⃗-refl : a ≤⃗ a
-- -- ≤⃗-refl = arr ≤ϵ-refl

-- -- ≤⃗-trans : ∀ {x y z} → x ≤⃗ y → y ≤⃗ z → x ≤⃗ z
-- -- ≤⃗-trans (arr xy) (arr yz) = arr (≤ϵ-trans xy yz)

-- -- postulate
-- --   ≲⁻¹-`⊤ʳ : T ≲ `⊤ → T ≡ `⊤
-- --   ≲⁻¹-→ʳ : T ≲ U₁ ⟨ a ⟩→ U₂ → ∃[ T₁ ] ∃[ T₂ ] ∃[ a′ ] T ≡ T₁ ⟨ a′ ⟩→ T₂ × a′ ≤⃗ a × U₁ ≲ T₁ × T₂ ≲ U₂
-- --   ≲⁻¹-⊗ʳ : T ≲ U₁ ⊗⟨ d ⟩ U₂ → ∃[ T₁ ] ∃[ T₂ ] T ≡ T₁ ⊗⟨ d ⟩ T₂ × T₁ ≲ U₁ × T₂ ≲ U₂
-- --   ≲⁻¹-⟨⟩ʳ : T ≲ ⟨ s ⟩ → ∃[ s′ ] T ≡ ⟨ s′ ⟩ × s′ ≲ s

-- --   skips-respects-≳ : ∀ {n} → Skips {n} Respects flip _≲_

-- -- unr-respects-≳ : Unr Respects flip _≲_
-- -- unr-respects-≳ x `⊤ rewrite ≲⁻¹-`⊤ʳ x = `⊤
-- -- unr-respects-≳ x (u₁ ⊗ u₂) with _ , _ , refl , u₁≤ , u₂≤ ← ≲⁻¹-⊗ʳ x = unr-respects-≳ u₁≤ u₁ ⊗ unr-respects-≳ u₂≤ u₂
-- -- unr-respects-≳ x (arr eq) with _ , _ , _ , refl , arr _ , _ ← ≲⁻¹-→ʳ x = arr eq
-- -- unr-respects-≳ x ⟨ skips ⟩ with _ , refl , s≤ ← ≲⁻¹-⟨⟩ʳ x = ⟨ skips-respects-≳ s≤ skips ⟩

-- -- mobile-respects-≳ : Mobile Respects flip _≲_
-- -- mobile-respects-≳ x `⊤ rewrite ≲⁻¹-`⊤ʳ x = `⊤
-- -- mobile-respects-≳ x (arr x₁) with _ , _ , _ , refl , arr _ , _ ← ≲⁻¹-→ʳ x = arr x₁
-- -- mobile-respects-≳ x (acq x₁) = {!!}
-- -- mobile-respects-≳ x (skip x₁) = {!!}
-- -- mobile-respects-≳ x (m ⊗ m₁) = {!!}
