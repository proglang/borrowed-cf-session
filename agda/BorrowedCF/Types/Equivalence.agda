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
open import BorrowedCF.Types.Substitution

open Bin
open Nat using (_≤_; s≤s; s≤s⁻¹; ≤-trans)
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

module _ {κ x} where
  open IsEquivalence (≃-isEquivalence κ x) using () renaming (reflexive to ≃-reflexive) public

≃-setoid : ∀ κ x → Setoid _ _
≃-setoid κ x = record { isEquivalence = ≃-isEquivalence κ x }

module ≃-Reasoning {κ x} = SetoidReasoning (≃-setoid κ x)

≃-; : s₁ ≃ s₁′ → s₂ ≃ s₂′ → s₁ ; s₂ ≃ s₁′ ; s₂′
≃-; eq₁ eq₂ = Eq*.gmap (_; _) ≃𝕊-;₁ eq₁ ◅◅ Eq*.gmap (_ ;_) ≃𝕊-;₂ eq₂

≃-μ : mu s ≃ unfold s
≃-μ = Eq*.return ≃𝕊-μ

≃-skipˡ : skip ; s ≃ s
≃-skipˡ = fwd ≃𝕊-skipˡ ◅ refl

≃-skips : Skips {n} Respects _≃_
≃-skips refl s = s
≃-skips (fwd x ◅ eq) s = ≃-skips eq (go x s) where
  go : Skips {n} Respects _≃𝕊_
  go ≃𝕊-μ       (mu s)    = skips-⋯ s
  go (≃𝕊-;₁ eq) (s₁ ; s₂) = go eq s₁ ; s₂
  go (≃𝕊-;₂ eq) (s₁ ; s₂) = s₁ ; go eq s₂
  go ≃𝕊-skipˡ   (s₁ ; s₂) = s₂
  go ≃𝕊-skipʳ   (s₁ ; s₂) = s₁
  go ≃𝕊-assoc   ((s₁ ; s₂) ; s₃) = s₁ ; (s₂ ; s₃)
  go ≃𝕊-distr   (() ; _)
≃-skips (bwd x ◅ eq) s = ≃-skips eq (go x s) where
  go : Skips {n} Respects (flip _≃𝕊_)
  go {y = mu s} ≃𝕊-μ ss
    with skips? s
  ... | yes ss′ = mu ss′
  ... | no ¬ss′ = mu $ skips-⋯⁻¹ {s = s} {ϕ = ⦅ mu s ⦆ₛ} ss λ where
    zero    (mu ss′) → ¬ss′ ss′
    (suc z) ()
  go (≃𝕊-;₁ eq) (s₁ ; s₂) = go eq s₁ ; s₂
  go (≃𝕊-;₂ eq) (s₁ ; s₂) = s₁ ; go eq s₂
  go ≃𝕊-skipˡ   s = skip ; s
  go ≃𝕊-skipʳ   s = s ; skip
  go ≃𝕊-assoc (s₁ ; (s₂ ; s₃)) = (s₁ ; s₂) ; s₃

skips⇒skip≃′ : (x : Skips s) → ∀ {n} → .(skipsSize x ≤ n) → skip ≃ s
skips⇒skip≃′ skip {zero} ≤n = refl
skips⇒skip≃′ skip {suc n} ≤n = refl
skips⇒skip≃′ (x₁ ; x₂) {suc n} ≤n =
  ≃-trans (≃-sym ≃-skipˡ)
    (≃-; (skips⇒skip≃′ x₁ {n} (≤-trans (Nat.m≤m+n _ _) (s≤s⁻¹ ≤n)))
         (skips⇒skip≃′ x₂ {n} (≤-trans (Nat.m≤n+m _ _) (s≤s⁻¹ ≤n))))
skips⇒skip≃′ {s = mu s} (mu x) {suc n} ≤n =
  ≃-trans (skips⇒skip≃′ (skips-⋯ {ϕ = ⦅ mu s ⦆ₛ} x) {n} (subst (_≤ n) (sym (skipsSize-⋯ x _)) (s≤s⁻¹ ≤n)))
          (≃-sym ≃-μ)

skips⇒skip≃ : Skips s → skip ≃ s
skips⇒skip≃ x = skips⇒skip≃′ x Nat.≤-refl

skip≃⇒skips : skip ≃ s → Skips s
skip≃⇒skips eq = ≃-skips eq skip
