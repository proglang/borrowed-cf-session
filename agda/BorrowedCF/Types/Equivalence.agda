module BorrowedCF.Types.Equivalence where

open import Data.Maybe using (Maybe)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
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

mutual
  infix 4 _≃𝕊_ _≃𝕋_

  data _≃𝕊_ {n} : Rel (𝕊 n) 0ℓ where
    ≃𝕊-;₁ : s₁ ≃𝕊 s₂ → s₁ ; s ≃𝕊 s₂ ; s
    ≃𝕊-;₂ : s₁ ≃𝕊 s₂ → s ; s₁ ≃𝕊 s ; s₂

    ≃𝕊-skipˡ : skip ; s ≃𝕊 s
    ≃𝕊-skipʳ : s ; skip ≃𝕊 s

    ≃𝕊-μ : mu s ≃𝕊 unfold s

    ≃𝕊-assoc : (s₁ ; s₂) ; s₃ ≃𝕊 s₁ ; (s₂ ; s₃)
    ≃𝕊-distr : brn p s₁ s₂ ; s ≃𝕊 brn p (s₁ ; s) (s₂ ; s)

    ≃𝕊-msg : T₁ ≃ T₂ → msg p T₁ ≃𝕊 msg p T₂
    ≃𝕊-brn₁ : s₁ ≃𝕊 s₂ → brn p s₁ s ≃𝕊 brn p s₂ s
    ≃𝕊-brn₂ : s₁ ≃𝕊 s₂ → brn p s s₁ ≃𝕊 brn p s s₂

  infix 4 _⟨≃𝕊⟩_

  _⟨≃𝕊⟩_ : Rel (𝕊 n) _
  _⟨≃𝕊⟩_ = Sym.SymClosure _≃𝕊_

  data _≃𝕋_ : Rel 𝕋 0ℓ where
    `⊤ : `⊤ ≃𝕋 `⊤
    _⊗_ : T₁ ≃𝕋 T₂ → U₁ ≃𝕋 U₂ → T₁ ⊗⟨ d ⟩ U₁ ≃𝕋 T₂ ⊗⟨ d ⟩ U₂
    _⊕_ : T₁ ≃𝕋 T₂ → U₁ ≃𝕋 U₂ → T₁ ⊕ U₁ ≃𝕋 T₂ ⊕ U₂
    _`→_ : T₁ ≃𝕋 T₂ → U₁ ≃𝕋 U₂ → T₁ ⟨ a ⟩→ U₁ ≃𝕋 T₂ ⟨ a ⟩→ U₂
    ⟨_⟩ : EqClosure _≃𝕊_ s₁ s₂ → ⟨ s₁ ⟩ ≃𝕋 ⟨ s₂ ⟩

  infix 4 _≃_ _≄_

  _≃_ : ∀ {κ x} → Rel (Ty κ x) 0ℓ
  _≃_ {𝕤} = EqClosure _≃𝕊_
  _≃_ {𝕥} = _≃𝕋_

_≄_ : ∀ {κ x} → Rel (Ty κ x) 0ℓ
t ≄ u = ¬ t ≃ u

≃-refl : ∀ {κ x} {t : Ty κ x} → t ≃ t
≃-refl {𝕤} = refl
≃-refl {𝕥} {t = ⟨ s ⟩} = ⟨ ≃-refl ⟩
≃-refl {𝕥} {t = `⊤} = `⊤
≃-refl {𝕥} {t = t ⟨ a ⟩→ u} = ≃-refl `→ ≃-refl
≃-refl {𝕥} {t = t ⊗⟨ d ⟩ u} = ≃-refl ⊗ ≃-refl
≃-refl {𝕥} {t = t ⊕ u} = ≃-refl ⊕ ≃-refl

≃-sym : ∀ {κ x} {t u : Ty κ x} → t ≃ u → u ≃ t
≃-sym {𝕤} eq = Eq*.symmetric _≃𝕊_ eq
≃-sym {𝕥} `⊤ = `⊤
≃-sym {𝕥} (eq₁ ⊗ eq₂) = ≃-sym eq₁ ⊗ ≃-sym eq₂
≃-sym {𝕥} (eq₁ ⊕ eq₂) = ≃-sym eq₁ ⊕ ≃-sym eq₂
≃-sym {𝕥} (eq₁ `→ eq₂) = ≃-sym eq₁ `→ ≃-sym eq₂
≃-sym {𝕥} ⟨ eq ⟩ = ⟨ ≃-sym eq ⟩

≃-trans :  ∀ {κ x} {u v w : Ty κ x} → u ≃ v → v ≃ w → u ≃ w
≃-trans {𝕤} uv vw = uv ◅◅ vw
≃-trans {𝕥} `⊤ `⊤ = `⊤
≃-trans {𝕥} (uv ⊗ uv₁) (vw ⊗ vw₁) = ≃-trans uv vw ⊗ ≃-trans uv₁ vw₁
≃-trans {𝕥} (uv ⊕ uv₁) (vw ⊕ vw₁) = ≃-trans uv vw ⊕ ≃-trans uv₁ vw₁
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
≃-skipˡ = Eq*.return ≃𝕊-skipˡ

≃-skipʳ : s ; skip ≃ s
≃-skipʳ = Eq*.return ≃𝕊-skipʳ

≃-assoc-; : (s₁ ; s₂) ; s₃ ≃ s₁ ; (s₂ ; s₃)
≃-assoc-; = Eq*.return ≃𝕊-assoc

≃-brn₁ : s₁ ≃ s₂ → brn p s₁ s ≃ brn p s₂ s
≃-brn₁ = Eq*.gmap _ ≃𝕊-brn₁

≃-brn₂ : s₁ ≃ s₂ → brn p s s₁ ≃ brn p s s₂
≃-brn₂ = Eq*.gmap _ ≃𝕊-brn₂

≃-brn : s₁ ≃ s₁′ → s₂ ≃ s₂′ → brn p s₁ s₂ ≃ brn p s₁′ s₂′
≃-brn e₁ e₂ = ≃-brn₁ e₁ ◅◅ ≃-brn₂ e₂

≃-distr : brn p s₁ s₂ ; s ≃ brn p (s₁ ; s) (s₂ ; s)
≃-distr = Eq*.return ≃𝕊-distr

≃-⋯ : {ϕ : m →ₛ n} → s₁ ≃ s₂ → s₁ ⋯ ϕ ≃ s₂ ⋯ ϕ
≃-⋯ {ϕ = ϕ} = go′ where
  go : {ϕ : m →ₛ n} → s₁ ≃𝕊 s₂ → s₁ ⋯ ϕ ≃ s₂ ⋯ ϕ
  go (≃𝕊-;₁ x) = ≃-; (go x) ≃-refl
  go (≃𝕊-;₂ x) = ≃-; ≃-refl (go x)
  go ≃𝕊-skipˡ = ≃-skipˡ
  go ≃𝕊-skipʳ = ≃-skipʳ
  go {ϕ = ϕ} (≃𝕊-μ {s = s}) =
    subst (λ w → mu (s ⋯ ϕ ↑) ≃ w) (sym (dist-↑-⦅⦆-⋯ s (mu s) ϕ)) ≃-μ
  go ≃𝕊-assoc = ≃-assoc-;
  go ≃𝕊-distr = ≃-distr
  go (≃𝕊-msg x) = Eq*.return (≃𝕊-msg x)
  go (≃𝕊-brn₁ x) = ≃-brn₁ (go x)
  go (≃𝕊-brn₂ x) = ≃-brn₂ (go x)

  go′ : {ϕ : m →ₛ n} → s₁ ≃ s₂ → s₁ ⋯ ϕ ≃ s₂ ⋯ ϕ
  go′ refl = refl
  go′ (fwd x ◅ xs) = go x ◅◅ go′ xs
  go′ (bwd x ◅ xs) = ≃-sym (go x) ◅◅ go′ xs

≃-⟨⟩⁻¹ : ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
≃-⟨⟩⁻¹ ⟨ eq ⟩ = eq

≃-⊗⁻¹ : T₁ ⊗⟨ d₁ ⟩ U₁ ≃ T₂ ⊗⟨ d₂ ⟩ U₂ → T₁ ≃ T₂ × d₁ ≡ d₂ × U₁ ≃ U₂
≃-⊗⁻¹ (eq₁ ⊗ eq₂) = eq₁ , refl , eq₂

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

≃-skipsˡ : Skips s → s ; s′ ≃ s′
≃-skipsˡ x = ≃-trans (≃-; (≃-sym (skips⇒skip≃ x)) refl) ≃-skipˡ

≃-skipsʳ : Skips s → s′ ; s ≃ s′
≃-skipsʳ x = ≃-trans (≃-; refl (≃-sym (skips⇒skip≃ x))) ≃-skipʳ

data AtomKind n : Set where
  `_ : 𝔽 n → AtomKind n
  end msg : Pol → AtomKind n
  ret acq : AtomKind n
  ``_ : UVar → AtomKind n

data Atom {n} : 𝕊 n → Set where
  `- : ∀ {x} → Atom (` x)
  end : Atom (end p)
  msg : Atom (msg p T)
  ret : Atom ret
  acq : Atom acq
  ``- : ∀ {α} → Atom (`` α)

atomKind : {a : 𝕊 n} → Atom a → AtomKind n
atomKind {a = ` x} `- = ` x
atomKind {a = end p} end = end p
atomKind {a = msg p t} msg = msg p
atomKind {a = ret} ret = ret
atomKind {a = acq} acq = acq
atomKind {a = `` α} ``- = `` α

atom-⋯ᵣ : Atom s → {ϕ : m →ᵣ n} → Atom (s ⋯ ϕ)
atom-⋯ᵣ `- = `-
atom-⋯ᵣ end = end
atom-⋯ᵣ msg = msg
atom-⋯ᵣ ret = ret
atom-⋯ᵣ acq = acq
atom-⋯ᵣ ``- = ``-

¬skips-atom : {a : 𝕊 n} → Atom a → ¬ Skips a
¬skips-atom `-  ()
¬skips-atom end ()
¬skips-atom msg ()
¬skips-atom ret ()
¬skips-atom acq ()
¬skips-atom ``- ()

¬atom-; : ¬ Atom (s₁ ; s₂)
¬atom-; ()

¬atom-brn : ¬ Atom (brn p s₁ s₂)
¬atom-brn ()

data AtomLike : 𝕊 n → Set where
  refl : Atom s → AtomLike s
  _;₁_ : AtomLike s₁ → Skips s₂ → AtomLike (s₁ ; s₂)
  _;₂_ : Skips s₁ → AtomLike s₂ → AtomLike (s₁ ; s₂)
  mu   : AtomLike s → AtomLike (mu s)

atomLike⊥skips : AtomLike s → Skips s → ⊥
atomLike⊥skips (refl ()) skip
atomLike⊥skips (a ;₁ _)  (z₁ ; z₂) = atomLike⊥skips a z₁
atomLike⊥skips (_ ;₂ a)  (z₁ ; z₂) = atomLike⊥skips a z₂
atomLike⊥skips (mu a)    (mu z)    = atomLike⊥skips a z

atomLike-⋯ᵣ : {ϕ : m →ᵣ n} → AtomLike s → AtomLike (s ⋯ᵣ ϕ)
atomLike-⋯ᵣ (refl A) = refl (atom-⋯ᵣ A)
atomLike-⋯ᵣ (a ;₁ x) = atomLike-⋯ᵣ a ;₁ skips-⋯ x
atomLike-⋯ᵣ (x ;₂ a) = skips-⋯ x ;₂ atomLike-⋯ᵣ a
atomLike-⋯ᵣ (mu a)   = mu (atomLike-⋯ᵣ a)

atomLike-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → AtomLike s → (∀ z → AtomLike (`/id (ϕ z))) → AtomLike (s ⋯ ϕ)
atomLike-⋯ (refl `-)  Aϕ = Aϕ _
atomLike-⋯ (refl end) Aϕ = refl end
atomLike-⋯ (refl msg) Aϕ = refl msg
atomLike-⋯ (refl ret) Aϕ = refl ret
atomLike-⋯ (refl acq) Aϕ = refl acq
atomLike-⋯ (refl ``-) Aϕ = refl ``-
atomLike-⋯ (a ;₁ x)   Aϕ = atomLike-⋯ a Aϕ ;₁ skips-⋯ x
atomLike-⋯ (x ;₂ a)   Aϕ = skips-⋯ x ;₂ atomLike-⋯ a Aϕ
atomLike-⋯ ⦃ K ⦄ (mu a) Aϕ = mu (atomLike-⋯ a λ where
  zero → refl (subst Atom (sym (`/`-is-` ⦃ K ⦄ _)) `-)
  (suc x) → subst AtomLike (wk-`/id _) (atomLike-⋯ᵣ (Aϕ x)))

atomLike-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → AtomLike (s ⋯ ϕ) →  (∀ z → ¬ Skips (`/id (ϕ z))) → AtomLike s
atomLike-⋯⁻¹ {s = skip}      (refl ())
atomLike-⋯⁻¹ {s = brn p _ _} (refl ())
atomLike-⋯⁻¹ {s = ` x}       a ¬Sϕ = refl `-
atomLike-⋯⁻¹ {s = end p}     a ¬Sϕ = refl end
atomLike-⋯⁻¹ {s = msg p t}   a ¬Sϕ = refl msg
atomLike-⋯⁻¹ {s = s₁ ; s₂}   (a ;₁ x) ¬Sϕ = atomLike-⋯⁻¹ a ¬Sϕ ;₁ skips-⋯⁻¹ x ¬Sϕ
atomLike-⋯⁻¹ {s = s₁ ; s₂}   (x ;₂ a) ¬Sϕ = skips-⋯⁻¹ x ¬Sϕ ;₂ atomLike-⋯⁻¹ a ¬Sϕ
atomLike-⋯⁻¹ {s = ret}       a ¬Sϕ = refl ret
atomLike-⋯⁻¹ {s = acq}       a ¬Sϕ = refl acq
atomLike-⋯⁻¹ {s = `` α}      a ¬Sϕ = refl ``-
atomLike-⋯⁻¹ {s = mu s} ⦃ K ⦄(mu a) ¬Sϕ = mu (atomLike-⋯⁻¹ a λ where
  zero    → ¬skips-`/` K
  (suc x) → ¬Sϕ x ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _)))

atomLike-≃ : s₁ ≃ s₂ → AtomLike s₁ → AtomLike s₂
atomLike-≃ refl = id
atomLike-≃ (x ◅ xs) = atomLike-≃ xs ∘ go x where
  go : SymClosure _≃𝕊_ s₁ s₂ → AtomLike s₁ → AtomLike s₂
  go (fwd (≃𝕊-msg x)) a = refl msg
  go (bwd (≃𝕊-msg x)) a = refl msg
  go (fwd (≃𝕊-;₁ x)) (a ;₁ z) = go (fwd x) a ;₁ z
  go (fwd (≃𝕊-;₁ x)) (z ;₂ a) = ≃-skips (Eq*.return x) z ;₂ a
  go (fwd (≃𝕊-;₂ x)) (a ;₁ z) = a ;₁ ≃-skips (Eq*.return x) z
  go (fwd (≃𝕊-;₂ x)) (z ;₂ a) = z ;₂ go (fwd x) a
  go (fwd ≃𝕊-skipˡ)  (refl () ;₁ z)
  go (fwd ≃𝕊-skipˡ)  (z ;₂ a) = a
  go (fwd ≃𝕊-skipʳ)  (a ;₁ z) = a
  go (fwd ≃𝕊-skipʳ)  (z ;₂ refl ())
  go (fwd ≃𝕊-μ)      (mu a) = atomLike-⋯ a λ where
    zero    → mu a
    (suc x) → refl `-
  go (fwd ≃𝕊-assoc) ((a ;₁ x) ;₁ y) = a ;₁ (x ; y)
  go (fwd ≃𝕊-assoc) ((x ;₂ a) ;₁ y) = x ;₂ (a ;₁ y)
  go (fwd ≃𝕊-assoc) ((x ;  y) ;₂ a) = x ;₂ (y ;₂ a)
  go (fwd ≃𝕊-distr) (refl () ;₁ x)
  go (bwd (≃𝕊-;₁ x)) (a ;₁ z) = go (bwd x) a ;₁ z
  go (bwd (≃𝕊-;₁ x)) (z ;₂ a) = ≃-skips (≃-sym (Eq*.return x)) z ;₂ a
  go (bwd (≃𝕊-;₂ x)) (a ;₁ z) = a ;₁ ≃-skips (≃-sym (Eq*.return x)) z
  go (bwd (≃𝕊-;₂ x)) (z ;₂ a) = z ;₂ go (bwd x) a
  go (bwd ≃𝕊-skipˡ) a = skip ;₂ a
  go (bwd ≃𝕊-skipʳ) a = a ;₁ skip
  go (bwd ≃𝕊-μ) a = mu (atomLike-⋯⁻¹ a λ where
    zero    z → atomLike⊥skips a (≃-skips ≃-μ z)
    (suc x) ())
  go (bwd ≃𝕊-assoc) (a ;₁ (x ;  y)) = (a ;₁ x) ;₁ y
  go (bwd ≃𝕊-assoc) (x ;₂ (a ;₁ y)) = (x ;₂ a) ;₁ y
  go (bwd ≃𝕊-assoc) (x ;₂ (y ;₂ a)) = (x ; y) ;₂ a
  go (bwd ≃𝕊-distr) (refl ())
  go (bwd (≃𝕊-brn₁ x)) (refl ())
  go (bwd (≃𝕊-brn₂ x)) (refl ())

atomLike-;⁻ : AtomLike (s₁ ; s₂) → AtomLike s₁ × Skips s₂ ⊎ AtomLike s₂ × Skips s₁
atomLike-;⁻ (a ;₁ x) = inj₁ (a , x)
atomLike-;⁻ (x ;₂ a) = inj₂ (a , x)

atom-;⁻ : Atom s → s ≃ s₁ ; s₂ → s ≃ s₁ × Skips s₂ ⊎ s ≃ s₂ × Skips s₁
atom-;⁻ A eq with atomLike-;⁻ (atomLike-≃ eq (refl A))
... | inj₁ (a , z) = inj₁ (≃-trans eq (≃-skipsʳ z) , z)
... | inj₂ (a , z) = inj₂ (≃-trans eq (≃-skipsˡ z) , z)

¬atomLike-brn : ¬ AtomLike (brn p s₁ s₂)
¬atomLike-brn (refl ())

atom≄brn : Atom s → s ≄ brn p s₁ s₂
atom≄brn A eq = ¬atomLike-brn (atomLike-≃ eq (refl A))

data All/One : Set where
  all one : All/One

_×[_]⊎_ : ∀ {a b} → Set a → All/One → Set b → Set _
X ×[ all ]⊎ Y = X × Y
X ×[ one ]⊎ Y = X ⊎ Y

all/one-mk :  ∀ {a b} {A : Set a} {B : Set b} (c : All/One) → A → B → A ×[ c ]⊎ B
all/one-mk all a b = a , b
all/one-mk one a _ = inj₁ a

all/one-map : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} (c : All/One) (f : A → A′) (g : B → B′) →
  A ×[ c ]⊎ B → A′ ×[ c ]⊎ B′
all/one-map all f g = Π.map f g
all/one-map one f g = Sum.map f g

data EndsIn (c : All/One) {a : 𝕊 n} .(A : Atom a) : 𝕊 n → Set where
  here : EndsIn c A a
  _;₁_ : EndsIn c A s₁ → Skips s₂ → EndsIn c A (s₁ ; s₂)
  -;₂_ : EndsIn c A s₂ → EndsIn c A (s₁ ; s₂)
  brn  : EndsIn c A s₁ ×[ c ]⊎ EndsIn c A s₂ → EndsIn c A (brn p s₁ s₂)
  mu   : EndsIn c (atom-⋯ᵣ A {weaken}) s′ → EndsIn c A (mu s′)

skips⊥endsIn : ∀ {c} .{A : Atom s′} → Skips s → EndsIn c A s → ⊥
skips⊥endsIn (s ; s₁) (e ;₁ x) = skips⊥endsIn s e
skips⊥endsIn (s ; s₁) (-;₂ e) = skips⊥endsIn s₁ e
skips⊥endsIn (mu s) (mu e) = skips⊥endsIn s e
skips⊥endsIn {A = A} skip here = ⊥-elim-irr (case A of λ())

{-
endsIn-⋯ : ∀ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {c} {a : 𝕊 m} .{A : Atom a} {ϕ : m –[ K ]→ n} →
  .(A′ : Atom (a ⋯ ϕ)) →
  EndsIn c A s → EndsIn c A′ (s ⋯ ϕ)
endsIn-⋯ A′ here = here
endsIn-⋯ A′ (e ;₁ s) = endsIn-⋯ A′ e ;₁ skips-⋯ s
endsIn-⋯ A′ (-;₂ e) = -;₂ endsIn-⋯ A′ e
endsIn-⋯ A′ (brn e) = {!!}
endsIn-⋯ {c = c} {a} {ϕ = ϕ} A′ (mu e) = EndsIn.mu
  $ subst (λ s → EndsIn c {s} _ _) {!!}
  $ endsIn-⋯ {ϕ = ϕ ↑} {!(atom-⋯ᵣ A′ {weaken})!} e

endsIn-≃ : ∀ {c} {a : 𝕊 n} {A : Atom a} → EndsIn c A Respects _≃_
endsIn-≃ refl = id
endsIn-≃ (x ◅ xs) = endsIn-≃ xs ∘ go x
  where
  go : ∀ {c} {a : 𝕊 n} {A : Atom a} → EndsIn c A Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ x)) (e ;₁ s) = go (fwd x) e ;₁ s
  go (fwd (≃𝕊-;₁ x)) (-;₂ e) = -;₂ e
  go (fwd (≃𝕊-;₂ x)) (e ;₁ s) = e ;₁ ≃-skips (Eq*.return x) s
  go (fwd (≃𝕊-;₂ x)) (-;₂ e) = -;₂ go (fwd x) e
  go (fwd ≃𝕊-skipˡ) (e ;₁ x) = ⊥-elim (skips⊥endsIn skip e)
  go (fwd ≃𝕊-skipˡ) (-;₂ e) = e
  go (fwd ≃𝕊-skipʳ) (e ;₁ x) = e
  go (fwd ≃𝕊-skipʳ) (-;₂ e) = ⊥-elim (skips⊥endsIn skip e)
  go (fwd ≃𝕊-μ) e = {!e!}
  go (fwd ≃𝕊-assoc) ((e ;₁ x₁) ;₁ x) = e ;₁ (x₁ ; x)
  go (fwd ≃𝕊-assoc) ((-;₂ e) ;₁ x) = -;₂ (e ;₁ x)
  go (fwd ≃𝕊-assoc) (-;₂ e) = -;₂ (-;₂ e)
  go (fwd ≃𝕊-distr) (brn e ;₁ x) = brn (all/one-map _ (_;₁ x) (_;₁ x) e)
  go (fwd ≃𝕊-distr) (-;₂ e) = brn (all/one-mk _ (-;₂ e) (-;₂ e))
  go (bwd (≃𝕊-;₁ x)) (e ;₁ x₁) = go (bwd x) e ;₁ x₁
  go (bwd (≃𝕊-;₁ x)) (-;₂ e) = -;₂ e
  go (bwd (≃𝕊-;₂ x)) (e ;₁ x₁) = e ;₁ ≃-skips (≃-sym (Eq*.return x)) x₁
  go (bwd (≃𝕊-;₂ x)) (-;₂ e) = -;₂ go (bwd x) e
  go (bwd ≃𝕊-skipˡ) e = -;₂ e
  go (bwd ≃𝕊-skipʳ) e = e ;₁ skip
  go (bwd ≃𝕊-μ) e = {!!}
  go (bwd ≃𝕊-assoc) (e ;₁ (x ; x₁)) = (e ;₁ x) ;₁ x₁
  go (bwd ≃𝕊-assoc) (-;₂ (e ;₁ x)) = (-;₂ e) ;₁ x
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ e)) = -;₂ e
  go {c = all} (bwd ≃𝕊-distr) (brn ((e₁ ;₁ s₁) , (e₂ ;₁ s₂))) = brn (e₁ , e₂) ;₁ s₂
  go {c = all} (bwd ≃𝕊-distr) (brn ((e₁ ;₁ s₁) , (-;₂ e₂))) = -;₂ e₂
  go {c = all} (bwd ≃𝕊-distr) (brn ((-;₂ e₁) , (e₂ ;₁ s₂))) = -;₂ e₁
  go {c = all} (bwd ≃𝕊-distr) (brn ((-;₂ e₁) , (-;₂ e₂))) = -;₂ e₁
  go {c = one} (bwd ≃𝕊-distr) (brn (inj₁ (x ;₁ x₁))) = brn (inj₁ x) ;₁ x₁
  go {c = one} (bwd ≃𝕊-distr) (brn (inj₁ (-;₂ x))) = -;₂ x
  go {c = one} (bwd ≃𝕊-distr) (brn (inj₂ (y ;₁ x))) = brn (inj₂ y) ;₁ x
  go {c = one} (bwd ≃𝕊-distr) (brn (inj₂ (-;₂ y))) = -;₂ y
-}

private
  endsVar : 𝔽 n → 𝕊 n → Set
  endsVar x = EndsIn one {` x} `-

  data MsgEnds (p : Pol) (T : 𝕋) {n} : 𝕊 n → Set where
    here : T ≃ T′ → MsgEnds p T (msg p T′)
    _;₁_ : MsgEnds p T s₁ → Skips s₂ → MsgEnds p T (s₁ ; s₂)
    -;₂_ : MsgEnds p T s₂ → MsgEnds p T (s₁ ; s₂)
    mu   : MsgEnds p T s → MsgEnds p T (mu s)
    brn  : MsgEnds p T s₁ → MsgEnds p T s₂ → MsgEnds p T (brn p′ s₁ s₂)

  ¬msgends-` : {x : 𝔽 n} → ¬ MsgEnds p T (` x)
  ¬msgends-` ()

  msgends-mu⁻ : MsgEnds p T (mu s) → MsgEnds p T s
  msgends-mu⁻ (mu Me) = Me

  msgends-brn⁻ : MsgEnds p T (brn p′ s₁ s₂) → MsgEnds p T s₁ × MsgEnds p T s₂
  msgends-brn⁻ (brn Me₁ Me₂) = Me₁ , Me₂

  msgends-;⁻ : MsgEnds p T (s₁ ; s₂) → MsgEnds p T s₁ × Skips s₂ ⊎ MsgEnds p T s₂
  msgends-;⁻ (Me₁ ;₁ s₂) = inj₁ (Me₁ , s₂)
  msgends-;⁻ (-;₂ Me₂)   = inj₂ Me₂

  skips⊥msgends : Skips s → MsgEnds p T s → ⊥
  skips⊥msgends (s₁ ; s₂) (Me ;₁ x) = skips⊥msgends s₁ Me
  skips⊥msgends (s₁ ; s₂) (-;₂ Me) = skips⊥msgends s₂ Me
  skips⊥msgends (mu s) (mu Me) = skips⊥msgends s Me

  msgends-⋯ᵣ : {ρ : m →ᵣ n} → MsgEnds p T s → MsgEnds p T (s ⋯ ρ)
  msgends-⋯ᵣ (here eq) = here eq
  msgends-⋯ᵣ (Me ;₁ x) = msgends-⋯ᵣ Me ;₁ skips-⋯ x
  msgends-⋯ᵣ (-;₂ Me) = -;₂ msgends-⋯ᵣ Me
  msgends-⋯ᵣ (mu Me) = mu (msgends-⋯ᵣ Me)
  msgends-⋯ᵣ (brn Me Me₁) = brn (msgends-⋯ᵣ Me) (msgends-⋯ᵣ Me₁)

  msgends-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → MsgEnds p T s → MsgEnds p T (s ⋯ ϕ)
  msgends-⋯ (here eq) = here eq
  msgends-⋯ (Me ;₁ x) = msgends-⋯ Me ;₁ skips-⋯ x
  msgends-⋯ (-;₂ Me) = -;₂ msgends-⋯ Me
  msgends-⋯ (mu Me) = mu (msgends-⋯ Me)
  msgends-⋯ (brn Me Me₁) = brn (msgends-⋯ Me) (msgends-⋯ Me₁)

  msgends-⋯ᵣ⁻¹ : {ϕ : m →ᵣ n} → MsgEnds p T (s ⋯ ϕ) → MsgEnds p T s
  msgends-⋯ᵣ⁻¹ {s = msg p₃ t} (here eq) = here eq
  msgends-⋯ᵣ⁻¹ {s = brn p₃ s₁ s₂} (brn Me Me₁) = brn (msgends-⋯ᵣ⁻¹ Me) (msgends-⋯ᵣ⁻¹ Me₁)
  msgends-⋯ᵣ⁻¹ {s = mu s} (mu Me) = mu (msgends-⋯ᵣ⁻¹ Me)
  msgends-⋯ᵣ⁻¹ {s = s₁ ; s₂} (Me ;₁ x) = msgends-⋯ᵣ⁻¹ Me ;₁ skips-⋯ᵣ⁻¹ x
  msgends-⋯ᵣ⁻¹ {s = s₁ ; s₂} (-;₂ Me) = -;₂ msgends-⋯ᵣ⁻¹ Me

  msgends⋯⇒ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} →
    MsgEnds p T (s ⋯ ϕ) →
    (∀ z → ¬ Skips (`/id (ϕ z))) →
    ∀ {z} → endsVar z s → MsgEnds p T (`/id (ϕ z))
  msgends⋯⇒ Me ∀¬S here = Me
  msgends⋯⇒ (Me ;₁ x₁) ∀¬S (E ;₁ x) = msgends⋯⇒ Me ∀¬S E
  msgends⋯⇒ (-;₂ Me) ∀¬S (E ;₁ s) = ⊥-elim (skips⊥msgends (skips-⋯ s) Me)
  msgends⋯⇒ (Me ;₁ s) ∀¬S (-;₂ E) = ⊥-elim (skips⊥endsIn (skips-⋯⁻¹ s ∀¬S) E)
  msgends⋯⇒ (-;₂ Me) ∀¬S (-;₂ E) = msgends⋯⇒ Me ∀¬S E
  msgends⋯⇒ (brn Me₁ Me₂) ∀¬S (brn (inj₁ E)) = msgends⋯⇒ Me₁ ∀¬S E
  msgends⋯⇒ (brn Me₁ Me₂) ∀¬S (brn (inj₂ E)) = msgends⋯⇒ Me₂ ∀¬S E
  msgends⋯⇒ ⦃ K ⦄ (mu Me) ∀¬S (mu E) =
    let IH = msgends⋯⇒ Me (λ{ zero → ¬skips-`/` K; (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _)) }) E in
    msgends-⋯ᵣ⁻¹ (subst (MsgEnds _ _) (sym (wk-`/id _)) IH)

  msgends-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → MsgEnds p T (s ⋯ ϕ)
    → (∀ z → ¬ Skips (`/id (ϕ z)))
    → (∀ z → endsVar z s → MsgEnds p T s)
    → MsgEnds p T s
  msgends-⋯⁻¹ {s = ` x} Me ∀¬S ∀¬E = ∀¬E x here
  msgends-⋯⁻¹ {s = msg p₃ t} (here eq) ∀¬S ∀¬E = here eq
  msgends-⋯⁻¹ {s = brn p₃ s₁ s₂} (brn Me₁ Me₂) ∀¬S ∀¬E =
    brn (msgends-⋯⁻¹ Me₁ ∀¬S λ z → proj₁ ∘ msgends-brn⁻ ∘ ∀¬E z ∘ brn ∘′ inj₁)
        (msgends-⋯⁻¹ Me₂ ∀¬S λ z → proj₂ ∘ msgends-brn⁻ ∘ ∀¬E z ∘ brn ∘′ inj₂)
  msgends-⋯⁻¹ {s = mu s} ⦃ K ⦄ (mu Me) ∀¬S ∀¬E =
    let ∀¬S′ = λ where zero    → ¬skips-`/` K
                       (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _))
    in
    mu (msgends-⋯⁻¹ Me ∀¬S′ λ where
      zero    → ⊥-elim ∘ ¬msgends-` ∘ subst (MsgEnds _ _) (`/`-is-` ⦃ K ⦄ _) ∘ msgends⋯⇒ Me ∀¬S′
      (suc z) → msgends-mu⁻ ∘ ∀¬E z ∘ mu)
  msgends-⋯⁻¹ {s = s₁ ; s₂} (Me ;₁ s) ∀¬S ∀¬E =
    let s′ = skips-⋯⁻¹ s ∀¬S in
    msgends-⋯⁻¹ Me ∀¬S (λ z E → proj₁ $ Sum.fromInj₁ (⊥-elim ∘ skips⊥msgends s′) $ msgends-;⁻ $ ∀¬E z (E ;₁ s′)) ;₁ s′
  msgends-⋯⁻¹ {s = s₁ ; s₂} (-;₂ Me) ∀¬S ∀¬E = -;₂ msgends-⋯⁻¹ Me ∀¬S λ z →
    Sum.fromInj₂ (⊥-elim ∘ flip skips⊥msgends Me ∘ skips-⋯ ∘ proj₂) ∘ msgends-;⁻ ∘ ∀¬E z ∘ -;₂_

  msgends-unfold⁻¹ : MsgEnds p T (unfold s) → MsgEnds p T s
  msgends-unfold⁻¹ {s = s} Me with skips? s
  ... | yes Ss = ⊥-elim (skips⊥msgends (skips-⋯ Ss) Me)
  ... | no ¬Ss =
    let ¬skips-unfold = λ{ zero (mu Ss) → ¬Ss Ss } in
    msgends-⋯⁻¹ Me ¬skips-unfold λ where
      zero    E → msgends-mu⁻ $ msgends⋯⇒ Me ¬skips-unfold E
      (suc x) E → ⊥-elim $ ¬msgends-` $ msgends⋯⇒ Me ¬skips-unfold E

  ≃-msgends : ∀ {n p T} {s₁ s₂ : 𝕊 n} → s₁ ≃ s₂ → MsgEnds p T s₁ → MsgEnds p T s₂
  ≃-msgends refl me = me
  ≃-msgends {n = n} {p} {T} (x ◅ xs) me = ≃-msgends xs (go x me) where
    go : ∀ {s₁ s₂ : 𝕊 n} → SymClosure _≃𝕊_ s₁ s₂ → MsgEnds p T s₁ → MsgEnds p T s₂
    go (fwd (≃𝕊-msg x)) (here eq) = here (≃-trans eq x)
    go (fwd ≃𝕊-μ) (mu Me) = msgends-⋯ Me
    go (fwd (≃𝕊-;₁ x)) (Me ;₁ x₁) = go (fwd x) Me ;₁ x₁
    go (fwd (≃𝕊-;₁ x)) (-;₂ Me) = -;₂ Me
    go (fwd (≃𝕊-;₂ x)) (Me ;₁ x₁) = Me ;₁ ≃-skips (Eq*.return x) x₁
    go (fwd (≃𝕊-;₂ x)) (-;₂ Me) = -;₂ go (fwd x) Me
    go (fwd (≃𝕊-brn₁ x)) (brn Me Me₁) = brn (go (fwd x) Me) Me₁
    go (fwd (≃𝕊-brn₂ x)) (brn Me Me₁) = brn Me (go (fwd x) Me₁)
    go (fwd ≃𝕊-skipˡ) (-;₂ Me) = Me
    go (fwd ≃𝕊-skipʳ) (Me ;₁ x) = Me
    go (fwd ≃𝕊-skipˡ) (() ;₁ _)
    go (fwd ≃𝕊-skipʳ) (-;₂ ())
    go (fwd ≃𝕊-assoc) ((Me ;₁ x₁) ;₁ x) = Me ;₁ (x₁ ; x)
    go (fwd ≃𝕊-assoc) ((-;₂ Me) ;₁ x) = -;₂ (Me ;₁ x)
    go (fwd ≃𝕊-assoc) (-;₂ Me) = -;₂ (-;₂ Me)
    go (fwd ≃𝕊-distr) (brn Me Me₁ ;₁ x) = brn (Me ;₁ x) (Me₁ ;₁ x)
    go (fwd ≃𝕊-distr) (-;₂ Me) = brn (-;₂ Me) (-;₂ Me)
    go (bwd (≃𝕊-msg x)) (here eq) = here (≃-trans eq (≃-sym x))
    go (bwd (≃𝕊-;₁ x)) (Me ;₁ x₁) = go (bwd x) Me ;₁ x₁
    go (bwd (≃𝕊-;₁ x)) (-;₂ Me) = -;₂ Me
    go (bwd (≃𝕊-;₂ x)) (Me ;₁ x₁) = Me ;₁ ≃-skips (Star.return (bwd x)) x₁
    go (bwd (≃𝕊-;₂ x)) (-;₂ Me) = -;₂ go (bwd x) Me
    go (bwd (≃𝕊-brn₁ x)) (brn Me Me₁) = brn (go (bwd x) Me) Me₁
    go (bwd (≃𝕊-brn₂ x)) (brn Me Me₁) = brn Me (go (bwd x) Me₁)
    go (bwd ≃𝕊-μ) Me = mu (msgends-unfold⁻¹ Me)
    go (bwd ≃𝕊-skipˡ) Me = -;₂ Me
    go (bwd ≃𝕊-skipʳ) Me = Me ;₁ skip
    go (bwd ≃𝕊-assoc) (Me ;₁ (x ; x₁)) = (Me ;₁ x) ;₁ x₁
    go (bwd ≃𝕊-assoc) (-;₂ (Me ;₁ x)) = (-;₂ Me) ;₁ x
    go (bwd ≃𝕊-assoc) (-;₂ (-;₂ Me)) = -;₂ Me
    go (bwd ≃𝕊-distr) (brn (Me ;₁ x) (Me₁ ;₁ x₁)) = brn Me Me₁ ;₁ x₁
    go (bwd ≃𝕊-distr) (brn (Me ;₁ x) (-;₂ Me₁)) = -;₂ Me₁
    go (bwd ≃𝕊-distr) (brn (-;₂ Me) Me₁) = -;₂ Me

  msgends-inv : ∀ {n p T T₂} → MsgEnds p T (msg {n} p T₂) → T ≃ T₂
  msgends-inv (here eq) = eq

≃-msg⁻¹ : msg {n} p₁ T₁ ≃ msg p₂ T₂ → p₁ ≡ p₂ → T₁ ≃ T₂
≃-msg⁻¹ eq refl = msgends-inv (≃-msgends eq (here ≃-refl))

atom-≃′-;ʳ-skips : {a₁ a₂ : 𝕊 n} → Atom a₁ → Atom a₂ → {s : 𝕊 n} → s ; a₁ ≃𝕊 a₂ → Skips s × a₁ ≡ a₂
atom-≃′-;ʳ-skips A₁ A₂ ≃𝕊-skipˡ = skip , refl
