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

≃-⟨⟩⁻¹ : ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
≃-⟨⟩⁻¹ ⟨ eq ⟩ = eq

≃-⊗⁻¹ : T₁ ⊗⟨ d₁ ⟩ U₁ ≃ T₂ ⊗⟨ d₂ ⟩ U₂ → T₁ ≃ T₂ × d₁ ≡ d₂ × U₁ ≃ U₂
≃-⊗⁻¹ (eq₁ ⊗ eq₂) = eq₁ , refl , eq₂

postulate ≃-msg⁻¹ : msg {n} p₁ T₁ ≃ msg p₂ T₂ → p₁ ≡ p₂ → T₁ ≃ T₂

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

data Atom {n} : 𝕊 n → Set where
  `- : ∀ {x} → Atom (` x)
  end : Atom (end p)
  msg : Atom (msg p T)
  ret : Atom ret
  acq : Atom acq
  ``- : ∀ {α} → Atom (`` α)

{-
atom-≄′ˡ : ∀ {a} → Atom a → ¬ a ≃𝕊 s
atom-≄′ˡ `-  ()
atom-≄′ˡ end ()
atom-≄′ˡ msg ()
atom-≄′ˡ ret ()
atom-≄′ˡ acq ()
atom-≄′ˡ ``- ()
-}

atom-⋯ᵣ : Atom s → {ϕ : m →ᵣ n} → Atom (s ⋯ ϕ)
atom-⋯ᵣ `- = `-
atom-⋯ᵣ end = end
atom-⋯ᵣ msg = msg
atom-⋯ᵣ ret = ret
atom-⋯ᵣ acq = acq
atom-⋯ᵣ ``- = ``-

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

atom-≃′-;ʳ-skips : {a₁ a₂ : 𝕊 n} → Atom a₁ → Atom a₂ → {s : 𝕊 n} → s ; a₁ ≃𝕊 a₂ → Skips s × a₁ ≡ a₂
atom-≃′-;ʳ-skips A₁ A₂ ≃𝕊-skipˡ = skip , refl

{-
atom-;ʳ-⁻¹-′ : {a₁ a₂ : 𝕊 n} → Atom a₁ → Atom a₂ → {s s₁ s₂ : 𝕊 n} → s₁ ; a₁ ≃𝕊 s → s₂ ; a₂ ≃𝕊 s → s₁ ≃ s₂ × a₁ ≡ a₂
atom-;ʳ-⁻¹-′ A₁ A₂ (≃𝕊-;₁ eq₁) (≃𝕊-;₁ eq₂) = ≃-trans (Eq*.return eq₁) (≃-sym (Eq*.return eq₂)) , refl
atom-;ʳ-⁻¹-′ A₁ A₂ (≃𝕊-;₁ eq₁) (≃𝕊-;₂ eq₂) = contradiction eq₂ (atom-≄′ˡ A₂)
atom-;ʳ-⁻¹-′ A₁ A₂ (≃𝕊-;₂ eq₁) (≃𝕊-;₁ eq₂) = contradiction eq₁ (atom-≄′ˡ A₁)
atom-;ʳ-⁻¹-′ A₁ A₂ (≃𝕊-;₂ eq₁) (≃𝕊-;₂ eq₂) = contradiction eq₁ (atom-≄′ˡ A₁)
atom-;ʳ-⁻¹-′ A₁ A₂ (≃𝕊-;₂ eq₁) ≃𝕊-assoc = contradiction eq₁ (atom-≄′ˡ A₁)
atom-;ʳ-⁻¹-′ A₁ A₂ ≃𝕊-skipˡ ≃𝕊-skipˡ = refl , refl
atom-;ʳ-⁻¹-′ A₁ A₂ ≃𝕊-assoc (≃𝕊-;₂ eq₂) = contradiction eq₂ (atom-≄′ˡ A₂)
atom-;ʳ-⁻¹-′ A₁ A₂ ≃𝕊-assoc ≃𝕊-assoc = refl , refl
atom-;ʳ-⁻¹-′ A₁ A₂ ≃𝕊-distr ≃𝕊-distr = refl , refl
-}


postulate
  atom-;-unsnoc : {a x y z : 𝕊 n} → Atom a → x ; y ≃ z ; a → Skips y ⊎ ∃[ y′ ] x ; y′ ≃ z × y′ ; a ≃ y

-- atom-refl-;-skips⁻¹ : Atom s → (s′ : 𝕊 n) → s ≃ s ; s′ → Skips s′
-- atom-refl-;-skips⁻¹ a (` x) eq = {!!}
-- atom-refl-;-skips⁻¹ a (end p) eq = {!!}
-- atom-refl-;-skips⁻¹ a (msg p t) eq = {!!}
-- atom-refl-;-skips⁻¹ a (brn p s₁ s₂) eq = {!!}
-- atom-refl-;-skips⁻¹ a (mu s) eq = {!!}
-- atom-refl-;-skips⁻¹ a (s₁ ; s₂) eq = {!!}
-- atom-refl-;-skips⁻¹ a skip eq = {!!}
-- atom-refl-;-skips⁻¹ a ret eq = {!!}
-- atom-refl-;-skips⁻¹ a acq eq = {!!}
-- atom-refl-;-skips⁻¹ a (`` α) eq = {!!}

-- -- atom-refl-;-skips⁻¹ : Atom s → s ≃ s ; s′ → Skips s′
-- -- atom-refl-;-skips⁻¹ `-  (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ end (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ msg (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ ret (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ acq (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ ``- (fwd () ◅ eq)
-- -- atom-refl-;-skips⁻¹ `-  (bwd x ◅ eq) = {!!}
-- -- atom-refl-;-skips⁻¹ end (bwd x ◅ eq) = {!!}
-- -- atom-refl-;-skips⁻¹ msg (bwd x ◅ eq) = {!!}
-- -- atom-refl-;-skips⁻¹ ret (bwd x ◅ eq) = {!!}
-- -- atom-refl-;-skips⁻¹ acq (bwd x ◅ eq) = {!!}
-- -- atom-refl-;-skips⁻¹ ``- (bwd x ◅ eq) = {!!}
