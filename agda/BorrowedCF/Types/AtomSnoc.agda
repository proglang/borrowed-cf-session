module BorrowedCF.Types.AtomSnoc where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence

open Bin
open Nat.Variables

private variable
  w z z₁ z₂ z′ : 𝕊 n

------------------------------------------------------------------------
-- Congruences that are not yet in Equivalence.agda
------------------------------------------------------------------------

≃-brn₁ : s₁ ≃ s₂ → brn p s₁ s ≃ brn p s₂ s
≃-brn₁ = Eq*.gmap _ ≃𝕊-brn₁

≃-brn₂ : s₁ ≃ s₂ → brn p s s₁ ≃ brn p s s₂
≃-brn₂ = Eq*.gmap _ ≃𝕊-brn₂

≃-brn : s₁ ≃ s₁′ → s₂ ≃ s₂′ → brn p s₁ s₂ ≃ brn p s₁′ s₂′
≃-brn e₁ e₂ = ≃-brn₁ e₁ ◅◅ ≃-brn₂ e₂

≃-distr : brn p s₁ s₂ ; s ≃ brn p (s₁ ; s) (s₂ ; s)
≃-distr = Eq*.return ≃𝕊-distr

------------------------------------------------------------------------
-- ≃ respects substitution
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Snoc a w z  :  structural witness that  w ≃ z ; a  (w "ends in" atom a)
------------------------------------------------------------------------

data Snoc {n} (a : 𝕊 n) : 𝕊 n → 𝕊 n → Set where
  here : Snoc a a skip
  _;₁_ : Snoc a s₁ z → Skips s₂ → Snoc a (s₁ ; s₂) z
  -;₂_ : Snoc a s₂ z → Snoc a (s₁ ; s₂) (s₁ ; z)
  brn  : Snoc a s₁ z₁ → Snoc a s₂ z₂ → Snoc a (brn p s₁ s₂) (brn p z₁ z₂)
  mu   : Snoc (a ⋯ weakenᵣ) s z → Snoc a (mu s) (z ⋯ ⦅ mu s ⦆ₛ)

snoc-sound : {a : 𝕊 n} → Snoc a w z → w ≃ z ; a
snoc-sound here = ≃-sym ≃-skipˡ
snoc-sound (sn ;₁ Sk) = ≃-trans (≃-skipsʳ Sk) (snoc-sound sn)
snoc-sound (-;₂ sn) = ≃-trans (≃-; ≃-refl (snoc-sound sn)) (≃-sym ≃-assoc-;)
snoc-sound (brn sn₁ sn₂) = ≃-trans (≃-brn (snoc-sound sn₁) (snoc-sound sn₂)) (≃-sym ≃-distr)
snoc-sound {a = a} (mu {s = s} {z = z} sn) =
  ≃-trans ≃-μ
    (subst (λ t → s ⋯ ⦅ mu s ⦆ₛ ≃ (z ⋯ ⦅ mu s ⦆ₛ) ; t)
           (wk-cancels-⦅⦆-⋯ a (mu s))
           (≃-⋯ (snoc-sound sn)))

------------------------------------------------------------------------
-- Snoc is preserved by substitution;  forward direction of the μ step
------------------------------------------------------------------------

snoc-⋯ : {a : 𝕊 m} {ϕ : m →ₛ n} → Snoc a w z → Snoc (a ⋯ ϕ) (w ⋯ ϕ) (z ⋯ ϕ)
snoc-⋯ here = here
snoc-⋯ (sn ;₁ Sk) = snoc-⋯ sn ;₁ skips-⋯ Sk
snoc-⋯ (-;₂ sn) = -;₂ snoc-⋯ sn
snoc-⋯ (brn sn₁ sn₂) = brn (snoc-⋯ sn₁) (snoc-⋯ sn₂)
snoc-⋯ {a = a} {ϕ = ϕ} (mu {s = s} {z = z} sn) =
  subst (Snoc (a ⋯ ϕ) (mu (s ⋯ ϕ ↑)))
    (sym (dist-↑-⦅⦆-⋯ z (mu s) ϕ))
    (mu (subst (λ t → Snoc t (s ⋯ ϕ ↑) (z ⋯ ϕ ↑)) (sym (⋯-↑-wk a ϕ)) (snoc-⋯ {ϕ = ϕ ↑} sn)))

snoc-unfold : {a : 𝕊 n} → Atom a → Snoc a (mu s) z → Snoc a (unfold s) z
snoc-unfold {a = a} A (mu {s = s} {z = z} sn) =
  subst (λ t → Snoc t (unfold s) (z ⋯ ⦅ mu s ⦆ₛ)) (wk-cancels-⦅⦆-⋯ a (mu s)) (snoc-⋯ sn)
snoc-unfold A here = case A of λ ()

------------------------------------------------------------------------
-- Backward direction of the μ step (structural un-substitution)
------------------------------------------------------------------------

EndsIn-` : 𝔽 n → 𝕊 n → Set
EndsIn-` x = EndsIn one {` x} `-

¬skips-atom : {a : 𝕊 n} → Atom a → ¬ Skips a
¬skips-atom `- ()
¬skips-atom end ()
¬skips-atom msg ()
¬skips-atom ret ()
¬skips-atom acq ()
¬skips-atom ``- ()

skips⊥snoc : {a : 𝕊 n} → Atom a → Skips w → Snoc a w z → ⊥
skips⊥snoc A Sk here = ¬skips-atom A Sk
skips⊥snoc A (Sk₁ ; Sk₂) (sn ;₁ _) = skips⊥snoc A Sk₁ sn
skips⊥snoc A (Sk₁ ; Sk₂) (-;₂ sn) = skips⊥snoc A Sk₂ sn
skips⊥snoc A (mu Sk) (mu sn) = skips⊥snoc (atom-⋯ᵣ A) Sk sn

↑ᵣ-inj : {ρ : m →ᵣ n} → (∀ {x y} → ρ x ≡ ρ y → x ≡ y) → ∀ {x y} → (ρ ↑) x ≡ (ρ ↑) y → x ≡ y
↑ᵣ-inj inj {zero} {zero} eqxy = refl
↑ᵣ-inj inj {suc x} {suc y} eqxy = cong suc (inj (Fin.suc-injective eqxy))

snoc-⋯ᵣ⁻¹ : {α : 𝕊 n} {a′ : 𝕊 m} {ρ : m →ᵣ n} → (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  Atom a′ → α ≡ a′ ⋯ ρ → Snoc α (s ⋯ ρ) z → ∃[ z₀ ] Snoc a′ s z₀
snoc-⋯ᵣ⁻¹ {s = ` x} inj (`- {x = x′}) eq here = _ , subst (λ w → Snoc (` x′) w skip) (cong `_ (sym (inj (`-injective eq)))) here
snoc-⋯ᵣ⁻¹ {s = ` x} inj end eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ` x} inj msg eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ` x} inj ret eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ` x} inj acq eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ` x} inj ``- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = end p} inj `- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = end p} inj end refl here = _ , here
snoc-⋯ᵣ⁻¹ {s = end p} inj msg eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = end p} inj ret eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = end p} inj acq eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = end p} inj ``- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = msg p t} inj `- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = msg p t} inj end eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = msg p t} inj msg refl here = _ , here
snoc-⋯ᵣ⁻¹ {s = msg p t} inj ret eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = msg p t} inj acq eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = msg p t} inj ``- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ret} inj `- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ret} inj end eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ret} inj msg eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ret} inj ret refl here = _ , here
snoc-⋯ᵣ⁻¹ {s = ret} inj acq eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = ret} inj ``- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = acq} inj `- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = acq} inj end eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = acq} inj msg eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = acq} inj ret eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = acq} inj acq refl here = _ , here
snoc-⋯ᵣ⁻¹ {s = acq} inj ``- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj `- eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj end eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj msg eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj ret eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj acq eq here = case eq of λ ()
snoc-⋯ᵣ⁻¹ {s = `` β} inj ``- refl here = _ , here
snoc-⋯ᵣ⁻¹ {s = skip} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
snoc-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
snoc-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq (sn ;₁ Sk) = _ , proj₂ (snoc-⋯ᵣ⁻¹ inj A eq sn) ;₁ skips-⋯ᵣ⁻¹ Sk
snoc-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq (-;₂ sn) = _ , -;₂ proj₂ (snoc-⋯ᵣ⁻¹ inj A eq sn)
snoc-⋯ᵣ⁻¹ {s = brn p s₁ s₂} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
snoc-⋯ᵣ⁻¹ {s = brn p s₁ s₂} inj A eq (brn sn₁ sn₂) = _ , brn (proj₂ (snoc-⋯ᵣ⁻¹ inj A eq sn₁)) (proj₂ (snoc-⋯ᵣ⁻¹ inj A eq sn₂))
snoc-⋯ᵣ⁻¹ {s = mu s} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
snoc-⋯ᵣ⁻¹ {s = mu s₀} {a′ = a′} {ρ = ρ} inj A eq (mu sn) =
  _ , mu (proj₂ (snoc-⋯ᵣ⁻¹ (↑ᵣ-inj inj) (atom-⋯ᵣ A) (cong (_⋯ weakenᵣ) eq ■ ⋯-↑-wk a′ ρ) sn))

weaken-inj : {x y : 𝔽 n} → weakenᵣ x ≡ weakenᵣ y → x ≡ y
weaken-inj = Fin.suc-injective

-- If s⋯ϕ ends in atom a and s ends in variable y, then the image ϕ y ends in a.
snoc⋯⇒snoc : {a : 𝕊 n} {ϕ : m →ₛ n} → Atom a → Snoc a (s ⋯ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) → ∀ {y} → EndsIn-` y s → ∃[ z′ ] Snoc a (`/id (ϕ y)) z′
snoc⋯⇒snoc A sn ∀¬S here = _ , sn
snoc⋯⇒snoc A (sn ;₁ Sk) ∀¬S (E ;₁ x) = snoc⋯⇒snoc A sn ∀¬S E
snoc⋯⇒snoc A (-;₂ sn) ∀¬S (E ;₁ x) = ⊥-elim (skips⊥snoc A (skips-⋯ x) sn)
snoc⋯⇒snoc A (sn ;₁ Sk) ∀¬S (-;₂ E) = ⊥-elim (skips⊥endsIn (skips-⋯⁻¹ Sk ∀¬S) E)
snoc⋯⇒snoc A (-;₂ sn) ∀¬S (-;₂ E) = snoc⋯⇒snoc A sn ∀¬S E
snoc⋯⇒snoc A (brn sn₁ sn₂) ∀¬S (brn (inj₁ E)) = snoc⋯⇒snoc A sn₁ ∀¬S E
snoc⋯⇒snoc A (brn sn₁ sn₂) ∀¬S (brn (inj₂ E)) = snoc⋯⇒snoc A sn₂ ∀¬S E
snoc⋯⇒snoc {a = a} {ϕ = ϕ} A (mu sn) ∀¬S {y = y} (mu E) =
  let ∀¬S′ = λ where zero → ¬skips-`/` Kₛ
                     (suc x) → ∀¬S x ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ x)))
      z′ , sn′ = snoc⋯⇒snoc (atom-⋯ᵣ A) sn ∀¬S′ E
  in snoc-⋯ᵣ⁻¹ weaken-inj A refl (subst (λ w → Snoc (a ⋯ weakenᵣ) w z′) (sym (wk-`/id (ϕ y))) sn′)

data ClosedAtom {n} : 𝕊 n → Set where
  end : ClosedAtom (end {n} p)
  msg : ClosedAtom (msg {n} p T)
  ret : ClosedAtom (ret {n})
  acq : ClosedAtom (acq {n})
  ``- : ∀ {α} → ClosedAtom (``_ {n} α)

closedatom-⋯ᵣ⁻¹ : {ρ : m →ᵣ n} → ClosedAtom (s ⋯ ρ) → ClosedAtom s
closedatom-⋯ᵣ⁻¹ {s = end p} end = end
closedatom-⋯ᵣ⁻¹ {s = msg p t} msg = msg
closedatom-⋯ᵣ⁻¹ {s = ret} ret = ret
closedatom-⋯ᵣ⁻¹ {s = acq} acq = acq
closedatom-⋯ᵣ⁻¹ {s = `` α} ``- = ``-

¬snoc-wk-zero : {α : 𝕊 n} → ¬ Snoc (α ⋯ weakenᵣ) (` zero) z
¬snoc-wk-zero {α = ` x} ()
¬snoc-wk-zero {α = end p} ()
¬snoc-wk-zero {α = msg p t} ()
¬snoc-wk-zero {α = brn p s₁ s₂} ()
¬snoc-wk-zero {α = mu s} ()
¬snoc-wk-zero {α = s₁ ; s₂} ()
¬snoc-wk-zero {α = skip} ()
¬snoc-wk-zero {α = ret} ()
¬snoc-wk-zero {α = acq} ()
¬snoc-wk-zero {α = `` β} ()

------------------------------------------------------------------------
-- EndsKind: "w ends in an atom of kind k" (prefix-free; kind is ≃-invariant)
------------------------------------------------------------------------

kindWk : AtomKind n → AtomKind (suc n)
kindWk (` x) = ` weakenᵣ x
kindWk (end p) = end p
kindWk (msg p) = msg p
kindWk ret = ret
kindWk acq = acq
kindWk (`` α) = `` α

atomKind-wk : (A : Atom s) → atomKind (atom-⋯ᵣ A {weakenᵣ}) ≡ kindWk (atomKind A)
atomKind-wk `- = refl
atomKind-wk end = refl
atomKind-wk msg = refl
atomKind-wk ret = refl
atomKind-wk acq = refl
atomKind-wk ``- = refl

data EndsKind {n} (k : AtomKind n) : 𝕊 n → Set where
  here : {a : 𝕊 n} (A : Atom a) → atomKind A ≡ k → EndsKind k a
  _;₁_ : EndsKind k s₁ → Skips s₂ → EndsKind k (s₁ ; s₂)
  -;₂_ : EndsKind k s₂ → EndsKind k (s₁ ; s₂)
  brn  : EndsKind k s₁ → EndsKind k s₂ → EndsKind k (brn p s₁ s₂)
  mu   : EndsKind (kindWk k) s → EndsKind k (mu s)

¬skips-atom′ : {a : 𝕊 n} → Atom a → ¬ Skips a
¬skips-atom′ = ¬skips-atom

skips⊥endskind : {k : AtomKind n} → Skips s → EndsKind k s → ⊥
skips⊥endskind Sk (here A _) = ¬skips-atom A Sk
skips⊥endskind (Sk₁ ; Sk₂) (e ;₁ _) = skips⊥endskind Sk₁ e
skips⊥endskind (Sk₁ ; Sk₂) (-;₂ e) = skips⊥endskind Sk₂ e
skips⊥endskind (mu Sk) (mu e) = skips⊥endskind Sk e

¬endskind-skip : {k : AtomKind n} → ¬ EndsKind k skip
¬endskind-skip = skips⊥endskind skip

AKvar-inj : {x y : 𝔽 n} → AtomKind.`_ x ≡ ` y → x ≡ y
AKvar-inj refl = refl
AK-end-inj : {p q : Pol} → AtomKind.end {n} p ≡ end q → p ≡ q
AK-end-inj refl = refl
AK-msg-inj : {p q : Pol} → AtomKind.msg {n} p ≡ msg q → p ≡ q
AK-msg-inj refl = refl
AK-uvar-inj : {γ δ : UVar} → AtomKind.``_ {n} γ ≡ `` δ → γ ≡ δ
AK-uvar-inj refl = refl

kindWk-inj : {k₁ k₂ : AtomKind n} → kindWk k₁ ≡ kindWk k₂ → k₁ ≡ k₂
kindWk-inj {k₁ = ` x} {k₂ = ` y} eq = cong `_ (weaken-inj (AKvar-inj eq))
kindWk-inj {k₁ = ` x} {k₂ = end p′} eq = case eq of λ ()
kindWk-inj {k₁ = ` x} {k₂ = msg q′} eq = case eq of λ ()
kindWk-inj {k₁ = ` x} {k₂ = ret} eq = case eq of λ ()
kindWk-inj {k₁ = ` x} {k₂ = acq} eq = case eq of λ ()
kindWk-inj {k₁ = ` x} {k₂ = `` δ} eq = case eq of λ ()
kindWk-inj {k₁ = end p} {k₂ = ` y} eq = case eq of λ ()
kindWk-inj {k₁ = end p} {k₂ = end p′} eq = cong end (AK-end-inj eq)
kindWk-inj {k₁ = end p} {k₂ = msg q′} eq = case eq of λ ()
kindWk-inj {k₁ = end p} {k₂ = ret} eq = case eq of λ ()
kindWk-inj {k₁ = end p} {k₂ = acq} eq = case eq of λ ()
kindWk-inj {k₁ = end p} {k₂ = `` δ} eq = case eq of λ ()
kindWk-inj {k₁ = msg q} {k₂ = ` y} eq = case eq of λ ()
kindWk-inj {k₁ = msg q} {k₂ = end p′} eq = case eq of λ ()
kindWk-inj {k₁ = msg q} {k₂ = msg q′} eq = cong msg (AK-msg-inj eq)
kindWk-inj {k₁ = msg q} {k₂ = ret} eq = case eq of λ ()
kindWk-inj {k₁ = msg q} {k₂ = acq} eq = case eq of λ ()
kindWk-inj {k₁ = msg q} {k₂ = `` δ} eq = case eq of λ ()
kindWk-inj {k₁ = ret} {k₂ = ` y} eq = case eq of λ ()
kindWk-inj {k₁ = ret} {k₂ = end p′} eq = case eq of λ ()
kindWk-inj {k₁ = ret} {k₂ = msg q′} eq = case eq of λ ()
kindWk-inj {k₁ = ret} {k₂ = ret} eq = refl
kindWk-inj {k₁ = ret} {k₂ = acq} eq = case eq of λ ()
kindWk-inj {k₁ = ret} {k₂ = `` δ} eq = case eq of λ ()
kindWk-inj {k₁ = acq} {k₂ = ` y} eq = case eq of λ ()
kindWk-inj {k₁ = acq} {k₂ = end p′} eq = case eq of λ ()
kindWk-inj {k₁ = acq} {k₂ = msg q′} eq = case eq of λ ()
kindWk-inj {k₁ = acq} {k₂ = ret} eq = case eq of λ ()
kindWk-inj {k₁ = acq} {k₂ = acq} eq = refl
kindWk-inj {k₁ = acq} {k₂ = `` δ} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = ` y} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = end p′} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = msg q′} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = ret} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = acq} eq = case eq of λ ()
kindWk-inj {k₁ = `` γ} {k₂ = `` δ} eq = cong ``_ (AK-uvar-inj eq)

BaseH : {m n : ℕ} (ϕ : m →ₛ n) (k : AtomKind m) (k′ : AtomKind n) → Set
BaseH ϕ k k′ = ∀ {a} (A : Atom a) → atomKind A ≡ k → Σ[ A′ ∈ Atom (a ⋯ ϕ) ] atomKind A′ ≡ k′

liftBaseH : {ϕ : m →ₛ n} {k : AtomKind m} {k′ : AtomKind n} → BaseH ϕ k k′ → BaseH (ϕ ↑) (kindWk k) (kindWk k′)
liftBaseH bH (`- {x = x}) p = ?
liftBaseH bH end p = ?
liftBaseH bH msg p = ?
liftBaseH bH ret p = ?
liftBaseH bH acq p = ?
liftBaseH bH ``- p = ?

endskind-⋯ : {ϕ : m →ₛ n} {k : AtomKind m} {k′ : AtomKind n} → BaseH ϕ k k′ → EndsKind k s → EndsKind k′ (s ⋯ ϕ)
endskind-⋯ bH (here A p) = let A′ , p′ = bH A p in here A′ p′
endskind-⋯ bH (e ;₁ Sk) = endskind-⋯ bH e ;₁ skips-⋯ Sk
endskind-⋯ bH (-;₂ e) = -;₂ endskind-⋯ bH e
endskind-⋯ bH (brn e₁ e₂) = brn (endskind-⋯ bH e₁) (endskind-⋯ bH e₂)
endskind-⋯ bH (mu e) = mu (endskind-⋯ (liftBaseH bH) e)

baseUnfold : {k : AtomKind n} → BaseH ⦅ mu s ⦆ₛ (kindWk k) k
baseUnfold {k = ` y} (`- {x = x}) p = ?
baseUnfold {k = end q} (`- {x = x}) ()
baseUnfold {k = msg q} (`- {x = x}) ()
baseUnfold {k = ret} (`- {x = x}) ()
baseUnfold {k = acq} (`- {x = x}) ()
baseUnfold {k = `` γ} (`- {x = x}) ()
baseUnfold end p = end , kindWk-inj p
baseUnfold msg p = msg , kindWk-inj p
baseUnfold ret p = ret , kindWk-inj p
baseUnfold acq p = acq , kindWk-inj p
baseUnfold ``- p = ``- , kindWk-inj p

endskind-unfold : {k : AtomKind n} → EndsKind (kindWk k) s → EndsKind k (unfold s)
endskind-unfold e = endskind-⋯ baseUnfold e

endskind-unfold⁻¹ : {k : AtomKind n} → EndsKind k (unfold s) → EndsKind (kindWk k) s
endskind-unfold⁻¹ = ?

≃-endskind : {k : AtomKind n} → EndsKind k Respects _≃_
≃-endskind refl = id
≃-endskind (x ◅ xs) = ≃-endskind xs ∘ go x where
  go : {k : AtomKind n} → SymClosure _≃𝕊_ s₁ s₂ → EndsKind k s₁ → EndsKind k s₂
  go (fwd ≃𝕊-μ) (mu e) = endskind-unfold e
  go (fwd (≃𝕊-msg x)) (here msg p) = here msg p
  go (bwd (≃𝕊-msg x)) (here msg p) = here msg p
  go (fwd (≃𝕊-;₁ x)) (e ;₁ x₁) = go (fwd x) e ;₁ x₁
  go (fwd (≃𝕊-;₁ x)) (-;₂ e) = -;₂ e
  go (fwd (≃𝕊-;₂ x)) (e ;₁ x₁) = e ;₁ ≃-skips (Eq*.return x) x₁
  go (fwd (≃𝕊-;₂ x)) (-;₂ e) = -;₂ go (fwd x) e
  go (fwd (≃𝕊-brn₁ x)) (brn e e₁) = brn (go (fwd x) e) e₁
  go (fwd (≃𝕊-brn₂ x)) (brn e e₁) = brn e (go (fwd x) e₁)
  go (fwd ≃𝕊-skipˡ) (-;₂ e) = e
  go (fwd ≃𝕊-skipʳ) (e ;₁ x) = e
  go (fwd ≃𝕊-skipˡ) (e ;₁ _) = ⊥-elim (¬endskind-skip e)
  go (fwd ≃𝕊-skipʳ) (-;₂ e) = ⊥-elim (¬endskind-skip e)
  go (fwd ≃𝕊-assoc) ((e ;₁ x₁) ;₁ x) = e ;₁ (x₁ ; x)
  go (fwd ≃𝕊-assoc) ((-;₂ e) ;₁ x) = -;₂ (e ;₁ x)
  go (fwd ≃𝕊-assoc) (-;₂ e) = -;₂ (-;₂ e)
  go (fwd ≃𝕊-distr) (brn e e₁ ;₁ x) = brn (e ;₁ x) (e₁ ;₁ x)
  go (fwd ≃𝕊-distr) (-;₂ e) = brn (-;₂ e) (-;₂ e)
  go (bwd (≃𝕊-;₁ x)) (e ;₁ x₁) = go (bwd x) e ;₁ x₁
  go (bwd (≃𝕊-;₁ x)) (-;₂ e) = -;₂ e
  go (bwd (≃𝕊-;₂ x)) (e ;₁ x₁) = e ;₁ ≃-skips (Star.return (bwd x)) x₁
  go (bwd (≃𝕊-;₂ x)) (-;₂ e) = -;₂ go (bwd x) e
  go (bwd (≃𝕊-brn₁ x)) (brn e e₁) = brn (go (bwd x) e) e₁
  go (bwd (≃𝕊-brn₂ x)) (brn e e₁) = brn e (go (bwd x) e₁)
  go (bwd ≃𝕊-μ) e = mu (endskind-unfold⁻¹ e)
  go (bwd ≃𝕊-skipˡ) e = -;₂ e
  go (bwd ≃𝕊-skipʳ) e = e ;₁ skip
  go (bwd ≃𝕊-assoc) (e ;₁ (x ; x₁)) = (e ;₁ x) ;₁ x₁
  go (bwd ≃𝕊-assoc) (-;₂ (e ;₁ x)) = (-;₂ e) ;₁ x
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ e)) = -;₂ e
  go (bwd ≃𝕊-distr) (brn (e ;₁ x) (e₁ ;₁ x₁)) = brn e e₁ ;₁ x₁
  go (bwd ≃𝕊-distr) (brn (e ;₁ x) (-;₂ e₁)) = -;₂ e₁
  go (bwd ≃𝕊-distr) (brn (-;₂ e) e₁) = -;₂ e
