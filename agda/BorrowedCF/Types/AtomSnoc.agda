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
