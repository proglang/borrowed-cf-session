-- | FRONT-atom peel: the mirror image of `AtomSnoc`/`AtomUnsnoc`, which do
--   the LAST atom of a chain.
--
--   `Cons a w z` is a structural witness that `w ≃ a ; z` ("w starts with the
--   atom a").  Unlike `Snoc` it has NO `brn` constructor, and that is not an
--   omission: `_;_` distributes over `brn` only on the RIGHT
--   (`≃𝕊-distr : brn p s₁ s₂ ; s ≃𝕊 brn p (s₁ ; s) (s₂ ; s)`), so an atom
--   never sits in front of a `brn` and `Cons a (brn ⋯) z` is uninhabited for
--   atomic `a`.  The whole `distr`/`brn` half of `≃-snoc`'s transport
--   therefore collapses into refutations, and with it the `SnocA`/`SnocM`/
--   `snoc-⋯-sum` apparatus of `AtomUnsnoc`: the only real work left is the
--   backward μ step, the exact mirror of `snoc-unfold⁻¹`.
--
--   The payoff is `atom-;-cons`, dual to `Equivalence.atom-;-unsnoc`: from
--   `x ; y ≃ a ; t` with `a` a closed non-`msg` atom, EITHER `x` skips and the
--   atom is at the front of `y`, OR `x ≃ a ; h` and `h ; y ≃ t`.  That is what
--   pins a group's `acq` to the front of one handle of a `BindCtx` chain.
module BorrowedCF.Types.AtomCons where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomSnoc
open import BorrowedCF.Types.AtomUnsnoc
  using (closedatom-atom; closedatom-≢var; closedatom-⋯ᶜ; closed-⋯-inj; wk-avar)

open Bin
open Nat.Variables

private variable
  w z z₁ z₂ z′ : 𝕊 n

------------------------------------------------------------------------
-- Cons a w z  :  structural witness that  w ≃ a ; z
------------------------------------------------------------------------

data Cons {n} (a : 𝕊 n) : 𝕊 n → 𝕊 n → Set where
  here : Cons a a skip
  hd   : Cons a s₁ z → Cons a (s₁ ; s₂) (z ; s₂)
  tl   : Skips s₁ → Cons a s₂ z → Cons a (s₁ ; s₂) z
  mu   : Cons (a ⋯ weakenᵣ) s z → Cons a (mu s) (z ⋯ ⦅ mu s ⦆ₛ)

cons-sound : {a : 𝕊 n} → Cons a w z → w ≃ a ; z
cons-sound here = ≃-sym ≃-skipʳ
cons-sound (hd c) = ≃-trans (≃-; (cons-sound c) ≃-refl) ≃-assoc-;
cons-sound (tl Sk c) = ≃-trans (≃-skipsˡ Sk) (cons-sound c)
cons-sound {a = a} (mu {s = s} {z = z} c) =
  ≃-trans ≃-μ
    (subst (λ t → s ⋯ ⦅ mu s ⦆ₛ ≃ t ; (z ⋯ ⦅ mu s ⦆ₛ))
           (wk-cancels-⦅⦆-⋯ a (mu s))
           (≃-⋯ (cons-sound c)))

------------------------------------------------------------------------
-- Inversions and refutations
------------------------------------------------------------------------

skips⊥cons : {a : 𝕊 n} → Atom a → Skips w → Cons a w z → ⊥
skips⊥cons A Sk here = ¬skips-atom A Sk
skips⊥cons A (Sk₁ ; Sk₂) (hd c) = skips⊥cons A Sk₁ c
skips⊥cons A (Sk₁ ; Sk₂) (tl _ c) = skips⊥cons A Sk₂ c
skips⊥cons A (mu Sk) (mu c) = skips⊥cons (atom-⋯ᵣ A) Sk c

cons-mu⁻ : {a : 𝕊 n} → Atom a → Cons a (mu s) z → ∃[ z′ ] Cons (a ⋯ weakenᵣ) s z′
cons-mu⁻ A (mu c) = _ , c
cons-mu⁻ A here = case A of λ ()

cons-;⁻ : {a : 𝕊 n} → Atom a → Cons a (s₁ ; s₂) z →
  (∃[ z′ ] Cons a s₁ z′) ⊎ (Skips s₁ × ∃[ z′ ] Cons a s₂ z′)
cons-;⁻ A (hd c) = inj₁ (_ , c)
cons-;⁻ A (tl Sk c) = inj₂ (Sk , _ , c)
cons-;⁻ A here = case A of λ ()

-- An atom in front of a `brn` is impossible: `_;_` distributes only rightwards.
¬cons-brn : {a : 𝕊 n} → Atom a → ¬ Cons a (brn p s₁ s₂) z
¬cons-brn A here = case A of λ ()

-- ... and a `w` that IS an atom must be the atom itself.
cons-atom⁻ : {a b : 𝕊 n} → Atom b → Cons a b z → b ≡ a
cons-atom⁻ B here = refl
cons-atom⁻ B (hd _) = case B of λ ()
cons-atom⁻ B (tl _ _) = case B of λ ()
cons-atom⁻ B (mu _) = case B of λ ()

¬cons-closed-var : {a : 𝕊 n}{x : 𝔽 n} → ClosedAtom a → ¬ Cons a (` x) z
¬cons-closed-var ca here = case ca of λ ()

¬cons-wk-zero : {α : 𝕊 n} → ¬ Cons (α ⋯ᵣ weakenᵣ) (` zero) z
¬cons-wk-zero {α = ` x} ()
¬cons-wk-zero {α = end p} ()
¬cons-wk-zero {α = msg p t} ()
¬cons-wk-zero {α = brn p s₁ s₂} ()
¬cons-wk-zero {α = mu s} ()
¬cons-wk-zero {α = s₁ ; s₂} ()
¬cons-wk-zero {α = skip} ()
¬cons-wk-zero {α = ret} ()
¬cons-wk-zero {α = acq} ()
¬cons-wk-zero {α = `` β} ()

-- The suffix is determined up to `≃` (the mirror of `snoc-prefix-unique`).
cons-suffix-unique : {a : 𝕊 n} → Atom a → Cons a w z₁ → Cons a w z₂ → z₁ ≃ z₂
cons-suffix-unique A here here = ≃-refl
cons-suffix-unique A here (hd _) = case A of λ ()
cons-suffix-unique A here (tl _ _) = case A of λ ()
cons-suffix-unique A here (mu _) = case A of λ ()
cons-suffix-unique A (hd _) here = case A of λ ()
cons-suffix-unique A (tl _ _) here = case A of λ ()
cons-suffix-unique A (mu _) here = case A of λ ()
cons-suffix-unique A (hd c₁) (hd c₂) = ≃-; (cons-suffix-unique A c₁ c₂) ≃-refl
cons-suffix-unique A (hd c₁) (tl Sk c₂) = ⊥-elim (skips⊥cons A Sk c₁)
cons-suffix-unique A (tl Sk c₁) (hd c₂) = ⊥-elim (skips⊥cons A Sk c₂)
cons-suffix-unique A (tl _ c₁) (tl _ c₂) = cons-suffix-unique A c₁ c₂
cons-suffix-unique A (mu {s = s} c₁) (mu c₂) =
  ≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (cons-suffix-unique (atom-⋯ᵣ A) c₁ c₂)

------------------------------------------------------------------------
-- Substitution;  the forward direction of the μ step
------------------------------------------------------------------------

cons-⋯ : {a : 𝕊 m} {ϕ : m →ₛ n} → Cons a w z → Cons (a ⋯ ϕ) (w ⋯ ϕ) (z ⋯ ϕ)
cons-⋯ here = here
cons-⋯ (hd c) = hd (cons-⋯ c)
cons-⋯ (tl Sk c) = tl (skips-⋯ Sk) (cons-⋯ c)
cons-⋯ {a = a} {ϕ = ϕ} (mu {s = s} {z = z} c) =
  subst (Cons (a ⋯ ϕ) (mu (s ⋯ ϕ ↑)))
    (sym (dist-↑-⦅⦆-⋯ z (mu s) ϕ))
    (mu (subst (λ t → Cons t (s ⋯ ϕ ↑) (z ⋯ ϕ ↑)) (sym (⋯-↑-wk a ϕ)) (cons-⋯ {ϕ = ϕ ↑} c)))

cons-unfold : {a : 𝕊 n} → Atom a → Cons a (mu s) z → Cons a (unfold s) z
cons-unfold {a = a} A (mu {s = s} {z = z} c) =
  subst (λ t → Cons t (unfold s) (z ⋯ ⦅ mu s ⦆ₛ)) (wk-cancels-⦅⦆-⋯ a (mu s)) (cons-⋯ c)
cons-unfold A here = case A of λ ()

------------------------------------------------------------------------
-- StartsVar x s : some branch of `s` begins with the variable `x`.
-- (The mirror of `EndsIn-` `, and the callback index of the μ un-substitution.)
------------------------------------------------------------------------

data StartsVar {n} (x : 𝔽 n) : 𝕊 n → Set where
  here : StartsVar x (` x)
  hd   : StartsVar x s₁ → StartsVar x (s₁ ; s₂)
  tl   : Skips s₁ → StartsVar x s₂ → StartsVar x (s₁ ; s₂)
  mu   : StartsVar (suc x) s → StartsVar x (mu s)

skips⊥startsVar : {x : 𝔽 n} → Skips s → StartsVar x s → ⊥
skips⊥startsVar (Sk₁ ; Sk₂) (hd E) = skips⊥startsVar Sk₁ E
skips⊥startsVar (Sk₁ ; Sk₂) (tl _ E) = skips⊥startsVar Sk₂ E
skips⊥startsVar (mu Sk) (mu E) = skips⊥startsVar Sk E

------------------------------------------------------------------------
-- Backward μ un-substitution (the mirror of `snoc-⋯ᵣ⁻¹`/`snoc-⋯⁻¹`)
------------------------------------------------------------------------

cons-⋯ᵣ⁻¹ : {α : 𝕊 n} {a′ : 𝕊 m} {ρ : m →ᵣ n} → (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  Atom a′ → α ≡ a′ ⋯ ρ → Cons α (s ⋯ ρ) z → ∃[ z₀ ] Cons a′ s z₀
cons-⋯ᵣ⁻¹ {s = ` x} inj (`- {x = x′}) eq here =
  _ , subst (λ w → Cons (` x′) w skip) (cong `_ (sym (inj (`-injective eq)))) here
cons-⋯ᵣ⁻¹ {s = end p} inj end refl here = _ , here
cons-⋯ᵣ⁻¹ {s = msg p t} inj msg refl here = _ , here
cons-⋯ᵣ⁻¹ {s = ret} inj ret refl here = _ , here
cons-⋯ᵣ⁻¹ {s = acq} inj acq refl here = _ , here
cons-⋯ᵣ⁻¹ {s = `` β} inj ``- refl here = _ , here
cons-⋯ᵣ⁻¹ {s = skip} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
cons-⋯ᵣ⁻¹ {s = brn p s₁ s₂} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
cons-⋯ᵣ⁻¹ {s = mu s} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
cons-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq here = ⊥-elim (case subst Atom (sym eq) (atom-⋯ᵣ A) of λ ())
cons-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq (hd c) = _ , hd (proj₂ (cons-⋯ᵣ⁻¹ inj A eq c))
cons-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj A eq (tl Sk c) =
  _ , tl (skips-⋯ᵣ⁻¹ Sk) (proj₂ (cons-⋯ᵣ⁻¹ inj A eq c))
cons-⋯ᵣ⁻¹ {s = mu s₀} {a′ = a′} {ρ = ρ} inj A eq (mu c) =
  _ , mu (proj₂ (cons-⋯ᵣ⁻¹ (↑ᵣ-inj inj) (atom-⋯ᵣ A) (cong (_⋯ weakenᵣ) eq ■ ⋯-↑-wk a′ ρ) c))

-- If `s ⋯ ϕ` starts with the atom `a` and `s` starts with the variable `y`,
-- then the image of `y` starts with `a`.
cons⋯⇒cons : {a : 𝕊 n} {ϕ : m →ₛ n} → Atom a → Cons a (s ⋯ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) → ∀ {y} → StartsVar y s → ∃[ z′ ] Cons a (`/id (ϕ y)) z′
cons⋯⇒cons A c ∀¬S here = _ , c
cons⋯⇒cons A (hd c) ∀¬S (hd E) = cons⋯⇒cons A c ∀¬S E
cons⋯⇒cons A (tl Sk c) ∀¬S (hd E) = ⊥-elim (skips⊥startsVar (skips-⋯⁻¹ Sk ∀¬S) E)
cons⋯⇒cons A (hd c) ∀¬S (tl Sk E) = ⊥-elim (skips⊥cons A (skips-⋯ Sk) c)
cons⋯⇒cons A (tl _ c) ∀¬S (tl _ E) = cons⋯⇒cons A c ∀¬S E
cons⋯⇒cons {a = a} {ϕ = ϕ} A (mu c) ∀¬S {y = y} (mu E) =
  let ∀¬S′ = λ where zero → ¬skips-`/` Kₛ
                     (suc x) → ∀¬S x ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ x)))
      z′ , c′ = cons⋯⇒cons (atom-⋯ᵣ A) c ∀¬S′ E
  in cons-⋯ᵣ⁻¹ weaken-inj A refl (subst (λ w → Cons (a ⋯ weakenᵣ) w z′) (sym (wk-`/id (ϕ y))) c′)

-- Pull a closed leaf atom back through ϕ (the `Cons` form of
-- `AtomUnsnoc.pullClosed`).
pullClosed≡ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {a c : 𝕊 m}{ϕ : m –[ K ]→ n} →
  Atom a → ClosedAtom c → (∀ x → a ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  a ⋯ ϕ ≡ c ⋯ ϕ → a ≡ c
pullClosed≡ (`- {x = x}) cc avar eqϕ with avar x refl
... | y , ϕx≡ = ⊥-elim (closedatom-≢var (closedatom-⋯ᶜ cc) (sym eqϕ ■ ϕx≡))
pullClosed≡ end cc avar eqϕ = closed-⋯-inj end cc eqϕ
pullClosed≡ msg cc avar eqϕ = closed-⋯-inj msg cc eqϕ
pullClosed≡ ret cc avar eqϕ = closed-⋯-inj ret cc eqϕ
pullClosed≡ acq cc avar eqϕ = closed-⋯-inj acq cc eqϕ
pullClosed≡ ``- cc avar eqϕ = closed-⋯-inj ``- cc eqϕ

pullClosedC : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {a c : 𝕊 m}{ϕ : m –[ K ]→ n} →
  Atom a → ClosedAtom c → (∀ x → a ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  a ⋯ ϕ ≡ c ⋯ ϕ → Cons a c skip
pullClosedC {a = a} A cc avar eq = subst (λ t → Cons a t skip) (pullClosed≡ A cc avar eq) here

cons-⋯⁻¹ : {α : 𝕊 n}{a′ : 𝕊 m}{ϕ : m →ₛ n} →
  Atom α → Atom a′ → α ≡ a′ ⋯ ϕ → (∀ x → a′ ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  Cons α (s ⋯ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) →
  (∀ y → StartsVar y s → ∃[ z′ ] Cons a′ s z′) →
  ∃[ z′ ] Cons a′ s z′
cons-⋯⁻¹ {s = ` x} Aα A eq avar c ∀¬S ∀¬E = ∀¬E x here
cons-⋯⁻¹ {s = end q} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosedC A end avar (sym eq)
cons-⋯⁻¹ {s = msg q T} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosedC A msg avar (sym eq)
cons-⋯⁻¹ {s = ret} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosedC A ret avar (sym eq)
cons-⋯⁻¹ {s = acq} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosedC A acq avar (sym eq)
cons-⋯⁻¹ {s = `` β} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosedC A ``- avar (sym eq)
cons-⋯⁻¹ {s = skip} Aα A eq avar here ∀¬S ∀¬E = case Aα of λ ()
cons-⋯⁻¹ {s = brn p s₁ s₂} Aα A eq avar here ∀¬S ∀¬E = case Aα of λ ()
cons-⋯⁻¹ {s = mu s₀} Aα A eq avar here ∀¬S ∀¬E = case Aα of λ ()
cons-⋯⁻¹ {s = s₁ ; s₂} Aα A eq avar here ∀¬S ∀¬E = case Aα of λ ()
cons-⋯⁻¹ {s = s₁ ; s₂} Aα A eq avar (hd c) ∀¬S ∀¬E =
  Π.map (λ w → w ; s₂) hd (cons-⋯⁻¹ Aα A eq avar c ∀¬S
    (λ y E → Sum.[ (λ (z′ , c₀) → z′ , c₀)
                 , (λ (Sk , _) → ⊥-elim (skips⊥cons Aα (skips-⋯ Sk) c)) ]
             (cons-;⁻ A (proj₂ (∀¬E y (hd E))))))
cons-⋯⁻¹ {s = s₁ ; s₂} Aα A eq avar (tl Sk c) ∀¬S ∀¬E =
  let Sk′ = skips-⋯⁻¹ Sk ∀¬S in
  Π.map₂ (tl Sk′) (cons-⋯⁻¹ Aα A eq avar c ∀¬S
    (λ y E → Sum.[ (λ (_ , c₀) → ⊥-elim (skips⊥cons A Sk′ c₀))
                 , (λ (_ , z′ , c₀) → z′ , c₀) ]
             (cons-;⁻ A (proj₂ (∀¬E y (tl Sk′ E))))))
cons-⋯⁻¹ {s = mu s₀} {α = α}{a′ = a′}{ϕ = ϕ} Aα A eq avar (mu c) ∀¬S ∀¬E =
  Π.map (_⋯ ⦅ mu s₀ ⦆ₛ) mu (cons-⋯⁻¹ (atom-⋯ᵣ Aα) (atom-⋯ᵣ A) eq′ avar′ c ∀¬S′ cb)
  where
  ∀¬S′ : ∀ z → ¬ Skips (`/id ((ϕ ↑) z))
  ∀¬S′ zero = ¬skips-`/` Kₛ
  ∀¬S′ (suc z) = ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ z)))
  eq′ : α ⋯ weakenᵣ ≡ (a′ ⋯ weakenᵣ) ⋯ (ϕ ↑)
  eq′ = cong (_⋯ weakenᵣ) eq ■ ⋯-↑-wk a′ ϕ
  avar′ : ∀ x → a′ ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id ((ϕ ↑) x) ≡ ` y
  avar′ = wk-avar A avar
  cb : ∀ z → StartsVar z s₀ → ∃[ z′ ] Cons (a′ ⋯ weakenᵣ) s₀ z′
  cb zero    E = let z′ , c0 = cons⋯⇒cons {ϕ = ϕ ↑} (atom-⋯ᵣ Aα) c ∀¬S′ E
                 in ⊥-elim (¬cons-wk-zero {α = α} (subst (λ w → Cons (α ⋯ weakenᵣ) w z′) (`/`-is-` ⦃ Kₛ ⦄ zero) c0))
  cb (suc z) E = cons-mu⁻ A (proj₂ (∀¬E z (mu E)))

cons-unfold⁻¹ : {a : 𝕊 n} → ClosedAtom a → Cons a (unfold s) z → ∃[ z′ ] Cons a (mu s) z′
cons-unfold⁻¹ {s = s} {a = a} ca c with skips? s
... | yes Ss = ⊥-elim (skips⊥cons (closedatom-atom ca) (skips-⋯ Ss) c)
... | no ¬Ss = Π.map (_⋯ ⦅ mu s ⦆ₛ) mu
    (cons-⋯⁻¹ (closedatom-atom ca) (atom-⋯ᵣ (closedatom-atom ca))
       (sym (wk-cancels-⦅⦆-⋯ _ (mu s))) avμ c ¬Sμ cb)
  where
  A = closedatom-atom ca
  ¬Sμ : ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
  ¬Sμ zero (mu Ss′) = ¬Ss Ss′
  ¬Sμ (suc x) = ¬skips-`
  avμ : ∀ x → a ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id (⦅ mu s ⦆ₛ x) ≡ ` y
  avμ x eqx = ⊥-elim (closedatom-≢var (closedatom-⋯ᶜ ca) eqx)
  cb : ∀ y → StartsVar y s → ∃[ z′ ] Cons (a ⋯ weakenᵣ) s z′
  cb zero    E = cons-mu⁻ A (proj₂ (cons⋯⇒cons A c ¬Sμ E))
  cb (suc x) E = ⊥-elim (¬cons-closed-var ca (proj₂ (cons⋯⇒cons A c ¬Sμ E)))

------------------------------------------------------------------------
-- `≃` transports Cons, suffix preserved up to `≃`
------------------------------------------------------------------------

ConsR : {n : ℕ} → 𝕊 n → 𝕊 n → 𝕊 n → Set
ConsR {n} a w₂ z = ∃[ z₂ ] Cons a w₂ z₂ × z ≃ z₂

≃-cons : {a : 𝕊 n} → ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  {w₁ w₂ : 𝕊 n} → w₁ ≃ w₂ → Cons a w₁ z → ConsR a w₂ z
≃-cons ca nm refl c = _ , c , ≃-refl
≃-cons {a = a} ca nm (x ◅ xs) c =
  let z₂ , c₂ , e = go x c in
  let z₃ , c₃ , e′ = ≃-cons ca nm xs c₂ in
  z₃ , c₃ , ≃-trans e e′
  where
  A = closedatom-atom ca
  go : {w₁ w₂ : 𝕊 _} → SymClosure _≃𝕊_ w₁ w₂ → Cons a w₁ z → ConsR a w₂ z
  go (fwd (≃𝕊-msg x)) here = ⊥-elim (nm refl)
  go (bwd (≃𝕊-msg x)) here = ⊥-elim (nm refl)
  go (fwd ≃𝕊-μ) c = _ , cons-unfold A c , ≃-refl
  go (bwd ≃𝕊-μ) c = let z₂ , c₂ = cons-unfold⁻¹ ca c
                    in z₂ , c₂ , cons-suffix-unique A c (cons-unfold A c₂)
  go (fwd (≃𝕊-;₁ x)) (hd c) = let z₂ , c₂ , e = go (fwd x) c in _ , hd c₂ , ≃-; e ≃-refl
  go (fwd (≃𝕊-;₁ x)) (tl Sk c) = _ , tl (≃-skips (Eq*.return x) Sk) c , ≃-refl
  go (bwd (≃𝕊-;₁ x)) (hd c) = let z₂ , c₂ , e = go (bwd x) c in _ , hd c₂ , ≃-; e ≃-refl
  go (bwd (≃𝕊-;₁ x)) (tl Sk c) = _ , tl (≃-skips (≃-sym (Eq*.return x)) Sk) c , ≃-refl
  go (fwd (≃𝕊-;₂ x)) (hd c) = _ , hd c , ≃-; ≃-refl (Eq*.return x)
  go (fwd (≃𝕊-;₂ x)) (tl Sk c) = let z₂ , c₂ , e = go (fwd x) c in _ , tl Sk c₂ , e
  go (bwd (≃𝕊-;₂ x)) (hd c) = _ , hd c , ≃-; ≃-refl (≃-sym (Eq*.return x))
  go (bwd (≃𝕊-;₂ x)) (tl Sk c) = let z₂ , c₂ , e = go (bwd x) c in _ , tl Sk c₂ , e
  go (fwd ≃𝕊-skipˡ) (hd c) = ⊥-elim (skips⊥cons A skip c)
  go (fwd ≃𝕊-skipˡ) (tl _ c) = _ , c , ≃-refl
  go (bwd ≃𝕊-skipˡ) c = _ , tl skip c , ≃-refl
  go (fwd ≃𝕊-skipʳ) (hd c) = _ , c , ≃-skipʳ
  go (fwd ≃𝕊-skipʳ) (tl _ c) = ⊥-elim (skips⊥cons A skip c)
  go (bwd ≃𝕊-skipʳ) c = _ , hd c , ≃-sym ≃-skipʳ
  go (fwd ≃𝕊-assoc) (hd (hd c)) = _ , hd c , ≃-assoc-;
  go (fwd ≃𝕊-assoc) (hd (tl Sk c)) = _ , tl Sk (hd c) , ≃-refl
  go (fwd ≃𝕊-assoc) (tl (Sk₁ ; Sk₂) c) = _ , tl Sk₁ (tl Sk₂ c) , ≃-refl
  go (bwd ≃𝕊-assoc) (hd c) = _ , hd (hd c) , ≃-sym ≃-assoc-;
  go (bwd ≃𝕊-assoc) (tl Sk (hd c)) = _ , hd (tl Sk c) , ≃-refl
  go (bwd ≃𝕊-assoc) (tl Sk₁ (tl Sk₂ c)) = _ , tl (Sk₁ ; Sk₂) c , ≃-refl
  go (fwd ≃𝕊-distr) (hd c) = ⊥-elim (¬cons-brn A c)
  go (fwd ≃𝕊-distr) (tl () _)
  go (fwd (≃𝕊-brn₁ x)) c = ⊥-elim (¬cons-brn A c)
  go (fwd (≃𝕊-brn₂ x)) c = ⊥-elim (¬cons-brn A c)
  go (bwd ≃𝕊-distr) c = ⊥-elim (¬cons-brn A c)
  go (bwd (≃𝕊-brn₁ x)) c = ⊥-elim (¬cons-brn A c)
  go (bwd (≃𝕊-brn₂ x)) c = ⊥-elim (¬cons-brn A c)

------------------------------------------------------------------------
-- THE PAYOFF: the front-atom split, dual to `atom-;-unsnoc`.
------------------------------------------------------------------------

atom-;-cons : {a : 𝕊 n} → ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  {x y t : 𝕊 n} → x ; y ≃ a ; t →
  (Skips x × (y ≃ a ; t)) ⊎ (∃[ h ] (x ≃ a ; h) × (h ; y ≃ t))
atom-;-cons {a = a} ca nm {x}{y}{t} eq
  with z₂ , c , skt≃z₂ ← ≃-cons ca nm (≃-sym eq) (hd here)
  with c
... | here = case ca of λ ()
... | hd c₁ =
  inj₂ (_ , cons-sound c₁ , ≃-trans (≃-sym skt≃z₂) ≃-skipˡ)
... | tl Sk c₂ =
  inj₁ (Sk , ≃-trans (cons-sound c₂)
               (≃-; ≃-refl (≃-sym (≃-trans (≃-sym ≃-skipˡ) skt≃z₂))))

-- A session that starts with a closed atom is not a skip, and is not `≃` to a
-- DIFFERENT atom.
atom-;-¬skips : {a : 𝕊 n} → ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  {t : 𝕊 n} → Skips s → ¬ (s ≃ a ; t)
atom-;-¬skips ca nm Sk eq =
  let _ , c , _ = ≃-cons ca nm (≃-sym eq) (hd here) in
  skips⊥cons (closedatom-atom ca) Sk c

atom-;-atom : {a b : 𝕊 n} → ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  Atom b → {t : 𝕊 n} → b ≃ a ; t → b ≡ a
atom-;-atom ca nm B eq =
  let _ , c , _ = ≃-cons ca nm (≃-sym eq) (hd here) in cons-atom⁻ B c

------------------------------------------------------------------------
-- The `acq` instance, packaged so that clients need neither `ClosedAtom`
-- nor `Atom` in scope (their constructor names clash with the session
-- constructors `ret`/`acq` themselves).
------------------------------------------------------------------------

acq-;-split : {x y t : 𝕊 n} → x ; y ≃ acq ; t →
  (Skips x × (y ≃ acq ; t)) ⊎ (∃[ h ] (x ≃ acq ; h) × (h ; y ≃ t))
acq-;-split = atom-;-cons acq (λ ())

acq-;-¬skips : {x t : 𝕊 n} → Skips x → ¬ (x ≃ acq ; t)
acq-;-¬skips = atom-;-¬skips acq (λ ())

acq-;-≄ret : {t : 𝕊 n} → ¬ (ret ≃ acq ; t)
acq-;-≄ret eq = case atom-;-atom acq (λ ()) ret eq of λ ()

acq-;-≄end : {t : 𝕊 n} → ¬ (end p ≃ acq ; t)
acq-;-≄end eq = case atom-;-atom acq (λ ()) end eq of λ ()

acq-;-≄msg : {t : 𝕊 n} → ¬ (msg p T ≃ acq ; t)
acq-;-≄msg eq = case atom-;-atom acq (λ ()) msg eq of λ ()

-- An atom never sits in FRONT of a `brn`: `_;_` distributes over `brn` only
-- on the right, so `select` / `branch` handles are never acq-headed.
acq-;-¬brn : {t : 𝕊 n} → ¬ (brn p s₁ s₂ ≃ acq ; t)
acq-;-¬brn eq =
  let _ , c , _ = ≃-cons acq (λ ()) (≃-sym eq) (hd here) in ¬cons-brn acq c
