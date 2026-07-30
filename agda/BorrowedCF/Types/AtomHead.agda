module BorrowedCF.Types.AtomHead where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomSnoc

open Bin
open Nat.Variables

private variable
  x : 𝔽 n

------------------------------------------------------------------------
-- StartsKind: "w starts with an atom of kind k" (skip-transparent prefix)
------------------------------------------------------------------------

data StartsKind {n} (k : AtomKind n) : 𝕊 n → Set where
  here : {a : 𝕊 n} (A : Atom a) → atomKind A ≡ k → StartsKind k a
  _◂_  : Skips s₁ → StartsKind k s₂ → StartsKind k (s₁ ; s₂)
  ▸_   : StartsKind k s₁ → StartsKind k (s₁ ; s₂)
  mu   : StartsKind (kindWk k) s → StartsKind k (mu s)

infixr 4 _◂_
infix 5 ▸_

data StartsVar {n} (x : 𝔽 n) : 𝕊 n → Set where
  here : StartsVar x (` x)
  _◂_  : Skips s₁ → StartsVar x s₂ → StartsVar x (s₁ ; s₂)
  ▸_   : StartsVar x s₁ → StartsVar x (s₁ ; s₂)
  mu   : StartsVar (weakenᵣ x) s → StartsVar x (mu s)

------------------------------------------------------------------------
-- basic lemmas
------------------------------------------------------------------------

¬startskind-brn : {k : AtomKind n} {p : Pol} {s₁ s₂ : 𝕊 n} → ¬ StartsKind k (brn p s₁ s₂)
¬startskind-brn (here () _)

skips⊥startskind : {k : AtomKind n} → Skips s → StartsKind k s → ⊥
skips⊥startskind Sk (here A _) = ¬skips-atom A Sk
skips⊥startskind (Sk₁ ; Sk₂) (Sk ◂ e) = skips⊥startskind Sk₂ e
skips⊥startskind (Sk₁ ; Sk₂) (▸ e) = skips⊥startskind Sk₁ e
skips⊥startskind (mu Sk) (mu e) = skips⊥startskind Sk e

¬startskind-skip : {k : AtomKind n} → ¬ StartsKind k skip
¬startskind-skip = skips⊥startskind skip

skips⊥startsvar : Skips s → StartsVar x s → ⊥
skips⊥startsvar () here
skips⊥startsvar (Sk₁ ; Sk₂) (Sk ◂ E) = skips⊥startsvar Sk₂ E
skips⊥startsvar (Sk₁ ; Sk₂) (▸ E) = skips⊥startsvar Sk₁ E
skips⊥startsvar (mu Sk) (mu E) = skips⊥startsvar Sk E

startskind-atom-kind : {a : 𝕊 n} {k : AtomKind n} (A : Atom a) → StartsKind k a → atomKind A ≡ k
startskind-atom-kind A (here A′ p) = atomKind≡ A A′ ■ p

startskind-;⁻ : {k : AtomKind n} → StartsKind k (s₁ ; s₂) → (Skips s₁ × StartsKind k s₂) ⊎ StartsKind k s₁
startskind-;⁻ (Sk ◂ e) = inj₁ (Sk , e)
startskind-;⁻ (▸ e) = inj₂ e

startskind-mu⁻ : {k : AtomKind n} → StartsKind k (mu s) → StartsKind (kindWk k) s
startskind-mu⁻ (mu e) = e

------------------------------------------------------------------------
-- StartsKind respects substitution (forward)
------------------------------------------------------------------------

startskind-⋯ : {ϕ : m →ₛ n} {k : AtomKind m} {k′ : AtomKind n} → BaseH ϕ k k′ → StartsKind k s → StartsKind k′ (s ⋯ ϕ)
startskind-⋯ bH (here A p) = let A′ , p′ = bH A p in here A′ p′
startskind-⋯ bH (Sk ◂ e) = skips-⋯ Sk ◂ startskind-⋯ bH e
startskind-⋯ bH (▸ e) = ▸ startskind-⋯ bH e
startskind-⋯ bH (mu e) = mu (startskind-⋯ (liftBaseH bH) e)

------------------------------------------------------------------------
-- StartsKind respects renaming (backward, structural)
------------------------------------------------------------------------

startskind-⋯ᵣ⁻¹ : {k : AtomKind m} {ρ : m →ᵣ n} → (∀ {x y} → ρ x ≡ ρ y → x ≡ y) → StartsKind (kindMapᵣ ρ k) (s ⋯ ρ) → StartsKind k s
startskind-⋯ᵣ⁻¹ {s = ` x} {k = ` y} inj (here `- pr) = here `- (cong `_ (inj (AKvar-inj pr)))
startskind-⋯ᵣ⁻¹ {s = ` x} {k = end p′} inj (here `- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ` x} {k = msg q′} inj (here `- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ` x} {k = ret} inj (here `- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ` x} {k = acq} inj (here `- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ` x} {k = `` δ} inj (here `- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = end p} {k = ` y} inj (here end pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = end p} {k = end p′} inj (here end pr) = here end (cong end (AK-end-inj pr))
startskind-⋯ᵣ⁻¹ {s = end p} {k = msg q′} inj (here end pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = end p} {k = ret} inj (here end pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = end p} {k = acq} inj (here end pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = end p} {k = `` δ} inj (here end pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = ` y} inj (here msg pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = end p′} inj (here msg pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = msg q′} inj (here msg pr) = here msg (cong msg (AK-msg-inj pr))
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = ret} inj (here msg pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = acq} inj (here msg pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = msg q T} {k = `` δ} inj (here msg pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ret} {k = ` y} inj (here ret pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ret} {k = end p′} inj (here ret pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ret} {k = msg q′} inj (here ret pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ret} {k = ret} inj (here ret pr) = here ret (refl)
startskind-⋯ᵣ⁻¹ {s = ret} {k = acq} inj (here ret pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = ret} {k = `` δ} inj (here ret pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = acq} {k = ` y} inj (here acq pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = acq} {k = end p′} inj (here acq pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = acq} {k = msg q′} inj (here acq pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = acq} {k = ret} inj (here acq pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = acq} {k = acq} inj (here acq pr) = here acq (refl)
startskind-⋯ᵣ⁻¹ {s = acq} {k = `` δ} inj (here acq pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = ` y} inj (here ``- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = end p′} inj (here ``- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = msg q′} inj (here ``- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = ret} inj (here ``- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = acq} inj (here ``- pr) = case pr of λ ()
startskind-⋯ᵣ⁻¹ {s = `` γ} {k = `` δ} inj (here ``- pr) = here ``- (cong ``_ (AK-uvar-inj pr))
startskind-⋯ᵣ⁻¹ {s = skip} inj e = ⊥-elim (skips⊥startskind skip e)
startskind-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj (Sk ◂ e) = skips-⋯ᵣ⁻¹ Sk ◂ startskind-⋯ᵣ⁻¹ inj e
startskind-⋯ᵣ⁻¹ {s = s₁ ; s₂} inj (▸ e) = ▸ startskind-⋯ᵣ⁻¹ inj e
startskind-⋯ᵣ⁻¹ {s = brn p s₁ s₂} inj e = ⊥-elim (¬startskind-brn e)
startskind-⋯ᵣ⁻¹ {s = mu s₀} {k = k} {ρ = ρ} inj (mu e) = mu (startskind-⋯ᵣ⁻¹ (↑ᵣ-inj inj) (subst (λ κ → StartsKind κ (s₀ ⋯ ρ ↑)) (sym (kindMapᵣ-↑ ρ k)) e))

------------------------------------------------------------------------
-- pulling a leading kind through a substitution's variable image
------------------------------------------------------------------------

startskind⋯⇒kind : {k′ : AtomKind n} {ϕ : m →ₛ n} → StartsKind k′ (s ⋯ ϕ) →
  (∀ x → ¬ Skips (`/id (ϕ x))) → ∀ {y} → StartsVar y s → StartsKind k′ (`/id (ϕ y))
startskind⋯⇒kind e ∀¬S here = e
startskind⋯⇒kind (▸ e) ∀¬S (▸ E) = startskind⋯⇒kind e ∀¬S E
startskind⋯⇒kind (▸ e) ∀¬S (Sk ◂ E) = ⊥-elim (skips⊥startskind (skips-⋯ Sk) e)
startskind⋯⇒kind (Sk ◂ e) ∀¬S (▸ E) = ⊥-elim (skips⊥startsvar (skips-⋯⁻¹ Sk ∀¬S) E)
startskind⋯⇒kind (Sk ◂ e) ∀¬S (Sk′ ◂ E) = startskind⋯⇒kind e ∀¬S E
startskind⋯⇒kind {ϕ = ϕ} (mu e) ∀¬S {y = y} (mu E) =
  startskind-⋯ᵣ⁻¹ {k = _} weaken-inj
    (subst (λ κ → StartsKind κ (`/id (ϕ y) ⋯ weakenᵣ)) (sym (kindMapᵣ-weaken _))
    (subst (λ w → StartsKind _ w) (sym (wk-`/id (ϕ y)))
      (startskind⋯⇒kind e (λ where zero → ¬skips-`/` Kₛ
                                   (suc x) → ∀¬S x ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ x)))) E)))

------------------------------------------------------------------------
-- pulling a leading kind back through a substitution (the μ-unfold engine)
------------------------------------------------------------------------

startskind-⋯⁻¹ : {N : ℕ} {kin : AtomKind N} {ϕ : suc N →ₛ N} {t : 𝕊 (suc N)} →
  StartsKind kin (t ⋯ ϕ) → (∀ x → ¬ Skips (`/id (ϕ x))) →
  (∀ x → StartsVar x t → StartsKind (kindWk kin) t) → StartsKind (kindWk kin) t
startskind-⋯⁻¹ {t = ` x} e ∀¬S ∀¬E = ∀¬E x here
startskind-⋯⁻¹ {t = end p} e ∀¬S ∀¬E = here end (cong kindWk (startskind-atom-kind end e))
startskind-⋯⁻¹ {t = msg p T} e ∀¬S ∀¬E = here msg (cong kindWk (startskind-atom-kind msg e))
startskind-⋯⁻¹ {t = ret} e ∀¬S ∀¬E = here ret (cong kindWk (startskind-atom-kind ret e))
startskind-⋯⁻¹ {t = acq} e ∀¬S ∀¬E = here acq (cong kindWk (startskind-atom-kind acq e))
startskind-⋯⁻¹ {t = `` γ} e ∀¬S ∀¬E = here ``- (cong kindWk (startskind-atom-kind ``- e))
startskind-⋯⁻¹ {t = skip} e ∀¬S ∀¬E = ⊥-elim (skips⊥startskind skip e)
startskind-⋯⁻¹ {t = brn p t₁ t₂} e ∀¬S ∀¬E = ⊥-elim (¬startskind-brn e)
startskind-⋯⁻¹ {t = t₁ ; t₂} (▸ e) ∀¬S ∀¬E =
  ▸ startskind-⋯⁻¹ e ∀¬S (λ z E → [ (λ{ (Sk , _) → ⊥-elim (skips⊥startsvar Sk E) }) , (λ e′ → e′) ]′ (startskind-;⁻ (∀¬E z (▸ E))))
startskind-⋯⁻¹ {t = t₁ ; t₂} (Sk ◂ e) ∀¬S ∀¬E =
  Sk′ ◂ startskind-⋯⁻¹ e ∀¬S (λ z E → [ (λ{ (_ , e2) → e2 }) , (λ e′ → ⊥-elim (skips⊥startskind Sk′ e′)) ]′ (startskind-;⁻ (∀¬E z (Sk′ ◂ E))))
  where Sk′ = skips-⋯⁻¹ Sk ∀¬S
startskind-⋯⁻¹ {kin = kin} {ϕ = ϕ} {t = mu t₀} (mu e) ∀¬S ∀¬E =
  mu (startskind-⋯⁻¹ e
    (λ where zero → ¬skips-`/` Kₛ
             (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ z))))
    (λ where zero E → ⊥-elim (kindWk-not-zero (sym (startskind-atom-kind `- (subst (StartsKind (kindWk kin)) (`/`-is-` ⦃ Kₛ ⦄ zero)
                          (startskind⋯⇒kind e (λ where zero → ¬skips-`/` Kₛ
                                                       (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ z)))) E)))))
             (suc z) E → startskind-mu⁻ (∀¬E z (mu E))))

startskind-unfold⁻¹ : {k : AtomKind n} → ClosedKind k → StartsKind k (unfold s) → StartsKind (kindWk k) s
startskind-unfold⁻¹ {s = s} {k = k} ck e with skips? s
... | yes Ss = ⊥-elim (skips⊥startskind (skips-⋯ Ss) e)
... | no ¬Ss = startskind-⋯⁻¹ e ¬su callback
  where
  ¬su : ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
  ¬su zero (mu Ss) = ¬Ss Ss
  ¬su (suc x) = ¬skips-`/` Kₛ
  callback : ∀ x → StartsVar x s → StartsKind (kindWk k) s
  callback zero E = startskind-mu⁻ (startskind⋯⇒kind e ¬su E)
  callback (suc j) E = ⊥-elim (closed-≢-var ck (startskind-atom-kind `- (startskind⋯⇒kind e ¬su E)))

startskind-unfold : {k : AtomKind n} → StartsKind (kindWk k) s → StartsKind k (unfold s)
startskind-unfold e = startskind-⋯ baseUnfold e

------------------------------------------------------------------------
-- StartsKind is ≃-invariant
------------------------------------------------------------------------

≃-startskind : {k : AtomKind n} → ClosedKind k → StartsKind k Respects _≃_
≃-startskind ck refl = id
≃-startskind ck (x ◅ xs) = ≃-startskind ck xs ∘ go ck x where
  go : {k : AtomKind n} → ClosedKind k → SymClosure _≃𝕊_ s₁ s₂ → StartsKind k s₁ → StartsKind k s₂
  go ck (fwd ≃𝕊-μ) (mu e) = startskind-unfold e
  go ck (fwd (≃𝕊-msg x)) (here msg p) = here msg p
  go ck (bwd (≃𝕊-msg x)) (here msg p) = here msg p
  go ck (fwd (≃𝕊-;₁ x)) (▸ e) = ▸ go ck (fwd x) e
  go ck (fwd (≃𝕊-;₁ x)) (Sk ◂ e) = ≃-skips (Eq*.return x) Sk ◂ e
  go ck (fwd (≃𝕊-;₂ x)) (▸ e) = ▸ e
  go ck (fwd (≃𝕊-;₂ x)) (Sk ◂ e) = Sk ◂ go ck (fwd x) e
  go ck (fwd ≃𝕊-skipˡ) (Sk ◂ e) = e
  go ck (fwd ≃𝕊-skipˡ) (▸ e) = ⊥-elim (¬startskind-skip e)
  go ck (fwd ≃𝕊-skipʳ) (▸ e) = e
  go ck (fwd ≃𝕊-skipʳ) (Sk ◂ e) = ⊥-elim (¬startskind-skip e)
  go ck (fwd ≃𝕊-assoc) (▸ (▸ e)) = ▸ e
  go ck (fwd ≃𝕊-assoc) (▸ (Sk ◂ e)) = Sk ◂ (▸ e)
  go ck (fwd ≃𝕊-assoc) ((Sk₁ ; Sk₂) ◂ e) = Sk₁ ◂ (Sk₂ ◂ e)
  go ck (fwd ≃𝕊-distr) (▸ e) = ⊥-elim (¬startskind-brn e)
  go ck (fwd ≃𝕊-distr) (() ◂ e)
  go ck (fwd (≃𝕊-brn₁ x)) e = ⊥-elim (¬startskind-brn e)
  go ck (fwd (≃𝕊-brn₂ x)) e = ⊥-elim (¬startskind-brn e)
  go ck (bwd (≃𝕊-;₁ x)) (▸ e) = ▸ go ck (bwd x) e
  go ck (bwd (≃𝕊-;₁ x)) (Sk ◂ e) = ≃-skips (Star.return (bwd x)) Sk ◂ e
  go ck (bwd (≃𝕊-;₂ x)) (▸ e) = ▸ e
  go ck (bwd (≃𝕊-;₂ x)) (Sk ◂ e) = Sk ◂ go ck (bwd x) e
  go ck (bwd ≃𝕊-μ) e = mu (startskind-unfold⁻¹ ck e)
  go ck (bwd ≃𝕊-skipˡ) e = skip ◂ e
  go ck (bwd ≃𝕊-skipʳ) e = ▸ e
  go ck (bwd ≃𝕊-assoc) (▸ e) = ▸ (▸ e)
  go ck (bwd ≃𝕊-assoc) (Sk₁ ◂ (▸ e)) = ▸ (Sk₁ ◂ e)
  go ck (bwd ≃𝕊-assoc) (Sk₁ ◂ (Sk₂ ◂ e)) = (Sk₁ ; Sk₂) ◂ e
  go ck (bwd ≃𝕊-distr) e = ⊥-elim (¬startskind-brn e)
  go ck (bwd (≃𝕊-brn₁ x)) e = ⊥-elim (¬startskind-brn e)
  go ck (bwd (≃𝕊-brn₂ x)) e = ⊥-elim (¬startskind-brn e)

------------------------------------------------------------------------
-- distinct leading atoms ⇒ ≄  (mirror of atomKind≢⇒≄-;ʳ)
------------------------------------------------------------------------

atomK-starts-closed-≡ : {a₁ a₂ : 𝕊 n} (A₁ : Atom a₁) → ClosedKind (atomKind A₁) → (A₂ : Atom a₂) →
  a₁ ; s₁ ≃ a₂ ; s₂ → atomKind A₂ ≡ atomKind A₁
atomK-starts-closed-≡ A₁ ck A₂ eq =
  [ (λ{ (Sk , _) → ⊥-elim (¬skips-atom A₂ Sk) }) , startskind-atom-kind A₂ ]′
    (startskind-;⁻ (≃-startskind ck eq (▸ here A₁ refl)))

atomKind≢⇒≄-;ˡ : {a₁ a₂ : 𝕊 n} (A₁ : Atom a₁) (A₂ : Atom a₂) →
  atomKind A₁ ≢ atomKind A₂ → a₁ ; s₁ ≄ a₂ ; s₂
atomKind≢⇒≄-;ˡ end       A₂ k≢ eq = k≢ (sym (atomK-starts-closed-≡ end end A₂ eq))
atomKind≢⇒≄-;ˡ msg       A₂ k≢ eq = k≢ (sym (atomK-starts-closed-≡ msg msg A₂ eq))
atomKind≢⇒≄-;ˡ ret       A₂ k≢ eq = k≢ (sym (atomK-starts-closed-≡ ret ret A₂ eq))
atomKind≢⇒≄-;ˡ acq       A₂ k≢ eq = k≢ (sym (atomK-starts-closed-≡ acq acq A₂ eq))
atomKind≢⇒≄-;ˡ (``- {α = α}) A₂ k≢ eq = k≢ (sym (atomK-starts-closed-≡ (``- {α = α}) (``- {γ = α}) A₂ eq))
atomKind≢⇒≄-;ˡ `-        end k≢ eq = k≢ (atomK-starts-closed-≡ end end `- (≃-sym eq))
atomKind≢⇒≄-;ˡ `-        msg k≢ eq = k≢ (atomK-starts-closed-≡ msg msg `- (≃-sym eq))
atomKind≢⇒≄-;ˡ `-        ret k≢ eq = k≢ (atomK-starts-closed-≡ ret ret `- (≃-sym eq))
atomKind≢⇒≄-;ˡ `-        acq k≢ eq = k≢ (atomK-starts-closed-≡ acq acq `- (≃-sym eq))
atomKind≢⇒≄-;ˡ `- (``- {α = α}) k≢ eq = k≢ (atomK-starts-closed-≡ (``- {α = α}) (``- {γ = α}) `- (≃-sym eq))
atomKind≢⇒≄-;ˡ {n = n} {s₁ = s₁} {s₂ = s₂} (`- {x = x}) (`- {x = y}) k≢ eq =
  k≢ (cong `_ (Fin.toℕ-injective (cong UVar.var (AK-uvar-inj keq))))
  where
  ϕ : n →ₛ n
  ϕ z = `` uvar ‼ (Fin.toℕ z)
  eq′ : (`` uvar ‼ (Fin.toℕ x)) ; (s₁ ⋯ ϕ) ≃ (`` uvar ‼ (Fin.toℕ y)) ; (s₂ ⋯ ϕ)
  eq′ = ≃-⋯ {ϕ = ϕ} eq
  keq : (`` uvar ‼ (Fin.toℕ x)) ≡ (`` uvar ‼ (Fin.toℕ y))
  keq = sym (atomK-starts-closed-≡ ``- ``- ``- eq′)

------------------------------------------------------------------------
-- the blocking lemma:  msg p T ; s₂  ≄  acq ; s′
------------------------------------------------------------------------

msg;≄acq; : {n : ℕ} {p : Pol} {T : 𝕋} {s₂ s′ : 𝕊 n} → (msg p T ; s₂) ≄ (acq ; s′)
msg;≄acq; = atomKind≢⇒≄-;ˡ msg acq (λ ())
