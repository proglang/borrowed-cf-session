-- | Renaming injectivity for `Tm`: an injective renaming induces an injective
--   term map.  Needed by Normal.FrontIndep's perm-φφ / perm-νφ preservation
--   (un-weakening a moved borrow's channel).
module BorrowedCF.Simulation.Support.Normal.TmRenInj where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.FinKits using (Inj; ↑-inj)

open import Data.Product using (_×_; _,_; proj₁; proj₂)

private
  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {x x′ y y′ z z′} →
          x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
  cong₃ f refl refl refl = refl

  `-inj : ∀ {n} {x y : 𝔽 n} → (` x) ≡ (` y) → x ≡ y
  `-inj refl = refl
  K-inj : ∀ {n} {c c′} → K {n} c ≡ K c′ → c ≡ c′
  K-inj refl = refl
  ƛ-inj : ∀ {n} {e e′ : Tm (1 + n)} → ƛ e ≡ ƛ e′ → e ≡ e′
  ƛ-inj refl = refl
  μ-inj : ∀ {n} {e e′ : Tm (1 + n)} → μ e ≡ μ e′ → e ≡ e′
  μ-inj refl = refl
  ·-inj : ∀ {n} {e e′ e₁ e₁′ : Tm n} {d d′} →
          (e ·⟨ d ⟩ e₁) ≡ (e′ ·⟨ d′ ⟩ e₁′) → (d ≡ d′) × (e ≡ e′) × (e₁ ≡ e₁′)
  ·-inj refl = refl , refl , refl
  seqT-inj : ∀ {n} {e e′ e₁ e₁′ : Tm n} → (e ; e₁) ≡ (e′ ; e₁′) → (e ≡ e′) × (e₁ ≡ e₁′)
  seqT-inj refl = refl , refl
  ⊗-inj : ∀ {n} {e e′ e₁ e₁′ : Tm n} → (e ⊗ e₁) ≡ (e′ ⊗ e₁′) → (e ≡ e′) × (e₁ ≡ e₁′)
  ⊗-inj refl = refl , refl
  let-inj : ∀ {n} {e e′ : Tm n} {e₁ e₁′ : Tm (1 + n)} →
            (`let e `in e₁) ≡ (`let e′ `in e₁′) → (e ≡ e′) × (e₁ ≡ e₁′)
  let-inj refl = refl , refl
  let⊗-inj : ∀ {n} {e e′ : Tm n} {e₁ e₁′ : Tm (2 + n)} →
             (`let⊗ e `in e₁) ≡ (`let⊗ e′ `in e₁′) → (e ≡ e′) × (e₁ ≡ e₁′)
  let⊗-inj refl = refl , refl
  inj-inj : ∀ {n} {i i′} {e e′ : Tm n} → `inj i e ≡ `inj i′ e′ → (i ≡ i′) × (e ≡ e′)
  inj-inj refl = refl , refl
  case-inj : ∀ {n} {e e′ : Tm n} {e₁ e₁′ e₂ e₂′ : Tm (1 + n)} →
             (`case e `of⟨ e₁ ; e₂ ⟩) ≡ (`case e′ `of⟨ e₁′ ; e₂′ ⟩) →
             (e ≡ e′) × (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  case-inj refl = refl , refl , refl

⋯ᵣ-inj : ∀ {m n} {ρ : m →ᵣ n} {e e′ : Tm m} → Inj ρ → e ⋯ ρ ≡ e′ ⋯ ρ → e ≡ e′
⋯ᵣ-inj {e = ` x} {e′ = ` y} inj eq = cong `_ (inj (`-inj eq))
⋯ᵣ-inj {e = K c} {e′ = K c₁} inj eq = cong K (K-inj eq)
⋯ᵣ-inj {e = ƛ e} {e′ = ƛ e′} inj eq = cong ƛ (⋯ᵣ-inj (↑-inj inj) (ƛ-inj eq))
⋯ᵣ-inj {e = μ e} {e′ = μ e′} inj eq = cong μ (⋯ᵣ-inj (↑-inj inj) (μ-inj eq))
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj eq with ·-inj eq
... | refl , p1 , p2 = cong₂ (_·⟨ d ⟩_) (⋯ᵣ-inj inj p1) (⋯ᵣ-inj inj p2)
⋯ᵣ-inj {e = e ; e₁} {e′ = e′ ; e₁′} inj eq with seqT-inj eq
... | p1 , p2 = cong₂ _;_ (⋯ᵣ-inj inj p1) (⋯ᵣ-inj inj p2)
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = e′ ⊗ e₁′} inj eq with ⊗-inj eq
... | p1 , p2 = cong₂ _⊗_ (⋯ᵣ-inj inj p1) (⋯ᵣ-inj inj p2)
⋯ᵣ-inj {e = `let e `in e₁} {e′ = `let e′ `in e₁′} inj eq with let-inj eq
... | p1 , p2 = cong₂ `let_`in_ (⋯ᵣ-inj inj p1) (⋯ᵣ-inj (↑-inj inj) p2)
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = `let⊗ e′ `in e₁′} inj eq with let⊗-inj eq
... | p1 , p2 = cong₂ `let⊗_`in_ (⋯ᵣ-inj inj p1) (⋯ᵣ-inj (↑-inj (↑-inj inj)) p2)
⋯ᵣ-inj {e = `inj i e} {e′ = `inj i′ e′} inj eq with inj-inj eq
... | refl , p = cong (`inj i) (⋯ᵣ-inj inj p)
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj eq with case-inj eq
... | p , p1 , p2 = cong₃ (λ a b c → `case a `of⟨ b ; c ⟩) (⋯ᵣ-inj inj p) (⋯ᵣ-inj (↑-inj inj) p1) (⋯ᵣ-inj (↑-inj inj) p2)
⋯ᵣ-inj {e = ` x} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = ` x} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = ` x} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = K c} {e′ = ` y} inj ()
⋯ᵣ-inj {e = K c} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = K c} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = K c} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = K c} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = K c} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = K c} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = K c} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = K c} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = K c} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = ` y} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = ƛ e} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = μ e} {e′ = ` y} inj ()
⋯ᵣ-inj {e = μ e} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = μ e} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = μ e} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = ` y} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = e ·⟨ d ⟩ e₁} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = ` y} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = e ; e₁} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = ` y} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = e ⊗ e₁} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = ` y} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = `let e `in e₁} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = ` y} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = `inj i′ e′} inj ()
⋯ᵣ-inj {e = `let⊗ e `in e₁} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = ` y} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `inj i e} {e′ = `case e′ `of⟨ e₁′ ; e₂′ ⟩} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = ` y} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = K c₁} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = ƛ e′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = μ e′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = e′ ·⟨ d′ ⟩ e₁′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = e′ ; e₁′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = e′ ⊗ e₁′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = `let e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = `let⊗ e′ `in e₁′} inj ()
⋯ᵣ-inj {e = `case e `of⟨ e₁ ; e₂ ⟩} {e′ = `inj i′ e′} inj ()
