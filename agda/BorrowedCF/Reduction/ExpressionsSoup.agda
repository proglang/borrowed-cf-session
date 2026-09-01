module BorrowedCF.Reduction.ExpressionsSoup where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup
open import BorrowedCF.Types using (Dir; L; R; 𝟙)

open Nat.Variables

module Variables where
  open Nat.Variables public
  variable e e₁ e₂ e₃ e′ : Tm n
  variable d : Dir

open Variables

data Value {n} : Tm n → Set where
  V-` : ∀ {x} → Value (` x)
  V-phi : ∀ {r} → Value (`phi r)
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (ƛ e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ⊗ e₂)
  V-⊕ : ∀ {i} → Value e → Value (`inj i e)

vTm : {e : Tm n} → Value e → Tm n
vTm {e = e} _ = e

value-rename : Value e → (ρ : 𝔽 n → 𝔽 n′) → Value (e ⋯ᵣ ρ)
value-rename V-` ρ = V-`
value-rename V-phi ρ = V-phi
value-rename V-K ρ = V-K
value-rename V-λ ρ = V-λ
value-rename (V-⊗ V₁ V₂) ρ = V-⊗ (value-rename V₁ ρ) (value-rename V₂ ρ)
value-rename (V-⊕ V) ρ = V-⊕ (value-rename V ρ)

-- Substitution at the innermost ordinary expression binder.  A phi address
-- at that binder is ill formed; unit makes the operation total on raw terms.
singleSub : Tm n → Sub (1 + n) n
singleSub {n = n} e = sub vars refs
  where
  vars : 𝔽 (1 + n) → Tm n
  vars zero = e
  vars (suc x) = ` x

  refs : PhiRef (1 + n) → Tm n
  refs (zero , k) = *
  refs (suc x , k) = `phi (x , k)

subst₀ : Tm n → Tm (1 + n) → Tm n
subst₀ e body = body ⋯ₛ singleSub e

data Frame (n : ℕ) : Set where
  app₁ : (e : Tm n) (d : Dir) → (d ≡ L → Value e) → Frame n
  app₂ : (e : Tm n) (d : Dir) → (d ≡ 𝟙 ⊎ d ≡ R → Value e) → Frame n
  □⊗_ : Tm n → Frame n
  _⊗□ : {e : Tm n} → Value e → Frame n
  □;_ : Tm n → Frame n
  `let-`in_ : Tm (1 + n) → Frame n
  `let⊗-`in_ : Tm (2 + n) → Frame n
  `inj□ : Side → Frame n
  `case□`of⟨_;_⟩ : Tm (1 + n) → Tm (1 + n) → Frame n

infixl 4.5 _[_]

_[_] : Frame n → Tm n → Tm n
app₁ e d V? [ e₀ ] = e₀ ·⟨ d ⟩ e
app₂ e d V? [ e₀ ] = e ·⟨ d ⟩ e₀
(□⊗ e) [ e₀ ] = e₀ ⊗ e
(V ⊗□) [ e₀ ] = vTm V ⊗ e₀
(□; e) [ e₀ ] = e₀ ; e
(`let-`in e) [ e₀ ] = `let e₀ `in e
(`let⊗-`in e) [ e₀ ] = `let⊗ e₀ `in e
`inj□ i [ e₀ ] = `inj i e₀
`case□`of⟨ e₁ ; e₂ ⟩ [ e₀ ] = `case e₀ `of⟨ e₁ ; e₂ ⟩

frame-rename : Frame n → (𝔽 n → 𝔽 n′) → Frame n′
frame-rename (app₁ e d V?) ρ =
  app₁ (e ⋯ᵣ ρ) d λ d≡L → value-rename (V? d≡L) ρ
frame-rename (app₂ e d V?) ρ =
  app₂ (e ⋯ᵣ ρ) d λ d≡→ → value-rename (V? d≡→) ρ
frame-rename (□⊗ e) ρ = □⊗ (e ⋯ᵣ ρ)
frame-rename (V ⊗□) ρ = value-rename V ρ ⊗□
frame-rename (□; e) ρ = □; (e ⋯ᵣ ρ)
frame-rename (`let-`in e) ρ = `let-`in (e ⋯ᵣ liftRen ρ)
frame-rename (`let⊗-`in e) ρ = `let⊗-`in (e ⋯ᵣ liftRen (liftRen ρ))
frame-rename (`inj□ i) ρ = `inj□ i
frame-rename (`case□`of⟨ e₁ ; e₂ ⟩) ρ =
  `case□`of⟨ (e₁ ⋯ᵣ liftRen ρ) ; (e₂ ⋯ᵣ liftRen ρ) ⟩

Frame* : ℕ → Set
Frame* n = List (Frame n)

infixl 4.5 _[_]*

_[_]* : Frame* n → Tm n → Tm n
[] [ e ]* = e
(E ∷ Es) [ e ]* = E [ Es [ e ]* ]

frames-rename : Frame* n → (𝔽 n → 𝔽 n′) → Frame* n′
frames-rename [] ρ = []
frames-rename (E ∷ Es) ρ = frame-rename E ρ ∷ frames-rename Es ρ

infix 4 _─→_ _⋯→_

data _─→_ {n} : Tm n → Tm n → Set where
  E-App : Value e₂ → (ƛ e₁) ·⟨ d ⟩ e₂ ─→ subst₀ e₂ e₁
  E-Seq : Value e₁ → e₁ ; e₂ ─→ e₂
  E-Let : Value e₁ → `let e₁ `in e₂ ─→ subst₀ e₁ e₂
  E-PairElim : Value e₁ → Value e₂ →
    `let⊗ (e₁ ⊗ e₂) `in e ─→ subst₀ e₂ (subst₀ (wk e₁) e)
  E-SumElim : ∀ {i} → Value e →
    `case `inj i e `of⟨ e₁ ; e₂ ⟩ ─→ subst₀ e (if i then e₁ else e₂)
  E-Unfold : μ e ─→ subst₀ (μ e) e

data _⋯→_ {n} : Tm n → Tm n → Set where
  E-□ : e₁ ─→ e₂ → e₁ ⋯→ e₂
  E-Ctx : (E : Frame n) → e₁ ⋯→ e₂ → E [ e₁ ] ⋯→ E [ e₂ ]
