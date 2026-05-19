{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction.Base where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context

module Variables where
  open Nat.Variables public
  variable e e₁ e₂ e₃ e′ : Tm n

open Variables

-- NB. Values are predicates on _unclosed_ terms. That is because
-- channel variables are values but we don't want to keep two kinds of
-- environments around. The notion of a "Value" is only correct in a
-- context Γ where `ChanCx Γ` holds.

ChanCx : Ctx n → Set
ChanCx Γ = ∀ x → ∃ λ s → Γ x ≡ ⟨ s ⟩

data Value {n} : Tm n → Set where
  V-` : ∀ {x} → Value (` x)
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (ƛ e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ⊗ e₂)

vTm : {e : Tm n} → Value e → Tm n
vTm {e = e} _ = e

Value-irr : {U V : Value e} → U ≡ V
Value-irr {U = V-`} {V-`} = refl
Value-irr {U = V-K} {V-K} = refl
Value-irr {U = V-λ} {V-λ} = refl
Value-irr {U = V-⊗ U₁ U₂} {V-⊗ V₁ V₂} = cong₂ V-⊗ Value-irr Value-irr

{-
data Blocked {n} : Tm n → Set where
  `fork : Blocked (K `fork · ƛ e)
  `new : Blocked (K (`new s) · K `unit)
  `lsplit : ∀ {x} → Blocked (K `lsplit · (` x))
  `rsplit : ∀ {x} → Blocked (K `rsplit · (` x))
  `drop : ∀ {x} → Blocked (K `drop · (` x))
  `acq : ∀ {x} → Blocked (K `acq · (` x))
  `send : ∀ {x} → Value e → Blocked (K `send · (e ⊗ (` x)))
  `recv : ∀ {x} → Blocked (K `recv · (` x))
  `end : ∀ {x} → Blocked (K (`end p) · (` x))
-}

Blocked : Tm n → Set
Blocked e = ∃[ c ] ∃[ e′ ] Value e′ × e ≡ c · e′

data Frame n : Set where
  □·_ : (e₂ : Tm n) → Frame n
  _·□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □⊗_ : (e₂ : Tm n) → Frame n
  _⊗□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □;_ : (e₂ : Tm n) → Frame n
  `let-`in_ : (e′ : Tm (1 + n)) → Frame n
  `let⊗-`in_ : (e′ : Tm (2 + n)) → Frame n

infixl 4.5 _[_]

_[_] : Frame n → Tm n → Tm n
(□· e) [ e₀ ] = e₀ · e
(V ·□) [ e₀ ] = vTm V · e₀
(□⊗ e) [ e₀ ] = e₀ ⊗ e
(V ⊗□) [ e₀ ] = vTm V ⊗ e₀
(□; e) [ e₀ ] = e₀ ; e
(`let-`in e) [ e₀ ] = `let e₀ `in e
(`let⊗-`in e) [ e₀ ] = `let⊗ e₀ `in e

--data EvCx

VSub : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Set
VSub ϕ = ∀ x → Value (`/id (ϕ x))

value-⋯ : ⦃ K : Kit 𝓕 ⦄ → Value e → (ϕ : m –[ K ]→ n) → VSub ϕ → Value (e ⋯ ϕ)
value-⋯ V-` ϕ Vϕ = Vϕ _
value-⋯ V-K ϕ Vϕ = V-K
value-⋯ V-λ ϕ Vϕ = V-λ
value-⋯ (V-⊗ V₁ V₂) ϕ Vϕ = V-⊗ (value-⋯ V₁ ϕ Vϕ) (value-⋯ V₂ ϕ Vϕ)

frame-⋯ : ⦃ K : Kit 𝓕 ⦄ → Frame m → (ϕ : m –[ K ]→ n) → VSub ϕ → Frame n
frame-⋯ (□· e₂) ϕ Vϕ = □· (e₂ ⋯ ϕ)
frame-⋯ (V₁ ·□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ·□
frame-⋯ (□⊗ e₂) ϕ Vϕ = □⊗ (e₂ ⋯ ϕ)
frame-⋯ (V₁ ⊗□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ·□
frame-⋯ (□; e₂) ϕ Vϕ = □; (e₂ ⋯ ϕ)
frame-⋯ (`let-`in e′) ϕ Vϕ = `let-`in (e′ ⋯ ϕ ↑)
frame-⋯ (`let⊗-`in e′) ϕ Vϕ = `let⊗-`in (e′ ⋯ ϕ ↑ ↑)

infixl 5 _⋯ᵛ_ _⋯ᶠ_

_⋯ᵛ_ : Value e → (ϕ : m →ᵣ n) → Value (e ⋯ ϕ)
V ⋯ᵛ ϕ = value-⋯ V ϕ λ x → V-`

_⋯ᶠ_ : Frame m → (ϕ : m →ᵣ n) → Frame n
E ⋯ᶠ ϕ = frame-⋯ E ϕ λ x → V-`

FullBlocked : Tm n → Set
FullBlocked {n} e = ∀ E (e′ : Tm n) → e ≡ E [ e′ ] → Blocked e′

Value⊥Blocked : Value {n} Un.⊥ Blocked
Value⊥Blocked (() , _ , _ , _ , refl)

unique-frame : (E E′ : Frame n) → ¬ Value e → ¬ Value e′ → E [ e ] ≡ E′ [ e′ ] → E ≡ E′ × e ≡ e′
unique-frame (□· e₂) (□· e₃) ¬V ¬V′ refl = refl , refl
unique-frame (□· e₂) (V₁ ·□) ¬V ¬V′ refl = ⊥-elim (¬V V₁)
unique-frame (V₁ ·□) (□· e₂) ¬V ¬V′ refl = ⊥-elim (¬V′ V₁)
unique-frame (V₁ ·□) (V₂ ·□) ¬V ¬V′ refl = cong _·□ Value-irr , refl
unique-frame (□⊗ e₂) (□⊗ e₃) ¬V ¬V′ refl = refl , refl
unique-frame (□⊗ e₂) (V₁ ⊗□) ¬V ¬V′ refl = ⊥-elim (¬V V₁)
unique-frame (V₁ ⊗□) (□⊗ e₂) ¬V ¬V′ refl = ⊥-elim (¬V′ V₁)
unique-frame (V₁ ⊗□) (V₂ ⊗□) ¬V ¬V′ refl = cong _⊗□ Value-irr , refl
unique-frame (□; e₂) (□; e₃) ¬V ¬V′ refl = refl , refl
unique-frame (`let-`in e′) (`let-`in e′₁) ¬V ¬V′ refl = refl , refl
unique-frame (`let⊗-`in e′) (`let⊗-`in e′₁) ¬V ¬V′ refl = refl , refl
