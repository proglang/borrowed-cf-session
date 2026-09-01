module BorrowedCF.Terms.BaseSoup where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Terms.Base
  using ( Const; `unit; `fork; `send; `recv; `drop; `acq; `discard
        ; `end; `new; `lsplit; `rsplit; `select; `branch; Side
        )
  public

open Nat.Variables

-- A phi cell is stored in one thread of a configuration.  Its reference
-- consists of that thread's index and the cell's position in its flag list.
-- The second component is checked against the configuration by UntypedSoup.
PhiRef : ℕ → Set
PhiRef m = 𝔽 m × ℕ

-- The first index scopes ordinary expression variables, including free
-- channel endpoints.  The second scopes the thread component of PhiRef.
data Tm (n m : ℕ) : Set where
  `_ : 𝔽 n → Tm n m
  `phi : PhiRef m → Tm n m
  K : (c : Const) → Tm n m
  ƛ : (e : Tm (1 + n) m) → Tm n m
  μ : (e : Tm (1 + n) m) → Tm n m
  _·⟨_⟩_ : (e₁ : Tm n m) (d : Dir) (e₂ : Tm n m) → Tm n m
  _;_ : (e₁ e₂ : Tm n m) → Tm n m
  _⊗_ : (e₁ e₂ : Tm n m) → Tm n m
  `let_`in_ : (e₁ : Tm n m) (e₂ : Tm (1 + n) m) → Tm n m
  `let⊗_`in_ : (e₁ : Tm n m) (e₂ : Tm (2 + n) m) → Tm n m
  `inj : (i : Side) (e : Tm n m) → Tm n m
  `case_`of⟨_;_⟩ :
    (e : Tm n m) (e₁ e₂ : Tm (1 + n) m) → Tm n m

pattern * = K `unit
pattern _·ᴸ_ e₁ e₂ = e₁ ·⟨ L ⟩ e₂
pattern _·ᴿ_ e₁ e₂ = e₁ ·⟨ R ⟩ e₂
pattern _·¹_ e₁ e₂ = e₁ ·⟨ 𝟙 ⟩ e₂

liftRen : (𝔽 n → 𝔽 n′) → 𝔽 (1 + n) → 𝔽 (1 + n′)
liftRen ρ zero = zero
liftRen ρ (suc x) = suc (ρ x)

infixl 5 _⋯ᵣ_

-- Ordinary renaming acts on channels and local expression variables.  Phi
-- references are independent of this namespace.
_⋯ᵣ_ : Tm n m → (𝔽 n → 𝔽 n′) → Tm n′ m
(` x) ⋯ᵣ ρ = ` ρ x
(`phi r) ⋯ᵣ ρ = `phi r
K c ⋯ᵣ ρ = K c
ƛ e ⋯ᵣ ρ = ƛ (e ⋯ᵣ liftRen ρ)
μ e ⋯ᵣ ρ = μ (e ⋯ᵣ liftRen ρ)
(e₁ ·⟨ d ⟩ e₂) ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) ·⟨ d ⟩ (e₂ ⋯ᵣ ρ)
(e₁ ; e₂) ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) ; (e₂ ⋯ᵣ ρ)
(e₁ ⊗ e₂) ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) ⊗ (e₂ ⋯ᵣ ρ)
(`let e₁ `in e₂) ⋯ᵣ ρ = `let (e₁ ⋯ᵣ ρ) `in (e₂ ⋯ᵣ liftRen ρ)
(`let⊗ e₁ `in e₂) ⋯ᵣ ρ =
  `let⊗ (e₁ ⋯ᵣ ρ) `in (e₂ ⋯ᵣ liftRen (liftRen ρ))
(`inj i e) ⋯ᵣ ρ = `inj i (e ⋯ᵣ ρ)
(`case e `of⟨ e₁ ; e₂ ⟩) ⋯ᵣ ρ =
  `case (e ⋯ᵣ ρ) `of⟨ (e₁ ⋯ᵣ liftRen ρ) ; (e₂ ⋯ᵣ liftRen ρ) ⟩

wk : Tm n m → Tm (1 + n) m
wk e = e ⋯ᵣ suc

Sub : ℕ → ℕ → ℕ → Set
Sub n n′ m = 𝔽 n → Tm n′ m

liftSub : Sub n n′ m → Sub (1 + n) (1 + n′) m
liftSub σ zero = ` zero
liftSub σ (suc x) = wk (σ x)

infixl 5 _⋯ₛ_

-- Substitution affects the ordinary namespace only.  This is the operation
-- used by expression reduction; PhiRef values remain pointers into Config.
_⋯ₛ_ : Tm n m → Sub n n′ m → Tm n′ m
(` x) ⋯ₛ σ = σ x
(`phi r) ⋯ₛ σ = `phi r
K c ⋯ₛ σ = K c
ƛ e ⋯ₛ σ = ƛ (e ⋯ₛ liftSub σ)
μ e ⋯ₛ σ = μ (e ⋯ₛ liftSub σ)
(e₁ ·⟨ d ⟩ e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ·⟨ d ⟩ (e₂ ⋯ₛ σ)
(e₁ ; e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ; (e₂ ⋯ₛ σ)
(e₁ ⊗ e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ⊗ (e₂ ⋯ₛ σ)
(`let e₁ `in e₂) ⋯ₛ σ = `let (e₁ ⋯ₛ σ) `in (e₂ ⋯ₛ liftSub σ)
(`let⊗ e₁ `in e₂) ⋯ₛ σ =
  `let⊗ (e₁ ⋯ₛ σ) `in (e₂ ⋯ₛ liftSub (liftSub σ))
(`inj i e) ⋯ₛ σ = `inj i (e ⋯ₛ σ)
(`case e `of⟨ e₁ ; e₂ ⟩) ⋯ₛ σ =
  `case (e ⋯ₛ σ) `of⟨ (e₁ ⋯ₛ liftSub σ) ; (e₂ ⋯ₛ liftSub σ) ⟩

renameRef : (𝔽 m → 𝔽 m′) → PhiRef m → PhiRef m′
renameRef ρ (j , k) = ρ j , k

infixl 5 _⋯phi_

-- Thread renaming is separate: it changes only the owner component of phi
-- references and does not pass under expression binders.
_⋯phi_ : Tm n m → (𝔽 m → 𝔽 m′) → Tm n m′
(` x) ⋯phi ρ = ` x
(`phi r) ⋯phi ρ = `phi (renameRef ρ r)
K c ⋯phi ρ = K c
ƛ e ⋯phi ρ = ƛ (e ⋯phi ρ)
μ e ⋯phi ρ = μ (e ⋯phi ρ)
(e₁ ·⟨ d ⟩ e₂) ⋯phi ρ = (e₁ ⋯phi ρ) ·⟨ d ⟩ (e₂ ⋯phi ρ)
(e₁ ; e₂) ⋯phi ρ = (e₁ ⋯phi ρ) ; (e₂ ⋯phi ρ)
(e₁ ⊗ e₂) ⋯phi ρ = (e₁ ⋯phi ρ) ⊗ (e₂ ⋯phi ρ)
(`let e₁ `in e₂) ⋯phi ρ = `let (e₁ ⋯phi ρ) `in (e₂ ⋯phi ρ)
(`let⊗ e₁ `in e₂) ⋯phi ρ = `let⊗ (e₁ ⋯phi ρ) `in (e₂ ⋯phi ρ)
(`inj i e) ⋯phi ρ = `inj i (e ⋯phi ρ)
(`case e `of⟨ e₁ ; e₂ ⟩) ⋯phi ρ =
  `case (e ⋯phi ρ) `of⟨ (e₁ ⋯phi ρ) ; (e₂ ⋯phi ρ) ⟩

phiRefs : Tm n m → List (PhiRef m)
phiRefs (` x) = []
phiRefs (`phi r) = r ∷ []
phiRefs (K c) = []
phiRefs (ƛ e) = phiRefs e
phiRefs (μ e) = phiRefs e
phiRefs (e₁ ·⟨ d ⟩ e₂) = phiRefs e₁ ++ phiRefs e₂
phiRefs (e₁ ; e₂) = phiRefs e₁ ++ phiRefs e₂
phiRefs (e₁ ⊗ e₂) = phiRefs e₁ ++ phiRefs e₂
phiRefs (`let e₁ `in e₂) = phiRefs e₁ ++ phiRefs e₂
phiRefs (`let⊗ e₁ `in e₂) = phiRefs e₁ ++ phiRefs e₂
phiRefs (`inj i e) = phiRefs e
phiRefs (`case e `of⟨ e₁ ; e₂ ⟩) =
  phiRefs e ++ phiRefs e₁ ++ phiRefs e₂
