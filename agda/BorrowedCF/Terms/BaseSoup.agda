module BorrowedCF.Terms.BaseSoup where

open import Data.Maybe using (Maybe; just; nothing)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Terms.Base
  using ( Const; `unit; `fork; `send; `recv; `drop; `acq; `discard
        ; `end; `new; `lsplit; `rsplit; `select; `branch; Side
        )
  public

open Nat.Variables

-- A phi cell is stored at one channel endpoint.  Its reference consists of
-- the endpoint's variable and the cell's position in that endpoint's list.
PhiRef : ℕ → Set
PhiRef n = 𝔽 n × ℕ

data Tm (n : ℕ) : Set where
  `_ : 𝔽 n → Tm n
  `phi : PhiRef n → Tm n
  K : (c : Const) → Tm n
  ƛ : (e : Tm (1 + n)) → Tm n
  μ : (e : Tm (1 + n)) → Tm n
  _·⟨_⟩_ : (e₁ : Tm n) (d : Dir) (e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _⊗_ : (e₁ e₂ : Tm n) → Tm n
  `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  `let⊗_`in_ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n
  `inj : (i : Side) (e : Tm n) → Tm n
  `case_`of⟨_;_⟩ :
    (e : Tm n) (e₁ e₂ : Tm (1 + n)) → Tm n

pattern * = K `unit
pattern _·ᴸ_ e₁ e₂ = e₁ ·⟨ L ⟩ e₂
pattern _·ᴿ_ e₁ e₂ = e₁ ·⟨ R ⟩ e₂
pattern _·¹_ e₁ e₂ = e₁ ·⟨ 𝟙 ⟩ e₂

liftRen : (𝔽 n → 𝔽 n′) → 𝔽 (1 + n) → 𝔽 (1 + n′)
liftRen ρ zero = zero
liftRen ρ (suc x) = suc (ρ x)

renameRef : (𝔽 n → 𝔽 n′) → PhiRef n → PhiRef n′
renameRef ρ (x , k) = ρ x , k

infixl 5 _⋯ᵣ_

-- Channel endpoints and phi addresses share the same namespace.  In
-- particular, both are weakened when passing under an expression binder.
_⋯ᵣ_ : Tm n → (𝔽 n → 𝔽 n′) → Tm n′
(` x) ⋯ᵣ ρ = ` ρ x
(`phi r) ⋯ᵣ ρ = `phi (renameRef ρ r)
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

wk : Tm n → Tm (1 + n)
wk e = e ⋯ᵣ suc

-- Variable and phi occurrences need separate images: the latter carries an
-- endpoint address, which an arbitrary variable substitution cannot provide.
record Sub (n n′ : ℕ) : Set where
  constructor sub
  field
    varImage : 𝔽 n → Tm n′
    phiImage : PhiRef n → Tm n′

open Sub public

liftSub : Sub n n′ → Sub (1 + n) (1 + n′)
liftSub {n = n} {n′ = n′} σ = sub vars refs
  where
  vars : 𝔽 (1 + n) → Tm (1 + n′)
  vars zero = ` zero
  vars (suc x) = wk (varImage σ x)

  refs : PhiRef (1 + n) → Tm (1 + n′)
  refs (zero , k) = `phi (zero , k)
  refs (suc x , k) = wk (phiImage σ (x , k))

infixl 5 _⋯ₛ_

_⋯ₛ_ : Tm n → Sub n n′ → Tm n′
(` x) ⋯ₛ σ = varImage σ x
(`phi r) ⋯ₛ σ = phiImage σ r
K c ⋯ₛ σ = K c
ƛ e ⋯ₛ σ = ƛ (e ⋯ₛ liftSub σ)
μ e ⋯ₛ σ = μ (e ⋯ₛ liftSub σ)
(e₁ ·⟨ d ⟩ e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ·⟨ d ⟩ (e₂ ⋯ₛ σ)
(e₁ ; e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ; (e₂ ⋯ₛ σ)
(e₁ ⊗ e₂) ⋯ₛ σ = (e₁ ⋯ₛ σ) ⊗ (e₂ ⋯ₛ σ)
(`let e₁ `in e₂) ⋯ₛ σ =
  `let (e₁ ⋯ₛ σ) `in (e₂ ⋯ₛ liftSub σ)
(`let⊗ e₁ `in e₂) ⋯ₛ σ =
  `let⊗ (e₁ ⋯ₛ σ) `in (e₂ ⋯ₛ liftSub (liftSub σ))
(`inj i e) ⋯ₛ σ = `inj i (e ⋯ₛ σ)
(`case e `of⟨ e₁ ; e₂ ⟩) ⋯ₛ σ =
  `case (e ⋯ₛ σ) `of⟨ (e₁ ⋯ₛ liftSub σ) ; (e₂ ⋯ₛ liftSub σ) ⟩

ResolvedPhiRef : ℕ → Set
ResolvedPhiRef n = Maybe (PhiRef n)

resolveRef : ∀ {n} d → PhiRef (d + n) → ResolvedPhiRef n
resolveRef d (x , k) with Fin.splitAt d x
... | inj₁ _ = nothing
... | inj₂ y = just (y , k)

-- Resolve references against the free-variable namespace of the enclosing
-- process.  A reference to one of the d local expression binders is retained
-- as nothing so that configuration well-formedness can reject it.
phiRefsFrom : ∀ {n} d → Tm (d + n) → List (ResolvedPhiRef n)
phiRefsFrom d (` x) = []
phiRefsFrom d (`phi r) = resolveRef d r ∷ []
phiRefsFrom d (K c) = []
phiRefsFrom d (ƛ e) = phiRefsFrom (suc d) e
phiRefsFrom d (μ e) = phiRefsFrom (suc d) e
phiRefsFrom d (e₁ ·⟨ dir ⟩ e₂) =
  phiRefsFrom d e₁ ++ phiRefsFrom d e₂
phiRefsFrom d (e₁ ; e₂) = phiRefsFrom d e₁ ++ phiRefsFrom d e₂
phiRefsFrom d (e₁ ⊗ e₂) = phiRefsFrom d e₁ ++ phiRefsFrom d e₂
phiRefsFrom d (`let e₁ `in e₂) =
  phiRefsFrom d e₁ ++ phiRefsFrom (suc d) e₂
phiRefsFrom d (`let⊗ e₁ `in e₂) =
  phiRefsFrom d e₁ ++ phiRefsFrom (suc (suc d)) e₂
phiRefsFrom d (`inj i e) = phiRefsFrom d e
phiRefsFrom d (`case e `of⟨ e₁ ; e₂ ⟩) =
  phiRefsFrom d e ++
  phiRefsFrom (suc d) e₁ ++
  phiRefsFrom (suc d) e₂

phiRefs : Tm n → List (ResolvedPhiRef n)
phiRefs = phiRefsFrom 0
