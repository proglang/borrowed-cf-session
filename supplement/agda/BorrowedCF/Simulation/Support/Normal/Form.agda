-- | Prenex normal forms for untyped processes.
--
--   Every untyped process is ≋-equal to one of the shape
--
--       ν/φ … ν/φ (⟪e₁⟫ ∥ … ∥ ⟪eₚ⟫ ∥ ⟪unit⟫)
--
--   i.e. a BINDER TELESCOPE over a flat parallel composition of threads.  This
--   module defines the data; Normal.Prenex computes it.
--
--   Design note (why `Tel` carries BOTH scopes).  Indexing a telescope by its
--   total width — `Tel w n`, body at `w + n` — forces a `+-assoc` transport at
--   every `ν`/`φ` step, and those transports then infect every downstream lemma
--   (this is the same `+-suc` bookkeeping that makes `Translation.UB[_]` painful).
--   Indexing by the OUTER and INNER scope instead makes `plug` definitionally
--   total with no `subst` anywhere.
module BorrowedCF.Simulation.Support.Normal.Form where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped

open import Data.List using (List; []; _∷_; _++_; map)

open Nat.Variables

------------------------------------------------------------------------
-- Binder telescopes.
------------------------------------------------------------------------

-- `Tel n k` : a nest of ν/φ binders that turns a body in scope k into a
-- process in scope n.  Outermost binder first.
-- Linked-φ: a `tφ` binder records the channel `c : Tm n` it guards (in the
-- OUTER scope n, exactly as the `φ` process constructor does).
data Tel : ℕ → ℕ → Set where
  []  : ∀ {n} → Tel n n
  tν  : ∀ {n k} → Tel (2 + n) k → Tel n k
  tφ  : ∀ {n k} → Flag → (c : Tm n) → Tel (1 + n) k → Tel n k

plug : ∀ {n k} → Tel n k → Proc k → Proc n
plug []         X = X
plug (tν t)     X = ν (plug t X)
plug (tφ f c t) X = φ f c (plug t X)

-- The weakening a telescope induces on its base scope.
wkTel : ∀ {n k} → Tel n k → n →ᵣ k
wkTel []           = idₖ
wkTel (tν t)       = weaken* ⦃ Kᵣ ⦄ 2 ·ₖ wkTel t
wkTel (tφ _ _ t)   = weaken* ⦃ Kᵣ ⦄ 1 ·ₖ wkTel t

infixr 5 _++ᵗ_

_++ᵗ_ : ∀ {n k j} → Tel n k → Tel k j → Tel n j
[]         ++ᵗ s = s
tν t       ++ᵗ s = tν (t ++ᵗ s)
tφ f c t   ++ᵗ s = tφ f c (t ++ᵗ s)

plug-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (X : Proc j) →
           plug (t ++ᵗ s) X ≡ plug t (plug s X)
plug-++ᵗ []         s X = refl
plug-++ᵗ (tν t)     s X = cong ν       (plug-++ᵗ t s X)
plug-++ᵗ (tφ f c t) s X = cong (φ f c) (plug-++ᵗ t s X)

------------------------------------------------------------------------
-- Flat thread lists.
------------------------------------------------------------------------

pars : ∀ {n} → List (Tm n) → Proc n
pars []       = ⟪ K `unit ⟫
pars (e ∷ es) = ⟪ e ⟫ ∥ pars es

pars-⋯ₚ : ∀ {n m} (es : List (Tm n)) (ρ : n →ᵣ m) →
          pars es ⋯ₚ ρ ≡ pars (map (_⋯ ρ) es)
pars-⋯ₚ []       ρ = refl
pars-⋯ₚ (e ∷ es) ρ = cong (⟪ e ⋯ ρ ⟫ ∥_) (pars-⋯ₚ es ρ)

------------------------------------------------------------------------
-- Normal forms.
------------------------------------------------------------------------

record NF (n : ℕ) : Set where
  constructor mkNF
  field
    {inner} : ℕ
    tel     : Tel n inner
    thr     : List (Tm inner)

open NF public

⌈_⌉ : ∀ {n} → NF n → Proc n
⌈ mkNF t es ⌉ = plug t (pars es)

------------------------------------------------------------------------
-- A renaming-invariant size, for the well-founded prenex recursion.
------------------------------------------------------------------------

size : ∀ {n} → Proc n → ℕ
size ⟪ _ ⟫     = 1
size (P ∥ Q)   = suc (size P + size Q)
size (ν P)     = suc (size P)
size (φ _ _ P) = suc (size P)

size-⋯ₚ : ∀ {n m} (P : Proc n) (ρ : n →ᵣ m) → size (P ⋯ₚ ρ) ≡ size P
size-⋯ₚ ⟪ _ ⟫     ρ = refl
size-⋯ₚ (P ∥ Q)   ρ = cong suc (cong₂ _+_ (size-⋯ₚ P ρ) (size-⋯ₚ Q ρ))
size-⋯ₚ (ν P)     ρ = cong suc (size-⋯ₚ P (ρ ↑* 2))
size-⋯ₚ (φ _ _ P) ρ = cong suc (size-⋯ₚ P (ρ ↑))
