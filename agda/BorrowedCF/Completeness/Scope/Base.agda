-- | Unification-variable scope bookkeeping, part 1: the predicate and substitution
--   agreement.
--
--   `UVarsIn m n t` says that every unification variable occurring in the type `t`
--   has an index in the half-open interval [m, n).  Polarity is irrelevant: only
--   `UVar.var` is inspected, so `` `` α `` and `` `` (UV.dual α) `` are in scope
--   under exactly the same bounds.
module BorrowedCF.Completeness.Scope.Base where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved

open Nat.Variables

------------------------------------------------------------------------
-- The predicate

-- A unification variable is in the window [lo, hi).  Polarity is irrelevant.
InRange : ℕ → ℕ → UVar → Set
InRange lo hi α = lo Nat.≤ UV.var α × UV.var α Nat.< hi

inRange-mono : ∀ (α : UVar) → m′ Nat.≤ m → n Nat.≤ n′ → InRange m n α → InRange m′ n′ α
inRange-mono α lo hi (p , q) = Nat.≤-trans lo p , Nat.≤-trans q hi

-- Every unification variable of the type has its index in [lo, hi).
data UVarsIn (lo hi : ℕ) : ∀ {κ x} → Ty κ x → Set where
  ⟨_⟩    : UVarsIn lo hi s → UVarsIn lo hi ⟨ s ⟩
  `⊤     : UVarsIn lo hi `⊤
  _⟨_⟩→_ : UVarsIn lo hi T → (a : Arr) → UVarsIn lo hi U → UVarsIn lo hi (T ⟨ a ⟩→ U)
  _⊗⟨_⟩_ : UVarsIn lo hi T → (d : Dir) → UVarsIn lo hi U → UVarsIn lo hi (T ⊗⟨ d ⟩ U)
  _⊕_    : UVarsIn lo hi T → UVarsIn lo hi U → UVarsIn lo hi (T ⊕ U)

  `_     : (x : 𝔽 n) → UVarsIn lo hi (` x)
  end    : UVarsIn lo hi (end {n} p)
  msg    : UVarsIn lo hi T → UVarsIn lo hi (msg {n} p T)
  brn    : UVarsIn lo hi s₁ → UVarsIn lo hi s₂ → UVarsIn lo hi (brn p s₁ s₂)
  mu     : UVarsIn lo hi s → UVarsIn lo hi (mu s)
  _;_ : UVarsIn lo hi s₁ → UVarsIn lo hi s₂ → UVarsIn lo hi (s₁ ; s₂)
  skip   : UVarsIn lo hi (skip {n})
  ret    : UVarsIn lo hi (ret {n})
  acq    : UVarsIn lo hi (acq {n})

  ``_    : ∀ {α} → InRange lo hi α → UVarsIn lo hi (``_ {n} α)

uvarsIn-mono : ∀ {κ x} {t : Ty κ x} → m′ Nat.≤ m → n Nat.≤ n′ →
  UVarsIn m n t → UVarsIn m′ n′ t
uvarsIn-mono lo hi ⟨ u ⟩ = ⟨ uvarsIn-mono lo hi u ⟩
uvarsIn-mono lo hi `⊤ = `⊤
uvarsIn-mono lo hi (u ⟨ a ⟩→ v) = uvarsIn-mono lo hi u ⟨ a ⟩→ uvarsIn-mono lo hi v
uvarsIn-mono lo hi (u ⊗⟨ d ⟩ v) = uvarsIn-mono lo hi u ⊗⟨ d ⟩ uvarsIn-mono lo hi v
uvarsIn-mono lo hi (u ⊕ v) = uvarsIn-mono lo hi u ⊕ uvarsIn-mono lo hi v
uvarsIn-mono lo hi (` x) = ` x
uvarsIn-mono lo hi end = end
uvarsIn-mono lo hi (msg u) = msg (uvarsIn-mono lo hi u)
uvarsIn-mono lo hi (brn u v) = brn (uvarsIn-mono lo hi u) (uvarsIn-mono lo hi v)
uvarsIn-mono lo hi (mu u) = mu (uvarsIn-mono lo hi u)
uvarsIn-mono lo hi (u ; v) = uvarsIn-mono lo hi u ; uvarsIn-mono lo hi v
uvarsIn-mono lo hi skip = skip
uvarsIn-mono lo hi ret = ret
uvarsIn-mono lo hi acq = acq
uvarsIn-mono lo hi (``_ {α = α} r) = `` inRange-mono α lo hi r

-- A solved type has no unification variables at all, hence is in every window.
solved⇒uvarsIn : ∀ {κ x} {t : Ty κ x} → SolvedTy t → UVarsIn m n t
solved⇒uvarsIn ⟨ st ⟩ = ⟨ solved⇒uvarsIn st ⟩
solved⇒uvarsIn `⊤ = `⊤
solved⇒uvarsIn (st ⟨ a ⟩→ su) = solved⇒uvarsIn st ⟨ a ⟩→ solved⇒uvarsIn su
solved⇒uvarsIn (st ⊗⟨ d ⟩ su) = solved⇒uvarsIn st ⊗⟨ d ⟩ solved⇒uvarsIn su
solved⇒uvarsIn (st ⊕ su) = solved⇒uvarsIn st ⊕ solved⇒uvarsIn su
solved⇒uvarsIn (` x) = ` x
solved⇒uvarsIn end = end
solved⇒uvarsIn (msg st) = msg (solved⇒uvarsIn st)
solved⇒uvarsIn (brn s₁ s₂) = brn (solved⇒uvarsIn s₁) (solved⇒uvarsIn s₂)
solved⇒uvarsIn (mu st) = mu (solved⇒uvarsIn st)
solved⇒uvarsIn (s₁ ; s₂) = solved⇒uvarsIn s₁ ; solved⇒uvarsIn s₂
solved⇒uvarsIn skip = skip
solved⇒uvarsIn acq = acq
solved⇒uvarsIn ret = ret

------------------------------------------------------------------------
-- Lifting to constraints

-- Data, not a function, so that Agda recovers the window and the constraint
-- from a proof (see the note at the end of Scope-STATUS.md).
data UVarsInC (lo hi : ℕ) : Constraint → Set where
  C-Eq  : UVarsIn lo hi T → UVarsIn lo hi U → UVarsInC lo hi (C-Eq T U)
  C-Mob : UVarsIn lo hi T → UVarsInC lo hi (C-Mob T)

UVarsInΔ : ℕ → ℕ → CSet → Set
UVarsInΔ m n Δ = All (UVarsInC m n) Δ

uvarsInC-mono : ∀ {C} → m′ Nat.≤ m → n Nat.≤ n′ → UVarsInC m n C → UVarsInC m′ n′ C
uvarsInC-mono lo hi (C-Eq p q) = C-Eq (uvarsIn-mono lo hi p) (uvarsIn-mono lo hi q)
uvarsInC-mono lo hi (C-Mob p) = C-Mob (uvarsIn-mono lo hi p)

uvarsInΔ-mono : m′ Nat.≤ m → n Nat.≤ n′ → UVarsInΔ m n Δ → UVarsInΔ m′ n′ Δ
uvarsInΔ-mono lo hi [] = []
uvarsInΔ-mono lo hi (p ∷ ps) = uvarsInC-mono lo hi p ∷ uvarsInΔ-mono lo hi ps

uvarsInΔ-++ : UVarsInΔ m n Δ₁ → UVarsInΔ m n Δ₂ → UVarsInΔ m n (Δ₁ ++ Δ₂)
uvarsInΔ-++ [] q = q
uvarsInΔ-++ (p ∷ ps) q = p ∷ uvarsInΔ-++ ps q

------------------------------------------------------------------------
-- Substitution agreement on a scope

-- Two substitutions agree on the window [m, n).  This is a record (not a bare
-- function type) so that Agda can invert it: from `Agree m n σ₁ σ₂` the four
-- arguments are recovered, which a defined function type would not give.
record Agree (m n : ℕ) (σ₁ σ₂ : UV.Sub) : Set where
  constructor agree
  field
    ap≡ : ∀ α → m Nat.≤ UV.var α → UV.var α Nat.< n → UV.ap σ₁ α ≡ UV.ap σ₂ α

open Agree public

agree-sym : Agree m n σ₁ σ₂ → Agree m n σ₂ σ₁
agree-sym ag = agree λ α lo hi → sym (ap≡ ag α lo hi)

-- Every two substitutions agree on the empty window.
agree-empty : Agree n n σ₁ σ₂
agree-empty = agree λ α lo hi → contradiction (Nat.≤-trans hi lo) (Nat.n≮n _)

subTy-agree : ∀ {κ x} {t : Ty κ x} → Agree m n σ₁ σ₂ → UVarsIn m n t →
  subTy t σ₁ ≡ subTy t σ₂
subTy-agree ag ⟨ u ⟩ = cong ⟨_⟩ (subTy-agree ag u)
subTy-agree ag `⊤ = refl
subTy-agree ag (u ⟨ a ⟩→ v) = cong₂ _⟨ a ⟩→_ (subTy-agree ag u) (subTy-agree ag v)
subTy-agree ag (u ⊗⟨ d ⟩ v) = cong₂ _⊗⟨ d ⟩_ (subTy-agree ag u) (subTy-agree ag v)
subTy-agree ag (u ⊕ v) = cong₂ _⊕_ (subTy-agree ag u) (subTy-agree ag v)
subTy-agree ag (` x) = refl
subTy-agree ag end = refl
subTy-agree ag (msg u) = cong (msg _) (subTy-agree ag u)
subTy-agree ag (brn u v) = cong₂ (brn _) (subTy-agree ag u) (subTy-agree ag v)
subTy-agree ag (mu u) = cong mu (subTy-agree ag u)
subTy-agree ag (u ; v) = cong₂ _;_ (subTy-agree ag u) (subTy-agree ag v)
subTy-agree ag skip = refl
subTy-agree ag ret = refl
subTy-agree ag acq = refl
subTy-agree ag (``_ {α = α} (p , q)) rewrite ap≡ ag α p q = refl

solvedCst-agree : ∀ {C} → Agree m n σ₁ σ₂ → UVarsInC m n C →
  SolvedCst C σ₁ → SolvedCst C σ₂
solvedCst-agree ag (C-Eq p q) sc =
  subst₂ _≃_ (subTy-agree ag p) (subTy-agree ag q) sc
solvedCst-agree ag (C-Mob p) sc = subst Mobile (subTy-agree ag p) sc

solvedΔ-agree : Agree m n σ₁ σ₂ → UVarsInΔ m n Δ → SolvedΔ Δ σ₁ → SolvedΔ Δ σ₂
solvedΔ-agree {Δ = []} ag [] [] = []
solvedΔ-agree {Δ = C ∷ Δ} ag (u ∷ us) (p ∷ ps) =
  solvedCst-agree ag u p ∷ solvedΔ-agree ag us ps

-- Constraints without unification variables are solved by every substitution.
solvedΔ-indep : UVarsInΔ n n Δ → SolvedΔ Δ σ₁ → SolvedΔ Δ σ₂
solvedΔ-indep = solvedΔ-agree agree-empty
