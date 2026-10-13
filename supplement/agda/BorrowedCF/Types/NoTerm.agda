-- | `NoTerm`: a session with NO TERMINATOR leaf -- neither `ret` nor `end`.
--
--   `Simulation/Support/Theorems/B1VacProbe.agda` has `NoRet` (no `ret`), and
--   that is what PLAN.md §6's mobility argument used.  It is too weak:
--   `Bounded s′` in `Mobile ⟨ acq ; s′ ⟩` is satisfied by an `end` tip as well
--   as by a `ret` tip, so `NoRet u` does not stop a group chain `u ; ret` from
--   carrying a Mobile handle followed by a second one
--   (`Examples/StrictGroupGap.agda`'s `mobile-head-alone-refuted`).
--
--   `NoTerm` is the correct premise, and it is exactly what a `New`-derived
--   session supplies: `New` admits neither `acq` nor `ret` nor `end`.  The
--   payoff is `bounded-tail-skips`: in a chain `w ; r ≃ q ; τ` whose only
--   terminator is the trailing atom `τ`, a BOUNDED `w` must already reach it,
--   so `r` skips.  That is "a group's terminator ends the group", which is
--   what `Position/Crux.agda`'s `mobile-head-alone` needs.
--
--   The module is deliberately term-syntax-free (the session-level `_⋯_` of
--   `Types/Substitution.agda` cannot be in scope with the term-level one), and
--   it exports NO constructor names: clients get `new⇒noTerm`,
--   `noTerm-;-fst/snd`, `noTerm-acq`, `noTerm-≃`, `termAtom-ret/end` and
--   `bounded-tail-skips`, none of which clash with the session constructors.
module BorrowedCF.Types.NoTerm where

open import Relation.Binary.Construct.Closure.Symmetric as Sym
  using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)

open Bin using (_Respects_)
open Nat.Variables

------------------------------------------------------------------------
-- 1.  The predicate.

data NoTerm {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoTerm (` x)
  acq  : NoTerm (acq {n})
  skip : NoTerm (skip {n})
  msg  : NoTerm (msg {n} p T)
  brn  : NoTerm s₁ → NoTerm s₂ → NoTerm (brn p s₁ s₂)
  mu   : NoTerm s → NoTerm (mu s)
  _;_  : NoTerm s₁ → NoTerm s₂ → NoTerm (s₁ ; s₂)

¬noTerm-ret : ¬ NoTerm (ret {n})
¬noTerm-ret ()

¬noTerm-end : ¬ NoTerm (end {n} p)
¬noTerm-end ()

noTerm-;-fst : NoTerm (s₁ ; s₂) → NoTerm s₁
noTerm-;-fst (x ; _) = x

noTerm-;-snd : NoTerm (s₁ ; s₂) → NoTerm s₂
noTerm-;-snd (_ ; y) = y

-- The two shapes clients build.
noTerm-acq : NoTerm s → NoTerm (acq {n} ; s)
noTerm-acq ns = acq ; ns

new⇒noTerm : New s → NoTerm s
new⇒noTerm New.`-        = `-
new⇒noTerm New.msg       = msg
new⇒noTerm (New.brn x y) = brn (new⇒noTerm x) (new⇒noTerm y)
new⇒noTerm (New.mu x)    = mu (new⇒noTerm x)
new⇒noTerm (x New.; y)   = new⇒noTerm x ; new⇒noTerm y
new⇒noTerm New.skip      = skip

------------------------------------------------------------------------
-- 2.  Substitution and `≃` (a literal copy of `GroupOrder.NoAcq`'s).

noTerm-⋯ᵣ : NoTerm s → {ρ : m →ᵣ n} → NoTerm (s ⋯ ρ)
noTerm-⋯ᵣ `-        = `-
noTerm-⋯ᵣ acq       = acq
noTerm-⋯ᵣ skip      = skip
noTerm-⋯ᵣ msg       = msg
noTerm-⋯ᵣ (brn x y) = brn (noTerm-⋯ᵣ x) (noTerm-⋯ᵣ y)
noTerm-⋯ᵣ (mu x)    = mu (noTerm-⋯ᵣ x)
noTerm-⋯ᵣ (x ; y)   = noTerm-⋯ᵣ x ; noTerm-⋯ᵣ y

noTerm-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoTerm s → {ϕ : m –[ K ]→ n} →
           (∀ x → NoTerm (`/id (ϕ x))) → NoTerm (s ⋯ ϕ)
noTerm-⋯ `- ∀ϕ = ∀ϕ _
noTerm-⋯ acq ∀ϕ = acq
noTerm-⋯ skip ∀ϕ = skip
noTerm-⋯ msg ∀ϕ = msg
noTerm-⋯ (brn x y) ∀ϕ = brn (noTerm-⋯ x ∀ϕ) (noTerm-⋯ y ∀ϕ)
noTerm-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noTerm-⋯ x λ where
  zero    → subst NoTerm (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoTerm (wk-`/id _) (noTerm-⋯ᵣ (∀ϕ z))
noTerm-⋯ (x ; y) ∀ϕ = noTerm-⋯ x ∀ϕ ; noTerm-⋯ y ∀ϕ

noTerm-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} →
             NoTerm (s ⋯ ϕ) → NoTerm s
noTerm-⋯⁻¹ {s = ` _} x = `-
noTerm-⋯⁻¹ {s = acq} x = acq
noTerm-⋯⁻¹ {s = skip} x = skip
noTerm-⋯⁻¹ {s = msg p t} x = msg
noTerm-⋯⁻¹ {s = end p} x = ⊥-elim (¬noTerm-end x)
noTerm-⋯⁻¹ {s = ret} x = ⊥-elim (¬noTerm-ret x)
noTerm-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noTerm-⋯⁻¹ x) (noTerm-⋯⁻¹ y)
noTerm-⋯⁻¹ {s = mu s} (mu x) = mu (noTerm-⋯⁻¹ x)
noTerm-⋯⁻¹ {s = _ ; _} (x ; y) = noTerm-⋯⁻¹ x ; noTerm-⋯⁻¹ y

noTerm-≃ : NoTerm {n} Respects _≃_
noTerm-≃ ≋-refl na = na
noTerm-≃ (x ◅ xs) na = noTerm-≃ xs (go x na)
  where
  go : NoTerm {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noTerm-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (fwd (≃𝕊-msg eq))  msg       = msg
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noTerm-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y
  go (bwd (≃𝕊-msg eq))  msg       = msg
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)

------------------------------------------------------------------------
-- 3.  THE PAYOFF.

noTerm⊥bounded : NoTerm s → Bounded s → ⊥
noTerm⊥bounded (nt₁ ; nt₂) (b ;₁ _) = noTerm⊥bounded nt₁ b
noTerm⊥bounded (nt₁ ; nt₂) (-;₂ b)  = noTerm⊥bounded nt₂ b
noTerm⊥bounded (mu nt)     (mu b)   = noTerm⊥bounded nt b
noTerm⊥bounded (brn nt₁ _) (brn b₁ _) = noTerm⊥bounded nt₁ b₁

-- A trailing terminator atom, packaged so that clients need no `Atom` in
-- scope (its `ret` / `end` constructors clash with the session ones).
data TermAtom {n} : 𝕊 n → Set where
  ret : TermAtom (ret {n})
  end : TermAtom (end {n} p)

termAtom-ret : TermAtom (ret {n})
termAtom-ret = ret

termAtom-end : TermAtom (end {n} p)
termAtom-end = end

termAtom⇒atom : {τ : 𝕊 n} → TermAtom τ → Atom τ
termAtom⇒atom ret = ret
termAtom⇒atom end = end

-- A GROUP'S TERMINATOR ENDS THE GROUP.  If the whole chain `q ; τ` has its
-- only terminator in the trailing atom `τ`, then a BOUNDED prefix `w` already
-- swallows it and everything after `w` skips.
bounded-tail-skips : {w r q τ : 𝕊 n} →
  TermAtom τ → NoTerm q → Bounded w → w ; r ≃ q ; τ → Skips r
bounded-tail-skips A NTq Bw eq with atom-;-unsnoc (termAtom⇒atom A) eq
... | inj₁ Sk = Sk
... | inj₂ (r′ , wr′≃q , _) =
  ⊥-elim (noTerm⊥bounded (noTerm-;-fst (noTerm-≃ (≃-sym wr′≃q) NTq)) Bw)

-- The `cons-ret/acq` step of the `BindCtx` induction: in `s₁ ; s₂ ≃ q ; τ`
-- with a NON-SKIPPING `s₂`, the trailing terminator sits inside `s₂`, so `s₁`
-- is a `NoTerm` prefix of `q` and `s₂` is `q′ ; τ` for a `NoTerm` `q′`.
noTerm-split : {s₁ s₂ q τ : 𝕊 n} →
  TermAtom τ → NoTerm q → ¬ Skips s₂ → s₁ ; s₂ ≃ q ; τ →
  Σ[ q′ ∈ 𝕊 n ] NoTerm s₁ × NoTerm q′ × (s₂ ≃ q′ ; τ)
noTerm-split A NTq ¬sk eq with atom-;-unsnoc (termAtom⇒atom A) eq
... | inj₁ Sk = ⊥-elim (¬sk Sk)
... | inj₂ (q′ , s₁q′≃q , q′τ≃s₂) =
  let NT = noTerm-≃ (≃-sym s₁q′≃q) NTq in
  q′ , noTerm-;-fst NT , noTerm-;-snd NT , ≃-sym q′τ≃s₂
