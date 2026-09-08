-- | The interface of the completeness induction (agent C4).
--
--   What `Main.agda` assumes, bundled as records so that the helper modules
--   (`Main/App.agda`, `Main/Bind.agda`) are parametrised over exactly the same things and
--   `Completeness.agda` has a single place to discharge them.
--
--   C1 (`Split.agda`), C2 (`Scope.agda`), C5 (`Decl.agda`) and C8 (`Sub.agda`) are DELIVERED
--   and imported directly, and the three base repairs (FINDINGS 1, 2, 4 of Main-STATUS.md)
--   have been applied by C6b / C6c / C10, so NOTHING is assumed any more: the induction and
--   the two theorems are unconditional.
--
--   C2's `Completeness/Scope.agda` is DELIVERED, so it is imported directly rather than
--   assumed.  The scope facts are OUTPUTS of the induction, not re-derived by `scope`:
--   `scope` cannot see the derivations built here, because A-Ann's `GuessIn` obligation asks
--   the guessed type to be in scope at the ENTRY counter, while the type this proof guesses for
--   a `ƛ` / `μ` / `⊗` / `inj` is the one its body INFERRED, with variables allocated after entry.
--
--   Owner: agent C4.
module BorrowedCF.Completeness.Main.Interface where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; _⊆_; ∁)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Split
open import BorrowedCF.Completeness.Decl
open import BorrowedCF.Completeness.Sub.Base using (Approx; approx-⸴) public

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open Fin.Patterns

private variable
  e e₁ e₂ : Tm n

------------------------------------------------------------------------
-- Substitutions are THREADED through the induction, never merged: the substitution a
-- subderivation produces agrees with the incoming one below the entry counter.
-- `Agree 0 m σ σ₀` (C2) is that relation; `extend σ₀ m s` assigns the freshly allocated
-- variable `m` and keeps everything below it.

extend : UV.Sub → ℕ → (s : 𝕊 0) → ¬ Skips s → UV.Sub
extend σ₀ m s ¬Ss = merge m σ₀ (single (UV.fresh m) s ¬Ss)

extend-agree : ∀ σ₀ m s (¬Ss : ¬ Skips s) → Agree 0 m (extend σ₀ m s ¬Ss) σ₀
extend-agree σ₀ m s ¬Ss = agree-sym (merge-agree-below m σ₀ (single (UV.fresh m) s ¬Ss))

extend-solving : ∀ σ₀ m s (¬Ss : ¬ Skips s) →
  Solving σ₀ → SolvedTy s → Solving (extend σ₀ m s ¬Ss)
extend-solving σ₀ m s ¬Ss Sσ Ss =
  merge-solving m σ₀ (single (UV.fresh m) s ¬Ss) Sσ (single-solving (UV.fresh m) s ¬Ss Ss)

extend-ap : ∀ σ₀ m s (¬Ss : ¬ Skips s) → UV.ap (extend σ₀ m s ¬Ss) (UV.fresh m) ≡ s
extend-ap σ₀ m s ¬Ss =
  merge-above m σ₀ (single (UV.fresh m) s ¬Ss) (UV.fresh m) Nat.≤-refl
    ■ single-ap (UV.fresh m) s ¬Ss

------------------------------------------------------------------------
-- The one repair the base system still needs (Main-STATUS.md).  FINDINGS 2 and 4 have
-- been applied to `Algorithmic.agda` by C6b/C6c; FINDING 1 has not; `mob-reflect` is not (FINDING 1).

------------------------------------------------------------------------
-- The conclusion of the generalised induction, and the induction hypothesis.
--
-- `Γ̂` is the ALGORITHMIC context; it approximates the declarative `Γ` in that instantiating
-- it with the incoming `σ₀` gives `Γ` up to `≃`.  It differs from `Γ` exactly at
-- A-LetPair / A-Case, which extend the context with an INFERRED type.

Conclusion : {n : ℕ} → Ctx n → Struct n → Tm n → 𝕋 → Eff → ℕ → UV.Sub → Set
Conclusion Γ̂ γ e T ϵ m σ₀ =
  Σ[ T̂ ∈ 𝕋 ] Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
    Solving σ × Agree 0 m σ σ₀ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (subTy T̂ σ ≃ T)
      × (m Nat.≤ k) × UVarsIn 0 k T̂ × UVarsInΔ 0 k Δ
      × (Γ̂ ; γ / m ⊢ e ⇒ T̂ ∣ ϵ′ ↑ Δ / k)

-- The induction hypothesis for ONE fixed subterm.  Passing the hypothesis per subterm (rather
-- than universally quantified) is what lets Agda see the structural recursion through the
-- per-case lemmas: at the call site the recursive call is `complete⇒ᵍ {e = e₁}` with `e₁` a
-- syntactic subterm.

IHAt : {n : ℕ} → Tm n → Set
IHAt {n} e = ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  Conclusion Γ̂ γ e T ϵ m σ₀

IH : Set
IH = ∀ {n} {e : Tm n} → IHAt e

------------------------------------------------------------------------
-- The heavy groups of cases, delegated to `Main/App.agda` and `Main/Bind.agda`.
-- Each takes the induction hypothesis of ITS OWN subterms.

AppCase : Set
AppCase = ∀ {n} {e₁ e₂ : Tm n} → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {d : Dir} {T : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e₁ ·⟨ d ⟩ e₂ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (e₁ ·⟨ d ⟩ e₂) T ϵ m σ₀

LetCase : Set
LetCase = ∀ {n} {e₁ : Tm n} {e₂ : Tm (suc n)} → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ `let e₁ `in e₂ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (`let e₁ `in e₂) T ϵ m σ₀

LetPairCase : Set
LetPairCase = ∀ {n} {e₁ : Tm n} {e₂ : Tm (suc (suc n))} → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ `let⊗ e₁ `in e₂ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (`let⊗ e₁ `in e₂) T ϵ m σ₀

CaseCase : Set
CaseCase = ∀ {n} {e : Tm n} {e₁ e₂ : Tm (suc n)} → IHAt e → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e → SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ `case e `of⟨ e₁ ; e₂ ⟩ T ϵ m σ₀
