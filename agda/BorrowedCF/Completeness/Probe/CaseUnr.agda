-- | Red-team probe, NOW A POSITIVE REGRESSION TEST: an unrestricted variable
--   shared by the scrutinee and a branch.  This was COUNTEREXAMPLE 1 against
--   `Complete⇐`/`Complete⇒`; the base rule has been repaired, so the term is now
--   algorithmically typable and the file records both derivations.
--
--   A-Case types the branches under `join p/s (` 0) (wk (γ ↓ ∁ (fv e)))`, i.e.
--   it deletes from the branch structure EVERY variable occurring in the
--   scrutinee.  The declarative T-Case splits `γ` into γ₁ (scrutinee) and γ₂
--   (branches), and `T-Weaken` lets γ₁ and γ₂ share an UNRESTRICTED variable
--   (`∥′-dup`).  The term below does exactly that.
module BorrowedCF.Completeness.Probe.CaseUnr where

open import Data.Fin.Subset as S using (Subset; ∁; _∈_; ⁅_⁆; _∪_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; ∉⊥)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain using (dom; ≼⇒dom⊆; _↓_)
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base

open Fin.Patterns

------------------------------------------------------------------------
-- The witness.  One unrestricted variable u : `⊤, structure γ = ` u.

Γ₀ : Ctx 1
Γ₀ = `⊤ ⸴ []

γ₀ : Struct 1
γ₀ = ` 0F

unr-⊤ : Unr (Γ₀ ﹫ 0F)
unr-⊤ = `⊤

-- case (inj₁ u) of { _ → u ; _ → u }   -- u free in the scrutinee AND in both branches
e₀ : Tm 1
e₀ = `case (`inj L (` 0F)) `of⟨ ` 1F ; ` 1F ⟩

------------------------------------------------------------------------
-- 1.  The declarative derivation.

branch : (`⊤ ⸴ Γ₀) ; (` 0F ∥ ` 1F) ⊢ ` 1F ∶ `⊤ ∣ ℙ
branch = T-Weaken
  (≼-trans (≼-refl (≈-sym ∥-unit₁)) (≼-cong-∥ (≼-∅ (` `⊤)) (≼-refl ≈-refl)))
  (T-Var 1F refl)

decl : Γ₀ ; γ₀ ⊢ e₀ ∶ `⊤ ∣ ℙ
decl = T-Weaken (≼-refl (≈-sym (∥-dup (` unr-⊤))))
                (T-Case par (T-Inj (T-Var 0F refl)) branch branch)

------------------------------------------------------------------------
-- 2.  The side conditions of Complete⇐ / Complete⇒ all hold.

solvedCtx : SolvedCtx Γ₀
solvedCtx 0F = `⊤

solvedTm : SolvedTm e₀
solvedTm = `case (`inj (` 0F)) `of⟨ ` 1F ; ` 1F ⟩

linear : LinStruct Γ₀ γ₀
linear 0F ¬u = ⊥-elim (¬u `⊤)

------------------------------------------------------------------------
-- 3.  POSITIVE TEST (2026-09-08, after the base repair).
--
--   A-Case now restricts the branches to `fvClose (fv e₁) ∪ fvClose (fv e₂)`
--   instead of `∁ (fv e)`, so `u` survives in the branch structure and the term
--   IS algorithmically typable.  Everything below is the derivation the repaired
--   rule produces; it fails to compile if the branch restriction regresses.

Δ₀ : CSet
Δ₀ = C-Eq `⊤ `⊤ ∷ C-Eq `⊤ `⊤ ∷ C-Eq `⊤ `⊤ ∷ []

-- scrutinee: A-Inj is a checking rule, so the inference goes through A-Ann.
scrut : Γ₀ ; γ₀ / 0 ⊢ (`inj L (` 0F)) ⇒ `⊤ ⊕ `⊤ ∣ ℙ ↑ C-Eq `⊤ `⊤ ∷ [] / 0
scrut = A-Ann (A-Inj {i = L} (A-Check (A-Var (≼-refl ≈-refl))))

-- the branch keeps `u` (index 1F under the binder) in its structure
brc : (`⊤ ⸴ Γ₀) ; ((` 0F) ∥ (` 1F)) / 0 ⊢ (` 1F) ⇒ `⊤ ∣ ℙ ↑ [] / 0
brc = A-Var (≼-trans (≼-refl (≈-sym ∥-unit₁))
                     (≼-cong-∥ (≼-∅ (` `⊤)) (≼-refl ≈-refl)))

alg : Γ₀ ; γ₀ / 0 ⊢ e₀ ⇐ `⊤ ∣ ℙ ↑ Δ₀ / 0
alg = A-Check (A-Case par (≼-refl (≈-sym (∥-dup (` unr-⊤)))) scrut brc brc)

solvedΔ₀ : ∀ {σ} → SolvedΔ Δ₀ σ
solvedΔ₀ = `⊤ ∷ `⊤ ∷ `⊤ ∷ []
