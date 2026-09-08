-- | Red-team probe: A-LetPair (and, identically, the new A-Let) hard-codes a
--   SEQUENTIAL structure between the pair components and the outer context,
--
--       T₁ ⸴ T₂ ⸴ Γ ; (join d (` 0F) (` 1F) ; wk (wk γ₂)) ⊢ e₂ ⇒ U
--
--   while the declarative T-LetPair takes a `p/s` and uses
--   `join p/s (join d (` 0F) (` 1F)) (wk (wk γ₂))`, so for `p/s = par` the body
--   may use an outer variable BEFORE a component.  `before-mono-≼` forbids that
--   under the algorithmic (sequential) structure.
module BorrowedCF.Completeness.Probe.LetPairPar where

open import Data.Fin.Subset using (⁅_⁆)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain using (_↓_)
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (before; _∈ₘ_; before-mono-≼; ¬mobile-noAcq; NoAcq)
open import BorrowedCF.Completeness.Base

open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- 1.  The witness.
--
--   p : ⟨ end ‼ ⟩ ⊗¹ `⊤     (index 0F)      z : ⟨ end ⁇ ⟩   (index 1F)
--   γ = ` p ∥ ` z
--   e = let⊗ p in (z ⊗ c₀)      -- the body puts z BEFORE the component c₀

Γ₀ : Ctx 2
Γ₀ = (⟨ end ‼ ⟩ ⊗⟨ 𝟙 ⟩ `⊤) ⸴ ⟨ end ⁇ ⟩ ⸴ []

γ₀ : Struct 2
γ₀ = (` 0F) ∥ (` 1F)

e₀ : Tm 2
e₀ = `let⊗ (` 0F) `in ((` 3F) ⊗ (` 0F))

T₀ : 𝕋
T₀ = ⟨ end ⁇ ⟩ ⊗⟨ L ⟩ ⟨ end ‼ ⟩

------------------------------------------------------------------------
-- 2.  Declarative derivation (with p/s = par at the let⊗).

body-decl : (⟨ end ‼ ⟩ ⸴ `⊤ ⸴ Γ₀) ; (((` 0F) ∥ (` 1F)) ∥ (` 3F))
              ⊢ ((` 3F) ⊗ (` 0F)) ∶ T₀ ∣ ℙ
body-decl = T-Weaken
  (≼-trans ;-≼-∥
    (≼-trans (≼-refl ∥-comm)
      (≼-cong-∥ (≼-trans (≼-refl (≈-sym ∥-unit₂))
                         (≼-cong-∥ (≼-refl ≈-refl) (≼-∅ (` `⊤))))
                (≼-refl ≈-refl))))
  (T-Pair seq seq (T-Var 3F refl) (T-Var 0F refl))

decl : Γ₀ ; γ₀ ⊢ e₀ ∶ T₀ ∣ ℙ
decl = T-LetPair par {γ₁ = ` 0F} {γ₂ = ` 1F} (T-Var 0F refl) body-decl

------------------------------------------------------------------------
-- 3.  Side conditions of Complete⇐.

solvedCtx : SolvedCtx Γ₀
solvedCtx 0F = ⟨ end ⟩ ⊗⟨ 𝟙 ⟩ `⊤
solvedCtx 1F = ⟨ end ⟩

solvedTm : SolvedTm e₀
solvedTm = `let⊗ (` 0F) `in ((` 3F) ⊗ (` 0F))

solvedTy : SolvedTy T₀
solvedTy = ⟨ end ⟩ ⊗⟨ L ⟩ ⟨ end ⟩

linear : LinStruct Γ₀ γ₀
linear 0F _ = Nat.s≤s Nat.z≤n
linear 1F _ = Nat.s≤s Nat.z≤n

------------------------------------------------------------------------
-- 4.  POSITIVE TEST (2026-09-08, after C6c's repair).
--
--   A-LetPair now takes a `p/s` and gives the body
--   `join p/s (join d (` 0F) (` 1F)) (wk (wk γ₂))`, so `p/s = par` mirrors the
--   declarative T-LetPair above and the term IS algorithmically typable.
--   Before the repair the body structure was hard-wired to `;`, which made
--   `before 0F 3F` unavoidable and refuted `Complete⇐`; this file then carried
--   `refute-Complete⇐`.  It now carries the derivation instead, and fails to
--   compile if the body join regresses to `;`.

Δ₀ : CSet
Δ₀ = C-Eq T₀ T₀ ∷ C-Eq ⟨ end ⁇ ⟩ ⟨ end ⁇ ⟩ ∷ C-Eq ⟨ end ‼ ⟩ ⟨ end ‼ ⟩ ∷ []

--  γ_b ↓ ⁅ 3F ⁆ ≈ ` 3F  and  γ_b ↓ ⁅ 0F ⁆ ≈ ` 0F, with γ_b the body structure
--  ((` 0F) ∥ (` 1F)) ∥ ([] ∥ (` 3F)).
cA : ∀ {Γ′ : Ctx 4} → Γ′ ∶ (([] ∥ []) ∥ ([] ∥ (` 3F))) ≈ (` 3F)
cA = ≈-trans (∥-cong ∥-unit₁ ∥-unit₁) ∥-unit₁

cB : ∀ {Γ′ : Ctx 4} → Γ′ ∶ (((` 0F) ∥ []) ∥ ([] ∥ [])) ≈ (` 0F)
cB = ≈-trans (∥-cong ∥-unit₂ ∥-unit₁) ∥-unit₂

body-alg : (⟨ end ‼ ⟩ ⸴ `⊤ ⸴ Γ₀) ; (((` 0F) ∥ (` 1F)) ∥ ([] ∥ (` 3F))) / 0
             ⊢ ((` 3F) ⊗ (` 0F)) ⇒ T₀ ∣ ℙ ↑ (C-Eq ⟨ end ⁇ ⟩ ⟨ end ⁇ ⟩ ∷ C-Eq ⟨ end ‼ ⟩ ⟨ end ‼ ⟩ ∷ []) / 0
body-alg = A-Ann (A-Pair seq
  (≼-trans (≼-refl (;-cong cA cB))
    (≼-trans ;-≼-∥
      (≼-trans (≼-refl ∥-comm)
        (≼-cong-∥ (≼-trans (≼-refl (≈-sym ∥-unit₂))
                           (≼-cong-∥ (≼-refl ≈-refl) (≼-∅ (` `⊤))))
                  (≼-refl (≈-sym ∥-unit₁))))))
  (λ _ → refl)
  (A-Check (A-Var (≼-refl (≈-sym cA))))
  (A-Check (A-Var (≼-refl (≈-sym cB)))))

alg : Γ₀ ; γ₀ / 0 ⊢ e₀ ⇐ T₀ ∣ ℙ ↑ Δ₀ / 0
alg = A-Check (A-LetPair par (≼-refl (∥-cong ∥-unit₂ ∥-unit₁))
                 (A-Var (≼-refl (≈-sym ∥-unit₂)))
                 body-alg)

solvedΔ₀ : ∀ {σ} → SolvedΔ Δ₀ σ
solvedΔ₀ = ≃-refl ∷ ≃-refl ∷ ≃-refl ∷ []
