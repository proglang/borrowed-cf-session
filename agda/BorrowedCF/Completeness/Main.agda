-- | Algorithmic completeness: the main induction (agent C4).
--
--   The proof is a structural induction on the TERM.  The declarative rules T-Conv and
--   T-Weaken are absorbed by the inversion lemmas of `Terms/Base.agda` (plus `inv-ƛ`/`inv-μ`
--   in `Main/Base.agda`), so every case starts from the inversion of its term former.
--
--   Only INFERENCE is proved (`complete⇒ᵍ`); checking is `A-Check` on top of it, which is why
--   the "check the argument against a type that still contains the function's unification
--   variables" problem never arises: the `C-Eq` that A-Check emits is discharged at the END,
--   under the substitution both subderivations have already agreed on.
--
--   The statement is GENERALISED in two ways over `Completeness/Base.agda`:
--     * the algorithmic context `Γ̂` need only APPROXIMATE the declarative `Γ`
--       (`subTy (Γ̂ ﹫ x) σ₀ ≃ Γ ﹫ x`), because A-LetPair and A-Case extend the context with
--       an INFERRED type;
--     * the substitution is THREADED: each subderivation starts from the previous one's
--       substitution and agrees with it below the entry counter (`Agree 0 m σ σ₀`).
--
--   The module is parametrised only over the two heavy groups of cases, which live in
--   `Main/App.agda` and `Main/Bind.agda` (a module cannot depend on itself, and the cases need
--   the induction hypothesis).  `Completeness.agda` instantiates it.  NOTHING else is assumed:
--   after the base repairs of C6b / C6c / C10 the induction is unconditional.
--
--   Owner: agent C4.
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Decl

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Interface

module BorrowedCF.Completeness.Main
  (app-case     : AppCase)
  (let-case     : LetCase)
  (letpair-case : LetPairCase)
  (case-case    : CaseCase)
  where

open import BorrowedCF.Completeness.Main.Simple
open import BorrowedCF.Completeness.Main.Abs
open import BorrowedCF.Completeness.Main.Struct

open Nat.Variables

------------------------------------------------------------------------
-- The induction.

complete⇒ᵍ : IH
complete⇒ᵍ {e = ` x} Sσ uΓ ap Se ST lin dv =
  var-case Sσ uΓ ap dv
complete⇒ᵍ {e = K c} Sσ uΓ ap Se ST lin dv =
  const-case Sσ uΓ ap Se ST dv
complete⇒ᵍ {e = ƛ e} Sσ uΓ ap Se ST lin dv =
  abs-case (complete⇒ᵍ {e = e}) Sσ uΓ ap (solvedTm-ƛ Se) ST lin dv
complete⇒ᵍ {e = μ (ƛ e)} Sσ uΓ ap Se ST lin dv =
  absrec-case (complete⇒ᵍ {e = e}) Sσ uΓ ap (solvedTm-μ Se) ST lin dv
complete⇒ᵍ {e = e₁ ·⟨ dr ⟩ e₂} Sσ uΓ ap Se ST lin dv =
  app-case (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
           (proj₁ (solvedTm-· Se)) (proj₂ (solvedTm-· Se)) ST lin dv
complete⇒ᵍ {e = e₁ ; e₂} Sσ uΓ ap Se ST lin dv =
  seq-case (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
           (proj₁ (solvedTm-; Se)) (proj₂ (solvedTm-; Se)) ST lin dv
complete⇒ᵍ {e = e₁ ⊗ e₂} Sσ uΓ ap Se ST lin dv =
  pair-case (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
            (proj₁ (solvedTm-⊗ Se)) (proj₂ (solvedTm-⊗ Se)) ST lin dv
complete⇒ᵍ {e = `let e₁ `in e₂} Sσ uΓ ap Se ST lin dv =
  let-case (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
           (proj₁ (solvedTm-let Se)) (proj₂ (solvedTm-let Se)) ST lin dv
complete⇒ᵍ {e = `let⊗ e₁ `in e₂} Sσ uΓ ap Se ST lin dv =
  letpair-case (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
               (proj₁ (solvedTm-let⊗ Se)) (proj₂ (solvedTm-let⊗ Se)) ST lin dv
complete⇒ᵍ {e = `inj i e} Sσ uΓ ap Se ST lin dv =
  inj-case (complete⇒ᵍ {e = e}) Sσ uΓ ap (solvedTm-inj Se) ST lin dv
complete⇒ᵍ {e = `case e `of⟨ e₁ ; e₂ ⟩} Sσ uΓ ap Se ST lin dv =
  case-case (complete⇒ᵍ {e = e}) (complete⇒ᵍ {e = e₁}) (complete⇒ᵍ {e = e₂}) Sσ uΓ ap
            (proj₁ (solvedTm-case Se)) (proj₁ (proj₂ (solvedTm-case Se))) (proj₂ (proj₂ (solvedTm-case Se))) ST lin dv

-- `μ e` is typable only for `e ≡ ƛ _` (T-AbsRec is the only rule for `μ`).
complete⇒ᵍ {e = μ (` x)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (K c)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (μ e)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (e₁ ·⟨ dr ⟩ e₂)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (e₁ ; e₂)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (e₁ ⊗ e₂)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (`let e₁ `in e₂)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (`let⊗ e₁ `in e₂)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ (`inj i e)} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _
complete⇒ᵍ {e = μ `case e `of⟨ e₁ ; e₂ ⟩} Sσ uΓ ap Se ST lin dv with inv-μ dv
... | _ , _ , _ , _ , _ , () , _

------------------------------------------------------------------------
-- The two theorems of `Completeness/Base.agda`.

complete⇒ : Complete⇒
complete⇒ {Γ = Γ} {γ = γ} {T = T} SΓ Se ST lin dv m
  with T̂ , ϵ′ , Δ , k , σ , Sσ , ag , SΔ , ϵ≤ , ≃T , m≤k , uvT̂ , uvΔ , der
     ← complete⇒ᵍ {Γ̂ = Γ} {m = m} s₀-solving (solvedCtx⇒uvarsInΓ SΓ)
         (λ x → ≃-reflexive (subTy-id (SΓ x) {s₀})) Se ST lin dv
  = T̂ , ϵ′ , Δ , k , σ , Sσ , SΔ , ϵ≤ , ≃T , der

complete⇐ : Complete⇐
complete⇐ {Γ = Γ} {γ = γ} {T = T} SΓ Se ST lin dv m
  with T̂ , ϵ′ , Δ , k , σ , Sσ , SΔ , ϵ≤ , ≃T , der ← complete⇒ SΓ Se ST lin dv m
  = ϵ′ , C-Eq T T̂ ∷ Δ , k , σ , Sσ ,
    (subst (_≃ subTy T̂ σ) (sym (subTy-id ST)) (≃-sym ≃T) ∷ SΔ) ,
    ϵ≤ , A-Check der
