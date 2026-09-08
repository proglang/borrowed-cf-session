-- | The three binding cases of the completeness induction: T-Let, T-LetPair, T-Case (C4).
--
--   These are the cases that put an INFERRED type into the context: A-Let / A-LetPair /
--   A-Case type their body in the type the first premise synthesised, which still contains
--   unification variables.  That is exactly what the generalised statement is for: `Approx`
--   asks the algorithmic context only to INSTANTIATE to the declarative one.
--
--   Each case is a `Dir`-indexed worker plus two call sites, one per `ParSeq`, because
--   `join par` / `join seq` reduce to `join 𝟙` / `join L` only when the ParSeq is a
--   constructor.
--
--   Owner: agent C4.
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; _⊆_; ∁)
open import Data.Fin.Subset.Properties
  using (x∈p∪q⁻; x∈p∪q⁺; p⊆p∪q; q⊆p∪q; x∈∁p⇒x∉p; ⊆-refl; ⊆-trans)
open import Data.List.Relation.Unary.All using ([]; _∷_)

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

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Bin
open import BorrowedCF.Completeness.Main.Interface

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Completeness.Main.Bind.Support

module BorrowedCF.Completeness.Main.Bind.Case where


open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- T-Case.

-- The structural side of the case rule: the canonical split of the declarative one.
-- These are TOP-LEVEL (a parametrised module) so that the big proof below refers to them by
-- name instead of duplicating their terms at every use.

caseY : ∀ {n} → Tm (suc n) → Tm (suc n) → Subset n
caseY e₁ e₂ = fvClose (fv e₁) ∪ fvClose (fv e₂)

module CS {n : ℕ} {Γ : Ctx n} {γ α β : Struct n} {e : Tm n} {e₁ e₂ : Tm (suc n)}
          {T₁ T₂ U : 𝕋} {ϵ : Eff}
          (d : Dir) (lin : LinStruct Γ γ) (≤γ : Γ ∶ join d α β ≼ γ)
          (dve : Γ ; α ⊢ e ∶ T₁ ⊕ T₂ ∣ ϵ)
          (dv₁ : (T₁ ⸴ Γ) ; join d (` 0F) (𝐂.wk β) ⊢ e₁ ∶ U ∣ ϵ)
          (dv₂ : (T₂ ⸴ Γ) ; join d (` 0F) (𝐂.wk β) ⊢ e₂ ∶ U ∣ ϵ)
          where

  covβ : AllCx Unr Γ (β ↓ ∁ (caseY e₁ e₂))
  covβ = bind-cover ⦃ join-dir ⦄ d β (caseY e₁ e₂) (p⊆p∪q _) dv₁

  Y⊆β : caseY e₁ e₂ ⊆ dom β
  Y⊆β z∈ = [ bind-fv⊆ ⦃ join-dir ⦄ d β dv₁ , bind-fv⊆ ⦃ join-dir ⦄ d β dv₂ ]′
             (x∈p∪q⁻ (fvClose (fv e₁)) (fvClose (fv e₂)) z∈)

  ≤L : Γ ∶ α ↓ (fv e) ≼ γ ↓ (fv e)
  ≤L = ≼-left d (fv e) (caseY e₁ e₂) lin ≤γ (fv-cover dve) covβ (fv⊆dom dve) Y⊆β

  ≤R : Γ ∶ β ↓ (caseY e₁ e₂) ≼ γ ↓ (caseY e₁ e₂)
  ≤R = ≼-right d (fv e) (caseY e₁ e₂) lin ≤γ (fv-cover dve) covβ (fv⊆dom dve) Y⊆β

  ≤γ′ : Γ ∶ join d (γ ↓ (fv e)) (γ ↓ (caseY e₁ e₂)) ≼ γ
  ≤γ′ = canon d (fv e) (caseY e₁ e₂) lin ≤γ (fv-cover dve) covβ (fv⊆dom dve) Y⊆β

  -- the two branch premises, confined to the canonical structure
  br₁ : (T₁ ⸴ Γ) ; join d (` 0F) (𝐂.wk (γ ↓ caseY e₁ e₂)) ⊢ e₁ ∶ U ∣ ϵ
  br₁ = T-Weaken (≼-join d (≼-refl ≈-refl) (wk≼ ≤R))
                 (restrict-bind d β (caseY e₁ e₂) (p⊆p∪q _) dv₁)

  br₂ : (T₂ ⸴ Γ) ; join d (` 0F) (𝐂.wk (γ ↓ caseY e₁ e₂)) ⊢ e₂ ∶ U ∣ ϵ
  br₂ = T-Weaken (≼-join d (≼-refl ≈-refl) (wk≼ ≤R))
                 (restrict-bind d β (caseY e₁ e₂) (q⊆p∪q _ _) dv₂)

  scr : Γ ; γ ↓ (fv e) ⊢ e ∶ T₁ ⊕ T₂ ∣ ϵ
  scr = T-Weaken ≤L (restrict dve)

private
  case-go : ∀ {n} {Γ Γ̂ : Ctx n} {γ α β : Struct n} {e : Tm n} {e₁ e₂ : Tm (suc n)}
              {T₁ T₂ U : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
    IHAt e → IHAt e₁ → IHAt e₂ →
    Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
    SolvedTm e → SolvedTm e₁ → SolvedTm e₂ → SolvedTy U → LinStruct Γ γ →
    (d : Dir) →
    (mk : ∀ {T̂₁ T̂₂ Û₁ Û₂ : 𝕋} {ϵ′ ϵ₁ ϵ₂ : Eff} {Δ₀ Δ Δ₁ Δ₂ : CSet} {m₁ m₂ k : ℕ} →
       let γ₂ = γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂)) in
       Γ̂ ∶ join d (γ ∣fv[ e ]) γ₂ ≼ γ ↑ Δ₀ →
       Γ̂ ; γ ∣fv[ e ] / m ⊢ e ⇒ T̂₁ ⊕ T̂₂ ∣ ϵ′ ↑ Δ / m₁ →
       T̂₁ ⸴ Γ̂ ; join d (` 0F) (𝐂.wk γ₂) / m₁ ⊢ e₁ ⇒ Û₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
       T̂₂ ⸴ Γ̂ ; join d (` 0F) (𝐂.wk γ₂) / m₂ ⊢ e₂ ⇒ Û₂ ∣ ϵ₂ ↑ Δ₂ / k →
       Γ̂ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ Û₁ ∣ ϵ′ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂
         ↑ C-Eq Û₁ Û₂ ∷ Δ₀ ++ Δ ++ Δ₁ ++ Δ₂ / k) →
    Γ ∶ join d α β ≼ γ →
    Γ ; α ⊢ e ∶ T₁ ⊕ T₂ ∣ ϵ →
    (T₁ ⸴ Γ) ; join d (` 0F) (𝐂.wk β) ⊢ e₁ ∶ U ∣ ϵ →
    (T₂ ⸴ Γ) ; join d (` 0F) (𝐂.wk β) ⊢ e₂ ∶ U ∣ ϵ →
    Conclusion Γ̂ γ `case e `of⟨ e₁ ; e₂ ⟩ U ϵ m σ₀
  case-go {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {α = α} {β = β} {e = e} {e₁ = e₁} {e₂ = e₂}
          {T₁ = T₁} {T₂ = T₂} {U = U}
          ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ SU lin d mk ≤γ dve dv₁ dv₂
    with T̂ , ϵ₀ , Δ , m₁ , σ₁ , Sσ₁ , ag₁ , SΔ , ϵ₀≤ , ≃₀ , m≤m₁ , uvT̂₀ , uvΔ , der₀
       ← ihe Sσ uΓ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) Se
             (subTy-solved T₁ s₀-solving ⊕ subTy-solved T₂ s₀-solving)
             (lin-sub Γ (γ ↓ (fv e)) (lin-↓ Γ γ (fv e) lin))
             (solve-ty Se (CS.scr d lin ≤γ dve dv₁ dv₂))
    with T̂₁ , T̂₂ , eqT̂ , ≃t₁ , ≃t₂ ← sum-inv ≃₀
    with Û₁ , ϵ₁ , Δ₁ , m₂ , σ₂ , Sσ₂ , ag₂ , SΔ₁ , ϵ₁≤ , ≃b₁ , m₁≤m₂ , uvÛ₁ , uvΔ₁ , derb₁
       ← ih₁ {Γ̂ = T̂₁ ⸴ Γ̂} Sσ₁
             (uvarsInΓ-⸴ (uvarsIn-⊕₁ (subst (UVarsIn 0 m₁) eqT̂ uvT̂₀))
                         (uvarsInΓ-mono Nat.≤-refl m≤m₁ uΓ))
             (λ where
                zero    → ≃t₁
                (suc x) → approx-agree {Γ = subCtx Γ s₀} {Γ̂ = Γ̂} uΓ ag₁
                                       (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) x)
             Se₁ (subTy-solved U s₀-solving)
             (lin-bind d (subTy T₁ s₀) (subCtx Γ s₀) (γ ↓ caseY e₁ e₂)
                       (lin-sub Γ (γ ↓ caseY e₁ e₂) (lin-↓ Γ γ (caseY e₁ e₂) lin)))
             (solve-ty Se₁ (CS.br₁ d lin ≤γ dve dv₁ dv₂))
    with Û₂ , ϵ₂ , Δ₂ , k , σ₃ , Sσ₃ , ag₃ , SΔ₂ , ϵ₂≤ , ≃b₂ , m₂≤k , uvÛ₂ , uvΔ₂ , derb₂
       ← ih₂ {Γ̂ = T̂₂ ⸴ Γ̂} Sσ₂
             (uvarsInΓ-⸴ (uvarsIn-mono Nat.≤-refl m₁≤m₂
                           (uvarsIn-⊕₂ (subst (UVarsIn 0 m₁) eqT̂ uvT̂₀)))
                         (uvarsInΓ-mono Nat.≤-refl (Nat.≤-trans m≤m₁ m₁≤m₂) uΓ))
             (λ where
                zero    → ≃-trans (≃-reflexive (subTy-agree ag₂
                                     (uvarsIn-⊕₂ (subst (UVarsIn 0 m₁) eqT̂ uvT̂₀))))
                                  ≃t₂
                (suc x) → approx-agree {Γ = subCtx Γ s₀} {Γ̂ = Γ̂} uΓ
                                       (agree-trans (agree-narrow m≤m₁ ag₂) ag₁)
                                       (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) x)
             Se₂ (subTy-solved U s₀-solving)
             (lin-bind d (subTy T₂ s₀) (subCtx Γ s₀) (γ ↓ caseY e₁ e₂)
                       (lin-sub Γ (γ ↓ caseY e₁ e₂) (lin-↓ Γ γ (caseY e₁ e₂) lin)))
             (solve-ty Se₂ (CS.br₂ d lin ≤γ dve dv₁ dv₂))
    with Lft ← ≼→ Sσ ap uΓ (CS.≤γ′ d lin ≤γ dve dv₁ dv₂)
    with AG ← agree-trans (agree-narrow m≤m₁ (agree-trans (agree-narrow m₁≤m₂ ag₃) ag₂)) ag₁
    with m≤k ← Nat.≤-trans m≤m₁ (Nat.≤-trans m₁≤m₂ m₂≤k)
    = _ , _ , _ , k , σ₃ , Sσ₃ , AG ,
      solvedΔ-∷
        (≃-trans (≃-reflexive (subTy-agree ag₃ uvÛ₁)) (≃-trans ≃b₁ (≃-sym ≃b₂)))
        (solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
          (solvedΔ-++
            (solvedΔ-agree (agree-sym (agree-trans (agree-narrow m₁≤m₂ ag₃) ag₂)) uvΔ SΔ)
            (solvedΔ-++ (solvedΔ-agree (agree-sym ag₃) uvΔ₁ SΔ₁) SΔ₂))) ,
      ⊔ϵ-lub (⊔ϵ-lub ϵ₀≤ ϵ₁≤) ϵ₂≤ ,
      ≃-trans (≃-reflexive (subTy-agree ag₃ uvÛ₁))
              (≃-trans ≃b₁ (≃-reflexive (subTy-id SU))) ,
      m≤k , uvarsIn-mono Nat.≤-refl m₂≤k uvÛ₁ ,
      C-Eq (uvarsIn-mono Nat.≤-refl m₂≤k uvÛ₁) uvÛ₂ ∷
        uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤k (csc Lft))
          (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m₁≤m₂ m₂≤k) uvΔ)
                       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m₂≤k uvΔ₁) uvΔ₂)) ,
      mk (der Lft)
         (subst (λ z → Γ̂ ; γ ∣fv[ e ] / _ ⊢ e ⇒ z ∣ ϵ₀ ↑ Δ / m₁) eqT̂ der₀)
         derb₁ derb₂

  case-dispatch : ∀ {n} {Γ Γ̂ : Ctx n} {γ α β : Struct n} {e : Tm n} {e₁ e₂ : Tm (suc n)}
                    {T₁ T₂ U : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
    IHAt e → IHAt e₁ → IHAt e₂ →
    Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
    SolvedTm e → SolvedTm e₁ → SolvedTm e₂ → SolvedTy U → LinStruct Γ γ →
    (p/s : ParSeq) →
    Γ ∶ join p/s α β ≼ γ →
    Γ ; α ⊢ e ∶ T₁ ⊕ T₂ ∣ ϵ →
    (T₁ ⸴ Γ) ; join p/s (` 0F) (𝐂.wk β) ⊢ e₁ ∶ U ∣ ϵ →
    (T₂ ⸴ Γ) ; join p/s (` 0F) (𝐂.wk β) ⊢ e₂ ∶ U ∣ ϵ →
    Conclusion Γ̂ γ `case e `of⟨ e₁ ; e₂ ⟩ U ϵ m σ₀
  case-dispatch ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ SU lin par ≤γ dve dv₁ dv₂ =
    case-go ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ SU lin 𝟙
            (λ ≤ x y z → A-Case par ≤ x y z) ≤γ dve dv₁ dv₂
  case-dispatch ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ SU lin seq ≤γ dve dv₁ dv₂ =
    case-go ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ SU lin L
            (λ ≤ x y z → A-Case seq ≤ x y z) ≤γ dve dv₁ dv₂

-- The nine-component inversion package must NOT be `with`-abstracted together with the ParSeq
-- constructor: that generalises the whole goal (the induction hypotheses, the approximation,
-- the linearity) before the split, and the elaboration blows up.  Bind it, then dispatch.
case-case : CaseCase
case-case ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ ST lin dv =
  let p/s , α , β , T₁ , T₂ , ≤γ , dve , dv₁ , dv₂ = inv-`case dv
  in case-dispatch ihe ih₁ ih₂ Sσ uΓ ap Se Se₁ Se₂ ST lin p/s ≤γ dve dv₁ dv₂
