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

module BorrowedCF.Completeness.Main.Bind.Let where


open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- T-Let.

private
  let-go : ∀ {n} {Γ Γ̂ : Ctx n} {γ α β : Struct n} {e₁ : Tm n} {e₂ : Tm (suc n)}
             {T₀ U : 𝕋} {ϵ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
    IHAt e₁ → IHAt e₂ →
    Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
    SolvedTm e₁ → SolvedTm e₂ → SolvedTy U → LinStruct Γ γ →
    (d : Dir) →
    (mk : ∀ {T̂ Û : 𝕋} {ϵ₁ ϵ₂ : Eff} {Δ₀ Δ₁ Δ₂ : CSet} {m′ k : ℕ} →
       Γ̂ ∶ join d (γ ∣fv[ e₁ ]) (γ ↓ fvClose (fv e₂)) ≼ γ ↑ Δ₀ →
       Γ̂ ; γ ∣fv[ e₁ ] / m ⊢ e₁ ⇒ T̂ ∣ ϵ₁ ↑ Δ₁ / m′ →
       T̂ ⸴ Γ̂ ; join d (` 0F) (𝐂.wk (γ ↓ fvClose (fv e₂))) / m′ ⊢ e₂ ⇒ Û ∣ ϵ₂ ↑ Δ₂ / k →
       Γ̂ ; γ / m ⊢ `let e₁ `in e₂ ⇒ Û ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₀ ++ Δ₁ ++ Δ₂ / k) →
    Γ ∶ join d α β ≼ γ →
    Γ ; α ⊢ e₁ ∶ T₀ ∣ ϵ →
    (T₀ ⸴ Γ) ; join d (` 0F) (𝐂.wk β) ⊢ e₂ ∶ U ∣ ϵ →
    Conclusion Γ̂ γ (`let e₁ `in e₂) U ϵ m σ₀
  let-go {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {α = α} {β = β} {e₁ = e₁} {e₂ = e₂} {T₀ = T₀} {U = U}
         ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ SU lin d mk ≤γ dv₁ dv₂ =
    let Y    = fvClose (fv e₂)
        covβ = bind-cover d β Y ⊆-refl dv₂
        Y⊆β  = bind-fv⊆ d β dv₂
        ≤L   = ≼-left d (fv e₁) Y lin ≤γ (fv-cover dv₁) covβ (fv⊆dom dv₁) Y⊆β
        ≤R   = ≼-right d (fv e₁) Y lin ≤γ (fv-cover dv₁) covβ (fv⊆dom dv₁) Y⊆β
        ≤γ′  = canon d (fv e₁) Y lin ≤γ (fv-cover dv₁) covβ (fv⊆dom dv₁) Y⊆β
        dv₁′ = T-Weaken ≤L (restrict dv₁)
        dv₂′ = T-Weaken (≼-join d (≼-refl ≈-refl) (wk≼ ≤R))
                        (restrict-bind d β Y ⊆-refl dv₂)
        r1 =
          ih₁ Sσ uΓ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) Se₁ (subTy-solved T₀ s₀-solving)
              (lin-sub Γ (γ ↓ (fv e₁)) (lin-↓ Γ γ (fv e₁) lin)) (solve-ty Se₁ dv₁′)
        T̂ , ϵ₁ , Δ₁ , m′ , σ₁ , Sσ₁ , ag₁ , SΔ₁ , ϵ₁≤ , ≃₁ , m≤m′ , uvT̂ , uvΔ₁ , der₁ = r1
        r2 =
          ih₂ {Γ̂ = T̂ ⸴ Γ̂} Sσ₁ (uvarsInΓ-⸴ uvT̂ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ))
              (λ where
                 zero    → ≃₁
                 (suc x) → approx-agree {Γ = subCtx Γ s₀} {Γ̂ = Γ̂} uΓ ag₁ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) x)
              Se₂ (subTy-solved U s₀-solving)
              (lin-bind d (subTy T₀ s₀) (subCtx Γ s₀) (γ ↓ Y) (lin-sub Γ (γ ↓ Y) (lin-↓ Γ γ Y lin)))
              (solve-ty Se₂ dv₂′)
        Û , ϵ₂ , Δ₂ , k , σ₂ , Sσ₂ , ag₂ , SΔ₂ , ϵ₂≤ , ≃₂ , m′≤k , uvÛ , uvΔ₂ , der₂ = r2
        Lft = ≼→ Sσ ap uΓ ≤γ′
        AG  = agree-trans (agree-narrow m≤m′ ag₂) ag₁
    in _ , _ , _ , k , σ₂ , Sσ₂ , AG ,
       solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
         (solvedΔ-++ (solvedΔ-agree (agree-sym ag₂) uvΔ₁ SΔ₁) SΔ₂) ,
       ⊔ϵ-lub ϵ₁≤ ϵ₂≤ , ≃-trans ≃₂ (≃-reflexive (subTy-id SU)) ,
       Nat.≤-trans m≤m′ m′≤k , uvÛ ,
       uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m≤m′ m′≤k) (csc Lft))
         (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤k uvΔ₁) uvΔ₂) ,
       mk (der Lft) der₁ der₂

let-case : LetCase
let-case ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin dv
  with inv-`let dv
... | par , α , β , T₀ , ≤γ , dv₁ , dv₂ =
  let-go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin 𝟙 (λ ≤ x y → A-Let par ≤ x y) ≤γ dv₁ dv₂
... | seq , α , β , T₀ , ≤γ , dv₁ , dv₂ =
  let-go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin L (λ ≤ x y → A-Let seq ≤ x y) ≤γ dv₁ dv₂

