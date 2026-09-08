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

module BorrowedCF.Completeness.Main.Bind.Support where


open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Plumbing: the outer component of a binder structure.

wk≼ : ∀ {n} {Γ : Ctx n} {T : 𝕋} {γ₀ γ : Struct n} →
  Γ ∶ γ₀ ≼ γ → (T ⸴ Γ) ∶ 𝐂.wk γ₀ ≼ 𝐂.wk γ
wk≼ {Γ = Γ} ≤γ = 𝐂.≼-⋯ (𝐂.⇔→⇒ ⦃ 𝐂.Kₛ ⦄ {Γ} (𝐂.wk-⇔ ⦃ 𝐂.Kₛ ⦄)) ≤γ

wk²≼ : ∀ {n} {Γ : Ctx n} {T U : 𝕋} {γ₀ γ : Struct n} →
    Γ ∶ γ₀ ≼ γ → (T ⸴ U ⸴ Γ) ∶ 𝐂.wk (𝐂.wk γ₀) ≼ 𝐂.wk (𝐂.wk γ)
wk²≼ ≤γ = wk≼ (wk≼ ≤γ)

bind-cover : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) {n} {Γ : Ctx n} {T U : 𝕋}
                 (β : Struct n) {e : Tm (suc n)} {ϵ : Eff} (X : Subset n) →
    fvClose (fv e) ⊆ X →
    (T ⸴ Γ) ; join a (` 0F) (𝐂.wk β) ⊢ e ∶ U ∣ ϵ →
    AllCx Unr Γ (β ↓ ∁ X)
bind-cover a β X ⊆X dbody = allCx-of-dom (β ↓ ∁ X) λ z z∈ →
    fv-cover′ dbody (∈-bind⁺ a β (↓-dom⊆dom β z∈))
                    (λ sz∈ → x∈∁p⇒x∉p (↓-dom β (∁ X) z∈) (⊆X (∈tail⁺ sz∈)))

bind-fv⊆ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) {n} {Γ : Ctx n} {T U : 𝕋}
               (β : Struct n) {e : Tm (suc n)} {ϵ : Eff} →
    (T ⸴ Γ) ; join a (` 0F) (𝐂.wk β) ⊢ e ∶ U ∣ ϵ →
    fvClose (fv e) ⊆ dom β
bind-fv⊆ a β dbody z∈ = ∈-bind⁻ a β (fv⊆dom dbody (∈tail⁻ z∈))

bind²-cover : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B)
                  {n} {Γ : Ctx n} {T₁ T₂ U : 𝕋} (β : Struct n) {e : Tm (suc (suc n))}
                  {ϵ : Eff} (X : Subset n) →
    fvClose* 2 (fv e) ⊆ X →
    (T₁ ⸴ T₂ ⸴ Γ) ; join a (join b (` 0F) (` 1F)) (𝐂.wk (𝐂.wk β)) ⊢ e ∶ U ∣ ϵ →
    AllCx Unr Γ (β ↓ ∁ X)
bind²-cover a b β X ⊆X dbody = allCx-of-dom (β ↓ ∁ X) λ z z∈ →
    fv-cover′ dbody (∈-bind²⁺ a b β (↓-dom⊆dom β z∈))
                    (λ sz∈ → x∈∁p⇒x∉p (↓-dom β (∁ X) z∈) (⊆X (∈drop⁺ 2 sz∈)))

bind²-fv⊆ : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B)
                {n} {Γ : Ctx n} {T₁ T₂ U : 𝕋} (β : Struct n) {e : Tm (suc (suc n))}
                {ϵ : Eff} →
    (T₁ ⸴ T₂ ⸴ Γ) ; join a (join b (` 0F) (` 1F)) (𝐂.wk (𝐂.wk β)) ⊢ e ∶ U ∣ ϵ →
    fvClose* 2 (fv e) ⊆ dom β
bind²-fv⊆ a b β dbody z∈ = ∈-bind²⁻ a b β (fv⊆dom dbody (∈drop⁻ 2 z∈))

