-- | The application case of the completeness induction: T-AppUnr / T-AppLin / T-AppLeft /
--   T-AppRight, all four through A-App (agent C4).
--
--   A-App INFERS the function's arrow and CHECKS the argument against its domain, which may
--   still contain unification variables allocated while inferring the function.  This is where
--   the substitution threading pays off: the argument is inferred too (`A-Check`), and the
--   `C-Eq` that A-Check emits is discharged at the final substitution, where both sides are
--   known to instantiate to the declarative argument type.
--
--   Owner: agent C4.
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

module BorrowedCF.Completeness.Main.App where

open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables

private
  -- The common worker.  `ec` turns the two effect bounds the induction hypotheses return
  -- into the `EffCompat` premise of A-App; it is the only thing the four declarative
  -- application rules disagree about (besides which premise is forced to be pure).
  go : ∀ {n} {Γ Γ̂ : Ctx n} {γ α β : Struct n} {e₁ e₂ : Tm n} {T₀ U : 𝕋} {a : Arr}
         {ϵ ϵ₁ᵈ ϵ₂ᵈ : Eff} {m : ℕ} {σ₀ : UV.Sub} →
    IHAt e₁ → IHAt e₂ →
    Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
    SolvedTm e₁ → SolvedTm e₂ → SolvedTy U → LinStruct Γ γ →
    Γ ∶ join (Arr.dir a) β α ≼ γ →
    Arr.eff a ≤ϵ ϵ →
    (∀ {x y : Eff} → x ≤ϵ ϵ₁ᵈ → y ≤ϵ ϵ₂ᵈ → EffCompat (Arr.dir a) y x) →
    ϵ₁ᵈ ≤ϵ ϵ → ϵ₂ᵈ ≤ϵ ϵ →
    Γ ; α ⊢ e₁ ∶ T₀ ⟨ a ⟩→ U ∣ ϵ₁ᵈ →
    Γ ; β ⊢ e₂ ∶ T₀ ∣ ϵ₂ᵈ →
    Conclusion Γ̂ γ (e₁ ·⟨ Arr.dir a ⟩ e₂) U ϵ m σ₀
  go {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {e₁ = e₁} {e₂ = e₂} {T₀ = T₀} {U = U} {a = a} {m = m}
     ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ SU lin ≤γ effa≤ ec ≤₁ ≤₂ dv₁ dv₂ =
    let T̂ , ϵ₁ , Δ₁ , m′ , σ₁ , Sσ₁ , ag₁ , SΔ₁ , ϵ₁≤ , ≃₁ , m≤m′ , uvT̂₀ , uvΔ₁ , der₁₀ =
          ih₁ Sσ uΓ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) Se₁
              (subTy-solved T₀ s₀-solving ⟨ a ⟩→ subTy-solved U s₀-solving)
              (lin-sub Γ (γ ↓ (fv e₁)) (lin-↓ Γ γ (fv e₁) lin))
              (solve-ty Se₁ (split-right (Arr.dir a) lin ≤γ dv₂ dv₁))
        T̂₁ , T̂₂ , eqT̂ , ≃dom , ≃cod = arrow-inv ≃₁
        uvT̂  = subst (UVarsIn 0 m′) eqT̂ uvT̂₀
        der₁ = subst (λ z → Γ̂ ; γ ∣fv[ e₁ ] / m ⊢ e₁ ⇒ z ∣ ϵ₁ ↑ Δ₁ / m′) eqT̂ der₁₀
        Û₂ , ϵ₂ , Δ₂ , k , σ₂ , Sσ₂ , ag₂ , SΔ₂ , ϵ₂≤ , ≃₂ , m′≤k , uvÛ₂ , uvΔ₂ , der₂ =
          ih₂ Sσ₁ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ)
              (approx-agree {Γ = subCtx Γ s₀} {Γ̂ = Γ̂} uΓ ag₁ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap)) Se₂
              (subTy-solved T₀ s₀-solving)
              (lin-sub Γ (γ ↓ (fv e₂)) (lin-↓ Γ γ (fv e₂) lin))
              (solve-ty Se₂ (split-left (Arr.dir a) lin ≤γ dv₂ dv₁))
        Lft = ≼→ Sσ ap uΓ (split-≤γ (Arr.dir a) lin ≤γ dv₂ dv₁)
        AG  = agree-trans (agree-narrow m≤m′ ag₂) ag₁
    in _ , _ , _ , k , σ₂ , Sσ₂ , AG ,
       solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
         (solvedΔ-++ (solvedΔ-agree (agree-sym ag₂) uvΔ₁ SΔ₁)
                     (≃-trans (≃-reflexive (subTy-agree ag₂ (uvarsIn-→₁ uvT̂)))
                              (≃-trans ≃dom (≃-sym ≃₂)) ∷ SΔ₂)) ,
       ⊔ϵ-lub (⊔ϵ-lub (≤ϵ-trans ϵ₁≤ ≤₁) (≤ϵ-trans ϵ₂≤ ≤₂)) effa≤ ,
       ≃-trans (≃-reflexive (subTy-agree ag₂ (uvarsIn-→₂ uvT̂)))
               (≃-trans ≃cod (≃-reflexive (subTy-id SU))) ,
       Nat.≤-trans m≤m′ m′≤k , uvarsIn-mono Nat.≤-refl m′≤k (uvarsIn-→₂ uvT̂) ,
       uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m≤m′ m′≤k) (csc Lft))
         (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤k uvΔ₁)
                      (C-Eq (uvarsIn-mono Nat.≤-refl m′≤k (uvarsIn-→₁ uvT̂)) uvÛ₂ ∷ uvΔ₂)) ,
       A-App (ec ϵ₁≤ ϵ₂≤) (der Lft) der₁ (A-Check der₂)

------------------------------------------------------------------------
-- The four declarative application rules.

app-case : AppCase
app-case ih₁ ih₂ {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} Sσ uΓ ap Se₁ Se₂ ST lin dv
  with inv-· dv
... | a , α , β , T₀ , ≤γ , refl , effa≤ , T-AppUnr a-unr dv₁ dv₂ =
  go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin ≤γ effa≤
     (λ {x} {y} _ _ → subst (λ z → EffCompat z y x) (sym (Arr.ω⇒𝟙 a a-unr)) Unit.tt)
     ≤ϵ-refl ≤ϵ-refl dv₁ dv₂
... | a , α , β , T₀ , ≤γ , refl , effa≤ , T-AppLin a-par dv₁ dv₂ =
  go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin ≤γ effa≤
     (λ {x} {y} _ _ → subst (λ z → EffCompat z y x) (sym (a-par .proj₂)) Unit.tt)
     ≤ϵ-refl ≤ϵ-refl dv₁ dv₂
... | a , α , β , T₀ , ≤γ , refl , effa≤ , T-AppLeft aL dv₁ dv₂ =
  go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin ≤γ effa≤
     (λ {x} {y} x≤ _ → subst (λ z → EffCompat z y x) (sym aL) (≤ϵℙ⇒≡ℙ x≤))
     ℙ≤ϵ ≤ϵ-refl dv₁ dv₂
... | a , α , β , T₀ , ≤γ , refl , effa≤ , T-AppRight aR dv₁ dv₂ =
  go ih₁ ih₂ Sσ uΓ ap Se₁ Se₂ ST lin ≤γ effa≤
     (λ {x} {y} _ y≤ → subst (λ z → EffCompat z y x) (sym aR) (≤ϵℙ⇒≡ℙ y≤))
     ≤ϵ-refl ℙ≤ϵ dv₁ dv₂
