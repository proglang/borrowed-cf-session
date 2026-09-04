-- | Typing eliminates the residual case of soup expression-step inversion.
module BorrowedCF.Simulation.BackwardSoup.TypedInversion where

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Reduction.Expressions as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Reduction.Base using (ChanCx)
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (PairEnv; step-inversion)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (letpair-var-untypable)

open Source using (_;_⊢_∶_∣_)

------------------------------------------------------------------------
-- A translated expression step reflects to a source expression step once
-- the source expression is known to be well typed in a channel context.

typed-step-inversion :
  {n n′ : ℕ} {Γ : Context.Ctx n} {γ : Context.Struct n}
  {e : Source.Tm n} {T : Types.𝕋} {ε : Types.Eff}
  {sigma : Translation.Env n n′}
  {t t′ : SoupTerm.Tm n′} →
  ChanCx Γ →
  Γ ; γ ⊢ e ∶ T ∣ ε →
  ValueEnv sigma →
  PairEnv sigma →
  Translation.T[ e ] sigma ≡ t →
  t SoupReduction.⋯→ t′ →
  Σ[ e′ ∈ Source.Tm n ]
    (e SourceReduction.⋯→ e′) ×
    (Translation.T[ e′ ] sigma ≡ t′)
typed-step-inversion {Γ = Γ} {γ = γ} {e = e} {T = T} {ε = ε}
  Γ-S ⊢e Vsigma Psigma translated red
  with step-inversion e _ Vsigma Psigma translated red
... | inj₁ reflected = reflected
... | inj₂ (E , x , body , shape) =
  ⊥-elim
    (letpair-var-untypable {E = E} {x = x} {body = body} Γ-S
      (subst (λ e′ → Γ ; γ ⊢ e′ ∶ T ∣ ε) shape ⊢e))
