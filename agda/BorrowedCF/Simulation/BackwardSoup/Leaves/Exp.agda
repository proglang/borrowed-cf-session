-- | Backward simulation for a soup expression step.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Exp where

import Data.Vec.Relation.Unary.All as AllV
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep

open import BorrowedCF.Simulation.ForwardSoup.Local.Exp
  using (exp-step; expThread; expSlotEq; expConfigStep)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; threadInContext; closedPairEnv; plug)
open import BorrowedCF.Simulation.BackwardSoup.TypedInversion
  using (typed-step-inversion)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (value-irreducible)

open Typed using (_;_⊢ₚ_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  stepping-not-unit :
    {n : ℕ} {t t′ : SoupTerm.Tm n} →
    t SoupExpression.⋯→ t′ → t ≢ SoupTerm.*
  stepping-not-unit red equal =
    value-irreducible SoupExpression.V-K
      (subst (SoupExpression._⋯→ _) equal red)

------------------------------------------------------------------------
-- The selected soup thread determines a unique source expression.  Typing
-- rules out the sole non-reflecting expression step, and the exact forward
-- leaf then constructs the image of the reflected reduct at the same slot.

exp-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  {j : 𝔽 m} {t′ : Soup.Thread n} →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  lookup ts j SoupExpression.⋯→ t′ →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs (SoupReduction.replaceAt ts j t′))
exp-reflect {P = P} {cs = cs} {ts = ts} {j = j} {t′ = t′}
  ⊢P image red
  with image-thread-term image j (stepping-not-unit red)
... | k , ctx , e , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx e AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢e
  with typed-step-inversion Γ′-S ⊢e
         (focusValueEnv ctx Typed.⟪ e ⟫ (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ e ⟫
           (logicalChannels image) closedPairEnv)
         (sym content) red
... | e′ , sourceRed , translated =
  plug ctx Typed.⟪ e′ ⟫
  , plug-red ctx (TypedReduction.R-Exp sourceRed)
  , closeConfigStep exactStep
  where
  focused = focusImage ctx Typed.⟪ e ⟫ (localImage image)

  leaf =
    exp-step
      (focusValueEnv ctx Typed.⟪ e ⟫ (logicalChannels image) (λ ()))
      (focused-image focused) sourceRed

  focusedSlot :
    threadEmbedding (focused-image focused) zero ≡
    threadEmbedding (localImage image)
      (threadInContext ctx Typed.⟪ e ⟫ zero)
  focusedSlot = focusImage-thread ctx Typed.⟪ e ⟫ (localImage image) zero

  sameSlot : expThread leaf ≡ j
  sameSlot =
    just-injective
      (sym (expSlotEq leaf) ■ focusedSlot ■
       cong (threadEmbedding (localImage image)) position ■ embedded)

  targetThreadsEq :
    SoupReduction.replaceAt ts (expThread leaf)
      (Translation.T[ e′ ]
        (focusEnv ctx Typed.⟪ e ⟫ (logicalChannels image) (λ ()))) ≡
    SoupReduction.replaceAt ts j t′
  targetThreadsEq = cong₂ (SoupReduction.replaceAt ts) sameSlot translated

  targetEq :
    Soup.config cs
      (SoupReduction.replaceAt ts (expThread leaf)
        (Translation.T[ e′ ]
          (focusEnv ctx Typed.⟪ e ⟫ (logicalChannels image) (λ ())))) ≡
    Soup.config cs (SoupReduction.replaceAt ts j t′)
  targetEq = cong (Soup.config cs) targetThreadsEq

  lifted = ascend focused (expConfigStep leaf)

  exactStep =
    subst
      (λ C′ →
        ForwardStep.ConfigStep
          (plug ctx Typed.⟪ e′ ⟫) (λ ()) (λ _ → ⊥) (λ _ → ⊥)
          (Soup.config cs ts) C′)
      targetEq lifted
