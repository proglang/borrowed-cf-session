-- | Backward simulation for the soup fork leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Fork where

import Data.Vec.Relation.Unary.All as AllV
open import Data.Maybe using (just)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Local.Fork
  using ( fork-step; forkParent; forkSlotEq; forkFrame
        ; forkChild≡; forkChildValue; forkSelectedFork; forkConfigStep)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (LocalImage; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-value-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusChannels; threadInContext; closedPairEnv; plug)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)

open Typed using (_;_⊢ₚ_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  fork-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n} {e t : SoupTerm.Tm n} →
    SoupExpression.Value e →
    t ≡ F SoupExpression.[
          SoupTerm.K SoupTerm.`fork SoupTerm.·¹ e
        ]* →
    t ≢ SoupTerm.*
  fork-redex-not-unit {F = F} Ve selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

------------------------------------------------------------------------
-- A soup fork step is the image of a source fork step.  The physical slot is
-- recovered from the global image, while `redex-unique` identifies the
-- caller-supplied decomposition of that slot with the forward fork leaf's
-- canonical decomposition.

fork-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (F : SoupExpression.Frame* (2 *ℕ n))
  {e : Soup.Thread n} →
  SoupExpression.Value e →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`fork SoupTerm.·¹ e
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs
        (SoupReduction.insertAfter
          (SoupReduction.replaceAt ts j (F SoupExpression.[ SoupTerm.* ]*))
          j
          (e SoupTerm.·¹ SoupTerm.*)))
fork-reflect {P = P} {cs = cs} {ts = ts} j F {e = e} Ve selected
  ⊢P image
  with image-thread-term image j
         (fork-redex-not-unit {F = F} {e = e} Ve selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F SoupTerm.`fork Types.𝟙 e
         (sym content ■ selected)
... | E , arg , refl , frameEq , argEq =
  plug ctx localTarget
  , plug-red ctx localRed
  , closeConfigStep exactStep
  where
  sigma =
    focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ())

  Vsigma =
    focusValueEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ())

  Varg : SourceReduction.Value arg
  Varg = T-value-inv arg sigma Vsigma
    (subst SoupExpression.Value (sym argEq) Ve)

  localTarget : Typed.Proc _
  localTarget =
    Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥
    Typed.⟪ Source._·¹_ arg Source.* ⟫

  localRed : Typed.⟪ source ⟫ TypedReduction.─→ₚ localTarget
  localRed = TypedReduction.R-Fork E Varg

  focused = focusImage ctx Typed.⟪ source ⟫ (localImage image)

  redexImage :
    LocalImage
      (Typed.⟪ SourceReduction._[_]* E
        (Source._·¹_ (Source.K Source.`fork) arg)
      ⟫)
      (focusChannels ctx Typed.⟪ source ⟫ (logicalChannels image))
      sigma
      (focusedAmbientChannel focused)
      (focusedAmbientThread focused)
      (Soup.config cs ts)
  redexImage = focused-image focused

  leaf =
    fork-step {E = E} {e = arg}
      {logicalChannels =
        focusChannels ctx Typed.⟪ source ⟫ (logicalChannels image)}
      {sigma = sigma} {C = Soup.config cs ts}
      Vsigma Varg redexImage

  focusedSlot :
    threadEmbedding (focused-image focused) zero ≡
    threadEmbedding (localImage image)
      (threadInContext ctx Typed.⟪ source ⟫ zero)
  focusedSlot = focusImage-thread ctx Typed.⟪ source ⟫ (localImage image) zero

  sameSlot : forkParent leaf ≡ j
  sameSlot =
    just-injective
      (sym (forkSlotEq leaf) ■ focusedSlot ■
       cong (threadEmbedding (localImage image)) position ■ embedded)

  redexEq :
    forkFrame leaf SoupExpression.[
      SoupTerm.K SoupTerm.`fork SoupTerm.·¹ Translation.T[ arg ] sigma
    ]* ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`fork SoupTerm.·¹ e
    ]*
  redexEq =
    sym (forkSelectedFork leaf) ■
    cong (lookup ts) sameSlot ■
    selected

  translatedChildValue :
    SoupExpression.Value (Translation.T[ arg ] sigma)
  translatedChildValue =
    subst SoupExpression.Value (forkChild≡ leaf) (forkChildValue leaf)

  frameUnitEq :
    forkFrame leaf SoupExpression.[ SoupTerm.* ]* ≡
    F SoupExpression.[ SoupTerm.* ]*
  frameUnitEq with
    redex-unique {F = forkFrame leaf} {F′ = F}
      {c = SoupTerm.`fork} {c′ = SoupTerm.`fork}
      translatedChildValue Ve redexEq
  ... | _ , _ , framePlugEq , _ = framePlugEq SoupTerm.*

  childEq :
    Translation.T[ arg ] sigma SoupTerm.·¹ SoupTerm.* ≡
    e SoupTerm.·¹ SoupTerm.*
  childEq with
    redex-unique {F = forkFrame leaf} {F′ = F}
      {c = SoupTerm.`fork} {c′ = SoupTerm.`fork}
      translatedChildValue Ve redexEq
  ... | _ , argEq′ , _ , _ =
    cong (λ u → u SoupTerm.·¹ SoupTerm.*) argEq′

  targetThreadsEq :
    SoupReduction.insertAfter
      (SoupReduction.replaceAt ts (forkParent leaf)
        (forkFrame leaf SoupExpression.[ SoupTerm.* ]*))
      (forkParent leaf)
      (Translation.T[ arg ] sigma SoupTerm.·¹ SoupTerm.*) ≡
    SoupReduction.insertAfter
      (SoupReduction.replaceAt ts j
        (F SoupExpression.[ SoupTerm.* ]*))
      j
      (e SoupTerm.·¹ SoupTerm.*)
  targetThreadsEq =
    cong₂
      (λ parent slot →
        SoupReduction.insertAfter
          (SoupReduction.replaceAt ts slot parent)
          slot
          (Translation.T[ arg ] sigma SoupTerm.·¹ SoupTerm.*))
      frameUnitEq sameSlot
    ■ cong
        (λ child →
          SoupReduction.insertAfter
            (SoupReduction.replaceAt ts j
              (F SoupExpression.[ SoupTerm.* ]*))
            j child)
        childEq

  targetEq :
    Soup.config cs
      (SoupReduction.insertAfter
        (SoupReduction.replaceAt ts (forkParent leaf)
          (forkFrame leaf SoupExpression.[ SoupTerm.* ]*))
        (forkParent leaf)
        (Translation.T[ arg ] sigma SoupTerm.·¹ SoupTerm.*)) ≡
    Soup.config cs
      (SoupReduction.insertAfter
        (SoupReduction.replaceAt ts j
          (F SoupExpression.[ SoupTerm.* ]*))
        j
        (e SoupTerm.·¹ SoupTerm.*))
  targetEq = cong (Soup.config cs) targetThreadsEq

  lifted = ascend focused (forkConfigStep leaf)

  exactStep =
    subst
      (λ C′ →
        ForwardStep.ConfigStep
          (plug ctx localTarget) (λ ()) (λ _ → ⊥) (λ _ → ⊥)
          (Soup.config cs ts) C′)
      targetEq lifted
