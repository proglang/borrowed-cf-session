-- | Backward simulation for the soup discard leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Discard where

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

open import BorrowedCF.Simulation.ForwardSoup.Local.Discard
  using ( DiscardStep; discard-step; discardThread; discardSlotEq
        ; discardFrame; discardArgument; discardTranslatedValue
        ; discardSelected; discardConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (LocalImage; OrientedChannel; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (CanonRedex; canon-discard)
import BorrowedCF.Simulation.BackwardSoup.Canonical as Canonical
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-value-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( FocusedImage; focusImage; focused-image; focusImage-thread
        ; ascend; plug-red; closeConfigStep
        ; focusedAmbientChannel; focusedAmbientThread)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusTyping; focusChannels; threadInContext
        ; closedPairEnv; plug; ≡→≋)
import BorrowedCF.Simulation.BackwardSoup.Position as Position
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Types using (𝟙; ⟨_⟩; ≃-sym; ≤ϵ-refl; _`→_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  cons-head-tail :
    {A : Set} {q : ℕ} (xs : Vec A (suc q)) →
    V.head xs ∷ V.tail xs ≡ xs
  cons-head-tail (x ∷ xs) = refl

  threadEmbedding-subst :
    {k n m : ℕ} {P : Typed.Proc k}
    {channels channels′ :
      Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set}
    {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    (eq : channels ≡ channels′) →
    (image :
      LocalImage P channels sigma ambientChannel ambientThread C) →
    (j : 𝔽 (Translation.processCount P)) →
    threadEmbedding
      (subst
        (λ channels″ →
          LocalImage P channels″ sigma ambientChannel ambientThread C)
        eq image)
      j ≡
    threadEmbedding image j
  threadEmbedding-subst refl image j = refl

  discard-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K SoupTerm.`discard SoupTerm.·¹ v
        ]* →
    t ≢ SoupTerm.*
  discard-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  discard-argument-var :
    {n : ℕ} {Γ : Context.Ctx n} {γ : Context.Struct n}
    {E : SourceReduction.Frame* n} {w : Source.Tm n} {T : Types.𝕋}
    {ϵ : Types.Eff} →
    Γ ; γ ⊢ E SourceReduction.[
      Source.K Source.`discard Source.·¹ w
    ]* ∶ T ∣ ϵ →
    SourceReduction.Value w →
    Σ[ x ∈ 𝔽 n ] w ≡ Source.` x
  discard-argument-var {E = E} {w = w} ⊢plug Vw
    with SourceReduction.⊢[]*⁻¹ E
           (Source.K Source.`discard Source.·¹ w) ⊢plug
  ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢app
    with Source.inv-·-unr ⊢app
           (λ ⊢fn →
             Source.constFnUnr′
               (Source.inv-K ⊢fn .proj₂ .proj₁)
               (Source.inv-K ⊢fn .proj₂ .proj₂ .proj₂))
  ... | _ , _ , _ , _ , _ , _ , _ , ⊢fn , ⊢arg
    with Source.inv-K ⊢fn
  ... | _ , dom≃ `→ _ , _ , Source.`discard =
    Position.handle-value-var
      (Source.T-Conv (≃-sym dom≃) ≤ϵ-refl ⊢arg)
      Vw

  redex-frame-unique :
    {n : ℕ} {F F′ : SoupExpression.Frame* n}
    {c c′ : Source.Const} {v v′ : SoupTerm.Tm n} →
    SoupExpression.Value v → SoupExpression.Value v′ →
    F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]* ≡
    F′ SoupExpression.[ SoupTerm.K c′ SoupTerm.·¹ v′ ]* →
    (t : SoupTerm.Tm n) →
    F SoupExpression.[ t ]* ≡ F′ SoupExpression.[ t ]*
  redex-frame-unique {F = F} {F′ = F′} {c = c} {c′ = c′}
    V V′ equal =
    proj₁ (proj₂ (proj₂
      (redex-unique {F = F} {F′ = F′} {c = c} {c′ = c′}
        V V′ equal)))

  canon-redex-local :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P Source.`discard src) →
    Typed.Proc (CanonRedex.midʳ cn)
  canon-redex-local cn =
    Typed.ν (suc (CanonRedex.bh cn) ∷ CanonRedex.D₁ cn)
      (CanonRedex.D₂ cn)
      (Typed.⟪
        SourceReduction._[_]*
          (SourceReduction._⋯ᶠ*_ (CanonRedex.E₀ cn) Source.weakenᵣ)
          (Source.K Source.`discard Source.·¹ (Source.` 0F))
       ⟫ Typed.∥
       (CanonRedex.Q₀ cn Typed.⋯ₚ Source.weakenᵣ))

  canon-redex-process :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    CanonRedex P Source.`discard src → Typed.Proc 0
  canon-redex-process cn =
    plug (CanonRedex.above′ cn) (canon-redex-local cn)

  canon-redex-image :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    GlobalImage P C →
    GlobalImage (canon-redex-process cn) C
  canon-redex-image cn =
    transportGlobalImage (CanonRedex.≋-redex cn)

  canon-redex-slot :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} {j : 𝔽 m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage P C) →
    threadEmbedding (localImage image) src ≡ just j →
    threadEmbedding (localImage (canon-redex-image cn image))
      (threadInContext (CanonRedex.above′ cn)
        (canon-redex-local cn) 0F) ≡ just j
  canon-redex-slot cn image slot =
    transportGlobalSlot
      (CanonRedex.≋-redex cn) image (CanonRedex.tracks cn) slot

  canon-redex-focus :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    FocusedImage
      (CanonRedex.above′ cn) (canon-redex-local cn)
      (logicalChannels image) (λ ())
      (λ _ → ⊥) (λ _ → ⊥) C
  canon-redex-focus cn image =
    focusImage (CanonRedex.above′ cn)
      (canon-redex-local cn) (localImage image)

  canon-redex-focus-thread :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    threadEmbedding (focused-image (canon-redex-focus cn image)) 0F ≡
    threadEmbedding (localImage image)
      (threadInContext (CanonRedex.above′ cn)
        (canon-redex-local cn) 0F)
  canon-redex-focus-thread cn image =
    focusImage-thread (CanonRedex.above′ cn)
      (canon-redex-local cn) (localImage image) 0F

  canon-redex-channels :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    Vec (OrientedChannel n)
      (Translation.channelCount (canon-redex-local cn))
  canon-redex-channels cn image =
    focusChannels (CanonRedex.above′ cn)
      (canon-redex-local cn) (logicalChannels image)

  canon-redex-head-channel :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    OrientedChannel n
  canon-redex-head-channel cn image =
    V.head (canon-redex-channels cn image)

  canon-redex-body-channels :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    Vec (OrientedChannel n)
      (Translation.channelCount
        (Typed._⋯ₚ_ (CanonRedex.Q₀ cn) Source.weakenᵣ))
  canon-redex-body-channels cn image =
    V.tail (canon-redex-channels cn image)

  canon-redex-channels-split :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    canon-redex-channels cn image ≡
      canon-redex-head-channel cn image ∷
      canon-redex-body-channels cn image
  canon-redex-channels-split cn image =
    sym (cons-head-tail (canon-redex-channels cn image))

  canon-redex-local-target :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P Source.`discard src) →
    Typed.Proc (CanonRedex.midʳ cn)
  canon-redex-local-target cn =
    Typed.ν (CanonRedex.bh cn ∷ CanonRedex.D₁ cn)
      (CanonRedex.D₂ cn)
      (Typed.⟪ SourceReduction._[_]* (CanonRedex.E₀ cn) Source.* ⟫
       Typed.∥ CanonRedex.Q₀ cn)

  canon-redex-target :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    CanonRedex P Source.`discard src → Typed.Proc 0
  canon-redex-target cn =
    plug (CanonRedex.above′ cn) (canon-redex-local-target cn)

  canon-discard-reduction :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P Source.`discard src) →
    P TypedReduction.─→ₚ canon-redex-target cn
  canon-discard-reduction cn =
    TypedReduction.R-Struct
      (CanonRedex.≋-redex cn)
      (plug-red (CanonRedex.above′ cn)
        (TypedReduction.R-Discard {E = CanonRedex.E₀ cn}))
      (≡→≋ refl)

  CanonDiscardStep :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    GlobalImage (canon-redex-process cn) C → Set
  CanonDiscardStep {C = C} cn image =
    DiscardStep
      {b₁ = CanonRedex.bh cn}
      {B₁ = CanonRedex.D₁ cn}
      {B₂ = CanonRedex.D₂ cn}
      {E = CanonRedex.E₀ cn}
      {P = CanonRedex.Q₀ cn}
      {channel = canon-redex-head-channel cn image}
      {bodyChannels = canon-redex-body-channels cn image}
      (canon-redex-local-target cn)
      (focusEnv (CanonRedex.above′ cn)
        (canon-redex-local cn) (logicalChannels image) (λ ()))
      (focusedAmbientChannel (canon-redex-focus cn image))
      (focusedAmbientThread (canon-redex-focus cn image))
      C
      (subst
        (λ channels →
          LocalImage (canon-redex-local cn) channels
            (focusEnv (CanonRedex.above′ cn)
              (canon-redex-local cn) (logicalChannels image) (λ ()))
            (focusedAmbientChannel (canon-redex-focus cn image))
            (focusedAmbientThread (canon-redex-focus cn image))
            C)
        (canon-redex-channels-split cn image)
        (focused-image (canon-redex-focus cn image)))

  canon-discard-leaf :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    [] ; Context.[] ⊢ₚ P →
    (image : GlobalImage (canon-redex-process cn) C) →
    CanonDiscardStep cn image
  canon-discard-leaf {C = C} cn ⊢P image
    with focusTyping (CanonRedex.above′ cn)
      (canon-redex-local cn) AllV.[]
      (AllV.[] / ⊢P ⊢-≋ CanonRedex.≋-redex cn)
  ... | Γᶜ , γᶜ , Γᶜ-S , ⊢local =
    discard-step
      {b₁ = CanonRedex.bh cn}
      {B₁ = CanonRedex.D₁ cn}
      {B₂ = CanonRedex.D₂ cn}
      {E = CanonRedex.E₀ cn}
      {P = CanonRedex.Q₀ cn}
      {channel = canon-redex-head-channel cn image}
      {bodyChannels = canon-redex-body-channels cn image}
      Γᶜ-S ⊢local
      (focusValueEnv (CanonRedex.above′ cn)
        (canon-redex-local cn) (logicalChannels image) (λ ()))
      (subst
        (λ channels →
          LocalImage (canon-redex-local cn) channels
            (focusEnv (CanonRedex.above′ cn)
              (canon-redex-local cn) (logicalChannels image) (λ ()))
            (focusedAmbientChannel (canon-redex-focus cn image))
            (focusedAmbientThread (canon-redex-focus cn image))
            C)
        (canon-redex-channels-split cn image)
        (focused-image (canon-redex-focus cn image)))

  canon-discard-same-slot :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} {j : 𝔽 m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage P C) →
    (leaf : CanonDiscardStep cn (canon-redex-image cn image)) →
    threadEmbedding (localImage image) src ≡ just j →
    discardThread leaf ≡ j
  canon-discard-same-slot cn image leaf sourceSlot =
    just-injective
      (sym (discardSlotEq leaf) ■
       threadEmbedding-subst
         (canon-redex-channels-split cn canonicalImage)
         (focused-image (canon-redex-focus cn canonicalImage)) 0F ■
       canon-redex-focus-thread cn canonicalImage ■
       canon-redex-slot cn image sourceSlot)
    where
    canonicalImage = canon-redex-image cn image

  canon-discard-exact-step :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`discard src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    (leaf : CanonDiscardStep cn image) →
    {j : 𝔽 m} {thread′ : Soup.Thread n} →
    discardThread leaf ≡ j →
    discardFrame leaf SoupExpression.[ SoupTerm.* ]* ≡ thread′ →
    ForwardStep.ConfigStep
      (canon-redex-target cn) (λ ()) (λ _ → ⊥) (λ _ → ⊥) C
      (Soup.config (Soup.channels C)
        (SoupReduction.replaceAt (Soup.threads C) j thread′))
  canon-discard-exact-step cn image leaf slotEq threadEq =
    ascend (canon-redex-focus cn image)
      (discardConfigStepAt leaf slotEq threadEq)

------------------------------------------------------------------------
-- A soup discard step on an exact translated handle is reflected by the
-- typed `R-Discard` rule at the canonical owner binder.

discard-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (F : SoupExpression.Frame* (2 *ℕ n))
  {i : 𝔽 n} {side : 𝔽 2} {e₂ : Soup.Thread n} →
  SoupExpression.Value
    (Translation.chanTriple (SoupTerm.* , Soup.endpoint i side , e₂)) →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`discard SoupTerm.·¹
        Translation.chanTriple (SoupTerm.* , Soup.endpoint i side , e₂)
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs
        (SoupReduction.replaceAt ts j (F SoupExpression.[ SoupTerm.* ]*)))
discard-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j F {i = i} {side = side} {e₂ = e₂} Vhandle selected
  ⊢P image
  with image-thread-term image j
         (discard-redex-not-unit {F = F} selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F SoupTerm.`discard Types.𝟙
         (Translation.chanTriple (SoupTerm.* , Soup.endpoint i side , e₂))
         (sym content ■ selected)
... | E , arg , refl , frameEq , argEq
  with discard-argument-var {E = E} {w = arg} ⊢source
         (T-value-inv arg
           (focusEnv ctx Typed.⟪
             SourceReduction._[_]* E
               (Source.K Source.`discard Source.·¹ arg)
           ⟫ (logicalChannels image) (λ ()))
           (focusValueEnv ctx Typed.⟪
             SourceReduction._[_]* E
               (Source.K Source.`discard Source.·¹ arg)
           ⟫ (logicalChannels image) (λ ()))
           (subst SoupExpression.Value (sym argEq) Vhandle))
... | x , refl =
  canon-redex-target cn
  , canon-discard-reduction cn
  , closeConfigStep exactStep
  where
  ⊢redex :
    [] ; Context.[] ⊢ₚ
      plug ctx Typed.⟪
        SourceReduction._[_]* E
          (Source.K Source.`discard Source.·¹ (Source.` x))
      ⟫
  ⊢redex = ⊢P

  bnd = Position.resolve ctx x

  head =
    impure-redex-head
      {ctx = ctx} {E = E} {c = Source.`discard} {x = x}
      ⊢redex Position.`discard

  cn =
    canon-discard E bnd
      (Canonical.headOfFirstGroup⇒shape bnd head) ⊢redex

  leaf =
    canon-discard-leaf cn ⊢P (canon-redex-image cn image)

  sameSlot =
    canon-discard-same-slot cn image leaf
      (cong (threadEmbedding (localImage image)) position ■ embedded)

  redexEq :
    discardFrame leaf SoupExpression.[
      SoupTerm.K SoupTerm.`discard SoupTerm.·¹ discardArgument leaf
    ]* ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`discard SoupTerm.·¹
        Translation.chanTriple (SoupTerm.* , Soup.endpoint i side , e₂)
    ]*
  redexEq =
    sym (discardSelected leaf) ■
    cong (lookup ts) sameSlot ■
    selected

  frameUnitEq :
    discardFrame leaf SoupExpression.[ SoupTerm.* ]* ≡
    F SoupExpression.[ SoupTerm.* ]*
  frameUnitEq =
    redex-frame-unique {n = 2 *ℕ n}
      {F = discardFrame leaf} {F′ = F}
      {c = SoupTerm.`discard} {c′ = SoupTerm.`discard}
      (discardTranslatedValue leaf) Vhandle redexEq SoupTerm.*

  exactStep :
    ForwardStep.ConfigStep
      (canon-redex-target cn) (λ ()) (λ _ → ⊥) (λ _ → ⊥)
      (Soup.config cs ts)
      (Soup.config cs
        (SoupReduction.replaceAt ts j
          (F SoupExpression.[ SoupTerm.* ]*)))
  exactStep =
    canon-discard-exact-step cn (canon-redex-image cn image) leaf
      sameSlot frameUnitEq
