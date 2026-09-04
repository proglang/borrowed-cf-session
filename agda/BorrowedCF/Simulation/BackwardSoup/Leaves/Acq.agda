-- | Backward simulation for the soup acquire leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Acq where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Relation.Unary.All as AllV
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅◅_) renaming (ε to ≋-refl)

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

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.Local.Acq
  using ( AcqStep; acq-step; acqThread; acqSlotEq
        ; acqPhysicalChannel; acqPhysicalSide; acqEndpoint; acqEndpointShape
        ; acqPhiSlot; acqBeforeFlags; acqAfterFlags
        ; acqPhiSlotZero; acqBeforeFlagsEmpty; acqFrame; acqTail
        ; acqArgument; acqTranslatedValue; acqArgument≡handle
        ; acqChannelFlags; acqSelected; acqConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( LocalImage; OptionalThreadImage; present; omitted; OrientedChannel
        ; threadEmbedding; live-thread)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated; env-separated; thread-separated)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.AcqShape
  using (acq-bind-shape)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (Canon; CanonAcq; canon; canon-acq; tracks-≡→≋ℕ; threadInContext-ℕ)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-pair-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( FocusedImage; focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread
        ; focusSeparated)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusChannels
        ; focusExprTyping; focusTyping; focusPairEnv; closedPairEnv
        ; threadInContext; plug; ≡→≋)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (resolve; binderTyping)
import BorrowedCF.Simulation.BackwardSoup.Position as Position
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using (Tracks; tracks-◅◅)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (endpoint-injective)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique; split-around-unique)
open import BorrowedCF.Simulation.Support.AcqInv
  using (fn-acq-dom)
open import BorrowedCF.Simulation.Support.Frames
  using (frame-plug₁)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  just-not-nothing : {A : Set} {x : A} → just x ≢ nothing
  just-not-nothing ()

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

  transportLocalChannels :
    {k n m : ℕ} {P : Typed.Proc k}
    {channels channels′ :
      Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set}
    {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    channels ≡ channels′ →
    LocalImage P channels sigma ambientChannel ambientThread C →
    LocalImage P channels′ sigma ambientChannel ambientThread C
  transportLocalChannels refl image = image

  threadEmbedding-transportLocalChannels :
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
    threadEmbedding (transportLocalChannels eq image) j ≡
    threadEmbedding image j
  threadEmbedding-transportLocalChannels refl image j = refl

  present-lookup :
    {n m : ℕ} {threads : Vec (Soup.Thread n) m}
    {slot : Maybe (𝔽 m)} {expected : Soup.Thread n} {j : 𝔽 m} →
    OptionalThreadImage {n = n} {m = m} threads slot expected →
    slot ≡ just j →
    lookup threads j ≡ expected
  present-lookup {threads = threads} {expected = expected}
    (present l slotEq content) same =
    subst (λ z → lookup threads z ≡ expected)
      (sym (just-injective (sym same ■ slotEq))) content
  present-lookup (omitted slotEq unitEq) same =
    ⊥-elim (just-not-nothing (sym same ■ slotEq))

  plug*-⋯ᵣ :
    {m n : ℕ} (E : SourceReduction.Frame* m) (t : Source.Tm m)
    (ρ : 𝔽 m → 𝔽 n) →
    Source._⋯_ (SourceReduction._[_]* E t) ρ ≡
    SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E ρ) (Source._⋯_ t ρ)
  plug*-⋯ᵣ [] t ρ = refl
  plug*-⋯ᵣ (F ∷ Es) t ρ =
    frame-plug₁ F ρ (λ _ → SourceReduction.V-`)
    ■ cong (SourceReduction._[_] (SourceReduction._⋯ᶠ_ F ρ))
        (plug*-⋯ᵣ Es t ρ)

  acq-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[ SoupTerm.K SoupTerm.`acq SoupTerm.·¹ v ]* →
    t ≢ SoupTerm.*
  acq-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  acq-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {γ : Context.Struct N}
      {arg : Source.Tm N} {U ϵ} →
    Γ ; γ ⊢ Source.K Source.`acq Source.·¹ arg ∶ U ∣ ϵ →
    Σ[ β ∈ Context.Struct N ] Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
    Σ[ s ∈ Types.𝕊 0 ]
      (Types.⟨ Types.acq Types.; s ⟩ Types.≃ R) ×
      (Γ ; β ⊢ arg ∶ R ∣ ϵ′)
  acq-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in _ , _ , _ , s , eq , ⊢arg
  acq-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in _ , _ , _ , s , eq , ⊢arg
  acq-arg-decomp (Source.T-Conv _ _ d) = acq-arg-decomp d
  acq-arg-decomp (Source.T-Weaken _ d) = acq-arg-decomp d

  ⟨⟩≄⊗ :
    ∀ {s T U d} → ¬ (Types.⟨ s ⟩ Types.≃ (T Types.⊗⟨ d ⟩ U))
  ⟨⟩≄⊗ ()

  pair-not-channel :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {a b : Source.Tm k} {R ϵ s} →
    Γ ; γ ⊢ a Source.⊗ b ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    ⊥
  pair-not-channel typed eq
    with Source.inv-⊗ typed
  ... | _ , _ , _ , _ , _ , _ , _ , _ , pairEq , _ =
    ⟨⟩≄⊗ (Types.≃-trans eq (Types.≃-sym pairEq))

  argument-var :
    ∀ {k n} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {sigma : Translation.Env k n}
      {arg : Source.Tm k} {s : Types.𝕊 0}
      {R : Types.𝕋} {ϵ : Types.Eff}
      {e₁ e₂ : SoupTerm.Tm n} {x : 𝔽 n} →
    Γ ; γ ⊢ arg ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    Translation.T[ arg ] sigma ≡ Translation.chanTriple (e₁ , x , e₂) →
    Σ[ y ∈ 𝔽 k ] arg ≡ Source.` y
  argument-var ⊢arg ch argEq
    with T-pair-inv _ _ argEq
  ... | inj₂ (y , varEq , _) = y , varEq
  ... | inj₁ (a , b , pairEq , _ , _) =
    ⊥-elim
      (pair-not-channel
        (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) pairEq ⊢arg)
        ch)

  acq-handle-injective :
    {n : ℕ} {endpoint endpoint′ : 𝔽 n} {slot slot′ : ℕ}
    {tail tail′ : SoupTerm.Tm n} →
    Translation.chanTriple
      (SoupTerm.`phi (endpoint , slot) , endpoint , tail) ≡
    Translation.chanTriple
      (SoupTerm.`phi (endpoint′ , slot′) , endpoint′ , tail′) →
    (endpoint ≡ endpoint′) × (slot ≡ slot′) × (tail ≡ tail′)
  acq-handle-injective refl = refl , refl , refl

  acq-replacement-cong :
    {n : ℕ} {F F′ : SoupExpression.Frame* n}
    {endpoint endpoint′ : 𝔽 n} {slot slot′ : ℕ}
    {tail tail′ : SoupTerm.Tm n} →
    endpoint ≡ endpoint′ → slot ≡ slot′ → tail ≡ tail′ →
    ((t : SoupTerm.Tm n) →
      F SoupExpression.[ t ]* ≡ F′ SoupExpression.[ t ]*) →
    SoupReduction.consumePhi endpoint slot
      (F SoupExpression.[
        Translation.chanTriple (SoupTerm.* , endpoint , tail) ]*) ≡
    SoupReduction.consumePhi endpoint′ slot′
      (F′ SoupExpression.[
        Translation.chanTriple (SoupTerm.* , endpoint′ , tail′) ]*)
  acq-replacement-cong refl refl refl frameEq =
    cong (SoupReduction.consumePhi _ _) (frameEq _)

------------------------------------------------------------------------
-- A strict soup acquire reflects to the canonical typed `R-Acq`.

acq-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (before after : List Soup.Flag) {tail : Soup.Thread n} →
  SoupReduction.is-open cs i →
  SoupReduction.endpointFlags (lookup cs i) side ≡
    before ++ Soup.acq ∷ after →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹
        Translation.chanTriple
          ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
          , Soup.endpoint i side
          , tail )
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config
        (V.updateAt cs i
          (SoupReduction.setEndpointFlags side (before ++ after)))
        (let endpoint = Soup.endpoint i side
             slot = L.length before
             ts′ = V.map (SoupReduction.consumePhi endpoint slot) ts
         in SoupReduction.replaceAt ts′ j
              (SoupReduction.consumePhi endpoint slot
                (F SoupExpression.[
                  Translation.chanTriple (SoupTerm.* , endpoint , tail) ]*))))
acq-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j i side F before after {tail} openEq flagsEq selected ⊢P image
  with image-thread-term image j
         (acq-redex-not-unit {F = F} selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F Source.`acq Types.𝟙
         (Translation.chanTriple
           ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
           , Soup.endpoint i side
           , tail ))
         (sym content ■ selected)
... | E , arg , sourceEq , frameEq , argEq
  with SourceReduction.⊢[]*⁻¹ E (Source.K Source.`acq Source.·¹ arg)
         (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) sourceEq ⊢source)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E , ⊢app
  with acq-arg-decomp ⊢app
... | β , R , ϵ′ , s , argTy , ⊢arg
  with argument-var ⊢arg argTy argEq
... | x , refl
  with binderTyping (resolve ctx x)
         Typed.⟪ E SourceReduction.[
           Source.K Source.`acq Source.·¹ (Source.` x) ]* ⟫
         (subst
           (λ z → [] ; Context.[] ⊢ₚ plug ctx Typed.⟪ z ⟫)
           sourceEq ⊢P)
... | Γᵇ , γᵇ , Γ₁ , Γ₂ , sᵇ , pᵇ , Γᵇ-S , newᵇ
      , typed₁ , typed₂ , bind₁ , bind₂ , ⊢body =
  targetProc
  , TypedReduction.R-Struct redex≋ typedStep ≋-refl
  , closeConfigStep exactStep
  where
  redexTerm : Source.Tm k
  redexTerm = E SourceReduction.[
    Source.K Source.`acq Source.·¹ (Source.` x) ]*

  redexLocal : Typed.Proc k
  redexLocal = Typed.⟪ redexTerm ⟫

  redexProc : Typed.Proc 0
  redexProc = plug ctx redexLocal

  sourceToRedex : P Typed.≋ redexProc
  sourceToRedex =
    ≡→≋ (cong (plug ctx ∘ Typed.⟪_⟫) sourceEq)

  sourceToRedexTracks :
    Tracks sourceToRedex
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext ctx redexLocal 0F)
  sourceToRedexTracks =
    tracks-≡→≋ℕ
      (cong (plug ctx ∘ Typed.⟪_⟫) sourceEq)
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext-ℕ ctx redexLocal Typed.⟪ source ⟫ 0F 0F refl)

  ⊢redex : [] ; Context.[] ⊢ₚ redexProc
  ⊢redex =
    subst
      (λ z → [] ; Context.[] ⊢ₚ plug ctx Typed.⟪ z ⟫)
      sourceEq ⊢P

  bnd = resolve ctx x

  preCanon = canon redexTerm bnd

  open Canon preCanon
    renaming ( above′ to preAbove; ρ to preRho; resid to preResid
             ; ≋-canon to pre≋; x-eq to preXEq; tracks to preTracks)

  preLocal : Typed.Proc _
  preLocal =
    Typed.ν (Position.Binder.B₁ bnd) (Position.Binder.B₂ bnd)
      (Typed.⟪ Source._⋯_ redexTerm preRho ⟫ Typed.∥ preResid)

  preProc : Typed.Proc 0
  preProc = plug preAbove preLocal

  redexGlobal = transportGlobalImage sourceToRedex image
  preGlobal = transportGlobalImage pre≋ redexGlobal

  preChannels = focusChannels preAbove preLocal (logicalChannels preGlobal)
  preChannel : OrientedChannel n
  preChannel = V.head preChannels
  preBodyChannels = V.tail preChannels
  preChannelsSplit = sym (cons-head-tail preChannels)

  preFocused = focusImage preAbove preLocal (localImage preGlobal)

  preRestrictionImage =
    subst
      (λ channels →
        LocalImage preLocal channels
          (focusEnv preAbove preLocal (logicalChannels preGlobal) (λ ()))
          (focusedAmbientChannel preFocused)
          (focusedAmbientThread preFocused)
          (Soup.config cs ts))
      preChannelsSplit
      (focused-image preFocused)

  preBodyImage = res-split-image preRestrictionImage
  preLeftImage = par-split-left preBodyImage

  sourceSlot :
    threadEmbedding (localImage image)
      (threadInContext ctx Typed.⟪ source ⟫ 0F) ≡ just j
  sourceSlot = cong (threadEmbedding (localImage image)) position ■ embedded

  redexSlot :
    threadEmbedding (localImage redexGlobal)
      (threadInContext ctx redexLocal 0F) ≡ just j
  redexSlot =
    transportGlobalSlot sourceToRedex image sourceToRedexTracks sourceSlot

  preLeftToFocused :
    threadEmbedding preLeftImage 0F ≡
    threadEmbedding (focused-image preFocused) 0F
  preLeftToFocused =
    threadEmbedding-subst preChannelsSplit (focused-image preFocused)
      (0F ↑ˡ Translation.processCount preResid)

  preFocusedToGlobal :
    threadEmbedding (focused-image preFocused) 0F ≡
    threadEmbedding (localImage preGlobal)
      (threadInContext preAbove preLocal 0F)
  preFocusedToGlobal =
    focusImage-thread preAbove preLocal (localImage preGlobal) 0F

  preGlobalSlot :
    threadEmbedding (localImage preGlobal)
      (threadInContext preAbove preLocal 0F) ≡ just j
  preGlobalSlot =
    transportGlobalSlot pre≋ redexGlobal preTracks redexSlot

  preSameSlot : threadEmbedding preLeftImage 0F ≡ just j
  preSameSlot = preLeftToFocused ■ preFocusedToGlobal ■ preGlobalSlot

  preThreadEq :
    lookup ts j ≡ Translation.T[ Source._⋯_ redexTerm preRho ]
      (bindEnv (Position.Binder.B₁ bnd) (Position.Binder.B₂ bnd) preChannel
        (focusEnv preAbove preLocal (logicalChannels preGlobal) (λ ())))
  preThreadEq = present-lookup (live-thread preLeftImage 0F) preSameSlot

  preSigma : Translation.Env (Canon.midᶜ preCanon) (2 *ℕ n)
  preSigma = focusEnv preAbove preLocal (logicalChannels preGlobal) (λ ())
  preEnv :
    Translation.Env
      (sum (Position.Binder.B₁ bnd) + sum (Position.Binder.B₂ bnd) +
       Canon.midᶜ preCanon)
      (2 *ℕ n)
  preEnv = bindEnv (Position.Binder.B₁ bnd) (Position.Binder.B₂ bnd)
    preChannel preSigma
  preValueSigma : ValueEnv preSigma
  preValueSigma = focusValueEnv preAbove preLocal (logicalChannels preGlobal) (λ ())
  preValueEnv : ValueEnv preEnv
  preValueEnv =
    bindEnv-Value
      {B₁ = Position.Binder.B₁ bnd}
      {B₂ = Position.Binder.B₂ bnd}
      {channel = preChannel}
      preValueSigma
  preFrame : SoupExpression.Frame* (2 *ℕ n)
  preFrame = Tᶠ*[ SourceReduction._⋯ᶠ*_ E preRho ] preValueEnv

  renamedTermEq :
    Source._⋯_ redexTerm preRho ≡
    SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E preRho)
      (Source.K Source.`acq Source.·¹
        (Source.` (Position.Binder.local bnd ↑ˡ Canon.midᶜ preCanon)))
  renamedTermEq =
    plug*-⋯ᵣ E (Source.K Source.`acq Source.·¹ (Source.` x)) preRho
    ■ cong
        (λ z → SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E preRho)
          (Source.K Source.`acq Source.·¹ (Source.` z)))
        preXEq

  preSelected :
    lookup ts j ≡
    preFrame SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹
        preEnv (Position.Binder.local bnd ↑ˡ Canon.midᶜ preCanon) ]*
  preSelected =
    preThreadEq
    ■ cong (λ z → Translation.T[ z ] preEnv) renamedTermEq
    ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E preRho) preValueEnv

  concreteValue :
    SoupExpression.Value
      (Translation.chanTriple
        ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
        , Soup.endpoint i side
        , tail ))
  concreteValue =
    subst SoupExpression.Value argEq
      (focusValueEnv ctx Typed.⟪ source ⟫
        (logicalChannels image) (λ ()) x)

  preRedexEq :
    preFrame SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹
        preEnv (Position.Binder.local bnd ↑ˡ Canon.midᶜ preCanon) ]* ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹
        Translation.chanTriple
          ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
          , Soup.endpoint i side
          , tail ) ]*
  preRedexEq = sym preSelected ■ selected

  preArgumentEq :
    preEnv (Position.Binder.local bnd ↑ˡ Canon.midᶜ preCanon) ≡
    Translation.chanTriple
      ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
      , Soup.endpoint i side
      , tail )
  preArgumentEq =
    proj₁ (proj₂
      (redex-unique
        {F = preFrame} {F′ = F}
        {c = Source.`acq} {c′ = Source.`acq}
        (preValueEnv (Position.Binder.local bnd ↑ˡ Canon.midᶜ preCanon))
        concreteValue preRedexEq))

  preChannelEq = res-split-channel preRestrictionImage

  shape =
    acq-bind-shape {n = n} {k = Canon.midᶜ preCanon}
      (Position.Binder.B₁ bnd) (Position.Binder.B₂ bnd)
      typed₁ typed₂ preChannel preSigma (Position.Binder.local bnd)
      cs i side before after preChannelEq preArgumentEq flagsEq

  canonical :
    CanonAcq redexProc (threadInContext ctx redexLocal 0F)
  canonical = canon-acq E bnd shape

  open CanonAcq canonical

  localRedex : Typed.Proc (CanonAcq.midᵃ canonical)
  localRedex =
    Typed.ν (zero ∷ suc ba ∷ D₁) D₂
      (Typed.⟪ E₀ SourceReduction.[
         Source.K Source.`acq Source.·¹ (Source.` 0F) ]* ⟫
       Typed.∥ Q₀)

  localTarget : Typed.Proc (CanonAcq.midᵃ canonical)
  localTarget =
    Typed.ν (suc ba ∷ D₁) D₂
      (Typed.⟪ E₀ SourceReduction.[ Source.` 0F ]* ⟫ Typed.∥ Q₀)

  canonicalRedex : Typed.Proc 0
  canonicalRedex = plug above′ localRedex

  targetProc : Typed.Proc 0
  targetProc = plug above′ localTarget

  redex≋ : P Typed.≋ canonicalRedex
  redex≋ =
    sourceToRedex ◅◅ ≋-redex

  redexTracks :
    Tracks redex≋
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext above′ localRedex 0F)
  redexTracks = tracks-◅◅ sourceToRedexTracks tracks

  typedStep : canonicalRedex TypedReduction.─→ₚ targetProc
  typedStep = plug-red above′ (TypedReduction.R-Acq {E = E₀})

  canonicalGlobal : GlobalImage canonicalRedex (Soup.config cs ts)
  canonicalGlobal = transportGlobalImage redex≋ image

  canonicalImage :
    LocalImage canonicalRedex (logicalChannels canonicalGlobal)
      (λ ()) (λ _ → ⊥) (λ _ → ⊥) (Soup.config cs ts)
  canonicalImage = localImage canonicalGlobal

  canonicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount localRedex)
  canonicalChannels = focusChannels above′ localRedex (logicalChannels canonicalGlobal)
  canonicalChannel : OrientedChannel n
  canonicalChannel = V.head canonicalChannels
  canonicalBodyChannels :
    Vec (OrientedChannel n) (Translation.channelCount localRedex Nat.∸ 1)
  canonicalBodyChannels = V.tail canonicalChannels
  canonicalChannelsSplit :
    canonicalChannels ≡ canonicalChannel ∷ canonicalBodyChannels
  canonicalChannelsSplit = sym (cons-head-tail canonicalChannels)

  focused :
    FocusedImage above′ localRedex (logicalChannels canonicalGlobal)
      (λ ()) (λ _ → ⊥) (λ _ → ⊥) (Soup.config cs ts)
  focused = focusImage above′ localRedex canonicalImage

  adjustedImage :
    LocalImage localRedex (canonicalChannel ∷ canonicalBodyChannels)
      (focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ()))
      (focusedAmbientChannel focused) (focusedAmbientThread focused)
      (Soup.config cs ts)
  adjustedImage =
    transportLocalChannels canonicalChannelsSplit (focused-image focused)

  closedSeparated :
    Separated (λ ()) (λ _ → ⊥) (λ _ → ⊥) (Soup.config cs ts)
  closedSeparated = record
    { env-separated = λ ()
    ; thread-separated = λ _ ()
    }

  localSeparated :
    Separated
      (focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ()))
      (focusedAmbientChannel focused) (focusedAmbientThread focused)
      (Soup.config cs ts)
  localSeparated =
    focusSeparated above′ localRedex closedSeparated canonicalImage

  localValueEnv :
    ValueEnv
      (focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ()))
  localValueEnv =
    focusValueEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ())

  leaf :
    AcqStep localTarget
      (focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ()))
      (focusedAmbientChannel focused) (focusedAmbientThread focused)
      (Soup.config cs ts) adjustedImage
  leaf =
    acq-step
      {b₁ = ba} {B₁ = D₁} {B₂ = D₂} {E = E₀} {P = Q₀}
      {channel = canonicalChannel} {bodyChannels = canonicalBodyChannels}
      localSeparated localValueEnv adjustedImage

  trackedSlot :
    threadEmbedding canonicalImage (threadInContext above′ localRedex 0F) ≡
    just j
  trackedSlot = transportGlobalSlot redex≋ image redexTracks sourceSlot

  focusedSlot :
    threadEmbedding (focused-image focused) 0F ≡
    threadEmbedding canonicalImage (threadInContext above′ localRedex 0F)
  focusedSlot = focusImage-thread above′ localRedex canonicalImage 0F

  adjustedSlot :
    threadEmbedding adjustedImage 0F ≡
    threadEmbedding (focused-image focused) 0F
  adjustedSlot =
    threadEmbedding-transportLocalChannels canonicalChannelsSplit
      (focused-image focused) 0F

  sameSlot : acqThread leaf ≡ j
  sameSlot =
    just-injective
      (sym (acqSlotEq leaf) ■ adjustedSlot ■ focusedSlot ■ trackedSlot)

  redexEq :
    acqFrame leaf SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹ acqArgument leaf ]* ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`acq SoupTerm.·¹
        Translation.chanTriple
          ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
          , Soup.endpoint i side
          , tail ) ]*
  redexEq = sym (acqSelected leaf) ■ cong (lookup ts) sameSlot ■ selected

  handleEq :
    acqArgument leaf ≡
    Translation.chanTriple
      ( SoupTerm.`phi (Soup.endpoint i side , L.length before)
      , Soup.endpoint i side
      , tail )
  handleEq =
    proj₁ (proj₂
      (redex-unique
        {F = acqFrame leaf} {F′ = F}
        {c = Source.`acq} {c′ = Source.`acq}
        (acqTranslatedValue leaf) concreteValue redexEq))

  handleParts =
    acq-handle-injective (sym (acqArgument≡handle leaf) ■ handleEq)

  endpointEq : acqEndpoint leaf ≡ Soup.endpoint i side
  endpointEq = proj₁ handleParts

  phiSlotEq : acqPhiSlot leaf ≡ L.length before
  phiSlotEq = proj₁ (proj₂ handleParts)

  tailEq : acqTail leaf ≡ tail
  tailEq = proj₂ (proj₂ handleParts)

  physicalEndpointEq = sym (acqEndpointShape leaf) ■ endpointEq
  channelEq = proj₁ (endpoint-injective {n = n} physicalEndpointEq)
  endpointSideEq = proj₂ (endpoint-injective {n = n} physicalEndpointEq)

  canonicalFlagsEq :
    SoupReduction.endpointFlags (lookup cs i) side ≡
    [] ++ Soup.acq ∷ acqAfterFlags leaf
  canonicalFlagsEq =
    subst₂
      (λ i′ side′ →
        SoupReduction.endpointFlags (lookup cs i′) side′ ≡
        [] ++ Soup.acq ∷ acqAfterFlags leaf)
      channelEq endpointSideEq
      (acqChannelFlags leaf
       ■ cong (λ prefix → prefix ++ Soup.acq ∷ acqAfterFlags leaf)
           (acqBeforeFlagsEmpty leaf))

  flagSplit : before ≡ [] × after ≡ acqAfterFlags leaf
  flagSplit =
    split-around-unique
      (sym flagsEq ■ canonicalFlagsEq)
      (sym phiSlotEq ■ acqPhiSlotZero leaf)

  targetFlagsEq : acqAfterFlags leaf ≡ before ++ after
  targetFlagsEq =
    sym
      (cong₂ (λ before′ after′ → before′ ++ after′)
        (proj₁ flagSplit) (proj₂ flagSplit))

  framePlugEq :
    (t : SoupTerm.Tm (2 *ℕ n)) →
    acqFrame leaf SoupExpression.[ t ]* ≡ F SoupExpression.[ t ]*
  framePlugEq =
    proj₂ (proj₂
      (redex-unique
        {F = acqFrame leaf} {F′ = F}
        {c = Source.`acq} {c′ = Source.`acq}
        (acqTranslatedValue leaf) concreteValue redexEq))

  replacementEq :
    SoupReduction.consumePhi (acqEndpoint leaf) (acqPhiSlot leaf)
      (acqFrame leaf SoupExpression.[
        Translation.chanTriple
          (SoupTerm.* , acqEndpoint leaf , acqTail leaf) ]*) ≡
    SoupReduction.consumePhi (Soup.endpoint i side) (L.length before)
      (F SoupExpression.[
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side , tail) ]*)
  replacementEq =
    acq-replacement-cong
      {F = acqFrame leaf} {F′ = F}
      {endpoint = acqEndpoint leaf} {endpoint′ = Soup.endpoint i side}
      {slot = acqPhiSlot leaf} {slot′ = L.length before}
      {tail = acqTail leaf} {tail′ = tail}
      endpointEq phiSlotEq tailEq framePlugEq

  exactStep =
    ascend focused
      (acqConfigStepAt leaf channelEq endpointSideEq sameSlot endpointEq
        phiSlotEq targetFlagsEq replacementEq)
