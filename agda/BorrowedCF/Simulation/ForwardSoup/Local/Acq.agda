-- | Phase 3, leaf rule `R-Acq` (`ForwardSoup/PLAN.md`, §4, Phase 3, item 7
--   and §4.5).
--
--   The source redex reacquires the head borrow of the *second* group of the
--   first binder block, beside a residual process `P`:
--
--     ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P)
--       ─→ₚ
--     ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ]* ⟫ ∥ P)
--
--   `sum (zero ∷ suc b₁ ∷ B₁)` *is* `sum (suc b₁ ∷ B₁)`, so no renaming is
--   involved: `E` and `P` are literally shared by redex and reduct, and only
--   the binder *environment* changes — the head group vanishes and every
--   φ-cell of the endpoint slides down by one.  That is exactly what
--   `RUS-Acquire` does to the soup: it drops flag `0` of the endpoint and maps
--   `consumePhi x 0` over *every* thread.
--
--   Consequently this is the only leaf that needs `Separated`: the ambient
--   threads must survive the global rewrite, which they do because they never
--   mention a φ-cell of a channel they do not own.  The `consumePhi` algebra
--   is in `Local/AcqSupport.agda`; here it is assembled in the usual shape
--   `res-split` → `par-split-left`/`-right` → `RUS-Acquire` →
--   `par-join`/`res-join` → `identity-step`.
module BorrowedCF.Simulation.ForwardSoup.Local.Acq where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*; T[_]-Env-cong)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads; bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated; env-separated; thread-separated; UB-phiFree-init)
open import BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- Exact evidence for the acquire leaf.

record AcqStep
  {k n m b₁ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n) (Translation.channelCount P)}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image : LocalImage
    (Typed.ν (0 ∷ suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K Source.`acq) (Source.` 0F)) ⟫
       Typed.∥ P))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) : Set where
  field
    acqThread : 𝔽 m
    acqSlotEq : threadEmbedding image zero ≡ just acqThread

    acqPhysicalChannel : 𝔽 n
    acqPhysicalSide : 𝔽 2
    acqEndpoint : 𝔽 (2 *ℕ n)
    acqPhiSlot : ℕ
    acqBeforeFlags acqAfterFlags : List Soup.Flag

    acqFrame : SoupExpression.Frame* (2 *ℕ n)
    acqTail acqArgument : Soup.Thread n

    acqSourceValue :
      SoupExpression.Value
        (bindEnv (0 ∷ suc b₁ ∷ B₁) B₂ channel sigma 0F)
    acqTranslatedValue :
      SoupExpression.Value acqArgument
    acqArgument≡source :
      acqArgument ≡ bindEnv (0 ∷ suc b₁ ∷ B₁) B₂ channel sigma 0F
    acqArgument≡handle :
      acqArgument ≡
      Translation.chanTriple
        (SoupTerm.`phi (acqEndpoint , acqPhiSlot) , acqEndpoint , acqTail)

    acqChannelOpen :
      proj₁ (lookup (Soup.channels C) acqPhysicalChannel) ≡ true
    acqChannelFlags :
      SoupReduction.endpointFlags
        (lookup (Soup.channels C) acqPhysicalChannel) acqPhysicalSide ≡
      acqBeforeFlags L.++ Soup.acq ∷ acqAfterFlags

    acqSelectedSource :
      lookup (Soup.threads C) acqThread ≡
      Translation.T[
        SourceReduction._[_]* E
          (Source._·¹_ (Source.K Source.`acq) (Source.` 0F))
      ] (bindEnv (0 ∷ suc b₁ ∷ B₁) B₂ channel sigma)
    acqSelected :
      lookup (Soup.threads C) acqThread ≡
      SoupExpression._[_]* acqFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`acq) acqArgument)

    acqConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config
          (V.updateAt (Soup.channels C) acqPhysicalChannel
            (SoupReduction.setEndpointFlags acqPhysicalSide acqAfterFlags))
          (let x = acqEndpoint
               k = acqPhiSlot
               ts′ = V.map (SoupReduction.consumePhi x k) (Soup.threads C)
           in SoupReduction.replaceAt ts′ acqThread
                (SoupReduction.consumePhi x k
                  (SoupExpression._[_]* acqFrame
                    (Translation.chanTriple (SoupTerm.* , x , acqTail))))))

open AcqStep public

------------------------------------------------------------------------
-- The leaf.

acq-step :
  {k n m b₁ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  Separated sigma ambientChannel ambientThread C →
  ValueEnv sigma →
  (image : LocalImage
    (Typed.ν (0 ∷ suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K Source.`acq) (Source.` 0F)) ⟫
       Typed.∥ P))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
  AcqStep
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E (Source.` 0F) ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C image
acq-step {k = k} {n = n} {m = m} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂}
  {E = E} {P = P} {channel = channel} {bodyChannels = bodyChannels}
  {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
  separated Vsigma image =
  dispatch (live-thread left 0F)
  where
  ----------------------------------------------------------------------
  -- The bound channel, physically.

  physical : 𝔽 n
  physical = physicalChannel channel

  orientation : Orientation
  orientation = proj₂ channel

  side₁ : 𝔽 2
  side₁ = orientSide orientation 0F

  end₁ end₂ : 𝔽 (2 *ℕ n)
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

  ends-apart : end₁ ≢ end₂
  ends-apart = physicalEndpoint-distinct channel

  ----------------------------------------------------------------------
  -- The two body environments.  `sum (0 ∷ suc b₁ ∷ B₁)` is
  -- `sum (suc b₁ ∷ B₁)`, so they have the same domain.

  env : Translation.Env (sum (0 ∷ suc b₁ ∷ B₁) + sum B₂ + k) (2 *ℕ n)
  env = bindEnv (0 ∷ suc b₁ ∷ B₁) B₂ channel sigma

  env′ : Translation.Env (sum (suc b₁ ∷ B₁) + sum B₂ + k) (2 *ℕ n)
  env′ = bindEnv (suc b₁ ∷ B₁) B₂ channel sigma

  Venv : ValueEnv env
  Venv =
    bindEnv-Value {B₁ = 0 ∷ suc b₁ ∷ B₁} {B₂ = B₂} {channel = channel} Vsigma

  Vconsumed : ValueEnv (consumeEnv end₁ 0 env)
  Vconsumed = consumeEnv-Value end₁ 0 Venv

  binderEnv₁ : Translation.Env (sum (0 ∷ suc b₁ ∷ B₁)) (2 *ℕ n)
  binderEnv₁ =
    proj₁ (Translation.UB[ 0 ∷ suc b₁ ∷ B₁ ] end₁
            (SoupTerm.* , end₁ , SoupTerm.*))

  binderEnv₁′ : Translation.Env (sum (suc b₁ ∷ B₁)) (2 *ℕ n)
  binderEnv₁′ =
    proj₁ (Translation.UB[ suc b₁ ∷ B₁ ] end₁
            (SoupTerm.* , end₁ , SoupTerm.*))

  binderEnv₂ : Translation.Env (sum B₂) (2 *ℕ n)
  binderEnv₂ =
    proj₁ (Translation.UB[ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

  ----------------------------------------------------------------------
  -- The acquired handle is the head of the surviving group, sitting at
  -- offset `1` of the binder block: its φ-cell is number `0`.

  head₁ =
    UBFrom-head 1 b₁ B₁ end₁ end₁ (SoupTerm.`phi (end₁ , 0)) SoupTerm.*

  tail₁ : SoupTerm.Tm (2 *ℕ n)
  tail₁ = proj₁ head₁

  triple₁ : SoupTerm.Tm (2 *ℕ n)
  triple₁ =
    Translation.chanTriple (SoupTerm.`phi (end₁ , 0) , end₁ , tail₁)

  handleEq : env 0F ≡ triple₁
  handleEq =
    ++ₛ-lookupˡ (binderEnv₁ Translation.++ₛ binderEnv₂) sigma
      (0F ↑ˡ sum B₂)
    ■ ++ₛ-lookupˡ binderEnv₁ binderEnv₂ 0F
    ■ proj₂ head₁

  ----------------------------------------------------------------------
  -- The flag lists of the bound channel.  The redex carries the extra
  -- `ϕ[ 0 ] = acq` in front of the reduct's list.

  tailFlags : List Soup.Flag
  tailFlags =
    proj₂ (Translation.UBFrom 1 (suc b₁ ∷ B₁) end₁
            (SoupTerm.`phi (end₁ , 0) , end₁ , SoupTerm.*))

  flags₂ : List Soup.Flag
  flags₂ =
    proj₂ (Translation.UB[ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

  ----------------------------------------------------------------------
  -- The source terms.

  redex : Source.Tm (sum (0 ∷ suc b₁ ∷ B₁) + sum B₂ + k)
  redex = Source._·¹_ (Source.K Source.`acq) (Source.` 0F)

  owner : Source.Tm (sum (0 ∷ suc b₁ ∷ B₁) + sum B₂ + k)
  owner = SourceReduction._[_]* E redex

  target : Source.Tm (sum (suc b₁ ∷ B₁) + sum B₂ + k)
  target = SourceReduction._[_]* E (Source.` 0F)

  reduct : Typed.Proc k
  reduct = Typed.ν (suc b₁ ∷ B₁) B₂ (Typed.⟪ target ⟫ Typed.∥ P)

  ----------------------------------------------------------------------
  -- Splitting the frame.

  body = res-split-image image
  chanEq = res-split-channel image
  notAmb = res-split-not-ambient image

  left = par-split-left body
  right = par-split-right body

  ambientChannelLeft : 𝔽 n → Set
  ambientChannelLeft =
    (aC ∪ᵖ singletonᵖ physical) ∪ᵖ ownedChannels bodyChannels

  ambientThreadLeft : 𝔽 m → Set
  ambientThreadLeft =
    aT ∪ᵖ ownedThreads (threadEmbedding body ∘ (1 ↑ʳ_))

  ----------------------------------------------------------------------
  -- The environment of the reduct is the environment of the redex with
  -- φ-cell `0` of `end₁` consumed.

  binderCoh₁ :
    (y : 𝔽 (sum (suc b₁ ∷ B₁))) →
    SoupReduction.consumePhi end₁ 0 (binderEnv₁ y) ≡ binderEnv₁′ y
  binderCoh₁ y =
    UBFrom-consumePhi 0 (suc b₁ ∷ B₁) end₁ end₁
      (SoupTerm.`phi (end₁ , 0)) SoupTerm.* y
    ■ cong
        (λ t →
          proj₁ (Translation.UBFrom 0 (suc b₁ ∷ B₁) end₁
                  (t , end₁ , SoupTerm.*)) y)
        (consumePhi-hit end₁)

  binderCoh₂ :
    (y : 𝔽 (sum B₂)) →
    SoupReduction.consumePhi end₁ 0 (binderEnv₂ y) ≡ binderEnv₂ y
  binderCoh₂ = UB-phiFree-init B₂ end₁ end₂ 0 ends-apart

  sigmaCoh :
    (y : 𝔽 k) → SoupReduction.consumePhi end₁ 0 (sigma y) ≡ sigma y
  sigmaCoh y = env-separated separated y physical side₁ 0 notAmb

  envCoh :
    (y : 𝔽 (sum (0 ∷ suc b₁ ∷ B₁) + sum B₂ + k)) →
    SoupReduction.consumePhi end₁ 0 (env y) ≡ env′ y
  envCoh =
    ++ₛ-consumePhi end₁ 0
      (binderEnv₁ Translation.++ₛ binderEnv₂)
      (binderEnv₁′ Translation.++ₛ binderEnv₂)
      sigma sigma
      (++ₛ-consumePhi end₁ 0 binderEnv₁ binderEnv₁′ binderEnv₂ binderEnv₂
        binderCoh₁ binderCoh₂)
      sigmaCoh

  ----------------------------------------------------------------------
  -- The soup frame and the expected owner thread.

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ E ] {σ = env} Venv

  expected : Soup.Thread n
  expected = Translation.T[ owner ] env

  ----------------------------------------------------------------------
  -- The bound channel is open and carries `acq` in front of `tailFlags`.

  openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
  openEq = cong proj₁ chanEq ■ open-orient orientation _

  flagsEq :
    SoupReduction.endpointFlags (lookup (Soup.channels C) physical) side₁ ≡
    [] L.++ Soup.acq ∷ tailFlags
  flagsEq =
    cong (λ ch → SoupReduction.endpointFlags ch side₁) chanEq
    ■ endpointFlags-orient orientation
        (true , Soup.acq ∷ tailFlags , flags₂) 0F

  targetChannels : Vec Soup.Channel n
  targetChannels =
    V.updateAt (Soup.channels C) physical
      (SoupReduction.setEndpointFlags side₁ tailFlags)

  newChanEq :
    lookup targetChannels physical ≡ bindChannel (suc b₁ ∷ B₁) B₂ channel
  newChanEq =
    V.lookup∘updateAt physical (Soup.channels C)
    ■ cong (SoupReduction.setEndpointFlags side₁ tailFlags) chanEq
    ■ setEndpointFlags-orient orientation
        (true , Soup.acq ∷ tailFlags , flags₂) 0F tailFlags
    ■ cong
        (λ flags → orientChannel orientation (true , flags , flags₂))
        (sym
          (UBFrom-flags-cong 0 1 (suc b₁ ∷ B₁)
            end₁ (SoupTerm.* , end₁ , SoupTerm.*)
            end₁ (SoupTerm.`phi (end₁ , 0) , end₁ , SoupTerm.*)))

  ----------------------------------------------------------------------
  -- The case analysis on the owner thread.

  dispatch :
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 0F) expected →
    AcqStep
      {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
      {channel = channel} {bodyChannels = bodyChannels}
      reduct sigma aC aT C image

  dispatch (omitted slotEq expectedEq) =
    ⊥-elim
      (plug-not-K F (sym (T[_]-plugᶠ* E {e = redex} Venv) ■ expectedEq))

  dispatch (present j slotEq lookupEq) =
    record
      { acqThread = j
      ; acqSlotEq = slotEq
      ; acqPhysicalChannel = physical
      ; acqPhysicalSide = side₁
      ; acqEndpoint = end₁
      ; acqPhiSlot = 0
      ; acqBeforeFlags = []
      ; acqAfterFlags = tailFlags
      ; acqFrame = F
      ; acqTail = tail₁
      ; acqArgument = triple₁
      ; acqSourceValue = Venv 0F
      ; acqTranslatedValue = subst SoupExpression.Value handleEq (Venv 0F)
      ; acqArgument≡source = sym handleEq
      ; acqArgument≡handle = refl
      ; acqChannelOpen = openEq
      ; acqChannelFlags = flagsEq
      ; acqSelectedSource = lookupEq
      ; acqSelected = selected
      ; acqConfigStep =
          identity-config-step
            soupStep ambientChannelsUnchanged ambientThreadsUnchanged
            (res-join joined newChanEq notAmb)
      }
    where
    ------------------------------------------------------------------
    -- The step.

    selected :
      lookup (Soup.threads C) j ≡
      SoupExpression._[_]* F
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`acq) triple₁)
    selected =
      lookupEq
      ■ T[_]-plugᶠ* E {e = redex} Venv
      ■ cong
          (λ handle →
            SoupExpression._[_]* F
              (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`acq) handle))
          handleEq

    acquired : SoupTerm.Tm (2 *ℕ n)
    acquired = Translation.chanTriple (SoupTerm.* , end₁ , tail₁)

    consumedThreads : Vec (Soup.Thread n) m
    consumedThreads =
      V.map (SoupReduction.consumePhi end₁ 0) (Soup.threads C)

    targetThreads : Vec (Soup.Thread n) m
    targetThreads =
      SoupReduction.replaceAt consumedThreads j
        (SoupReduction.consumePhi end₁ 0
          (SoupExpression._[_]* F acquired))

    targetConfig : Soup.Config n m
    targetConfig = Soup.config targetChannels targetThreads

    soupStep : C SoupReduction.─→ₚ targetConfig
    soupStep =
      SoupReduction.RUS-Acquire
        {cs = Soup.channels C} {ts = Soup.threads C}
        j physical side₁ F [] tailFlags {e = tail₁}
        openEq flagsEq selected

    ------------------------------------------------------------------
    -- The frame is untouched: the only rewritten channel is the bound one,
    -- and the ambient threads are φ-free for its endpoint.

    ambientChannelsUnchanged :
      (i : 𝔽 n) → aC i →
      lookup targetChannels i ≡ lookup (Soup.channels C) i
    ambientChannelsUnchanged i ambient =
      V.lookup∘updateAt′ i physical
        (λ eq → notAmb (subst aC eq ambient))
        (Soup.channels C)

    ambientThreadsUnchanged :
      (l′ : 𝔽 m) → aT l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    ambientThreadsUnchanged l′ ambient =
      V.lookup∘updateAt′ l′ j
        (λ eq → thread-not-ambient left slotEq (inj₁ (subst aT eq ambient)))
        consumedThreads
      ■ V.lookup-map l′ (SoupReduction.consumePhi end₁ 0) (Soup.threads C)
      ■ thread-separated separated l′ ambient physical side₁ 0 notAmb

    ------------------------------------------------------------------
    -- The image of the owner after the step.  Consuming φ-cell `0` turns
    -- the acquired handle into the reduct's environment entry.

    tripleEq :
      SoupReduction.consumePhi end₁ 0 acquired ≡ consumeEnv end₁ 0 env 0F
    tripleEq =
      sym
        ( cong (SoupReduction.consumePhi end₁ 0) handleEq
        ■ cong
            (λ t →
              Translation.chanTriple
                (t , end₁ , SoupReduction.consumePhi end₁ 0 tail₁))
            (consumePhi-hit end₁)
        )

    targetThread : lookup targetThreads j ≡ Translation.T[ target ] env′
    targetThread =
      V.lookup∘updateAt j consumedThreads
      ■ Tᶠ*-plug-consumePhi E Venv end₁ 0 Vconsumed acquired
      ■ cong
          (SoupExpression._[_]*
            (Tᶠ*[ E ] {σ = consumeEnv end₁ 0 env} Vconsumed))
          tripleEq
      ■ sym (T[_]-plugᶠ* E {e = Source.` 0F} Vconsumed)
      ■ T[_]-Env-cong target envCoh

    targetGarbageThread :
      (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
      ¬ ambientThreadLeft l′ →
      lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
    targetGarbageThread l′ outside notAmbient =
      V.lookup∘updateAt′ l′ j
        (λ eq → outside 0F (slotEq ■ cong just (sym eq)))
        consumedThreads
      ■ V.lookup-map l′ (SoupReduction.consumePhi end₁ 0) (Soup.threads C)
      ■ cong (SoupReduction.consumePhi end₁ 0)
          (garbage-thread left l′ outside notAmbient)

    leftImage :
      LocalImage (Typed.⟪ target ⟫)
        [] env′ ambientChannelLeft ambientThreadLeft targetConfig
    leftImage = record
      { channelEmbedding-injective = channelEmbedding-injective left
      ; threadEmbedding = threadEmbedding left
      ; threadEmbedding-injective = threadEmbedding-injective left
      ; channel-not-ambient = λ ()
      ; thread-not-ambient = thread-not-ambient left
      ; live-channel = λ ()
      ; live-thread = λ where
          0F → present j slotEq targetThread
      ; garbage-channel = λ i outside notAmbient →
          V.lookup∘updateAt′ i physical
            (λ eq → notAmbient (inj₁ (inj₂ (sym eq))))
            (Soup.channels C)
          ■ garbage-channel left i outside notAmbient
      ; garbage-thread = targetGarbageThread
      }

    ------------------------------------------------------------------
    -- The residual process: every thread is rewritten, but its own image
    -- travels along `consumePhi-image`.

    consumedImage =
      consumePhi-image
        {channels = Soup.channels C} {channels′ = targetChannels}
        {threads = Soup.threads C}
        physical side₁ 0 envCoh
        (λ i eq → channel-not-ambient right i (inj₁ (inj₂ (sym eq))))
        (λ i notAmbient →
          V.lookup∘updateAt′ i physical
            (λ eq → notAmbient (inj₁ (inj₂ (sym eq))))
            (Soup.channels C))
        right

    -- Only the redex thread is replaced on top of the global rewrite, and
    -- it is ambient for the residual.
    threadsUnchangedRight :
      (l′ : 𝔽 m) →
      ¬ (aT ∪ᵖ
         ownedThreads
           (threadEmbedding body ∘ (_↑ˡ Translation.processCount P))) l′ →
      lookup targetThreads l′ ≡ lookup consumedThreads l′
    threadsUnchangedRight l′ notAmbient =
      V.lookup∘updateAt′ l′ j
        (λ eq → notAmbient (inj₂ (0F , (slotEq ■ cong just (sym eq)))))
        consumedThreads

    rightImage =
      config-resp
        {C = Soup.config targetChannels consumedThreads}
        {C′ = targetConfig}
        (λ _ _ → refl) threadsUnchangedRight consumedImage

    ------------------------------------------------------------------
    -- Re-assembling the frame.

    joined :
      LocalImage (Typed.⟪ target ⟫ Typed.∥ P)
        bodyChannels env′ (aC ∪ᵖ singletonᵖ physical) aT targetConfig
    joined =
      par-join leftImage rightImage
        (λ i → inj₂ (i , refl))
        (λ {i} {l′} embedded → inj₂ (i , embedded))
        (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
        (λ _ ambient → ambient) (λ _ ambient → ambient)

U-acq-local :
  {k n m b₁ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum B₂ + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (suc (Translation.channelCount P))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  Separated sigma ambientChannel ambientThread C →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (0 ∷ suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K Source.`acq) (Source.` 0F)) ⟫
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E (Source.` 0F) ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C
U-acq-local {k = k} {n = n} {m = m} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂}
  {E = E} {P = P} {logicalChannels = channel ∷ bodyChannels}
  {sigma = sigma} {ambientChannel = ambientChannel}
  {ambientThread = ambientThread} {C = C} separated Vsigma image =
  configStep⇒localStep
    (acqConfigStep
      (acq-step {k = k} {n = n} {m = m} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂}
        {E = E} {P = P} {channel = channel} {bodyChannels = bodyChannels}
        {sigma = sigma} {ambientChannel = ambientChannel}
        {ambientThread = ambientThread} {C = C}
        separated Vsigma image))
