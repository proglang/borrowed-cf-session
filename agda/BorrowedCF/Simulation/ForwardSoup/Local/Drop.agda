-- | Phase 3, leaf rule `R-Drop` (`ForwardSoup/PLAN.md`, §4, Phase 3, item 6).
--
--   The source redex drops the head borrow of the first binder group,
--   beside a residual process `P`:
--
--     ν (suc b₁ ∷ B₁) B₂
--       (⟪ E ⋯ᶠ* weakenᵣ [ K `drop ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
--       ─→ₚ
--     ν (b₁ ∷ B₁) B₂ (⟪ E [ * ]* ⟫ ∥ P)
--
--   Typing forces `b₁ ≡ 0` and `B₁ ≡ c′ ∷ B′` (`drop-shape`), so the head
--   group shrinks `1 ∷ c′ ∷ B′ ↦ 0 ∷ c′ ∷ B′`: the environment loses its head
--   entry (`weakenᵣ-bindEnv-coh-drop`) and the head *flag* flips from
--   `ϕ[ 1 ] = drop` to `ϕ[ 0 ] = acq` while the `UBFrom 1 (c′ ∷ B′) …` tail is
--   shared by redex and reduct.  That is exactly `RUS-Drop` with `before = []`
--   and `after` that shared tail; the dropped handle is the head of the group,
--   whose triple is `𝓒[ * × end₁ × `phi (end₁ , 0) ]`.
--
--   Apart from the bound channel's flag list, the shape is `Local/Discard.agda`
--   verbatim: `res-split` → `par-split-left`/`-right` → `UB-head` →
--   `RUS-Drop` → `par-join`/`res-join` → `identity-step`.
module BorrowedCF.Simulation.ForwardSoup.Local.Drop where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Reduction.Base using (ChanCx)
open Typed using (_;_⊢ₚ_)

open import BorrowedCF.Simulation.Support.Theorems.DropShape using (drop-shape)

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads; bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.Local.BindDrop
  using (weakenᵣ-bindEnv-coh-drop)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value; Tᶠ*-plug-ren-coh)
open import BorrowedCF.Simulation.ForwardSoup.Local.Residual
  using (residual-image; ownedChannels-transport; ownedChannels-transport⁻)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (transportChannels)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ; UB-head; processCount-rename)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- Exact evidence for the drop leaf.

record DropStep
  {k n m b₁ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n)
      (Translation.channelCount (Typed._⋯ₚ_ P Source.weakenᵣ))}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image : LocalImage
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`drop)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) : Set where
  field
    dropThread : 𝔽 m
    dropSlotEq : threadEmbedding image zero ≡ just dropThread

    dropFrame : SoupExpression.Frame* (2 *ℕ n)
    dropArgument : Soup.Thread n
    dropEndpoint : 𝔽 (2 *ℕ n)
    dropTailFlags : List Soup.Flag

    dropSelectedSource :
      lookup (Soup.threads C) dropThread ≡
      Translation.T[
        SourceReduction._[_]*
          (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
          (Source._·¹_ (Source.K Source.`drop) (Source.` 0F))
      ] (bindEnv (suc b₁ ∷ B₁) B₂ channel sigma)
    dropSelected :
      lookup (Soup.threads C) dropThread ≡
      SoupExpression._[_]* dropFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`drop) dropArgument)

    dropConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config
          (V.updateAt (Soup.channels C) (physicalChannel channel)
            (SoupReduction.setEndpointFlags
              (orientSide (proj₂ channel) 0F)
              (Soup.acq ∷ dropTailFlags)))
          (SoupReduction.replaceAt (Soup.threads C) dropThread
            (SoupExpression._[_]* dropFrame SoupTerm.*)))

open DropStep public

------------------------------------------------------------------------
-- The leaf.

drop-step :
  {k n m b₁ : ℕ} {Γ : Context.Ctx k} {g : Context.Struct k}
  {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n)
      (Translation.channelCount (Typed._⋯ₚ_ P Source.weakenᵣ))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ChanCx Γ →
  Γ ; g ⊢ₚ
    Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`drop) (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)) →
  ValueEnv sigma →
  (image : LocalImage
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`drop) (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
  DropStep
    {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
    {channel = channel} {bodyChannels = bodyChannels}
    (Typed.ν (b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C
    image
drop-step {k = k} {n = n} {m = m} {B₂ = B₂} {E = E} {P = P}
  {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C}
  Γ-S ⊢P Vsigma image
  with drop-shape {E = E} {P = P} ⊢P
... | refl , c′ , B′ , refl =
  dispatch (live-thread left 0F)
  where
  ------------------------------------------------------------------
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

  ------------------------------------------------------------------
  -- The weakening of the rule and the two body environments.

  wkrho :
    𝔽 (sum (0 ∷ c′ ∷ B′) + sum B₂ + k) →
    𝔽 (sum (1 ∷ c′ ∷ B′) + sum B₂ + k)
  wkrho = Source.weakenᵣ

  sourceEnv : Translation.Env (sum (1 ∷ c′ ∷ B′) + sum B₂ + k) (2 *ℕ n)
  sourceEnv = bindEnv (1 ∷ c′ ∷ B′) B₂ channel sigma

  targetEnv : Translation.Env (sum (0 ∷ c′ ∷ B′) + sum B₂ + k) (2 *ℕ n)
  targetEnv = bindEnv (0 ∷ c′ ∷ B′) B₂ channel sigma

  envCoh :
    (x : 𝔽 (sum (0 ∷ c′ ∷ B′) + sum B₂ + k)) →
    sourceEnv (wkrho x) ≡ targetEnv x
  envCoh =
    weakenᵣ-bindEnv-coh-drop {c′ = c′} {B′ = B′} {B₂ = B₂}
      {channel = channel} {sigma = sigma}

  Vsource : ValueEnv sourceEnv
  Vsource =
    bindEnv-Value {B₁ = 1 ∷ c′ ∷ B′} {B₂ = B₂} {channel = channel} Vsigma

  Vtarget : ValueEnv targetEnv
  Vtarget =
    bindEnv-Value {B₁ = 0 ∷ c′ ∷ B′} {B₂ = B₂} {channel = channel} Vsigma

  binderEnv₁ : Translation.Env (sum (1 ∷ c′ ∷ B′)) (2 *ℕ n)
  binderEnv₁ =
    proj₁ (Translation.UB[ 1 ∷ c′ ∷ B′ ] end₁
            (SoupTerm.* , end₁ , SoupTerm.*))

  binderEnv₂ : Translation.Env (sum B₂) (2 *ℕ n)
  binderEnv₂ =
    proj₁ (Translation.UB[ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

  ------------------------------------------------------------------
  -- The dropped handle is the head of the first binder group; the borrow
  -- it releases is the φ-cell number `0` of that group.

  head₁ = UB-head 0 (c′ ∷ B′) end₁ end₁ SoupTerm.* SoupTerm.*

  triple₁ : SoupTerm.Tm (2 *ℕ n)
  triple₁ =
    Translation.chanTriple
      (SoupTerm.* , end₁ , SoupTerm.`phi (end₁ , 0))

  handleEq : sourceEnv 0F ≡ triple₁
  handleEq =
    ++ₛ-lookupˡ (binderEnv₁ Translation.++ₛ binderEnv₂) sigma
      (0F ↑ˡ sum B₂)
    ■ ++ₛ-lookupˡ binderEnv₁ binderEnv₂ 0F
    ■ proj₂ head₁

  ------------------------------------------------------------------
  -- The flag lists of the bound channel.  Only the head flag changes:
  -- `ϕ[ 1 ] = drop` becomes `ϕ[ 0 ] = acq`; the tail is shared.

  tailFlags : List Soup.Flag
  tailFlags =
    proj₂ (Translation.UBFrom 1 (c′ ∷ B′) end₁
            (SoupTerm.`phi (end₁ , 0) , end₁ , SoupTerm.*))

  flags₂ : List Soup.Flag
  flags₂ =
    proj₂ (Translation.UB[ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

  ------------------------------------------------------------------
  -- The source terms.

  redex : Source.Tm (sum (1 ∷ c′ ∷ B′) + sum B₂ + k)
  redex = Source._·¹_ (Source.K Source.`drop) (Source.` 0F)

  owner : Source.Tm (sum (1 ∷ c′ ∷ B′) + sum B₂ + k)
  owner = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E wkrho) redex

  target : Source.Tm (sum (0 ∷ c′ ∷ B′) + sum B₂ + k)
  target = SourceReduction._[_]* E Source.*

  reduct : Typed.Proc k
  reduct =
    Typed.ν (0 ∷ c′ ∷ B′) B₂ (Typed.⟪ target ⟫ Typed.∥ P)

  ------------------------------------------------------------------
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

  ambientThreadRight : 𝔽 m → Set
  ambientThreadRight =
    aT ∪ᵖ
    ownedThreads
      (threadEmbedding body ∘
        (_↑ˡ Translation.processCount (Typed._⋯ₚ_ P wkrho)))

  ------------------------------------------------------------------
  -- The soup frame and the expected owner thread.

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ SourceReduction._⋯ᶠ*_ E wkrho ] {σ = sourceEnv} Vsource

  expected : Soup.Thread n
  expected = Translation.T[ owner ] sourceEnv

  plugged : Soup.Thread n
  plugged = SoupExpression._[_]* F SoupTerm.*

  ------------------------------------------------------------------
  -- The bound channel is open and carries `drop` in front of `tailFlags`.

  openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
  openEq = cong proj₁ chanEq ■ open-orient orientation _

  flagsEq :
    SoupReduction.endpointFlags (lookup (Soup.channels C) physical) side₁ ≡
    [] L.++ Soup.drop ∷ tailFlags
  flagsEq =
    cong (λ ch → SoupReduction.endpointFlags ch side₁) chanEq
    ■ endpointFlags-orient orientation
        (true , Soup.drop ∷ tailFlags , flags₂) 0F

  targetChannels : Vec Soup.Channel n
  targetChannels =
    V.updateAt (Soup.channels C) physical
      (SoupReduction.setEndpointFlags side₁ (Soup.acq ∷ tailFlags))

  newChanEq :
    lookup targetChannels physical ≡ bindChannel (0 ∷ c′ ∷ B′) B₂ channel
  newChanEq =
    V.lookup∘updateAt physical (Soup.channels C)
    ■ cong (SoupReduction.setEndpointFlags side₁ (Soup.acq ∷ tailFlags))
        chanEq
    ■ setEndpointFlags-orient orientation
        (true , Soup.drop ∷ tailFlags , flags₂) 0F (Soup.acq ∷ tailFlags)

  ------------------------------------------------------------------
  -- The case analysis on the owner thread.

  dispatch :
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 0F) expected →
    DropStep
      {b₁ = 0} {B₁ = c′ ∷ B′} {B₂ = B₂} {E = E} {P = P}
      {channel = channel} {bodyChannels = bodyChannels}
      reduct sigma aC aT C image

  dispatch (omitted slotEq expectedEq) =
    ⊥-elim
      (plug-not-K F
        (sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E wkrho)
               {e = redex} Vsource)
         ■ expectedEq))

  dispatch (present j slotEq lookupEq) =
    record
      { dropThread = j
      ; dropSlotEq = slotEq
      ; dropFrame = F
      ; dropArgument = triple₁
      ; dropEndpoint = end₁
      ; dropTailFlags = tailFlags
      ; dropSelectedSource = lookupEq
      ; dropSelected = selected
      ; dropConfigStep =
          identity-config-step
            soupStep ambientChannelsUnchanged ambientThreadsUnchanged
            (res-join joined newChanEq notAmb)
      }
    where
    ----------------------------------------------------------------
    -- The step.

    selected :
      lookup (Soup.threads C) j ≡
      SoupExpression._[_]* F
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`drop) triple₁)
    selected =
      lookupEq
      ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E wkrho) {e = redex} Vsource
      ■ cong
          (λ handle →
            SoupExpression._[_]* F
              (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`drop) handle))
          handleEq

    targetThreads : Vec (Soup.Thread n) m
    targetThreads = SoupReduction.replaceAt (Soup.threads C) j plugged

    targetConfig : Soup.Config n m
    targetConfig = Soup.config targetChannels targetThreads

    soupStep : C SoupReduction.─→ₚ targetConfig
    soupStep =
      SoupReduction.RUS-Drop
        {cs = Soup.channels C} {ts = Soup.threads C}
        j physical side₁ F [] tailFlags openEq flagsEq selected

    ----------------------------------------------------------------
    -- The frame is untouched: the only rewritten thread is the owner and
    -- the only rewritten channel is the bound one, neither of which is
    -- ambient for the whole image.

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
        (Soup.threads C)

    ----------------------------------------------------------------
    -- The image of the owner after the step.

    targetThread : lookup targetThreads j ≡ Translation.T[ target ] targetEnv
    targetThread =
      V.lookup∘updateAt j (Soup.threads C)
      ■ Tᶠ*-plug-ren-coh E wkrho sourceEnv targetEnv Vsource Vtarget
          envCoh SoupTerm.*
      ■ sym (T[_]-plugᶠ* E {e = Source.*} Vtarget)

    targetGarbageThread :
      (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
      ¬ ambientThreadLeft l′ →
      lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
    targetGarbageThread l′ outside notAmbient =
      V.lookup∘updateAt′ l′ j
        (λ eq → outside 0F (slotEq ■ cong just (sym eq)))
        (Soup.threads C)
      ■ garbage-thread left l′ outside notAmbient

    leftImage :
      LocalImage (Typed.⟪ target ⟫)
        [] targetEnv ambientChannelLeft ambientThreadLeft targetConfig
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

    ----------------------------------------------------------------
    -- The residual process: the rewritten thread and the rewritten
    -- channel are both ambient for it, and its image travels from
    -- `P ⋯ₚ weakenᵣ` to `P`.

    threadsUnchangedRight :
      (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    threadsUnchangedRight l′ notAmbient =
      V.lookup∘updateAt′ l′ j
        (λ eq → notAmbient (inj₂ (0F , (slotEq ■ cong just (sym eq)))))
        (Soup.threads C)

    rightImage =
      config-resp {C = C} {C′ = targetConfig}
        (λ i notAmbient →
          V.lookup∘updateAt′ i physical
            (λ eq → notAmbient (inj₁ (inj₂ (sym eq))))
            (Soup.channels C))
        threadsUnchangedRight right

    residual = residual-image {P = P} {rho = wkrho} envCoh rightImage

    processEq :
      Translation.processCount (Typed._⋯ₚ_ P wkrho) ≡
      Translation.processCount P
    processEq = processCount-rename P wkrho

    ----------------------------------------------------------------
    -- Re-assembling the frame.

    joined :
      LocalImage (Typed.⟪ target ⟫ Typed.∥ P)
        (transportChannels P wkrho bodyChannels) targetEnv
        (aC ∪ᵖ singletonᵖ physical) aT targetConfig
    joined =
      par-join leftImage residual
        (λ i →
          inj₂
            (ownedChannels-transport {P = P} {rho = wkrho}
              {channels = bodyChannels} _ (i , refl)))
        (λ {i} {l′} embedded →
          inj₂ (Fin.cast (sym processEq) i , embedded))
        (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
        (λ i → λ where
          (inj₁ ambient) → inj₁ ambient
          (inj₂ owned) →
            inj₂
              (ownedChannels-transport⁻ {P = P} {rho = wkrho}
                {channels = bodyChannels} i owned))
        (λ l′ → λ where
          (inj₁ ambient) → inj₁ ambient
          (inj₂ (i , owned)) →
            inj₂
              ( Fin.cast processEq i
              , ( cong (λ t → threadEmbedding rightImage t)
                    (Fin.cast-involutive (sym processEq) processEq i)
                ■ owned
                )
              ))

U-drop-local :
  {k n m b₁ : ℕ} {Γ : Context.Ctx k} {g : Context.Struct k}
  {B₁ B₂ : Typed.BindGroup}
  {E : SourceReduction.Frame* (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {P : Typed.Proc (sum (b₁ ∷ B₁) + sum B₂ + k)}
  {logicalChannels :
    Vec (OrientedChannel n)
      (suc (Translation.channelCount (Typed._⋯ₚ_ P Source.weakenᵣ)))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ChanCx Γ →
  Γ ; g ⊢ₚ
    Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`drop) (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)) →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`drop) (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C
U-drop-local {k = k} {n = n} {m = m} {b₁ = b₁}
  {Γ = Γ} {g = g} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
  {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Γ-S ⊢P Vsigma image =
  configStep⇒localStep
    (dropConfigStep
      (drop-step {k = k} {n = n} {m = m} {b₁ = b₁}
        {Γ = Γ} {g = g} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
        {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} Γ-S ⊢P Vsigma image))
