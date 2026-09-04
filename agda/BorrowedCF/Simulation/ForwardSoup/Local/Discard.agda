-- | Phase 3, leaf rule `R-Discard` (`ForwardSoup/PLAN.md`, §4, Phase 3,
--   item 5).
--
--   The source redex discards the head borrow of the first binder group,
--   beside a residual process `P`:
--
--     ν (suc b₁ ∷ B₁) B₂
--       (⟪ E ⋯ᶠ* weakenᵣ [ K `discard ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
--       ─→ₚ
--     ν (b₁ ∷ B₁) B₂ (⟪ E [ * ]* ⟫ ∥ P)
--
--   The shape is `Local/Com.agda` minus the second redex thread: `res-split`
--   → `par-split-left`/`-right` → `UB-head` for the discarded handle →
--   `RUS-Discard` → `par-join`/`res-join` → `identity-step`.  The soup rule
--   discards *any* value, so nothing about the channel changes — which is
--   also why the head bind group must not carry a φ-flag for the borrow
--   being dropped.  Three cases:
--
--     * `b₁ = suc b′` (any `B₁`): the head block of `UB[ suc (suc b′) ∷ B₁ ]`
--       shrinks by one entry and the flag list is unchanged
--       (`weakenᵣ-bindEnv-coh`, `bindChannel-drop`);
--     * `b₁ = 0`, `B₁ = []`: the head block disappears and neither group has
--       flags (`weakenᵣ-bindEnv-coh-last`, `bindChannel-last`);
--     * `b₁ = 0`, `B₁ = _ ∷ _`: untypeable — the flag `ϕ[ 1 ] = drop` would
--       have to become `ϕ[ 0 ] = acq`, and indeed the typed side rejects the
--       redex (`discard-b0-vacuous`).
module BorrowedCF.Simulation.ForwardSoup.Local.Discard where

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

open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (discard-b0-vacuous)

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
  using ( weakenᵣ-bindEnv-coh; weakenᵣ-bindEnv-coh-last
        ; bindChannel-drop; bindChannel-last
        )
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
-- Exact evidence for the discard leaf.

record DiscardStep
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
                 (Source._·¹_ (Source.K Source.`discard)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) : Set where
  field
    discardThread : 𝔽 m
    discardSlotEq : threadEmbedding image zero ≡ just discardThread

    discardFrame : SoupExpression.Frame* (2 *ℕ n)
    discardArgument discardTail : Soup.Thread n
    discardEndpoint : 𝔽 (2 *ℕ n)

    discardSourceValue :
      SoupExpression.Value (bindEnv (suc b₁ ∷ B₁) B₂ channel sigma 0F)
    discardTranslatedValue :
      SoupExpression.Value discardArgument
    discardArgument≡source :
      discardArgument ≡ bindEnv (suc b₁ ∷ B₁) B₂ channel sigma 0F
    discardArgument≡handle :
      discardArgument ≡
      Translation.chanTriple (SoupTerm.* , discardEndpoint , discardTail)

    discardSelectedSource :
      lookup (Soup.threads C) discardThread ≡
      Translation.T[
        SourceReduction._[_]*
          (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
          (Source._·¹_ (Source.K Source.`discard) (Source.` 0F))
      ] (bindEnv (suc b₁ ∷ B₁) B₂ channel sigma)
    discardSelected :
      lookup (Soup.threads C) discardThread ≡
      SoupExpression._[_]* discardFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`discard) discardArgument)

    discardConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.replaceAt (Soup.threads C) discardThread
            (SoupExpression._[_]* discardFrame SoupTerm.*)))

open DiscardStep public

------------------------------------------------------------------------
-- The common part of the three cases: the head borrow disappears from the
-- environment (`envCoherent`) and the bound channel keeps its content
-- (`bindEqual`).

private
  discard-worker :
    {k n m b₁ : ℕ} {B₁ B₂ : Typed.BindGroup}
    {E : SourceReduction.Frame* (sum (b₁ ∷ B₁) + sum B₂ + k)}
    {P : Typed.Proc (sum (b₁ ∷ B₁) + sum B₂ + k)}
    {channel : OrientedChannel n}
    {bodyChannels :
      Vec (OrientedChannel n)
        (Translation.channelCount (Typed._⋯ₚ_ P Source.weakenᵣ))}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    ((x : 𝔽 (sum (b₁ ∷ B₁) + sum B₂ + k)) →
      bindEnv (suc b₁ ∷ B₁) B₂ channel sigma (Source.weakenᵣ x) ≡
      bindEnv (b₁ ∷ B₁) B₂ channel sigma x) →
    bindChannel (suc b₁ ∷ B₁) B₂ channel ≡
      bindChannel (b₁ ∷ B₁) B₂ channel →
    ValueEnv sigma →
    (image : LocalImage
        (Typed.ν (suc b₁ ∷ B₁) B₂
          (Typed.⟪ SourceReduction._[_]*
                     (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                     (Source._·¹_ (Source.K Source.`discard)
                       (Source.` 0F)) ⟫
           Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
        (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
    DiscardStep
      {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
      {channel = channel} {bodyChannels = bodyChannels}
      (Typed.ν (b₁ ∷ B₁) B₂
        (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥ P))
      sigma ambientChannel ambientThread C image
  discard-worker {k = k} {n = n} {m = m} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂}
    {E = E} {P = P} {channel = channel} {bodyChannels = bodyChannels}
    {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
    envCoh bindEq Vsigma image =
    dispatch (live-thread left 0F)
    where
    ------------------------------------------------------------------
    -- The bound channel, physically.

    physical : 𝔽 n
    physical = physicalChannel channel

    orientation : Orientation
    orientation = proj₂ channel

    end₁ end₂ : 𝔽 (2 *ℕ n)
    end₁ = physicalEndpoint channel 0F
    end₂ = physicalEndpoint channel 1F

    ------------------------------------------------------------------
    -- The weakening of the rule and the two body environments.

    wkrho :
      𝔽 (sum (b₁ ∷ B₁) + sum B₂ + k) →
      𝔽 (sum (suc b₁ ∷ B₁) + sum B₂ + k)
    wkrho = Source.weakenᵣ

    sourceEnv : Translation.Env (sum (suc b₁ ∷ B₁) + sum B₂ + k) (2 *ℕ n)
    sourceEnv = bindEnv (suc b₁ ∷ B₁) B₂ channel sigma

    targetEnv : Translation.Env (sum (b₁ ∷ B₁) + sum B₂ + k) (2 *ℕ n)
    targetEnv = bindEnv (b₁ ∷ B₁) B₂ channel sigma

    Vsource : ValueEnv sourceEnv
    Vsource =
      bindEnv-Value {B₁ = suc b₁ ∷ B₁} {B₂ = B₂} {channel = channel} Vsigma

    Vtarget : ValueEnv targetEnv
    Vtarget =
      bindEnv-Value {B₁ = b₁ ∷ B₁} {B₂ = B₂} {channel = channel} Vsigma

    binderEnv₁ : Translation.Env (sum (suc b₁ ∷ B₁)) (2 *ℕ n)
    binderEnv₁ =
      proj₁ (Translation.UB[ suc b₁ ∷ B₁ ] end₁
              (SoupTerm.* , end₁ , SoupTerm.*))

    binderEnv₂ : Translation.Env (sum B₂) (2 *ℕ n)
    binderEnv₂ =
      proj₁ (Translation.UB[ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

    ------------------------------------------------------------------
    -- The discarded handle is the head of the first binder group.

    head₁ = UB-head b₁ B₁ end₁ end₁ SoupTerm.* SoupTerm.*

    tail₁ : SoupTerm.Tm (2 *ℕ n)
    tail₁ = proj₁ head₁

    triple₁ : SoupTerm.Tm (2 *ℕ n)
    triple₁ = Translation.chanTriple (SoupTerm.* , end₁ , tail₁)

    handleEq : sourceEnv 0F ≡ triple₁
    handleEq =
      ++ₛ-lookupˡ (binderEnv₁ Translation.++ₛ binderEnv₂) sigma
        (0F ↑ˡ sum B₂)
      ■ ++ₛ-lookupˡ binderEnv₁ binderEnv₂ 0F
      ■ proj₂ head₁

    -- The discarded soup term is a value: it is the image of a variable.
    Vtriple : SoupExpression.Value triple₁
    Vtriple = subst SoupExpression.Value handleEq (Vsource 0F)

    ------------------------------------------------------------------
    -- The source terms.

    redex : Source.Tm (sum (suc b₁ ∷ B₁) + sum B₂ + k)
    redex =
      Source._·¹_ (Source.K Source.`discard) (Source.` 0F)

    owner : Source.Tm (sum (suc b₁ ∷ B₁) + sum B₂ + k)
    owner = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E wkrho) redex

    target : Source.Tm (sum (b₁ ∷ B₁) + sum B₂ + k)
    target = SourceReduction._[_]* E Source.*

    reduct : Typed.Proc k
    reduct =
      Typed.ν (b₁ ∷ B₁) B₂ (Typed.⟪ target ⟫ Typed.∥ P)

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
    -- The case analysis on the owner thread.

    dispatch :
      OptionalThreadImage {n = n} (Soup.threads C)
        (threadEmbedding left 0F) expected →
      DiscardStep
        {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
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
        { discardThread = j
        ; discardSlotEq = slotEq
        ; discardFrame = F
        ; discardArgument = triple₁
        ; discardTail = tail₁
        ; discardEndpoint = end₁
        ; discardSourceValue = Vsource 0F
        ; discardTranslatedValue = Vtriple
        ; discardArgument≡source = sym handleEq
        ; discardArgument≡handle = refl
        ; discardSelectedSource = lookupEq
        ; discardSelected = selected
        ; discardConfigStep =
            identity-config-step soupStep (λ _ _ → refl) ambientThreadsUnchanged
              (res-join joined (chanEq ■ bindEq) notAmb)
        }
      where
      ----------------------------------------------------------------
      -- The step.

      selected :
        lookup (Soup.threads C) j ≡
        SoupExpression._[_]* F
          (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`discard) triple₁)
      selected =
        lookupEq
        ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E wkrho) {e = redex} Vsource
        ■ cong
            (λ handle →
              SoupExpression._[_]* F
                (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`discard) handle))
            handleEq

      targetThreads : Vec (Soup.Thread n) m
      targetThreads = SoupReduction.replaceAt (Soup.threads C) j plugged

      targetConfig : Soup.Config n m
      targetConfig = Soup.config (Soup.channels C) targetThreads

      soupStep : C SoupReduction.─→ₚ targetConfig
      soupStep =
        SoupReduction.RUS-Discard
          {cs = Soup.channels C} {ts = Soup.threads C}
          j F {e = triple₁} Vtriple selected

      ----------------------------------------------------------------
      -- The frame is untouched: the only rewritten thread is the owner,
      -- which is not ambient for the whole image.

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
            garbage-channel left i outside notAmbient
        ; garbage-thread = targetGarbageThread
        }

      ----------------------------------------------------------------
      -- The residual process: the rewritten thread is ambient for it, and
      -- its image travels from `P ⋯ₚ weakenᵣ` to `P`.

      threadsUnchangedRight :
        (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
        lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
      threadsUnchangedRight l′ notAmbient =
        V.lookup∘updateAt′ l′ j
          (λ eq → notAmbient (inj₂ (0F , (slotEq ■ cong just (sym eq)))))
          (Soup.threads C)

      rightImage =
        config-resp {C = C} {C′ = targetConfig}
          (λ _ _ → refl) threadsUnchangedRight right

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

------------------------------------------------------------------------
-- The leaf.

discard-step :
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
                 (Source._·¹_ (Source.K Source.`discard)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)) →
  ValueEnv sigma →
  (image : LocalImage
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`discard)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
  DiscardStep
    {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
    {channel = channel} {bodyChannels = bodyChannels}
    (Typed.ν (b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C image
discard-step {b₁ = suc b′} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
  {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
  Γ-S ⊢P Vsigma image =
  discard-worker {b₁ = suc b′} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
    {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
    (weakenᵣ-bindEnv-coh {b′ = b′} {B₁ = B₁} {B₂ = B₂}
      {channel = channel} {sigma = sigma})
    (bindChannel-drop {b′ = b′} {B₁ = B₁} {B₂ = B₂} {channel = channel})
    Vsigma image
discard-step {b₁ = zero} {B₁ = []} {B₂ = B₂} {E = E} {P = P}
  {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
  Γ-S ⊢P Vsigma image =
  discard-worker {b₁ = zero} {B₁ = []} {B₂ = B₂} {E = E} {P = P}
    {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
    (weakenᵣ-bindEnv-coh-last {B₂ = B₂} {channel = channel} {sigma = sigma})
    (bindChannel-last {B₂ = B₂} {channel = channel})
    Vsigma image
discard-step {b₁ = zero} {B₁ = c₀ ∷ B′} {E = E} {P = P}
  Γ-S ⊢P Vsigma image =
  ⊥-elim (discard-b0-vacuous {E = E} {P = P} ⊢P)

U-discard-local :
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
                 (Source._·¹_ (Source.K Source.`discard)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)) →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (suc b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E Source.weakenᵣ)
                 (Source._·¹_ (Source.K Source.`discard)
                   (Source.` 0F)) ⟫
       Typed.∥ (Typed._⋯ₚ_ P Source.weakenᵣ)))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (b₁ ∷ B₁) B₂
      (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥ P))
    sigma ambientChannel ambientThread C
U-discard-local {b₁ = suc b′} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
  {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  Γ-S ⊢P Vsigma image =
  configStep⇒localStep
    (discardConfigStep
      (discard-step {b₁ = suc b′} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P}
        {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
        Γ-S ⊢P Vsigma image))
U-discard-local {b₁ = zero} {B₁ = []} {B₂ = B₂} {E = E} {P = P}
  {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  Γ-S ⊢P Vsigma image =
  configStep⇒localStep
    (discardConfigStep
      (discard-step {b₁ = zero} {B₁ = []} {B₂ = B₂} {E = E} {P = P}
        {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
        Γ-S ⊢P Vsigma image))
U-discard-local {b₁ = zero} {B₁ = c₀ ∷ B′} {E = E} {P = P}
  {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  Γ-S ⊢P Vsigma image =
  configStep⇒localStep
    (discardConfigStep
      (discard-step {b₁ = zero} {B₁ = c₀ ∷ B′} {E = E} {P = P}
        {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
        Γ-S ⊢P Vsigma image))
