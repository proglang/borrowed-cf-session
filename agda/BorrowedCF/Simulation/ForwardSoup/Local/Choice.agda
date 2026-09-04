-- | Phase 3, leaf rule `R-Choice` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   The source redex holds the two owners of one channel under a restriction,
--   beside an arbitrary residual process `P`:
--
--     ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
--       ((⟪ E₁ [ K (`select c) ·¹ ` x ]* ⟫ ∥ ⟪ E₂ [ K `branch ·¹ ` y ]* ⟫) ∥ P)
--       ─→ₚ
--     ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
--       ((⟪ E₁ [ ` x ]* ⟫ ∥ ⟪ E₂ [ `inj c (` y) ]* ⟫) ∥ P)
--
--   Both handles are the *head* variable of their binder group, so `UB-head`
--   exposes them as channel triples over the two physical endpoints of the
--   bound channel and `RUS-Choice` fires.  The rule keeps both namespaces and
--   every channel, so the frame travels along `identity-step`; the two binder
--   groups are unchanged, so the bound channel keeps its content and
--   `res-join` reuses the very equation `res-split-channel` produced.  The
--   residual `P` keeps its image because both rewritten threads are ambient
--   for it — that is what `config-resp` is for.
module BorrowedCF.Simulation.ForwardSoup.Local.Choice where

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
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads; bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ; UB-head)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- The leaf.

record ChoiceStep
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E₁ E₂ :
    SourceReduction.Frame*
      (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {choice : Source.Side}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {channel : OrientedChannel n}
  {bodyChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image :
    LocalImage
      (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
        ((Typed.⟪ SourceReduction._[_]* E₁
                    (Source._·¹_ (Source.K (Source.`select choice))
                      (Source.` 0F)) ⟫
          Typed.∥
          Typed.⟪ SourceReduction._[_]* E₂
                    (Source._·¹_ (Source.K Source.`branch)
                      (Source.` (Source.wkʳ k
                                  (Source.wkˡ (suc b₁ + sum B₁) 0F)))) ⟫)
         Typed.∥ P))
      (channel ∷ bodyChannels) sigma ambientChannel ambientThread C)
  (P′ : Typed.Proc k) : Set where
  field
    choiceSelector choiceBrancher : 𝔽 m
    choiceSelectorSlot :
      threadEmbedding (par-split-left (res-split-image image)) 0F ≡
      just choiceSelector
    choiceBrancherSlot :
      threadEmbedding (par-split-left (res-split-image image)) 1F ≡
      just choiceBrancher
    choiceSelector≢Brancher : choiceSelector ≢ choiceBrancher

    choiceChannel : 𝔽 n
    choiceSide₁ choiceSide₂ : 𝔽 2
    choiceOpposite : SoupReduction.Opposite choiceSide₁ choiceSide₂
    choiceOpen : SoupReduction.is-open (Soup.channels C) choiceChannel

    choiceSelectFrame choiceBranchFrame : SoupExpression.Frame* (2 *ℕ n)
    choiceLabel : Source.Side
    choiceSelectTail choiceBranchTail : Soup.Thread n

    choiceSelectedSelect :
      lookup (Soup.threads C) choiceSelector ≡
      SoupExpression._[_]* choiceSelectFrame
        (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`select choiceLabel))
          (SoupTerm._⊗_
            (SoupTerm._⊗_ SoupTerm.*
              (SoupTerm.` (Soup.endpoint choiceChannel choiceSide₁)))
            choiceSelectTail))
    choiceSelectedBranch :
      lookup (Soup.threads C) choiceBrancher ≡
      SoupExpression._[_]* choiceBranchFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`branch)
          (SoupTerm._⊗_
            (SoupTerm._⊗_ SoupTerm.*
              (SoupTerm.` (Soup.endpoint choiceChannel choiceSide₂)))
            choiceBranchTail))

    choiceConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.replaceTwo (Soup.threads C)
            choiceSelector
              (SoupExpression._[_]* choiceSelectFrame
                (SoupTerm._⊗_
                  (SoupTerm._⊗_ SoupTerm.*
                    (SoupTerm.` (Soup.endpoint choiceChannel choiceSide₁)))
                  choiceSelectTail))
            choiceBrancher
              (SoupExpression._[_]* choiceBranchFrame
                (SoupTerm.`inj choiceLabel
                  (SoupTerm._⊗_
                    (SoupTerm._⊗_ SoupTerm.*
                      (SoupTerm.` (Soup.endpoint choiceChannel choiceSide₂)))
                    choiceBranchTail)))))

open ChoiceStep public

choice-step :
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E₁ E₂ :
    SourceReduction.Frame*
      (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {choice : Source.Side}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {channel : OrientedChannel n}
  {bodyChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (image : LocalImage
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁
                  (Source._·¹_ (Source.K (Source.`select choice))
                    (Source.` 0F)) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂
                  (Source._·¹_ (Source.K Source.`branch)
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc b₁ + sum B₁) 0F)))) ⟫)
       Typed.∥ P))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
  ValueEnv sigma →
  ChoiceStep
    {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
    {E₁ = E₁} {E₂ = E₂} {choice = choice} {P = P}
    {channel = channel} {bodyChannels = bodyChannels}
    sigma ambientChannel ambientThread C image
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁ (Source.` 0F) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂
                  (Source.`inj choice
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc b₁ + sum B₁) 0F)))) ⟫)
       Typed.∥ P))
choice-step {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
  {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} {choice = choice} {P = P}
  {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} image Vsigma =
  dispatch (live-thread left 0F) (live-thread left 1F)
  where
  ----------------------------------------------------------------------
  -- The bound channel, physically.

  physical : 𝔽 n
  physical = physicalChannel channel

  orientation : Orientation
  orientation = proj₂ channel

  side₁ side₂ : 𝔽 2
  side₁ = orientSide orientation 0F
  side₂ = orientSide orientation 1F

  end₁ end₂ : 𝔽 (2 *ℕ n)
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

  ----------------------------------------------------------------------
  -- The body of the restriction and its environment.

  handleVar : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)
  handleVar = Source.wkʳ k (Source.wkˡ (suc b₁ + sum B₁) 0F)

  redex₁ redex₂ reduct₁ reduct₂ :
    Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)
  redex₁ =
    Source._·¹_ (Source.K (Source.`select choice)) (Source.` 0F)
  redex₂ =
    Source._·¹_ (Source.K Source.`branch) (Source.` handleVar)
  reduct₁ = Source.` 0F
  reduct₂ = Source.`inj choice (Source.` handleVar)

  owner₁ owner₂ target₁ target₂ :
    Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)
  owner₁ = SourceReduction._[_]* E₁ redex₁
  owner₂ = SourceReduction._[_]* E₂ redex₂
  target₁ = SourceReduction._[_]* E₁ reduct₁
  target₂ = SourceReduction._[_]* E₂ reduct₂

  reduct : Typed.Proc k
  reduct =
    Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫) Typed.∥ P)

  env : Translation.Env (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k) (2 *ℕ n)
  env = bindEnv (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) channel sigma

  Venv : ValueEnv env
  Venv =
    bindEnv-Value {B₁ = suc b₁ ∷ B₁} {B₂ = suc b₂ ∷ B₂} {channel = channel}
      Vsigma

  binderEnv₁ : Translation.Env (sum (suc b₁ ∷ B₁)) (2 *ℕ n)
  binderEnv₁ =
    proj₁ (Translation.UB[ suc b₁ ∷ B₁ ] end₁ (SoupTerm.* , end₁ , SoupTerm.*))

  binderEnv₂ : Translation.Env (sum (suc b₂ ∷ B₂)) (2 *ℕ n)
  binderEnv₂ =
    proj₁ (Translation.UB[ suc b₂ ∷ B₂ ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

  ----------------------------------------------------------------------
  -- Both handles are the head of their binder group, hence a channel
  -- triple over the corresponding physical endpoint.

  head₁ = UB-head b₁ B₁ end₁ end₁ SoupTerm.* SoupTerm.*
  head₂ = UB-head b₂ B₂ end₂ end₂ SoupTerm.* SoupTerm.*

  tail₁ tail₂ : SoupTerm.Tm (2 *ℕ n)
  tail₁ = proj₁ head₁
  tail₂ = proj₁ head₂

  triple₁ triple₂ : SoupTerm.Tm (2 *ℕ n)
  triple₁ = Translation.chanTriple (SoupTerm.* , end₁ , tail₁)
  triple₂ = Translation.chanTriple (SoupTerm.* , end₂ , tail₂)

  handleEq₁ : env 0F ≡ triple₁
  handleEq₁ =
    ++ₛ-lookupˡ (binderEnv₁ Translation.++ₛ binderEnv₂) sigma
      (0F ↑ˡ sum (suc b₂ ∷ B₂))
    ■ ++ₛ-lookupˡ binderEnv₁ binderEnv₂ 0F
    ■ proj₂ head₁

  handleEq₂ : env handleVar ≡ triple₂
  handleEq₂ =
    ++ₛ-lookupˡ (binderEnv₁ Translation.++ₛ binderEnv₂) sigma
      (Source.wkˡ (suc b₁ + sum B₁) 0F)
    ■ ++ₛ-lookupʳ binderEnv₁ binderEnv₂ 0F
    ■ proj₂ head₂

  ----------------------------------------------------------------------
  -- Splitting the frame: the bound channel joins the ambient set, then the
  -- two owners are separated from the residual process.

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
    aT ∪ᵖ ownedThreads (threadEmbedding body ∘ (2 ↑ʳ_))

  ambientThreadRight : 𝔽 m → Set
  ambientThreadRight =
    aT ∪ᵖ
    ownedThreads (threadEmbedding body ∘ (_↑ˡ Translation.processCount P))

  ----------------------------------------------------------------------
  -- The two soup frames and the expected owner threads.

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = Tᶠ*[ E₁ ] {σ = env} Venv
  F₂ = Tᶠ*[ E₂ ] {σ = env} Venv

  expected₁ expected₂ : Soup.Thread n
  expected₁ = Translation.T[ owner₁ ] env
  expected₂ = Translation.T[ owner₂ ] env

  plugged₁ plugged₂ : Soup.Thread n
  plugged₁ = SoupExpression._[_]* F₁ triple₁
  plugged₂ = SoupExpression._[_]* F₂ (SoupTerm.`inj choice triple₂)

  ----------------------------------------------------------------------
  -- The bound channel is open.

  openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
  openEq = cong proj₁ chanEq ■ open-orient orientation _

  ----------------------------------------------------------------------
  -- The case analysis on the two owner threads.

  dispatch :
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 0F) expected₁ →
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 1F) expected₂ →
    ChoiceStep
      {channel = channel} {bodyChannels = bodyChannels}
      sigma aC aT C image reduct

  -- An omitted owner thread would be `K `unit`, but the translation of a
  -- plugged application never is.
  dispatch (omitted slotEq expectedEq) _ =
    ⊥-elim
      (plug-not-K F₁ (sym (T[_]-plugᶠ* E₁ {e = redex₁} Venv) ■ expectedEq))
  dispatch (present _ _ _) (omitted slotEq expectedEq) =
    ⊥-elim
      (plug-not-K F₂ (sym (T[_]-plugᶠ* E₂ {e = redex₂} Venv) ■ expectedEq))

  dispatch (present j slotEq₁ lookupEq₁) (present l slotEq₂ lookupEq₂) =
    record
      { choiceSelector = j
      ; choiceBrancher = l
      ; choiceSelectorSlot = slotEq₁
      ; choiceBrancherSlot = slotEq₂
      ; choiceSelector≢Brancher = j≢l
      ; choiceChannel = physical
      ; choiceSide₁ = side₁
      ; choiceSide₂ = side₂
      ; choiceOpposite = orientSide-opposite orientation
      ; choiceOpen = openEq
      ; choiceSelectFrame = F₁
      ; choiceBranchFrame = F₂
      ; choiceLabel = choice
      ; choiceSelectTail = tail₁
      ; choiceBranchTail = tail₂
      ; choiceSelectedSelect = selected₁
      ; choiceSelectedBranch = selected₂
      ; choiceConfigStep =
          identity-config-step soupStep (λ _ _ → refl) ambientThreadsUnchanged
            (res-join joined chanEq notAmb)
      }
    where
    j≢l : j ≢ l
    j≢l eq
      with threadEmbedding-injective left slotEq₁
             (slotEq₂ ■ cong just (sym eq))
    ... | ()

    ------------------------------------------------------------------
    -- The step.

    selected₁ :
      lookup (Soup.threads C) j ≡
      SoupExpression._[_]* F₁
        (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`select choice)) triple₁)
    selected₁ =
      lookupEq₁
      ■ T[_]-plugᶠ* E₁ {e = redex₁} Venv
      ■ cong
          (λ t →
            SoupExpression._[_]* F₁
              (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`select choice)) t))
          handleEq₁

    selected₂ :
      lookup (Soup.threads C) l ≡
      SoupExpression._[_]* F₂
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`branch) triple₂)
    selected₂ =
      lookupEq₂
      ■ T[_]-plugᶠ* E₂ {e = redex₂} Venv
      ■ cong
          (λ t →
            SoupExpression._[_]* F₂
              (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`branch) t))
          handleEq₂

    targetThreads : Vec (Soup.Thread n) m
    targetThreads =
      SoupReduction.replaceTwo (Soup.threads C) j plugged₁ l plugged₂

    targetConfig : Soup.Config n m
    targetConfig = Soup.config (Soup.channels C) targetThreads

    soupStep : C SoupReduction.─→ₚ targetConfig
    soupStep =
      SoupReduction.RUS-Choice
        {cs = Soup.channels C} {ts = Soup.threads C}
        j l physical side₁ side₂ F₁ F₂ choice
        {e₁′ = tail₁} {e₂′ = tail₂}
        j≢l (orientSide-opposite orientation) openEq selected₁ selected₂

    ------------------------------------------------------------------
    -- The frame is untouched: the only rewritten threads are the two
    -- owners, which are not ambient for the whole image.

    ambientThreadsUnchanged :
      (l′ : 𝔽 m) → aT l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    ambientThreadsUnchanged l′ ambient =
      V.lookup∘updateAt′ l′ l
        (λ eq → thread-not-ambient left slotEq₂ (inj₁ (subst aT eq ambient)))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → thread-not-ambient left slotEq₁ (inj₁ (subst aT eq ambient)))
          (Soup.threads C)

    ------------------------------------------------------------------
    -- The image of the two owners after the step.

    targetThread₁ : lookup targetThreads j ≡ Translation.T[ target₁ ] env
    targetThread₁ =
      V.lookup∘updateAt′ j l j≢l
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt j (Soup.threads C)
      ■ cong (SoupExpression._[_]* F₁) (sym handleEq₁)
      ■ sym (T[_]-plugᶠ* E₁ {e = reduct₁} Venv)

    targetThread₂ : lookup targetThreads l ≡ Translation.T[ target₂ ] env
    targetThread₂ =
      V.lookup∘updateAt l (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ cong (λ t → SoupExpression._[_]* F₂ (SoupTerm.`inj choice t))
          (sym handleEq₂)
      ■ sym (T[_]-plugᶠ* E₂ {e = reduct₂} Venv)

    targetGarbageThread :
      (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
      ¬ ambientThreadLeft l′ →
      lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
    targetGarbageThread l′ outside notAmbient =
      V.lookup∘updateAt′ l′ l
        (λ eq → outside 1F (slotEq₂ ■ cong just (sym eq)))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → outside 0F (slotEq₁ ■ cong just (sym eq)))
          (Soup.threads C)
      ■ garbage-thread left l′ outside notAmbient

    leftImage :
      LocalImage
        (Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫)
        [] env ambientChannelLeft ambientThreadLeft targetConfig
    leftImage = record
      { channelEmbedding-injective = channelEmbedding-injective left
      ; threadEmbedding = threadEmbedding left
      ; threadEmbedding-injective = threadEmbedding-injective left
      ; channel-not-ambient = λ ()
      ; thread-not-ambient = thread-not-ambient left
      ; live-channel = λ ()
      ; live-thread = λ where
          0F → present j slotEq₁ targetThread₁
          1F → present l slotEq₂ targetThread₂
      ; garbage-channel = λ i outside notAmbient →
          garbage-channel left i outside notAmbient
      ; garbage-thread = targetGarbageThread
      }

    ------------------------------------------------------------------
    -- The residual process never looks at the two rewritten threads:
    -- both are ambient for it.

    threadsUnchangedRight :
      (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    threadsUnchangedRight l′ notAmbient =
      V.lookup∘updateAt′ l′ l
        (λ eq → notAmbient (inj₂ (1F , (slotEq₂ ■ cong just (sym eq)))))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → notAmbient (inj₂ (0F , (slotEq₁ ■ cong just (sym eq)))))
          (Soup.threads C)

    rightImage =
      config-resp {C = C} {C′ = targetConfig}
        (λ _ _ → refl) threadsUnchangedRight right

    ------------------------------------------------------------------
    -- Re-assembling the frame.

    joined :
      LocalImage
        ((Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫) Typed.∥ P)
        bodyChannels env
        (aC ∪ᵖ singletonᵖ physical) aT targetConfig
    joined =
      par-join leftImage rightImage
        (λ i → inj₂ (i , refl))
        (λ {i} {l′} embedded → inj₂ (i , embedded))
        (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
        (λ _ ambient → ambient) (λ _ ambient → ambient)

U-choice-local :
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {E₁ E₂ :
    SourceReduction.Frame*
      (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {choice : Source.Side}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (suc (Translation.channelCount P))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁
                  (Source._·¹_ (Source.K (Source.`select choice))
                    (Source.` 0F)) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂
                  (Source._·¹_ (Source.K Source.`branch)
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc b₁ + sum B₁) 0F)))) ⟫)
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁ (Source.` 0F) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂
                  (Source.`inj choice
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc b₁ + sum B₁) 0F)))) ⟫)
       Typed.∥ P))
    sigma ambientChannel ambientThread C
U-choice-local {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
  {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} {choice = choice}
  {P = P} {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma image =
  configStep⇒localStep
    (choiceConfigStep
      (choice-step {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
        {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} {choice = choice}
        {P = P} {channel = channel} {bodyChannels = bodyChannels}
        {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} image Vsigma))
