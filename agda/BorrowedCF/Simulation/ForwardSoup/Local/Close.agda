-- | Phase 3, leaf rule `R-Close` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   The source redex is a restriction with a singleton binder group on each
--   side whose body is a parallel composition of the two endpoint owners:
--
--     ν [1] [1] (⟪ E₁⁺ [ K (`end ‼) ·¹ ` 0F ]* ⟫ ∥ ⟪ E₂⁺ [ K (`end ⁇) ·¹ ` 1F ]* ⟫)
--       ─→ₚ  ⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ * ]* ⟫
--
--   Physically the two owner threads become `E [ * ]*` and the bound channel
--   is closed, so the soup takes an `RUS-Close` step and neither the channel
--   nor the thread namespace changes: the frame travels along
--   `identity-step`.  The bound channel leaves the image (the reduct owns no
--   channel at all) and becomes garbage rather than ambient — `RUS-Close`
--   marks it `(false , [] , [])`, exactly the shape `garbage-channel` wants.
module BorrowedCF.Simulation.ForwardSoup.Local.Close where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)
import Data.Fin.Properties as FinP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Extrusion
  using (weaken*-coherent)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (Tᶠ*-plug-ren-coh; bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

private
  -- Both binder groups of `R-Close` are `[ 1 ]`, so both endpoint
  -- environments are singletons and both flag lists are empty; the bound
  -- channel is therefore open with no pending flags, whatever its
  -- orientation.
  bindChannel-close :
    {n : ℕ} (channel : OrientedChannel n) →
    bindChannel (1 ∷ []) (1 ∷ []) channel ≡ (true , [] , [])
  bindChannel-close (i , forward) = refl
  bindChannel-close (i , reverse) = refl

------------------------------------------------------------------------
-- The leaf.

U-close-local :
  {k n m : ℕ}
  {E₁ E₂ : SourceReduction.Frame* k}
  {logicalChannels : Vec (OrientedChannel n) 1}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (1 ∷ []) (1 ∷ [])
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₁
                   (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                 (Source._·¹_ (Source.K (Source.`end Types.‼))
                   (Source.` 0F)) ⟫
       Typed.∥
       Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₂
                   (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                 (Source._·¹_ (Source.K (Source.`end Types.⁇))
                   (Source.` 1F)) ⟫))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.⟪ SourceReduction._[_]* E₁ Source.* ⟫ Typed.∥
     Typed.⟪ SourceReduction._[_]* E₂ Source.* ⟫)
    sigma ambientChannel ambientThread C
U-close-local {k = k} {n = n} {m = m} {E₁ = E₁} {E₂ = E₂}
  {logicalChannels = channel ∷ []} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} Vsigma image =
  dispatch (live-thread body 0F) (live-thread body 1F)
  where
  ----------------------------------------------------------------------
  -- The physical channel and the two physical sides it implements.

  physical : 𝔽 n
  physical = physicalChannel channel

  orientation : Orientation
  orientation = proj₂ channel

  side₁ side₂ : 𝔽 2
  side₁ = orientSide orientation 0F
  side₂ = orientSide orientation 1F

  ----------------------------------------------------------------------
  -- The body of the restriction, and its environment.

  bindRen : 𝔽 k → 𝔽 (2 + k)
  bindRen = Source.weaken* ⦃ Source.Kᵣ ⦄ 2

  redex₁ redex₂ : Source.Tm (2 + k)
  redex₁ = Source._·¹_ (Source.K (Source.`end Types.‼)) (Source.` 0F)
  redex₂ = Source._·¹_ (Source.K (Source.`end Types.⁇)) (Source.` 1F)

  ownerFrame₁ ownerFrame₂ : SourceReduction.Frame* (2 + k)
  ownerFrame₁ = SourceReduction._⋯ᶠ*_ E₁ bindRen
  ownerFrame₂ = SourceReduction._⋯ᶠ*_ E₂ bindRen

  owner₁ owner₂ : Source.Tm (2 + k)
  owner₁ = SourceReduction._[_]* ownerFrame₁ redex₁
  owner₂ = SourceReduction._[_]* ownerFrame₂ redex₂

  env : Translation.Env (2 + k) (2 *ℕ n)
  env = bindEnv (1 ∷ []) (1 ∷ []) channel sigma

  Venv : ValueEnv env
  Venv =
    bindEnv-Value {B₁ = 1 ∷ []} {B₂ = 1 ∷ []} {channel = channel} Vsigma

  binderEnv : Translation.Env 2 (2 *ℕ n)
  binderEnv =
    proj₁ (Translation.UB[ 1 ∷ [] ] (physicalEndpoint channel 0F)
            (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ 1 ∷ [] ] (physicalEndpoint channel 1F)
            (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))

  envCoh : (x : 𝔽 k) → env (bindRen x) ≡ sigma x
  envCoh = weaken*-coherent binderEnv sigma

  body = res-split-image image

  ----------------------------------------------------------------------
  -- The two soup frames and the expected thread contents.

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = Tᶠ*[ ownerFrame₁ ] {σ = env} Venv
  F₂ = Tᶠ*[ ownerFrame₂ ] {σ = env} Venv

  expected₁ expected₂ : Soup.Thread n
  expected₁ = Translation.T[ owner₁ ] env
  expected₂ = Translation.T[ owner₂ ] env

  plugged₁ plugged₂ : Soup.Thread n
  plugged₁ = SoupExpression._[_]* F₁ SoupTerm.*
  plugged₂ = SoupExpression._[_]* F₂ SoupTerm.*

  ----------------------------------------------------------------------
  -- The content of the bound channel.

  chanEq : lookup (Soup.channels C) physical ≡ (true , [] , [])
  chanEq = res-split-channel image ■ bindChannel-close channel

  ----------------------------------------------------------------------
  -- The case analysis on the two owner threads.

  dispatch :
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding body 0F) expected₁ →
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding body 1F) expected₂ →
    LocalStep
      (Typed.⟪ SourceReduction._[_]* E₁ Source.* ⟫ Typed.∥
       Typed.⟪ SourceReduction._[_]* E₂ Source.* ⟫)
      sigma aC aT C

  -- An omitted owner thread would be `K `unit`, but the translation of a
  -- plugged application never is.
  dispatch (omitted slotEq expectedEq) _ =
    ⊥-elim
      (plug-not-K F₁
        (sym (T[_]-plugᶠ* ownerFrame₁ {e = redex₁} Venv) ■ expectedEq))
  dispatch (present _ _ _) (omitted slotEq expectedEq) =
    ⊥-elim
      (plug-not-K F₂
        (sym (T[_]-plugᶠ* ownerFrame₂ {e = redex₂} Venv) ■ expectedEq))

  dispatch (present j slotEq₁ lookupEq₁) (present l slotEq₂ lookupEq₂) =
    identity-step soupStep channelsUnchanged threadsUnchanged targetImage
    where
    j≢l : j ≢ l
    j≢l eq
      with threadEmbedding-injective body slotEq₁
             (slotEq₂ ■ cong just (sym eq))
    ... | ()

    selected₁ = lookupEq₁ ■ T[_]-plugᶠ* ownerFrame₁ {e = redex₁} Venv
    selected₂ = lookupEq₂ ■ T[_]-plugᶠ* ownerFrame₂ {e = redex₂} Venv

    targetChannels : Vec Soup.Channel n
    targetChannels =
      SoupReduction.replaceAt (Soup.channels C) physical (false , [] , [])

    targetThreads : Vec (Soup.Thread n) m
    targetThreads =
      SoupReduction.replaceTwo (Soup.threads C) j plugged₁ l plugged₂

    soupStep :
      C SoupReduction.─→ₚ Soup.config targetChannels targetThreads
    soupStep =
      SoupReduction.RUS-Close
        {cs = Soup.channels C} {ts = Soup.threads C}
        j l physical side₁ side₂ F₁ F₂
        {e₁ = SoupTerm.*} {e₁′ = SoupTerm.*}
        {e₂ = SoupTerm.*} {e₂′ = SoupTerm.*}
        j≢l (orientSide-opposite orientation) chanEq selected₁ selected₂

    ------------------------------------------------------------------
    -- The frame is untouched.

    channelsUnchanged :
      (i : 𝔽 n) → aC i →
      lookup targetChannels i ≡ lookup (Soup.channels C) i
    channelsUnchanged i ambient =
      V.lookup∘updateAt′ i physical
        (λ eq → channel-not-ambient image 0F (subst aC eq ambient))
        (Soup.channels C)

    threadsUnchanged :
      (i : 𝔽 m) → aT i →
      lookup targetThreads i ≡ lookup (Soup.threads C) i
    threadsUnchanged i ambient =
      V.lookup∘updateAt′ i l
        (λ eq → thread-not-ambient body slotEq₂ (subst aT eq ambient))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ i j
          (λ eq → thread-not-ambient body slotEq₁ (subst aT eq ambient))
          (Soup.threads C)

    ------------------------------------------------------------------
    -- The image of the reduct.

    targetThread₁ :
      lookup targetThreads j ≡
      Translation.T[ SourceReduction._[_]* E₁ Source.* ] sigma
    targetThread₁ =
      V.lookup∘updateAt′ j l j≢l
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt j (Soup.threads C)
      ■ Tᶠ*-plug-ren-coh E₁ bindRen env sigma Venv Vsigma envCoh SoupTerm.*
      ■ sym (T[_]-plugᶠ* E₁ {e = Source.*} Vsigma)

    targetThread₂ :
      lookup targetThreads l ≡
      Translation.T[ SourceReduction._[_]* E₂ Source.* ] sigma
    targetThread₂ =
      V.lookup∘updateAt l
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ Tᶠ*-plug-ren-coh E₂ bindRen env sigma Venv Vsigma envCoh SoupTerm.*
      ■ sym (T[_]-plugᶠ* E₂ {e = Source.*} Vsigma)

    targetGarbageChannel :
      (i : 𝔽 n) → ¬ aC i →
      lookup targetChannels i ≡ (false , [] , [])
    targetGarbageChannel i notAmbient with i FinP.≟ physical
    ... | yes refl = V.lookup∘updateAt physical (Soup.channels C)
    ... | no i≢ =
      V.lookup∘updateAt′ i physical i≢ (Soup.channels C)
      ■ garbage-channel image i (λ where 0F eq → i≢ (sym eq)) notAmbient

    targetGarbageThread :
      (i : 𝔽 m) → OptionalOutside (threadEmbedding body) i → ¬ aT i →
      lookup targetThreads i ≡ SoupTerm.K Source.`unit
    targetGarbageThread i outside notAmbient =
      V.lookup∘updateAt′ i l
        (λ eq → outside 1F (slotEq₂ ■ cong just (sym eq)))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ i j
          (λ eq → outside 0F (slotEq₁ ■ cong just (sym eq)))
          (Soup.threads C)
      ■ garbage-thread body i outside notAmbient

    targetImage :
      LocalImage
        (Typed.⟪ SourceReduction._[_]* E₁ Source.* ⟫ Typed.∥
         Typed.⟪ SourceReduction._[_]* E₂ Source.* ⟫)
        [] sigma aC aT (Soup.config targetChannels targetThreads)
    targetImage = record
      { channelEmbedding-injective = channelEmbedding-injective body
      ; threadEmbedding = threadEmbedding body
      ; threadEmbedding-injective = threadEmbedding-injective body
      ; channel-not-ambient = λ ()
      ; thread-not-ambient = thread-not-ambient body
      ; live-channel = λ ()
      ; live-thread = λ where
          0F → present j slotEq₁ targetThread₁
          1F → present l slotEq₂ targetThread₂
      ; garbage-channel = λ i _ notAmbient → targetGarbageChannel i notAmbient
      ; garbage-thread = targetGarbageThread
      }
