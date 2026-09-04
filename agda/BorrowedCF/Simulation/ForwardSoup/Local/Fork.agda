-- | Phase 3, leaf rule `R-Fork` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   The redex thread `E [ K `fork ·¹ e ]*` splits into the continuation
--   `E [ * ]*` and a fresh child `e ·¹ *`, inserted directly behind it.  The
--   channel namespace is untouched, but the thread namespace grows by one, so
--   the frame travels along the embedding `Fin.punchIn (suc j)`, where `j` is
--   the physical slot of the redex thread.  The continuation lands in slot
--   `Fin.punchIn (suc j) j` and the child in slot `suc j`.
module BorrowedCF.Simulation.ForwardSoup.Local.Fork where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just)

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
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*; T[_]-Value)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (ambient-resp; env-resp)
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (Transport; AmbientEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

private
  just-inj :
    {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
  just-inj refl = refl

------------------------------------------------------------------------
-- The leaf.

record ForkStep
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {e : Source.Tm k}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    forkParent : 𝔽 m
    forkSourceFrame : SourceReduction.Frame* k
    forkSourceFrame≡ : forkSourceFrame ≡ E

    forkFrame : SoupExpression.Frame* (2 *ℕ n)
    forkChild : Soup.Thread n
    forkChild≡ : forkChild ≡ Translation.T[ e ] sigma
    forkChildValue : SoupExpression.Value forkChild
    forkSourceValue : SourceReduction.Value e

    forkSelectedSource :
      lookup (Soup.threads C) forkParent ≡
      Translation.T[
        SourceReduction._[_]* E
          (Source._·¹_ (Source.K Source.`fork) e)
      ] sigma
    forkSelectedFork :
      lookup (Soup.threads C) forkParent ≡
      SoupExpression._[_]* forkFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`fork)
          (Translation.T[ e ] sigma))

    forkParentSlot forkChildSlot : 𝔽 (suc m)
    forkParentSlot≡ : forkParentSlot ≡ Fin.punchIn (suc forkParent) forkParent
    forkChildSlot≡ : forkChildSlot ≡ suc forkParent

    forkConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.insertAfter
            (SoupReduction.replaceAt (Soup.threads C) forkParent
              (SoupExpression._[_]* forkFrame SoupTerm.*))
            forkParent
            (SoupTerm._·¹_ (Translation.T[ e ] sigma) SoupTerm.*)))

open ForkStep public

fork-step :
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {e : Source.Tm k}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  SourceReduction.Value e →
  LocalImage
    (Typed.⟪ SourceReduction._[_]* E
               (Source._·¹_ (Source.K Source.`fork) e) ⟫)
    logicalChannels sigma ambientChannel ambientThread C →
  ForkStep {E = E} {e = e}
    (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥
     Typed.⟪ Source._·¹_ e Source.* ⟫)
    sigma ambientChannel ambientThread C
fork-step {n = n} {m = m} {E = E} {e = e}
  {logicalChannels = []} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} Vsigma Ve image
  with live-thread image 0F

-- An omitted redex thread would be `K `unit`, but the translation of a
-- plugged application never is.
... | omitted slotEq expectedEq =
  ⊥-elim
    (plug-not-K (Tᶠ*[ E ] {σ = sigma} Vsigma)
      (sym (T[_]-plugᶠ* E
              {e = Source._·¹_ (Source.K Source.`fork) e} Vsigma)
       ■ expectedEq))

... | present j slotEq lookupEq = record
  { forkParent = j
  ; forkSourceFrame = E
  ; forkSourceFrame≡ = refl
  ; forkFrame = F
  ; forkChild = Translation.T[ e ] sigma
  ; forkChild≡ = refl
  ; forkChildValue = T[_]-Value Ve Vsigma
  ; forkSourceValue = Ve
  ; forkSelectedSource = lookupEq
  ; forkSelectedFork = selected
  ; forkParentSlot = parentIndex
  ; forkChildSlot = suc j
  ; forkParentSlot≡ = refl
  ; forkChildSlot≡ = refl
  ; forkConfigStep = record
      { config-step = soupStep
      ; config-embedding = emb
      ; config-logicalChannels′ = []
      ; config-image′ =
          ambient-resp toChannel fromChannel (λ _ ambient → ambient)
            (λ _ ambient → ambient)
            (env-resp (λ x → sym (ren-id (sigma x) (λ _ → refl))) targetImage)
      }
  }
  where
  ts : Vec (Soup.Thread n) m
  ts = Soup.threads C

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ E ] {σ = sigma} Vsigma

  parent child : Soup.Thread n
  parent = SoupExpression._[_]* F SoupTerm.*
  child = SoupTerm._·¹_ (Translation.T[ e ] sigma) SoupTerm.*

  targetThreads : Vec (Soup.Thread n) (suc m)
  targetThreads =
    V.insertAt (SoupReduction.replaceAt ts j parent) (suc j) child

  targetConfig : Soup.Config n (suc m)
  targetConfig = Soup.config (Soup.channels C) targetThreads

  selected :
    lookup ts j ≡
    SoupExpression._[_]* F
      (SoupTerm._·¹_ (SoupTerm.K Source.`fork) (Translation.T[ e ] sigma))
  selected =
    lookupEq
    ■ T[_]-plugᶠ* E {e = Source._·¹_ (Source.K Source.`fork) e} Vsigma

  soupStep : C SoupReduction.─→ₚ targetConfig
  soupStep =
    SoupReduction.RUS-Fork {cs = Soup.channels C} {ts = ts} j F
      (T[_]-Value Ve Vsigma) selected

  j-not-ambient : ¬ aT j
  j-not-ambient = thread-not-ambient image slotEq

  -- The slot of the continuation in the enlarged thread vector.
  parentIndex : 𝔽 (suc m)
  parentIndex = Fin.punchIn (suc j) j

  ----------------------------------------------------------------------
  -- The embedding: the child is inserted, so ambient threads are punched.

  ambientThreadContent :
    (l : 𝔽 m) → aT l →
    lookup targetThreads (Fin.punchIn (suc j) l) ≡ lookup ts l SoupTerm.⋯ᵣ id
  ambientThreadContent l ambient =
    V.insertAt-punchIn (SoupReduction.replaceAt ts j parent) (suc j) child l
    ■ V.lookup∘updateAt′ l j
        (λ l≡j → j-not-ambient (subst aT l≡j ambient)) ts
    ■ sym (ren-id (lookup ts l) (λ _ → refl))

  emb : AmbientEmbedding aC aT C targetConfig
  emb = record
    { channelEmbedding = id
    ; channelEmbedding-injective = id
    ; threadEmbedding = Fin.punchIn (suc j)
    ; threadEmbedding-injective = λ {l₁} {l₂} eq →
        Fin.punchIn-injective (suc j) l₁ l₂ eq
    ; endpointEmbedding = id
    ; endpoint-respects-channel = λ _ _ → refl
    ; ambient-channel-content = λ _ _ → refl
    ; ambient-thread-content = ambientThreadContent
    }

  toChannel : (i : 𝔽 n) → aC i → Transport id aC i
  toChannel i ambient = i , ambient , refl

  fromChannel : (i : 𝔽 n) → Transport id aC i → aC i
  fromChannel i (source , ambient , sourceEq) = subst aC sourceEq ambient

  ----------------------------------------------------------------------
  -- The image of the reduct.

  aT′ : 𝔽 (suc m) → Set
  aT′ = Transport (Fin.punchIn (suc j)) aT

  targetThreadEmbedding : 𝔽 2 → Maybe (𝔽 (suc m))
  targetThreadEmbedding zero = just parentIndex
  targetThreadEmbedding (suc zero) = just (suc j)

  targetThreadEmbedding-injective :
    ∀ {i₁ i₂ l} →
    targetThreadEmbedding i₁ ≡ just l →
    targetThreadEmbedding i₂ ≡ just l →
    i₁ ≡ i₂
  targetThreadEmbedding-injective {zero} {zero} eq₁ eq₂ = refl
  targetThreadEmbedding-injective {zero} {suc zero} eq₁ eq₂ =
    ⊥-elim (Fin.punchInᵢ≢i (suc j) j (just-inj (eq₁ ■ sym eq₂)))
  targetThreadEmbedding-injective {suc zero} {zero} eq₁ eq₂ =
    ⊥-elim (Fin.punchInᵢ≢i (suc j) j (just-inj (eq₂ ■ sym eq₁)))
  targetThreadEmbedding-injective {suc zero} {suc zero} eq₁ eq₂ = refl

  targetThread-not-ambient :
    ∀ {i l} → targetThreadEmbedding i ≡ just l → ¬ aT′ l
  targetThread-not-ambient {zero} eq (source , ambient , sourceEq) =
    j-not-ambient
      (subst aT
        (Fin.punchIn-injective (suc j) source j
          (sourceEq ■ sym (just-inj eq)))
        ambient)
  targetThread-not-ambient {suc zero} eq (source , ambient , sourceEq) =
    Fin.punchInᵢ≢i (suc j) source (sourceEq ■ sym (just-inj eq))

  parentLive :
    lookup targetThreads parentIndex ≡
    Translation.T[ SourceReduction._[_]* E Source.* ] sigma
  parentLive =
    V.insertAt-punchIn (SoupReduction.replaceAt ts j parent) (suc j) child j
    ■ V.lookup∘updateAt j ts
    ■ sym (T[_]-plugᶠ* E {e = Source.*} Vsigma)

  childLive :
    lookup targetThreads (suc j) ≡
    Translation.T[ Source._·¹_ e Source.* ] sigma
  childLive =
    V.insertAt-lookup (SoupReduction.replaceAt ts j parent) (suc j) child

  targetGarbageThread :
    (l : 𝔽 (suc m)) → OptionalOutside targetThreadEmbedding l → ¬ aT′ l →
    lookup targetThreads l ≡ SoupTerm.K Source.`unit
  targetGarbageThread l outside notAmbient =
    cong (lookup targetThreads) (sym punchEq)
    ■ V.insertAt-punchIn
        (SoupReduction.replaceAt ts j parent) (suc j) child l₀
    ■ V.lookup∘updateAt′ l₀ j l₀≢j ts
    ■ garbage-thread image l₀ outsideOld notAmbientOld
    where
    sucj≢l : suc j ≢ l
    sucj≢l eq = outside 1F (cong just eq)

    l₀ : 𝔽 m
    l₀ = Fin.punchOut {i = suc j} {j = l} sucj≢l

    punchEq : Fin.punchIn (suc j) l₀ ≡ l
    punchEq = Fin.punchIn-punchOut sucj≢l

    l₀≢j : l₀ ≢ j
    l₀≢j eq =
      outside 0F
        (cong just (sym (cong (Fin.punchIn (suc j)) eq) ■ punchEq))

    outsideOld : OptionalOutside (threadEmbedding image) l₀
    outsideOld 0F eq = l₀≢j (sym (just-inj (sym slotEq ■ eq)))

    notAmbientOld : ¬ aT l₀
    notAmbientOld ambient = notAmbient (l₀ , ambient , punchEq)

  targetImage :
    LocalImage
      (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥
       Typed.⟪ Source._·¹_ e Source.* ⟫)
      [] sigma aC aT′ targetConfig
  targetImage = record
    { channelEmbedding-injective = channelEmbedding-injective image
    ; threadEmbedding = targetThreadEmbedding
    ; threadEmbedding-injective = targetThreadEmbedding-injective
    ; channel-not-ambient = λ ()
    ; thread-not-ambient = targetThread-not-ambient
    ; live-channel = λ ()
    ; live-thread = λ where
        0F → present parentIndex refl parentLive
        1F → present (suc j) refl childLive
    ; garbage-channel = garbage-channel image
    ; garbage-thread = targetGarbageThread
    }

U-fork-local :
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {e : Source.Tm k}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  SourceReduction.Value e →
  LocalImage
    (Typed.⟪ SourceReduction._[_]* E
               (Source._·¹_ (Source.K Source.`fork) e) ⟫)
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.⟪ SourceReduction._[_]* E Source.* ⟫ Typed.∥
     Typed.⟪ Source._·¹_ e Source.* ⟫)
    sigma ambientChannel ambientThread C
U-fork-local {k = k} {n = n} {m = m} {E = E} {e = e}
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma Ve image =
  configStep⇒localStep
    (forkConfigStep
      (fork-step {k = k} {n = n} {m = m} {E = E} {e = e}
        {logicalChannels = logicalChannels} {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} Vsigma Ve image))
