-- | Phase 3, leaf rule `R-Exp` (`ForwardSoup/PLAN.md`, §4, Phase 3, item 1).
--
--   A pure expression step happens inside one thread: the soup takes the
--   corresponding `RUS-Exp` step on the thread carrying the translation of the
--   redex, and nothing else moves.  In particular the physical namespace is
--   unchanged, so the frame travels along `identity-step`.
module BorrowedCF.Simulation.ForwardSoup.Local.Exp where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Expressions as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; T[_]-⋯→)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.Local.Step

open Nat.Variables hiding (n′; m′)

------------------------------------------------------------------------
-- The redex thread is `present`: its expected content is `T[ e ] sigma`,
-- which steps, whereas `K `unit` does not.

record ExpStep
  {k n m : ℕ} {e e′ : Source.Tm k}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    expThread : 𝔽 m

    expSelectedThread :
      lookup (Soup.threads C) expThread ≡ Translation.T[ e ] sigma
    expSourceStep :
      e SourceReduction.⋯→ e′
    expTranslatedStep :
      lookup (Soup.threads C) expThread
        SoupExpression.⋯→ Translation.T[ e′ ] sigma

    expConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.replaceAt (Soup.threads C) expThread
            (Translation.T[ e′ ] sigma)))

open ExpStep public

exp-step :
  {k n m : ℕ} {e e′ : Source.Tm k}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  LocalImage (Typed.⟪ e ⟫) logicalChannels sigma
    ambientChannel ambientThread C →
  e SourceReduction.⋯→ e′ →
  ExpStep {e = e} {e′ = e′}
    (Typed.⟪ e′ ⟫) sigma ambientChannel ambientThread C
exp-step {n = n} {m = m} {e = e} {e′ = e′} {logicalChannels = []} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma image red
  with live-thread image zero

-- The thread is omitted, so its content would be `K `unit`; but the
-- translation of the redex steps, and a constant does not.
... | omitted slotEq expectedEq =
  ⊥-elim
    (K-irreducible
      (subst (λ source → source SoupExpression.⋯→ Translation.T[ e′ ] sigma)
        expectedEq translatedStep))
  where
  translatedStep :
    Translation.T[ e ] sigma SoupExpression.⋯→ Translation.T[ e′ ] sigma
  translatedStep = T[_]-⋯→ Vsigma red

... | present j slotEq lookupEq = record
  { expThread = j
  ; expSelectedThread = lookupEq
  ; expSourceStep = red
  ; expTranslatedStep = selectedStep
  ; expConfigStep =
      identity-config-step (SoupReduction.RUS-Exp j selectedStep)
        (λ _ _ → refl) threadsUnchanged targetImage
  }
  where
  targetThreads : Vec (Soup.Thread n) m
  targetThreads =
    SoupReduction.replaceAt (Soup.threads C) j (Translation.T[ e′ ] sigma)

  selectedStep :
    lookup (Soup.threads C) j SoupExpression.⋯→ Translation.T[ e′ ] sigma
  selectedStep =
    subst (λ source → source SoupExpression.⋯→ Translation.T[ e′ ] sigma)
      (sym lookupEq) (T[_]-⋯→ Vsigma red)

  -- An ambient thread is not the redex thread, so it is untouched.
  threadsUnchanged :
    (l : 𝔽 m) → ambientThread l →
    lookup targetThreads l ≡ lookup (Soup.threads C) l
  threadsUnchanged l ambient =
    V.lookup∘updateAt′ l j
      (λ l≡j → thread-not-ambient image slotEq (subst ambientThread l≡j ambient))
      (Soup.threads C)

  targetImage :
    LocalImage (Typed.⟪ e′ ⟫) [] sigma ambientChannel ambientThread
      (Soup.config (Soup.channels C) targetThreads)
  targetImage = record
    { channelEmbedding-injective = channelEmbedding-injective image
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; channel-not-ambient = channel-not-ambient image
    ; thread-not-ambient = thread-not-ambient image
    ; live-channel = live-channel image
    ; live-thread = λ where
        zero → present j slotEq (V.lookup∘updateAt j (Soup.threads C))
    ; garbage-channel = garbage-channel image
    ; garbage-thread = λ l outside notAmbient →
        V.lookup∘updateAt′ l j
          (λ l≡j → outside zero (slotEq ■ cong just (sym l≡j)))
          (Soup.threads C)
        ■ garbage-thread image l outside notAmbient
    }

U-exp-local :
  {k n m : ℕ} {e e′ : Source.Tm k}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  LocalImage (Typed.⟪ e ⟫) logicalChannels sigma
    ambientChannel ambientThread C →
  e SourceReduction.⋯→ e′ →
  LocalStep (Typed.⟪ e′ ⟫) sigma ambientChannel ambientThread C
U-exp-local {k = k} {n = n} {m = m} {e = e} {e′ = e′}
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma image red =
  configStep⇒localStep
    (expConfigStep
      (exp-step {k = k} {n = n} {m = m} {e = e} {e′ = e′}
        {logicalChannels = logicalChannels} {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} Vsigma image red))
