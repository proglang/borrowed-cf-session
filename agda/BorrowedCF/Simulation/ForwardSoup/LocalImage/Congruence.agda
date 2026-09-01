module BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage

open Nat.Variables
open Fin.Patterns

unitProcess : ∀ {n} → Typed.Proc n
unitProcess = Typed.⟪ Source.K Source.`unit ⟫

retarget-thread :
  {threads : Vec (Soup.Thread n) m} {slot : Maybe (𝔽 m)}
  {before after : Soup.Thread n} →
  before ≡ after →
  OptionalThreadImage {n = n} threads slot before →
  OptionalThreadImage {n = n} threads slot after
retarget-thread equal (present l embedded live) =
  present l embedded (live ■ equal)
retarget-thread equal (omitted omittedEq unitEq) =
  omitted omittedEq (sym equal ■ unitEq)

unit-head-thread :
  (P : Typed.Proc n)
  (channels : Vec (OrientedChannel c) (Translation.channelCount P))
  (sigma : Translation.Env n (2 *ℕ c)) →
  lookup (proj₂ (flattenOriented (unitProcess Typed.∥ P) channels sigma))
    0F ≡ SoupTerm.K Source.`unit
unit-head-thread P channels sigma
  with flattenOriented P channels sigma
... | channelsP , threadsP = refl

unit-tail-thread :
  (P : Typed.Proc n)
  (channels : Vec (OrientedChannel c) (Translation.channelCount P))
  (sigma : Translation.Env n (2 *ℕ c))
  (j : 𝔽 (Translation.processCount P)) →
  lookup (proj₂ (flattenOriented (unitProcess Typed.∥ P) channels sigma))
    (suc j) ≡
  lookup (proj₂ (flattenOriented P channels sigma)) j
unit-tail-thread P channels sigma j
  with flattenOriented P channels sigma
... | channelsP , threadsP = refl

unit-left-elim :
  {P : Typed.Proc n}
  {channels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (unitProcess Typed.∥ P) channels sigma
    ambientChannel ambientThread C →
  LocalImage P channels sigma ambientChannel ambientThread C
unit-left-elim {c = c} {m = m} {P = P} {channels = channels} {sigma = sigma}
  {ambientThread = ambientThread} {C = C} image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image ∘ suc
  ; threadEmbedding-injective = λ equalᵢ equalⱼ →
      Fin.suc-injective (threadEmbedding-injective image equalᵢ equalⱼ)
  ; live-channel = live-channel image
  ; live-thread = λ j →
      retarget-thread {n = c} {threads = Soup.threads C}
        (unit-tail-thread P channels sigma j)
        (live-thread image (suc j))
  ; garbage-channel = garbage-channel image
  ; garbage-thread = garbageThread
  }
  where
  garbageThread :
    (j : 𝔽 m) →
    OptionalOutside (threadEmbedding image ∘ suc) j →
    ¬ ambientThread j →
    lookup (Soup.threads C) j ≡ SoupTerm.K Source.`unit
  garbageThread j outside notAmbient
    with live-thread image 0F
  ... | omitted omittedEq unitEq =
    garbage-thread image j oldOutside notAmbient
    where
    oldOutside : OptionalOutside (threadEmbedding image) j
    oldOutside zero equal = case sym omittedEq ■ equal of λ ()
    oldOutside (suc k) = outside k
  ... | present l embedded live with FinP._≟_ l j
  ...   | yes refl =
    live ■ unit-head-thread P channels sigma
  ...   | no l≠j =
    garbage-thread image j oldOutside notAmbient
    where
    oldOutside : OptionalOutside (threadEmbedding image) j
    oldOutside zero equal = l≠j (just-injective (sym embedded ■ equal))
    oldOutside (suc k) = outside k

unit-left-intro :
  {P : Typed.Proc n}
  {channels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage P channels sigma ambientChannel ambientThread C →
  LocalImage (unitProcess Typed.∥ P) channels sigma
    ambientChannel ambientThread C
unit-left-intro {c = c} {m = m} {P = P} {channels = channels}
  {sigma = sigma} {C = C} image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = embedding′
  ; threadEmbedding-injective = embedding′-injective
  ; live-channel = live-channel image
  ; live-thread = λ where
      zero → omitted refl (unit-head-thread P channels sigma)
      (suc j) →
        retarget-thread {n = c} {threads = Soup.threads C}
          (sym (unit-tail-thread P channels sigma j))
          (live-thread image j)
  ; garbage-channel = garbage-channel image
  ; garbage-thread = λ j outside →
      garbage-thread image j (λ k → outside (suc k))
  }
  where
  embedding′ : 𝔽 (suc (Translation.processCount P)) → Maybe (𝔽 m)
  embedding′ zero = nothing
  embedding′ (suc j) = threadEmbedding image j

  embedding′-injective :
    ∀ {i j l} →
    embedding′ i ≡ just l →
    embedding′ j ≡ just l →
    i ≡ j
  embedding′-injective {zero} ()
  embedding′-injective {suc i} {zero} equalᵢ ()
  embedding′-injective {suc i} {suc j} equalᵢ equalⱼ =
    cong suc (threadEmbedding-injective image equalᵢ equalⱼ)
