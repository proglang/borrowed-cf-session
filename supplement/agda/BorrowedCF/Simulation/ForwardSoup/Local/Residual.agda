-- | Phase 3 helper for the ν-rule leaves (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   Every remaining ν-rule (`R-Com`, `R-LSplit`, `R-RSplit`, `R-Drop`,
--   `R-Discard`) leaves the residual process *renamed* in the redex and plain
--   in the reduct:
--
--     ν … ((⟪ … ⟫ ∥ ⟪ … ⟫) ∥ (P ⋯ₚ ρ))  ─→ₚ  ν … ((⟪ … ⟫ ∥ ⟪ … ⟫) ∥ P)
--
--   The image of the residual therefore has to travel from `P ⋯ₚ ρ` to `P`.
--   `LocalImage/Renaming.agda` provides the *forward* direction; here it is
--   inverted by `reindex-sym`, which forces the channel vector back through
--   the `V.cast` round trip of `Simulation/ForwardSoup/Renaming.agda`.
--
--   `residual-image` keeps the thread embedding of its argument on the nose
--   (`channels-resp` is a plain record copy, `reindex-image` postcomposes with
--   `threadBackward`), so a caller can read
--
--     threadEmbedding (residual-image coh image) j
--       = threadEmbedding image (Fin.cast (sym (processCount-rename P ρ)) j)
--
--   definitionally; `residual-thread` records that fact.
module BorrowedCF.Simulation.ForwardSoup.Local.Residual where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using (reindex-image; retarget-thread)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (ownedChannels)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Reindex
  using (reindex-sym)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Renaming
  using (renaming-reindex)
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (transportChannels; untransportChannels; transportChannels-cast)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename; processCount-rename)

private
  variable
    A : Set
    a b k n m : ℕ

------------------------------------------------------------------------
-- The other `V.cast` round trip.  `Renaming.agda` only proves
-- `transportChannels ∘ untransportChannels ≗ id`; the residual needs the
-- opposite composite, because the image it starts from is indexed by the
-- *renamed* channel count.

private
  cast-cast :
    {p q : ℕ} (equal : p ≡ q) (xs : Vec A p) →
    V.cast (sym equal) (V.cast equal xs) ≡ xs
  cast-cast equal xs =
    V.cast-trans equal (sym equal) xs ■
    V.cast-is-id (equal ■ sym equal) xs

untransport-transport :
  (P : Typed.Proc a) (rho : 𝔽 a → 𝔽 b)
  (xs : Vec A (Translation.channelCount (P Typed.⋯ₚ rho))) →
  untransportChannels P rho (transportChannels P rho xs) ≡ xs
untransport-transport P rho xs =
  cong (V.cast (sym (channelCount-rename P rho)))
    (transportChannels-cast P rho xs)
  ■ cast-cast (channelCount-rename P rho) xs

------------------------------------------------------------------------
-- Changing the channel vector of an image along an equality.  Spelled out
-- as a record copy rather than as a `subst`, so that the thread embedding of
-- the result is *syntactically* the thread embedding of the argument.

channels-resp :
  {P : Typed.Proc k}
  {channels channels′ :
    Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  channels ≡ channels′ →
  LocalImage P channels sigma ambientChannel ambientThread C →
  LocalImage P channels′ sigma ambientChannel ambientThread C
channels-resp {P = P} {channels = channels} {channels′ = channels′}
  {sigma = sigma} {ambientChannel = ambientChannel} {C = C} equal image = record
  { channelEmbedding-injective = λ {i} {j} same →
      channelEmbedding-injective image
        (entry i ■ same ■ sym (entry j))
  ; threadEmbedding = threadEmbedding image
  ; threadEmbedding-injective = threadEmbedding-injective image
  ; channel-not-ambient = λ i ambient →
      channel-not-ambient image i (subst ambientChannel (sym (entry i)) ambient)
  ; thread-not-ambient = thread-not-ambient image
  ; live-channel = λ i →
      cong (lookup (Soup.channels C)) (sym (entry i))
      ■ live-channel image i
      ■ cong (λ cs → lookup (proj₁ (flattenOriented P cs sigma)) i) equal
  ; live-thread = λ j →
      retarget-thread {threads = Soup.threads C}
        (cong (λ cs → lookup (proj₂ (flattenOriented P cs sigma)) j) equal)
        (live-thread image j)
  ; garbage-channel = λ i outside notAmbient →
      garbage-channel image i
        (λ j same → outside j (sym (entry j) ■ same))
        notAmbient
  ; garbage-thread = garbage-thread image
  }
  where
  entry :
    (i : 𝔽 (Translation.channelCount P)) →
    physicalChannel (lookup channels i) ≡
    physicalChannel (lookup channels′ i)
  entry i = cong (λ cs → physicalChannel (lookup cs i)) equal

------------------------------------------------------------------------
-- The residual under a renaming.

residual-image :
  {P : Typed.Proc a} {rho : 𝔽 a → 𝔽 b}
  {channels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.⋯ₚ rho))}
  {sourceEnv : Translation.Env b (2 *ℕ n)}
  {targetEnv : Translation.Env a (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ((x : 𝔽 a) → sourceEnv (rho x) ≡ targetEnv x) →
  LocalImage (P Typed.⋯ₚ rho) channels sourceEnv
    ambientChannel ambientThread C →
  LocalImage P (transportChannels P rho channels) targetEnv
    ambientChannel ambientThread C
residual-image {P = P} {rho = rho} {channels = channels}
  {sourceEnv = sourceEnv} {targetEnv = targetEnv} coherent image =
  reindex-image
    (reindex-sym
      (renaming-reindex {P = P} {rho = rho}
        {sourceChannels = transportChannels P rho channels}
        {sourceEnv = sourceEnv} {targetEnv = targetEnv} coherent))
    (channels-resp (sym (untransport-transport P rho channels)) image)

-- The thread embedding is only re-indexed by the `V.cast` on process counts.
residual-thread :
  {P : Typed.Proc a} {rho : 𝔽 a → 𝔽 b}
  {channels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.⋯ₚ rho))}
  {sourceEnv : Translation.Env b (2 *ℕ n)}
  {targetEnv : Translation.Env a (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (coherent : (x : 𝔽 a) → sourceEnv (rho x) ≡ targetEnv x)
  (image :
    LocalImage (P Typed.⋯ₚ rho) channels sourceEnv
      ambientChannel ambientThread C)
  (j : 𝔽 (Translation.processCount P)) →
  threadEmbedding (residual-image {P = P} {rho = rho} coherent image) j ≡
  threadEmbedding image (Fin.cast (sym (processCount-rename P rho)) j)
residual-thread coherent image j = refl

------------------------------------------------------------------------
-- Ownership of the transported channel vector.

private
  transport-lookup :
    (P : Typed.Proc a) (rho : 𝔽 a → 𝔽 b)
    (channels :
      Vec (OrientedChannel n) (Translation.channelCount (P Typed.⋯ₚ rho)))
    (i : 𝔽 (Translation.channelCount P)) →
    lookup (transportChannels P rho channels) i ≡
    lookup channels (Fin.cast (sym (channelCount-rename P rho)) i)
  transport-lookup P rho channels i =
    cong (λ xs → lookup xs i) (transportChannels-cast P rho channels)
    ■ V.lookup-cast₁ (channelCount-rename P rho) channels i

ownedChannels-transport :
  {P : Typed.Proc a} {rho : 𝔽 a → 𝔽 b}
  {channels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.⋯ₚ rho))}
  (i : 𝔽 n) →
  ownedChannels (transportChannels P rho channels) i →
  ownedChannels channels i
ownedChannels-transport {P = P} {rho = rho} {channels = channels} i
  (j , owned) =
  Fin.cast (sym (channelCount-rename P rho)) j
  , (sym (cong physicalChannel (transport-lookup P rho channels j)) ■ owned)

ownedChannels-transport⁻ :
  {P : Typed.Proc a} {rho : 𝔽 a → 𝔽 b}
  {channels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.⋯ₚ rho))}
  (i : 𝔽 n) →
  ownedChannels channels i →
  ownedChannels (transportChannels P rho channels) i
ownedChannels-transport⁻ {P = P} {rho = rho} {channels = channels} i
  (j , owned) =
  Fin.cast (channelCount-rename P rho) j
  , ( cong physicalChannel
        ( transport-lookup P rho channels
            (Fin.cast (channelCount-rename P rho) j)
        ■ cong (lookup channels)
            (Fin.cast-involutive (sym (channelCount-rename P rho))
              (channelCount-rename P rho) j)
        )
    ■ owned
    )
