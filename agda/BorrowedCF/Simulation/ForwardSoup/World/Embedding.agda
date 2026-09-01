module BorrowedCF.Simulation.ForwardSoup.World.Embedding where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open Nat.Variables

Transport : {a b : ℕ} → (𝔽 a → 𝔽 b) → (𝔽 a → Set) → 𝔽 b → Set
Transport embedding predicate j =
  Σ[ i ∈ _ ] predicate i × embedding i ≡ j

record AmbientEmbedding
  {n m n′ m′ : ℕ}
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (source : Soup.Config n m)
  (target : Soup.Config n′ m′) : Set where
  field
    channelEmbedding : 𝔽 n → 𝔽 n′
    channelEmbedding-injective :
      ∀ {i j} → channelEmbedding i ≡ channelEmbedding j → i ≡ j

    threadEmbedding : 𝔽 m → 𝔽 m′
    threadEmbedding-injective :
      ∀ {i j} → threadEmbedding i ≡ threadEmbedding j → i ≡ j

    endpointEmbedding : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ n′)
    endpoint-respects-channel :
      (i : 𝔽 n) (side : 𝔽 2) →
      endpointEmbedding (Soup.endpoint i side) ≡
      Soup.endpoint (channelEmbedding i) side

    ambient-channel-content :
      (i : 𝔽 n) → ambientChannel i →
      lookup (Soup.channels target) (channelEmbedding i) ≡
      lookup (Soup.channels source) i

    ambient-thread-content :
      (j : 𝔽 m) → ambientThread j →
      lookup (Soup.threads target) (threadEmbedding j) ≡
      lookup (Soup.threads source) j SoupTerm.⋯ᵣ endpointEmbedding

open AmbientEmbedding public

targetAmbientChannel :
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {source : Soup.Config n m} {target : Soup.Config n′ m′} →
  AmbientEmbedding ambientChannel ambientThread source target →
  𝔽 n′ → Set
targetAmbientChannel {ambientChannel = ambientChannel} embedding =
  Transport (channelEmbedding embedding) ambientChannel

targetAmbientThread :
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {source : Soup.Config n m} {target : Soup.Config n′ m′} →
  AmbientEmbedding ambientChannel ambientThread source target →
  𝔽 m′ → Set
targetAmbientThread {ambientThread = ambientThread} embedding =
  Transport (threadEmbedding embedding) ambientThread
