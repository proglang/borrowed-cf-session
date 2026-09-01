module BorrowedCF.Simulation.ForwardSoup.Image where

open import Data.Bool using (false)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup as 𝐒Tm hiding (wk)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as TranslationSoup
import BorrowedCF.Processes.UntypedSoup as 𝐒

open 𝐓 using (Proc)
open TranslationSoup using (channelCount; processCount; flatten)

open Nat.Variables

FinInjective : {a b : ℕ} → (𝔽 a → 𝔽 b) → Set
FinInjective f = ∀ {x y} → f x ≡ f y → x ≡ y

canonicalFlatten :
  (P : Proc 0) →
  Vec 𝐒.Channel (channelCount P) ×
  Vec (𝐒.Thread (channelCount P)) (processCount P)
canonicalFlatten P = flatten P (V.allFin (channelCount P)) (λ ())

canonicalChannels : (P : Proc 0) → Vec 𝐒.Channel (channelCount P)
canonicalChannels P = proj₁ (canonicalFlatten P)

canonicalThreads :
  (P : Proc 0) → Vec (𝐒.Thread (channelCount P)) (processCount P)
canonicalThreads P = proj₂ (canonicalFlatten P)

liftRen-id :
  {ρ : 𝔽 n → 𝔽 n} →
  ρ ≗ id →
  liftRen ρ ≗ id
liftRen-id ρ≗ zero = refl
liftRen-id ρ≗ (suc x) = cong suc (ρ≗ x)

rename-id≗ :
  (e : Tm n) {ρ : 𝔽 n → 𝔽 n} →
  ρ ≗ id →
  e ⋯ᵣ ρ ≡ e
rename-id≗ (` x) ρ≗ = cong `_ (ρ≗ x)
rename-id≗ (`phi (x , k)) ρ≗ = cong (λ y → `phi (y , k)) (ρ≗ x)
rename-id≗ (K c) ρ≗ = refl
rename-id≗ (ƛ e) ρ≗ = cong ƛ (rename-id≗ e (liftRen-id ρ≗))
rename-id≗ (μ e) ρ≗ = cong μ (rename-id≗ e (liftRen-id ρ≗))
rename-id≗ (e₁ ·⟨ d ⟩ e₂) ρ≗ =
  cong₂ (_·⟨ d ⟩_) (rename-id≗ e₁ ρ≗) (rename-id≗ e₂ ρ≗)
rename-id≗ (e₁ ; e₂) ρ≗ =
  cong₂ _;_ (rename-id≗ e₁ ρ≗) (rename-id≗ e₂ ρ≗)
rename-id≗ (e₁ ⊗ e₂) ρ≗ =
  cong₂ _⊗_ (rename-id≗ e₁ ρ≗) (rename-id≗ e₂ ρ≗)
rename-id≗ (`let e₁ `in e₂) ρ≗ =
  cong₂ `let_`in_
    (rename-id≗ e₁ ρ≗)
    (rename-id≗ e₂ (liftRen-id ρ≗))
rename-id≗ (`let⊗ e₁ `in e₂) ρ≗ =
  cong₂ `let⊗_`in_
    (rename-id≗ e₁ ρ≗)
    (rename-id≗ e₂ (liftRen-id (liftRen-id ρ≗)))
rename-id≗ (`inj i e) ρ≗ = cong (`inj i) (rename-id≗ e ρ≗)
rename-id≗ (`case e `of⟨ e₁ ; e₂ ⟩) ρ≗ =
  cong₂ (λ e′ e₁′ → `case e′ `of⟨ e₁′ ; _ ⟩)
    (rename-id≗ e ρ≗)
    (rename-id≗ e₁ (liftRen-id ρ≗))
  ■ cong (`case _ `of⟨ _ ;_⟩) (rename-id≗ e₂ (liftRen-id ρ≗))

rename-id : (e : Tm n) → e ⋯ᵣ id ≡ e
rename-id e = rename-id≗ e (λ _ → refl)

ChannelOutside :
  {P : Proc 0} {n : ℕ} →
  (𝔽 (channelCount P) → 𝔽 n) → 𝔽 n → Set
ChannelOutside {P = P} emb i =
  (k : 𝔽 (channelCount P)) → emb k ≢ i

ThreadOutside :
  {P : Proc 0} {m : ℕ} →
  (𝔽 (processCount P) → 𝔽 m) → 𝔽 m → Set
ThreadOutside {P = P} emb j =
  (k : 𝔽 (processCount P)) → emb k ≢ j

record SoupImage (P : Proc 0) {n m} (C : 𝐒.Config n m) : Set where
  field
    channelEmbedding : 𝔽 (channelCount P) → 𝔽 n
    channelEmbedding-injective : FinInjective channelEmbedding

    threadEmbedding : 𝔽 (processCount P) → 𝔽 m
    threadEmbedding-injective : FinInjective threadEmbedding

    endpointEmbedding : 𝔽 (2 *ℕ channelCount P) → 𝔽 (2 *ℕ n)
    endpoint-respects-channel :
      (i : 𝔽 (channelCount P)) (side : 𝔽 2) →
      endpointEmbedding (𝐒.endpoint i side) ≡
      𝐒.endpoint (channelEmbedding i) side

    live-channel :
      (i : 𝔽 (channelCount P)) →
      lookup (𝐒.channels C) (channelEmbedding i) ≡
      lookup (canonicalChannels P) i

    live-thread :
      (j : 𝔽 (processCount P)) →
      lookup (𝐒.threads C) (threadEmbedding j) ≡
      lookup (canonicalThreads P) j ⋯ᵣ endpointEmbedding

    garbage-channel :
      (i : 𝔽 n) →
      ChannelOutside {P = P} channelEmbedding i →
      lookup (𝐒.channels C) i ≡ (false , [] , [])

    garbage-thread :
      (j : 𝔽 m) →
      ThreadOutside {P = P} threadEmbedding j →
      lookup (𝐒.threads C) j ≡ K `unit

open SoupImage public

initialImage :
  (P : Proc 0) →
  SoupImage P (𝐒.config (canonicalChannels P) (canonicalThreads P))
initialImage P = record
  { channelEmbedding = id
  ; channelEmbedding-injective = λ eq → eq
  ; threadEmbedding = id
  ; threadEmbedding-injective = λ eq → eq
  ; endpointEmbedding = id
  ; endpoint-respects-channel = λ i side → refl
  ; live-channel = λ i → refl
  ; live-thread = λ j → sym (rename-id (lookup (canonicalThreads P) j))
  ; garbage-channel = λ i outside →
      ⊥-elim (outside i refl)
  ; garbage-thread = λ j outside →
      ⊥-elim (outside j refl)
  }
