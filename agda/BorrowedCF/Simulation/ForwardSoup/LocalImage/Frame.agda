module BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (T[_]-Env-cong)

open Nat.Variables
open Fin.Patterns

private variable
  a b : ℕ

------------------------------------------------------------------------
-- Predicate algebra for ambient (frame) resources.

infixr 6 _∪ᵖ_

_∪ᵖ_ : (𝔽 a → Set) → (𝔽 a → Set) → 𝔽 a → Set
(p ∪ᵖ q) i = p i ⊎ q i

singletonᵖ : 𝔽 a → 𝔽 a → Set
singletonᵖ i j = i ≡ j

ownedChannels : {n k : ℕ} → Vec (OrientedChannel n) k → 𝔽 n → Set
ownedChannels {k = k} logicalChannels i =
  Σ[ j ∈ 𝔽 k ] physicalChannel (lookup logicalChannels j) ≡ i

ownedThreads : {k m : ℕ} → (𝔽 k → Maybe (𝔽 m)) → 𝔽 m → Set
ownedThreads {k = k} threadEmb l = Σ[ j ∈ 𝔽 k ] threadEmb j ≡ just l

------------------------------------------------------------------------
-- Pointwise-equivalent ambient predicates.

ambient-resp :
  {P : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel ambientChannel′ : 𝔽 n → Set}
  {ambientThread ambientThread′ : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ((i : 𝔽 n) → ambientChannel i → ambientChannel′ i) →
  ((i : 𝔽 n) → ambientChannel′ i → ambientChannel i) →
  ((l : 𝔽 m) → ambientThread l → ambientThread′ l) →
  ((l : 𝔽 m) → ambientThread′ l → ambientThread l) →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C →
  LocalImage P logicalChannels sigma ambientChannel′ ambientThread′ C
ambient-resp toChannel fromChannel toThread fromThread image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image
  ; threadEmbedding-injective = threadEmbedding-injective image
  ; channel-not-ambient = λ i ambient →
      channel-not-ambient image i (fromChannel _ ambient)
  ; thread-not-ambient = λ {_} {l} slotEq ambient →
      thread-not-ambient image slotEq (fromThread l ambient)
  ; live-channel = live-channel image
  ; live-thread = live-thread image
  ; garbage-channel = λ i outside notAmbient →
      garbage-channel image i outside (λ ambient → notAmbient (toChannel i ambient))
  ; garbage-thread = λ j outside notAmbient →
      garbage-thread image j outside (λ ambient → notAmbient (toThread j ambient))
  }

------------------------------------------------------------------------
-- Pointwise-equal environments.

private
  appendEnv-point-cong :
    {left₁ : Translation.Env a n} {left₂ : Translation.Env a n}
    {right₁ : Translation.Env b n} {right₂ : Translation.Env b n} →
    ((i : 𝔽 a) → left₁ i ≡ left₂ i) →
    ((i : 𝔽 b) → right₁ i ≡ right₂ i) →
    (i : 𝔽 (a + b)) →
    (left₁ Translation.++ₛ right₁) i ≡
    (left₂ Translation.++ₛ right₂) i
  appendEnv-point-cong {a = a} leftEq rightEq i with Fin.splitAt a i
  ... | inj₁ x = leftEq x
  ... | inj₂ x = rightEq x

  thread-image-cong :
    {threads : Vec (Soup.Thread n) m} {slot : Maybe (𝔽 m)}
    {expected expected′ : Soup.Thread n} →
    expected ≡ expected′ →
    OptionalThreadImage {n = n} threads slot expected →
    OptionalThreadImage {n = n} threads slot expected′
  thread-image-cong refl image = image

flattenOriented-env-cong :
  (P : Typed.Proc k)
  (logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P))
  {sigma sigma′ : Translation.Env k (2 *ℕ n)} →
  ((x : 𝔽 k) → sigma x ≡ sigma′ x) →
  flattenOriented P logicalChannels sigma ≡
  flattenOriented P logicalChannels sigma′
flattenOriented-env-cong (Typed.⟪ e ⟫) [] envEq =
  cong (λ term → [] , term ∷ []) (T[ e ]-Env-cong envEq)
flattenOriented-env-cong (P Typed.∥ Q) channels envEq
  rewrite flattenOriented-env-cong P
            (V.take (Translation.channelCount P) channels) envEq
        | flattenOriented-env-cong Q
            (V.drop (Translation.channelCount P) channels) envEq
  = refl
flattenOriented-env-cong (Typed.ν B₁ B₂ P) (channel ∷ channels) envEq
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  cong
    (λ result →
      orientChannel (proj₂ channel) (true , flags₁ , flags₂) ∷ proj₁ result ,
      proj₂ result)
    (flattenOriented-env-cong P channels
      (appendEnv-point-cong (λ _ → refl) envEq))

env-resp :
  {P : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma sigma′ : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ((x : 𝔽 k) → sigma x ≡ sigma′ x) →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C →
  LocalImage P logicalChannels sigma′ ambientChannel ambientThread C
env-resp {P = P} {logicalChannels = logicalChannels} envEq image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image
  ; threadEmbedding-injective = threadEmbedding-injective image
  ; channel-not-ambient = channel-not-ambient image
  ; thread-not-ambient = thread-not-ambient image
  ; live-channel = λ i →
      live-channel image i ■
      cong (λ result → lookup (proj₁ result) i)
        (flattenOriented-env-cong P logicalChannels envEq)
  ; live-thread = λ j →
      thread-image-cong
        (cong (λ result → lookup (proj₂ result) j)
          (flattenOriented-env-cong P logicalChannels envEq))
        (live-thread image j)
  ; garbage-channel = garbage-channel image
  ; garbage-thread = garbage-thread image
  }

------------------------------------------------------------------------
-- Binder frames.

bindEnv :
  (B₁ B₂ : Typed.BindGroup) → OrientedChannel n →
  Translation.Env k (2 *ℕ n) →
  Translation.Env (sum B₁ + sum B₂ + k) (2 *ℕ n)
bindEnv B₁ B₂ channel sigma =
  (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel zero)
            (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*))
     Translation.++ₛ
   proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
            (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)))
  Translation.++ₛ sigma

bindChannel :
  (B₁ B₂ : Typed.BindGroup) → OrientedChannel n → Soup.Channel
bindChannel B₁ B₂ channel =
  orientChannel (proj₂ channel)
    ( true
    , proj₂ (Translation.UB[ B₁ ] (physicalEndpoint channel zero)
               (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*))
    , proj₂ (Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
               (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*))
    )

flatten-bind :
  (B₁ B₂ : Typed.BindGroup)
  (P : Typed.Proc (sum B₁ + sum B₂ + k))
  (channel : OrientedChannel n)
  (logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P))
  (sigma : Translation.Env k (2 *ℕ n)) →
  flattenOriented (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma ≡
  ( bindChannel B₁ B₂ channel ∷
      proj₁ (flattenOriented P logicalChannels
              (bindEnv B₁ B₂ channel sigma))
  , proj₂ (flattenOriented P logicalChannels
            (bindEnv B₁ B₂ channel sigma))
  )
flatten-bind B₁ B₂ P channel logicalChannels sigma = refl

flatten-bind-channel :
  {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + k)}
  {channel : OrientedChannel n}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)} →
  lookup
    (proj₁ (flattenOriented (Typed.ν B₁ B₂ P)
             (channel ∷ logicalChannels) sigma))
    zero ≡
  bindChannel B₁ B₂ channel
flatten-bind-channel {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
  {logicalChannels = logicalChannels} {sigma = sigma} =
  cong (λ result → lookup (proj₁ result) zero)
    (flatten-bind B₁ B₂ P channel logicalChannels sigma)

flatten-bind-channel-suc :
  {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + k)}
  {channel : OrientedChannel n}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)} →
  (i : 𝔽 (Translation.channelCount P)) →
  lookup
    (proj₁ (flattenOriented (Typed.ν B₁ B₂ P)
             (channel ∷ logicalChannels) sigma))
    (suc i) ≡
  lookup
    (proj₁ (flattenOriented P logicalChannels
             (bindEnv B₁ B₂ channel sigma)))
    i
flatten-bind-channel-suc {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
  {logicalChannels = logicalChannels} {sigma = sigma} i =
  cong (λ result → lookup (proj₁ result) (suc i))
    (flatten-bind B₁ B₂ P channel logicalChannels sigma)

flatten-bind-thread :
  {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + k)}
  {channel : OrientedChannel n}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)} →
  (j : 𝔽 (Translation.processCount P)) →
  lookup
    (proj₂ (flattenOriented (Typed.ν B₁ B₂ P)
             (channel ∷ logicalChannels) sigma))
    j ≡
  lookup
    (proj₂ (flattenOriented P logicalChannels
             (bindEnv B₁ B₂ channel sigma)))
    j
flatten-bind-thread {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
  {logicalChannels = logicalChannels} {sigma = sigma} j =
  cong (λ result → lookup (proj₂ result) j)
    (flatten-bind B₁ B₂ P channel logicalChannels sigma)
