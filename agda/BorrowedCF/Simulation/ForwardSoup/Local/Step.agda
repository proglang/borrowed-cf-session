-- | Phase 3 scaffolding for the local simulation (`ForwardSoup/PLAN.md`, §3,
--   §6.2 and the Phase 3 paragraph of §6.3).
--
--   `LocalStep` packages one soup step together with the ambient embedding
--   that carries the frame across it.  The rest of this module is the
--   infrastructure shared by the eleven leaf rules:
--
--     * `embedding-mono`, for shrinking the ambient sets of an embedding;
--     * `identity-embedding`/`identity-step`, for the rules that neither
--       create nor destroy channels or threads;
--     * the orientation kit, which lets a leaf rule work at
--       `orientSide o side` instead of a fixed polarity;
--     * `K-irreducible`/`plug-not-K`, the two irreducibility facts that refute
--       the `omitted` case of `live-thread` for a redex thread.
module BorrowedCF.Simulation.ForwardSoup.Local.Step where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (ambient-resp; env-resp)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using (renameEnv)
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (Transport; AmbientEmbedding; targetAmbientChannel; targetAmbientThread)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- One simulated step, with the frame carried across it.

record LocalStep
  {k n m : ℕ}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    n′ m′ : ℕ
    C′ : Soup.Config n′ m′
    step : C SoupReduction.─→ₚ C′
    embedding : AmbientEmbedding ambientChannel ambientThread C C′
    logicalChannels′ :
      Vec (OrientedChannel n′) (Translation.channelCount P′)
    image′ :
      LocalImage P′ logicalChannels′
        (renameEnv (AmbientEmbedding.endpointEmbedding embedding) sigma)
        (targetAmbientChannel embedding)
        (targetAmbientThread embedding)
        C′

open LocalStep public

record ConfigStep
  {k n m n′ m′ : ℕ}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (C′ : Soup.Config n′ m′) : Set where
  field
    config-step : C SoupReduction.─→ₚ C′
    config-embedding : AmbientEmbedding ambientChannel ambientThread C C′
    config-logicalChannels′ :
      Vec (OrientedChannel n′) (Translation.channelCount P′)
    config-image′ :
      LocalImage P′ config-logicalChannels′
        (renameEnv (AmbientEmbedding.endpointEmbedding config-embedding) sigma)
        (targetAmbientChannel config-embedding)
        (targetAmbientThread config-embedding)
        C′

open ConfigStep public

configStep⇒localStep :
  {k n m n′ m′ : ℕ} {P′ : Typed.Proc k}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  ConfigStep P′ sigma ambientChannel ambientThread C C′ →
  LocalStep P′ sigma ambientChannel ambientThread C
configStep⇒localStep {n′ = n′} {m′ = m′} {C′ = C′} step′ = record
  { n′ = n′
  ; m′ = m′
  ; C′ = C′
  ; step = config-step step′
  ; embedding = config-embedding step′
  ; logicalChannels′ = config-logicalChannels′ step′
  ; image′ = config-image′ step′
  }

------------------------------------------------------------------------
-- Shrinking the ambient sets of an embedding.  Only the two content
-- obligations mention them, so restricting the sets keeps every map — and
-- hence `targetAmbientChannel`/`targetAmbientThread` stay the transports of
-- the *same* maps.

embedding-mono :
  {n m n′ m′ : ℕ}
  {ambientChannel ambientChannel₁ : 𝔽 n → Set}
  {ambientThread ambientThread₁ : 𝔽 m → Set}
  {C : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  ((i : 𝔽 n) → ambientChannel i → ambientChannel₁ i) →
  ((l : 𝔽 m) → ambientThread l → ambientThread₁ l) →
  AmbientEmbedding ambientChannel₁ ambientThread₁ C C′ →
  AmbientEmbedding ambientChannel ambientThread C C′
embedding-mono monoChannel monoThread embedding = record
  { channelEmbedding =
      AmbientEmbedding.channelEmbedding embedding
  ; channelEmbedding-injective =
      AmbientEmbedding.channelEmbedding-injective embedding
  ; threadEmbedding =
      AmbientEmbedding.threadEmbedding embedding
  ; threadEmbedding-injective =
      AmbientEmbedding.threadEmbedding-injective embedding
  ; endpointEmbedding =
      AmbientEmbedding.endpointEmbedding embedding
  ; endpoint-respects-channel =
      AmbientEmbedding.endpoint-respects-channel embedding
  ; ambient-channel-content = λ i ambient →
      AmbientEmbedding.ambient-channel-content embedding i (monoChannel i ambient)
  ; ambient-thread-content = λ j ambient →
      AmbientEmbedding.ambient-thread-content embedding j (monoThread j ambient)
  }

------------------------------------------------------------------------
-- The identity renaming on soup terms.  `AmbientEmbedding` states its thread
-- obligation up to the endpoint renaming, so every rule that keeps the
-- physical namespace needs this law.

ren-id :
  {n : ℕ} (t : SoupTerm.Tm n) {rho : 𝔽 n → 𝔽 n} →
  ((x : 𝔽 n) → rho x ≡ x) →
  t SoupTerm.⋯ᵣ rho ≡ t
ren-id (SoupTerm.` x) eq = cong (λ y → SoupTerm.` y) (eq x)
ren-id (SoupTerm.`phi r) eq =
  cong SoupTerm.`phi (cong (λ y → y , proj₂ r) (eq (proj₁ r)))
ren-id (SoupTerm.K c) eq = refl
ren-id (SoupTerm.ƛ t) eq =
  cong SoupTerm.ƛ (ren-id t λ where zero → refl; (suc x) → cong suc (eq x))
ren-id (SoupTerm.μ t) eq =
  cong SoupTerm.μ (ren-id t λ where zero → refl; (suc x) → cong suc (eq x))
ren-id (t₁ SoupTerm.·⟨ d ⟩ t₂) eq =
  cong₂ (SoupTerm._·⟨ d ⟩_) (ren-id t₁ eq) (ren-id t₂ eq)
ren-id (t₁ SoupTerm.; t₂) eq =
  cong₂ SoupTerm._;_ (ren-id t₁ eq) (ren-id t₂ eq)
ren-id (t₁ SoupTerm.⊗ t₂) eq =
  cong₂ SoupTerm._⊗_ (ren-id t₁ eq) (ren-id t₂ eq)
ren-id (SoupTerm.`let t₁ `in t₂) eq =
  cong₂ SoupTerm.`let_`in_ (ren-id t₁ eq)
    (ren-id t₂ λ where zero → refl; (suc x) → cong suc (eq x))
ren-id (SoupTerm.`let⊗ t₁ `in t₂) eq =
  cong₂ SoupTerm.`let⊗_`in_ (ren-id t₁ eq)
    (ren-id t₂ λ where
      zero → refl
      (suc zero) → refl
      (suc (suc x)) → cong suc (cong suc (eq x)))
ren-id (SoupTerm.`inj side t) eq = cong (SoupTerm.`inj side) (ren-id t eq)
ren-id (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) eq =
  cong₂ (λ head branches →
          SoupTerm.`case head `of⟨ proj₁ branches ; proj₂ branches ⟩)
    (ren-id t eq)
    (cong₂ _,_
      (ren-id t₁ λ where zero → refl; (suc x) → cong suc (eq x))
      (ren-id t₂ λ where zero → refl; (suc x) → cong suc (eq x)))

------------------------------------------------------------------------
-- The identity embedding, for the rules that keep both counts.

identity-embedding :
  {n m : ℕ}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C C′ : Soup.Config n m} →
  ((i : 𝔽 n) → ambientChannel i →
    lookup (Soup.channels C′) i ≡ lookup (Soup.channels C) i) →
  ((j : 𝔽 m) → ambientThread j →
    lookup (Soup.threads C′) j ≡ lookup (Soup.threads C) j) →
  AmbientEmbedding ambientChannel ambientThread C C′
identity-embedding {C = C} channelContent threadContent = record
  { channelEmbedding = id
  ; channelEmbedding-injective = id
  ; threadEmbedding = id
  ; threadEmbedding-injective = id
  ; endpointEmbedding = id
  ; endpoint-respects-channel = λ _ _ → refl
  ; ambient-channel-content = channelContent
  ; ambient-thread-content = λ j ambient →
      threadContent j ambient
      ■ sym (ren-id (lookup (Soup.threads C) j) (λ _ → refl))
  }

------------------------------------------------------------------------
-- One step that keeps the physical namespace: the embedding is the identity,
-- so the image of the reduct only has to be adjusted along the (definitional)
-- identity renaming of the environment and the ambient predicates.

identity-config-step :
  {k n m : ℕ} {P′ : Typed.Proc k}
  {logicalChannels′ :
    Vec (OrientedChannel n) (Translation.channelCount P′)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C C′ : Soup.Config n m} →
  C SoupReduction.─→ₚ C′ →
  ((i : 𝔽 n) → ambientChannel i →
    lookup (Soup.channels C′) i ≡ lookup (Soup.channels C) i) →
  ((j : 𝔽 m) → ambientThread j →
    lookup (Soup.threads C′) j ≡ lookup (Soup.threads C) j) →
  LocalImage P′ logicalChannels′ sigma ambientChannel ambientThread C′ →
  ConfigStep P′ sigma ambientChannel ambientThread C C′
identity-config-step {n = n} {m = m} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread}
  {C′ = C′} step channelContent threadContent image = record
  { config-step = step
  ; config-embedding = identity-embedding channelContent threadContent
  ; config-logicalChannels′ = _
  ; config-image′ =
      ambient-resp toChannel fromChannel toThread fromThread
        (env-resp (λ x → sym (ren-id (sigma x) (λ _ → refl))) image)
  }
  where
  toChannel : (i : 𝔽 n) → ambientChannel i → Transport id ambientChannel i
  toChannel i ambient = i , ambient , refl

  fromChannel : (i : 𝔽 n) → Transport id ambientChannel i → ambientChannel i
  fromChannel i (source , ambient , sourceEq) =
    subst ambientChannel sourceEq ambient

  toThread : (l : 𝔽 m) → ambientThread l → Transport id ambientThread l
  toThread l ambient = l , ambient , refl

  fromThread : (l : 𝔽 m) → Transport id ambientThread l → ambientThread l
  fromThread l (source , ambient , sourceEq) =
    subst ambientThread sourceEq ambient

identity-step :
  {k n m : ℕ} {P′ : Typed.Proc k}
  {logicalChannels′ :
    Vec (OrientedChannel n) (Translation.channelCount P′)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C C′ : Soup.Config n m} →
  C SoupReduction.─→ₚ C′ →
  ((i : 𝔽 n) → ambientChannel i →
    lookup (Soup.channels C′) i ≡ lookup (Soup.channels C) i) →
  ((j : 𝔽 m) → ambientThread j →
    lookup (Soup.threads C′) j ≡ lookup (Soup.threads C) j) →
  LocalImage P′ logicalChannels′ sigma ambientChannel ambientThread C′ →
  LocalStep P′ sigma ambientChannel ambientThread C
identity-step step channelContent threadContent image =
  configStep⇒localStep
    (identity-config-step step channelContent threadContent image)

------------------------------------------------------------------------
-- Moving an image to a configuration that agrees with the old one away from
-- the frame.  An image only ever inspects non-ambient positions: the ones it
-- owns — which `channel-not-ambient`/`thread-not-ambient` place outside the
-- ambient sets — and the garbage ones, which are non-ambient by the
-- hypothesis of the garbage clauses.  So the *ambient* positions are exactly
-- the ones an image never looks at, and two configurations agreeing outside
-- them carry the same images.
--
-- This is what a leaf rule needs for the sibling processes it does not touch:
-- the rule rewrites some threads, all of which are ambient for the sibling's
-- image, so the sibling's image survives unchanged.

private
  thread-image-transfer :
    {n m : ℕ} {threads threads′ : Vec (Soup.Thread n) m}
    {slot : Maybe (𝔽 m)} {expected : Soup.Thread n} →
    ((l : 𝔽 m) → slot ≡ just l → lookup threads′ l ≡ lookup threads l) →
    OptionalThreadImage {n = n} threads slot expected →
    OptionalThreadImage {n = n} threads′ slot expected
  thread-image-transfer content (present l slotEq lookupEq) =
    present l slotEq (content l slotEq ■ lookupEq)
  thread-image-transfer content (omitted slotEq expectedEq) =
    omitted slotEq expectedEq

config-resp :
  {k n m : ℕ} {P : Typed.Proc k}
  {logicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C C′ : Soup.Config n m} →
  ((i : 𝔽 n) → ¬ ambientChannel i →
    lookup (Soup.channels C′) i ≡ lookup (Soup.channels C) i) →
  ((l : 𝔽 m) → ¬ ambientThread l →
    lookup (Soup.threads C′) l ≡ lookup (Soup.threads C) l) →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C′
config-resp {logicalChannels = logicalChannels} channelContent threadContent
  image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image
  ; threadEmbedding-injective = threadEmbedding-injective image
  ; channel-not-ambient = channel-not-ambient image
  ; thread-not-ambient = thread-not-ambient image
  ; live-channel = λ i →
      channelContent (physicalChannel (lookup logicalChannels i))
        (channel-not-ambient image i)
      ■ live-channel image i
  ; live-thread = λ j →
      thread-image-transfer
        (λ l slotEq → threadContent l (thread-not-ambient image slotEq))
        (live-thread image j)
  ; garbage-channel = λ i outside notAmbient →
      channelContent i notAmbient ■ garbage-channel image i outside notAmbient
  ; garbage-thread = λ l outside notAmbient →
      threadContent l notAmbient ■ garbage-thread image l outside notAmbient
  }

------------------------------------------------------------------------
-- Orientation kit.  A leaf rule sees the logical side `side` of an oriented
-- channel; the soup rule fires at the physical side `orientSide o side`.

orientSide-opposite :
  (orientation : Orientation) →
  SoupReduction.Opposite
    (orientSide orientation zero) (orientSide orientation (suc zero))
orientSide-opposite forward = SoupReduction.left-right
orientSide-opposite reverse = SoupReduction.right-left

open-orient :
  (orientation : Orientation) (channel : Soup.Channel) →
  proj₁ (orientChannel orientation channel) ≡ proj₁ channel
open-orient forward channel = refl
open-orient reverse (open? , leftFlags , rightFlags) = refl

endpointFlags-orient :
  (orientation : Orientation) (channel : Soup.Channel) (side : 𝔽 2) →
  SoupReduction.endpointFlags
    (orientChannel orientation channel) (orientSide orientation side) ≡
  SoupReduction.endpointFlags channel side
endpointFlags-orient forward channel side = refl
endpointFlags-orient reverse (open? , leftFlags , rightFlags) zero = refl
endpointFlags-orient reverse (open? , leftFlags , rightFlags) (suc zero) = refl

setEndpointFlags-orient :
  (orientation : Orientation) (channel : Soup.Channel) (side : 𝔽 2)
  (flags : List Soup.Flag) →
  SoupReduction.setEndpointFlags (orientSide orientation side) flags
    (orientChannel orientation channel) ≡
  orientChannel orientation
    (SoupReduction.setEndpointFlags side flags channel)
setEndpointFlags-orient forward channel side flags = refl
setEndpointFlags-orient reverse (open? , leftFlags , rightFlags) zero flags =
  refl
setEndpointFlags-orient reverse (open? , leftFlags , rightFlags)
  (suc zero) flags = refl

appendEndpointFlag-orient :
  (orientation : Orientation) (channel : Soup.Channel) (side : 𝔽 2)
  (flag : Soup.Flag) →
  SoupReduction.appendEndpointFlag (orientSide orientation side) flag
    (orientChannel orientation channel) ≡
  orientChannel orientation
    (SoupReduction.appendEndpointFlag side flag channel)
appendEndpointFlag-orient forward channel side flag = refl
appendEndpointFlag-orient reverse (open? , leftFlags , rightFlags) zero flag =
  refl
appendEndpointFlag-orient reverse (open? , leftFlags , rightFlags)
  (suc zero) flag = refl

------------------------------------------------------------------------
-- Redex threads are present: a constant never steps, and a plugged
-- application is never a constant.  Both refute the `omitted` case of
-- `live-thread` for the thread carrying the redex.

frame-not-K :
  {n : ℕ} (F : SoupExpression.Frame n)
  {t : SoupTerm.Tm n} {c : SoupTerm.Const} →
  F SoupExpression.[ t ] ≢ SoupTerm.K c
frame-not-K (SoupExpression.app₁ _ _ _) ()
frame-not-K (SoupExpression.app₂ _ _ _) ()
frame-not-K (SoupExpression.□⊗ _) ()
frame-not-K (_ SoupExpression.⊗□) ()
frame-not-K (SoupExpression.□; _) ()
frame-not-K (SoupExpression.`let-`in _) ()
frame-not-K (SoupExpression.`let⊗-`in _) ()
frame-not-K (SoupExpression.`inj□ _) ()
frame-not-K SoupExpression.`case□`of⟨ _ ; _ ⟩ ()

K-head-irreducible :
  {n : ℕ} {c : SoupTerm.Const} {t : SoupTerm.Tm n} →
  ¬ (SoupTerm.K c SoupExpression.─→ t)
K-head-irreducible ()

private
  no-K-step :
    {n : ℕ} {t t′ : SoupTerm.Tm n} {c : SoupTerm.Const} →
    t SoupExpression.⋯→ t′ → t ≡ SoupTerm.K c → ⊥
  no-K-step (SoupExpression.E-□ red) refl = K-head-irreducible red
  no-K-step (SoupExpression.E-Ctx F red) eq = frame-not-K F eq

K-irreducible :
  {n : ℕ} {c : SoupTerm.Const} {t : SoupTerm.Tm n} →
  ¬ (SoupTerm.K c SoupExpression.⋯→ t)
K-irreducible red = no-K-step red refl

plug-not-K :
  {n : ℕ} (F : SoupExpression.Frame* n) →
  {t₁ t₂ : SoupTerm.Tm n} {d : _} {c : SoupTerm.Const} →
  F SoupExpression.[ t₁ SoupTerm.·⟨ d ⟩ t₂ ]* ≢ SoupTerm.K c
plug-not-K [] ()
plug-not-K (F ∷ Fs) eq = frame-not-K F eq
