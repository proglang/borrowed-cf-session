-- | Phase 3, leaf rule `R-New` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   `E [ K (`new s) ·¹ * ]*` allocates a channel: the source reduct is a
--   restriction with binder groups `0 ∷ 1 ∷ []` on both sides, and the soup
--   takes an `RUS-New` step that inserts a fresh open channel at the chosen
--   physical index `i`.  The thread namespace is unchanged, but every endpoint
--   index shifts along `insertEndpoint i`, so the frame travels along the
--   embedding `(Fin.punchIn i , id , insertEndpoint i)`.
--
--   The new channel becomes the only logical channel of the reduct, forward
--   oriented; `res-join` rebuilds the restriction over it once the body image
--   is available.  The body image's live thread is `newResult i F`, which
--   `newResult-eq` identifies with the translation of the reduct in the
--   binder environment.
module BorrowedCF.Simulation.ForwardSoup.Local.New where

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
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind using (res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Extrusion
  using (weaken*-coherent)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (ambient-resp; bindEnv; bindChannel; _∪ᵖ_; singletonᵖ)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using (renameEnv)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (Tᶠ*-plug-ren-coh; Tᶠ*-plug-renEnv; bindEnv-Value; renameEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (Transport; AmbientEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

private
  -- The reduct owns exactly one channel, so its logical channel indices
  -- other than the head are vacuous — but at the *enlarged* physical size,
  -- so the source image's injectivity proof cannot be reused verbatim.
  vacuous : {A : Set} → 𝔽 0 → A
  vacuous ()

------------------------------------------------------------------------
-- `insertEndpoint` acts on endpoints by punching the channel index.

remQuot-endpoint :
  {n : ℕ} (i : 𝔽 n) (side : 𝔽 2) →
  Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) (Soup.endpoint i side)) ≡
  (i , side)
remQuot-endpoint {n} i side =
  cong (Fin.remQuot 2)
    (Fin.cast-involutive (Nat.*-comm 2 n) (Nat.*-comm n 2)
      (Fin.combine i side))
  ■ Fin.remQuot-combine i side

insertEndpoint-endpoint :
  {n : ℕ} (target : 𝔽 (suc n)) (i : 𝔽 n) (side : 𝔽 2) →
  SoupReduction.insertEndpoint target (Soup.endpoint i side) ≡
  Soup.endpoint (Fin.punchIn target i) side
insertEndpoint-endpoint target i side =
  cong
    (λ split →
      Soup.endpoint (Fin.punchIn target (proj₁ split)) (proj₂ split))
    (remQuot-endpoint i side)

------------------------------------------------------------------------
-- The leaf.

record NewStep
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {s : Types.𝕊 0}
  {logicalChannels : Vec (OrientedChannel n) 0}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image : LocalImage
    (Typed.⟪ SourceReduction._[_]* E
      (Source._·¹_ (Source.K (Source.`new s)) Source.*) ⟫)
    logicalChannels sigma ambientChannel ambientThread C) : Set where
  field
    newThread : 𝔽 m
    newSlotEq : threadEmbedding image zero ≡ just newThread
    newSourceFrame : SourceReduction.Frame* k
    newSourceFrame≡ : newSourceFrame ≡ E

    newFrame : SoupExpression.Frame* (2 *ℕ n)
    newSelectedSource :
      lookup (Soup.threads C) newThread ≡
      Translation.T[
        SourceReduction._[_]* E
          (Source._·¹_ (Source.K (Source.`new s)) Source.*)
      ] sigma
    newSelectedNew :
      lookup (Soup.threads C) newThread ≡
      SoupExpression._[_]* newFrame
        (SoupTerm._·¹_ (SoupTerm.K (Source.`new s)) SoupTerm.*)

    newIndex : 𝔽 (suc n)
    newEndpointRenaming : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
    newEndpointRenaming≡ :
      newEndpointRenaming ≡ SoupReduction.insertEndpoint newIndex

    newFreshChannel : Soup.Channel
    newFreshChannel≡ :
      newFreshChannel ≡ (true , Soup.acq ∷ [] , Soup.acq ∷ [])
    newTargetChannels : Vec Soup.Channel (suc n)
    newTargetChannels≡ :
      newTargetChannels ≡
      V.insertAt (Soup.channels C) newIndex newFreshChannel
    newTargetThreads : Vec (Soup.Thread (suc n)) m
    newTargetThreads≡ :
      newTargetThreads ≡
      SoupReduction.replaceAt
        (V.map (SoupReduction.insertThreadEndpoints newIndex)
          (Soup.threads C))
        newThread
        (SoupReduction.newResult newIndex newFrame)

    newConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config
          (V.insertAt (Soup.channels C) newIndex
            (true , Soup.acq ∷ [] , Soup.acq ∷ []))
          (SoupReduction.replaceAt
            (V.map (SoupReduction.insertThreadEndpoints newIndex)
              (Soup.threads C))
            newThread
            (SoupReduction.newResult newIndex newFrame)))

open NewStep public

new-step :
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {s : Types.𝕊 0}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  (i : 𝔽 (suc n)) →
  ValueEnv sigma →
  (image : LocalImage
    (Typed.⟪ SourceReduction._[_]* E
               (Source._·¹_ (Source.K (Source.`new s)) Source.*) ⟫)
    logicalChannels sigma ambientChannel ambientThread C) →
  NewStep {E = E} {s = s}
    (Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                 (Source._⊗_ (Source.` 0F) (Source.` 1F)) ⟫))
    sigma ambientChannel ambientThread C image
new-step {k = k} {n = n} {m = m} {E = E} {s = s}
  {logicalChannels = []} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} i Vsigma image
  with live-thread image 0F

-- An omitted redex thread would be `K `unit`, but the translation of a
-- plugged application never is.
... | omitted slotEq expectedEq =
  ⊥-elim
    (plug-not-K (Tᶠ*[ E ] {σ = sigma} Vsigma)
      (sym (T[_]-plugᶠ* E
              {e = Source._·¹_ (Source.K (Source.`new s)) Source.*} Vsigma)
       ■ expectedEq))

... | present j slotEq lookupEq = record
  { newThread = j
  ; newSlotEq = slotEq
  ; newSourceFrame = E
  ; newSourceFrame≡ = refl
  ; newFrame = F
  ; newSelectedSource = lookupEq
  ; newSelectedNew = selected
  ; newIndex = i
  ; newEndpointRenaming = rho
  ; newEndpointRenaming≡ = refl
  ; newFreshChannel = freshChannel
  ; newFreshChannel≡ = refl
  ; newTargetChannels = targetChannels
  ; newTargetChannels≡ = refl
  ; newTargetThreads = targetThreads
  ; newTargetThreads≡ = refl
  ; newConfigStep = record
      { config-step = soupStep
      ; config-embedding = emb
      ; config-logicalChannels′ = newChannel ∷ []
      ; config-image′ =
          ambient-resp (λ _ ambient → ambient) (λ _ ambient → ambient)
            toThread fromThread targetImage
      }
  }
  where
  cs : Vec Soup.Channel n
  cs = Soup.channels C

  ts : Vec (Soup.Thread n) m
  ts = Soup.threads C

  -- The physical endpoint renaming induced by the allocation.
  rho : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
  rho = SoupReduction.insertEndpoint i

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ E ] {σ = sigma} Vsigma

  selected :
    lookup ts j ≡
    SoupExpression._[_]* F
      (SoupTerm._·¹_ (SoupTerm.K (Source.`new s)) SoupTerm.*)
  selected =
    lookupEq
    ■ T[_]-plugᶠ* E
        {e = Source._·¹_ (Source.K (Source.`new s)) Source.*} Vsigma

  freshChannel : Soup.Channel
  freshChannel = true , Soup.acq ∷ [] , Soup.acq ∷ []

  targetChannels : Vec Soup.Channel (suc n)
  targetChannels = V.insertAt cs i freshChannel

  targetThreads : Vec (Soup.Thread (suc n)) m
  targetThreads =
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints i) ts) j
      (SoupReduction.newResult i F)

  targetConfig : Soup.Config (suc n) m
  targetConfig = Soup.config targetChannels targetThreads

  soupStep : C SoupReduction.─→ₚ targetConfig
  soupStep =
    SoupReduction.RUS-New {s = s} {cs = cs} {ts = ts} j i F selected

  j-not-ambient : ¬ aT j
  j-not-ambient = thread-not-ambient image slotEq

  ----------------------------------------------------------------------
  -- The embedding: one channel is inserted, the threads keep
  -- their slots but their endpoints shift.

  ambientThreadContent :
    (l : 𝔽 m) → aT l →
    lookup targetThreads l ≡ lookup ts l SoupTerm.⋯ᵣ rho
  ambientThreadContent l ambient =
    V.lookup∘updateAt′ l j
      (λ l≡j → j-not-ambient (subst aT l≡j ambient))
      (V.map (SoupReduction.insertThreadEndpoints i) ts)
    ■ V.lookup-map l (SoupReduction.insertThreadEndpoints i) ts

  emb : AmbientEmbedding aC aT C targetConfig
  emb = record
    { channelEmbedding = Fin.punchIn i
    ; channelEmbedding-injective = λ {i₁} {i₂} eq →
        Fin.punchIn-injective i i₁ i₂ eq
    ; threadEmbedding = id
    ; threadEmbedding-injective = id
    ; endpointEmbedding = rho
    ; endpoint-respects-channel = insertEndpoint-endpoint i
    ; ambient-channel-content = λ i₀ _ →
        V.insertAt-punchIn cs i freshChannel i₀
    ; ambient-thread-content = ambientThreadContent
    }

  toThread : (l : 𝔽 m) → aT l → Transport id aT l
  toThread l ambient = l , ambient , refl

  fromThread : (l : 𝔽 m) → Transport id aT l → aT l
  fromThread l (source , ambient , sourceEq) = subst aT sourceEq ambient

  ----------------------------------------------------------------------
  -- The bound channel of the reduct, and the environment of its body.

  newChannel : OrientedChannel (suc n)
  newChannel = i , forward

  bindRen : 𝔽 k → 𝔽 (2 + k)
  bindRen = Source.weaken* ⦃ Source.Kᵣ ⦄ 2

  outerEnv : Translation.Env k (2 *ℕ suc n)
  outerEnv = renameEnv rho sigma

  VouterEnv : ValueEnv outerEnv
  VouterEnv = renameEnv-Value rho Vsigma

  env : Translation.Env (2 + k) (2 *ℕ suc n)
  env = bindEnv (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) newChannel outerEnv

  Venv : ValueEnv env
  Venv =
    bindEnv-Value {B₁ = 0 ∷ 1 ∷ []} {B₂ = 0 ∷ 1 ∷ []} {channel = newChannel}
      VouterEnv

  binderEnv : Translation.Env 2 (2 *ℕ suc n)
  binderEnv =
    proj₁ (Translation.UB[ 0 ∷ 1 ∷ [] ] (physicalEndpoint newChannel 0F)
            (SoupTerm.* , physicalEndpoint newChannel 0F , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ 0 ∷ 1 ∷ [] ] (physicalEndpoint newChannel 1F)
            (SoupTerm.* , physicalEndpoint newChannel 1F , SoupTerm.*))

  envCoh : (x : 𝔽 k) → env (bindRen x) ≡ outerEnv x
  envCoh = weaken*-coherent binderEnv outerEnv

  ----------------------------------------------------------------------
  -- The soup rule produces `newResult`; the image expects the translation
  -- of the reduct in the binder environment.  The two coincide because the
  -- two endpoint variables translate to the two channel triples.

  reduct : Source.Tm (2 + k)
  reduct =
    SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E bindRen)
      (Source._⊗_ (Source.` 0F) (Source.` 1F))

  newResult-eq :
    SoupReduction.newResult i F ≡ Translation.T[ reduct ] env
  newResult-eq =
    sym
      (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E bindRen)
         {e = Source._⊗_ (Source.` 0F) (Source.` 1F)} Venv
       ■ Tᶠ*-plug-ren-coh E bindRen env outerEnv Venv VouterEnv envCoh
           (SoupTerm._⊗_ (env 0F) (env 1F))
       ■ Tᶠ*-plug-renEnv E Vsigma rho (SoupTerm._⊗_ (env 0F) (env 1F)))

  ----------------------------------------------------------------------
  -- The image of the body of the reduct.

  targetGarbageChannel :
    (i′ : 𝔽 (suc n)) →
    LocalOutside (physicalChannel ∘ lookup []) i′ →
    ¬ (Transport (Fin.punchIn i) aC ∪ᵖ singletonᵖ (physicalChannel newChannel)) i′ →
    lookup targetChannels i′ ≡ (false , [] , [])
  targetGarbageChannel i′ outside notAmbient with i Fin.≟ i′
  ... | yes refl = ⊥-elim (notAmbient (inj₂ refl))
  ... | no i≢i′ =
    cong (lookup targetChannels) (sym punchEq)
    ■ V.insertAt-punchIn cs i freshChannel i₀
    ■ garbage-channel image i₀ (λ ())
        (λ ambient → notAmbient (inj₁ (i₀ , ambient , punchEq)))
    where
    i₀ : 𝔽 n
    i₀ = Fin.punchOut i≢i′

    punchEq : Fin.punchIn i i₀ ≡ i′
    punchEq = Fin.punchIn-punchOut i≢i′

  bodyImage :
    LocalImage (Typed.⟪ reduct ⟫) [] env
      (Transport (Fin.punchIn i) aC ∪ᵖ singletonᵖ (physicalChannel newChannel))
      aT targetConfig
  bodyImage = record
    { channelEmbedding-injective = λ {i} _ → vacuous i
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; channel-not-ambient = λ ()
    ; thread-not-ambient = thread-not-ambient image
    ; live-channel = λ ()
    ; live-thread = λ where
        0F →
          present j slotEq
            (V.lookup∘updateAt j
               (V.map (SoupReduction.insertThreadEndpoints i) ts)
             ■ newResult-eq)
    ; garbage-channel = targetGarbageChannel
    ; garbage-thread = λ l outside notAmbient →
        V.lookup∘updateAt′ l j
          (λ l≡j → outside 0F (slotEq ■ cong just (sym l≡j)))
          (V.map (SoupReduction.insertThreadEndpoints i) ts)
        ■ V.lookup-map l (SoupReduction.insertThreadEndpoints i) ts
        ■ cong (SoupTerm._⋯ᵣ rho)
            (garbage-thread image l outside notAmbient)
    }

  channelContent :
    lookup targetChannels (physicalChannel newChannel) ≡
    bindChannel (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) newChannel
  channelContent = V.insertAt-lookup cs i freshChannel

  notAmbient : ¬ Transport (Fin.punchIn i) aC (physicalChannel newChannel)
  notAmbient (source , ambient , sourceEq) =
    Fin.punchInᵢ≢i i source sourceEq

  targetImage :
    LocalImage
      (Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) (Typed.⟪ reduct ⟫))
      (newChannel ∷ []) outerEnv (Transport (Fin.punchIn i) aC) aT targetConfig
  targetImage = res-join bodyImage channelContent notAmbient

U-new-local :
  {k n m : ℕ}
  {E : SourceReduction.Frame* k} {s : Types.𝕊 0}
  {logicalChannels : Vec (OrientedChannel n) 0}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  LocalImage
    (Typed.⟪ SourceReduction._[_]* E
               (Source._·¹_ (Source.K (Source.`new s)) Source.*) ⟫)
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                 (Source._⊗_ (Source.` 0F) (Source.` 1F)) ⟫))
    sigma ambientChannel ambientThread C
U-new-local {k = k} {n = n} {m = m} {E = E} {s = s}
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma image =
  configStep⇒localStep
    (newConfigStep
      (new-step {k = k} {n = n} {m = m} {E = E} {s = s}
        {logicalChannels = logicalChannels} {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} 0F Vsigma image))
