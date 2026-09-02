-- | Phase 3, leaf rule `R-New` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   `E [ K (`new s) ·¹ * ]*` allocates a channel: the source reduct is a
--   restriction with binder groups `0 ∷ 1 ∷ []` on both sides, and the soup
--   takes an `RUS-New` step that inserts a fresh open channel at physical
--   index `0F`.  The thread namespace is unchanged, but every endpoint index
--   shifts along `insertEndpoint 0F`, so the frame travels along the
--   embedding `(suc , id , insertEndpoint 0F)`.
--
--   The new channel becomes the head of the logical channel vector, forward
--   oriented; `res-join` rebuilds the restriction over it once the body image
--   is available.  The body image's live thread is `newResult 0F F`, which
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
  {logicalChannels = []} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} Vsigma image
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
  { n′ = suc n
  ; m′ = m
  ; C′ = targetConfig
  ; step = soupStep
  ; embedding = emb
  ; logicalChannels′ = newChannel ∷ []
  ; image′ =
      ambient-resp (λ _ ambient → ambient) (λ _ ambient → ambient)
        toThread fromThread targetImage
  }
  where
  cs : Vec Soup.Channel n
  cs = Soup.channels C

  ts : Vec (Soup.Thread n) m
  ts = Soup.threads C

  -- The physical endpoint renaming induced by the allocation.
  rho : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
  rho = SoupReduction.insertEndpoint 0F

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
  targetChannels = V.insertAt cs 0F freshChannel

  targetThreads : Vec (Soup.Thread (suc n)) m
  targetThreads =
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints 0F) ts) j
      (SoupReduction.newResult 0F F)

  targetConfig : Soup.Config (suc n) m
  targetConfig = Soup.config targetChannels targetThreads

  soupStep : C SoupReduction.─→ₚ targetConfig
  soupStep =
    SoupReduction.RUS-New {s = s} {cs = cs} {ts = ts} j 0F F selected

  j-not-ambient : ¬ aT j
  j-not-ambient = thread-not-ambient image slotEq

  ----------------------------------------------------------------------
  -- The embedding: one channel is inserted at the front, the threads keep
  -- their slots but their endpoints shift.

  ambientThreadContent :
    (l : 𝔽 m) → aT l →
    lookup targetThreads l ≡ lookup ts l SoupTerm.⋯ᵣ rho
  ambientThreadContent l ambient =
    V.lookup∘updateAt′ l j
      (λ l≡j → j-not-ambient (subst aT l≡j ambient))
      (V.map (SoupReduction.insertThreadEndpoints 0F) ts)
    ■ V.lookup-map l (SoupReduction.insertThreadEndpoints 0F) ts

  emb : AmbientEmbedding aC aT C targetConfig
  emb = record
    { channelEmbedding = suc
    ; channelEmbedding-injective = Fin.suc-injective
    ; threadEmbedding = id
    ; threadEmbedding-injective = id
    ; endpointEmbedding = rho
    ; endpoint-respects-channel = insertEndpoint-endpoint 0F
    ; ambient-channel-content = λ i _ →
        V.insertAt-punchIn cs 0F freshChannel i
    ; ambient-thread-content = ambientThreadContent
    }

  toThread : (l : 𝔽 m) → aT l → Transport id aT l
  toThread l ambient = l , ambient , refl

  fromThread : (l : 𝔽 m) → Transport id aT l → aT l
  fromThread l (source , ambient , sourceEq) = subst aT sourceEq ambient

  ----------------------------------------------------------------------
  -- The bound channel of the reduct, and the environment of its body.

  newChannel : OrientedChannel (suc n)
  newChannel = 0F , forward

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
    SoupReduction.newResult 0F F ≡ Translation.T[ reduct ] env
  newResult-eq =
    sym
      (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E bindRen)
         {e = Source._⊗_ (Source.` 0F) (Source.` 1F)} Venv
       ■ Tᶠ*-plug-ren-coh E bindRen env outerEnv Venv VouterEnv envCoh
           (SoupTerm._⊗_ (env 0F) (env 1F))
       ■ Tᶠ*-plug-renEnv E Vsigma rho (SoupTerm._⊗_ (env 0F) (env 1F)))

  ----------------------------------------------------------------------
  -- The image of the body of the reduct.

  bodyImage :
    LocalImage (Typed.⟪ reduct ⟫) [] env
      (Transport suc aC ∪ᵖ singletonᵖ (physicalChannel newChannel))
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
               (V.map (SoupReduction.insertThreadEndpoints 0F) ts)
             ■ newResult-eq)
    ; garbage-channel = λ where
        zero outside notAmbient → ⊥-elim (notAmbient (inj₂ refl))
        (suc i₀) outside notAmbient →
          V.insertAt-punchIn cs 0F freshChannel i₀
          ■ garbage-channel image i₀ (λ ())
              (λ ambient → notAmbient (inj₁ (i₀ , ambient , refl)))
    ; garbage-thread = λ l outside notAmbient →
        V.lookup∘updateAt′ l j
          (λ l≡j → outside 0F (slotEq ■ cong just (sym l≡j)))
          (V.map (SoupReduction.insertThreadEndpoints 0F) ts)
        ■ V.lookup-map l (SoupReduction.insertThreadEndpoints 0F) ts
        ■ cong (SoupTerm._⋯ᵣ rho)
            (garbage-thread image l outside notAmbient)
    }

  channelContent :
    lookup targetChannels (physicalChannel newChannel) ≡
    bindChannel (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) newChannel
  channelContent = V.insertAt-lookup cs 0F freshChannel

  notAmbient : ¬ Transport suc aC (physicalChannel newChannel)
  notAmbient (source , ambient , ())

  targetImage :
    LocalImage
      (Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) (Typed.⟪ reduct ⟫))
      (newChannel ∷ []) outerEnv (Transport suc aC) aT targetConfig
  targetImage = res-join bodyImage channelContent notAmbient
