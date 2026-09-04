-- | Phase 3, leaf rule `R-RSplit` (`ForwardSoup/PLAN.md`, §4, Phase 3,
--   item 4, and §6.4 option 1).
--
--     ν (B₁ ++ (q + suc b₁) ∷ B₂) B
--       (⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
--       ─→ₚ
--     ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
--       (⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj …) ⊗ (` 𝐒.inj …) ]* ⟫ ∥ (P ⋯ₚ 𝐒.rwk))
--
--   Unlike `R-LSplit` the split block is *cut in two*, so a new sync boundary
--   appears at flag position `length B₁` of the split endpoint: every φ-cell
--   of that endpoint at slot `length B₁` or above moves up by one, in every
--   thread of the soup.  That is exactly `RUS-RSplit`'s `insertPhi` sweep —
--   the dual of `RUS-Acquire`'s `consumePhi` sweep — so this leaf needs
--   `Separated` for the ambient threads, like `Local/Acq.agda`, *and* the
--   confinement/renaming machinery of `Local/LSplit.agda` for the frame and
--   the residual, which travel forward along `𝐒.rwk`.
module BorrowedCF.Simulation.ForwardSoup.Local.RSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Reduction.Base using (ChanCx)
open Typed using (_;_⊢ₚ_)

open import BorrowedCF.Simulation.Support.SplitConfine using (rsplit-confine)

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads; bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Renaming
  using (rename-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated; env-separated; thread-separated)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.InsertSupport
  using ( insertEnv; insertEnv-Value; Tᶠ*-insertPhi-frames
        ; phiFree-insertPhi; insertPhi-image
        )
open import BorrowedCF.Simulation.ForwardSoup.Local.Residual
  using ( residual-image; channels-resp
        ; ownedChannels-transport; ownedChannels-transport⁻)
open import BorrowedCF.Simulation.ForwardSoup.Local.RSplitCommon
open import BorrowedCF.Simulation.ForwardSoup.Local.SplitCommon
open import BorrowedCF.Simulation.ForwardSoup.Local.Step
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (transportChannels; untransportChannels; cast-cons)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename; processCount-rename)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- Transporting an image along an equality of source processes, and the two
-- `V.cast` facts about channel ownership that the residual chain needs.

private
  cast-zero : {a b : ℕ} (equal : suc a ≡ suc b) →
    Fin.cast equal 0F ≡ 0F
  cast-zero refl = refl

  proc-image :
    {a n m : ℕ} {P Q : Typed.Proc a} (equal : P ≡ Q)
    {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env a (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    LocalImage P logicalChannels sigma ambientChannel ambientThread C →
    LocalImage Q
      (V.cast (cong Translation.channelCount equal) logicalChannels)
      sigma ambientChannel ambientThread C
  proc-image refl {logicalChannels = logicalChannels} image =
    channels-resp (sym (V.cast-is-id refl logicalChannels)) image

  proc-image-thread :
    {a n m : ℕ} {P Q : Typed.Proc a} (equal : P ≡ Q)
    {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env a (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m}
    (image :
      LocalImage P logicalChannels sigma ambientChannel ambientThread C)
    (i : 𝔽 (Translation.processCount P)) →
    threadEmbedding (proc-image equal image)
        (Fin.cast (cong Translation.processCount equal) i) ≡
      threadEmbedding image i
  proc-image-thread refl image i =
    cong (threadEmbedding image) (Fin.cast-is-id refl i)

  ownedChannels-cast :
    {p r n : ℕ} (equal : p ≡ r) (xs : Vec (OrientedChannel n) p) (i : 𝔽 n) →
    ownedChannels (V.cast equal xs) i → ownedChannels xs i
  ownedChannels-cast refl xs i owned =
    subst (λ ys → ownedChannels ys i) (V.cast-is-id refl xs) owned

  ownedChannels-cast⁻ :
    {p r n : ℕ} (equal : p ≡ r) (xs : Vec (OrientedChannel n) p) (i : 𝔽 n) →
    ownedChannels xs i → ownedChannels (V.cast equal xs) i
  ownedChannels-cast⁻ refl xs i owned =
    subst (λ ys → ownedChannels ys i) (sym (V.cast-is-id refl xs)) owned

  record RSplitCore
    {k n m q b₁ kk : ℕ} {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
    {rho :
      𝔽 kk → 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
    {E₀ : SourceReduction.Frame* kk}
    {P₀ : Typed.Proc kk}
    (P′ : Typed.Proc k)
    (sigma : Translation.Env k (2 *ℕ n))
    (ambientChannel : 𝔽 n → Set)
    (ambientThread : 𝔽 m → Set)
    (C : Soup.Config n m)
    (ownerSlot : Maybe (𝔽 m)) : Set where
    field
      coreThread : 𝔽 m
      coreSlotEq : ownerSlot ≡ just coreThread
      coreChannel : 𝔽 n
      coreSide : 𝔽 2
      coreOpen : SoupReduction.is-open (Soup.channels C) coreChannel

      coreBoundary : ℕ
      coreBefore coreAfter : List Soup.Flag
      coreBoundaryEq : L.length coreBefore ≡ coreBoundary
      coreFlagsEq :
        SoupReduction.endpointFlags (lookup (Soup.channels C) coreChannel)
          coreSide ≡
        coreBefore L.++ coreAfter

      coreFrame : SoupExpression.Frame* (2 *ℕ n)
      coreHandleLeft : SoupTerm.Tm (2 *ℕ n)
      coreHandleEnd : 𝔽 (2 *ℕ n)
      coreHandleRight : SoupTerm.Tm (2 *ℕ n)
      coreHandleEndEq : coreHandleEnd ≡ Soup.endpoint coreChannel coreSide
      coreSelected :
        lookup (Soup.threads C) coreThread ≡
        SoupExpression._[_]* coreFrame
          (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`rsplit s))
            (Translation.chanTriple
              (coreHandleLeft , coreHandleEnd , coreHandleRight)))

      coreTargetChannels : Vec Soup.Channel n
      coreTargetChannels≡ :
        coreTargetChannels ≡
        V.updateAt (Soup.channels C) coreChannel
          (SoupReduction.setEndpointFlags coreSide
            (coreBefore L.++ Soup.drop ∷ coreAfter))
      coreInsertedThreads : Vec (Soup.Thread n) m
      coreInsertedThreads≡ :
        coreInsertedThreads ≡
        V.map (SoupReduction.insertPhi coreHandleEnd coreBoundary)
          (Soup.threads C)
      coreReplacement : Soup.Thread n
      coreReplacement≡ :
        coreReplacement ≡
        SoupExpression._[_]*
          (SoupReduction.insertPhi-frames coreHandleEnd coreBoundary coreFrame)
          (SoupTerm._⊗_
            (Translation.chanTriple
              ( SoupReduction.insertPhi coreHandleEnd coreBoundary coreHandleLeft
              , coreHandleEnd
              , SoupTerm.`phi (coreHandleEnd , coreBoundary) ))
            (Translation.chanTriple
              ( SoupTerm.`phi (coreHandleEnd , coreBoundary)
              , coreHandleEnd
              , SoupReduction.insertPhi coreHandleEnd coreBoundary coreHandleRight )))
      coreTargetThreads : Vec (Soup.Thread n) m
      coreTargetThreads≡ :
        coreTargetThreads ≡
        SoupReduction.replaceAt coreInsertedThreads coreThread coreReplacement
      coreTargetConfig : Soup.Config n m
      coreTargetConfig≡ :
        coreTargetConfig ≡ Soup.config coreTargetChannels coreTargetThreads

      coreConfigStep :
        ConfigStep P′ sigma ambientChannel ambientThread C coreTargetConfig

------------------------------------------------------------------------
-- The rule, with the frame and the residual already factored through `ρ⁻`.

private
  rsplit-worker :
    {k n m q b₁ kk : ℕ} {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
    {rho :
      𝔽 kk → 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
    {E₀ : SourceReduction.Frame* kk}
    {P₀ : Typed.Proc kk}
    {channel : OrientedChannel n}
    {bodyChannels :
      Vec (OrientedChannel n)
        (Translation.channelCount (Typed._⋯ₚ_ P₀ rho))}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    ((y : 𝔽 kk) →
      rho y ≢
      Source.SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {k} (q ↑ʳ 0F)) →
    Separated sigma ambientChannel ambientThread C →
    ValueEnv sigma →
    (image : LocalImage
      (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_ E₀ rho)
                   (Source._·¹_ (Source.K (Source.`rsplit s))
                     (Source.`
                       (Source.SplitRenamings.atk B₁ B₂ (sum B)
                         {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
         Typed.∥ (Typed._⋯ₚ_ P₀ rho)))
      (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
    RSplitCore {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
      {rho = rho} {E₀ = E₀} {P₀ = P₀}
      (Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_
                     (SourceReduction._⋯ᶠ*_ E₀ rho)
                     (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}))
                   (Source._⊗_
                     (Source.`
                       (Source.SplitRenamings.inj B₁ B₂ (sum B)
                         {(q + 1) ∷ suc b₁ ∷ []} {k}
                         ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                     (Source.`
                       (Source.SplitRenamings.inj B₁ B₂ (sum B)
                         {(q + 1) ∷ suc b₁ ∷ []} {k}
                         ((q + 1) ↑ʳ 0F)))) ⟫
         Typed.∥
           (Typed._⋯ₚ_ P₀
             (λ y →
               Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}
                 (rho y)))))
      sigma ambientChannel ambientThread C (threadEmbedding image 0F)
  rsplit-worker {k = k} {n = n} {m = m} {q = q} {b₁ = b₁} {kk = kk}
    {B₁ = B₁} {B₂ = B₂} {B = B} {s = s} {rho = rho} {E₀ = E₀} {P₀ = P₀}
    {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
    {ambientChannel = aC} {ambientThread = aT} {C = C}
    skip separated Vsigma image =
    dispatch (live-thread left 0F)
    where
    module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

    G G′ : Typed.BindGroup
    G = B₁ ++ (q + suc b₁) ∷ B₂
    G′ = B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂

    physical : 𝔽 n
    physical = physicalChannel channel

    orientation : Orientation
    orientation = proj₂ channel

    side₁ : 𝔽 2
    side₁ = orientSide orientation 0F

    end₁ end₂ : 𝔽 (2 *ℕ n)
    end₁ = physicalEndpoint channel 0F
    end₂ = physicalEndpoint channel 1F

    boundary : ℕ
    boundary = L.length B₁

    rwk : 𝔽 (sum G + sum B + k) → 𝔽 (sum G′ + sum B + k)
    rwk = 𝐒.rwk {q} {b₁} {k}

    x₀ : 𝔽 (sum G + sum B + k)
    x₀ = 𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)

    v₁ v₂ : 𝔽 (sum G′ + sum B + k)
    v₁ = 𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))
    v₂ = 𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k} ((q + 1) ↑ʳ 0F)

    sourceEnv : Translation.Env (sum G + sum B + k) (2 *ℕ n)
    sourceEnv = bindEnv G B channel sigma

    targetEnv : Translation.Env (sum G′ + sum B + k) (2 *ℕ n)
    targetEnv = bindEnv G′ B channel sigma

    insertedEnv : Translation.Env (sum G + sum B + k) (2 *ℕ n)
    insertedEnv = insertEnv end₁ boundary sourceEnv

    Vsource : ValueEnv sourceEnv
    Vsource = bindEnv-Value {B₁ = G} {B₂ = B} {channel = channel} Vsigma

    Vtarget : ValueEnv targetEnv
    Vtarget = bindEnv-Value {B₁ = G′} {B₂ = B} {channel = channel} Vsigma

    Vinserted : ValueEnv insertedEnv
    Vinserted = insertEnv-Value end₁ boundary Vsource

    ------------------------------------------------------------------
    -- The three handles.

    shape = group-rsplit-shape B₁ B₂ q b₁ end₁ end₁ SoupTerm.* SoupTerm.*

    e₁ e₂ : SoupTerm.Tm (2 *ℕ n)
    e₁ = proj₁ shape
    e₂ = proj₁ (proj₂ shape)

    handleSrc : sourceEnv x₀ ≡ Translation.chanTriple (e₁ , end₁ , e₂)
    handleSrc =
      cong sourceEnv
        (inj-injAt B₁ B₂ B ((q + suc b₁) ∷ []) k ((q ↑ʳ 0F) ↑ˡ sum B₂))
      ■ bindEnv-group G B channel sigma
          (injAt B₁ ((q + suc b₁) ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)
            ↑ˡ sum B ↑ˡ k)
          (injAt B₁ ((q + suc b₁) ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₁ (proj₂ (proj₂ shape))

    handleTgt₀ :
      targetEnv v₁ ≡
      Translation.chanTriple
        ( SoupReduction.insertPhi end₁ boundary e₁
        , end₁
        , SoupTerm.`phi (end₁ , boundary) )
    handleTgt₀ =
      cong targetEnv
        (inj-injAt B₁ B₂ B ((q + 1) ∷ suc b₁ ∷ []) k
          ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
      ■ bindEnv-group G′ B channel sigma
          (injAt B₁ ((q + 1) ∷ suc b₁ ∷ []) B₂
            ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)) ↑ˡ sum B ↑ˡ k)
          (injAt B₁ ((q + 1) ∷ suc b₁ ∷ []) B₂
            ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₁ (proj₂ (proj₂ (proj₂ shape)))

    handleTgt₁ :
      targetEnv v₂ ≡
      Translation.chanTriple
        ( SoupTerm.`phi (end₁ , boundary)
        , end₁
        , SoupReduction.insertPhi end₁ boundary e₂ )
    handleTgt₁ =
      cong targetEnv
        (inj-injAt B₁ B₂ B ((q + 1) ∷ suc b₁ ∷ []) k ((q + 1) ↑ʳ 0F))
      ■ bindEnv-group G′ B channel sigma
          (injAt B₁ ((q + 1) ∷ suc b₁ ∷ []) B₂ ((q + 1) ↑ʳ 0F)
            ↑ˡ sum B ↑ˡ k)
          (injAt B₁ ((q + 1) ∷ suc b₁ ∷ []) B₂ ((q + 1) ↑ʳ 0F))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₂ (proj₂ (proj₂ (proj₂ shape)))

    ------------------------------------------------------------------
    -- The source terms.

    redex : Source.Tm (sum G + sum B + k)
    redex = Source._·¹_ (Source.K (Source.`rsplit s)) (Source.` x₀)

    owner : Source.Tm (sum G + sum B + k)
    owner = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E₀ rho) redex

    target : Source.Tm (sum G′ + sum B + k)
    target =
      SourceReduction._[_]*
        (SourceReduction._⋯ᶠ*_ (SourceReduction._⋯ᶠ*_ E₀ rho) rwk)
        (Source._⊗_ (Source.` v₁) (Source.` v₂))

    residualProc : Typed.Proc (sum G′ + sum B + k)
    residualProc = Typed._⋯ₚ_ P₀ (λ y → rwk (rho y))

    reduct : Typed.Proc k
    reduct = Typed.ν G′ B (Typed.⟪ target ⟫ Typed.∥ residualProc)

    ------------------------------------------------------------------
    -- Splitting the frame.

    body = res-split-image image
    chanEq = res-split-channel image
    notAmb = res-split-not-ambient image

    left = par-split-left body
    right = par-split-right body

    ambientChannelLeft : 𝔽 n → Set
    ambientChannelLeft =
      (aC ∪ᵖ singletonᵖ physical) ∪ᵖ ownedChannels bodyChannels

    ambientThreadLeft : 𝔽 m → Set
    ambientThreadLeft =
      aT ∪ᵖ ownedThreads (threadEmbedding body ∘ (1 ↑ʳ_))

    ambientThreadRight : 𝔽 m → Set
    ambientThreadRight =
      aT ∪ᵖ
      ownedThreads
        (threadEmbedding body ∘
          (_↑ˡ Translation.processCount (Typed._⋯ₚ_ P₀ rho)))

    ------------------------------------------------------------------
    -- The soup frame and the expected owner thread.

    F : SoupExpression.Frame* (2 *ℕ n)
    F = Tᶠ*[ SourceReduction._⋯ᶠ*_ E₀ rho ] {σ = sourceEnv} Vsource

    expected : Soup.Thread n
    expected = Translation.T[ owner ] sourceEnv

    sigmaFixed :
      (u : 𝔽 k) → SoupReduction.insertPhi end₁ boundary (sigma u) ≡ sigma u
    sigmaFixed u =
      phiFree-insertPhi (env-separated separated u) physical side₁ boundary
        notAmb

    envCoh :
      (y : 𝔽 kk) → insertedEnv (rho y) ≡ targetEnv (rwk (rho y))
    envCoh y =
      source-target-rwk B₁ B₂ B q b₁ channel sigma sigmaFixed (rho y) (skip y)

    ------------------------------------------------------------------
    -- The flag lists of the bound channel: one new `drop` boundary at
    -- position `length B₁`.

    flagsG : List Soup.Flag
    flagsG = proj₂ (Translation.UB[ G ] end₁ (SoupTerm.* , end₁ , SoupTerm.*))

    flags₂ : List Soup.Flag
    flags₂ = proj₂ (Translation.UB[ B ] end₂ (SoupTerm.* , end₂ , SoupTerm.*))

    before after : List Soup.Flag
    before = prefixFlags B₁
    after = bindFlags ((q + suc b₁) ∷ B₂)

    lenEq : L.length before ≡ boundary
    lenEq = prefixFlags-length B₁

    ------------------------------------------------------------------
    -- The case analysis on the owner thread.

    dispatch :
      OptionalThreadImage {n = n} (Soup.threads C)
        (threadEmbedding left 0F) expected →
      RSplitCore {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
        {rho = rho} {E₀ = E₀} {P₀ = P₀}
        reduct sigma aC aT C (threadEmbedding image 0F)

    dispatch (omitted slotEq expectedEq) =
      ⊥-elim
        (plug-not-K F
          (sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₀ rho)
                 {e = redex} Vsource)
           ■ expectedEq))

    dispatch (present j slotEq lookupEq) = record
      { coreThread = j
      ; coreSlotEq = slotEq
      ; coreChannel = physical
      ; coreSide = side₁
      ; coreOpen = openEq
      ; coreBoundary = boundary
      ; coreBefore = before
      ; coreAfter = after
      ; coreBoundaryEq = lenEq
      ; coreFlagsEq = flagsEq
      ; coreFrame = F
      ; coreHandleLeft = e₁
      ; coreHandleEnd = end₁
      ; coreHandleRight = e₂
      ; coreHandleEndEq = refl
      ; coreSelected = selected
      ; coreTargetChannels = targetChannels
      ; coreTargetChannels≡ = refl
      ; coreInsertedThreads = insertedThreads
      ; coreInsertedThreads≡ = refl
      ; coreReplacement = plugged
      ; coreReplacement≡ = refl
      ; coreTargetThreads = targetThreads
      ; coreTargetThreads≡ = refl
      ; coreTargetConfig = targetConfig
      ; coreTargetConfig≡ = refl
      ; coreConfigStep =
          identity-config-step
            soupStep ambientChannelsUnchanged ambientThreadsUnchanged
            (res-join joined newChanEq notAmb)
      }
      where
      ----------------------------------------------------------------
      -- The step.

      selected :
        lookup (Soup.threads C) j ≡
        SoupExpression._[_]* F
          (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`rsplit s))
            (Translation.chanTriple (e₁ , end₁ , e₂)))
      selected =
        lookupEq
        ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₀ rho) {e = redex} Vsource
        ■ cong
            (λ handle →
              SoupExpression._[_]* F
                (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`rsplit s)) handle))
            handleSrc

      openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
      openEq = cong proj₁ chanEq ■ open-orient orientation _

      flagsEq :
        SoupReduction.endpointFlags (lookup (Soup.channels C) physical)
          side₁ ≡
        before L.++ after
      flagsEq =
        cong (λ ch → SoupReduction.endpointFlags ch side₁) chanEq
        ■ endpointFlags-orient orientation (true , flagsG , flags₂) 0F
        ■ UB-flags-shape G end₁ end₁ SoupTerm.* SoupTerm.*
        ■ bindFlags-rsplit-src B₁ B₂ q b₁

      targetChannels : Vec Soup.Channel n
      targetChannels =
        V.updateAt (Soup.channels C) physical
          (SoupReduction.setEndpointFlags side₁
            (before L.++ Soup.drop ∷ after))

      newChanEq :
        lookup targetChannels physical ≡ bindChannel G′ B channel
      newChanEq =
        V.lookup∘updateAt physical (Soup.channels C)
        ■ cong
            (SoupReduction.setEndpointFlags side₁
              (before L.++ Soup.drop ∷ after))
            chanEq
        ■ setEndpointFlags-orient orientation (true , flagsG , flags₂) 0F
            (before L.++ Soup.drop ∷ after)
        ■ cong
            (λ flags → orientChannel orientation (true , flags , flags₂))
            (sym
              ( UB-flags-shape G′ end₁ end₁ SoupTerm.* SoupTerm.*
              ■ bindFlags-rsplit-tgt B₁ B₂ q b₁ ))

      insertedThreads : Vec (Soup.Thread n) m
      insertedThreads =
        V.map (SoupReduction.insertPhi end₁ boundary) (Soup.threads C)

      plugged : Soup.Thread n
      plugged =
        SoupExpression._[_]*
          (SoupReduction.insertPhi-frames end₁ boundary F)
          (SoupTerm._⊗_
            (Translation.chanTriple
              ( SoupReduction.insertPhi end₁ boundary e₁
              , end₁
              , SoupTerm.`phi (end₁ , boundary) ))
            (Translation.chanTriple
              ( SoupTerm.`phi (end₁ , boundary)
              , end₁
              , SoupReduction.insertPhi end₁ boundary e₂ )))

      targetThreads : Vec (Soup.Thread n) m
      targetThreads = SoupReduction.replaceAt insertedThreads j plugged

      targetConfig : Soup.Config n m
      targetConfig = Soup.config targetChannels targetThreads

      soupStep : C SoupReduction.─→ₚ targetConfig
      soupStep =
        subst
          (λ z →
            C SoupReduction.─→ₚ
            Soup.config targetChannels
              (SoupReduction.replaceAt
                (V.map (SoupReduction.insertPhi end₁ z) (Soup.threads C)) j
                (SoupExpression._[_]*
                  (SoupReduction.insertPhi-frames end₁ z F)
                  (SoupTerm._⊗_
                    (Translation.chanTriple
                      ( SoupReduction.insertPhi end₁ z e₁
                      , end₁
                      , SoupTerm.`phi (end₁ , z) ))
                    (Translation.chanTriple
                      ( SoupTerm.`phi (end₁ , z)
                      , end₁
                      , SoupReduction.insertPhi end₁ z e₂ ))))))
          lenEq
          (SoupReduction.RUS-RSplit
            {cs = Soup.channels C} {ts = Soup.threads C}
            j physical side₁ F before after {e₁ = e₁} {e₂ = e₂}
            openEq flagsEq selected)

      ----------------------------------------------------------------
      -- The ambient frame is untouched.

      ambientChannelsUnchanged :
        (i : 𝔽 n) → aC i →
        lookup targetChannels i ≡ lookup (Soup.channels C) i
      ambientChannelsUnchanged i ambient =
        V.lookup∘updateAt′ i physical
          (λ eq → notAmb (subst aC eq ambient))
          (Soup.channels C)

      ambientThreadsUnchanged :
        (l′ : 𝔽 m) → aT l′ →
        lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
      ambientThreadsUnchanged l′ ambient =
        V.lookup∘updateAt′ l′ j
          (λ eq → thread-not-ambient left slotEq (inj₁ (subst aT eq ambient)))
          insertedThreads
        ■ V.lookup-map l′ (SoupReduction.insertPhi end₁ boundary)
            (Soup.threads C)
        ■ phiFree-insertPhi (thread-separated separated l′ ambient)
            physical side₁ boundary notAmb

      ----------------------------------------------------------------
      -- The image of the owner after the step.

      targetThread : lookup targetThreads j ≡ Translation.T[ target ] targetEnv
      targetThread =
        V.lookup∘updateAt j insertedThreads
        ■ cong
            (SoupExpression._[_]*
              (SoupReduction.insertPhi-frames end₁ boundary F))
            (cong₂ SoupTerm._⊗_ (sym handleTgt₀) (sym handleTgt₁))
        ■ Tᶠ*-insertPhi-frames (SourceReduction._⋯ᶠ*_ E₀ rho) Vsource
            end₁ boundary Vinserted
            (SoupTerm._⊗_ (targetEnv v₁) (targetEnv v₂))
        ■ Tᶠ*-plug-ren-ren-coh E₀ rho rwk insertedEnv targetEnv
            Vinserted Vtarget envCoh
            (SoupTerm._⊗_ (targetEnv v₁) (targetEnv v₂))
        ■ sym
            (T[_]-plugᶠ*
              (SourceReduction._⋯ᶠ*_ (SourceReduction._⋯ᶠ*_ E₀ rho) rwk)
              {e = Source._⊗_ (Source.` v₁) (Source.` v₂)} Vtarget)

      targetGarbageThread :
        (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
        ¬ ambientThreadLeft l′ →
        lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
      targetGarbageThread l′ outside notAmbient =
        V.lookup∘updateAt′ l′ j
          (λ eq → outside 0F (slotEq ■ cong just (sym eq)))
          insertedThreads
        ■ V.lookup-map l′ (SoupReduction.insertPhi end₁ boundary)
            (Soup.threads C)
        ■ cong (SoupReduction.insertPhi end₁ boundary)
            (garbage-thread left l′ outside notAmbient)

      leftImage :
        LocalImage (Typed.⟪ target ⟫)
          [] targetEnv ambientChannelLeft ambientThreadLeft targetConfig
      leftImage = record
        { channelEmbedding-injective = channelEmbedding-injective left
        ; threadEmbedding = threadEmbedding left
        ; threadEmbedding-injective = threadEmbedding-injective left
        ; channel-not-ambient = λ ()
        ; thread-not-ambient = thread-not-ambient left
        ; live-channel = λ ()
        ; live-thread = λ where
            0F → present j slotEq targetThread
        ; garbage-channel = λ i outside notAmbient →
            V.lookup∘updateAt′ i physical
              (λ eq → notAmbient (inj₁ (inj₂ (sym eq))))
              (Soup.channels C)
            ■ garbage-channel left i outside notAmbient
        ; garbage-thread = targetGarbageThread
        }

      ----------------------------------------------------------------
      -- The residual process travels forward along `rwk ∘ rho`, after the
      -- global `insertPhi` sweep.

      threadsUnchangedRight :
        (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
        lookup targetThreads l′ ≡ lookup insertedThreads l′
      threadsUnchangedRight l′ notAmbient =
        V.lookup∘updateAt′ l′ j
          (λ eq → notAmbient (inj₂ (0F , (slotEq ■ cong just (sym eq)))))
          insertedThreads

      insertedImage =
        insertPhi-image
          {channels = Soup.channels C} {channels′ = targetChannels}
          {threads = Soup.threads C}
          physical side₁ boundary (λ _ → refl)
          (λ i eq → channel-not-ambient right i (inj₁ (inj₂ (sym eq))))
          (λ i notAmbient →
            V.lookup∘updateAt′ i physical
              (λ eq → notAmbient (inj₁ (inj₂ (sym eq))))
              (Soup.channels C))
          right

      rightImage =
        config-resp
          {C = Soup.config targetChannels insertedThreads}
          {C′ = targetConfig}
          (λ _ _ → refl) threadsUnchangedRight insertedImage

      confined =
        residual-image {P = P₀} {rho = rho}
          {channels = bodyChannels}
          {sourceEnv = insertedEnv} {targetEnv = λ y → insertedEnv (rho y)}
          (λ _ → refl) rightImage

      residual =
        rename-image {P = P₀} {rho = λ y → rwk (rho y)}
          {sourceChannels = transportChannels P₀ rho bodyChannels}
          {sourceEnv = targetEnv} {targetEnv = λ y → insertedEnv (rho y)}
          (λ y → sym (envCoh y)) confined

      residualChannels :
        Vec (OrientedChannel n) (Translation.channelCount residualProc)
      residualChannels =
        untransportChannels P₀ (λ y → rwk (rho y))
          (transportChannels P₀ rho bodyChannels)

      channelShift : Translation.channelCount P₀ ≡
                     Translation.channelCount residualProc
      channelShift = sym (channelCount-rename P₀ (λ y → rwk (rho y)))

      processShiftA :
        Translation.processCount (Typed._⋯ₚ_ P₀ rho) ≡
        Translation.processCount P₀
      processShiftA = processCount-rename P₀ rho

      processShiftB :
        Translation.processCount residualProc ≡
        Translation.processCount P₀
      processShiftB = processCount-rename P₀ (λ y → rwk (rho y))

      forwardSlot :
        𝔽 (Translation.processCount (Typed._⋯ₚ_ P₀ rho)) →
        𝔽 (Translation.processCount residualProc)
      forwardSlot i = Fin.cast (sym processShiftB) (Fin.cast processShiftA i)

      forwardSlotEq :
        (i : 𝔽 (Translation.processCount (Typed._⋯ₚ_ P₀ rho))) →
        threadEmbedding residual (forwardSlot i) ≡ threadEmbedding right i
      forwardSlotEq i =
        cong (threadEmbedding right)
          ( cong (Fin.cast (sym processShiftA))
              (Fin.cast-involutive processShiftB (sym processShiftB)
                (Fin.cast processShiftA i))
          ■ Fin.cast-involutive (sym processShiftA) processShiftA i
          )

      joined :
        LocalImage (Typed.⟪ target ⟫ Typed.∥ residualProc)
          residualChannels targetEnv
          (aC ∪ᵖ singletonᵖ physical) aT targetConfig
      joined =
        par-join leftImage residual
          (λ i →
            inj₂
              (ownedChannels-transport {P = P₀} {rho = rho}
                {channels = bodyChannels} _
                (ownedChannels-cast channelShift
                  (transportChannels P₀ rho bodyChannels) _ (i , refl))))
          (λ {i} {l′} embedded →
            inj₂
              ( Fin.cast (sym processShiftA) (Fin.cast processShiftB i)
              , embedded
              ))
          (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
          (λ i → λ where
            (inj₁ ambient) → inj₁ ambient
            (inj₂ owned) →
              inj₂
                (ownedChannels-cast⁻ channelShift
                  (transportChannels P₀ rho bodyChannels) i
                  (ownedChannels-transport⁻ {P = P₀} {rho = rho}
                    {channels = bodyChannels} i owned)))
          (λ l′ → λ where
            (inj₁ ambient) → inj₁ ambient
            (inj₂ (i , owned)) →
              inj₂ (forwardSlot i , (forwardSlotEq i ■ owned)))

------------------------------------------------------------------------
-- The leaf.

record RSplitStep
  {k n m q b₁ : ℕ} {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
  {E : SourceReduction.Frame*
         (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {P : Typed.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (suc (Translation.channelCount P))}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image :
    LocalImage
      (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]* E
                   (Source._·¹_ (Source.K (Source.`rsplit s))
                     (Source.`
                       (Source.SplitRenamings.atk B₁ B₂ (sum B)
                         {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
         Typed.∥ P))
      logicalChannels sigma ambientChannel ambientThread C) : Set where
  field
    rsplitArity : ℕ
    rsplitRenaming :
      𝔽 rsplitArity →
      𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)
    rsplitSkip :
      (y : 𝔽 rsplitArity) →
      rsplitRenaming y ≢
      Source.SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {k} (q ↑ʳ 0F)
    rsplitSourceFrame : SourceReduction.Frame* rsplitArity
    rsplitSourceFrameFactor :
      E ≡ SourceReduction._⋯ᶠ*_ rsplitSourceFrame rsplitRenaming
    rsplitSourceResidual : Typed.Proc rsplitArity
    rsplitSourceResidualFactor :
      P ≡ Typed._⋯ₚ_ rsplitSourceResidual rsplitRenaming

    rsplitThread : 𝔽 m
    rsplitSlotEq : threadEmbedding image 0F ≡ just rsplitThread
    rsplitChannel : 𝔽 n
    rsplitSide : 𝔽 2
    rsplitOpen : SoupReduction.is-open (Soup.channels C) rsplitChannel

    rsplitBoundary : ℕ
    rsplitBefore rsplitAfter : List Soup.Flag
    rsplitBoundaryEq : L.length rsplitBefore ≡ rsplitBoundary
    rsplitFlagsEq :
      SoupReduction.endpointFlags (lookup (Soup.channels C) rsplitChannel)
        rsplitSide ≡
      rsplitBefore L.++ rsplitAfter

    rsplitFrame : SoupExpression.Frame* (2 *ℕ n)
    rsplitHandleLeft : SoupTerm.Tm (2 *ℕ n)
    rsplitHandleEnd : 𝔽 (2 *ℕ n)
    rsplitHandleRight : SoupTerm.Tm (2 *ℕ n)
    rsplitHandleEndEq : rsplitHandleEnd ≡ Soup.endpoint rsplitChannel rsplitSide
    rsplitSelected :
      lookup (Soup.threads C) rsplitThread ≡
      SoupExpression._[_]* rsplitFrame
        (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`rsplit s))
          (Translation.chanTriple
            (rsplitHandleLeft , rsplitHandleEnd , rsplitHandleRight)))

    rsplitTargetChannels : Vec Soup.Channel n
    rsplitTargetChannels≡ :
      rsplitTargetChannels ≡
      V.updateAt (Soup.channels C) rsplitChannel
        (SoupReduction.setEndpointFlags rsplitSide
          (rsplitBefore L.++ Soup.drop ∷ rsplitAfter))
    rsplitInsertedThreads : Vec (Soup.Thread n) m
    rsplitInsertedThreads≡ :
      rsplitInsertedThreads ≡
      V.map (SoupReduction.insertPhi rsplitHandleEnd rsplitBoundary)
        (Soup.threads C)
    rsplitReplacement : Soup.Thread n
    rsplitReplacement≡ :
      rsplitReplacement ≡
      SoupExpression._[_]*
        (SoupReduction.insertPhi-frames rsplitHandleEnd rsplitBoundary rsplitFrame)
        (SoupTerm._⊗_
          (Translation.chanTriple
            ( SoupReduction.insertPhi rsplitHandleEnd rsplitBoundary rsplitHandleLeft
            , rsplitHandleEnd
            , SoupTerm.`phi (rsplitHandleEnd , rsplitBoundary) ))
          (Translation.chanTriple
            ( SoupTerm.`phi (rsplitHandleEnd , rsplitBoundary)
            , rsplitHandleEnd
            , SoupReduction.insertPhi rsplitHandleEnd rsplitBoundary
                rsplitHandleRight )))
    rsplitTargetThreads : Vec (Soup.Thread n) m
    rsplitTargetThreads≡ :
      rsplitTargetThreads ≡
      SoupReduction.replaceAt rsplitInsertedThreads rsplitThread rsplitReplacement
    rsplitTargetConfig : Soup.Config n m
    rsplitTargetConfig≡ :
      rsplitTargetConfig ≡ Soup.config rsplitTargetChannels rsplitTargetThreads

    rsplitConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C rsplitTargetConfig

open RSplitStep public

rsplit-step :
  {k n m q b₁ : ℕ} {Γ : Context.Ctx k} {g : Context.Struct k}
  {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
  {E : SourceReduction.Frame*
         (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {P : Typed.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (suc (Translation.channelCount P))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ChanCx Γ →
  Γ ; g ⊢ₚ
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P) →
  ValueEnv sigma →
  Separated sigma ambientChannel ambientThread C →
  (image : LocalImage
    (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C) →
  RSplitStep {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
    {E = E} {P = P}
    (Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.inj B₁ B₂ (sum B)
                       {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                   (Source.`
                     (Source.SplitRenamings.inj B₁ B₂ (sum B)
                       {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ P
           (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}))))
    sigma ambientChannel ambientThread C image
rsplit-step {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
  {s = s} {E = E} {P = P} {logicalChannels = channel ∷ bodyChannels}
  {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
  Γ-S ⊢P Vsigma separated image
  with rsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁}
         {s = s} {E = E} {P = P} ⊢P
... | kk , rho , skip , E₀ , Eeq , P₀ , Peq = record
  { rsplitArity = kk
  ; rsplitRenaming = rho
  ; rsplitSkip = skip
  ; rsplitSourceFrame = E₀
  ; rsplitSourceFrameFactor = Eeq
  ; rsplitSourceResidual = P₀
  ; rsplitSourceResidualFactor = Peq
  ; rsplitThread = RSplitCore.coreThread core
  ; rsplitSlotEq = sym redexImageThread ■ RSplitCore.coreSlotEq core
  ; rsplitChannel = RSplitCore.coreChannel core
  ; rsplitSide = RSplitCore.coreSide core
  ; rsplitOpen = RSplitCore.coreOpen core
  ; rsplitBoundary = RSplitCore.coreBoundary core
  ; rsplitBefore = RSplitCore.coreBefore core
  ; rsplitAfter = RSplitCore.coreAfter core
  ; rsplitBoundaryEq = RSplitCore.coreBoundaryEq core
  ; rsplitFlagsEq = RSplitCore.coreFlagsEq core
  ; rsplitFrame = RSplitCore.coreFrame core
  ; rsplitHandleLeft = RSplitCore.coreHandleLeft core
  ; rsplitHandleEnd = RSplitCore.coreHandleEnd core
  ; rsplitHandleRight = RSplitCore.coreHandleRight core
  ; rsplitHandleEndEq = RSplitCore.coreHandleEndEq core
  ; rsplitSelected = RSplitCore.coreSelected core
  ; rsplitTargetChannels = RSplitCore.coreTargetChannels core
  ; rsplitTargetChannels≡ = RSplitCore.coreTargetChannels≡ core
  ; rsplitInsertedThreads = RSplitCore.coreInsertedThreads core
  ; rsplitInsertedThreads≡ = RSplitCore.coreInsertedThreads≡ core
  ; rsplitReplacement = RSplitCore.coreReplacement core
  ; rsplitReplacement≡ = RSplitCore.coreReplacement≡ core
  ; rsplitTargetThreads = RSplitCore.coreTargetThreads core
  ; rsplitTargetThreads≡ = RSplitCore.coreTargetThreads≡ core
  ; rsplitTargetConfig = RSplitCore.coreTargetConfig core
  ; rsplitTargetConfig≡ = RSplitCore.coreTargetConfig≡ core
  ; rsplitConfigStep =
      subst
        (λ Z → ConfigStep Z sigma aC aT C (RSplitCore.coreTargetConfig core))
        stepEq
        (RSplitCore.coreConfigStep core)
  }
  where
  module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

  rwk : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k) →
        𝔽 (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B + k)
  rwk = 𝐒.rwk {q} {b₁} {k}

  redexEq :
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P)
    ≡
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₀ rho)
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P₀ rho))
  redexEq =
    cong₂
      (λ E′ P′ →
        Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
          (Typed.⟪ SourceReduction._[_]* E′
                     (Source._·¹_ (Source.K (Source.`rsplit s))
                       (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
           Typed.∥ P′))
      Eeq Peq

  redexImage =
    channels-resp
      (cast-cons (cong Translation.channelCount Peq) channel bodyChannels)
      (proc-image redexEq image)

  redexImageThread :
    threadEmbedding redexImage 0F ≡ threadEmbedding image 0F
  redexImageThread =
    cong (threadEmbedding (proc-image redexEq image))
      (sym (cast-zero (cong Translation.processCount redexEq)))
    ■ proc-image-thread redexEq image 0F

  core :
    RSplitCore {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
      {rho = rho} {E₀ = E₀} {P₀ = P₀}
      (Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_
                     (SourceReduction._⋯ᶠ*_ E₀ rho) rwk)
                   (Source._⊗_
                     (Source.`
                       (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                         ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                     (Source.`
                       (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                         ((q + 1) ↑ʳ 0F)))) ⟫
         Typed.∥ (Typed._⋯ₚ_ P₀ (λ y → rwk (rho y)))))
      sigma aC aT C (threadEmbedding redexImage 0F)
  core =
    rsplit-worker {rho = rho} {E₀ = E₀} {P₀ = P₀} {channel = channel}
      skip separated Vsigma redexImage

  stepEq :
    Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_
                   (SourceReduction._⋯ᶠ*_ E₀ rho) rwk)
                 (Source._⊗_
                   (Source.`
                     (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                   (Source.`
                     (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P₀ (λ y → rwk (rho y))))
    ≡
    Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E rwk)
                 (Source._⊗_
                   (Source.`
                     (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                   (Source.`
                     (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P rwk))
  stepEq =
    cong₂
      (λ E′ P′ →
        Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
          (Typed.⟪ SourceReduction._[_]*
                     (SourceReduction._⋯ᶠ*_ E′ rwk)
                     (Source._⊗_
                       (Source.`
                         (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                           ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                       (Source.`
                         (𝐒.inj {(q + 1) ∷ suc b₁ ∷ []} {k}
                           ((q + 1) ↑ʳ 0F)))) ⟫
           Typed.∥ P′))
      (sym Eeq)
      (sym (Typed.fusionₚ P₀ rho rwk)
       ■ cong (λ Z → Typed._⋯ₚ_ Z rwk) (sym Peq))

U-rsplit-local :
  {k n m q b₁ : ℕ} {Γ : Context.Ctx k} {g : Context.Struct k}
  {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
  {E : SourceReduction.Frame*
         (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {P : Typed.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (suc (Translation.channelCount P))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ChanCx Γ →
  Γ ; g ⊢ₚ
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P) →
  ValueEnv sigma →
  Separated sigma ambientChannel ambientThread C →
  LocalImage
    (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`rsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.inj B₁ B₂ (sum B)
                       {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                   (Source.`
                     (Source.SplitRenamings.inj B₁ B₂ (sum B)
                       {(q + 1) ∷ suc b₁ ∷ []} {k}
                       ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ P
           (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k}))))
    sigma ambientChannel ambientThread C
U-rsplit-local {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
  {s = s} {E = E} {P = P} {logicalChannels = channel ∷ bodyChannels}
  {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
  Γ-S ⊢P Vsigma separated image =
  configStep⇒localStep
    (RSplitStep.rsplitConfigStep
      (rsplit-step {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
        {s = s} {E = E} {P = P}
        {logicalChannels = channel ∷ bodyChannels}
        {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
        Γ-S ⊢P Vsigma separated image))
