-- | Phase 3, leaf rule `R-LSplit` (`ForwardSoup/PLAN.md`, §4, Phase 3,
--   item 4).
--
--     ν (B₁ ++ (q + suc b₁) ∷ B₂) B
--       (⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
--       ─→ₚ
--     ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
--       (⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫
--        ∥ (P ⋯ₚ 𝐒.lwk))
--
--   Unlike every previous leaf the *reduct* is the one at the larger arity:
--   one borrow is inserted in the middle of the first binder group, so frames
--   and residual travel forward along `𝐒.lwk`.  The environment agreement
--   `source-target-lwk` holds away from the consumed handle only, and typing
--   (`lsplit-confine`) supplies the factorisation `E ≡ E₀ ⋯ᶠ* ρ⁻`,
--   `P ≡ P₀ ⋯ₚ ρ⁻` through a renaming that misses it.
--
--   The bound channel is untouched: its two flag lists are unchanged, because
--   the split block's flag `ϕ[ q + suc b₁ ] = drop` stays `drop`
--   (`bindFlags-lsplit`).  So the soup side is `RUS-LSplit`, whose channel
--   vector is literally the old one, and the shape is `Local/Discard.agda`'s:
--   `res-split` → `par-split-left`/`-right` → the handle triple →
--   `RUS-LSplit` → `par-join`/`res-join` → `identity-step`.
module BorrowedCF.Simulation.ForwardSoup.Local.LSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

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

open import BorrowedCF.Simulation.Support.SplitConfine using (lsplit-confine)

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
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Residual
  using ( residual-image; channels-resp
        ; ownedChannels-transport; ownedChannels-transport⁻)
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

  record LSplitCore
    {k n m q b₁ kk : ℕ} {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
    {rho :
      𝔽 kk → 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
    {E₀ : SourceReduction.Frame* kk}
    {P₀ : Typed.Proc kk}
    (P′ : Typed.Proc k)
    (sigma : Translation.Env k (2 *ℕ n))
    (ambientChannel : 𝔽 n → Set)
    (ambientThread : 𝔽 m → Set)
    (C : Soup.Config n m) : Set where
    field
      coreThread : 𝔽 m
      coreChannel : 𝔽 n
      coreSide : 𝔽 2
      coreOpen : SoupReduction.is-open (Soup.channels C) coreChannel

      coreFrame : SoupExpression.Frame* (2 *ℕ n)
      coreHandleLeft : SoupTerm.Tm (2 *ℕ n)
      coreHandleEnd : 𝔽 (2 *ℕ n)
      coreHandleRight : SoupTerm.Tm (2 *ℕ n)
      coreSelected :
        lookup (Soup.threads C) coreThread ≡
        SoupExpression._[_]* coreFrame
          (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`lsplit s))
            (Translation.chanTriple
              (coreHandleLeft , coreHandleEnd , coreHandleRight)))

      coreReplacement : Soup.Thread n
      coreReplacement≡ :
        coreReplacement ≡
        SoupExpression._[_]* coreFrame
          (SoupTerm._⊗_
            (Translation.chanTriple
              (coreHandleLeft , coreHandleEnd , SoupTerm.*))
            (Translation.chanTriple
              (SoupTerm.* , coreHandleEnd , coreHandleRight)))

      coreConfigStep :
        ConfigStep P′ sigma ambientChannel ambientThread C
          (Soup.config (Soup.channels C)
            (SoupReduction.replaceAt
              (Soup.threads C) coreThread coreReplacement))

------------------------------------------------------------------------
-- The rule, with the frame and the residual already factored through `ρ⁻`.

private
  lsplit-worker :
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
    ValueEnv sigma →
    LocalImage
      (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_ E₀ rho)
                   (Source._·¹_ (Source.K (Source.`lsplit s))
                     (Source.`
                       (Source.SplitRenamings.atk B₁ B₂ (sum B)
                         {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
         Typed.∥ (Typed._⋯ₚ_ P₀ rho)))
      (channel ∷ bodyChannels) sigma ambientChannel ambientThread C →
    LSplitCore {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
      {rho = rho} {E₀ = E₀} {P₀ = P₀}
      (Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_
                     (SourceReduction._⋯ᶠ*_ E₀ rho)
                     (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}))
                   (Source._⊗_
                     (Source.`
                       (Source.SplitRenamings.atk B₁ B₂ (sum B)
                         {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                     (Source.`
                       (Source.SplitRenamings.atk B₁ B₂ (sum B)
                         {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
         Typed.∥
           (Typed._⋯ₚ_ P₀
             (λ y →
               Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}
                 (rho y)))))
      sigma ambientChannel ambientThread C
  lsplit-worker {k = k} {n = n} {m = m} {q = q} {b₁ = b₁} {kk = kk}
    {B₁ = B₁} {B₂ = B₂} {B = B} {s = s} {rho = rho} {E₀ = E₀} {P₀ = P₀}
    {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
    {ambientChannel = aC} {ambientThread = aT} {C = C}
    skip Vsigma image =
    dispatch (live-thread left 0F)
    where
    module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

    G G′ : Typed.BindGroup
    G = B₁ ++ (q + suc b₁) ∷ B₂
    G′ = B₁ ++ (q + suc (suc b₁)) ∷ B₂

    physical : 𝔽 n
    physical = physicalChannel channel

    end₁ end₂ : 𝔽 (2 *ℕ n)
    end₁ = physicalEndpoint channel 0F
    end₂ = physicalEndpoint channel 1F

    lwk : 𝔽 (sum G + sum B + k) → 𝔽 (sum G′ + sum B + k)
    lwk = 𝐒.lwk {q} {b₁} {k}

    x₀ : 𝔽 (sum G + sum B + k)
    x₀ = 𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)

    x₀′ x₁′ : 𝔽 (sum G′ + sum B + k)
    x₀′ = 𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 0F)
    x₁′ = 𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 1F)

    sourceEnv : Translation.Env (sum G + sum B + k) (2 *ℕ n)
    sourceEnv = bindEnv G B channel sigma

    targetEnv : Translation.Env (sum G′ + sum B + k) (2 *ℕ n)
    targetEnv = bindEnv G′ B channel sigma

    Vsource : ValueEnv sourceEnv
    Vsource = bindEnv-Value {B₁ = G} {B₂ = B} {channel = channel} Vsigma

    Vtarget : ValueEnv targetEnv
    Vtarget = bindEnv-Value {B₁ = G′} {B₂ = B} {channel = channel} Vsigma

    ------------------------------------------------------------------
    -- The three handles.

    shape = group-lsplit-shape B₁ B₂ q b₁ end₁ end₁ SoupTerm.* SoupTerm.*

    e₁ e₂ : SoupTerm.Tm (2 *ℕ n)
    e₁ = proj₁ shape
    e₂ = proj₁ (proj₂ shape)

    handleSrc : sourceEnv x₀ ≡ Translation.chanTriple (e₁ , end₁ , e₂)
    handleSrc =
      cong sourceEnv (atk-blockAt B₁ B₂ B (q + suc b₁) k (q ↑ʳ 0F))
      ■ bindEnv-group G B channel sigma
          (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F) ↑ˡ sum B ↑ˡ k)
          (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₁ (proj₂ (proj₂ shape))

    handleTgt₀ :
      targetEnv x₀′ ≡ Translation.chanTriple (e₁ , end₁ , SoupTerm.*)
    handleTgt₀ =
      cong targetEnv (atk-blockAt B₁ B₂ B (q + suc (suc b₁)) k (q ↑ʳ 0F))
      ■ bindEnv-group G′ B channel sigma
          (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 0F) ↑ˡ sum B ↑ˡ k)
          (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 0F))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₁ (proj₂ (proj₂ (proj₂ shape)))

    handleTgt₁ :
      targetEnv x₁′ ≡ Translation.chanTriple (SoupTerm.* , end₁ , e₂)
    handleTgt₁ =
      cong targetEnv (atk-blockAt B₁ B₂ B (q + suc (suc b₁)) k (q ↑ʳ 1F))
      ■ bindEnv-group G′ B channel sigma
          (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 1F) ↑ˡ sum B ↑ˡ k)
          (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 1F))
          (Fin.toℕ-↑ˡ _ k ■ Fin.toℕ-↑ˡ _ (sum B))
      ■ proj₂ (proj₂ (proj₂ (proj₂ shape)))

    ------------------------------------------------------------------
    -- The source terms.

    redex : Source.Tm (sum G + sum B + k)
    redex = Source._·¹_ (Source.K (Source.`lsplit s)) (Source.` x₀)

    owner : Source.Tm (sum G + sum B + k)
    owner = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E₀ rho) redex

    target : Source.Tm (sum G′ + sum B + k)
    target =
      SourceReduction._[_]*
        (SourceReduction._⋯ᶠ*_ (SourceReduction._⋯ᶠ*_ E₀ rho) lwk)
        (Source._⊗_ (Source.` x₀′) (Source.` x₁′))

    residualProc : Typed.Proc (sum G′ + sum B + k)
    residualProc = Typed._⋯ₚ_ P₀ (λ y → lwk (rho y))

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

    envCoh :
      (y : 𝔽 kk) → sourceEnv (rho y) ≡ targetEnv (lwk (rho y))
    envCoh y =
      source-target-lwk B₁ B₂ B q b₁ channel sigma (rho y) (skip y)

    ------------------------------------------------------------------
    -- The flag lists of the bound channel do not move.

    bindEq : bindChannel G B channel ≡ bindChannel G′ B channel
    bindEq =
      cong
        (λ flags →
          orientChannel (proj₂ channel)
            ( true
            , flags
            , proj₂ (Translation.UB[ B ] end₂
                      (SoupTerm.* , end₂ , SoupTerm.*))
            ))
        ( UB-flags-shape G end₁ end₁ SoupTerm.* SoupTerm.*
        ■ bindFlags-lsplit B₁ B₂ q b₁
        ■ sym (UB-flags-shape G′ end₁ end₁ SoupTerm.* SoupTerm.*)
        )

    ------------------------------------------------------------------
    -- The case analysis on the owner thread.

    dispatch :
      OptionalThreadImage {n = n} (Soup.threads C)
        (threadEmbedding left 0F) expected →
      LSplitCore reduct sigma aC aT C

    dispatch (omitted slotEq expectedEq) =
      ⊥-elim
        (plug-not-K F
          (sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₀ rho)
                 {e = redex} Vsource)
           ■ expectedEq))

    dispatch (present j slotEq lookupEq) = record
      { coreThread = j
      ; coreChannel = physical
      ; coreSide = orientSide (proj₂ channel) 0F
      ; coreOpen = openEq
      ; coreFrame = F
      ; coreHandleLeft = e₁
      ; coreHandleEnd = end₁
      ; coreHandleRight = e₂
      ; coreSelected = selected
      ; coreReplacement = plugged
      ; coreReplacement≡ = refl
      ; coreConfigStep =
          identity-config-step soupStep (λ _ _ → refl) ambientThreadsUnchanged
            (res-join joined (chanEq ■ bindEq) notAmb)
      }
      where
      ----------------------------------------------------------------
      -- The step.

      selected :
        lookup (Soup.threads C) j ≡
        SoupExpression._[_]* F
          (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`lsplit s))
            (Translation.chanTriple (e₁ , end₁ , e₂)))
      selected =
        lookupEq
        ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₀ rho) {e = redex} Vsource
        ■ cong
            (λ handle →
              SoupExpression._[_]* F
                (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`lsplit s)) handle))
            handleSrc

      plugged : Soup.Thread n
      plugged =
        SoupExpression._[_]* F
          (SoupTerm._⊗_
            (Translation.chanTriple (e₁ , end₁ , SoupTerm.*))
            (Translation.chanTriple (SoupTerm.* , end₁ , e₂)))

      targetThreads : Vec (Soup.Thread n) m
      targetThreads = SoupReduction.replaceAt (Soup.threads C) j plugged

      targetConfig : Soup.Config n m
      targetConfig = Soup.config (Soup.channels C) targetThreads

      openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
      openEq = cong proj₁ chanEq ■ open-orient (proj₂ channel) _

      soupStep : C SoupReduction.─→ₚ targetConfig
      soupStep =
        SoupReduction.RUS-LSplit
          {cs = Soup.channels C} {ts = Soup.threads C}
          j physical (orientSide (proj₂ channel) 0F) F
          {e₁ = e₁} {e₂ = e₂} openEq selected

      ----------------------------------------------------------------
      -- The frame is untouched.

      ambientThreadsUnchanged :
        (l′ : 𝔽 m) → aT l′ →
        lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
      ambientThreadsUnchanged l′ ambient =
        V.lookup∘updateAt′ l′ j
          (λ eq → thread-not-ambient left slotEq (inj₁ (subst aT eq ambient)))
          (Soup.threads C)

      ----------------------------------------------------------------
      -- The image of the owner after the step.

      targetThread : lookup targetThreads j ≡ Translation.T[ target ] targetEnv
      targetThread =
        V.lookup∘updateAt j (Soup.threads C)
        ■ cong (SoupExpression._[_]* F)
            (cong₂ SoupTerm._⊗_ (sym handleTgt₀) (sym handleTgt₁))
        ■ Tᶠ*-plug-ren-ren-coh E₀ rho lwk sourceEnv targetEnv
            Vsource Vtarget envCoh
            (SoupTerm._⊗_ (targetEnv x₀′) (targetEnv x₁′))
        ■ sym
            (T[_]-plugᶠ*
              (SourceReduction._⋯ᶠ*_ (SourceReduction._⋯ᶠ*_ E₀ rho) lwk)
              {e = Source._⊗_ (Source.` x₀′) (Source.` x₁′)} Vtarget)

      targetGarbageThread :
        (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
        ¬ ambientThreadLeft l′ →
        lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
      targetGarbageThread l′ outside notAmbient =
        V.lookup∘updateAt′ l′ j
          (λ eq → outside 0F (slotEq ■ cong just (sym eq)))
          (Soup.threads C)
        ■ garbage-thread left l′ outside notAmbient

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
            garbage-channel left i outside notAmbient
        ; garbage-thread = targetGarbageThread
        }

      ----------------------------------------------------------------
      -- The residual process travels forward along `lwk ∘ rho`.

      threadsUnchangedRight :
        (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
        lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
      threadsUnchangedRight l′ notAmbient =
        V.lookup∘updateAt′ l′ j
          (λ eq → notAmbient (inj₂ (0F , (slotEq ■ cong just (sym eq)))))
          (Soup.threads C)

      rightImage =
        config-resp {C = C} {C′ = targetConfig}
          (λ _ _ → refl) threadsUnchangedRight right

      confined =
        residual-image {P = P₀} {rho = rho}
          {channels = bodyChannels}
          {sourceEnv = sourceEnv} {targetEnv = λ y → sourceEnv (rho y)}
          (λ _ → refl) rightImage

      residual =
        rename-image {P = P₀} {rho = λ y → lwk (rho y)}
          {sourceChannels = transportChannels P₀ rho bodyChannels}
          {sourceEnv = targetEnv} {targetEnv = λ y → sourceEnv (rho y)}
          (λ y → sym (envCoh y)) confined

      residualChannels :
        Vec (OrientedChannel n) (Translation.channelCount residualProc)
      residualChannels =
        untransportChannels P₀ (λ y → lwk (rho y))
          (transportChannels P₀ rho bodyChannels)

      channelShift : Translation.channelCount P₀ ≡
                     Translation.channelCount residualProc
      channelShift = sym (channelCount-rename P₀ (λ y → lwk (rho y)))

      processShiftA :
        Translation.processCount (Typed._⋯ₚ_ P₀ rho) ≡
        Translation.processCount P₀
      processShiftA = processCount-rename P₀ rho

      processShiftB :
        Translation.processCount residualProc ≡
        Translation.processCount P₀
      processShiftB = processCount-rename P₀ (λ y → lwk (rho y))

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

record LSplitStep
  {k n m q b₁ : ℕ} {B₁ B₂ B : Typed.BindGroup} {s : Types.𝕊 0}
  {E : SourceReduction.Frame*
         (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  {P : Typed.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)}
  (P′ : Typed.Proc k)
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    lsplitArity : ℕ
    lsplitRenaming :
      𝔽 lsplitArity → 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)
    lsplitSkip :
      (y : 𝔽 lsplitArity) →
      lsplitRenaming y ≢
      Source.SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {k} (q ↑ʳ 0F)
    lsplitSourceFrame : SourceReduction.Frame* lsplitArity
    lsplitSourceFrameFactor :
      E ≡ SourceReduction._⋯ᶠ*_ lsplitSourceFrame lsplitRenaming
    lsplitSourceResidual : Typed.Proc lsplitArity
    lsplitSourceResidualFactor :
      P ≡ Typed._⋯ₚ_ lsplitSourceResidual lsplitRenaming

    lsplitThread : 𝔽 m
    lsplitChannel : 𝔽 n
    lsplitSide : 𝔽 2
    lsplitOpen : SoupReduction.is-open (Soup.channels C) lsplitChannel

    lsplitFrame : SoupExpression.Frame* (2 *ℕ n)
    lsplitHandleLeft : SoupTerm.Tm (2 *ℕ n)
    lsplitHandleEnd : 𝔽 (2 *ℕ n)
    lsplitHandleRight : SoupTerm.Tm (2 *ℕ n)
    lsplitSelected :
      lookup (Soup.threads C) lsplitThread ≡
      SoupExpression._[_]* lsplitFrame
        (SoupTerm._·¹_ (SoupTerm.K (SoupTerm.`lsplit s))
          (Translation.chanTriple
            (lsplitHandleLeft , lsplitHandleEnd , lsplitHandleRight)))

    lsplitReplacement : Soup.Thread n
    lsplitReplacement≡ :
      lsplitReplacement ≡
      SoupExpression._[_]* lsplitFrame
        (SoupTerm._⊗_
          (Translation.chanTriple
            (lsplitHandleLeft , lsplitHandleEnd , SoupTerm.*))
          (Translation.chanTriple
            (SoupTerm.* , lsplitHandleEnd , lsplitHandleRight)))

    lsplitConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.replaceAt
            (Soup.threads C) lsplitThread lsplitReplacement))

open LSplitStep public

lsplit-step :
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
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P) →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C →
  LSplitStep {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
    {E = E} {P = P}
    (Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ P
           (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}))))
    sigma ambientChannel ambientThread C
lsplit-step {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
  {s = s} {E = E} {P = P} {logicalChannels = channel ∷ bodyChannels}
  {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
  Γ-S ⊢P Vsigma image
  with lsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁}
         {s = s} {E = E} {P = P} ⊢P
... | kk , rho , skip , E₀ , Eeq , P₀ , Peq = record
  { lsplitArity = kk
  ; lsplitRenaming = rho
  ; lsplitSkip = skip
  ; lsplitSourceFrame = E₀
  ; lsplitSourceFrameFactor = Eeq
  ; lsplitSourceResidual = P₀
  ; lsplitSourceResidualFactor = Peq
  ; lsplitThread = LSplitCore.coreThread core
  ; lsplitChannel = LSplitCore.coreChannel core
  ; lsplitSide = LSplitCore.coreSide core
  ; lsplitOpen = LSplitCore.coreOpen core
  ; lsplitFrame = LSplitCore.coreFrame core
  ; lsplitHandleLeft = LSplitCore.coreHandleLeft core
  ; lsplitHandleEnd = LSplitCore.coreHandleEnd core
  ; lsplitHandleRight = LSplitCore.coreHandleRight core
  ; lsplitSelected = LSplitCore.coreSelected core
  ; lsplitReplacement = LSplitCore.coreReplacement core
  ; lsplitReplacement≡ = LSplitCore.coreReplacement≡ core
  ; lsplitConfigStep =
      subst
        (λ Z →
          ConfigStep Z sigma aC aT C
            (Soup.config (Soup.channels C)
              (SoupReduction.replaceAt
                (Soup.threads C)
                (LSplitCore.coreThread core)
                (LSplitCore.coreReplacement core))))
        stepEq
        (LSplitCore.coreConfigStep core)
  }
  where
  module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

  lwk : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k) →
        𝔽 (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B + k)
  lwk = 𝐒.lwk {q} {b₁} {k}

  redexEq :
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P)
    ≡
    Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₀ rho)
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P₀ rho))
  redexEq =
    cong₂
      (λ E′ P′ →
        Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
          (Typed.⟪ SourceReduction._[_]* E′
                     (Source._·¹_ (Source.K (Source.`lsplit s))
                       (Source.` (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
           Typed.∥ P′))
      Eeq Peq

  redexImage =
    channels-resp
      (cast-cons (cong Translation.channelCount Peq) channel bodyChannels)
      (proc-image redexEq image)

  core :
    LSplitCore {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B} {s = s}
      {rho = rho} {E₀ = E₀} {P₀ = P₀}
      (Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_
                     (SourceReduction._⋯ᶠ*_ E₀ rho) lwk)
                   (Source._⊗_
                     (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                     (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
         Typed.∥ (Typed._⋯ₚ_ P₀ (λ y → lwk (rho y)))))
      sigma aC aT C
  core =
    lsplit-worker {rho = rho} {E₀ = E₀} {P₀ = P₀} {channel = channel}
      skip Vsigma redexImage

  stepEq :
    Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_
                   (SourceReduction._⋯ᶠ*_ E₀ rho) lwk)
                 (Source._⊗_
                   (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                   (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P₀ (λ y → lwk (rho y))))
    ≡
    Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E lwk)
                 (Source._⊗_
                   (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                   (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
       Typed.∥ (Typed._⋯ₚ_ P lwk))
  stepEq =
    cong₂
      (λ E′ P′ →
        Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
          (Typed.⟪ SourceReduction._[_]*
                     (SourceReduction._⋯ᶠ*_ E′ lwk)
                     (Source._⊗_
                       (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                       (Source.` (𝐒.atk {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
           Typed.∥ P′))
      (sym Eeq)
      (sym (Typed.fusionₚ P₀ rho lwk)
       ■ cong (λ Z → Typed._⋯ₚ_ Z lwk) (sym Peq))

U-lsplit-local :
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
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P) →
  ValueEnv sigma →
  LocalImage
    (Typed.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`lsplit s))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc b₁} {k} (q ↑ʳ 0F)))) ⟫
       Typed.∥ P))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E
                   (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc (suc b₁)} {k} (q ↑ʳ 0F)))
                   (Source.`
                     (Source.SplitRenamings.atk B₁ B₂ (sum B)
                       {q + suc (suc b₁)} {k} (q ↑ʳ 1F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ P
           (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k}))))
    sigma ambientChannel ambientThread C
U-lsplit-local {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
  {s = s} {E = E} {P = P} {logicalChannels = channel ∷ bodyChannels}
  {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
  Γ-S ⊢P Vsigma image
  = configStep⇒localStep
      (LSplitStep.lsplitConfigStep
        (lsplit-step {k = k} {q = q} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {B = B}
          {s = s} {E = E} {P = P}
          {logicalChannels = channel ∷ bodyChannels}
          {sigma = sigma} {ambientChannel = aC} {ambientThread = aT} {C = C}
          Γ-S ⊢P Vsigma image))
