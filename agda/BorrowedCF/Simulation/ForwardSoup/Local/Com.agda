-- | Phase 3, leaf rule `R-Com` (`ForwardSoup/PLAN.md`, §4, Phase 3).
--
--   The source redex holds a sender and a receiver on one channel under a
--   restriction, beside a residual process `P`:
--
--     ν (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂)
--       ((⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ ` 0F) ]* ⟫
--         ∥ ⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ ` (…) ]* ⟫) ∥ (P ⋯ₚ wkρ))
--       ─→ₚ
--     ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
--       ((⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ e ]* ⟫) ∥ P)
--
--   The shape is the one of `Local/Choice.agda` — `res-split` → `par-split`
--   → `UB-head` on both handles → `RUS-Com` → `par-join`/`res-join` →
--   `identity-step` — with three differences:
--
--     1. both binder groups shrink by one, so the body environments of redex
--        and reduct differ; `envCoh` (built from `wkₚ-A`/`wkₚ-B`/`wkₚ-C` and
--        `UB-env-drop`) relates them, and `UB-flags-drop` shows that the bound
--        channel keeps its content;
--     2. the two evaluation frames are weakened by `wkρ`, so the reduct
--        threads are reached with `Tᶠ*-plug-ren-coh` rather than by plugging
--        the very same frame;
--     3. the residual process is renamed, so its image travels along
--        `residual-image`, and the channel bookkeeping of `par-join` goes
--        through `ownedChannels-transport`.
module BorrowedCF.Simulation.ForwardSoup.Local.Com where

open import Data.Nat.ListAction using (sum)
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

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*; T[_]-Value)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads; bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.Local.BindDrop
  using ( lift*-↑ˡ; lift*-↑ʳ; split-left; split-right; split-ambient
        ; Ub-drop; UB-env-drop; UB-flags-drop
        )
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value; T-ren-coh; Tᶠ*-plug-ren-coh)
open import BorrowedCF.Simulation.ForwardSoup.Local.Residual
  using (residual-image; ownedChannels-transport; ownedChannels-transport⁻)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (transportChannels)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ; UB-head; processCount-rename)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

------------------------------------------------------------------------
-- Arithmetic of the communication weakening `wkₚ a c`.
--
--   `wkₚ a c` inserts one variable at the head of each of the two binder
--   blocks of the redex.  The three lemmas below say where it sends the three
--   kinds of variable: the ones bound by the first block, the ones bound by
--   the second, and the ambient ones.

private
  wkₚ-A :
    ∀ a c {k} (v : 𝔽 a) →
    Source.wkₚ {n = k} a c ((v ↑ˡ c) ↑ˡ k) ≡ ((Fin.suc v ↑ˡ suc c) ↑ˡ k)
  wkₚ-A a c {k} v =
    cong (λ z → cast₂ (Source._↑*_ Source.weakenᵣ (suc a) z)) step₁
    ■ cong cast₂ step₂
    ■ step₃
    where
    cast₁ : 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
    cast₁ = Fin.cast (cong suc (+-assoc a c k))

    cast₂ : 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) k))

    i : 𝔽 (a + c + k)
    i = (v ↑ˡ c) ↑ˡ k

    toℕi : Fin.toℕ i ≡ Fin.toℕ v
    toℕi = Fin.toℕ-↑ˡ (v ↑ˡ c) k ■ Fin.toℕ-↑ˡ v c

    step₁ : cast₁ (Fin.suc i) ≡ Fin.suc v ↑ˡ (c + k)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
       ■ cong suc toℕi
       ■ sym (Fin.toℕ-↑ˡ (Fin.suc v) (c + k)))

    step₂ :
      Source._↑*_ Source.weakenᵣ (suc a) (Fin.suc v ↑ˡ (c + k)) ≡
      Fin.suc v ↑ˡ suc (c + k)
    step₂ = lift*-↑ˡ Source.weakenᵣ (suc a) (Fin.suc v)

    step₃ :
      cast₂ (Fin.suc v ↑ˡ suc (c + k)) ≡ ((Fin.suc v ↑ˡ suc c) ↑ˡ k)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) k))
         (Fin.suc v ↑ˡ suc (c + k))
       ■ Fin.toℕ-↑ˡ (Fin.suc v) (suc (c + k))
       ■ sym (Fin.toℕ-↑ˡ (Fin.suc v ↑ˡ suc c) k
              ■ Fin.toℕ-↑ˡ (Fin.suc v) (suc c)))

  wkₚ-B :
    ∀ a c {k} (w : 𝔽 c) →
    Source.wkₚ {n = k} a c ((a ↑ʳ w) ↑ˡ k) ≡
    (((suc a) ↑ʳ Fin.suc w) ↑ˡ k)
  wkₚ-B a c {k} w =
    cong (λ z → cast₂ (Source._↑*_ Source.weakenᵣ (suc a) z)) step₁
    ■ cong cast₂ step₂
    ■ step₃
    where
    cast₁ : 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
    cast₁ = Fin.cast (cong suc (+-assoc a c k))

    cast₂ : 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) k))

    i : 𝔽 (a + c + k)
    i = (a ↑ʳ w) ↑ˡ k

    toℕi : Fin.toℕ i ≡ a + Fin.toℕ w
    toℕi = Fin.toℕ-↑ˡ (a ↑ʳ w) k ■ Fin.toℕ-↑ʳ a w

    step₁ : cast₁ (Fin.suc i) ≡ suc a ↑ʳ (w ↑ˡ k)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
       ■ cong suc toℕi
       ■ sym (Fin.toℕ-↑ʳ (suc a) (w ↑ˡ k)
              ■ cong (suc a +_) (Fin.toℕ-↑ˡ w k)))

    step₂ :
      Source._↑*_ Source.weakenᵣ (suc a) (suc a ↑ʳ (w ↑ˡ k)) ≡
      suc a ↑ʳ Fin.suc (w ↑ˡ k)
    step₂ = lift*-↑ʳ Source.weakenᵣ (suc a) (w ↑ˡ k)

    step₃ :
      cast₂ (suc a ↑ʳ Fin.suc (w ↑ˡ k)) ≡ ((suc a ↑ʳ Fin.suc w) ↑ˡ k)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) k))
         (suc a ↑ʳ Fin.suc (w ↑ˡ k))
       ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc (w ↑ˡ k))
       ■ cong (λ t → suc a + suc t) (Fin.toℕ-↑ˡ w k)
       ■ sym (Fin.toℕ-↑ˡ (suc a ↑ʳ Fin.suc w) k
              ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc w)))

  -- The ambient block, which `Com.agda`'s arity-0 version never needed.
  wkₚ-C :
    ∀ a c {k} (y : 𝔽 k) →
    Source.wkₚ {n = k} a c ((a + c) ↑ʳ y) ≡ ((suc a + suc c) ↑ʳ y)
  wkₚ-C a c {k} y =
    cong (λ z → cast₂ (Source._↑*_ Source.weakenᵣ (suc a) z)) step₁
    ■ cong cast₂ step₂
    ■ step₃
    where
    cast₁ : 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
    cast₁ = Fin.cast (cong suc (+-assoc a c k))

    cast₂ : 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) k))

    i : 𝔽 (a + c + k)
    i = (a + c) ↑ʳ y

    toℕi : Fin.toℕ i ≡ a + c + Fin.toℕ y
    toℕi = Fin.toℕ-↑ʳ (a + c) y

    step₁ : cast₁ (Fin.suc i) ≡ suc a ↑ʳ (c ↑ʳ y)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
       ■ cong suc toℕi
       ■ cong suc (+-assoc a c (Fin.toℕ y))
       ■ sym (Fin.toℕ-↑ʳ (suc a) (c ↑ʳ y)
              ■ cong (suc a +_) (Fin.toℕ-↑ʳ c y)))

    step₂ :
      Source._↑*_ Source.weakenᵣ (suc a) (suc a ↑ʳ (c ↑ʳ y)) ≡
      suc a ↑ʳ Fin.suc (c ↑ʳ y)
    step₂ = lift*-↑ʳ Source.weakenᵣ (suc a) (c ↑ʳ y)

    step₃ :
      cast₂ (suc a ↑ʳ Fin.suc (c ↑ʳ y)) ≡ ((suc a + suc c) ↑ʳ y)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) k))
         (suc a ↑ʳ Fin.suc (c ↑ʳ y))
       ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc (c ↑ʳ y))
       ■ cong (λ t → suc a + suc t) (Fin.toℕ-↑ʳ c y)
       ■ sym (+-assoc (suc a) (suc c) (Fin.toℕ y))
       ■ sym (Fin.toℕ-↑ʳ (suc a + suc c) y))

------------------------------------------------------------------------
-- The leaf.

record ComStep
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {E₁ E₂ :
    SourceReduction.Frame*
      (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {e : Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n)
      (Translation.channelCount
        (Typed._⋯ₚ_ P
          (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂))))}
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m)
  (image :
    LocalImage
      (Typed.ν (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂)
        ((Typed.⟪ SourceReduction._[_]*
                    (SourceReduction._⋯ᶠ*_ E₁
                      (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                    (Source._·¹_ (Source.K Source.`send)
                      (Source._⊗_
                        (Source._⋯_ e
                          (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                        (Source.` 0F))) ⟫
          Typed.∥
          Typed.⟪ SourceReduction._[_]*
                    (SourceReduction._⋯ᶠ*_ E₂
                      (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                    (Source._·¹_ (Source.K Source.`recv)
                      (Source.` (Source.wkʳ k
                                  (Source.wkˡ (suc (suc b₁) + sum B₁) 0F)))) ⟫)
          Typed.∥
          (Typed._⋯ₚ_ P
            (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))))
      (channel ∷ bodyChannels) sigma ambientChannel ambientThread C)
  (P′ : Typed.Proc k) : Set where
  field
    comSender comReceiver : 𝔽 m
    comSenderSlot :
      threadEmbedding (par-split-left (res-split-image image)) 0F ≡
      just comSender
    comReceiverSlot :
      threadEmbedding (par-split-left (res-split-image image)) 1F ≡
      just comReceiver
    comSender≢Receiver : comSender ≢ comReceiver

    comChannel : 𝔽 n
    comSide₁ comSide₂ : 𝔽 2
    comOpposite : SoupReduction.Opposite comSide₁ comSide₂
    comOpen : SoupReduction.is-open (Soup.channels C) comChannel

    comSendFrame comRecvFrame : SoupExpression.Frame* (2 *ℕ n)
    comMessage comSendTail comRecvTail : Soup.Thread n
    comMessageValue : SoupExpression.Value comMessage

    comSelectedSend :
      lookup (Soup.threads C) comSender ≡
      SoupExpression._[_]* comSendFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`send)
          (SoupTerm._⊗_ comMessage
            (SoupTerm._⊗_
              (SoupTerm._⊗_ SoupTerm.*
                (SoupTerm.` (Soup.endpoint comChannel comSide₁)))
              comSendTail)))
    comSelectedRecv :
      lookup (Soup.threads C) comReceiver ≡
      SoupExpression._[_]* comRecvFrame
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`recv)
          (SoupTerm._⊗_
            (SoupTerm._⊗_ SoupTerm.*
              (SoupTerm.` (Soup.endpoint comChannel comSide₂)))
            comRecvTail))

    comConfigStep :
      ConfigStep P′ sigma ambientChannel ambientThread C
        (Soup.config (Soup.channels C)
          (SoupReduction.replaceTwo (Soup.threads C)
            comSender (SoupExpression._[_]* comSendFrame SoupTerm.*)
            comReceiver (SoupExpression._[_]* comRecvFrame comMessage)))

open ComStep public

com-step :
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {E₁ E₂ :
    SourceReduction.Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {e : Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {channel : OrientedChannel n}
  {bodyChannels :
    Vec (OrientedChannel n)
      (Translation.channelCount
        (Typed._⋯ₚ_ P
          (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂))))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (image : LocalImage
    (Typed.ν (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]*
                  (SourceReduction._⋯ᶠ*_ E₁
                    (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                  (Source._·¹_ (Source.K Source.`send)
                    (Source._⊗_
                      (Source._⋯_ e
                        (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                      (Source.` 0F))) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]*
                  (SourceReduction._⋯ᶠ*_ E₂
                    (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                  (Source._·¹_ (Source.K Source.`recv)
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc (suc b₁) + sum B₁) 0F)))) ⟫)
        Typed.∥
        (Typed._⋯ₚ_ P
         (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))))
    (channel ∷ bodyChannels) sigma ambientChannel ambientThread C) →
  ValueEnv sigma →
  SourceReduction.Value e →
  ComStep
    {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
    {P = P} {E₁ = E₁} {E₂ = E₂} {e = e}
    {channel = channel} {bodyChannels = bodyChannels}
    sigma ambientChannel ambientThread C image
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁ Source.* ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂ e ⟫)
       Typed.∥ P))
com-step {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
  {B₁ = B₁} {B₂ = B₂} {P = P} {E₁ = E₁} {E₂ = E₂} {e = e}
  {channel = channel} {bodyChannels = bodyChannels} {sigma = sigma}
  {ambientChannel = aC} {ambientThread = aT} {C = C} image Vsigma V =
  dispatch (live-thread left 0F) (live-thread left 1F)
  where
  ----------------------------------------------------------------------
  -- The weakening of the rule.

  wkrho :
    𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k) →
    𝔽 (sum (suc (suc b₁) ∷ B₁) + sum (suc (suc b₂) ∷ B₂) + k)
  wkrho = Source.wkₚ {n = k} (suc b₁ + sum B₁) (suc b₂ + sum B₂)

  ----------------------------------------------------------------------
  -- The bound channel, physically.

  physical : 𝔽 n
  physical = physicalChannel channel

  orientation : Orientation
  orientation = proj₂ channel

  side₁ side₂ : 𝔽 2
  side₁ = orientSide orientation 0F
  side₂ = orientSide orientation 1F

  end₁ end₂ : 𝔽 (2 *ℕ n)
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

  ----------------------------------------------------------------------
  -- The two body environments.

  sourceEnv :
    Translation.Env
      (sum (suc (suc b₁) ∷ B₁) + sum (suc (suc b₂) ∷ B₂) + k) (2 *ℕ n)
  sourceEnv = bindEnv (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂) channel sigma

  targetEnv :
    Translation.Env (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k) (2 *ℕ n)
  targetEnv = bindEnv (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) channel sigma

  Vsource : ValueEnv sourceEnv
  Vsource =
    bindEnv-Value {B₁ = suc (suc b₁) ∷ B₁} {B₂ = suc (suc b₂) ∷ B₂}
      {channel = channel} Vsigma

  Vtarget : ValueEnv targetEnv
  Vtarget =
    bindEnv-Value {B₁ = suc b₁ ∷ B₁} {B₂ = suc b₂ ∷ B₂}
      {channel = channel} Vsigma

  sourceBinder₁ : Translation.Env (sum (suc (suc b₁) ∷ B₁)) (2 *ℕ n)
  sourceBinder₁ =
    proj₁ (Translation.UB[ suc (suc b₁) ∷ B₁ ] end₁
            (SoupTerm.* , end₁ , SoupTerm.*))

  sourceBinder₂ : Translation.Env (sum (suc (suc b₂) ∷ B₂)) (2 *ℕ n)
  sourceBinder₂ =
    proj₁ (Translation.UB[ suc (suc b₂) ∷ B₂ ] end₂
            (SoupTerm.* , end₂ , SoupTerm.*))

  targetBinder₁ : Translation.Env (sum (suc b₁ ∷ B₁)) (2 *ℕ n)
  targetBinder₁ =
    proj₁ (Translation.UB[ suc b₁ ∷ B₁ ] end₁
            (SoupTerm.* , end₁ , SoupTerm.*))

  targetBinder₂ : Translation.Env (sum (suc b₂ ∷ B₂)) (2 *ℕ n)
  targetBinder₂ =
    proj₁ (Translation.UB[ suc b₂ ∷ B₂ ] end₂
            (SoupTerm.* , end₂ , SoupTerm.*))

  ----------------------------------------------------------------------
  -- The redex environment agrees with the reduct environment across `wkρ`:
  -- both binder blocks lose their head variable, the ambient block is
  -- untouched.

  -- The case analysis is factored out: `with`-abstracting `Fin.splitAt` in
  -- the statement of `envCoh` would rewrite its right-hand side too.
  classify :
    (x : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
    (Σ[ v ∈ 𝔽 (sum (suc b₁ ∷ B₁)) ]
       (v ↑ˡ sum (suc b₂ ∷ B₂)) ↑ˡ k ≡ x)
    ⊎ (Σ[ w ∈ 𝔽 (sum (suc b₂ ∷ B₂)) ]
       (sum (suc b₁ ∷ B₁) ↑ʳ w) ↑ˡ k ≡ x)
    ⊎ (Σ[ y ∈ 𝔽 k ]
       (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) ↑ʳ y ≡ x)
  classify x
    with Fin.splitAt (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) x in outer
  ... | inj₂ y =
    inj₂ (inj₂
      (y , split-ambient (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) outer))
  ... | inj₁ z with Fin.splitAt (sum (suc b₁ ∷ B₁)) z in inner
  ...   | inj₁ v =
    inj₁
      (v , split-left (sum (suc b₁ ∷ B₁)) (sum (suc b₂ ∷ B₂)) outer inner)
  ...   | inj₂ w =
    inj₂ (inj₁
      (w , split-right (sum (suc b₁ ∷ B₁)) (sum (suc b₂ ∷ B₂)) outer inner))

  envCoh :
    (x : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
    sourceEnv (wkrho x) ≡ targetEnv x
  envCoh x with classify x
  ... | inj₁ (v , xeq) =
    cong (λ t → sourceEnv (wkrho t)) (sym xeq)
    ■ cong sourceEnv
        (wkₚ-A (sum (suc b₁ ∷ B₁)) (sum (suc b₂ ∷ B₂)) v)
    ■ ++ₛ-lookupˡ (sourceBinder₁ Translation.++ₛ sourceBinder₂) sigma
        (Fin.suc v ↑ˡ sum (suc (suc b₂) ∷ B₂))
    ■ ++ₛ-lookupˡ sourceBinder₁ sourceBinder₂ (Fin.suc v)
    ■ UB-env-drop b₁ B₁ end₁ end₁ SoupTerm.* v
    ■ sym (++ₛ-lookupˡ targetBinder₁ targetBinder₂ v)
    ■ sym (++ₛ-lookupˡ (targetBinder₁ Translation.++ₛ targetBinder₂) sigma
            (v ↑ˡ sum (suc b₂ ∷ B₂)))
    ■ cong targetEnv xeq
  ... | inj₂ (inj₁ (w , xeq)) =
    cong (λ t → sourceEnv (wkrho t)) (sym xeq)
    ■ cong sourceEnv
        (wkₚ-B (sum (suc b₁ ∷ B₁)) (sum (suc b₂ ∷ B₂)) w)
    ■ ++ₛ-lookupˡ (sourceBinder₁ Translation.++ₛ sourceBinder₂) sigma
        (sum (suc (suc b₁) ∷ B₁) ↑ʳ Fin.suc w)
    ■ ++ₛ-lookupʳ sourceBinder₁ sourceBinder₂ (Fin.suc w)
    ■ UB-env-drop b₂ B₂ end₂ end₂ SoupTerm.* w
    ■ sym (++ₛ-lookupʳ targetBinder₁ targetBinder₂ w)
    ■ sym (++ₛ-lookupˡ (targetBinder₁ Translation.++ₛ targetBinder₂) sigma
            (sum (suc b₁ ∷ B₁) ↑ʳ w))
    ■ cong targetEnv xeq
  ... | inj₂ (inj₂ (y , xeq)) =
    cong (λ t → sourceEnv (wkrho t)) (sym xeq)
    ■ cong sourceEnv
        (wkₚ-C (sum (suc b₁ ∷ B₁)) (sum (suc b₂ ∷ B₂)) y)
    ■ ++ₛ-lookupʳ (sourceBinder₁ Translation.++ₛ sourceBinder₂) sigma y
    ■ sym (++ₛ-lookupʳ (targetBinder₁ Translation.++ₛ targetBinder₂) sigma y)
    ■ cong targetEnv xeq

  ----------------------------------------------------------------------
  -- Both handles are the head of their binder group.

  head₁ = UB-head (suc b₁) B₁ end₁ end₁ SoupTerm.* SoupTerm.*
  head₂ = UB-head (suc b₂) B₂ end₂ end₂ SoupTerm.* SoupTerm.*

  tail₁ tail₂ : SoupTerm.Tm (2 *ℕ n)
  tail₁ = proj₁ head₁
  tail₂ = proj₁ head₂

  triple₁ triple₂ : SoupTerm.Tm (2 *ℕ n)
  triple₁ = Translation.chanTriple (SoupTerm.* , end₁ , tail₁)
  triple₂ = Translation.chanTriple (SoupTerm.* , end₂ , tail₂)

  -- The two heads, with their block index pinned down.
  sendHandle : 𝔽 (sum (suc (suc b₁) ∷ B₁))
  sendHandle = 0F

  recvHandle : 𝔽 (sum (suc (suc b₂) ∷ B₂))
  recvHandle = 0F

  handleVar :
    𝔽 (sum (suc (suc b₁) ∷ B₁) + sum (suc (suc b₂) ∷ B₂) + k)
  handleVar =
    Source.wkʳ k (Source.wkˡ (suc (suc b₁) + sum B₁) recvHandle)

  handleEq₁ : sourceEnv 0F ≡ triple₁
  handleEq₁ =
    ++ₛ-lookupˡ (sourceBinder₁ Translation.++ₛ sourceBinder₂) sigma
      (sendHandle ↑ˡ sum (suc (suc b₂) ∷ B₂))
    ■ ++ₛ-lookupˡ sourceBinder₁ sourceBinder₂ sendHandle
    ■ proj₂ head₁

  handleEq₂ : sourceEnv handleVar ≡ triple₂
  handleEq₂ =
    ++ₛ-lookupˡ (sourceBinder₁ Translation.++ₛ sourceBinder₂) sigma
      (Source.wkˡ (suc (suc b₁) + sum B₁) recvHandle)
    ■ ++ₛ-lookupʳ sourceBinder₁ sourceBinder₂ recvHandle
    ■ proj₂ head₂

  ----------------------------------------------------------------------
  -- The bound channel keeps its content: only the head flag of each group
  -- disappears, and `UB-flags-drop` says the flag lists agree.

  bindEq :
    bindChannel (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂) channel ≡
    bindChannel (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) channel
  bindEq =
    cong₂
      (λ flags₁ flags₂ →
        orientChannel orientation (true , flags₁ , flags₂))
      (UB-flags-drop b₁ B₁ end₁ end₁ SoupTerm.* SoupTerm.*)
      (UB-flags-drop b₂ B₂ end₂ end₂ SoupTerm.* SoupTerm.*)

  ----------------------------------------------------------------------
  -- The source terms.

  sendRedex recvRedex :
    Source.Tm (sum (suc (suc b₁) ∷ B₁) + sum (suc (suc b₂) ∷ B₂) + k)
  sendRedex =
    Source._·¹_ (Source.K Source.`send)
      (Source._⊗_ (Source._⋯_ e wkrho) (Source.` 0F))
  recvRedex =
    Source._·¹_ (Source.K Source.`recv) (Source.` handleVar)

  owner₁ owner₂ :
    Source.Tm (sum (suc (suc b₁) ∷ B₁) + sum (suc (suc b₂) ∷ B₂) + k)
  owner₁ = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E₁ wkrho) sendRedex
  owner₂ = SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E₂ wkrho) recvRedex

  target₁ target₂ :
    Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)
  target₁ = SourceReduction._[_]* E₁ Source.*
  target₂ = SourceReduction._[_]* E₂ e

  reduct : Typed.Proc k
  reduct =
    Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫) Typed.∥ P)

  ----------------------------------------------------------------------
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
    aT ∪ᵖ ownedThreads (threadEmbedding body ∘ (2 ↑ʳ_))

  ambientThreadRight : 𝔽 m → Set
  ambientThreadRight =
    aT ∪ᵖ
    ownedThreads
      (threadEmbedding body ∘
        (_↑ˡ Translation.processCount (Typed._⋯ₚ_ P wkrho)))

  ----------------------------------------------------------------------
  -- The soup frames and the transmitted value.

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = Tᶠ*[ SourceReduction._⋯ᶠ*_ E₁ wkrho ] {σ = sourceEnv} Vsource
  F₂ = Tᶠ*[ SourceReduction._⋯ᶠ*_ E₂ wkrho ] {σ = sourceEnv} Vsource

  message : Soup.Thread n
  message = Translation.T[ e ] targetEnv

  Vmessage : SoupExpression.Value message
  Vmessage = T[_]-Value V Vtarget

  messageEq : Translation.T[ Source._⋯_ e wkrho ] sourceEnv ≡ message
  messageEq = T-ren-coh e wkrho sourceEnv targetEnv envCoh

  expected₁ expected₂ : Soup.Thread n
  expected₁ = Translation.T[ owner₁ ] sourceEnv
  expected₂ = Translation.T[ owner₂ ] sourceEnv

  plugged₁ plugged₂ : Soup.Thread n
  plugged₁ = SoupExpression._[_]* F₁ SoupTerm.*
  plugged₂ = SoupExpression._[_]* F₂ message

  ----------------------------------------------------------------------
  -- The bound channel is open.

  openEq : proj₁ (lookup (Soup.channels C) physical) ≡ true
  openEq = cong proj₁ chanEq ■ open-orient orientation _

  ----------------------------------------------------------------------
  -- The case analysis on the two owner threads.

  dispatch :
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 0F) expected₁ →
    OptionalThreadImage {n = n} (Soup.threads C)
      (threadEmbedding left 1F) expected₂ →
    ComStep
      {channel = channel} {bodyChannels = bodyChannels}
      sigma aC aT C image reduct

  dispatch (omitted slotEq expectedEq) _ =
    ⊥-elim
      (plug-not-K F₁
        (sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₁ wkrho)
               {e = sendRedex} Vsource)
         ■ expectedEq))
  dispatch (present _ _ _) (omitted slotEq expectedEq) =
    ⊥-elim
      (plug-not-K F₂
        (sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₂ wkrho)
               {e = recvRedex} Vsource)
         ■ expectedEq))

  dispatch (present j slotEq₁ lookupEq₁) (present l slotEq₂ lookupEq₂) =
    record
      { comSender = j
      ; comReceiver = l
      ; comSenderSlot = slotEq₁
      ; comReceiverSlot = slotEq₂
      ; comSender≢Receiver = j≢l
      ; comChannel = physical
      ; comSide₁ = side₁
      ; comSide₂ = side₂
      ; comOpposite = orientSide-opposite orientation
      ; comOpen = openEq
      ; comSendFrame = F₁
      ; comRecvFrame = F₂
      ; comMessage = message
      ; comSendTail = tail₁
      ; comRecvTail = tail₂
      ; comMessageValue = Vmessage
      ; comSelectedSend = selected₁
      ; comSelectedRecv = selected₂
      ; comConfigStep =
          identity-config-step soupStep (λ _ _ → refl) ambientThreadsUnchanged
            (res-join joined (chanEq ■ bindEq) notAmb)
      }
    where
    j≢l : j ≢ l
    j≢l eq
      with threadEmbedding-injective left slotEq₁
             (slotEq₂ ■ cong just (sym eq))
    ... | ()

    ------------------------------------------------------------------
    -- The step.

    selected₁ :
      lookup (Soup.threads C) j ≡
      SoupExpression._[_]* F₁
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`send)
          (SoupTerm._⊗_ message triple₁))
    selected₁ =
      lookupEq₁
      ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₁ wkrho)
          {e = sendRedex} Vsource
      ■ cong₂
          (λ msg handle →
            SoupExpression._[_]* F₁
              (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`send)
                (SoupTerm._⊗_ msg handle)))
          messageEq handleEq₁

    selected₂ :
      lookup (Soup.threads C) l ≡
      SoupExpression._[_]* F₂
        (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`recv) triple₂)
    selected₂ =
      lookupEq₂
      ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₂ wkrho)
          {e = recvRedex} Vsource
      ■ cong
          (λ handle →
            SoupExpression._[_]* F₂
              (SoupTerm._·¹_ (SoupTerm.K SoupTerm.`recv) handle))
          handleEq₂

    targetThreads : Vec (Soup.Thread n) m
    targetThreads =
      SoupReduction.replaceTwo (Soup.threads C) j plugged₁ l plugged₂

    targetConfig : Soup.Config n m
    targetConfig = Soup.config (Soup.channels C) targetThreads

    soupStep : C SoupReduction.─→ₚ targetConfig
    soupStep =
      SoupReduction.RUS-Com
        {cs = Soup.channels C} {ts = Soup.threads C}
        j l physical side₁ side₂ F₁ F₂
        {e = message}
        {e₁′ = tail₁} {e₂′ = tail₂}
        j≢l (orientSide-opposite orientation) openEq Vmessage
        selected₁ selected₂

    ------------------------------------------------------------------
    -- The frame is untouched.

    ambientThreadsUnchanged :
      (l′ : 𝔽 m) → aT l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    ambientThreadsUnchanged l′ ambient =
      V.lookup∘updateAt′ l′ l
        (λ eq → thread-not-ambient left slotEq₂ (inj₁ (subst aT eq ambient)))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → thread-not-ambient left slotEq₁ (inj₁ (subst aT eq ambient)))
          (Soup.threads C)

    ------------------------------------------------------------------
    -- The image of the two owners after the step.

    targetThread₁ : lookup targetThreads j ≡ Translation.T[ target₁ ] targetEnv
    targetThread₁ =
      V.lookup∘updateAt′ j l j≢l
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt j (Soup.threads C)
      ■ Tᶠ*-plug-ren-coh E₁ wkrho sourceEnv targetEnv Vsource Vtarget
          envCoh SoupTerm.*
      ■ sym (T[_]-plugᶠ* E₁ {e = Source.*} Vtarget)

    targetThread₂ : lookup targetThreads l ≡ Translation.T[ target₂ ] targetEnv
    targetThread₂ =
      V.lookup∘updateAt l (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ Tᶠ*-plug-ren-coh E₂ wkrho sourceEnv targetEnv Vsource Vtarget
          envCoh message
      ■ sym (T[_]-plugᶠ* E₂ {e = e} Vtarget)

    targetGarbageThread :
      (l′ : 𝔽 m) → OptionalOutside (threadEmbedding left) l′ →
      ¬ ambientThreadLeft l′ →
      lookup targetThreads l′ ≡ SoupTerm.K Source.`unit
    targetGarbageThread l′ outside notAmbient =
      V.lookup∘updateAt′ l′ l
        (λ eq → outside 1F (slotEq₂ ■ cong just (sym eq)))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → outside 0F (slotEq₁ ■ cong just (sym eq)))
          (Soup.threads C)
      ■ garbage-thread left l′ outside notAmbient

    leftImage :
      LocalImage
        (Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫)
        [] targetEnv ambientChannelLeft ambientThreadLeft targetConfig
    leftImage = record
      { channelEmbedding-injective = channelEmbedding-injective left
      ; threadEmbedding = threadEmbedding left
      ; threadEmbedding-injective = threadEmbedding-injective left
      ; channel-not-ambient = λ ()
      ; thread-not-ambient = thread-not-ambient left
      ; live-channel = λ ()
      ; live-thread = λ where
          0F → present j slotEq₁ targetThread₁
          1F → present l slotEq₂ targetThread₂
      ; garbage-channel = λ i outside notAmbient →
          garbage-channel left i outside notAmbient
      ; garbage-thread = targetGarbageThread
      }

    ------------------------------------------------------------------
    -- The residual process: both rewritten threads are ambient for it, and
    -- its image travels from `P ⋯ₚ wkρ` to `P`.

    threadsUnchangedRight :
      (l′ : 𝔽 m) → ¬ ambientThreadRight l′ →
      lookup targetThreads l′ ≡ lookup (Soup.threads C) l′
    threadsUnchangedRight l′ notAmbient =
      V.lookup∘updateAt′ l′ l
        (λ eq → notAmbient (inj₂ (1F , (slotEq₂ ■ cong just (sym eq)))))
        (SoupReduction.replaceAt (Soup.threads C) j plugged₁)
      ■ V.lookup∘updateAt′ l′ j
          (λ eq → notAmbient (inj₂ (0F , (slotEq₁ ■ cong just (sym eq)))))
          (Soup.threads C)

    rightImage =
      config-resp {C = C} {C′ = targetConfig}
        (λ _ _ → refl) threadsUnchangedRight right

    residual = residual-image {P = P} {rho = wkrho} envCoh rightImage

    processEq :
      Translation.processCount (Typed._⋯ₚ_ P wkrho) ≡
      Translation.processCount P
    processEq = processCount-rename P wkrho

    ------------------------------------------------------------------
    -- Re-assembling the frame.

    joined :
      LocalImage
        ((Typed.⟪ target₁ ⟫ Typed.∥ Typed.⟪ target₂ ⟫) Typed.∥ P)
        (transportChannels P wkrho bodyChannels) targetEnv
        (aC ∪ᵖ singletonᵖ physical) aT targetConfig
    joined =
      par-join leftImage residual
        (λ i →
          inj₂
            (ownedChannels-transport {P = P} {rho = wkrho}
              {channels = bodyChannels} _ (i , refl)))
        (λ {i} {l′} embedded →
          inj₂ (Fin.cast (sym processEq) i , embedded))
        (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
        (λ i → λ where
          (inj₁ ambient) → inj₁ ambient
          (inj₂ owned) →
            inj₂
              (ownedChannels-transport⁻ {P = P} {rho = wkrho}
                {channels = bodyChannels} i owned))
        (λ l′ → λ where
          (inj₁ ambient) → inj₁ ambient
          (inj₂ (i , owned)) →
            inj₂
              ( Fin.cast processEq i
              , ( cong (λ t → threadEmbedding rightImage t)
                    (Fin.cast-involutive (sym processEq) processEq i)
                ■ owned
                )
              ))

U-com-local :
  {k n m b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {E₁ E₂ :
    SourceReduction.Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {e : Source.Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)}
  {logicalChannels :
    Vec (OrientedChannel n)
      (suc
        (Translation.channelCount
          (Typed._⋯ₚ_ P
            (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  ValueEnv sigma →
  SourceReduction.Value e →
  LocalImage
    (Typed.ν (suc (suc b₁) ∷ B₁) (suc (suc b₂) ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]*
                  (SourceReduction._⋯ᶠ*_ E₁
                    (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                  (Source._·¹_ (Source.K Source.`send)
                    (Source._⊗_
                      (Source._⋯_ e
                        (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                      (Source.` 0F))) ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]*
                  (SourceReduction._⋯ᶠ*_ E₂
                    (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))
                  (Source._·¹_ (Source.K Source.`recv)
                    (Source.` (Source.wkʳ k
                                (Source.wkˡ (suc (suc b₁) + sum B₁) 0F)))) ⟫)
       Typed.∥
       (Typed._⋯ₚ_ P
         (Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)))))
    logicalChannels sigma ambientChannel ambientThread C →
  LocalStep
    (Typed.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((Typed.⟪ SourceReduction._[_]* E₁ Source.* ⟫
        Typed.∥
        Typed.⟪ SourceReduction._[_]* E₂ e ⟫)
       Typed.∥ P))
    sigma ambientChannel ambientThread C
U-com-local {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
  {B₁ = B₁} {B₂ = B₂} {P = P} {E₁ = E₁} {E₂ = E₂} {e = e}
  {logicalChannels = channel ∷ bodyChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  Vsigma V image =
  configStep⇒localStep
    (comConfigStep
      (com-step {k = k} {n = n} {m = m} {b₁ = b₁} {b₂ = b₂}
        {B₁ = B₁} {B₂ = B₂} {P = P} {E₁ = E₁} {E₂ = E₂}
        {e = e} {channel = channel} {bodyChannels = bodyChannels}
        {sigma = sigma}
        {ambientChannel = ambientChannel} {ambientThread = ambientThread}
        {C = C} image Vsigma V))
