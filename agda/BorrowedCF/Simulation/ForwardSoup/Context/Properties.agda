module BorrowedCF.Simulation.ForwardSoup.Context.Properties where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Context
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-Value; UB-Value)
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression

open Nat.Variables

Focus : ℕ → ℕ → ℕ → Set
Focus channelCount arity c =
  Vec (OrientedChannel c) channelCount ×
  Translation.Env arity (2 *ℕ c)

focus :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)) →
  Translation.Env n (2 *ℕ c) →
  Focus (Translation.channelCount P) k c
focus hole P channels sigma = channels , sigma
focus (par context Q) P channels sigma =
  focus context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma
focus (bind B₁ B₂ context) P (channel ∷ channels) sigma
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)

focusChannels :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)) →
  Translation.Env n (2 *ℕ c) →
  Vec (OrientedChannel c) (Translation.channelCount P)
focusChannels context P channels sigma =
  proj₁ (focus context P channels sigma)

focusEnv :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P))) →
  Translation.Env n (2 *ℕ c) →
  Translation.Env k (2 *ℕ c)
focusEnv context P channels sigma =
  proj₂ (focus context P channels sigma)

focusEnv-Value :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  {sigma : Translation.Env n (2 *ℕ c)} →
  ValueEnv sigma →
  ValueEnv (focusEnv context P channels sigma)
focusEnv-Value hole P channels Vsigma = Vsigma
focusEnv-Value (par context Q) P channels Vsigma =
  focusEnv-Value context P
    (V.take (Translation.channelCount (plug context P)) channels) Vsigma
focusEnv-Value (bind B₁ B₂ context) P (channel ∷ channels) Vsigma
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
         in ub₁
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
         in ub₂
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focusEnv-Value context P channels
    (++ₛ-Value (++ₛ-Value Vsigma₁ Vsigma₂) Vsigma)
  where
  Vsigma₁ : ValueEnv sigma₁
  Vsigma₁ x = subst SoupExpression.Value
    (cong (λ result → proj₁ result x) ub₁)
    (UB-Value B₁ (physicalEndpoint channel zero)
      {e₁ = SoupTerm.*} {e₂ = SoupTerm.*}
      {c = physicalEndpoint channel zero}
      SoupExpression.V-K SoupExpression.V-K x)

  Vsigma₂ : ValueEnv sigma₂
  Vsigma₂ x = subst SoupExpression.Value
    (cong (λ result → proj₁ result x) ub₂)
    (UB-Value B₂ (physicalEndpoint channel (suc zero))
      {e₁ = SoupTerm.*} {e₂ = SoupTerm.*}
      {c = physicalEndpoint channel (suc zero)}
      SoupExpression.V-K SoupExpression.V-K x)

focus-logical-channel :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.channelCount P)) →
  lookup channels (channelInContext context P i) ≡
  lookup (focusChannels context P channels sigma) i
focus-logical-channel hole P channels sigma i = refl
focus-logical-channel (par context Q) P channels sigma i =
  cong
    (λ cs → lookup cs
      (channelInContext context P i ↑ˡ Translation.channelCount Q))
    (sym (V.take++drop≡id
      (Translation.channelCount (plug context P)) channels)) ■
  V.lookup-++ˡ
    (V.take (Translation.channelCount (plug context P)) channels)
    (V.drop (Translation.channelCount (plug context P)) channels)
    (channelInContext context P i) ■
  focus-logical-channel context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma i
focus-logical-channel (bind B₁ B₂ context) P
  (channel ∷ channels) sigma i
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus-logical-channel context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) i

focus-channel :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.channelCount P)) →
  lookup (proj₁ (flattenOriented (plug context P) channels sigma))
    (channelInContext context P i) ≡
  lookup (proj₁ (flattenOriented P
    (focusChannels context P channels sigma)
    (focusEnv context P channels sigma))) i
focus-channel hole P channels sigma i = refl
focus-channel (par context Q) P channels sigma i
  with flattenOriented (plug context P)
         (V.take (Translation.channelCount (plug context P)) channels) sigma
         in flatP
     | flattenOriented Q
         (V.drop (Translation.channelCount (plug context P)) channels) sigma
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ =
  V.lookup-++ˡ channelsP channelsQ (channelInContext context P i) ■
  sym (cong
    (λ result → lookup (proj₁ result) (channelInContext context P i))
    flatP) ■
  focus-channel context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma i
focus-channel (bind B₁ B₂ context) P (channel ∷ channels) sigma i
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus-channel context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) i

focus-thread :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.processCount P)) →
  lookup (proj₂ (flattenOriented (plug context P) channels sigma))
    (threadInContext context P i) ≡
  lookup (proj₂ (flattenOriented P
    (focusChannels context P channels sigma)
    (focusEnv context P channels sigma))) i
focus-thread hole P channels sigma i = refl
focus-thread (par context Q) P channels sigma i
  with flattenOriented (plug context P)
         (V.take (Translation.channelCount (plug context P)) channels) sigma
         in flatP
     | flattenOriented Q
         (V.drop (Translation.channelCount (plug context P)) channels) sigma
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ =
  V.lookup-++ˡ threadsP threadsQ (threadInContext context P i) ■
  sym (cong
    (λ result → lookup (proj₂ result) (threadInContext context P i))
    flatP) ■
  focus-thread context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma i
focus-thread (bind B₁ B₂ context) P (channel ∷ channels) sigma i
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus-thread context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) i

focus-image :
  {P : Typed.Proc k} {context : ProcessContext k n}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (plug context P) channels sigma
    ambientChannel ambientThread C →
  LocalImage P
    (focusChannels context P channels sigma)
    (focusEnv context P channels sigma)
    (λ _ → ⊤) (λ _ → ⊤) C
focus-image {P = P} {context = context} {channels = channels}
  {sigma = sigma} {C = C} image = record
  { channelEmbedding-injective = λ {i} {j} equal →
      channelInContext-injective context P
        (channelEmbedding-injective image
          (cong physicalChannel (focus-logical-channel context P channels sigma i) ■
           equal ■
           cong physicalChannel
             (sym (focus-logical-channel context P channels sigma j))))
  ; threadEmbedding =
      threadEmbedding image ∘ threadInContext context P
  ; threadEmbedding-injective = λ equalᵢ equalⱼ →
      threadInContext-injective context P
        (threadEmbedding-injective image equalᵢ equalⱼ)
  ; live-channel = λ i →
      cong (lookup (Soup.channels C))
        (sym (cong physicalChannel
          (focus-logical-channel context P channels sigma i))) ■
      live-channel image (channelInContext context P i) ■
      focus-channel context P channels sigma i
  ; live-thread = λ i →
      case live-thread image (threadInContext context P i) of λ where
        (present l embedded live) →
          present l embedded
            (live ■ focus-thread context P channels sigma i)
        (omitted omittedEq unitEq) →
          omitted omittedEq
            (sym (focus-thread context P channels sigma i) ■ unitEq)
  ; garbage-channel = λ _ _ notAmbient →
      ⊥-elim (notAmbient tt)
  ; garbage-thread = λ _ _ notAmbient →
      ⊥-elim (notAmbient tt)
  }
