module BorrowedCF.Simulation.ForwardSoup.LocalImage.Commutation where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Renaming
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (untransportChannels)

open Nat.Variables
open Fin.Patterns

private variable a b o : ℕ

-- Environment coherence for the associativity swap: reassociating the two
-- binder blocks of nested restrictions transports the ambient environment
-- exactly along `assocSwapᵣ`.
assocSwap-coherent :
  (left : Translation.Env a o)
  (right : Translation.Env b o)
  (ambient : Translation.Env n o)
  (x : 𝔽 (a + (b + n))) →
  (right Translation.++ₛ (left Translation.++ₛ ambient))
    (Source.assocSwapᵣ a b x) ≡
  (left Translation.++ₛ (right Translation.++ₛ ambient)) x
assocSwap-coherent left right ambient x =
  Source.++-assocSwapᵣ left right {ambient} x

private
  -- Shifting a body index past the two restriction channels.
  shiftPastRestrictions : {k : ℕ} → 𝔽 k → 𝔽 (suc (suc k))
  shiftPastRestrictions i = suc (suc i)

  -- A local copy of the symmetry of `ImageReindex`; the forward and backward
  -- maps simply exchange roles.
  reindex-sym :
    {P : Typed.Proc n} {Q : Typed.Proc n′}
    {sourceChannels :
      Vec (OrientedChannel c) (Translation.channelCount P)}
    {targetChannels :
      Vec (OrientedChannel c) (Translation.channelCount Q)}
    {sourceEnv : Translation.Env n (2 *ℕ c)}
    {targetEnv : Translation.Env n′ (2 *ℕ c)} →
    ImageReindex {P = P} {Q = Q}
      sourceChannels targetChannels sourceEnv targetEnv →
    ImageReindex {P = Q} {Q = P}
      targetChannels sourceChannels targetEnv sourceEnv
  reindex-sym {P = P} {sourceChannels = sourceChannels}
    {sourceEnv = sourceEnv} reindex = record
    { channelBackward = channelForward reindex
    ; channelForward = channelBackward reindex
    ; channel-forward-backward = channel-backward-forward reindex
    ; channel-backward-forward = channel-forward-backward reindex
    ; channel-entry = λ i →
        sym (channel-entry reindex (channelForward reindex i) ■
             cong (physicalChannel ∘ lookup sourceChannels)
               (channel-backward-forward reindex i))
    ; channel-content = λ i →
        sym (channel-content reindex (channelForward reindex i)) ■
        cong (lookup (proj₁ (flattenOriented P sourceChannels sourceEnv)))
          (channel-backward-forward reindex i)
    ; threadBackward = threadForward reindex
    ; threadForward = threadBackward reindex
    ; thread-forward-backward = thread-backward-forward reindex
    ; thread-backward-forward = thread-forward-backward reindex
    ; thread-content = λ i →
        sym (thread-content reindex (threadForward reindex i)) ■
        cong (lookup (proj₂ (flattenOriented P sourceChannels sourceEnv)))
          (thread-backward-forward reindex i)
    }

-- Commuting two restrictions swaps the two leading physical channels and
-- reindexes the body along the associativity swap.
commutationChannels :
  (B₁ B₂ A₁ A₂ : Typed.BindGroup)
  (P : Typed.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n))) →
  Vec (OrientedChannel c)
    (Translation.channelCount (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P))) →
  Vec (OrientedChannel c)
    (Translation.channelCount
      (Typed.ν A₁ A₂ (Typed.ν B₁ B₂
        (P Typed.⋯ₚ
          Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))))
commutationChannels B₁ B₂ A₁ A₂ P (outer ∷ inner ∷ channels) =
  inner ∷ outer ∷
  untransportChannels P
    (Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)) channels

commutation-reindex :
  (B₁ B₂ A₁ A₂ : Typed.BindGroup)
  (P : Typed.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n)))
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P))))
  (sigma : Translation.Env n (2 *ℕ c)) →
  ImageReindex
    {P = Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P)}
    {Q = Typed.ν A₁ A₂ (Typed.ν B₁ B₂
      (P Typed.⋯ₚ
        Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))}
    channels (commutationChannels B₁ B₂ A₁ A₂ P channels) sigma sigma
commutation-reindex {n = n} {c = c} B₁ B₂ A₁ A₂ P
  (outer ∷ inner ∷ channels) sigma = record
  { channelBackward = λ where
      zero → suc zero
      (suc zero) → zero
      (suc (suc i)) → suc (suc (channelBackward bodyReindex i))
  ; channelForward = λ where
      zero → suc zero
      (suc zero) → zero
      (suc (suc i)) → suc (suc (channelForward bodyReindex i))
  ; channel-forward-backward = λ where
      zero → refl
      (suc zero) → refl
      (suc (suc i)) →
        cong shiftPastRestrictions
          (channel-forward-backward bodyReindex i)
  ; channel-backward-forward = λ where
      zero → refl
      (suc zero) → refl
      (suc (suc i)) →
        cong shiftPastRestrictions
          (channel-backward-forward bodyReindex i)
  ; channel-entry = λ where
      zero → refl
      (suc zero) → refl
      (suc (suc i)) → channel-entry bodyReindex i
  ; channel-content = λ where
      zero → refl
      (suc zero) → refl
      (suc (suc i)) → channel-content bodyReindex i
  ; threadBackward = threadBackward bodyReindex
  ; threadForward = threadForward bodyReindex
  ; thread-forward-backward = thread-forward-backward bodyReindex
  ; thread-backward-forward = thread-backward-forward bodyReindex
  ; thread-content = thread-content bodyReindex
  }
  where
  rho :
    𝔽 (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n)) →
    𝔽 (sum B₁ + sum B₂ + (sum A₁ + sum A₂ + n))
  rho = Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)

  outerEnv : Translation.Env (sum B₁ + sum B₂) (2 *ℕ c)
  outerEnv =
    proj₁ (Translation.UB[ B₁ ] (physicalEndpoint outer zero)
      (SoupTerm.* , physicalEndpoint outer zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ B₂ ] (physicalEndpoint outer (suc zero))
      (SoupTerm.* , physicalEndpoint outer (suc zero) , SoupTerm.*))

  innerEnv : Translation.Env (sum A₁ + sum A₂) (2 *ℕ c)
  innerEnv =
    proj₁ (Translation.UB[ A₁ ] (physicalEndpoint inner zero)
      (SoupTerm.* , physicalEndpoint inner zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ A₂ ] (physicalEndpoint inner (suc zero))
      (SoupTerm.* , physicalEndpoint inner (suc zero) , SoupTerm.*))

  sourceBodyEnv :
    Translation.Env (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n)) (2 *ℕ c)
  sourceBodyEnv = innerEnv Translation.++ₛ (outerEnv Translation.++ₛ sigma)

  targetBodyEnv :
    Translation.Env (sum B₁ + sum B₂ + (sum A₁ + sum A₂ + n)) (2 *ℕ c)
  targetBodyEnv = outerEnv Translation.++ₛ (innerEnv Translation.++ₛ sigma)

  bodyReindex :
    ImageReindex {P = P} {Q = P Typed.⋯ₚ rho}
      channels (untransportChannels P rho channels)
      sourceBodyEnv targetBodyEnv
  bodyReindex = renaming-reindex
    {P = P} {rho = rho} {sourceChannels = channels}
    {sourceEnv = targetBodyEnv} {targetEnv = sourceBodyEnv}
    (assocSwap-coherent innerEnv outerEnv sigma)

commutation-image :
  {B₁ B₂ A₁ A₂ : Typed.BindGroup}
  {P : Typed.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n))}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P)))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P)) channels sigma
    ambientChannel ambientThread C →
  LocalImage
    (Typed.ν A₁ A₂ (Typed.ν B₁ B₂
      (P Typed.⋯ₚ
        Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))))
    (commutationChannels B₁ B₂ A₁ A₂ P channels)
    sigma ambientChannel ambientThread C
commutation-image {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}
  {channels = channels} {sigma = sigma} image =
  reindex-image (commutation-reindex B₁ B₂ A₁ A₂ P channels sigma) image

commutation-image⁻ :
  {B₁ B₂ A₁ A₂ : Typed.BindGroup}
  {P : Typed.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n))}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P)))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage
    (Typed.ν A₁ A₂ (Typed.ν B₁ B₂
      (P Typed.⋯ₚ
        Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))))
    (commutationChannels B₁ B₂ A₁ A₂ P channels)
    sigma ambientChannel ambientThread C →
  LocalImage (Typed.ν B₁ B₂ (Typed.ν A₁ A₂ P)) channels sigma
    ambientChannel ambientThread C
commutation-image⁻ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}
  {channels = channels} {sigma = sigma} image =
  reindex-image
    (reindex-sym (commutation-reindex B₁ B₂ A₁ A₂ P channels sigma)) image
