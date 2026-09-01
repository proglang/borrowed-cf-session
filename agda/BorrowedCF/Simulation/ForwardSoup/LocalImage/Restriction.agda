module BorrowedCF.Simulation.ForwardSoup.LocalImage.Restriction where

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

open Nat.Variables
open Fin.Patterns

private variable
  a b : ℕ

UB-endpoint-cong :
  (B : Typed.BindGroup) {x y : 𝔽 n} →
  x ≡ y →
  Translation.UB[ B ] x (SoupTerm.* , x , SoupTerm.*) ≡
  Translation.UB[ B ] y (SoupTerm.* , y , SoupTerm.*)
UB-endpoint-cong B refl = refl

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

swapRestrictionChannels :
  (B₁ B₂ : Typed.BindGroup)
  (P : Typed.Proc (sum B₁ + sum B₂ + n)) →
  Vec (OrientedChannel c) (suc (Translation.channelCount P)) →
  Vec (OrientedChannel c)
    (suc (Translation.channelCount
      (P Typed.⋯ₚ Source.swapᵣ (sum B₁) (sum B₂))))
swapRestrictionChannels B₁ B₂ P (channel ∷ channels) =
  flipOrientedChannel channel ∷
  untransportChannels P (Source.swapᵣ (sum B₁) (sum B₂)) channels

restriction-swap-image :
  {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + n)}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount (Typed.ν B₁ B₂ P))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (Typed.ν B₁ B₂ P) channels sigma
    ambientChannel ambientThread C →
  LocalImage
    (Typed.ν B₂ B₁
      (P Typed.⋯ₚ Source.swapᵣ (sum B₁) (sum B₂)))
    (swapRestrictionChannels B₁ B₂ P channels)
    sigma ambientChannel ambientThread C
restriction-swap-image {n = n} {c = c} {B₁ = B₁} {B₂ = B₂} {P = P}
  {channels = (channel , forward) ∷ channels} {sigma = sigma} image
  with Translation.UB[ B₁ ] (physicalEndpoint (channel , forward) zero)
         (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*)
         in sourceLeft
     | Translation.UB[ B₂ ]
         (physicalEndpoint (channel , forward) (suc zero))
         (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
          SoupTerm.*)
         in sourceRight
     | Translation.UB[ B₂ ]
         (physicalEndpoint (channel , reverse) zero)
         (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*)
         in targetRight
     | Translation.UB[ B₁ ]
         (physicalEndpoint (channel , reverse) (suc zero))
         (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
          SoupTerm.*)
         in targetLeft
... | leftEnv , leftFlags | rightEnv , rightFlags
    | targetRightEnv , targetRightFlags
    | targetLeftEnv , targetLeftFlags =
  reindex-image reindex image
  where
  rho : 𝔽 (sum B₁ + sum B₂ + n) →
    𝔽 (sum B₂ + sum B₁ + n)
  rho = Source.swapᵣ (sum B₁) (sum B₂)

  targetChannels :
    Vec (OrientedChannel c) (Translation.channelCount (P Typed.⋯ₚ rho))
  targetChannels = untransportChannels P rho channels

  targetRight-sourceRight :
    Translation.UB[ B₂ ]
      (physicalEndpoint (channel , reverse) zero)
      (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*)
    ≡
    Translation.UB[ B₂ ]
      (physicalEndpoint (channel , forward) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
       SoupTerm.*)
  targetRight-sourceRight = UB-endpoint-cong B₂
    (physicalEndpoint-flip-left (channel , forward))

  targetLeft-sourceLeft :
    Translation.UB[ B₁ ]
      (physicalEndpoint (channel , reverse) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
       SoupTerm.*)
    ≡
    Translation.UB[ B₁ ]
      (physicalEndpoint (channel , forward) zero)
      (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*)
  targetLeft-sourceLeft = UB-endpoint-cong B₁
    (physicalEndpoint-flip-right (channel , forward))

  targetEnv-sourceEnv :
    (x : 𝔽 (sum B₂ + sum B₁ + n)) →
    ((proj₁ (Translation.UB[ B₂ ]
        (physicalEndpoint (channel , reverse) zero)
        (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₁ ]
        (physicalEndpoint (channel , reverse) (suc zero))
        (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
         SoupTerm.*))) Translation.++ₛ sigma) x
    ≡
    ((proj₁ (Translation.UB[ B₂ ]
        (physicalEndpoint (channel , forward) (suc zero))
        (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
         SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₁ ]
        (physicalEndpoint (channel , forward) zero)
        (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*)))
      Translation.++ₛ sigma) x
  targetEnv-sourceEnv = appendEnv-point-cong
    (appendEnv-point-cong
      (λ x → cong (λ result → proj₁ result x) targetRight-sourceRight)
      (λ x → cong (λ result → proj₁ result x) targetLeft-sourceLeft))
    (λ _ → refl)

  sourceBodyEnv : Translation.Env (sum B₁ + sum B₂ + n) (2 *ℕ c)
  sourceBodyEnv =
    (proj₁ (Translation.UB[ B₁ ]
      (physicalEndpoint (channel , forward) zero)
      (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ B₂ ]
      (physicalEndpoint (channel , forward) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
       SoupTerm.*))) Translation.++ₛ sigma

  targetBodyEnv : Translation.Env (sum B₂ + sum B₁ + n) (2 *ℕ c)
  targetBodyEnv =
    (proj₁ (Translation.UB[ B₂ ]
      (physicalEndpoint (channel , reverse) zero)
      (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ B₁ ]
      (physicalEndpoint (channel , reverse) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
       SoupTerm.*))) Translation.++ₛ sigma

  bodyReindex :
    ImageReindex {P = P} {Q = P Typed.⋯ₚ rho}
      channels targetChannels sourceBodyEnv targetBodyEnv
  bodyReindex = renaming-reindex
    {P = P} {rho = rho} {sourceChannels = channels}
    {sourceEnv = targetBodyEnv} {targetEnv = sourceBodyEnv}
    (λ x →
      targetEnv-sourceEnv (rho x) ■
      swap-prefix-coherent
        (proj₁ (Translation.UB[ B₁ ]
          (physicalEndpoint (channel , forward) zero)
          (SoupTerm.* , physicalEndpoint (channel , forward) zero ,
           SoupTerm.*)))
        (proj₁ (Translation.UB[ B₂ ]
          (physicalEndpoint (channel , forward) (suc zero))
          (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
           SoupTerm.*)))
        sigma x)

  reindex :
    ImageReindex
      {P = Typed.ν B₁ B₂ P}
      {Q = Typed.ν B₂ B₁ (P Typed.⋯ₚ rho)}
      ((channel , forward) ∷ channels)
      ((channel , reverse) ∷ targetChannels) sigma sigma
  reindex = record
    { channelBackward = λ where
        zero → zero
        (suc i) → suc (channelBackward bodyReindex i)
    ; channelForward = λ where
        zero → zero
        (suc i) → suc (channelForward bodyReindex i)
    ; channel-forward-backward = λ where
        zero → refl
        (suc i) → cong suc (channel-forward-backward bodyReindex i)
    ; channel-backward-forward = λ where
        zero → refl
        (suc i) → cong suc (channel-backward-forward bodyReindex i)
    ; channel-entry = λ where
        zero → refl
        (suc i) → channel-entry bodyReindex i
    ; channel-content = λ where
        zero →
          sym (orientChannel-flip
            (channel , forward) true
            (proj₂ (Translation.UB[ B₁ ]
              (physicalEndpoint (channel , forward) zero)
              (SoupTerm.* , physicalEndpoint (channel , forward) zero ,
               SoupTerm.*)))
            (proj₂ (Translation.UB[ B₂ ]
              (physicalEndpoint (channel , forward) (suc zero))
              (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
               SoupTerm.*)))) ■
          cong₂ (λ right left →
            orientChannel reverse (true , right , left))
            (sym (cong proj₂ targetRight-sourceRight))
            (sym (cong proj₂ targetLeft-sourceLeft))
        (suc i) → channel-content bodyReindex i
    ; threadBackward = threadBackward bodyReindex
    ; threadForward = threadForward bodyReindex
    ; thread-forward-backward = thread-forward-backward bodyReindex
    ; thread-backward-forward = thread-backward-forward bodyReindex
    ; thread-content = thread-content bodyReindex
    }
restriction-swap-image {n = n} {c = c} {B₁ = B₁} {B₂ = B₂} {P = P}
  {channels = (channel , reverse) ∷ channels} {sigma = sigma} image
  with Translation.UB[ B₁ ] (physicalEndpoint (channel , reverse) zero)
         (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*)
         in sourceLeft
     | Translation.UB[ B₂ ]
         (physicalEndpoint (channel , reverse) (suc zero))
         (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
          SoupTerm.*)
         in sourceRight
     | Translation.UB[ B₂ ]
         (physicalEndpoint (channel , forward) zero)
         (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*)
         in targetRight
     | Translation.UB[ B₁ ]
         (physicalEndpoint (channel , forward) (suc zero))
         (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
          SoupTerm.*)
         in targetLeft
... | leftEnv , leftFlags | rightEnv , rightFlags
    | targetRightEnv , targetRightFlags
    | targetLeftEnv , targetLeftFlags =
  reindex-image reindex image
  where
  rho : 𝔽 (sum B₁ + sum B₂ + n) →
    𝔽 (sum B₂ + sum B₁ + n)
  rho = Source.swapᵣ (sum B₁) (sum B₂)

  targetChannels :
    Vec (OrientedChannel c) (Translation.channelCount (P Typed.⋯ₚ rho))
  targetChannels = untransportChannels P rho channels

  targetRight-sourceRight :
    Translation.UB[ B₂ ]
      (physicalEndpoint (channel , forward) zero)
      (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*)
    ≡
    Translation.UB[ B₂ ]
      (physicalEndpoint (channel , reverse) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
       SoupTerm.*)
  targetRight-sourceRight = UB-endpoint-cong B₂
    (physicalEndpoint-flip-left (channel , reverse))

  targetLeft-sourceLeft :
    Translation.UB[ B₁ ]
      (physicalEndpoint (channel , forward) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
       SoupTerm.*)
    ≡
    Translation.UB[ B₁ ]
      (physicalEndpoint (channel , reverse) zero)
      (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*)
  targetLeft-sourceLeft = UB-endpoint-cong B₁
    (physicalEndpoint-flip-right (channel , reverse))

  targetEnv-sourceEnv :
    (x : 𝔽 (sum B₂ + sum B₁ + n)) →
    ((proj₁ (Translation.UB[ B₂ ]
        (physicalEndpoint (channel , forward) zero)
        (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₁ ]
        (physicalEndpoint (channel , forward) (suc zero))
        (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
         SoupTerm.*))) Translation.++ₛ sigma) x
    ≡
    ((proj₁ (Translation.UB[ B₂ ]
        (physicalEndpoint (channel , reverse) (suc zero))
        (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
         SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₁ ]
        (physicalEndpoint (channel , reverse) zero)
        (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*)))
      Translation.++ₛ sigma) x
  targetEnv-sourceEnv = appendEnv-point-cong
    (appendEnv-point-cong
      (λ x → cong (λ result → proj₁ result x) targetRight-sourceRight)
      (λ x → cong (λ result → proj₁ result x) targetLeft-sourceLeft))
    (λ _ → refl)

  sourceBodyEnv : Translation.Env (sum B₁ + sum B₂ + n) (2 *ℕ c)
  sourceBodyEnv =
    (proj₁ (Translation.UB[ B₁ ]
      (physicalEndpoint (channel , reverse) zero)
      (SoupTerm.* , physicalEndpoint (channel , reverse) zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ B₂ ]
      (physicalEndpoint (channel , reverse) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
       SoupTerm.*))) Translation.++ₛ sigma

  targetBodyEnv : Translation.Env (sum B₂ + sum B₁ + n) (2 *ℕ c)
  targetBodyEnv =
    (proj₁ (Translation.UB[ B₂ ]
      (physicalEndpoint (channel , forward) zero)
      (SoupTerm.* , physicalEndpoint (channel , forward) zero , SoupTerm.*))
    Translation.++ₛ
    proj₁ (Translation.UB[ B₁ ]
      (physicalEndpoint (channel , forward) (suc zero))
      (SoupTerm.* , physicalEndpoint (channel , forward) (suc zero) ,
       SoupTerm.*))) Translation.++ₛ sigma

  bodyReindex :
    ImageReindex {P = P} {Q = P Typed.⋯ₚ rho}
      channels targetChannels sourceBodyEnv targetBodyEnv
  bodyReindex = renaming-reindex
    {P = P} {rho = rho} {sourceChannels = channels}
    {sourceEnv = targetBodyEnv} {targetEnv = sourceBodyEnv}
    (λ x →
      targetEnv-sourceEnv (rho x) ■
      swap-prefix-coherent
        (proj₁ (Translation.UB[ B₁ ]
          (physicalEndpoint (channel , reverse) zero)
          (SoupTerm.* , physicalEndpoint (channel , reverse) zero ,
           SoupTerm.*)))
        (proj₁ (Translation.UB[ B₂ ]
          (physicalEndpoint (channel , reverse) (suc zero))
          (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
           SoupTerm.*)))
        sigma x)

  reindex :
    ImageReindex
      {P = Typed.ν B₁ B₂ P}
      {Q = Typed.ν B₂ B₁ (P Typed.⋯ₚ rho)}
      ((channel , reverse) ∷ channels)
      ((channel , forward) ∷ targetChannels) sigma sigma
  reindex = record
    { channelBackward = λ where
        zero → zero
        (suc i) → suc (channelBackward bodyReindex i)
    ; channelForward = λ where
        zero → zero
        (suc i) → suc (channelForward bodyReindex i)
    ; channel-forward-backward = λ where
        zero → refl
        (suc i) → cong suc (channel-forward-backward bodyReindex i)
    ; channel-backward-forward = λ where
        zero → refl
        (suc i) → cong suc (channel-backward-forward bodyReindex i)
    ; channel-entry = λ where
        zero → refl
        (suc i) → channel-entry bodyReindex i
    ; channel-content = λ where
        zero →
          sym (orientChannel-flip
            (channel , reverse) true
            (proj₂ (Translation.UB[ B₁ ]
              (physicalEndpoint (channel , reverse) zero)
              (SoupTerm.* , physicalEndpoint (channel , reverse) zero ,
               SoupTerm.*)))
            (proj₂ (Translation.UB[ B₂ ]
              (physicalEndpoint (channel , reverse) (suc zero))
              (SoupTerm.* , physicalEndpoint (channel , reverse) (suc zero) ,
               SoupTerm.*)))) ■
          cong₂ (λ right left →
            orientChannel forward (true , right , left))
            (sym (cong proj₂ targetRight-sourceRight))
            (sym (cong proj₂ targetLeft-sourceLeft))
        (suc i) → channel-content bodyReindex i
    ; threadBackward = threadBackward bodyReindex
    ; threadForward = threadForward bodyReindex
    ; thread-forward-backward = thread-forward-backward bodyReindex
    ; thread-backward-forward = thread-backward-forward bodyReindex
    ; thread-content = thread-content bodyReindex
    }
