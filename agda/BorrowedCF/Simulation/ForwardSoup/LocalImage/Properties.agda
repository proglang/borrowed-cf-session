module BorrowedCF.Simulation.ForwardSoup.LocalImage.Properties where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm
open import BorrowedCF.Simulation.ForwardSoup.LocalImage

open Nat.Variables

forwardChannel : ∀ {n} → 𝔽 n → OrientedChannel n
forwardChannel i = i , forward

flattenOriented-forward :
  (P : Typed.Proc n) →
  (channels : Vec (𝔽 c) (Translation.channelCount P)) →
  (sigma : Translation.Env n (2 *ℕ c)) →
  flattenOriented P (V.map forwardChannel channels) sigma ≡
  Translation.flatten P channels sigma
flattenOriented-forward (Typed.⟪ e ⟫) [] sigma = refl
flattenOriented-forward (P Typed.∥ Q) channels sigma
  rewrite V.take-map forwardChannel (Translation.channelCount P) channels
        | V.drop-map forwardChannel (Translation.channelCount P) channels
        | flattenOriented-forward P
            (V.take (Translation.channelCount P) channels) sigma
        | flattenOriented-forward Q
            (V.drop (Translation.channelCount P) channels) sigma
  = refl
flattenOriented-forward (Typed.ν B₁ B₂ P) (channel ∷ channels) sigma
  with Translation.UB[ B₁ ]
         (physicalEndpoint (forwardChannel channel) zero)
         (SoupTerm.* , physicalEndpoint (forwardChannel channel) zero ,
          SoupTerm.*)
     | Translation.UB[ B₂ ]
         (physicalEndpoint (forwardChannel channel) (suc zero))
         (SoupTerm.* ,
          physicalEndpoint (forwardChannel channel) (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂
  = cong
      (λ result →
        ((true , flags₁ , flags₂) ∷ proj₁ result , proj₂ result))
      (flattenOriented-forward P channels
        ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma))

forwardPhysical-allFin :
  (i : 𝔽 n) →
  physicalChannel (lookup (V.map forwardChannel (V.allFin n)) i) ≡ i
forwardPhysical-allFin i =
  cong physicalChannel
    (V.lookup-map i forwardChannel (V.allFin _)) ■
  V.lookup-allFin i

initialLocalImage :
  (P : Typed.Proc 0) →
  LocalImage P
    (V.map forwardChannel (V.allFin (Translation.channelCount P)))
    (λ ()) (λ _ → ⊥) (λ _ → ⊥)
    (Soup.config
      (proj₁ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ())))
      (proj₂ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ()))))
initialLocalImage P = record
  { channelEmbedding-injective = λ {i} {j} equal →
      sym (forwardPhysical-allFin i) ■ equal ■
      forwardPhysical-allFin j
  ; threadEmbedding = just
  ; threadEmbedding-injective = λ { refl refl → refl }
  ; live-channel = λ i →
      cong
        (lookup (proj₁ (Translation.flatten P
          (V.allFin (Translation.channelCount P)) (λ ()))))
        (forwardPhysical-allFin i) ■
      cong (λ result → lookup (proj₁ result) i)
        (sym (flattenOriented-forward P
          (V.allFin (Translation.channelCount P)) (λ ())))
  ; live-thread = λ j → present j refl
      (cong (λ result → lookup (proj₂ result) j)
        (sym (flattenOriented-forward P
          (V.allFin (Translation.channelCount P)) (λ ()))))
  ; garbage-channel = λ i outside _ →
      ⊥-elim (outside i (forwardPhysical-allFin i))
  ; garbage-thread = λ j outside _ →
      ⊥-elim (outside j refl)
  }
