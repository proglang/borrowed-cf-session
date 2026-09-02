module BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (T[_]-Env-cong; T[_]-renEnv)

open Nat.Variables

variable a b : ℕ

renameEnv :
  (𝔽 n → 𝔽 n′) → Translation.Env k n → Translation.Env k n′
renameEnv rho sigma x = sigma x SoupTerm.⋯ᵣ rho

renameOriented :
  (𝔽 n → 𝔽 n′) → OrientedChannel n → OrientedChannel n′
renameOriented rho (channel , orientation) = rho channel , orientation

physicalChannel-rename :
  (rho : 𝔽 n → 𝔽 n′) (channel : OrientedChannel n) →
  physicalChannel (renameOriented rho channel) ≡
  rho (physicalChannel channel)
physicalChannel-rename rho (channel , orientation) = refl

physicalEndpoint-rename :
  (channelRho : 𝔽 n → 𝔽 n′)
  (endpointRho : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ n′)) →
  ((i : 𝔽 n) (side : 𝔽 2) →
    endpointRho (Soup.endpoint i side) ≡
    Soup.endpoint (channelRho i) side) →
  (channel : OrientedChannel n) (side : 𝔽 2) →
  physicalEndpoint (renameOriented channelRho channel) side ≡
  endpointRho (physicalEndpoint channel side)
physicalEndpoint-rename channelRho endpointRho respects
  (channel , forward) side = sym (respects channel side)
physicalEndpoint-rename channelRho endpointRho respects
  (channel , reverse) zero = sym (respects channel (suc zero))
physicalEndpoint-rename channelRho endpointRho respects
  (channel , reverse) (suc zero) = sym (respects channel zero)

chanTriple-ren :
  (rho : 𝔽 n → 𝔽 n′) (e₁ e₂ : SoupTerm.Tm n) (c : 𝔽 n) →
  Translation.chanTriple (e₁ , c , e₂) SoupTerm.⋯ᵣ rho ≡
  Translation.chanTriple
    (e₁ SoupTerm.⋯ᵣ rho , rho c , e₂ SoupTerm.⋯ᵣ rho)
chanTriple-ren rho e₁ e₂ c = refl

Ub-ren :
  ∀ b (rho : 𝔽 n → 𝔽 n′)
    (e₁ : SoupTerm.Tm n) (c : 𝔽 n) (e₂ : SoupTerm.Tm n)
    (x : 𝔽 b) →
  Translation.Ub[ b ] (e₁ , c , e₂) x SoupTerm.⋯ᵣ rho ≡
  Translation.Ub[ b ]
    (e₁ SoupTerm.⋯ᵣ rho , rho c , e₂ SoupTerm.⋯ᵣ rho) x
Ub-ren zero rho e₁ c e₂ ()
Ub-ren (suc zero) rho e₁ c e₂ zero = refl
Ub-ren (suc (suc b)) rho e₁ c e₂ zero = refl
Ub-ren (suc (suc b)) rho e₁ c e₂ (suc x) =
  Ub-ren (suc b) rho SoupTerm.* c e₂ x

UBFrom-ren :
  ∀ k (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′)
    (r : 𝔽 n) (e₁ : SoupTerm.Tm n) (c : 𝔽 n)
    (e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
  proj₁ (Translation.UBFrom k B r (e₁ , c , e₂)) x
    SoupTerm.⋯ᵣ rho ≡
  proj₁ (Translation.UBFrom k B (rho r)
    (e₁ SoupTerm.⋯ᵣ rho , rho c , e₂ SoupTerm.⋯ᵣ rho)) x
UBFrom-ren k [] rho r e₁ c e₂ ()
UBFrom-ren k (b ∷ []) rho r e₁ c e₂ x =
  Ub-ren (b + 0) rho e₁ c e₂ x
UBFrom-ren k (b ∷ B@(b′ ∷ B′)) rho r e₁ c e₂ y
  with UBFrom-ren (suc k) B rho r (SoupTerm.`phi (r , k)) c e₂
     | Fin.splitAt b y
... | induction | inj₁ x =
  Ub-ren b rho e₁ c (SoupTerm.`phi (r , k)) x
... | induction | inj₂ x = induction x

UB-ren :
  ∀ (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′)
    (r : 𝔽 n) (e₁ : SoupTerm.Tm n) (c : 𝔽 n)
    (e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
  proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)) x
    SoupTerm.⋯ᵣ rho ≡
  proj₁ (Translation.UB[ B ] (rho r)
    (e₁ SoupTerm.⋯ᵣ rho , rho c , e₂ SoupTerm.⋯ᵣ rho)) x
UB-ren = UBFrom-ren zero

UBFrom-flags-ren :
  ∀ k (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′)
    (r : 𝔽 n) (c : Translation.UChan n) →
  proj₂ (Translation.UBFrom k B r c) ≡
  proj₂ (Translation.UBFrom k B (rho r)
    (proj₁ c SoupTerm.⋯ᵣ rho , rho (proj₁ (proj₂ c)) ,
     proj₂ (proj₂ c) SoupTerm.⋯ᵣ rho))
UBFrom-flags-ren k [] rho r c = refl
UBFrom-flags-ren k (b ∷ []) rho r c = refl
UBFrom-flags-ren k (b ∷ B@(b′ ∷ B′)) rho r (e₁ , c , e₂) =
  cong (Translation.ϕ[ b ] ∷_)
    (UBFrom-flags-ren (suc k) B rho r
      (SoupTerm.`phi (r , k) , c , e₂))

UB-flags-ren :
  ∀ (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′)
    (r : 𝔽 n) (c : Translation.UChan n) →
  proj₂ (Translation.UB[ B ] r c) ≡
  proj₂ (Translation.UB[ B ] (rho r)
    (proj₁ c SoupTerm.⋯ᵣ rho , rho (proj₁ (proj₂ c)) ,
     proj₂ (proj₂ c) SoupTerm.⋯ᵣ rho))
UB-flags-ren = UBFrom-flags-ren zero

++ₛ-ren-coherent :
  {sigma₁ : Translation.Env a n} {sigma₂ : Translation.Env b n}
  {tau₁ : Translation.Env a n′} {tau₂ : Translation.Env b n′}
  (rho : 𝔽 n → 𝔽 n′) →
  ((x : 𝔽 a) → tau₁ x ≡ sigma₁ x SoupTerm.⋯ᵣ rho) →
  ((x : 𝔽 b) → tau₂ x ≡ sigma₂ x SoupTerm.⋯ᵣ rho) →
  (x : 𝔽 (a + b)) →
  (tau₁ Translation.++ₛ tau₂) x ≡
  (sigma₁ Translation.++ₛ sigma₂) x SoupTerm.⋯ᵣ rho
++ₛ-ren-coherent {a = a} rho coherent₁ coherent₂ x
  with Fin.splitAt a x
... | inj₁ y = coherent₁ y
... | inj₂ y = coherent₂ y

UB-ren-coherent :
  (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′)
  (r : 𝔽 n) (e₁ : SoupTerm.Tm n) (c : 𝔽 n)
  (e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
  proj₁ (Translation.UB[ B ] (rho r)
    (e₁ SoupTerm.⋯ᵣ rho , rho c , e₂ SoupTerm.⋯ᵣ rho)) x ≡
  proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)) x
    SoupTerm.⋯ᵣ rho
UB-ren-coherent B rho r e₁ c e₂ x =
  sym (UB-ren B rho r e₁ c e₂ x)

-- | The instance used below, with the literal `SoupTerm.*` endpoints that
--   `flattenOriented` builds.  Stating it this way keeps the type syntactically
--   equal to the `with`-abstracted binder environments.
UB-ren-coherent-* :
  (B : Typed.BindGroup) (rho : 𝔽 n → 𝔽 n′) (r c : 𝔽 n) (x : 𝔽 (sum B)) →
  proj₁ (Translation.UB[ B ] (rho r)
    (SoupTerm.* , rho c , SoupTerm.*)) x ≡
  proj₁ (Translation.UB[ B ] r (SoupTerm.* , c , SoupTerm.*)) x
    SoupTerm.⋯ᵣ rho
UB-ren-coherent-* B rho r c =
  UB-ren-coherent B rho r SoupTerm.* c SoupTerm.*

flattenChannels-physical :
  (P : Typed.Proc k)
  (channelRho : 𝔽 n → 𝔽 n′)
  (endpointRho : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ n′))
  (respects : (i : 𝔽 n) (side : 𝔽 2) →
    endpointRho (Soup.endpoint i side) ≡
    Soup.endpoint (channelRho i) side)
  (channels : Vec (OrientedChannel n) (Translation.channelCount P))
  (source : Translation.Env k (2 *ℕ n))
  (target : Translation.Env k (2 *ℕ n′)) →
  ((x : 𝔽 k) → target x ≡ source x SoupTerm.⋯ᵣ endpointRho) →
  proj₁ (flattenOriented P (V.map (renameOriented channelRho) channels)
    target) ≡
  proj₁ (flattenOriented P channels source)
flattenChannels-physical (Typed.⟪ e ⟫) channelRho endpointRho respects
  [] source target coherent = refl
flattenChannels-physical (P Typed.∥ Q) channelRho endpointRho respects
  channels source target coherent
  rewrite V.take-map (renameOriented channelRho)
            (Translation.channelCount P) channels
        | V.drop-map (renameOriented channelRho)
            (Translation.channelCount P) channels
        | flattenChannels-physical P channelRho endpointRho respects
            (V.take (Translation.channelCount P) channels)
            source target coherent
        | flattenChannels-physical Q channelRho endpointRho respects
            (V.drop (Translation.channelCount P) channels)
            source target coherent
  = refl
flattenChannels-physical (Typed.ν B₁ B₂ P)
  channelRho endpointRho respects (channel ∷ channels) source target coherent
  rewrite physicalEndpoint-rename channelRho endpointRho respects channel zero
        | physicalEndpoint-rename channelRho endpointRho respects
            channel (suc zero)
        | UB-flags-ren B₁ endpointRho (physicalEndpoint channel zero)
            (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
        | UB-flags-ren B₂ endpointRho
            (physicalEndpoint channel (suc zero))
            (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
     | Translation.UB[ B₁ ] (endpointRho (physicalEndpoint channel zero))
         (SoupTerm.* , endpointRho (physicalEndpoint channel zero) ,
          SoupTerm.*)
     | Translation.UB[ B₂ ]
         (endpointRho (physicalEndpoint channel (suc zero)))
         (SoupTerm.* , endpointRho (physicalEndpoint channel (suc zero)) ,
          SoupTerm.*)
     | UB-ren-coherent-* B₁ endpointRho
         (physicalEndpoint channel zero) (physicalEndpoint channel zero)
     | UB-ren-coherent-* B₂ endpointRho
         (physicalEndpoint channel (suc zero))
         (physicalEndpoint channel (suc zero))
... | sigma₁ , flags₁ | sigma₂ , flags₂
    | tau₁ , targetFlags₁ | tau₂ , targetFlags₂
    | coherent₁ | coherent₂ =
  cong₂ _∷_
    refl
    (flattenChannels-physical P channelRho endpointRho respects
      channels
      ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ source)
      ((tau₁ Translation.++ₛ tau₂) Translation.++ₛ target)
      (++ₛ-ren-coherent endpointRho
        (++ₛ-ren-coherent endpointRho coherent₁ coherent₂)
        coherent))

flattenThreads-physical :
  (P : Typed.Proc k)
  (channelRho : 𝔽 n → 𝔽 n′)
  (endpointRho : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ n′))
  (respects : (i : 𝔽 n) (side : 𝔽 2) →
    endpointRho (Soup.endpoint i side) ≡
    Soup.endpoint (channelRho i) side)
  (channels : Vec (OrientedChannel n) (Translation.channelCount P))
  (source : Translation.Env k (2 *ℕ n))
  (target : Translation.Env k (2 *ℕ n′)) →
  ((x : 𝔽 k) → target x ≡ source x SoupTerm.⋯ᵣ endpointRho) →
  proj₂ (flattenOriented P (V.map (renameOriented channelRho) channels)
    target) ≡
  V.map (SoupTerm._⋯ᵣ endpointRho)
    (proj₂ (flattenOriented P channels source))
flattenThreads-physical (Typed.⟪ e ⟫) channelRho endpointRho respects
  [] source target coherent =
  cong (_∷ [])
    (T[_]-Env-cong e coherent ■ T[_]-renEnv e source endpointRho)
flattenThreads-physical (P Typed.∥ Q) channelRho endpointRho respects
  channels source target coherent
  rewrite V.take-map (renameOriented channelRho)
            (Translation.channelCount P) channels
        | V.drop-map (renameOriented channelRho)
            (Translation.channelCount P) channels
        | flattenThreads-physical P channelRho endpointRho respects
            (V.take (Translation.channelCount P) channels)
            source target coherent
        | flattenThreads-physical Q channelRho endpointRho respects
            (V.drop (Translation.channelCount P) channels)
            source target coherent
        | V.map-++ (SoupTerm._⋯ᵣ endpointRho)
            (proj₂ (flattenOriented P
              (V.take (Translation.channelCount P) channels) source))
            (proj₂ (flattenOriented Q
              (V.drop (Translation.channelCount P) channels) source))
  = refl
flattenThreads-physical (Typed.ν B₁ B₂ P)
  channelRho endpointRho respects (channel ∷ channels) source target coherent
  rewrite physicalEndpoint-rename channelRho endpointRho respects channel zero
        | physicalEndpoint-rename channelRho endpointRho respects
            channel (suc zero)
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
     | Translation.UB[ B₁ ] (endpointRho (physicalEndpoint channel zero))
         (SoupTerm.* , endpointRho (physicalEndpoint channel zero) ,
          SoupTerm.*)
     | Translation.UB[ B₂ ]
         (endpointRho (physicalEndpoint channel (suc zero)))
         (SoupTerm.* , endpointRho (physicalEndpoint channel (suc zero)) ,
          SoupTerm.*)
     | UB-ren-coherent-* B₁ endpointRho
         (physicalEndpoint channel zero) (physicalEndpoint channel zero)
     | UB-ren-coherent-* B₂ endpointRho
         (physicalEndpoint channel (suc zero))
         (physicalEndpoint channel (suc zero))
... | sigma₁ , flags₁ | sigma₂ , flags₂
    | tau₁ , targetFlags₁ | tau₂ , targetFlags₂
    | coherent₁ | coherent₂ =
  flattenThreads-physical P channelRho endpointRho respects channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ source)
    ((tau₁ Translation.++ₛ tau₂) Translation.++ₛ target)
    (++ₛ-ren-coherent endpointRho
      (++ₛ-ren-coherent endpointRho coherent₁ coherent₂)
      coherent)
