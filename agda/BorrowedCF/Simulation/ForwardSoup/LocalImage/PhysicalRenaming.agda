module BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage

open Nat.Variables

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
