module BorrowedCF.Processes.TranslationSoup.Properties where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Processes.TranslationSoup
  using (UChan; UB[_]; syncs; ϕ[_])
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Nat.Variables

UB-flags-length :
  (B : 𝐓.BindGroup) (r : 𝔽 n) (c : UChan n) →
  L.length (proj₂ (UB[ B ] r c)) ≡ syncs B
UB-flags-length [] r c = refl
UB-flags-length (b ∷ []) r c = refl
UB-flags-length (b ∷ B@(_ ∷ _)) r (e₁ , c , e₂)
  with UB[ B ] r (𝐒Tm.`phi (r , syncs B) , c , e₂)
     | UB-flags-length B r (𝐒Tm.`phi (r , syncs B) , c , e₂)
... | σ , fs | ih =
  let open ≡-Reasoning in
  L.length (fs ++ ϕ[ b ] ∷ [])
    ≡⟨ L.length-++ fs ⟩
  L.length fs + 1
    ≡⟨ +-suc (L.length fs) 0 ⟩
  suc (L.length fs + 0)
    ≡⟨ cong suc (+-identityʳ (L.length fs)) ⟩
  suc (L.length fs)
    ≡⟨ cong suc ih ⟩
  suc (syncs B)
    ∎
