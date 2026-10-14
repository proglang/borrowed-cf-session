module BorrowedCF.Processes.TranslationSoup.Properties where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.UntypedSoup as 𝐒
open import BorrowedCF.Processes.TranslationSoup
  using (UChan; UBFrom; UB[_]; chanTriple; syncs; ϕ[_])
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Nat.Variables

channel0 : 𝔽 1
channel0 = Fin.zero {n = 0}

slot0 : 𝔽 2
slot0 = Fin.zero {n = 1}

slot1 : 𝔽 2
slot1 = Fin.suc (Fin.zero {n = 0})

baseChan : UChan 1
baseChan = 𝐒Tm.* , channel0 , 𝐒Tm.*

UBFrom-flags-length :
  (k : ℕ) (B : 𝐓.BindGroup) (r : 𝔽 n) (c : UChan n) →
  L.length (proj₂ (UBFrom k B r c)) ≡ syncs B
UBFrom-flags-length k [] r c = refl
UBFrom-flags-length k (b ∷ []) r c = refl
UBFrom-flags-length k (b ∷ B@(_ ∷ _)) r (e₁ , c , e₂) =
  cong suc (UBFrom-flags-length (suc k) B r (𝐒Tm.`phi (r , k) , c , e₂))

UB-flags-length :
  (B : 𝐓.BindGroup) (r : 𝔽 n) (c : UChan n) →
  L.length (proj₂ (UB[ B ] r c)) ≡ syncs B
UB-flags-length B r c = UBFrom-flags-length zero B r c

flags-0∷1 :
  proj₂ (UB[ 0 ∷ 1 ∷ [] ] channel0 baseChan)
  ≡ 𝐒.acq ∷ []
flags-0∷1 = refl

flags-0∷1∷1 :
  proj₂ (UB[ 0 ∷ 1 ∷ 1 ∷ [] ] channel0 baseChan)
  ≡ 𝐒.acq ∷ 𝐒.drop ∷ []
flags-0∷1∷1 = refl

phi-slot-zero :
  proj₁ (UB[ 1 ∷ 0 ∷ 1 ∷ [] ] channel0 baseChan) slot0
  ≡ chanTriple (𝐒Tm.* , channel0 , 𝐒Tm.`phi (channel0 , 0))
phi-slot-zero = refl

phi-slot-one :
  proj₁ (UB[ 1 ∷ 0 ∷ 1 ∷ [] ] channel0 baseChan) slot1
  ≡ chanTriple (𝐒Tm.`phi (channel0 , 1) , channel0 , 𝐒Tm.*)
phi-slot-one = refl
