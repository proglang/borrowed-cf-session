module BorrowedCF.Simulation.ForwardSoup.Renaming where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (T[_]-Env-cong; T[_]-⋯ᵣ)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalEndpoint; flattenOriented)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename; processCount-rename;
    ++ₛ-lookupˡ; ++ₛ-lookupʳ)

open Nat.Variables
open Fin.Patterns

private variable
  A : Set
  b c o : ℕ

transportChannels :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.channelCount (P Typed.⋯ₚ ρ)) →
  Vec A (Translation.channelCount P)
transportChannels (Typed.⟪ e ⟫) ρ [] = []
transportChannels (P Typed.∥ Q) ρ xs =
  transportChannels P ρ
    (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) xs) V.++
  transportChannels Q ρ
    (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) xs)
transportChannels (Typed.ν B₁ B₂ P) ρ (x ∷ xs) =
  x ∷ transportChannels P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs

transportProcesses :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.processCount (P Typed.⋯ₚ ρ)) →
  Vec A (Translation.processCount P)
transportProcesses (Typed.⟪ e ⟫) ρ xs = xs
transportProcesses (P Typed.∥ Q) ρ xs =
  transportProcesses P ρ
    (V.take (Translation.processCount (P Typed.⋯ₚ ρ)) xs) V.++
  transportProcesses Q ρ
    (V.drop (Translation.processCount (P Typed.⋯ₚ ρ)) xs)
transportProcesses (Typed.ν B₁ B₂ P) ρ xs =
  transportProcesses P (Source._↑*_ ρ (sum B₁ + sum B₂)) xs

cast-split :
  {a a′ b b′ : ℕ}
  (left : a ≡ a′) (right : b ≡ b′)
  (xs : Vec A (a + b)) →
  V.cast (cong₂ _+_ left right) xs ≡
  V.cast left (V.take a xs) V.++ V.cast right (V.drop a xs)
cast-split {a = a} refl refl xs =
  VecP.cast-is-id refl xs ■
  sym (V.take++drop≡id a xs) ■
  cong₂ V._++_
    (sym (VecP.cast-is-id refl (V.take a xs)))
    (sym (VecP.cast-is-id refl (V.drop a xs)))

cast-cons :
  {a b : ℕ} (equal : a ≡ b) (x : A) (xs : Vec A a) →
  V.cast (cong suc equal) (x ∷ xs) ≡ x ∷ V.cast equal xs
cast-cons refl x xs =
  VecP.cast-is-id refl (x ∷ xs) ■
  cong (x ∷_) (sym (VecP.cast-is-id refl xs))

transportChannels-cast :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.channelCount (P Typed.⋯ₚ ρ))) →
  transportChannels P ρ xs ≡
  V.cast (channelCount-rename P ρ) xs
transportChannels-cast (Typed.⟪ e ⟫) ρ [] =
  sym (VecP.cast-is-id refl [])
transportChannels-cast (P Typed.∥ Q) ρ xs =
  cong₂ V._++_
    (transportChannels-cast P ρ
      (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) xs))
    (transportChannels-cast Q ρ
      (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) xs)) ■
  sym (cast-split
    (channelCount-rename P ρ) (channelCount-rename Q ρ) xs)
transportChannels-cast (Typed.ν B₁ B₂ P) ρ (x ∷ xs) =
  cong (x ∷_) (transportChannels-cast P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs) ■
  sym (cast-cons
    (channelCount-rename P (Source._↑*_ ρ (sum B₁ + sum B₂)))
    x xs)

transportProcesses-cast :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.processCount (P Typed.⋯ₚ ρ))) →
  transportProcesses P ρ xs ≡
  V.cast (processCount-rename P ρ) xs
transportProcesses-cast (Typed.⟪ e ⟫) ρ xs =
  sym (VecP.cast-is-id refl xs)
transportProcesses-cast (P Typed.∥ Q) ρ xs =
  cong₂ V._++_
    (transportProcesses-cast P ρ
      (V.take (Translation.processCount (P Typed.⋯ₚ ρ)) xs))
    (transportProcesses-cast Q ρ
      (V.drop (Translation.processCount (P Typed.⋯ₚ ρ)) xs)) ■
  sym (cast-split
    (processCount-rename P ρ) (processCount-rename Q ρ) xs)
transportProcesses-cast (Typed.ν B₁ B₂ P) ρ xs =
  transportProcesses-cast P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs

untransportChannels :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.channelCount P) →
  Vec A (Translation.channelCount (P Typed.⋯ₚ ρ))
untransportChannels P ρ =
  V.cast (sym (channelCount-rename P ρ))

untransportProcesses :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.processCount P) →
  Vec A (Translation.processCount (P Typed.⋯ₚ ρ))
untransportProcesses P ρ =
  V.cast (sym (processCount-rename P ρ))

transportChannels-untransport :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.channelCount P)) →
  transportChannels P ρ (untransportChannels P ρ xs) ≡ xs
transportChannels-untransport P ρ xs =
  transportChannels-cast P ρ (untransportChannels P ρ xs) ■
  VecP.cast-trans
    (sym (channelCount-rename P ρ)) (channelCount-rename P ρ) xs ■
  VecP.cast-is-id
    (sym (channelCount-rename P ρ) ■ channelCount-rename P ρ) xs

transportProcesses-untransport :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.processCount P)) →
  transportProcesses P ρ (untransportProcesses P ρ xs) ≡ xs
transportProcesses-untransport P ρ xs =
  transportProcesses-cast P ρ (untransportProcesses P ρ xs) ■
  VecP.cast-trans
    (sym (processCount-rename P ρ)) (processCount-rename P ρ) xs ■
  VecP.cast-is-id
    (sym (processCount-rename P ρ) ■ processCount-rename P ρ) xs

take-++ˡ :
  (xs : Vec A n) (ys : Vec A m) →
  V.take n (xs V.++ ys) ≡ xs
take-++ˡ [] ys = refl
take-++ˡ (x ∷ xs) ys = cong (x ∷_) (take-++ˡ xs ys)

drop-++ˡ :
  (xs : Vec A n) (ys : Vec A m) →
  V.drop n (xs V.++ ys) ≡ ys
drop-++ˡ [] ys = refl
drop-++ˡ (x ∷ xs) ys = drop-++ˡ xs ys

lift*-↑ˡ :
  (ρ : 𝔽 n → 𝔽 n′) (b : ℕ) (x : 𝔽 b) →
  Source._↑*_ ρ b (x ↑ˡ n) ≡ x ↑ˡ n′
lift*-↑ˡ ρ (suc b) zero = refl
lift*-↑ˡ ρ (suc b) (suc x) = cong suc (lift*-↑ˡ ρ b x)

lift*-↑ʳ :
  (ρ : 𝔽 n → 𝔽 n′) (b : ℕ) (x : 𝔽 n) →
  Source._↑*_ ρ b (b ↑ʳ x) ≡ b ↑ʳ ρ x
lift*-↑ʳ ρ zero x = refl
lift*-↑ʳ ρ (suc b) x = cong suc (lift*-↑ʳ ρ b x)

prefix-coherent :
  {b n n′ o : ℕ}
  {bound : Translation.Env b o}
  {source : Translation.Env n′ o}
  {target : Translation.Env n o}
  (ρ : 𝔽 n → 𝔽 n′) →
  ((x : 𝔽 n) → source (ρ x) ≡ target x) →
  (x : 𝔽 (b + n)) →
  (bound Translation.++ₛ source) (Source._↑*_ ρ b x) ≡
  (bound Translation.++ₛ target) x
prefix-coherent {b = b} {n = n} {n′ = n′}
  {bound = bound} {source = source} {target = target} ρ coherent x
  with Fin.splitAt b x in split
... | inj₁ y =
  cong (bound Translation.++ₛ source)
    (sym (cong (Source._↑*_ ρ b) left-equal)) ■
  cong (bound Translation.++ₛ source) (lift*-↑ˡ ρ b y) ■
  ++ₛ-lookupˡ bound source y
  where
  left-equal : y ↑ˡ n ≡ x
  left-equal =
    sym (cong (Fin.join b n) split) ■ Fin.join-splitAt b n x
... | inj₂ y =
  cong (bound Translation.++ₛ source)
    (sym (cong (Source._↑*_ ρ b) right-equal)) ■
  cong (bound Translation.++ₛ source) (lift*-↑ʳ ρ b y) ■
  ++ₛ-lookupʳ bound source (ρ y) ■
  coherent y
  where
  right-equal : b ↑ʳ y ≡ x
  right-equal =
    sym (cong (Fin.join b n) split) ■ Fin.join-splitAt b n x

flattenChannels-rename :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.⋯ₚ ρ)))
  (source : Translation.Env n′ (2 *ℕ c))
  (target : Translation.Env n (2 *ℕ c)) →
  ((x : 𝔽 n) → source (ρ x) ≡ target x) →
  transportChannels P ρ
    (proj₁ (flattenOriented (P Typed.⋯ₚ ρ) channels source)) ≡
  proj₁ (flattenOriented P
    (transportChannels P ρ channels) target)
flattenChannels-rename (Typed.⟪ e ⟫) ρ [] source target coherent = refl
flattenChannels-rename (P Typed.∥ Q) ρ channels source target coherent
  with flattenOriented (P Typed.⋯ₚ ρ)
         (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels) source
         in flatP
     | flattenOriented (Q Typed.⋯ₚ ρ)
         (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels) source
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ
  rewrite take-++ˡ channelsP channelsQ
        | drop-++ˡ channelsP channelsQ
        | take-++ˡ
            (transportChannels P ρ
              (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
            (transportChannels Q ρ
              (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
        | drop-++ˡ
            (transportChannels P ρ
              (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
            (transportChannels Q ρ
              (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
  = cong₂ V._++_
      (cong (transportChannels P ρ) (sym (cong proj₁ flatP)) ■
       flattenChannels-rename P ρ
         (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels)
         source target coherent)
      (cong (transportChannels Q ρ) (sym (cong proj₁ flatQ)) ■
       flattenChannels-rename Q ρ
         (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels)
         source target coherent)
flattenChannels-rename (Typed.ν B₁ B₂ P) ρ
  (channel ∷ channels) source target coherent
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂
  rewrite flattenChannels-rename P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ source)
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ target)
    (prefix-coherent ρ coherent) = refl

flattenThreads-rename :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.⋯ₚ ρ)))
  (source : Translation.Env n′ (2 *ℕ c))
  (target : Translation.Env n (2 *ℕ c)) →
  ((x : 𝔽 n) → source (ρ x) ≡ target x) →
  transportProcesses P ρ
    (proj₂ (flattenOriented (P Typed.⋯ₚ ρ) channels source)) ≡
  proj₂ (flattenOriented P
    (transportChannels P ρ channels) target)
flattenThreads-rename (Typed.⟪ e ⟫) ρ [] source target coherent =
  cong (_∷ []) (T[_]-⋯ᵣ e ρ source ■ T[_]-Env-cong e coherent)
flattenThreads-rename (P Typed.∥ Q) ρ channels source target coherent
  with flattenOriented (P Typed.⋯ₚ ρ)
         (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels) source
         in flatP
     | flattenOriented (Q Typed.⋯ₚ ρ)
         (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels) source
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ
  rewrite take-++ˡ threadsP threadsQ
        | drop-++ˡ threadsP threadsQ
        | take-++ˡ
            (transportChannels P ρ
              (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
            (transportChannels Q ρ
              (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
        | drop-++ˡ
            (transportChannels P ρ
              (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
            (transportChannels Q ρ
              (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels))
  = cong₂ V._++_
      (cong (transportProcesses P ρ) (sym (cong proj₂ flatP)) ■
       flattenThreads-rename P ρ
         (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) channels)
         source target coherent)
      (cong (transportProcesses Q ρ) (sym (cong proj₂ flatQ)) ■
       flattenThreads-rename Q ρ
         (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) channels)
         source target coherent)
flattenThreads-rename (Typed.ν B₁ B₂ P) ρ
  (channel ∷ channels) source target coherent
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  flattenThreads-rename P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ source)
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ target)
    (prefix-coherent ρ coherent)
