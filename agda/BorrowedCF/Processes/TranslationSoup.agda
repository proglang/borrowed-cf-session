module BorrowedCF.Processes.TranslationSoup where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Processes.Translation as 𝐔Trans
import BorrowedCF.Terms.Base as 𝐔Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Nat.Variables

variable c : ℕ

channelCount : 𝐔.Proc n → ℕ
channelCount (𝐔.⟪ e ⟫) = 0
channelCount (P 𝐔.∥ Q) = channelCount P + channelCount Q
channelCount (𝐔.ν P) = suc (channelCount P)
channelCount (𝐔.φ f P) = channelCount P

processCount : 𝐔.Proc n → ℕ
processCount (𝐔.⟪ e ⟫) = 1
processCount (P 𝐔.∥ Q) = processCount P + processCount Q
processCount (𝐔.ν P) = processCount P
processCount (𝐔.φ f P) = processCount P

-- Number of phi cells that the first process in a subtree already hosts.
-- An enclosing phi binder is appended after these cells.
firstFlags : 𝐔.Proc n → ℕ
firstFlags (𝐔.⟪ e ⟫) = 0
firstFlags (P 𝐔.∥ Q) = firstFlags P
firstFlags (𝐔.ν P) = firstFlags P
firstFlags (𝐔.φ f P) = suc (firstFlags P)

T[_] : 𝐔Tm.Tm n → 𝐒Tm.Sub n n′ m → 𝐒Tm.Tm n′ m
T[ 𝐔Tm.` x ] σ = σ x
T[ 𝐔Tm.K c ] σ = 𝐒Tm.K c
T[ 𝐔Tm.ƛ e ] σ = 𝐒Tm.ƛ (T[ e ] (𝐒Tm.liftSub σ))
T[ 𝐔Tm.μ e ] σ = 𝐒Tm.μ (T[ e ] (𝐒Tm.liftSub σ))
T[ e₁ 𝐔Tm.·⟨ d ⟩ e₂ ] σ =
  (T[ e₁ ] σ) 𝐒Tm.·⟨ d ⟩ (T[ e₂ ] σ)
T[ e₁ 𝐔Tm.; e₂ ] σ = (T[ e₁ ] σ) 𝐒Tm.; (T[ e₂ ] σ)
T[ e₁ 𝐔Tm.⊗ e₂ ] σ = (T[ e₁ ] σ) 𝐒Tm.⊗ (T[ e₂ ] σ)
T[ 𝐔Tm.`let e₁ `in e₂ ] σ =
  𝐒Tm.`let (T[ e₁ ] σ) `in (T[ e₂ ] (𝐒Tm.liftSub σ))
T[ 𝐔Tm.`let⊗ e₁ `in e₂ ] σ =
  𝐒Tm.`let⊗ (T[ e₁ ] σ) `in
    (T[ e₂ ] (𝐒Tm.liftSub (𝐒Tm.liftSub σ)))
T[ 𝐔Tm.`inj i e ] σ = 𝐒Tm.`inj i (T[ e ] σ)
T[ 𝐔Tm.`case e `of⟨ e₁ ; e₂ ⟩ ] σ =
  𝐒Tm.`case (T[ e ] σ) `of⟨ (T[ e₁ ] (𝐒Tm.liftSub σ))
                             ; (T[ e₂ ] (𝐒Tm.liftSub σ)) ⟩

translateFlag : 𝐔.Flag → 𝐒.Flag
translateFlag 𝐔.drop = 𝐒.drop
translateFlag 𝐔.acq = 𝐒.acq

firstProcess :
  (P : 𝐔.Proc n) → Vec (𝔽 m) (processCount P) → 𝔽 m
firstProcess (𝐔.⟪ e ⟫) (j ∷ []) = j
firstProcess (P 𝐔.∥ Q) js =
  firstProcess P (V.take (processCount P) js)
firstProcess (𝐔.ν P) js = firstProcess P js
firstProcess (𝐔.φ f P) js = firstProcess P js

appendFirstFlag :
  (P : 𝐔.Proc n) → 𝐒.Flag →
  Vec (𝐒.Thread c m) (processCount P) →
  Vec (𝐒.Thread c m) (processCount P)
appendFirstFlag (𝐔.⟪ e ⟫) f ((t , fs) ∷ []) =
  (t , fs ++ f ∷ []) ∷ []
appendFirstFlag {c = c} (P 𝐔.∥ Q) f ts =
  appendFirstFlag {c = c} P f (V.take (processCount P) ts)
    V.++ V.drop (processCount P) ts
appendFirstFlag {c = c} (𝐔.ν P) f ts = appendFirstFlag {c = c} P f ts
appendFirstFlag {c = c} (𝐔.φ g P) f ts = appendFirstFlag {c = c} P f ts

restrictionSub :
  𝔽 c → 𝐒Tm.Sub n (2 *ℕ c) m → 𝐒Tm.Sub (2 + n) (2 *ℕ c) m
restrictionSub i σ zero = 𝐒Tm.` 𝐒.leftEnd i
restrictionSub i σ (suc zero) = 𝐒Tm.` 𝐒.rightEnd i
restrictionSub i σ (suc (suc x)) = σ x

phiSub :
  𝔽 m → ℕ → 𝐒Tm.Sub n c m → 𝐒Tm.Sub (1 + n) c m
phiSub j k σ zero = 𝐒Tm.`phi (j , k)
phiSub j k σ (suc x) = σ x

flatten :
  (P : 𝐔.Proc n) →
  Vec (𝔽 c) (channelCount P) →
  Vec (𝔽 m) (processCount P) →
  𝐒Tm.Sub n (2 *ℕ c) m →
  Vec (𝐒.Thread c m) (processCount P)
flatten (𝐔.⟪ e ⟫) [] (j ∷ []) σ = (T[ e ] σ , []) ∷ []
flatten (P 𝐔.∥ Q) cs js σ =
  flatten P
    (V.take (channelCount P) cs)
    (V.take (processCount P) js)
    σ
  V.++
  flatten Q
    (V.drop (channelCount P) cs)
    (V.drop (processCount P) js)
    σ
flatten (𝐔.ν P) (i ∷ cs) js σ =
  flatten P cs js (restrictionSub i σ)
flatten {c = c} (𝐔.φ f P) cs js σ =
  appendFirstFlag {c = c} P (translateFlag f)
    (flatten P cs js
      (phiSub (firstProcess P js) (firstFlags P) σ))

SoupConfig : Set
SoupConfig = Σ[ c ∈ ℕ ] Σ[ m ∈ ℕ ] 𝐒.Config c m

flattenClosed : 𝐔.Proc 0 → SoupConfig
flattenClosed P =
  channelCount P , processCount P ,
  𝐒.config
    (V.replicate (channelCount P) false)
    (flatten P
      (V.allFin (channelCount P))
      (V.allFin (processCount P))
      λ ())

U[_] : 𝐓.Proc 0 → SoupConfig
U[ P ] = flattenClosed (𝐔Trans.U[ P ] λ ())
