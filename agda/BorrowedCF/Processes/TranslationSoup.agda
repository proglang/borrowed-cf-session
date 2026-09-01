module BorrowedCF.Processes.TranslationSoup where

open import Data.Nat.ListAction using (sum)
open import Data.Sum using ([_,_]′)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Nat.Variables

variable a b c : ℕ

Env : ℕ → ℕ → Set
Env n n′ = 𝔽 n → 𝐒Tm.Tm n′

liftEnv : Env n n′ → Env (1 + n) (1 + n′)
liftEnv σ zero = 𝐒Tm.` zero
liftEnv σ (suc x) = 𝐒Tm.wk (σ x)

T[_] : 𝐓Tm.Tm n → Env n n′ → 𝐒Tm.Tm n′
T[ 𝐓Tm.` x ] σ = σ x
T[ 𝐓Tm.K c ] σ = 𝐒Tm.K c
T[ 𝐓Tm.ƛ e ] σ = 𝐒Tm.ƛ (T[ e ] (liftEnv σ))
T[ 𝐓Tm.μ e ] σ = 𝐒Tm.μ (T[ e ] (liftEnv σ))
T[ e₁ 𝐓Tm.·⟨ d ⟩ e₂ ] σ =
  (T[ e₁ ] σ) 𝐒Tm.·⟨ d ⟩ (T[ e₂ ] σ)
T[ e₁ 𝐓Tm.; e₂ ] σ = (T[ e₁ ] σ) 𝐒Tm.; (T[ e₂ ] σ)
T[ e₁ 𝐓Tm.⊗ e₂ ] σ = (T[ e₁ ] σ) 𝐒Tm.⊗ (T[ e₂ ] σ)
T[ 𝐓Tm.`let e₁ `in e₂ ] σ =
  𝐒Tm.`let (T[ e₁ ] σ) `in (T[ e₂ ] (liftEnv σ))
T[ 𝐓Tm.`let⊗ e₁ `in e₂ ] σ =
  𝐒Tm.`let⊗ (T[ e₁ ] σ) `in (T[ e₂ ] (liftEnv (liftEnv σ)))
T[ 𝐓Tm.`inj i e ] σ = 𝐒Tm.`inj i (T[ e ] σ)
T[ 𝐓Tm.`case e `of⟨ e₁ ; e₂ ⟩ ] σ =
  𝐒Tm.`case (T[ e ] σ) `of⟨ (T[ e₁ ] (liftEnv σ))
                               ; (T[ e₂ ] (liftEnv σ)) ⟩

UChan : ℕ → Set
UChan n = 𝐒Tm.Tm n × 𝔽 n × 𝐒Tm.Tm n

chanTriple : UChan n → 𝐒Tm.Tm n
chanTriple (e₁ , c , e₂) = (e₁ 𝐒Tm.⊗ (𝐒Tm.` c)) 𝐒Tm.⊗ e₂

ϕ[_] : ℕ → 𝐒.Flag
ϕ[ zero ] = 𝐒.acq
ϕ[ suc _ ] = 𝐒.drop

syncs : 𝐓.BindGroup → ℕ
syncs [] = 0
syncs (_ ∷ []) = 0
syncs (_ ∷ B@(_ ∷ _)) = suc (syncs B)

infixr 5 _++ₛ_

_++ₛ_ : Env a n → Env b n → Env (a + b) n
_++ₛ_ {a} σ₁ σ₂ i = [ σ₁ , σ₂ ]′ (Fin.splitAt a i)

Ub[_] : (b : ℕ) → UChan n → Env b n
Ub[ 1 ] c zero = chanTriple c
Ub[ suc (suc b) ] (e₁ , c , e₂) zero =
  chanTriple (e₁ , c , 𝐒Tm.*)
Ub[ suc (suc b) ] (e₁ , c , e₂) (suc x) =
  Ub[ suc b ] (𝐒Tm.* , c , e₂) x

BindResult : 𝐓.BindGroup → ℕ → Set
BindResult B n = Env (sum B) n × List 𝐒.Flag

UB[_] : (B : 𝐓.BindGroup) → 𝔽 n → UChan n → BindResult B n
UB[ [] ] r c = (λ ()) , []
UB[ b ∷ [] ] r c = Ub[ b + 0 ] c , []
UB[ b ∷ B@(_ ∷ _) ] r (e₁ , c , e₂)
  with UB[ B ] r (𝐒Tm.`phi (r , syncs B) , c , e₂)
... | σ , fs =
  ( (λ y →
      [ Ub[ b ] (e₁ , c , 𝐒Tm.`phi (r , syncs B)) , σ ]′
        (Fin.splitAt b y))
  , fs ++ ϕ[ b ] ∷ []
  )

channelCount : 𝐓.Proc n → ℕ
channelCount (𝐓.⟪ e ⟫) = 0
channelCount (P 𝐓.∥ Q) = channelCount P + channelCount Q
channelCount (𝐓.ν B₁ B₂ P) = suc (channelCount P)

processCount : 𝐓.Proc n → ℕ
processCount (𝐓.⟪ e ⟫) = 1
processCount (P 𝐓.∥ Q) = processCount P + processCount Q
processCount (𝐓.ν B₁ B₂ P) = processCount P

flatten :
  (P : 𝐓.Proc n) →
  Vec (𝔽 c) (channelCount P) →
  Env n (2 *ℕ c) →
  Vec 𝐒.Channel (channelCount P) ×
  Vec (𝐒.Thread c) (processCount P)
flatten (𝐓.⟪ e ⟫) [] σ = [] , T[ e ] σ ∷ []
flatten (P 𝐓.∥ Q) cs σ
  with flatten P (V.take (channelCount P) cs) σ
     | flatten Q (V.drop (channelCount P) cs) σ
... | cs₁ , ts₁ | cs₂ , ts₂ = cs₁ V.++ cs₂ , ts₁ V.++ ts₂
flatten (𝐓.ν B₁ B₂ P) (i ∷ cs) σ
  with UB[ B₁ ] (𝐒.leftEnd i) (𝐒Tm.* , 𝐒.leftEnd i , 𝐒Tm.*)
     | UB[ B₂ ] (𝐒.rightEnd i) (𝐒Tm.* , 𝐒.rightEnd i , 𝐒Tm.*)
... | σ₁ , fs₁ | σ₂ , fs₂
  with flatten P cs ((σ₁ ++ₛ σ₂) ++ₛ σ)
... | channels , threads =
  (true , fs₁ , fs₂) ∷ channels , threads

SoupConfig : Set
SoupConfig = Σ[ c ∈ ℕ ] Σ[ m ∈ ℕ ] 𝐒.Config c m

U[_] : 𝐓.Proc 0 → SoupConfig
U[ P ] with flatten P (V.allFin (channelCount P)) (λ ())
... | channels , threads =
  channelCount P , processCount P , 𝐒.config channels threads
