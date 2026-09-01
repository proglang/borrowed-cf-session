module BorrowedCF.Simulation.ForwardSoup.Translation where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Terms.BaseSoup as SoupTerm
open import BorrowedCF.Simulation.ForwardSoup.Image
  using (SoupImage; canonicalChannels; channelEmbedding; live-channel)
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)

open Nat.Variables
open Fin.Patterns

variable c : ℕ

++ₛ-lookupˡ :
  ∀ {a b n} (sigma₁ : Translation.Env a n)
    (sigma₂ : Translation.Env b n) (i : 𝔽 a) →
  (sigma₁ Translation.++ₛ sigma₂) (i ↑ˡ b) ≡ sigma₁ i
++ₛ-lookupˡ {a = a} {b = b} sigma₁ sigma₂ i =
  cong [ sigma₁ , sigma₂ ]′ (Fin.splitAt-↑ˡ a i b)

++ₛ-lookupʳ :
  ∀ {a b n} (sigma₁ : Translation.Env a n)
    (sigma₂ : Translation.Env b n) (i : 𝔽 b) →
  (sigma₁ Translation.++ₛ sigma₂) (a ↑ʳ i) ≡ sigma₂ i
++ₛ-lookupʳ {a = a} {b = b} sigma₁ sigma₂ i =
  cong [ sigma₁ , sigma₂ ]′ (Fin.splitAt-↑ʳ a b i)

++ₛ-Value :
  ∀ {a b n} {sigma₁ : Translation.Env a n}
    {sigma₂ : Translation.Env b n} →
  ValueEnv sigma₁ → ValueEnv sigma₂ →
  ValueEnv (sigma₁ Translation.++ₛ sigma₂)
++ₛ-Value {a = a} Vsigma₁ Vsigma₂ i with Fin.splitAt a i
... | inj₁ x = Vsigma₁ x
... | inj₂ x = Vsigma₂ x

UB-head :
  ∀ b (B : Typed.BindGroup) (r c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
  Σ[ e₂′ ∈ SoupTerm.Tm n ]
    proj₁ (Translation.UB[ suc b ∷ B ] r (e₁ , c , e₂)) 0F ≡
    Translation.chanTriple (e₁ , c , e₂′)
UB-head zero [] r c e₁ e₂ = e₂ , refl
UB-head (suc b) [] r c e₁ e₂ = SoupTerm.* , refl
UB-head zero (b′ ∷ B) r c e₁ e₂
  with Translation.UB[ b′ ∷ B ] r
         (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , c , e₂)
... | sigma , flags =
  SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , refl
UB-head (suc b) (b′ ∷ B) r c e₁ e₂
  with Translation.UB[ b′ ∷ B ] r
         (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , c , e₂)
... | sigma , flags = SoupTerm.* , refl

chanTriple-value :
  ∀ {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupExpression.Value e₁ → SoupExpression.Value e₂ →
  SoupExpression.Value (Translation.chanTriple (e₁ , c , e₂))
chanTriple-value V₁ V₂ =
  SoupExpression.V-⊗ (SoupExpression.V-⊗ V₁ SoupExpression.V-`) V₂

Ub-Value :
  ∀ b {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupExpression.Value e₁ → SoupExpression.Value e₂ →
  ValueEnv (Translation.Ub[ b ] (e₁ , c , e₂))
Ub-Value zero V₁ V₂ ()
Ub-Value (suc zero) V₁ V₂ zero = chanTriple-value V₁ V₂
Ub-Value (suc (suc b)) V₁ V₂ zero =
  chanTriple-value V₁ SoupExpression.V-K
Ub-Value (suc (suc b)) V₁ V₂ (suc x) =
  Ub-Value (suc b) SoupExpression.V-K V₂ x

UB-Value :
  ∀ (B : Typed.BindGroup) (r : 𝔽 n)
    {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupExpression.Value e₁ → SoupExpression.Value e₂ →
  ValueEnv (proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)))
UB-Value [] r V₁ V₂ ()
UB-Value (b ∷ []) r {e₁} {e₂} {c} V₁ V₂ =
  subst
    (λ k → ValueEnv (Translation.Ub[ k ] (e₁ , c , e₂)))
    (sym (+-identityʳ b))
    (Ub-Value b V₁ V₂)
UB-Value (b ∷ B@(b′ ∷ B′)) r {e₁} {e₂} {c} V₁ V₂ y
  with Translation.UB[ B ] r
         (SoupTerm.`phi (r , Translation.syncs B) , c , e₂) in ubEq
     | UB-Value B r SoupExpression.V-phi V₂
... | sigma , flags | Vsigma with Fin.splitAt b y
...   | inj₁ x = Ub-Value b V₁ SoupExpression.V-phi x
...   | inj₂ x =
  subst SoupExpression.Value
    (cong (λ result → proj₁ result x) ubEq)
    (Vsigma x)

flatten-channel-open :
  (P : Typed.Proc n)
  (cs : Vec (𝔽 c) (Translation.channelCount P))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.channelCount P)) →
  proj₁ (lookup (proj₁ (Translation.flatten P cs sigma)) i) ≡ true
flatten-channel-open (Typed.⟪ e ⟫) [] sigma ()
flatten-channel-open (P Typed.∥ Q) cs sigma i
  with Translation.flatten P (V.take (Translation.channelCount P) cs) sigma in flatP
     | Translation.flatten Q (V.drop (Translation.channelCount P) cs) sigma in flatQ
     | Fin.splitAt (Translation.channelCount P) i in split
... | channels₁ , threads₁ | channels₂ , threads₂ | inj₁ j =
  subst
    (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
    (sym (cong (Fin.join (Translation.channelCount P)
                    (Translation.channelCount Q)) split) ■
     Fin.join-splitAt (Translation.channelCount P)
       (Translation.channelCount Q) i)
    (cong proj₁ (V.lookup-++ˡ channels₁ channels₂ j) ■
     cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatP) ■
     flatten-channel-open P
       (V.take (Translation.channelCount P) cs) sigma j)
... | channels₁ , threads₁ | channels₂ , threads₂ | inj₂ j =
  subst
    (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
    (sym (cong (Fin.join (Translation.channelCount P)
                    (Translation.channelCount Q)) split) ■
     Fin.join-splitAt (Translation.channelCount P)
       (Translation.channelCount Q) i)
    (cong proj₁ (V.lookup-++ʳ channels₁ channels₂ j) ■
     cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatQ) ■
     flatten-channel-open Q
       (V.drop (Translation.channelCount P) cs) sigma j)
flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) sigma zero = refl
flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) sigma (suc j)
  with Translation.UB[ B₁ ] (Soup.leftEnd i)
         (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)
     | Translation.UB[ B₂ ] (Soup.rightEnd i)
         (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  flatten-channel-open P cs
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) j

canonical-channel-open :
  (P : Typed.Proc 0) (i : 𝔽 (Translation.channelCount P)) →
  proj₁ (lookup (canonicalChannels P) i) ≡ true
canonical-channel-open P i =
  flatten-channel-open P (V.allFin (Translation.channelCount P)) (λ ()) i

image-channel-open :
  {P : Typed.Proc 0} {C : Soup.Config n m} →
  (image : SoupImage P C) (i : 𝔽 (Translation.channelCount P)) →
  proj₁ (lookup (Soup.channels C) (channelEmbedding image i)) ≡ true
image-channel-open {P = P} image i =
  cong proj₁ (live-channel image i) ■ canonical-channel-open P i
