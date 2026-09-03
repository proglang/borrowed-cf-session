module BorrowedCF.Simulation.ForwardSoup.Translation where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)

open Nat.Variables
open Fin.Patterns

channelCount-rename :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Translation.channelCount (P Typed.⋯ₚ ρ) ≡
  Translation.channelCount P
channelCount-rename (Typed.⟪ e ⟫) ρ = refl
channelCount-rename (P Typed.∥ Q) ρ =
  cong₂ _+_ (channelCount-rename P ρ) (channelCount-rename Q ρ)
channelCount-rename (Typed.ν B₁ B₂ P) ρ =
  cong suc (channelCount-rename P
    (Source._↑*_ ρ (sum B₁ + sum B₂)))

processCount-rename :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Translation.processCount (P Typed.⋯ₚ ρ) ≡
  Translation.processCount P
processCount-rename (Typed.⟪ e ⟫) ρ = refl
processCount-rename (P Typed.∥ Q) ρ =
  cong₂ _+_ (processCount-rename P ρ) (processCount-rename Q ρ)
processCount-rename (Typed.ν B₁ B₂ P) ρ =
  processCount-rename P (Source._↑*_ ρ (sum B₁ + sum B₂))

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
  with Translation.UBFrom 1 (b′ ∷ B) r
         (SoupTerm.`phi (r , 0) , c , e₂)
... | sigma , flags =
  SoupTerm.`phi (r , 0) , refl
UB-head (suc b) (b′ ∷ B) r c e₁ e₂
  with Translation.UBFrom 1 (b′ ∷ B) r
         (SoupTerm.`phi (r , 0) , c , e₂)
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

UBFrom-Value :
  ∀ k (B : Typed.BindGroup) (r : 𝔽 n)
    {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupExpression.Value e₁ → SoupExpression.Value e₂ →
  ValueEnv (proj₁ (Translation.UBFrom k B r (e₁ , c , e₂)))
UBFrom-Value k [] r V₁ V₂ ()
UBFrom-Value k (b ∷ []) r {e₁} {e₂} {c} V₁ V₂ =
  subst
    (λ k → ValueEnv (Translation.Ub[ k ] (e₁ , c , e₂)))
    (sym (+-identityʳ b))
    (Ub-Value b V₁ V₂)
UBFrom-Value k (b ∷ B@(b′ ∷ B′)) r {e₁} {e₂} {c} V₁ V₂ y
  with Translation.UBFrom (suc k) B r
         (SoupTerm.`phi (r , k) , c , e₂) in ubEq
     | UBFrom-Value (suc k) B r SoupExpression.V-phi V₂
... | sigma , flags | Vsigma with Fin.splitAt b y
...   | inj₁ x = Ub-Value b V₁ SoupExpression.V-phi x
...   | inj₂ x =
  subst SoupExpression.Value
    (cong (λ result → proj₁ result x) ubEq)
    (Vsigma x)

UB-Value :
  ∀ (B : Typed.BindGroup) (r : 𝔽 n)
    {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupExpression.Value e₁ → SoupExpression.Value e₂ →
  ValueEnv (proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)))
UB-Value = UBFrom-Value zero
