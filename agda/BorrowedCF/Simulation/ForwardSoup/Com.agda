module BorrowedCF.Simulation.ForwardSoup.Com where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Sum using ([_,_]′)
import Data.Fin.Properties as FinP
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
open import BorrowedCF.Processes.Renamings using (𝔽-cast-injective)
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open Typed using (_;_⊢ₚ_)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image

open Nat.Variables
open Fin.Patterns

variable c c′ : ℕ

private
  plug*ˢ : SourceReduction.Frame* n → Source.Tm n → Source.Tm n
  plug*ˢ = SourceReduction._[_]*

  plug*ᵘ : SoupExpression.Frame* n → SoupTerm.Tm n → SoupTerm.Tm n
  plug*ᵘ = SoupExpression._[_]*

  chanTriple : SoupTerm.Tm n → 𝔽 n → SoupTerm.Tm n → SoupTerm.Tm n
  chanTriple e₁ x e₂ = Translation.chanTriple (e₁ , x , e₂)

  emptyEnv : Translation.Env 0 n
  emptyEnv ()

  emptyValueEnv : {n : ℕ} → ValueEnv (emptyEnv {n = n})
  emptyValueEnv ()

  ++ₛ-Value :
    {a b n : ℕ} {σ₁ : Translation.Env a n} {σ₂ : Translation.Env b n} →
    ValueEnv σ₁ → ValueEnv σ₂ → ValueEnv (σ₁ Translation.++ₛ σ₂)
  ++ₛ-Value {a = a} V₁ V₂ x with Fin.splitAt a x
  ... | inj₁ y = V₁ y
  ... | inj₂ y = V₂ y

  ++ₛ-lookupˡ :
    ∀ {a b n} (σ₁ : Translation.Env a n)
      (σ₂ : Translation.Env b n) (i : 𝔽 a) →
    (σ₁ Translation.++ₛ σ₂) (i ↑ˡ b) ≡ σ₁ i
  ++ₛ-lookupˡ {a = a} {b = b} σ₁ σ₂ i =
    cong [ σ₁ , σ₂ ]′ (Fin.splitAt-↑ˡ a i b)

  ++ₛ-lookupʳ :
    ∀ {a b n} (σ₁ : Translation.Env a n)
      (σ₂ : Translation.Env b n) (i : 𝔽 b) →
    (σ₁ Translation.++ₛ σ₂) (a ↑ʳ i) ≡ σ₂ i
  ++ₛ-lookupʳ {a = a} {b = b} σ₁ σ₂ i =
    cong [ σ₁ , σ₂ ]′ (Fin.splitAt-↑ʳ a b i)

  Bˢ : ℕ → Typed.BindGroup → Typed.BindGroup
  Bˢ b B = suc (suc b) ∷ B

  Bᵗ : ℕ → Typed.BindGroup → Typed.BindGroup
  Bᵗ b B = suc b ∷ B

  head-var :
    ∀ b B →
    𝔽 (sum (Bˢ b B))
  head-var b B = 0F

  send-var :
    ∀ b₁ b₂ B₁ B₂ →
    𝔽 (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0)
  send-var b₁ b₂ B₁ B₂ = 0F

  wkρ :
    ∀ b₁ b₂ B₁ B₂ →
    𝔽 (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    𝔽 (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0)
  wkρ b₁ b₂ B₁ B₂ =
    Source.wkₚ (suc b₁ + sum B₁) (suc b₂ + sum B₂)

  recv-var :
    ∀ b₁ b₂ B₁ B₂ →
    𝔽 (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0)
  recv-var b₁ b₂ B₁ B₂ =
    Source.wkʳ 0 (Source.wkˡ (suc (suc b₁) + sum B₁) 0F)

  comSource :
    ∀ b₁ b₂ B₁ B₂ →
    SourceReduction.Frame* (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    SourceReduction.Frame* (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Typed.Proc (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Source.Tm (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Typed.Proc 0
  comSource b₁ b₂ B₁ B₂ E₁ E₂ P e =
    Typed.ν (Bˢ b₁ B₁) (Bˢ b₂ B₂)
      ((Typed.⟪
          plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (wkρ b₁ b₂ B₁ B₂))
            (Source.K Source.`send Source.·¹
              ((Source._⋯_ e (wkρ b₁ b₂ B₁ B₂)) Source.⊗
               (Source.` (send-var b₁ b₂ B₁ B₂))))
        ⟫
        Typed.∥
        Typed.⟪
          plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (wkρ b₁ b₂ B₁ B₂))
            (Source.K Source.`recv Source.·¹
              (Source.` (recv-var b₁ b₂ B₁ B₂)))
        ⟫)
       Typed.∥ (Typed._⋯ₚ_ P (wkρ b₁ b₂ B₁ B₂)))

  comTarget :
    ∀ b₁ b₂ B₁ B₂ →
    SourceReduction.Frame* (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    SourceReduction.Frame* (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Typed.Proc (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Source.Tm (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) →
    Typed.Proc 0
  comTarget b₁ b₂ B₁ B₂ E₁ E₂ P e =
    Typed.ν (Bᵗ b₁ B₁) (Bᵗ b₂ B₂)
      ((Typed.⟪ plug*ˢ E₁ Source.* ⟫
        Typed.∥
        Typed.⟪ plug*ˢ E₂ e ⟫)
       Typed.∥ P)

  channelCount-⋯ₚ :
    (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
    Translation.channelCount (Typed._⋯ₚ_ P ρ) ≡
    Translation.channelCount P
  channelCount-⋯ₚ (Typed.⟪ e ⟫) ρ = refl
  channelCount-⋯ₚ (P Typed.∥ Q) ρ =
    cong₂ _+_ (channelCount-⋯ₚ P ρ) (channelCount-⋯ₚ Q ρ)
  channelCount-⋯ₚ (Typed.ν B₁ B₂ P) ρ =
    cong suc (channelCount-⋯ₚ P (Source._↑*_ ρ (sum B₁ + sum B₂)))

  processCount-⋯ₚ :
    (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
    Translation.processCount (Typed._⋯ₚ_ P ρ) ≡
    Translation.processCount P
  processCount-⋯ₚ (Typed.⟪ e ⟫) ρ = refl
  processCount-⋯ₚ (P Typed.∥ Q) ρ =
    cong₂ _+_ (processCount-⋯ₚ P ρ) (processCount-⋯ₚ Q ρ)
  processCount-⋯ₚ (Typed.ν B₁ B₂ P) ρ =
    processCount-⋯ₚ P (Source._↑*_ ρ (sum B₁ + sum B₂))

  endpoint-cast :
    ∀ {a b : ℕ} (eq : a ≡ b) (i : 𝔽 a) (side : 𝔽 2) →
    Fin.cast (cong (2 *ℕ_) eq) (Soup.endpoint i side) ≡
    Soup.endpoint (Fin.cast eq i) side
  endpoint-cast refl i side =
    FinP.cast-is-id refl (Soup.endpoint i side)
    ■ cong (λ z → Soup.endpoint z side)
        (sym (FinP.cast-is-id refl i))

  cast-suc-channel :
    ∀ {a b : ℕ} (eq : a ≡ b) (i : 𝔽 b) →
    Fin.cast (cong suc (sym eq)) (suc i) ≡
    suc (Fin.cast (sym eq) i)
  cast-suc-channel refl i =
    FinP.cast-is-id refl (suc i)
    ■ cong suc (sym (FinP.cast-is-id refl i))

  UB-flags-cong :
    ∀ (B : Typed.BindGroup) {n₁ n₂ : ℕ}
      (r₁ : 𝔽 n₁) (c₁ : Translation.UChan n₁)
      (r₂ : 𝔽 n₂) (c₂ : Translation.UChan n₂) →
    proj₂ (Translation.UB[ B ] r₁ c₁) ≡
    proj₂ (Translation.UB[ B ] r₂ c₂)
  UB-flags-cong [] r₁ c₁ r₂ c₂ = refl
  UB-flags-cong (b ∷ []) r₁ c₁ r₂ c₂ = refl
  UB-flags-cong (b ∷ B@(b′ ∷ B′)) r₁ (e₁ , c₁ , e₂) r₂ (e₁′ , c₂ , e₂′)
    with Translation.UB[ B ] r₁
           (SoupTerm.`phi (r₁ , Translation.syncs B) , c₁ , e₂)
       | Translation.UB[ B ] r₂
           (SoupTerm.`phi (r₂ , Translation.syncs B) , c₂ , e₂′)
       | UB-flags-cong B r₁
           (SoupTerm.`phi (r₁ , Translation.syncs B) , c₁ , e₂)
           r₂
           (SoupTerm.`phi (r₂ , Translation.syncs B) , c₂ , e₂′)
  ... | σ₁ , fs₁ | σ₂ , fs₂ | eq = cong (_++ Translation.ϕ[ b ] ∷ []) eq

  UB-flags-drop :
    ∀ b B {n : ℕ} (r c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
    proj₂ (Translation.UB[ Bˢ b B ] r (e₁ , c , e₂)) ≡
    proj₂ (Translation.UB[ Bᵗ b B ] r (e₁ , c , e₂))
  UB-flags-drop b [] r c e₁ e₂ = refl
  UB-flags-drop b (b′ ∷ B) r c e₁ e₂
    with Translation.UB[ b′ ∷ B ] r
           (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , c , e₂)
  ... | σ , fs = refl

  Ub-drop :
    ∀ b {n : ℕ} (c : 𝔽 n) (e₂ : SoupTerm.Tm n)
      (x : 𝔽 (suc b)) →
    Translation.Ub[ suc (suc b) ] (SoupTerm.* , c , e₂) (suc x) ≡
    Translation.Ub[ suc b ] (SoupTerm.* , c , e₂) x
  Ub-drop zero c e₂ zero = refl
  Ub-drop (suc b) c e₂ zero = refl
  Ub-drop (suc b) c e₂ (suc x) = Ub-drop b c e₂ x

  UB-env-drop :
    ∀ b B {n : ℕ} (r c : 𝔽 n) (e₂ : SoupTerm.Tm n)
      (x : 𝔽 (sum (Bᵗ b B))) →
    proj₁ (Translation.UB[ Bˢ b B ] r (SoupTerm.* , c , e₂)) (suc x) ≡
    proj₁ (Translation.UB[ Bᵗ b B ] r (SoupTerm.* , c , e₂)) x
  UB-env-drop zero [] r c e₂ 0F = refl
  UB-env-drop (suc b) [] r c e₂ 0F = refl
  UB-env-drop (suc b) [] r c e₂ (suc x) = UB-env-drop b [] r c e₂ x
  UB-env-drop b (b′ ∷ B) r c e₂ x
    with Translation.UB[ b′ ∷ B ] r
           (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , c , e₂)
       | Fin.splitAt (suc b) x
  ... | σ , fs | inj₁ y =
    Ub-drop b c (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B))) y
  ... | σ , fs | inj₂ y = refl

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
  ... | σ , fs =
    SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , refl
  UB-head (suc b) (b′ ∷ B) r c e₁ e₂
    with Translation.UB[ b′ ∷ B ] r
           (SoupTerm.`phi (r , Translation.syncs (b′ ∷ B)) , c , e₂)
  ... | σ , fs = SoupTerm.* , refl

  Ub-ren :
    ∀ b {n n′ : ℕ} (η : 𝔽 n → 𝔽 n′)
      (e₁ : SoupTerm.Tm n) (c : 𝔽 n) (e₂ : SoupTerm.Tm n)
      (x : 𝔽 b) →
    Translation.Ub[ b ] (e₁ , c , e₂) x SoupTerm.⋯ᵣ η ≡
    Translation.Ub[ b ]
      (e₁ SoupTerm.⋯ᵣ η , η c , e₂ SoupTerm.⋯ᵣ η) x
  Ub-ren zero η e₁ c e₂ ()
  Ub-ren (suc zero) η e₁ c e₂ zero = refl
  Ub-ren (suc (suc b)) η e₁ c e₂ zero = refl
  Ub-ren (suc (suc b)) η e₁ c e₂ (suc x) =
    Ub-ren (suc b) η SoupTerm.* c e₂ x

  UB-ren :
    ∀ (B : Typed.BindGroup) {n n′ : ℕ} (η : 𝔽 n → 𝔽 n′)
      (r : 𝔽 n) (e₁ : SoupTerm.Tm n) (c : 𝔽 n)
      (e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
    proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)) x SoupTerm.⋯ᵣ η ≡
    proj₁ (Translation.UB[ B ] (η r)
      (e₁ SoupTerm.⋯ᵣ η , η c , e₂ SoupTerm.⋯ᵣ η)) x
  UB-ren [] η r e₁ c e₂ ()
  UB-ren (b ∷ []) η r e₁ c e₂ x =
    Ub-ren (b + 0) η e₁ c e₂ x
  UB-ren (b ∷ B@(b′ ∷ B′)) η r e₁ c e₂ y
    with UB-ren B η r (SoupTerm.`phi (r , Translation.syncs B)) c e₂
       | Fin.splitAt b y
  ... | IH | inj₁ x =
    Ub-ren b η e₁ c (SoupTerm.`phi (r , Translation.syncs B)) x
  ... | IH | inj₂ x =
    IH x

  chanTriple-coherent :
    {cₛ cₜ o : ℕ}
    {e₁ₛ e₂ₛ : SoupTerm.Tm cₛ} {xₛ : 𝔽 cₛ}
    {e₁ₜ e₂ₜ : SoupTerm.Tm cₜ} {xₜ : 𝔽 cₜ}
    (ρₛ : 𝔽 cₛ → 𝔽 o) (ρₜ : 𝔽 cₜ → 𝔽 o) →
    e₁ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₁ₜ SoupTerm.⋯ᵣ ρₜ →
    ρₛ xₛ ≡ ρₜ xₜ →
    e₂ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₂ₜ SoupTerm.⋯ᵣ ρₜ →
    Translation.chanTriple (e₁ₛ , xₛ , e₂ₛ) SoupTerm.⋯ᵣ ρₛ ≡
    Translation.chanTriple (e₁ₜ , xₜ , e₂ₜ) SoupTerm.⋯ᵣ ρₜ
  chanTriple-coherent ρₛ ρₜ e₁eq xeq e₂eq =
    cong₂ SoupTerm._⊗_
      (cong₂ SoupTerm._⊗_ e₁eq (cong SoupTerm.`_ xeq))
      e₂eq

  Ub-coherent :
    ∀ b {cₛ cₜ o : ℕ}
      {e₁ₛ e₂ₛ : SoupTerm.Tm cₛ} {xₛ : 𝔽 cₛ}
      {e₁ₜ e₂ₜ : SoupTerm.Tm cₜ} {xₜ : 𝔽 cₜ}
      (ρₛ : 𝔽 cₛ → 𝔽 o) (ρₜ : 𝔽 cₜ → 𝔽 o) →
    e₁ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₁ₜ SoupTerm.⋯ᵣ ρₜ →
    ρₛ xₛ ≡ ρₜ xₜ →
    e₂ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₂ₜ SoupTerm.⋯ᵣ ρₜ →
    (i : 𝔽 b) →
    Translation.Ub[ b ] (e₁ₛ , xₛ , e₂ₛ) i SoupTerm.⋯ᵣ ρₛ ≡
    Translation.Ub[ b ] (e₁ₜ , xₜ , e₂ₜ) i SoupTerm.⋯ᵣ ρₜ
  Ub-coherent zero ρₛ ρₜ e₁eq xeq e₂eq ()
  Ub-coherent (suc zero) ρₛ ρₜ e₁eq xeq e₂eq zero =
    chanTriple-coherent ρₛ ρₜ e₁eq xeq e₂eq
  Ub-coherent (suc (suc b)) ρₛ ρₜ e₁eq xeq e₂eq zero =
    chanTriple-coherent ρₛ ρₜ e₁eq xeq refl
  Ub-coherent (suc (suc b)) ρₛ ρₜ e₁eq xeq e₂eq (suc i) =
    Ub-coherent (suc b) ρₛ ρₜ refl xeq e₂eq i

  UB-coherent :
    ∀ (B : Typed.BindGroup) {cₛ cₜ o : ℕ}
      {rₛ xₛ : 𝔽 cₛ} {e₁ₛ e₂ₛ : SoupTerm.Tm cₛ}
      {rₜ xₜ : 𝔽 cₜ} {e₁ₜ e₂ₜ : SoupTerm.Tm cₜ}
      (ρₛ : 𝔽 cₛ → 𝔽 o) (ρₜ : 𝔽 cₜ → 𝔽 o) →
    ρₛ rₛ ≡ ρₜ rₜ →
    e₁ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₁ₜ SoupTerm.⋯ᵣ ρₜ →
    ρₛ xₛ ≡ ρₜ xₜ →
    e₂ₛ SoupTerm.⋯ᵣ ρₛ ≡ e₂ₜ SoupTerm.⋯ᵣ ρₜ →
    (i : 𝔽 (sum B)) →
    proj₁ (Translation.UB[ B ] rₛ (e₁ₛ , xₛ , e₂ₛ)) i
      SoupTerm.⋯ᵣ ρₛ
    ≡
    proj₁ (Translation.UB[ B ] rₜ (e₁ₜ , xₜ , e₂ₜ)) i
      SoupTerm.⋯ᵣ ρₜ
  UB-coherent [] ρₛ ρₜ req e₁eq xeq e₂eq ()
  UB-coherent (b ∷ []) ρₛ ρₜ req e₁eq xeq e₂eq i =
    Ub-coherent (b + 0) ρₛ ρₜ e₁eq xeq e₂eq i
  UB-coherent (b ∷ B@(b′ ∷ B′)) ρₛ ρₜ req e₁eq xeq e₂eq i
    with UB-coherent B ρₛ ρₜ req
           (cong (λ z → SoupTerm.`phi (z , Translation.syncs B)) req)
           xeq e₂eq
       | Fin.splitAt b i
  ... | IH | inj₁ y =
    Ub-coherent b ρₛ ρₜ e₁eq xeq
      (cong (λ z → SoupTerm.`phi (z , Translation.syncs B)) req)
      y
  ... | IH | inj₂ y = IH y

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
  ... | σ , fs | Vσ with Fin.splitAt b y
  ...   | inj₁ x = Ub-Value b V₁ SoupExpression.V-phi x
  ...   | inj₂ x =
    subst SoupExpression.Value
      (cong (λ result → proj₁ result x) ubEq)
      (Vσ x)

  bindFlags : Typed.BindGroup → List Soup.Flag
  bindFlags [] = []
  bindFlags (b ∷ []) = []
  bindFlags (b ∷ B@(_ ∷ _)) = bindFlags B ++ Translation.ϕ[ b ] ∷ []

  UB-flags-shape :
    ∀ (B : Typed.BindGroup) {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    proj₂ (Translation.UB[ B ] r (e₁ , c , e₂)) ≡ bindFlags B
  UB-flags-shape [] r c e₁ e₂ = refl
  UB-flags-shape (b ∷ []) r c e₁ e₂ = refl
  UB-flags-shape (b ∷ B@(b′ ∷ B′)) r c e₁ e₂
    with Translation.UB[ B ] r
           (SoupTerm.`phi (r , Translation.syncs B) , c , e₂)
       | UB-flags-shape B r c
           (SoupTerm.`phi (r , Translation.syncs B)) e₂
  ... | σ , fs | eq = cong (_++ Translation.ϕ[ b ] ∷ []) eq

  channelShape :
    (P : Typed.Proc n) → Vec Soup.Channel (Translation.channelCount P)
  channelShape (Typed.⟪ e ⟫) = []
  channelShape (P Typed.∥ Q) = channelShape P V.++ channelShape Q
  channelShape (Typed.ν B₁ B₂ P) =
    (true , bindFlags B₁ , bindFlags B₂) ∷ channelShape P

  flatten-channels-shape :
    ∀ {c : ℕ} (P : Typed.Proc n)
      (cs : Vec (𝔽 c) (Translation.channelCount P))
      (σ : Translation.Env n (2 *ℕ c)) →
    proj₁ (Translation.flatten P cs σ) ≡ channelShape P
  flatten-channels-shape (Typed.⟪ e ⟫) [] σ = refl
  flatten-channels-shape (P Typed.∥ Q) cs σ
    with Translation.flatten P (V.take (Translation.channelCount P) cs) σ
       | Translation.flatten Q (V.drop (Translation.channelCount P) cs) σ
       | flatten-channels-shape P
           (V.take (Translation.channelCount P) cs) σ
       | flatten-channels-shape Q
           (V.drop (Translation.channelCount P) cs) σ
  ... | channels₁ , threads₁ | channels₂ , threads₂ | eq₁ | eq₂ =
    cong₂ V._++_ eq₁ eq₂
  flatten-channels-shape (Typed.ν B₁ B₂ P) (i ∷ cs) σ
    rewrite UB-flags-shape B₁ (Soup.leftEnd i) (Soup.leftEnd i)
              SoupTerm.* SoupTerm.*
          | UB-flags-shape B₂ (Soup.rightEnd i) (Soup.rightEnd i)
              SoupTerm.* SoupTerm.*
    with Translation.UB[ B₁ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)
       | Translation.UB[ B₂ ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)
       | flatten-channels-shape P cs
           ((proj₁ (Translation.UB[ B₁ ] (Soup.leftEnd i)
               (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
             Translation.++ₛ
             proj₁ (Translation.UB[ B₂ ] (Soup.rightEnd i)
               (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
            Translation.++ₛ σ)
  ... | σ₁ , fs₁ | σ₂ , fs₂ | eq =
    cong ((true , bindFlags B₁ , bindFlags B₂) ∷_) eq

  flatten-channel-open :
    (P : Typed.Proc n)
    (cs : Vec (𝔽 c) (Translation.channelCount P))
    (σ : Translation.Env n (2 *ℕ c))
    (i : 𝔽 (Translation.channelCount P)) →
    proj₁ (lookup (proj₁ (Translation.flatten P cs σ)) i) ≡ true
  flatten-channel-open (Typed.⟪ e ⟫) [] σ ()
  flatten-channel-open (P Typed.∥ Q) cs σ i
    with Translation.flatten P (V.take (Translation.channelCount P) cs) σ in flatP
       | Translation.flatten Q (V.drop (Translation.channelCount P) cs) σ in flatQ
       | Fin.splitAt (Translation.channelCount P) i in split
  ... | channels₁ , threads₁ | channels₂ , threads₂ | inj₁ j =
    subst
      (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
      (sym (cong (Fin.join (Translation.channelCount P)
                      (Translation.channelCount Q)) split)
       ■ Fin.join-splitAt (Translation.channelCount P)
           (Translation.channelCount Q) i)
      (cong proj₁ (V.lookup-++ˡ channels₁ channels₂ j)
       ■ cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatP)
       ■ flatten-channel-open P
           (V.take (Translation.channelCount P) cs) σ j)
  ... | channels₁ , threads₁ | channels₂ , threads₂ | inj₂ j =
    subst
      (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
      (sym (cong (Fin.join (Translation.channelCount P)
                      (Translation.channelCount Q)) split)
       ■ Fin.join-splitAt (Translation.channelCount P)
           (Translation.channelCount Q) i)
      (cong proj₁ (V.lookup-++ʳ channels₁ channels₂ j)
       ■ cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatQ)
       ■ flatten-channel-open Q
           (V.drop (Translation.channelCount P) cs) σ j)
  flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) σ zero = refl
  flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) σ (suc j)
    with Translation.UB[ B₁ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)
       | Translation.UB[ B₂ ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)
  ... | σ₁ , fs₁ | σ₂ , fs₂ =
    flatten-channel-open P cs
      ((σ₁ Translation.++ₛ σ₂) Translation.++ₛ σ) j

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

  subst-Vec-++ :
    ∀ {A : Set} {a a′ b b′ : ℕ}
      (eq₁ : a ≡ a′) (eq₂ : b ≡ b′)
      (xs : Vec A a) (ys : Vec A b) →
    subst (Vec A) (cong₂ _+_ eq₁ eq₂) (xs V.++ ys) ≡
    subst (Vec A) eq₁ xs V.++ subst (Vec A) eq₂ ys
  subst-Vec-++ refl refl xs ys = refl

  subst-Vec-∷ :
    ∀ {A : Set} {a b : ℕ} (eq : a ≡ b) (x : A) (xs : Vec A a) →
    subst (Vec A) (cong suc eq) (x ∷ xs) ≡
    x ∷ subst (Vec A) eq xs
  subst-Vec-∷ refl x xs = refl

  channelShape-⋯ₚ :
    (P : Typed.Proc n) (θ : 𝔽 n → 𝔽 n′) →
    subst (Vec Soup.Channel) (channelCount-⋯ₚ P θ)
      (channelShape (P Typed.⋯ₚ θ)) ≡ channelShape P
  channelShape-⋯ₚ (Typed.⟪ e ⟫) θ = refl
  channelShape-⋯ₚ (P Typed.∥ Q) θ =
    subst-Vec-++
      (channelCount-⋯ₚ P θ) (channelCount-⋯ₚ Q θ)
      (channelShape (P Typed.⋯ₚ θ)) (channelShape (Q Typed.⋯ₚ θ))
    ■ cong₂ V._++_ (channelShape-⋯ₚ P θ) (channelShape-⋯ₚ Q θ)
  channelShape-⋯ₚ (Typed.ν B₁ B₂ P) θ =
    subst-Vec-∷
      (channelCount-⋯ₚ P (Source._↑*_ θ (sum B₁ + sum B₂)))
      (true , bindFlags B₁ , bindFlags B₂)
      (channelShape
        (P Typed.⋯ₚ (Source._↑*_ θ (sum B₁ + sum B₂))))
    ■ cong ((true , bindFlags B₁ , bindFlags B₂) ∷_)
      (channelShape-⋯ₚ P (Source._↑*_ θ (sum B₁ + sum B₂)))

  lift*-↑ˡ : ∀ {a b} (ρ : 𝔽 a → 𝔽 b) j (y : 𝔽 j) →
    Source._↑*_ ρ j (y ↑ˡ a) ≡ y ↑ˡ b
  lift*-↑ˡ ρ (suc j) zero = refl
  lift*-↑ˡ ρ (suc j) (suc y) = cong suc (lift*-↑ˡ ρ j y)

  lift*-↑ʳ : ∀ {a b} (ρ : 𝔽 a → 𝔽 b) j (w : 𝔽 a) →
    Source._↑*_ ρ j (j ↑ʳ w) ≡ j ↑ʳ ρ w
  lift*-↑ʳ ρ zero w = refl
  lift*-↑ʳ ρ (suc j) w = cong suc (lift*-↑ʳ ρ j w)

  wkₚ-A : ∀ a c {k} (v : 𝔽 a) →
    Source.wkₚ {n = k} a c ((v ↑ˡ c) ↑ˡ k) ≡
    ((Fin.suc v ↑ˡ suc c) ↑ˡ k)
  wkₚ-A a c {k} v =
    cong (λ z → cast₂ (Source._↑*_ Source.weakenᵣ (suc a) z)) step₁
    ■ cong cast₂ step₂
    ■ step₃
    where
    cast₁ : 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
    cast₁ = Fin.cast (cong suc (+-assoc a c k))

    cast₂ : 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) k))

    i : 𝔽 (a + c + k)
    i = (v ↑ˡ c) ↑ˡ k

    toℕi : Fin.toℕ i ≡ Fin.toℕ v
    toℕi = FinP.toℕ-↑ˡ (v ↑ˡ c) k ■ FinP.toℕ-↑ˡ v c

    step₁ : cast₁ (Fin.suc i) ≡ Fin.suc v ↑ˡ (c + k)
    step₁ = FinP.toℕ-injective
      (FinP.toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
       ■ cong suc toℕi
       ■ sym (FinP.toℕ-↑ˡ (Fin.suc v) (c + k)))

    step₂ :
      Source._↑*_ Source.weakenᵣ (suc a) (Fin.suc v ↑ˡ (c + k)) ≡
      Fin.suc v ↑ˡ suc (c + k)
    step₂ = lift*-↑ˡ Source.weakenᵣ (suc a) (Fin.suc v)

    step₃ : cast₂ (Fin.suc v ↑ˡ suc (c + k)) ≡
      (Fin.suc v ↑ˡ suc c) ↑ˡ k
    step₃ = FinP.toℕ-injective
      (FinP.toℕ-cast (sym (+-assoc (suc a) (suc c) k))
         (Fin.suc v ↑ˡ suc (c + k))
       ■ FinP.toℕ-↑ˡ (Fin.suc v) (suc (c + k))
       ■ sym (FinP.toℕ-↑ˡ (Fin.suc v ↑ˡ suc c) k
              ■ FinP.toℕ-↑ˡ (Fin.suc v) (suc c)))

  wkₚ-B : ∀ a c {k} (w : 𝔽 c) →
    Source.wkₚ {n = k} a c ((a ↑ʳ w) ↑ˡ k) ≡
    (((suc a) ↑ʳ Fin.suc w) ↑ˡ k)
  wkₚ-B a c {k} w =
    cong (λ z → cast₂ (Source._↑*_ Source.weakenᵣ (suc a) z)) step₁
    ■ cong cast₂ step₂
    ■ step₃
    where
    cast₁ : 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
    cast₁ = Fin.cast (cong suc (+-assoc a c k))

    cast₂ : 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) k))

    i : 𝔽 (a + c + k)
    i = (a ↑ʳ w) ↑ˡ k

    toℕi : Fin.toℕ i ≡ a + Fin.toℕ w
    toℕi = FinP.toℕ-↑ˡ (a ↑ʳ w) k ■ FinP.toℕ-↑ʳ a w

    step₁ : cast₁ (Fin.suc i) ≡ suc a ↑ʳ (w ↑ˡ k)
    step₁ = FinP.toℕ-injective
      (FinP.toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
       ■ cong suc toℕi
       ■ sym (FinP.toℕ-↑ʳ (suc a) (w ↑ˡ k)
              ■ cong (suc a +_) (FinP.toℕ-↑ˡ w k)))

    step₂ :
      Source._↑*_ Source.weakenᵣ (suc a) (suc a ↑ʳ (w ↑ˡ k)) ≡
      suc a ↑ʳ Fin.suc (w ↑ˡ k)
    step₂ = lift*-↑ʳ Source.weakenᵣ (suc a) (w ↑ˡ k)

    step₃ : cast₂ (suc a ↑ʳ Fin.suc (w ↑ˡ k)) ≡
      (suc a ↑ʳ Fin.suc w) ↑ˡ k
    step₃ = FinP.toℕ-injective
      (FinP.toℕ-cast (sym (+-assoc (suc a) (suc c) k))
         (suc a ↑ʳ Fin.suc (w ↑ˡ k))
       ■ FinP.toℕ-↑ʳ (suc a) (Fin.suc (w ↑ˡ k))
       ■ cong (λ t → suc a + suc t) (FinP.toℕ-↑ˡ w k)
       ■ sym (FinP.toℕ-↑ˡ (suc a ↑ʳ Fin.suc w) k
              ■ FinP.toℕ-↑ʳ (suc a) (Fin.suc w)))

  binderEnv :
    ∀ (B₁ B₂ : Typed.BindGroup) {c : ℕ} →
    𝔽 c → Translation.Env (sum B₁ + sum B₂ + 0) (2 *ℕ c)
  binderEnv B₁ B₂ i =
    (proj₁
      (Translation.UB[ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
    Translation.++ₛ
    proj₁
      (Translation.UB[ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
    Translation.++ₛ (λ ())

  sourceEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} →
    𝔽 c →
    Translation.Env (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0) (2 *ℕ c)
  sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} =
    binderEnv (Bˢ b₁ B₁) (Bˢ b₂ B₂)

  targetEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} →
    𝔽 c →
    Translation.Env (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0) (2 *ℕ c)
  targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} =
    binderEnv (Bᵗ b₁ B₁) (Bᵗ b₂ B₂)

  split-left-0 :
    ∀ a b {x : 𝔽 (a + b + 0)} {z : 𝔽 (a + b)} {v : 𝔽 a} →
    Fin.splitAt (a + b) x ≡ inj₁ z →
    Fin.splitAt a z ≡ inj₁ v →
    (v ↑ˡ b) ↑ˡ 0 ≡ x
  split-left-0 a b {x} {z} {v} outer inner =
    cong (λ s → Fin.join a b s ↑ˡ 0) (sym inner)
    ■ cong (λ y → y ↑ˡ 0) (FinP.join-splitAt a b z)
    ■ cong (Fin.join (a + b) 0) (sym outer)
    ■ FinP.join-splitAt (a + b) 0 x

  split-right-0 :
    ∀ a b {x : 𝔽 (a + b + 0)} {z : 𝔽 (a + b)} {w : 𝔽 b} →
    Fin.splitAt (a + b) x ≡ inj₁ z →
    Fin.splitAt a z ≡ inj₂ w →
    (a ↑ʳ w) ↑ˡ 0 ≡ x
  split-right-0 a b {x} {z} {w} outer inner =
    cong (λ s → Fin.join a b s ↑ˡ 0) (sym inner)
    ■ cong (λ y → y ↑ˡ 0) (FinP.join-splitAt a b z)
    ■ cong (Fin.join (a + b) 0) (sym outer)
    ■ FinP.join-splitAt (a + b) 0 x

  source-targetEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ}
      (i : 𝔽 c)
      (x : 𝔽 (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0)) →
    sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i
      (wkρ b₁ b₂ B₁ B₂ x) ≡
    targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i x
  source-targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i x
    with Fin.splitAt (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂)) x in outer
  ... | inj₂ ()
  ... | inj₁ z with Fin.splitAt (sum (Bᵗ b₁ B₁)) z in inner
  ...   | inj₁ v =
    let xeq :
          (v ↑ˡ sum (Bᵗ b₂ B₂)) ↑ˡ 0 ≡ x
        xeq = split-left-0
          (sum (Bᵗ b₁ B₁)) (sum (Bᵗ b₂ B₂)) outer inner
    in
    cong (λ y →
      sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i
        (wkρ b₁ b₂ B₁ B₂ y)) (sym xeq)
    ■ (cong
        (sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i)
        (wkₚ-A (sum (Bᵗ b₁ B₁)) (sum (Bᵗ b₂ B₂)) v)
       ■ ++ₛ-lookupˡ
          {a = sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂)} {b = 0}
          (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
             (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)) Translation.++ₛ
           proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
             (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
          (λ ())
          (Fin.suc v ↑ˡ sum (Bˢ b₂ B₂))
       ■ ++ₛ-lookupˡ
          {a = sum (Bˢ b₁ B₁)} {b = sum (Bˢ b₂ B₂)}
          (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
             (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
          (proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
             (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
          (Fin.suc v)
       ■ UB-env-drop b₁ B₁ (Soup.leftEnd i) (Soup.leftEnd i) SoupTerm.* v)
  ...   | inj₂ w =
    let xeq :
          (sum (Bᵗ b₁ B₁) ↑ʳ w) ↑ˡ 0 ≡ x
        xeq = split-right-0
          (sum (Bᵗ b₁ B₁)) (sum (Bᵗ b₂ B₂)) outer inner
    in
    cong (λ y →
      sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i
        (wkρ b₁ b₂ B₁ B₂ y)) (sym xeq)
    ■ (cong
        (sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i)
        (wkₚ-B (sum (Bᵗ b₁ B₁)) (sum (Bᵗ b₂ B₂)) w)
       ■ ++ₛ-lookupˡ
          {a = sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂)} {b = 0}
          (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
             (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)) Translation.++ₛ
           proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
             (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
          (λ ())
          (sum (Bˢ b₁ B₁) ↑ʳ Fin.suc w)
       ■ ++ₛ-lookupʳ
          {a = sum (Bˢ b₁ B₁)} {b = sum (Bˢ b₂ B₂)}
          (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
             (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
          (proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
             (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
          (Fin.suc w)
       ■ UB-env-drop b₂ B₂ (Soup.rightEnd i) (Soup.rightEnd i) SoupTerm.* w)

  sourceValueEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    ValueEnv (sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i)
  sourceValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value (Bˢ b₁ B₁) (Soup.leftEnd i)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value (Bˢ b₂ B₂) (Soup.rightEnd i)
          SoupExpression.V-K SoupExpression.V-K))
      (λ ())

  targetValueEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    ValueEnv (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i)
  targetValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value (Bᵗ b₁ B₁) (Soup.leftEnd i)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value (Bᵗ b₂ B₂) (Soup.rightEnd i)
          SoupExpression.V-K SoupExpression.V-K))
      (λ ())

  source-renamedEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ}
      (i : 𝔽 c) (ρ : 𝔽 (2 *ℕ c) → 𝔽 n) →
    Translation.Env (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0) n
  source-renamedEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i ρ x =
    sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i x SoupTerm.⋯ᵣ ρ

  source-renamedValueEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c n : ℕ}
      (i : 𝔽 c) (ρ : 𝔽 (2 *ℕ c) → 𝔽 n) →
    ValueEnv (source-renamedEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i ρ)
  source-renamedValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i ρ x =
    SoupExpression.value-rename
      (sourceValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i x)
      ρ

  env₁-lookup :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    let σ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i in
    Σ[ tail ∈ SoupTerm.Tm (2 *ℕ c) ]
      σ (send-var b₁ b₂ B₁ B₂) ≡
      chanTriple SoupTerm.* (Soup.leftEnd i) tail
  env₁-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    let h = UB-head (suc b₁) B₁ (Soup.leftEnd i) (Soup.leftEnd i) SoupTerm.* SoupTerm.* in
    proj₁ h ,
    (++ₛ-lookupˡ
      {a = sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂)}
      {b = 0}
      (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      (λ ())
      (head-var b₁ B₁ ↑ˡ sum (Bˢ b₂ B₂))
    ■ ++ₛ-lookupˡ
      {a = sum (Bˢ b₁ B₁)}
      {b = sum (Bˢ b₂ B₂)}
      (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
      (proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      (head-var b₁ B₁)
    ■ proj₂ h)

  env₂-lookup :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    let σ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i in
    Σ[ tail ∈ SoupTerm.Tm (2 *ℕ c) ]
      σ (recv-var b₁ b₂ B₁ B₂) ≡
      chanTriple SoupTerm.* (Soup.rightEnd i) tail
  env₂-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    let h = UB-head (suc b₂) B₂ (Soup.rightEnd i) (Soup.rightEnd i) SoupTerm.* SoupTerm.* in
    proj₁ h ,
    (++ₛ-lookupˡ
      {a = sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂)}
      {b = 0}
      (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      (λ ())
      (Source.wkˡ (suc (suc b₁) + sum B₁) 0F)
    ■ ++ₛ-lookupʳ
      {a = sum (Bˢ b₁ B₁)}
      {b = sum (Bˢ b₂ B₂)}
      (proj₁ (Translation.UB[ Bˢ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
      (proj₁ (Translation.UB[ Bˢ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      0F
    ■ proj₂ h)

  plugᶠ-ren :
    (E : SourceReduction.Frame n) {e : Source.Tm n} (ρ : 𝔽 n → 𝔽 n′) →
    Source._⋯_ (SourceReduction._[_] E e) ρ ≡
    SourceReduction._[_] (SourceReduction._⋯ᶠ_ E ρ) (Source._⋯_ e ρ)
  plugᶠ-ren (SourceReduction.app₁ e d V?) ρ = refl
  plugᶠ-ren (SourceReduction.app₂ e d V?) ρ = refl
  plugᶠ-ren (SourceReduction.□⊗ e₂) ρ = refl
  plugᶠ-ren (V SourceReduction.⊗□) ρ = refl
  plugᶠ-ren (SourceReduction.□; e₂) ρ = refl
  plugᶠ-ren (SourceReduction.`let-`in e′) ρ = refl
  plugᶠ-ren (SourceReduction.`let⊗-`in e′) ρ = refl
  plugᶠ-ren (SourceReduction.`inj□ i) ρ = refl
  plugᶠ-ren (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) ρ = refl

  plug*ˢ-ren :
    (E : SourceReduction.Frame* n) {e : Source.Tm n} (ρ : 𝔽 n → 𝔽 n′) →
    Source._⋯_ (plug*ˢ E e) ρ ≡
    plug*ˢ (SourceReduction._⋯ᶠ*_ E ρ) (Source._⋯_ e ρ)
  plug*ˢ-ren [] ρ = refl
  plug*ˢ-ren (E ∷ Es) ρ =
    plugᶠ-ren E ρ
    ■ cong (SourceReduction._[_] (SourceReduction._⋯ᶠ_ E ρ))
        (plug*ˢ-ren Es ρ)

  cast-suc-suc≢zero :
    ∀ {a b : ℕ} (eq : 2 + a ≡ 2 + b) (l : 𝔽 a) →
    Fin.cast eq (suc (suc l)) ≢ 0F
  cast-suc-suc≢zero refl l ()

  cast-suc-suc≢one :
    ∀ {a b : ℕ} (eq : 2 + a ≡ 2 + b) (l : 𝔽 a) →
    Fin.cast eq (suc (suc l)) ≢ 1F
  cast-suc-suc≢one refl l ()

  cast-++ :
    ∀ {A : Set} {a a′ b b′ : ℕ}
      (ea : a ≡ a′) (eb : b ≡ b′)
      (xs : Vec A a) (ys : Vec A b) →
    V.cast (cong₂ _+_ ea eb) (xs V.++ ys) ≡
    V.cast ea xs V.++ V.cast eb ys
  cast-++ refl refl xs ys =
    VecP.cast-is-id refl (xs V.++ ys)
    ■ cong₂ V._++_
        (sym (VecP.cast-is-id refl xs))
        (sym (VecP.cast-is-id refl ys))

  cast-∷ :
    ∀ {A : Set} {a a′ : ℕ} (e : a ≡ a′) (x : A) (xs : Vec A a) →
    V.cast (cong suc e) (x ∷ xs) ≡ x ∷ V.cast e xs
  cast-∷ refl x xs =
    VecP.cast-is-id refl (x ∷ xs)
    ■ cong (x ∷_) (sym (VecP.cast-is-id refl xs))

  cast-∷-sym :
    ∀ {A : Set} {a a′ : ℕ} (e : a ≡ a′) (x : A) (xs : Vec A a′) →
    V.cast (sym (cong suc e)) (x ∷ xs) ≡ x ∷ V.cast (sym e) xs
  cast-∷-sym refl x xs =
    VecP.cast-is-id refl (x ∷ xs)
    ■ cong (x ∷_) (sym (VecP.cast-is-id refl xs))

  cast-cancelʳ :
    ∀ {A : Set} {a b : ℕ} (eq : a ≡ b) (xs : Vec A a) →
    xs ≡ V.cast (sym eq) (V.cast eq xs)
  cast-cancelʳ eq xs = sym (VecP.cast-sym eq refl)

  map-cast :
    ∀ {A B : Set} {a a′ : ℕ} (e : a ≡ a′)
      (f : A → B) (xs : Vec A a) →
    V.map f (V.cast e xs) ≡ V.cast e (V.map f xs)
  map-cast refl f xs =
    cong (V.map f) (VecP.cast-is-id refl xs)
    ■ sym (VecP.cast-is-id refl (V.map f xs))

  take-cast-++ :
    ∀ {A : Set} {a a′ b b′ : ℕ}
      (ea : a ≡ a′) (eb : b ≡ b′)
      (xs : Vec A (a + b)) →
    V.take a′ (V.cast (cong₂ _+_ ea eb) xs) ≡
    V.cast ea (V.take a xs)
  take-cast-++ refl refl xs =
    cong (V.take _) (VecP.cast-is-id refl xs)
    ■ sym (VecP.cast-is-id refl (V.take _ xs))

  drop-cast-++ :
    ∀ {A : Set} {a a′ b b′ : ℕ}
      (ea : a ≡ a′) (eb : b ≡ b′)
      (xs : Vec A (a + b)) →
    V.drop a′ (V.cast (cong₂ _+_ ea eb) xs) ≡
    V.cast eb (V.drop a xs)
  drop-cast-++ refl refl xs =
    cong (V.drop _) (VecP.cast-is-id refl xs)
    ■ sym (VecP.cast-is-id refl (V.drop _ xs))

  cast-ν-channels :
    ∀ {A : Set} {n n′ : ℕ}
      (B₁ B₂ : Typed.BindGroup)
      (P : Typed.Proc (sum B₁ + sum B₂ + n))
      (θ : 𝔽 n → 𝔽 n′)
      {c : ℕ}
      (i : A)
      (cs : Vec A (Translation.channelCount P)) →
    V.cast (sym (channelCount-⋯ₚ (Typed.ν B₁ B₂ P) θ)) (i ∷ cs) ≡
    i ∷ V.cast
      (sym (channelCount-⋯ₚ P
        (Source._↑*_ θ (sum B₁ + sum B₂))))
      cs
  cast-ν-channels B₁ B₂ P θ i cs =
    cast-∷-sym
      (channelCount-⋯ₚ P
        (Source._↑*_ θ (sum B₁ + sum B₂)))
      i cs

  tail-cast-ν-channels :
    ∀ {A : Set} {n n′ : ℕ}
      (B₁ B₂ : Typed.BindGroup)
      (P : Typed.Proc (sum B₁ + sum B₂ + n))
      (θ : 𝔽 n → 𝔽 n′)
      {c : ℕ}
      (i : A)
      (cs : Vec A (Translation.channelCount P)) →
    V.tail (V.cast (sym (channelCount-⋯ₚ (Typed.ν B₁ B₂ P) θ)) (i ∷ cs)) ≡
    V.cast
      (sym (channelCount-⋯ₚ P
        (Source._↑*_ θ (sum B₁ + sum B₂))))
      cs
  tail-cast-ν-channels B₁ B₂ P θ {c = c} i cs =
    cong V.tail (cast-ν-channels B₁ B₂ P θ {c = c} i cs)

  renameThreads :
    ∀ {c c′ m : ℕ} →
    (𝔽 (2 *ℕ c) → 𝔽 c′) →
    Vec (Soup.Thread c) m →
    Vec (SoupTerm.Tm c′) m
  renameThreads η = V.map (λ t → t SoupTerm.⋯ᵣ η)

  flatten-ren-threads :
    (P : Typed.Proc n) (θ : 𝔽 n → 𝔽 n′)
    {c c′ : ℕ}
    (cs : Vec (𝔽 c) (Translation.channelCount P))
    (σₛ : Translation.Env n′ (2 *ℕ c))
    (σₜ : Translation.Env n (2 *ℕ c))
    (η : 𝔽 (2 *ℕ c) → 𝔽 c′) →
    ((x : 𝔽 n) → σₛ (θ x) SoupTerm.⋯ᵣ η ≡ σₜ x SoupTerm.⋯ᵣ η) →
    renameThreads {c = c} {c′ = c′} η
      (V.cast (processCount-⋯ₚ P θ)
        (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
          (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ)))
    ≡
    renameThreads {c = c} {c′ = c′} η
      (proj₂ (Translation.flatten P cs σₜ))
  flatten-ren-threads (Typed.⟪ e ⟫) θ {c = c} {c′ = c′} [] σₛ σₜ η env =
    cong (_∷ [])
      (cong (SoupTerm._⋯ᵣ η) (T[_]-⋯ᵣ e θ σₛ)
       ■ sym (T[_]-renEnv e (σₛ ∘ θ) η)
       ■ T[_]-Env-cong e env
       ■ T[_]-renEnv e σₜ η)
  flatten-ren-threads (P Typed.∥ Q) θ {c = c} {c′ = c′} cs σₛ σₜ η env
    =
    cong (renameThreads {c = c} {c′ = c′} η)
      (cong (V.cast (cong₂ _+_
          (processCount-⋯ₚ P θ) (processCount-⋯ₚ Q θ)))
        (cong₂ V._++_
          (cong (λ xs →
              proj₂ (Translation.flatten (P Typed.⋯ₚ θ) xs σₛ))
            (take-cast-++ (sym (channelCount-⋯ₚ P θ))
              (sym (channelCount-⋯ₚ Q θ)) cs))
          (cong (λ xs →
              proj₂ (Translation.flatten (Q Typed.⋯ₚ θ) xs σₛ))
            (drop-cast-++ (sym (channelCount-⋯ₚ P θ))
              (sym (channelCount-⋯ₚ Q θ)) cs)))
       ■ cast-++ (processCount-⋯ₚ P θ) (processCount-⋯ₚ Q θ)
          (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ P θ))
              (V.take (Translation.channelCount P) cs)) σₛ))
          (proj₂ (Translation.flatten (Q Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ Q θ))
              (V.drop (Translation.channelCount P) cs)) σₛ)))
    ■ VecP.map-++ (λ t → t SoupTerm.⋯ᵣ η)
        (V.cast (processCount-⋯ₚ P θ)
          (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ P θ))
              (V.take (Translation.channelCount P) cs)) σₛ)))
        (V.cast (processCount-⋯ₚ Q θ)
          (proj₂ (Translation.flatten (Q Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ Q θ))
              (V.drop (Translation.channelCount P) cs)) σₛ)))
    ■ cong₂ V._++_
      (flatten-ren-threads P θ (V.take (Translation.channelCount P) cs)
        σₛ σₜ η env)
      (flatten-ren-threads Q θ (V.drop (Translation.channelCount P) cs)
        σₛ σₜ η env)
    ■ sym (VecP.map-++ (λ t → t SoupTerm.⋯ᵣ η)
        (proj₂ (Translation.flatten P
          (V.take (Translation.channelCount P) cs) σₜ))
        (proj₂ (Translation.flatten Q
          (V.drop (Translation.channelCount P) cs) σₜ)))
  flatten-ren-threads {n = n} {n′ = n′}
    (Typed.ν B₁ B₂ P) θ {c = c} {c′ = c′} (i ∷ cs) σₛ σₜ η env =
    cong (renameThreads {c = c} {c′ = c′} η)
      (cong (V.cast (processCount-⋯ₚ P
          (Source._↑*_ θ (sum B₁ + sum B₂))))
          (cong (λ xs →
            proj₂ (Translation.flatten
              (P Typed.⋯ₚ Source._↑*_ θ (sum B₁ + sum B₂))
              xs (σᴮ Translation.++ₛ σₛ)))
          (tail-cast-ν-channels B₁ B₂ P θ {c = c} i cs)))
    ■ flatten-ren-threads P (Source._↑*_ θ (sum B₁ + sum B₂))
        {c = c} {c′ = c′} cs
        (σᴮ Translation.++ₛ σₛ)
        (σᴮ Translation.++ₛ σₜ)
        η
        env′
    where
    b = sum B₁ + sum B₂

    σᴮ : Translation.Env b (2 *ℕ c)
    σᴮ =
      proj₁ (Translation.UB[ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*))

    env′ :
      (x : 𝔽 (b + n)) →
      ((σᴮ Translation.++ₛ σₛ)
        (Source._↑*_ θ b x)) SoupTerm.⋯ᵣ η
      ≡
      ((σᴮ Translation.++ₛ σₜ) x) SoupTerm.⋯ᵣ η
    env′ x with Fin.splitAt b x in split
    ... | inj₁ y =
      cong (λ s →
          [ σᴮ , σₛ ]′ s SoupTerm.⋯ᵣ η)
        (cong (λ z → Fin.splitAt b (Source._↑*_ θ b z))
          (sym (cong (Fin.join b n) (sym split)
                ■ Fin.join-splitAt b n x))
         ■ cong (Fin.splitAt b) (lift*-↑ˡ θ b y)
         ■ Fin.splitAt-↑ˡ b y n′)
    ... | inj₂ y =
      cong (λ s →
          [ σᴮ , σₛ ]′ s SoupTerm.⋯ᵣ η)
        (cong (λ z → Fin.splitAt b (Source._↑*_ θ b z))
          (sym (cong (Fin.join b n) (sym split)
                ■ Fin.join-splitAt b n x))
         ■ cong (Fin.splitAt b) (lift*-↑ʳ θ b y)
         ■ Fin.splitAt-↑ʳ b n′ (θ y))
      ■ env y

  flatten-ren-thread :
    (P : Typed.Proc n) (θ : 𝔽 n → 𝔽 n′)
    {c c′ : ℕ}
    (cs : Vec (𝔽 c) (Translation.channelCount P))
    (σₛ : Translation.Env n′ (2 *ℕ c))
    (σₜ : Translation.Env n (2 *ℕ c))
    (η : 𝔽 (2 *ℕ c) → 𝔽 c′) →
    ((x : 𝔽 n) → σₛ (θ x) SoupTerm.⋯ᵣ η ≡ σₜ x SoupTerm.⋯ᵣ η) →
    (l : 𝔽 (Translation.processCount P)) →
    lookup
      (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
        (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ))
      (Fin.cast (sym (processCount-⋯ₚ P θ)) l)
      SoupTerm.⋯ᵣ η
    ≡
    lookup (proj₂ (Translation.flatten P cs σₜ)) l SoupTerm.⋯ᵣ η
  flatten-ren-thread P θ {c = c} {c′ = c′} cs σₛ σₜ η env l =
    sym (VecP.lookup-map
      (Fin.cast (sym (processCount-⋯ₚ P θ)) l)
      (λ t → t SoupTerm.⋯ᵣ η)
      (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
        (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ)))
    ■ sym (VecP.lookup-cast (processCount-⋯ₚ P θ)
        (renameThreads {c = c} {c′ = c′} η
          (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ)))
        (Fin.cast (sym (processCount-⋯ₚ P θ)) l))
    ■ cong
        (lookup
          (V.cast (processCount-⋯ₚ P θ)
            (renameThreads {c = c} {c′ = c′} η
              (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
                (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ)))))
        (Fin.cast-involutive
          (processCount-⋯ₚ P θ) (sym (processCount-⋯ₚ P θ)) l)
    ■ cong (λ xs → lookup xs l)
        (sym (map-cast (processCount-⋯ₚ P θ)
          (λ t → t SoupTerm.⋯ᵣ η)
          (proj₂ (Translation.flatten (P Typed.⋯ₚ θ)
            (V.cast (sym (channelCount-⋯ₚ P θ)) cs) σₛ))))
    ■ cong (λ xs → lookup xs l)
        (flatten-ren-threads P θ cs σₛ σₜ η env)
    ■ VecP.lookup-map l (λ t → t SoupTerm.⋯ᵣ η)
        (proj₂ (Translation.flatten P cs σₜ))

  flatten-endpoint-thread :
    (P : Typed.Proc n)
    {cₛ cₜ o : ℕ}
    (csₛ : Vec (𝔽 cₛ) (Translation.channelCount P))
    (csₜ : Vec (𝔽 cₜ) (Translation.channelCount P))
    (σₛ : Translation.Env n (2 *ℕ cₛ))
    (σₜ : Translation.Env n (2 *ℕ cₜ))
    (ρₛ : 𝔽 (2 *ℕ cₛ) → 𝔽 o)
    (ρₜ : 𝔽 (2 *ℕ cₜ) → 𝔽 o) →
    ((x : 𝔽 n) → σₛ x SoupTerm.⋯ᵣ ρₛ ≡ σₜ x SoupTerm.⋯ᵣ ρₜ) →
    ((i : 𝔽 (Translation.channelCount P)) (side : 𝔽 2) →
      ρₛ (Soup.endpoint (lookup csₛ i) side) ≡
      ρₜ (Soup.endpoint (lookup csₜ i) side)) →
    (l : 𝔽 (Translation.processCount P)) →
    lookup (proj₂ (Translation.flatten P csₛ σₛ)) l SoupTerm.⋯ᵣ ρₛ
    ≡
    lookup (proj₂ (Translation.flatten P csₜ σₜ)) l SoupTerm.⋯ᵣ ρₜ
  flatten-endpoint-thread (Typed.⟪ e ⟫) [] [] σₛ σₜ ρₛ ρₜ env chan zero =
    sym (T[_]-renEnv e σₛ ρₛ)
    ■ T[_]-Env-cong e env
    ■ T[_]-renEnv e σₜ ρₜ
  flatten-endpoint-thread (P Typed.∥ Q) csₛ csₜ σₛ σₜ ρₛ ρₜ env chan l
    with Translation.flatten P (V.take (Translation.channelCount P) csₛ) σₛ in flatPₛ
       | Translation.flatten Q (V.drop (Translation.channelCount P) csₛ) σₛ in flatQₛ
       | Translation.flatten P (V.take (Translation.channelCount P) csₜ) σₜ in flatPₜ
       | Translation.flatten Q (V.drop (Translation.channelCount P) csₜ) σₜ in flatQₜ
       | Fin.splitAt (Translation.processCount P) l in split
  ... | channelsPₛ , threadsPₛ | channelsQₛ , threadsQₛ
      | channelsPₜ , threadsPₜ | channelsQₜ , threadsQₜ | inj₁ lP =
    subst
      (λ k →
        lookup (threadsPₛ V.++ threadsQₛ) k SoupTerm.⋯ᵣ ρₛ ≡
        lookup (threadsPₜ V.++ threadsQₜ) k SoupTerm.⋯ᵣ ρₜ)
      (sym (cong (Fin.join (Translation.processCount P)
                    (Translation.processCount Q)) split)
       ■ Fin.join-splitAt (Translation.processCount P)
            (Translation.processCount Q) l)
      (cong (SoupTerm._⋯ᵣ ρₛ) (V.lookup-++ˡ threadsPₛ threadsQₛ lP)
       ■ cong (λ result → lookup (proj₂ result) lP SoupTerm.⋯ᵣ ρₛ)
           (sym flatPₛ)
       ■ flatten-endpoint-thread P
           (V.take (Translation.channelCount P) csₛ)
           (V.take (Translation.channelCount P) csₜ)
           σₛ σₜ ρₛ ρₜ env
           (λ i side →
             cong (λ z → ρₛ (Soup.endpoint z side))
               (sym (V.lookup-++ˡ
                  (V.take (Translation.channelCount P) csₛ)
                  (V.drop (Translation.channelCount P) csₛ) i)
                ■ cong (λ xs → lookup xs (i ↑ˡ Translation.channelCount Q))
                  (V.take++drop≡id (Translation.channelCount P) csₛ))
             ■ chan (i ↑ˡ Translation.channelCount Q) side
             ■ cong (λ z → ρₜ (Soup.endpoint z side))
               (sym
                 (sym (V.lookup-++ˡ
                    (V.take (Translation.channelCount P) csₜ)
                    (V.drop (Translation.channelCount P) csₜ) i)
                  ■ cong (λ xs → lookup xs (i ↑ˡ Translation.channelCount Q))
                    (V.take++drop≡id (Translation.channelCount P) csₜ))))
           lP
       ■ cong (λ result → lookup (proj₂ result) lP SoupTerm.⋯ᵣ ρₜ)
           flatPₜ
       ■ cong (SoupTerm._⋯ᵣ ρₜ)
           (sym (V.lookup-++ˡ threadsPₜ threadsQₜ lP)))
  ... | channelsPₛ , threadsPₛ | channelsQₛ , threadsQₛ
      | channelsPₜ , threadsPₜ | channelsQₜ , threadsQₜ | inj₂ lQ =
    subst
      (λ k →
        lookup (threadsPₛ V.++ threadsQₛ) k SoupTerm.⋯ᵣ ρₛ ≡
        lookup (threadsPₜ V.++ threadsQₜ) k SoupTerm.⋯ᵣ ρₜ)
      (sym (cong (Fin.join (Translation.processCount P)
                    (Translation.processCount Q)) split)
       ■ Fin.join-splitAt (Translation.processCount P)
            (Translation.processCount Q) l)
      (cong (SoupTerm._⋯ᵣ ρₛ) (V.lookup-++ʳ threadsPₛ threadsQₛ lQ)
       ■ cong (λ result → lookup (proj₂ result) lQ SoupTerm.⋯ᵣ ρₛ)
           (sym flatQₛ)
       ■ flatten-endpoint-thread Q
           (V.drop (Translation.channelCount P) csₛ)
           (V.drop (Translation.channelCount P) csₜ)
           σₛ σₜ ρₛ ρₜ env
           (λ i side →
             cong (λ z → ρₛ (Soup.endpoint z side))
               (sym (V.lookup-++ʳ
                  (V.take (Translation.channelCount P) csₛ)
                  (V.drop (Translation.channelCount P) csₛ) i)
                ■ cong (λ xs → lookup xs (Translation.channelCount P ↑ʳ i))
                  (V.take++drop≡id (Translation.channelCount P) csₛ))
             ■ chan (Translation.channelCount P ↑ʳ i) side
             ■ cong (λ z → ρₜ (Soup.endpoint z side))
               (sym
                 (sym (V.lookup-++ʳ
                    (V.take (Translation.channelCount P) csₜ)
                    (V.drop (Translation.channelCount P) csₜ) i)
                  ■ cong (λ xs → lookup xs (Translation.channelCount P ↑ʳ i))
                    (V.take++drop≡id (Translation.channelCount P) csₜ))))
           lQ
       ■ cong (λ result → lookup (proj₂ result) lQ SoupTerm.⋯ᵣ ρₜ)
           flatQₜ
       ■ cong (SoupTerm._⋯ᵣ ρₜ)
           (sym (V.lookup-++ʳ threadsPₜ threadsQₜ lQ)))
  flatten-endpoint-thread (Typed.ν B₁ B₂ P) (iₛ ∷ csₛ) (iₜ ∷ csₜ)
    σₛ σₜ ρₛ ρₜ env chan l
    with Translation.UB[ B₁ ] (Soup.leftEnd iₛ)
           (SoupTerm.* , Soup.leftEnd iₛ , SoupTerm.*) in ub₁ₛ
       | Translation.UB[ B₂ ] (Soup.rightEnd iₛ)
           (SoupTerm.* , Soup.rightEnd iₛ , SoupTerm.*) in ub₂ₛ
       | Translation.UB[ B₁ ] (Soup.leftEnd iₜ)
           (SoupTerm.* , Soup.leftEnd iₜ , SoupTerm.*) in ub₁ₜ
       | Translation.UB[ B₂ ] (Soup.rightEnd iₜ)
           (SoupTerm.* , Soup.rightEnd iₜ , SoupTerm.*) in ub₂ₜ
  ... | σ₁ₛ , fs₁ₛ | σ₂ₛ , fs₂ₛ | σ₁ₜ , fs₁ₜ | σ₂ₜ , fs₂ₜ =
    flatten-endpoint-thread P csₛ csₜ
      ((σ₁ₛ Translation.++ₛ σ₂ₛ) Translation.++ₛ σₛ)
      ((σ₁ₜ Translation.++ₛ σ₂ₜ) Translation.++ₛ σₜ)
      ρₛ ρₜ env′ chan′ l
    where
    b = sum B₁ + sum B₂

    envᴮ :
      (x : 𝔽 b) →
      (σ₁ₛ Translation.++ₛ σ₂ₛ) x SoupTerm.⋯ᵣ ρₛ ≡
      (σ₁ₜ Translation.++ₛ σ₂ₜ) x SoupTerm.⋯ᵣ ρₜ
    envᴮ x with Fin.splitAt (sum B₁) x in split
    ... | inj₁ y =
      cong (λ result → proj₁ result y SoupTerm.⋯ᵣ ρₛ) (sym ub₁ₛ)
      ■ UB-coherent B₁
        {rₛ = Soup.leftEnd iₛ} {xₛ = Soup.leftEnd iₛ}
        {e₁ₛ = SoupTerm.*} {e₂ₛ = SoupTerm.*}
        {rₜ = Soup.leftEnd iₜ} {xₜ = Soup.leftEnd iₜ}
        {e₁ₜ = SoupTerm.*} {e₂ₜ = SoupTerm.*}
        ρₛ ρₜ
          (chan zero zero) refl (chan zero zero) refl y
      ■ cong (λ result → proj₁ result y SoupTerm.⋯ᵣ ρₜ) ub₁ₜ
    ... | inj₂ y =
      cong (λ result → proj₁ result y SoupTerm.⋯ᵣ ρₛ) (sym ub₂ₛ)
      ■ UB-coherent B₂
        {rₛ = Soup.rightEnd iₛ} {xₛ = Soup.rightEnd iₛ}
        {e₁ₛ = SoupTerm.*} {e₂ₛ = SoupTerm.*}
        {rₜ = Soup.rightEnd iₜ} {xₜ = Soup.rightEnd iₜ}
        {e₁ₜ = SoupTerm.*} {e₂ₜ = SoupTerm.*}
        ρₛ ρₜ
          (chan zero (suc zero)) refl (chan zero (suc zero)) refl y
      ■ cong (λ result → proj₁ result y SoupTerm.⋯ᵣ ρₜ) ub₂ₜ

    env′ :
      (x : 𝔽 (b + _)) →
      ((σ₁ₛ Translation.++ₛ σ₂ₛ) Translation.++ₛ σₛ) x
        SoupTerm.⋯ᵣ ρₛ
      ≡
      ((σ₁ₜ Translation.++ₛ σ₂ₜ) Translation.++ₛ σₜ) x
        SoupTerm.⋯ᵣ ρₜ
    env′ x with Fin.splitAt b x in split
    ... | inj₁ y =
      envᴮ y
    ... | inj₂ y =
      env y

    chan′ :
      (j : 𝔽 (Translation.channelCount P)) (side : 𝔽 2) →
      ρₛ (Soup.endpoint (lookup csₛ j) side) ≡
      ρₜ (Soup.endpoint (lookup csₜ j) side)
    chan′ j side = chan (suc j) side

U-com :
  ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
    {E₁ E₂ : SourceReduction.Frame* (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0)}
    {P : Typed.Proc (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0)}
    {e : Source.Tm (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0)}
    {n m : ℕ} {C : Soup.Config n m} →
  SourceReduction.Value e →
  V.[] ; Context.[]
    ⊢ₚ
    comSource b₁ b₂ B₁ B₂ E₁ E₂ P e →
  SoupImage (comSource b₁ b₂ B₁ B₂ E₁ E₂ P e) C →
  Σ[ C′ ∈ Soup.Config n m ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (comTarget b₁ b₂ B₁ B₂ E₁ E₂ P e) C′
U-com {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
  {E₁ = E₁} {E₂ = E₂} {P = P} {e = e}
  {n = n} {m = m} {C = C} Ve ⊢P image =
  C′ ,
  SoupReduction.RUS-Com
    j j₂ i zero (suc zero) F₁ F₂
    j≢k SoupReduction.left-right
    selected-channel Veᵘ selected₁ selected₂ ,
  record
    { channelEmbedding = channelEmbedding′
    ; channelEmbedding-injective = channelEmbedding-injective′
    ; threadEmbedding = threadEmbedding′
    ; threadEmbedding-injective = threadEmbedding-injective′
    ; endpointEmbedding = endpointEmbedding′
    ; endpoint-respects-channel = endpoint-respects-channel′
    ; live-channel = live-channel′
    ; live-thread = live-thread′
    ; garbage-channel = garbage-channel′
    ; garbage-thread = garbage-thread′
    }
  where
  SourceProc TargetProc : Typed.Proc 0
  SourceProc = comSource b₁ b₂ B₁ B₂ E₁ E₂ P e
  TargetProc = comTarget b₁ b₂ B₁ B₂ E₁ E₂ P e

  j j₂ : 𝔽 m
  j = threadEmbedding image 0F
  j₂ = threadEmbedding image 1F

  i : 𝔽 n
  i = channelEmbedding image 0F

  ρ : 𝔽 (2 *ℕ Translation.channelCount SourceProc) → 𝔽 (2 *ℕ n)
  ρ = endpointEmbedding image

  σₛ₀ : Translation.Env (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0)
          (2 *ℕ Translation.channelCount SourceProc)
  σₛ₀ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F

  σₛ : Translation.Env (sum (Bˢ b₁ B₁) + sum (Bˢ b₂ B₂) + 0) (2 *ℕ n)
  σₛ = source-renamedEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F ρ

  Vσₛ : ValueEnv σₛ
  Vσₛ = source-renamedValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F ρ

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = Tᶠ*[ SourceReduction._⋯ᶠ*_ E₁ (wkρ b₁ b₂ B₁ B₂) ] {σ = σₛ} Vσₛ
  F₂ = Tᶠ*[ SourceReduction._⋯ᶠ*_ E₂ (wkρ b₁ b₂ B₁ B₂) ] {σ = σₛ} Vσₛ

  eᵘ : SoupTerm.Tm (2 *ℕ n)
  eᵘ = Translation.T[ Source._⋯_ e (wkρ b₁ b₂ B₁ B₂) ] σₛ

  Veᵘ : SoupExpression.Value eᵘ
  Veᵘ = T[_]-Value (SourceReduction._⋯ᵛ_ Ve (wkρ b₁ b₂ B₁ B₂)) Vσₛ

  tail₁⁰ tail₂⁰ : SoupTerm.Tm (2 *ℕ Translation.channelCount SourceProc)
  tail₁⁰ = proj₁ (env₁-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F)
  tail₂⁰ = proj₁ (env₂-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F)

  tail₁ tail₂ : SoupTerm.Tm (2 *ℕ n)
  tail₁ = tail₁⁰ SoupTerm.⋯ᵣ ρ
  tail₂ = tail₂⁰ SoupTerm.⋯ᵣ ρ

  triple₁ triple₂ : SoupTerm.Tm (2 *ℕ n)
  triple₁ = chanTriple SoupTerm.* (Soup.endpoint i zero) tail₁
  triple₂ = chanTriple SoupTerm.* (Soup.endpoint i (suc zero)) tail₂

  parent child : Soup.Thread n
  parent = plug*ᵘ F₁ SoupTerm.*
  child = plug*ᵘ F₂ eᵘ

  threads′ : Vec (Soup.Thread n) m
  threads′ = SoupReduction.replaceTwo (Soup.threads C) j parent j₂ child

  C′ : Soup.Config n m
  C′ = Soup.config (Soup.channels C) threads′

  channelCountEq :
    Translation.channelCount TargetProc ≡
    Translation.channelCount SourceProc
  channelCountEq =
    cong suc (sym (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂)))

  processCountEq :
    Translation.processCount TargetProc ≡
    Translation.processCount SourceProc
  processCountEq =
    cong (2 +_) (sym (processCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂)))

  endpointCountEq :
    2 *ℕ Translation.channelCount TargetProc ≡
    2 *ℕ Translation.channelCount SourceProc
  endpointCountEq = cong (2 *ℕ_) channelCountEq

  channelEmbedding′ : 𝔽 (Translation.channelCount TargetProc) → 𝔽 n
  channelEmbedding′ x = channelEmbedding image (Fin.cast channelCountEq x)

  threadEmbedding′ : 𝔽 (Translation.processCount TargetProc) → 𝔽 m
  threadEmbedding′ x = threadEmbedding image (Fin.cast processCountEq x)

  endpointEmbedding′ :
    𝔽 (2 *ℕ Translation.channelCount TargetProc) →
    𝔽 (2 *ℕ n)
  endpointEmbedding′ x = ρ (Fin.cast endpointCountEq x)

  j≢k : j ≢ j₂
  j≢k eq with threadEmbedding-injective image eq
  ... | ()

  selected-channel :
    proj₁ (lookup (Soup.channels C) i) ≡ true
  selected-channel = image-channel-open image 0F

  x-triple : σₛ (send-var b₁ b₂ B₁ B₂) ≡ triple₁
  x-triple =
    cong (SoupTerm._⋯ᵣ ρ)
      (proj₂ (env₁-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F))
    ■ cong (λ z → chanTriple SoupTerm.* z tail₁)
        (endpoint-respects-channel image 0F zero)

  y-triple :
    σₛ (recv-var b₁ b₂ B₁ B₂) ≡ triple₂
  y-triple =
    cong (SoupTerm._⋯ᵣ ρ)
      (proj₂ (env₂-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F))
    ■ cong (λ z → chanTriple SoupTerm.* z tail₂)
        (endpoint-respects-channel image 0F (suc zero))

  selected₁ : lookup (Soup.threads C) j ≡
    plug*ᵘ F₁ (SoupTerm.K Source.`send SoupTerm.·¹ (eᵘ SoupTerm.⊗ triple₁))
  selected₁ =
    live-thread image 0F
    ■ sym (T[_]-renEnv
        (plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (wkρ b₁ b₂ B₁ B₂))
          (Source.K Source.`send Source.·¹
            ((Source._⋯_ e (wkρ b₁ b₂ B₁ B₂)) Source.⊗
             (Source.` (send-var b₁ b₂ B₁ B₂)))))
        σₛ₀ ρ)
    ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₁ (wkρ b₁ b₂ B₁ B₂)) Vσₛ
    ■ cong (λ z →
        plug*ᵘ F₁ (SoupTerm.K Source.`send SoupTerm.·¹ (eᵘ SoupTerm.⊗ z)))
        x-triple

  selected₂ : lookup (Soup.threads C) j₂ ≡
    plug*ᵘ F₂ (SoupTerm.K Source.`recv SoupTerm.·¹ triple₂)
  selected₂ =
    live-thread image 1F
    ■ sym (T[_]-renEnv
        (plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (wkρ b₁ b₂ B₁ B₂))
          (Source.K Source.`recv Source.·¹
            (Source.` (recv-var b₁ b₂ B₁ B₂))))
        σₛ₀ ρ)
    ■ T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₂ (wkρ b₁ b₂ B₁ B₂)) Vσₛ
    ■ cong (λ z →
        plug*ᵘ F₂ (SoupTerm.K Source.`recv SoupTerm.·¹ z))
        y-triple

  channelEmbedding-injective′ : FinInjective channelEmbedding′
  channelEmbedding-injective′ eq =
    𝔽-cast-injective channelCountEq
      (channelEmbedding-injective image eq)

  threadEmbedding-injective′ : FinInjective threadEmbedding′
  threadEmbedding-injective′ eq =
    𝔽-cast-injective processCountEq
      (threadEmbedding-injective image eq)

  endpoint-respects-channel′ :
    (i : 𝔽 (Translation.channelCount TargetProc)) (side : 𝔽 2) →
    endpointEmbedding′ (Soup.endpoint i side) ≡
    Soup.endpoint (channelEmbedding′ i) side
  endpoint-respects-channel′ i side =
    cong ρ (endpoint-cast channelCountEq i side)
    ■ endpoint-respects-channel image (Fin.cast channelCountEq i) side

  live-channel′ :
    (l : 𝔽 (Translation.channelCount TargetProc)) →
    lookup (Soup.channels C′) (channelEmbedding′ l) ≡
    lookup (canonicalChannels TargetProc) l
  live-channel′ 0F =
    live-channel image 0F
    ■ cong₂ (λ fs₁ fs₂ → true , fs₁ , fs₂)
        (UB-flags-drop b₁ B₁
          (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
          (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
          SoupTerm.* SoupTerm.*
         ■ UB-flags-cong (Bᵗ b₁ B₁)
          (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
          (SoupTerm.* ,
           Soup.leftEnd {n = Translation.channelCount SourceProc} 0F ,
           SoupTerm.*)
          (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
          (SoupTerm.* ,
           Soup.leftEnd {n = Translation.channelCount TargetProc} 0F ,
           SoupTerm.*))
        (UB-flags-drop b₂ B₂
          (Soup.rightEnd {n = Translation.channelCount SourceProc} 0F)
          (Soup.rightEnd {n = Translation.channelCount SourceProc} 0F)
          SoupTerm.* SoupTerm.*
         ■ UB-flags-cong (Bᵗ b₂ B₂)
          (Soup.rightEnd {n = Translation.channelCount SourceProc} 0F)
          (SoupTerm.* ,
           Soup.rightEnd {n = Translation.channelCount SourceProc} 0F ,
           SoupTerm.*)
          (Soup.rightEnd {n = Translation.channelCount TargetProc} 0F)
          (SoupTerm.* ,
           Soup.rightEnd {n = Translation.channelCount TargetProc} 0F ,
           SoupTerm.*))
  live-channel′ (suc l) =
    live-channel image
      (suc (Fin.cast
        (sym (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))) l))
    ■ cong
        (λ channels → lookup channels
          (suc (Fin.cast
            (sym (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))) l)))
        (flatten-channels-shape SourceProc
          (V.allFin (Translation.channelCount SourceProc)) (λ ()))
    ■ sym (VecP.lookup-cast₁
        (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
        (channelShape (P Typed.⋯ₚ (wkρ b₁ b₂ B₁ B₂))) l)
    ■ cong (λ channels → lookup channels l)
        (sym (VecP.subst-is-cast
          (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
          (channelShape (P Typed.⋯ₚ (wkρ b₁ b₂ B₁ B₂)))))
    ■ cong (λ channels → lookup channels l)
        (channelShape-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
    ■ cong (λ channels → lookup channels (suc l))
        (sym (flatten-channels-shape TargetProc
          (V.allFin (Translation.channelCount TargetProc)) (λ ())))

  garbage-channel′ :
    (l : 𝔽 n) →
    ChannelOutside {P = TargetProc} channelEmbedding′ l →
    lookup (Soup.channels C′) l ≡ (false , [] , [])
  garbage-channel′ l outside =
    garbage-channel image l sourceOutside
    where
    sourceOutside : ChannelOutside {P = SourceProc} (channelEmbedding image) l
    sourceOutside k eq =
      outside (Fin.cast (sym channelCountEq) k)
        (cong (channelEmbedding image)
          (Fin.cast-involutive channelCountEq (sym channelCountEq) k)
        ■ eq)

  cast-zero : ∀ {a b : ℕ} (eq : suc a ≡ suc b) →
    Fin.cast eq 0F ≡ 0F
  cast-zero refl = refl

  channelEmbedding′-zero :
    channelEmbedding′ 0F ≡ i
  channelEmbedding′-zero =
    cong (channelEmbedding image) (cast-zero channelCountEq)

  endpointEmbedding′-zero :
    (side : 𝔽 2) →
    endpointEmbedding′ (Soup.endpoint 0F side) ≡
    Soup.endpoint i side
  endpointEmbedding′-zero side =
    endpoint-respects-channel′ 0F side
    ■ cong (λ z → Soup.endpoint z side) channelEmbedding′-zero

  source-UB-concrete :
    (B : Typed.BindGroup) (side : 𝔽 2) (x : 𝔽 (sum B)) →
    proj₁
      (Translation.UB[ B ] (Soup.endpoint 0F side)
        (SoupTerm.* , Soup.endpoint 0F side , SoupTerm.*)) x
      SoupTerm.⋯ᵣ ρ
    ≡
    proj₁
      (Translation.UB[ B ] (Soup.endpoint i side)
        (SoupTerm.* , Soup.endpoint i side , SoupTerm.*)) x
  source-UB-concrete B side x =
    UB-ren B ρ
      (Soup.endpoint 0F side)
      SoupTerm.*
      (Soup.endpoint 0F side)
      SoupTerm.*
      x
    ■ cong
        (λ z →
          proj₁
            (Translation.UB[ B ] z
              (SoupTerm.* , z , SoupTerm.*)) x)
        (endpoint-respects-channel image 0F side)

  target-UB-concrete :
    (B : Typed.BindGroup) (side : 𝔽 2) (x : 𝔽 (sum B)) →
    proj₁
      (Translation.UB[ B ] (Soup.endpoint 0F side)
        (SoupTerm.* , Soup.endpoint 0F side , SoupTerm.*)) x
      SoupTerm.⋯ᵣ endpointEmbedding′
    ≡
    proj₁
      (Translation.UB[ B ] (Soup.endpoint i side)
        (SoupTerm.* , Soup.endpoint i side , SoupTerm.*)) x
  target-UB-concrete B side x =
    UB-ren B endpointEmbedding′
      (Soup.endpoint 0F side)
      SoupTerm.*
      (Soup.endpoint 0F side)
      SoupTerm.*
      x
    ■ cong
        (λ z →
          proj₁
            (Translation.UB[ B ] z
              (SoupTerm.* , z , SoupTerm.*)) x)
        (endpointEmbedding′-zero side)

  targetEnv-renamed :
    (x : 𝔽 (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂) + 0)) →
    targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
      {c = Translation.channelCount TargetProc} 0F x
      SoupTerm.⋯ᵣ endpointEmbedding′
    ≡
    targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
      {c = Translation.channelCount SourceProc} 0F x
      SoupTerm.⋯ᵣ ρ
  targetEnv-renamed x
    with Fin.splitAt (sum (Bᵗ b₁ B₁) + sum (Bᵗ b₂ B₂)) x in outer
  ... | inj₂ ()
  ... | inj₁ z with Fin.splitAt (sum (Bᵗ b₁ B₁)) z in inner
  ...   | inj₁ v =
    target-UB-concrete (Bᵗ b₁ B₁) zero v
    ■ sym (source-UB-concrete (Bᵗ b₁ B₁) zero v)
  ...   | inj₂ w =
    target-UB-concrete (Bᵗ b₂ B₂) (suc zero) w
    ■ sym (source-UB-concrete (Bᵗ b₂ B₂) (suc zero) w)

  parent-live :
    parent ≡
    lookup (canonicalThreads TargetProc) 0F SoupTerm.⋯ᵣ endpointEmbedding′
  parent-live =
    sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₁ (wkρ b₁ b₂ B₁ B₂)) Vσₛ)
    ■ cong (λ z → Translation.T[ z ] σₛ)
        (sym (plug*ˢ-ren E₁ (wkρ b₁ b₂ B₁ B₂)))
    ■ T[_]-⋯ᵣ (plug*ˢ E₁ Source.*) (wkρ b₁ b₂ B₁ B₂) σₛ
    ■ T[_]-Env-cong (plug*ˢ E₁ Source.*)
        (λ x → cong (SoupTerm._⋯ᵣ ρ)
          (source-targetEnv {b₁ = b₁} {b₂ = b₂}
            {B₁ = B₁} {B₂ = B₂} 0F x))
    ■ sym (T[_]-Env-cong (plug*ˢ E₁ Source.*) targetEnv-renamed)
    ■ T[_]-renEnv (plug*ˢ E₁ Source.*)
        (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
          {c = Translation.channelCount TargetProc} 0F)
        endpointEmbedding′

  child-live :
    child ≡
    lookup (canonicalThreads TargetProc) 1F SoupTerm.⋯ᵣ endpointEmbedding′
  child-live =
    sym (T[_]-plugᶠ* (SourceReduction._⋯ᶠ*_ E₂ (wkρ b₁ b₂ B₁ B₂)) Vσₛ)
    ■ cong (λ z → Translation.T[ z ] σₛ)
        (sym (plug*ˢ-ren E₂ (wkρ b₁ b₂ B₁ B₂)))
    ■ T[_]-⋯ᵣ (plug*ˢ E₂ e) (wkρ b₁ b₂ B₁ B₂) σₛ
    ■ T[_]-Env-cong (plug*ˢ E₂ e)
        (λ x → cong (SoupTerm._⋯ᵣ ρ)
          (source-targetEnv {b₁ = b₁} {b₂ = b₂}
            {B₁ = B₁} {B₂ = B₂} 0F x))
    ■ sym (T[_]-Env-cong (plug*ˢ E₂ e) targetEnv-renamed)
    ■ T[_]-renEnv (plug*ˢ E₂ e)
        (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
          {c = Translation.channelCount TargetProc} 0F)
        endpointEmbedding′

  tail-live :
    (l : 𝔽 (Translation.processCount P)) →
    lookup (canonicalThreads SourceProc)
        (Fin.cast processCountEq (suc (suc l)))
      SoupTerm.⋯ᵣ ρ
    ≡
    lookup (canonicalThreads TargetProc) (suc (suc l))
      SoupTerm.⋯ᵣ endpointEmbedding′
  tail-live l =
    cong
      (λ channels →
        lookup
          (proj₂ (Translation.flatten
            (P Typed.⋯ₚ wkρ b₁ b₂ B₁ B₂)
            channels σₛ₀))
          (Fin.cast (sym (processCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))) l)
          SoupTerm.⋯ᵣ ρ)
      (cast-cancelʳ
        (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
        (V.tabulate (λ x → id (suc x))))
    ■ flatten-ren-thread P (wkρ b₁ b₂ B₁ B₂)
      (V.cast (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
        (V.tabulate (λ x → id (suc x))))
      σₛ₀
      (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
        {c = Translation.channelCount SourceProc} 0F)
      ρ
      (λ x → cong (SoupTerm._⋯ᵣ ρ)
        (source-targetEnv {b₁ = b₁} {b₂ = b₂}
          {B₁ = B₁} {B₂ = B₂} 0F x))
      l
    ■ flatten-endpoint-thread P
      (V.cast (channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂))
        (V.tabulate (λ x → id (suc x))))
      (V.drop 0 (V.tabulate (λ x → id (suc x))))
      (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
        {c = Translation.channelCount SourceProc} 0F)
      (targetEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
        {c = Translation.channelCount TargetProc} 0F)
      ρ endpointEmbedding′
      (λ x → sym (targetEnv-renamed x))
      tail-channel
      l
    where
    cc = channelCount-⋯ₚ P (wkρ b₁ b₂ B₁ B₂)

    tail-channel :
      (j : 𝔽 (Translation.channelCount P)) (side : 𝔽 2) →
      ρ
        (Soup.endpoint
          (lookup
            (V.cast cc (V.tabulate (λ x → id (suc x))))
            j)
          side)
      ≡
      endpointEmbedding′
        (Soup.endpoint
          (lookup
            (V.drop 0 (V.tabulate (λ x → id (suc x))))
            j)
          side)
    tail-channel j side =
      cong (λ z → ρ (Soup.endpoint z side))
        (VecP.lookup-cast₁ cc
          (V.tabulate (λ x → id (suc x))) j
        ■ VecP.lookup∘tabulate
          (λ x → id (suc x)) (Fin.cast (sym cc) j))
      ■ sym
        (cong ρ
          (endpoint-cast channelCountEq (suc j) side
          ■ cong (λ z → Soup.endpoint z side)
              (cast-suc-channel cc j)))
      ■ cong endpointEmbedding′
        (cong (λ z → Soup.endpoint z side)
          (sym (VecP.lookup∘tabulate (λ x → id (suc x)) j)))

  live-thread′ :
    (l : 𝔽 (Translation.processCount TargetProc)) →
    lookup (Soup.threads C′) (threadEmbedding′ l) ≡
    lookup (canonicalThreads TargetProc) l SoupTerm.⋯ᵣ endpointEmbedding′
  live-thread′ zero =
    VecP.lookup∘updateAt′ j j₂ j≢k
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ VecP.lookup∘updateAt j (Soup.threads C)
    ■ parent-live
  live-thread′ (suc zero) =
    VecP.lookup∘updateAt j₂
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ child-live
  live-thread′ (suc (suc l)) =
    VecP.lookup∘updateAt′ (threadEmbedding′ (suc (suc l))) j₂
      (λ eq → cast-suc-suc≢one processCountEq l
        (threadEmbedding-injective image eq))
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ VecP.lookup∘updateAt′ (threadEmbedding′ (suc (suc l))) j
      (λ eq → cast-suc-suc≢zero processCountEq l
        (threadEmbedding-injective image eq))
      (Soup.threads C)
    ■ live-thread image (Fin.cast processCountEq (suc (suc l)))
    ■ tail-live l

  garbage-thread′ :
    (l : 𝔽 m) →
    ThreadOutside {P = TargetProc} threadEmbedding′ l →
    lookup (Soup.threads C′) l ≡ SoupTerm.K Source.`unit
  garbage-thread′ l outside =
    VecP.lookup∘updateAt′ l j₂ (λ l≡k → outside 1F (sym l≡k))
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ VecP.lookup∘updateAt′ l j (λ l≡j → outside 0F (sym l≡j))
      (Soup.threads C)
    ■ garbage-thread image l sourceOutside
    where
    sourceOutside : ThreadOutside {P = SourceProc} (threadEmbedding image) l
    sourceOutside k eq =
      outside (Fin.cast (sym processCountEq) k)
        (cong (threadEmbedding image)
          (Fin.cast-involutive processCountEq (sym processCountEq) k)
        ■ eq)
