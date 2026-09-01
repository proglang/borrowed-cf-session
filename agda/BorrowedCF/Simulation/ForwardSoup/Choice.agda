module BorrowedCF.Simulation.ForwardSoup.Choice where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ; UB-head; UB-Value; image-channel-open)

open Nat.Variables
open Fin.Patterns

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

  B′ : ℕ → Typed.BindGroup → Typed.BindGroup
  B′ b B = suc b ∷ B

  choice-var₁ :
    ∀ b₁ b₂ B₁ B₂ →
    𝔽 (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)
  choice-var₁ b₁ b₂ B₁ B₂ = 0F

  choice-var₂ :
    ∀ b₁ b₂ B₁ B₂ →
    𝔽 (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)
  choice-var₂ b₁ b₂ B₁ B₂ =
    Source.wkʳ 0 (Source.wkˡ (suc b₁ + sum B₁) 0F)

  choiceSource :
    ∀ b₁ b₂ B₁ B₂ →
    SourceReduction.Frame* (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    SourceReduction.Frame* (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    Typed.Proc (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    Source.Side →
    Typed.Proc 0
  choiceSource b₁ b₂ B₁ B₂ E₁ E₂ P side =
    Typed.ν (B′ b₁ B₁) (B′ b₂ B₂)
      ((Typed.⟪ plug*ˢ E₁
          (Source.K (Source.`select side) Source.·¹
           (Source.` (choice-var₁ b₁ b₂ B₁ B₂))) ⟫
        Typed.∥
        Typed.⟪ plug*ˢ E₂
          (Source.K Source.`branch Source.·¹
           (Source.` (choice-var₂ b₁ b₂ B₁ B₂))) ⟫)
       Typed.∥ P)

  choiceTarget :
    ∀ b₁ b₂ B₁ B₂ →
    SourceReduction.Frame* (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    SourceReduction.Frame* (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    Typed.Proc (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) →
    Source.Side →
    Typed.Proc 0
  choiceTarget b₁ b₂ B₁ B₂ E₁ E₂ P side =
    Typed.ν (B′ b₁ B₁) (B′ b₂ B₂)
      ((Typed.⟪ plug*ˢ E₁
          (Source.` (choice-var₁ b₁ b₂ B₁ B₂)) ⟫
        Typed.∥
        Typed.⟪ plug*ˢ E₂
          (Source.`inj side (Source.` (choice-var₂ b₁ b₂ B₁ B₂))) ⟫)
       Typed.∥ P)

  sourceEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} →
    𝔽 c →
    Translation.Env (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) (2 *ℕ c)
  sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    (proj₁
      (Translation.UB[ B′ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
    Translation.++ₛ
    proj₁
      (Translation.UB[ B′ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
    Translation.++ₛ (λ ())

  sourceValueEnv :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    ValueEnv (sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i)
  sourceValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value (B′ b₁ B₁) (Soup.leftEnd i)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value (B′ b₂ B₂) (Soup.rightEnd i)
          SoupExpression.V-K SoupExpression.V-K))
      (λ ())

  env₁-lookup :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    let σ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i in
    Σ[ tail ∈ SoupTerm.Tm (2 *ℕ c) ]
      σ (choice-var₁ b₁ b₂ B₁ B₂) ≡
      chanTriple SoupTerm.* (Soup.leftEnd i) tail
  env₁-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    let h = UB-head b₁ B₁ (Soup.leftEnd i) (Soup.leftEnd i) SoupTerm.* SoupTerm.* in
    proj₁ h ,
    (++ₛ-lookupˡ {b = 0}
      (proj₁ (Translation.UB[ B′ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B′ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      (λ ())
      (0F ↑ˡ sum (B′ b₂ B₂))
    ■ ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B′ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
      (proj₁ (Translation.UB[ B′ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      0F
    ■ proj₂ h)

  env₂-lookup :
    ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup} {c : ℕ} (i : 𝔽 c) →
    let σ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i in
    Σ[ tail ∈ SoupTerm.Tm (2 *ℕ c) ]
      σ (choice-var₂ b₁ b₂ B₁ B₂) ≡
      chanTriple SoupTerm.* (Soup.rightEnd i) tail
  env₂-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} i =
    let h = UB-head b₂ B₂ (Soup.rightEnd i) (Soup.rightEnd i) SoupTerm.* SoupTerm.* in
    proj₁ h ,
    (++ₛ-lookupˡ {b = 0}
      (proj₁ (Translation.UB[ B′ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B′ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      (λ ())
      (Source.wkˡ (suc b₁ + sum B₁) 0F)
    ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B′ b₁ B₁ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
      (proj₁ (Translation.UB[ B′ b₂ B₂ ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
      0F
    ■ proj₂ h)

U-choice :
  ∀ {b₁ b₂ : ℕ} {B₁ B₂ : Typed.BindGroup}
    {E₁ E₂ : SourceReduction.Frame* (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)}
    {P : Typed.Proc (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)}
    {side : Source.Side}
    {n m : ℕ} {C : Soup.Config n m} →
  SoupImage (choiceSource b₁ b₂ B₁ B₂ E₁ E₂ P side) C →
  Σ[ C′ ∈ Soup.Config n m ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (choiceTarget b₁ b₂ B₁ B₂ E₁ E₂ P side) C′
U-choice {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
  {E₁ = E₁} {E₂ = E₂} {P = P} {side = side}
  {n = n} {m = m} {C = C} image =
  C′ ,
  SoupReduction.RUS-Choice
    j j₂ i zero (suc zero) F₁ F₂ side
    j≢k SoupReduction.left-right
    selected-channel selected₁ selected₂ ,
  record
    { channelEmbedding = channelEmbedding image
    ; channelEmbedding-injective = channelEmbedding-injective image
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; endpointEmbedding = ρ
    ; endpoint-respects-channel = endpoint-respects-channel image
    ; live-channel = live-channel image
    ; live-thread = live-thread′
    ; garbage-channel = garbage-channel image
    ; garbage-thread = garbage-thread′
    }
  where
  SourceProc TargetProc : Typed.Proc 0
  SourceProc = choiceSource b₁ b₂ B₁ B₂ E₁ E₂ P side
  TargetProc = choiceTarget b₁ b₂ B₁ B₂ E₁ E₂ P side

  j j₂ : 𝔽 m
  j = threadEmbedding image 0F
  j₂ = threadEmbedding image 1F

  i : 𝔽 n
  i = channelEmbedding image 0F

  ρ : 𝔽 (2 *ℕ Translation.channelCount SourceProc) → 𝔽 (2 *ℕ n)
  ρ = endpointEmbedding image

  σ₀ : Translation.Env (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)
         (2 *ℕ Translation.channelCount SourceProc)
  σ₀ = sourceEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F

  Vσ₀ : ValueEnv σ₀
  Vσ₀ = sourceValueEnv {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F

  σ : Translation.Env (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0) (2 *ℕ n)
  σ x = σ₀ x SoupTerm.⋯ᵣ ρ

  Vσ : ValueEnv σ
  Vσ x = SoupExpression.value-rename (Vσ₀ x) ρ

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = Tᶠ*[ E₁ ] {σ = σ} Vσ
  F₂ = Tᶠ*[ E₂ ] {σ = σ} Vσ

  x y : 𝔽 (sum (B′ b₁ B₁) + sum (B′ b₂ B₂) + 0)
  x = choice-var₁ b₁ b₂ B₁ B₂
  y = choice-var₂ b₁ b₂ B₁ B₂

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
  parent = plug*ᵘ F₁ triple₁
  child = plug*ᵘ F₂ (SoupTerm.`inj side triple₂)

  threads′ : Vec (Soup.Thread n) m
  threads′ = SoupReduction.replaceTwo (Soup.threads C) j parent j₂ child

  C′ : Soup.Config n m
  C′ = Soup.config (Soup.channels C) threads′

  j≢k : j ≢ j₂
  j≢k eq with threadEmbedding-injective image eq
  ... | ()

  selected-channel :
    proj₁ (lookup (Soup.channels C) i) ≡ true
  selected-channel = image-channel-open image 0F

  x-triple :
    σ x ≡ triple₁
  x-triple =
    cong (SoupTerm._⋯ᵣ ρ)
      (proj₂ (env₁-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F))
    ■ cong (λ z → chanTriple SoupTerm.* z tail₁)
        (endpoint-respects-channel image 0F zero)

  y-triple :
    σ y ≡ triple₂
  y-triple =
    cong (SoupTerm._⋯ᵣ ρ)
      (proj₂ (env₂-lookup {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} 0F))
    ■ cong (λ z → chanTriple SoupTerm.* z tail₂)
        (endpoint-respects-channel image 0F (suc zero))

  selected₁ :
    lookup (Soup.threads C) j ≡
    plug*ᵘ F₁ (SoupTerm.K (Source.`select side) SoupTerm.·¹ triple₁)
  selected₁ =
    live-thread image 0F
    ■ sym (T[_]-renEnv (plug*ˢ E₁ (Source.K (Source.`select side) Source.·¹ (Source.` x))) σ₀ ρ)
    ■ T[_]-plugᶠ* E₁ Vσ
    ■ cong (λ z → plug*ᵘ F₁ (SoupTerm.K (Source.`select side) SoupTerm.·¹ z))
        x-triple

  selected₂ :
    lookup (Soup.threads C) j₂ ≡
    plug*ᵘ F₂ (SoupTerm.K Source.`branch SoupTerm.·¹ triple₂)
  selected₂ =
    live-thread image 1F
    ■ sym (T[_]-renEnv (plug*ˢ E₂ (Source.K Source.`branch Source.·¹ (Source.` y))) σ₀ ρ)
    ■ T[_]-plugᶠ* E₂ Vσ
    ■ cong (λ z → plug*ᵘ F₂ (SoupTerm.K Source.`branch SoupTerm.·¹ z))
        y-triple

  parent-live :
    parent ≡
    lookup (canonicalThreads TargetProc) 0F SoupTerm.⋯ᵣ ρ
  parent-live =
    cong (plug*ᵘ F₁) (sym x-triple)
    ■ sym (T[_]-plugᶠ* E₁ Vσ)
    ■ T[_]-renEnv (plug*ˢ E₁ (Source.` x)) σ₀ ρ

  child-live :
    child ≡
    lookup (canonicalThreads TargetProc) 1F SoupTerm.⋯ᵣ ρ
  child-live =
    cong (λ z → plug*ᵘ F₂ (SoupTerm.`inj side z)) (sym y-triple)
    ■ sym (T[_]-plugᶠ* E₂ Vσ)
    ■ T[_]-renEnv (plug*ˢ E₂ (Source.`inj side (Source.` y))) σ₀ ρ

  live-thread′ :
    (l : 𝔽 (Translation.processCount TargetProc)) →
    lookup (Soup.threads C′) (threadEmbedding image l) ≡
    lookup (canonicalThreads TargetProc) l SoupTerm.⋯ᵣ ρ
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
    VecP.lookup∘updateAt′ (threadEmbedding image (suc (suc l))) j₂
      (λ eq → case threadEmbedding-injective image eq of λ ())
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ VecP.lookup∘updateAt′ (threadEmbedding image (suc (suc l))) j
      (λ eq → case threadEmbedding-injective image eq of λ ())
      (Soup.threads C)
    ■ live-thread image (suc (suc l))

  garbage-thread′ :
    (l : 𝔽 m) →
    ThreadOutside {P = TargetProc} (threadEmbedding image) l →
    lookup (Soup.threads C′) l ≡ SoupTerm.K Source.`unit
  garbage-thread′ l outside =
    VecP.lookup∘updateAt′ l j₂ (λ l≡k → outside 1F (sym l≡k))
      (SoupReduction.replaceAt (Soup.threads C) j parent)
    ■ VecP.lookup∘updateAt′ l j (λ l≡j → outside 0F (sym l≡j))
      (Soup.threads C)
    ■ garbage-thread image l outside
