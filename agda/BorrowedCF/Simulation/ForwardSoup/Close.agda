module BorrowedCF.Simulation.ForwardSoup.Close where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP
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
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image

open Nat.Variables
open Fin.Patterns

private
  emptyEnv : Translation.Env 0 n
  emptyEnv ()

  emptyValueEnv : ∀ {n} → ValueEnv (emptyEnv {n = n})
  emptyValueEnv ()

  plug*ˢ : SourceReduction.Frame* n → Source.Tm n → Source.Tm n
  plug*ˢ = SourceReduction._[_]*

  plug*ᵘ : SoupExpression.Frame* n → SoupTerm.Tm n → SoupTerm.Tm n
  plug*ᵘ = SoupExpression._[_]*

  channelSoup : SoupTerm.Tm n → 𝔽 n → SoupTerm.Tm n → SoupTerm.Tm n
  channelSoup e₁ x e₂ =
    SoupTerm._⊗_ (SoupTerm._⊗_ e₁ (SoupTerm.` x)) e₂

  closeSend : Source.Tm 2
  closeSend = Source._·¹_ (Source.K (Source.`end Types.‼)) (Source.` 0F)

  closeRecv : Source.Tm 2
  closeRecv = Source._·¹_ (Source.K (Source.`end Types.⁇)) (Source.` 1F)

  closeSource :
    SourceReduction.Frame* 0 →
    SourceReduction.Frame* 0 →
    Typed.Proc 0
  closeSource E₁ E₂ =
    Typed.ν (1 ∷ []) (1 ∷ [])
      ( Typed.⟪ plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (Source.weaken* 2)) closeSend ⟫
      Typed.∥
        Typed.⟪ plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (Source.weaken* 2)) closeRecv ⟫
      )

  closeTarget :
    SourceReduction.Frame* 0 →
    SourceReduction.Frame* 0 →
    Typed.Proc 0
  closeTarget E₁ E₂ =
    Typed.⟪ plug*ˢ E₁ Source.* ⟫
    Typed.∥
    Typed.⟪ plug*ˢ E₂ Source.* ⟫

  source-frame-env :
    SourceReduction.Frame* 0 →
    SoupExpression.Frame* (2 *ℕ n)
  source-frame-env E = Tᶠ*[ E ] {σ = emptyEnv} emptyValueEnv

  closed-frame-env :
    SourceReduction.Frame* 0 →
    SoupExpression.Frame* n
  closed-frame-env E = Tᶠ*[ E ] {σ = emptyEnv} emptyValueEnv

  closeEnv : 𝔽 n → 𝔽 n → Translation.Env 2 n
  closeEnv left right zero =
    channelSoup SoupTerm.* left SoupTerm.*
  closeEnv left right (suc zero) =
    channelSoup SoupTerm.* right SoupTerm.*

  closeValueEnv :
    ∀ {n} {left right : 𝔽 n} →
    ValueEnv (closeEnv left right)
  closeValueEnv zero =
    SoupExpression.V-⊗
      (SoupExpression.V-⊗ SoupExpression.V-K SoupExpression.V-`)
      SoupExpression.V-K
  closeValueEnv (suc zero) =
    SoupExpression.V-⊗
      (SoupExpression.V-⊗ SoupExpression.V-K SoupExpression.V-`)
      SoupExpression.V-K

  canonicalCloseEnv : Translation.Env 2 (2 *ℕ 1)
  canonicalCloseEnv =
    closeEnv (Soup.endpoint {n = 1} 0F zero)
      (Soup.endpoint {n = 1} 0F (suc zero))

  canonicalGeneratedEnv : Translation.Env 2 (2 *ℕ 1)
  canonicalGeneratedEnv =
    let sigma₁ = proj₁ (Translation.UB[ 1 ∷ [] ] (Soup.leftEnd {n = 1} 0F)
          (SoupTerm.* , Soup.leftEnd {n = 1} 0F , SoupTerm.*))
        sigma₂ = proj₁ (Translation.UB[ 1 ∷ [] ] (Soup.rightEnd {n = 1} 0F)
          (SoupTerm.* , Soup.rightEnd {n = 1} 0F , SoupTerm.*))
    in (sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ (λ ())

  canonical-generated-env :
    (x : 𝔽 2) → canonicalGeneratedEnv x ≡ canonicalCloseEnv x
  canonical-generated-env zero = refl
  canonical-generated-env (suc zero) = refl

  weaken2↑ : 1 Source.→ᵣ 3
  weaken2↑ = Source._↑ (Source.weaken* 2)

  weaken2↑↑ : 2 Source.→ᵣ 4
  weaken2↑↑ = Source._↑ (Source._↑ (Source.weaken* 2))

  translated-renamed :
    (e : Source.Tm 0) (ρ : 𝔽 0 → 𝔽 n) →
    Translation.T[ e ] emptyEnv ≡
    (Translation.T[ e ] (emptyEnv {n = 0})) SoupTerm.⋯ᵣ ρ
  translated-renamed e ρ =
    T[_]-Env-cong e (λ ()) ■
    T[_]-renEnv e (emptyEnv {n = 0}) ρ

  canonical-empty :
    ∀ {n} (e : Source.Tm 0) →
    Translation.T[ e ] (λ ()) ≡ Translation.T[ e ] (emptyEnv {n = n})
  canonical-empty e = T[_]-Env-cong e (λ ())

  T-weaken2-0 :
    (e : Source.Tm 0) (σ : Translation.Env 2 n) →
    Translation.T[ Source._⋯_ e (Source.weaken* 2) ] σ ≡
    Translation.T[ e ] emptyEnv
  T-weaken2-0 e σ =
    T[_]-⋯ᵣ e (Source.weaken* 2) σ ■
    T[_]-Env-cong e (λ ())

  T-weaken2-1 :
    (e : Source.Tm 1) (σ : Translation.Env 2 n) →
    Translation.T[ Source._⋯_ e weaken2↑ ]
      (Translation.liftEnv σ) ≡
    Translation.T[ e ] (Translation.liftEnv emptyEnv)
  T-weaken2-1 e σ =
    T[_]-⋯ᵣ e weaken2↑ (Translation.liftEnv σ) ■
    T[_]-Env-cong e λ where
      zero → refl

  T-weaken2-2 :
    (e : Source.Tm 2) (σ : Translation.Env 2 n) →
    Translation.T[ Source._⋯_ e weaken2↑↑ ]
      (Translation.liftEnv (Translation.liftEnv σ)) ≡
    Translation.T[ e ] (Translation.liftEnv (Translation.liftEnv emptyEnv))
  T-weaken2-2 e σ =
    T[_]-⋯ᵣ e weaken2↑↑
      (Translation.liftEnv (Translation.liftEnv σ)) ■
    T[_]-Env-cong e λ where
      zero → refl
      (suc zero) → refl

  T-frame-weaken2-plug :
    (E : SourceReduction.Frame 0)
    {e : Source.Tm 2} {u : SoupTerm.Tm n}
    (σ : Translation.Env 2 n) →
    Translation.T[ e ] σ ≡ u →
    Translation.T[ SourceReduction._[_]
      (SourceReduction.frame-⋯ E (Source.weaken* 2) (λ _ → SourceReduction.V-`))
      e ] σ ≡
    SoupExpression._[_]
      (Tᶠ[ E ] {σ = emptyEnv} emptyValueEnv) u
  T-frame-weaken2-plug (SourceReduction.app₁ e d V?) σ redex-eq =
    cong₂ (SoupTerm._·⟨ d ⟩_) redex-eq (T-weaken2-0 e σ)
  T-frame-weaken2-plug (SourceReduction.app₂ e d V?) σ redex-eq =
    cong₂ (λ x y → SoupTerm._·⟨_⟩_ x d y)
      (T-weaken2-0 e σ) redex-eq
  T-frame-weaken2-plug (SourceReduction.□⊗ e) σ redex-eq =
    cong₂ SoupTerm._⊗_ redex-eq (T-weaken2-0 e σ)
  T-frame-weaken2-plug (V SourceReduction.⊗□) σ redex-eq =
    cong₂ SoupTerm._⊗_
      (T-weaken2-0 (SourceReduction.vTm V) σ)
      redex-eq
  T-frame-weaken2-plug (SourceReduction.□; e) σ redex-eq =
    cong₂ SoupTerm._;_ redex-eq (T-weaken2-0 e σ)
  T-frame-weaken2-plug (SourceReduction.`let-`in e) σ redex-eq =
    cong₂ SoupTerm.`let_`in_ redex-eq (T-weaken2-1 e σ)
  T-frame-weaken2-plug (SourceReduction.`let⊗-`in e) σ redex-eq =
    cong₂ SoupTerm.`let⊗_`in_ redex-eq (T-weaken2-2 e σ)
  T-frame-weaken2-plug (SourceReduction.`inj□ i) σ redex-eq =
    cong (SoupTerm.`inj i) redex-eq
  T-frame-weaken2-plug (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) σ redex-eq =
    cong₂ (λ e es → SoupTerm.`case e `of⟨ proj₁ es ; proj₂ es ⟩)
      redex-eq
      (cong₂ _,_ (T-weaken2-1 e₁ σ) (T-weaken2-1 e₂ σ))

  T-plug-weaken2* :
    (E : SourceReduction.Frame* 0)
    {e : Source.Tm 2} {u : SoupTerm.Tm n}
    (σ : Translation.Env 2 n) →
    Translation.T[ e ] σ ≡ u →
    Translation.T[ plug*ˢ (SourceReduction._⋯ᶠ*_ E (Source.weaken* 2)) e ] σ ≡
    plug*ᵘ (closed-frame-env E) u
  T-plug-weaken2* [] σ redex-eq = redex-eq
  T-plug-weaken2* (E ∷ Es) σ redex-eq =
    T-frame-weaken2-plug E σ (T-plug-weaken2* Es σ redex-eq)

U-close :
  {E₁ E₂ : SourceReduction.Frame* 0}
  {n m : ℕ} {C : Soup.Config n m} →
  SoupImage (closeSource E₁ E₂) C →
  Σ[ C′ ∈ Soup.Config n m ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (closeTarget E₁ E₂) C′
U-close {E₁ = E₁} {E₂ = E₂} {n = n} {m = m} {C = C} image =
  C′ ,
  SoupReduction.RUS-Close
    {n = n} {m = m} {cs = Soup.channels C} {ts = Soup.threads C}
    j₁ j₂ i zero (suc zero) F₁ F₂
    {e₁ = SoupTerm.*} {e₁′ = SoupTerm.*}
    {e₂ = SoupTerm.*} {e₂′ = SoupTerm.*}
    j≢k SoupReduction.left-right
    selected-channel selected₁ selected₂ ,
  record
    { channelEmbedding = λ ()
    ; channelEmbedding-injective = λ {}
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; endpointEmbedding = λ ()
    ; endpoint-respects-channel = λ ()
    ; live-channel = λ ()
    ; live-thread = live-thread′
    ; garbage-channel = garbage-channel′
    ; garbage-thread = garbage-thread′
    }
  where
  j₁ : 𝔽 m
  j₁ = threadEmbedding image 0F

  j₂ : 𝔽 m
  j₂ = threadEmbedding image 1F

  i : 𝔽 n
  i = channelEmbedding image 0F

  ρ : 𝔽 (2 *ℕ 1) → 𝔽 (2 *ℕ n)
  ρ = endpointEmbedding image

  physCloseEnv : Translation.Env 2 (2 *ℕ n)
  physCloseEnv =
    closeEnv (Soup.endpoint i zero) (Soup.endpoint i (suc zero))

  close-env-renamed :
    (x : 𝔽 2) →
    SoupTerm._⋯ᵣ_ (canonicalCloseEnv x) ρ ≡ physCloseEnv x
  close-env-renamed zero =
    cong (λ x → channelSoup SoupTerm.* x SoupTerm.*)
      (endpoint-respects-channel image 0F zero)
  close-env-renamed (suc zero) =
    cong (λ x → channelSoup SoupTerm.* x SoupTerm.*)
      (endpoint-respects-channel image 0F (suc zero))

  F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)
  F₁ = source-frame-env {n = n} E₁
  F₂ = source-frame-env {n = n} E₂

  parent child : Soup.Thread n
  parent = plug*ᵘ F₁ SoupTerm.*
  child = plug*ᵘ F₂ SoupTerm.*

  threads′ : Vec (Soup.Thread n) m
  threads′ = SoupReduction.replaceTwo (Soup.threads C) j₁ parent j₂ child

  channels′ : Vec Soup.Channel n
  channels′ = SoupReduction.replaceAt (Soup.channels C) i (false , [] , [])

  C′ : Soup.Config n m
  C′ = Soup.config channels′ threads′

  j≢k : j₁ ≢ j₂
  j≢k eq with threadEmbedding-injective image eq
  ... | ()

  selected-channel :
    lookup (Soup.channels C) i ≡ (true , [] , [])
  selected-channel = live-channel image 0F

  selected₁ :
    lookup (Soup.threads C) j₁ ≡
    plug*ᵘ F₁
      (SoupTerm.K (Source.`end Types.‼) SoupTerm.·¹
        channelSoup SoupTerm.* (Soup.endpoint i zero) SoupTerm.*)
  selected₁ =
    live-thread image 0F
    ■ cong (SoupTerm._⋯ᵣ ρ)
        (T[_]-Env-cong
          (plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (Source.weaken* 2)) closeSend)
          canonical-generated-env)
    ■ sym
      (T[_]-renEnv
        (plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (Source.weaken* 2)) closeSend)
        canonicalCloseEnv ρ)
    ■ T[_]-Env-cong
      (plug*ˢ (SourceReduction._⋯ᶠ*_ E₁ (Source.weaken* 2)) closeSend)
      close-env-renamed
    ■ T-plug-weaken2* E₁ physCloseEnv refl

  selected₂ :
    lookup (Soup.threads C) j₂ ≡
    plug*ᵘ F₂
      (SoupTerm.K (Source.`end Types.⁇) SoupTerm.·¹
        channelSoup SoupTerm.* (Soup.endpoint i (suc zero)) SoupTerm.*)
  selected₂ =
    live-thread image 1F
    ■ cong (SoupTerm._⋯ᵣ ρ)
        (T[_]-Env-cong
          (plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (Source.weaken* 2)) closeRecv)
          canonical-generated-env)
    ■ sym
      (T[_]-renEnv
        (plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (Source.weaken* 2)) closeRecv)
        canonicalCloseEnv ρ)
    ■ T[_]-Env-cong
      (plug*ˢ (SourceReduction._⋯ᶠ*_ E₂ (Source.weaken* 2)) closeRecv)
      close-env-renamed
    ■ T-plug-weaken2* E₂ physCloseEnv refl

  parent-live :
    parent ≡
    lookup (canonicalThreads (closeTarget E₁ E₂)) 0F
      SoupTerm.⋯ᵣ (λ ())
  parent-live =
    sym (T[_]-plugᶠ* E₁ (emptyValueEnv {n = 2 *ℕ n}))
    ■ translated-renamed (plug*ˢ E₁ Source.*) (λ ())
    ■ cong (SoupTerm._⋯ᵣ (λ ()))
        (sym (canonical-empty {n = 0} (plug*ˢ E₁ Source.*)))

  child-live :
    child ≡
    lookup (canonicalThreads (closeTarget E₁ E₂)) 1F
      SoupTerm.⋯ᵣ (λ ())
  child-live =
    sym (T[_]-plugᶠ* E₂ (emptyValueEnv {n = 2 *ℕ n}))
    ■ translated-renamed (plug*ˢ E₂ Source.*) (λ ())
    ■ cong (SoupTerm._⋯ᵣ (λ ()))
        (sym (canonical-empty {n = 0} (plug*ˢ E₂ Source.*)))

  live-thread′ :
    (l : 𝔽 (Translation.processCount (closeTarget E₁ E₂))) →
    lookup (Soup.threads C′) (threadEmbedding image l) ≡
    lookup (canonicalThreads (closeTarget E₁ E₂)) l
      SoupTerm.⋯ᵣ (λ ())
  live-thread′ zero =
    VecP.lookup∘updateAt′ j₁ j₂ j≢k
      (SoupReduction.replaceAt (Soup.threads C) j₁ parent)
    ■ VecP.lookup∘updateAt j₁ (Soup.threads C)
    ■ parent-live
  live-thread′ (suc zero) =
    VecP.lookup∘updateAt j₂
      (SoupReduction.replaceAt (Soup.threads C) j₁ parent)
    ■ child-live

  garbage-channel′ :
    (l : 𝔽 n) →
    ChannelOutside {P = closeTarget E₁ E₂} (λ ()) l →
    lookup (Soup.channels C′) l ≡ (false , [] , [])
  garbage-channel′ l outside with l FinP.≟ i
  ... | yes refl = VecP.lookup∘updateAt i (Soup.channels C)
  ... | no l≢i =
    VecP.lookup∘updateAt′ l i l≢i (Soup.channels C)
    ■ garbage-channel image l (λ { zero i≡l → l≢i (sym i≡l) })

  garbage-thread′ :
    (l : 𝔽 m) →
    ThreadOutside {P = closeTarget E₁ E₂} (threadEmbedding image) l →
    lookup (Soup.threads C′) l ≡ SoupTerm.K Source.`unit
  garbage-thread′ l outside =
    VecP.lookup∘updateAt′ l j₂ (λ l≡k → outside 1F (sym l≡k))
      (SoupReduction.replaceAt (Soup.threads C) j₁ parent)
    ■ VecP.lookup∘updateAt′ l j₁ (λ l≡j → outside 0F (sym l≡j))
      (Soup.threads C)
    ■ garbage-thread image l outside
