module BorrowedCF.Simulation.ForwardSoup.Fork where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Fin.Base as FinBase using (punchIn; punchOut)
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

open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image

open Nat.Variables
open Fin.Patterns

private
  emptyEnv : Translation.Env 0 n
  emptyEnv ()

  plug*ˢ : SourceReduction.Frame* n → Source.Tm n → Source.Tm n
  plug*ˢ = SourceReduction._[_]*

  plug*ᵘ : SoupExpression.Frame* n → SoupTerm.Tm n → SoupTerm.Tm n
  plug*ᵘ = SoupExpression._[_]*

  forkRedex : Source.Tm 0 → Source.Tm 0
  forkRedex e = Source._·¹_ (Source.K Source.`fork) e

  childSource : Source.Tm 0 → Source.Tm 0
  childSource e = Source._·¹_ e Source.*

  childSoup : SoupTerm.Tm n → SoupTerm.Tm n
  childSoup e = SoupTerm._·¹_ e SoupTerm.*

translated-renamed :
  (e : Source.Tm 0) (ρ : 𝔽 0 → 𝔽 n) →
  Translation.T[ e ] emptyEnv ≡
  (Translation.T[ e ] (emptyEnv {n = 0})) SoupTerm.⋯ᵣ ρ
translated-renamed e ρ =
  T[_]-Env-cong e (λ ()) ■
  T[_]-renEnv e (emptyEnv {n = 0}) ρ

canonical-empty :
  ∀ {n} (e : Source.Tm 0) →
  Translation.T[ e ] (λ ()) ≡
  Translation.T[ e ] (emptyEnv {n = n})
canonical-empty e = T[_]-Env-cong e (λ ())

emptyValueEnv : ∀ {n} → ValueEnv (emptyEnv {n = n})
emptyValueEnv ()

forkSource : SourceReduction.Frame* 0 → Source.Tm 0 → Typed.Proc 0
forkSource E e = Typed.⟪ plug*ˢ E (forkRedex e) ⟫

forkTarget : SourceReduction.Frame* 0 → Source.Tm 0 → Typed.Proc 0
forkTarget E e =
  Typed.⟪ plug*ˢ E Source.* ⟫
  Typed.∥
  Typed.⟪ childSource e ⟫

U-fork :
  {E : SourceReduction.Frame* 0} {e : Source.Tm 0}
  {n m : ℕ} {C : Soup.Config n m} →
  SoupImage (forkSource E e) C →
  SourceReduction.Value e →
  Σ[ C′ ∈ Soup.Config n (suc m) ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (forkTarget E e) C′
U-fork {E = E} {e = e} {n = n} {m = m} {C = C} image Ve =
  C′ ,
  SoupReduction.RUS-Fork j F (T[_]-Value Ve emptyValueEnv) selected ,
  record
    { channelEmbedding = channelEmbedding image
    ; channelEmbedding-injective = channelEmbedding-injective image
    ; threadEmbedding = threadEmbedding′
    ; threadEmbedding-injective = threadEmbedding′-injective
    ; endpointEmbedding = ρ
    ; endpoint-respects-channel = λ ()
    ; live-channel = λ ()
    ; live-thread = λ where
        zero →
          VecP.insertAt-punchIn
            (SoupReduction.replaceAt (Soup.threads C) j parent)
            (suc j)
            child
            (threadEmbedding image 0F)
          ■ VecP.lookup∘updateAt (threadEmbedding image 0F) (Soup.threads C)
          ■ parent-live
        (suc zero) →
          VecP.insertAt-lookup
            (SoupReduction.replaceAt (Soup.threads C) j parent)
            (suc j)
            child
          ■ child-live
    ; garbage-channel = garbage-channel image
    ; garbage-thread = garbage-thread′
    }
  where
  j : 𝔽 m
  j = threadEmbedding image 0F

  ρ : 𝔽 0 → 𝔽 _
  ρ = endpointEmbedding image

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ E ] {σ = emptyEnv} emptyValueEnv

  arg : Soup.Thread n
  arg = Translation.T[ e ] emptyEnv

  parent : Soup.Thread n
  parent = plug*ᵘ F SoupTerm.*

  child : Soup.Thread n
  child = childSoup arg

  threads′ : Vec (Soup.Thread n) (suc m)
  threads′ =
    SoupReduction.insertAfter
      (SoupReduction.replaceAt (Soup.threads C) j parent)
      j
      child

  C′ : Soup.Config n (suc m)
  C′ = Soup.config (Soup.channels C) threads′

  selected :
    lookup (Soup.threads C) j ≡
    plug*ᵘ F (SoupTerm._·¹_ (SoupTerm.K Source.`fork) arg)
  selected =
    live-thread image 0F
    ■ cong (SoupTerm._⋯ᵣ ρ) (canonical-empty {n = 0} (plug*ˢ E (forkRedex e)))
    ■ sym (translated-renamed (plug*ˢ E (forkRedex e)) ρ)
    ■ T[_]-plugᶠ* E emptyValueEnv

  parent-live :
    parent ≡
    (lookup (canonicalThreads (forkTarget E e)) 0F) SoupTerm.⋯ᵣ ρ
  parent-live =
    sym (T[_]-plugᶠ* E emptyValueEnv)
    ■ translated-renamed (plug*ˢ E Source.*) ρ
    ■ cong (SoupTerm._⋯ᵣ ρ) (sym (canonical-empty {n = 0} (plug*ˢ E Source.*)))

  child-live :
    child ≡
    (lookup (canonicalThreads (forkTarget E e)) 1F) SoupTerm.⋯ᵣ ρ
  child-live =
    translated-renamed (childSource e) ρ
    ■ cong (SoupTerm._⋯ᵣ ρ) (sym (canonical-empty {n = 0} (childSource e)))

  threadEmbedding′ : 𝔽 2 → 𝔽 (suc m)
  threadEmbedding′ zero = punchIn (suc j) j
  threadEmbedding′ (suc zero) = suc j

  threadEmbedding′-injective : FinInjective threadEmbedding′
  threadEmbedding′-injective {zero} {zero} eq = refl
  threadEmbedding′-injective {zero} {suc zero} eq =
    ⊥-elim (FinP.punchInᵢ≢i (suc j) j eq)
  threadEmbedding′-injective {suc zero} {zero} eq =
    ⊥-elim (FinP.punchInᵢ≢i (suc j) j (sym eq))
  threadEmbedding′-injective {suc zero} {suc zero} eq = refl

  garbage-thread′ :
    (k : 𝔽 (suc m)) →
    ThreadOutside {P = forkTarget E e} threadEmbedding′ k →
    lookup threads′ k ≡ SoupTerm.K Source.`unit
  garbage-thread′ k outside with k FinP.≟ suc j
  ... | yes k≡ =
    ⊥-elim (outside 1F (sym k≡))
  ... | no k≢pos =
    cong (lookup threads′) (sym (FinP.punchIn-punchOut pos≢k))
    ■ VecP.insertAt-punchIn
        (SoupReduction.replaceAt (Soup.threads C) j parent)
        (suc j)
        child
        l
    ■ VecP.lookup∘updateAt′ l j l≢j (Soup.threads C)
    ■ garbage-thread image l outside-old
    where
    pos≢k : suc j ≢ k
    pos≢k = k≢pos ∘ sym

    l : 𝔽 m
    l = punchOut {i = suc j} {j = k} pos≢k

    outside-old : ThreadOutside {P = forkSource E e} (threadEmbedding image) l
    outside-old zero old≡l =
      outside 0F
        (cong (punchIn (suc j)) old≡l
         ■ FinP.punchIn-punchOut pos≢k)

    l≢j : l ≢ j
    l≢j l≡j = outside-old 0F (sym l≡j)
