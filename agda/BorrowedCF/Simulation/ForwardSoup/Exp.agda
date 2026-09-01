module BorrowedCF.Simulation.ForwardSoup.Exp where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Expressions as SourceReduction
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

translated-renamed :
  ∀ {n} (e : Source.Tm 0) (rho : 𝔽 0 → 𝔽 n) →
  Translation.T[ e ] (emptyEnv {n = n}) ≡
  SoupTerm._⋯ᵣ_ (Translation.T[ e ] (emptyEnv {n = 0})) rho
translated-renamed e rho =
  T[_]-Env-cong e (λ ()) ■
  T[_]-renEnv e (emptyEnv {n = 0}) rho

canonical-empty :
  ∀ {n} (e : Source.Tm 0) →
  Translation.T[ e ] (λ ()) ≡
  Translation.T[ e ] (emptyEnv {n = n})
canonical-empty e = T[_]-Env-cong e (λ ())

U-exp :
  ∀ {e e′ : Source.Tm 0} {n m} {C : Soup.Config n m} →
  SoupImage (Typed.⟪ e ⟫) C →
  e SourceReduction.⋯→ e′ →
  Σ[ C′ ∈ Soup.Config n m ]
    (C SoupReduction.─→ₚ C′) × SoupImage (Typed.⟪ e′ ⟫) C′
U-exp {e = e} {e′ = e′} {n = n} {C = C} image red =
  let j = threadEmbedding image 0F
      rho = endpointEmbedding image
      before =
        live-thread image 0F ■
        cong (SoupTerm._⋯ᵣ rho) (canonical-empty {n = 0} e) ■
        sym (translated-renamed e rho)
      after =
        translated-renamed e′ rho ■
        cong (SoupTerm._⋯ᵣ rho) (sym (canonical-empty {n = 0} e′))
      translated-step = T[_]-⋯→ (λ ()) red
      selected-step =
        subst (λ lhs →
          lhs SoupExpression.⋯→ Translation.T[ e′ ] emptyEnv)
          (sym before) translated-step
      C′ = Soup.config (Soup.channels C)
             (SoupReduction.replaceAt (Soup.threads C) j
               (Translation.T[ e′ ] emptyEnv))
  in C′ , SoupReduction.RUS-Exp j selected-step , record
    { channelEmbedding = channelEmbedding image
    ; channelEmbedding-injective = channelEmbedding-injective image
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; endpointEmbedding = rho
    ; endpoint-respects-channel = endpoint-respects-channel image
    ; live-channel = live-channel image
    ; live-thread = λ where
        zero → VecP.lookup∘updateAt j (Soup.threads C) ■ after
    ; garbage-channel = garbage-channel image
    ; garbage-thread = λ k outside →
        VecP.lookup∘updateAt′ k j
          (λ k≡j → outside 0F (sym k≡j)) (Soup.threads C)
        ■ garbage-thread image k outside
    }
