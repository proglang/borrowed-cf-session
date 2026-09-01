module BorrowedCF.Processes.TranslationSoup.Examples where

open import Data.Maybe using (just; nothing)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as 𝐓Soup
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Fin.Patterns

restriction :
  𝐓Soup.U[
    𝐓.ν (1 ∷ []) (1 ∷ [])
      (𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫)
  ]
  ≡
  ( 1 , 1
  , 𝐒.config
      ((false , [] , []) ∷ [])
      ( ( 𝐓Soup.chanTriple
            (𝐒Tm.* , 𝐒.leftEnd (Fin.zero {n = 0}) , 𝐒Tm.*)
          𝐒Tm.⊗
          𝐓Soup.chanTriple
            (𝐒Tm.* , 𝐒.rightEnd (Fin.zero {n = 0}) , 𝐒Tm.*)
        ) ∷ []
      )
  )
restriction = refl

flagged-restriction :
  𝐓Soup.U[
    𝐓.ν (1 ∷ 0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      (𝐓.⟪ 𝐓Tm.K 𝐓Tm.`unit ⟫)
  ]
  ≡
  ( 1 , 1
  , 𝐒.config
      ( ( false
        , 𝐒.acq ∷ 𝐒.drop ∷ []
        , 𝐒.acq ∷ []
        ) ∷ []
      )
      (𝐒Tm.K 𝐒Tm.`unit ∷ [])
  )
flagged-restriction = refl

bindResult : 𝐓Soup.BindResult (1 ∷ 0 ∷ 1 ∷ []) 2
bindResult =
  𝐓Soup.UB[ 1 ∷ 0 ∷ 1 ∷ [] ]
    0F
    (𝐒Tm.* , 0F , 𝐒Tm.*)

bind-flags :
  proj₂ bindResult ≡ 𝐒.acq ∷ 𝐒.drop ∷ []
bind-flags = refl

bind-first :
  proj₁ bindResult 0F
  ≡ 𝐓Soup.chanTriple (𝐒Tm.* , 0F , 𝐒Tm.`phi (0F , 1))
bind-first = refl

bind-last :
  proj₁ bindResult 1F
  ≡ 𝐓Soup.chanTriple (𝐒Tm.`phi (0F , 0) , 0F , 𝐒Tm.*)
bind-last = refl

resolvedTerm : 𝐒Tm.Tm 1
resolvedTerm = 𝐒Tm.ƛ (𝐒Tm.`phi (1F , 0))

resolved-under-binder :
  𝐒Tm.phiRefs resolvedTerm
  ≡ just (0F , 0) ∷ []
resolved-under-binder = refl

invalidTerm : 𝐒Tm.Tm 1
invalidTerm = 𝐒Tm.ƛ (𝐒Tm.`phi (0F , 0))

local-ref-rejected :
  𝐒Tm.phiRefs invalidTerm
  ≡ nothing ∷ []
local-ref-rejected = refl

oneChannel : 𝐒.Config 1 0
oneChannel =
  𝐒.config
    ((false , 𝐒.drop ∷ [] , 𝐒.acq ∷ []) ∷ [])
    []

endpoint-order :
  𝐒.endpointFlagLists oneChannel
  ≡ (𝐒.drop ∷ []) ∷ (𝐒.acq ∷ []) ∷ []
endpoint-order = refl
