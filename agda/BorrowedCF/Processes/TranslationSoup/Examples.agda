module BorrowedCF.Processes.TranslationSoup.Examples where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as 𝐓Soup
import BorrowedCF.Processes.Untyped as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Terms.Base as 𝐔Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Fin.Patterns

restriction-leaf :
  𝐓Soup.flattenClosed
    (𝐔.ν (𝐔.⟪ (𝐔Tm.` 0F) 𝐔Tm.⊗ (𝐔Tm.` 1F) ⟫))
  ≡
  (1 , 1 ,
   𝐒.config
     (false ∷ [])
     (((𝐒Tm.` (𝐒.leftEnd (Fin.zero {n = 0}))) 𝐒Tm.⊗
       (𝐒Tm.` (𝐒.rightEnd (Fin.zero {n = 0}))) , []) ∷ []))
restriction-leaf = refl

nested-phi-leaf :
  𝐓Soup.flattenClosed
    (𝐔.φ 𝐔.drop
      (𝐔.φ 𝐔.acq
        (𝐔.⟪ (𝐔Tm.` 0F) 𝐔Tm.⊗ (𝐔Tm.` 1F) ⟫)))
  ≡
  (0 , 1 ,
   𝐒.config
     []
     (((𝐒Tm.`phi (0F , 0)) 𝐒Tm.⊗ (𝐒Tm.`phi (0F , 1)) ,
       𝐒.acq ∷ 𝐒.drop ∷ []) ∷ []))
nested-phi-leaf = refl
