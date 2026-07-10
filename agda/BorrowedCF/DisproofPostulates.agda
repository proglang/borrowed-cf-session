module BorrowedCF.DisproofPostulates where

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.LinUnique using (cnt; ≼-cnt; fv⇒cnt)
open import Data.Fin using () renaming (zero to Z; suc to S)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.Nat using (_≤_; s≤s)

ΓL : Ctx 1
ΓL _ = ⟨ end ‼ ⟩

Z-lin : Unr (ΓL Z) → ⊥
Z-lin ⟨ () ⟩

2≰1 : 2 ≤ 1 → ⊥
2≰1 (s≤s ())

1≰0 : 1 ≤ 0 → ⊥
1≰0 ()

-- (1) ↓fv-≼ is FALSE: γ₂ free ⇒ a linear var duplicates.  `Z∥`Z ≼ `Z, cnt 2≤1.
bad-dfv : ⊥
bad-dfv = 2≰1 (≼-cnt {x = Z} Z-lin (↓fv-≼ {Γ = ΓL} {γ₁ = ` Z} {γ₂ = ` Z} 𝟙 (T-Var Z refl)))

-- (2) ≤γ-letpair is FALSE: fully generic (no derivation).  (`Z);(`Z) ≼ `Z, cnt 2≤1.
bad-lp : ⊥
bad-lp = 2≰1 (≼-cnt {x = Z} Z-lin (≤γ-letpair {Γ = ΓL} {γ = ` Z} {e₁ = ` Z} {e₂ = ` (S (S Z))}))

-- (3) refine-fv is FALSE: retyping under an unrelated γ strips the needed variable.
--     refine-fv [] (T-Var Z) demands a derivation of `Z under [].
bad-rfv : ⊥
bad-rfv = 1≰0 (fv⇒cnt (proj₁ (refine-fv {Γ = ΓL} {γ′ = ` Z} [] (T-Var Z refl))) (x∈⁅x⁆ Z))
