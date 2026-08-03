-- | Bare-variable front-forcing for the telescoped backward R-Choice.  Twin of
--   Backward.Com.{com,recv}-front-force-notmob, but the consumed handle argument
--   is a BARE channel variable `(` x)` (select / branch), so both the LEFT-block
--   (select) and RIGHT-block (branch) versions use `barevar-arg-count` +
--   `choice-¬before` (constant-general in the head `c`).  The ¬Mobile facts are
--   supplied by the caller (from ChoiceConfineGen.{select,branch}-¬mobile for the
--   handle, and ComMobileFront.mobile-front-end-⊥ for the block front).
module BorrowedCF.Simulation.Backward.ChoiceConfine where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open import BorrowedCF.Simulation.Support.ReverseConfine using (count-handle-comᴸ)
open import BorrowedCF.Simulation.Support.RevGrindC
  using (count-handle-groupᴿ; before-com-binderᴿ-gen; before-com-binderᴸ-gen)
open import BorrowedCF.Simulation.Support.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Support.RevGrindA using (choice-¬before; barevar-arg-count)
open import BorrowedCF.Simulation.Support.RevComConfine using (com-xS-min)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Types using (Mobile; unr⇒mobile)
open import BorrowedCF.Context using (join; _∶_≼_; _∥_)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅; LeftPat)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n; toℕ-fromℕ<)
open import Data.Nat.Properties using (+-identityʳ)

open TP using (BindGroup; structBinder)
open Fin.Patterns

------------------------------------------------------------------------
-- LEFT-block bare-variable front-force (select handle).
------------------------------------------------------------------------

select-front-force-notmob : ∀ {mm} (BL BR : BindGroup)
  {Delta : Ctx (sum BL + sum BR + mm)}
  {g : Struct mm} {Pat : CxPat (sum BL + sum BR + mm)}
  {grS aS bR : Struct (sum BL + sum BR + mm)}
  {U eps} {c}
  (xpos : 𝔽 (sum BL))
  (fr : 𝔽 (sum BL + sum BR + mm)) (tfrG : Fin.toℕ fr ≡ 0)
  → ¬ Mobile (lookup Delta fr)
  → ¬ Mobile (lookup Delta ((xpos ↑ˡ sum BR) ↑ˡ mm))
  → LeftPat Pat
  → Delta ∶ Pat [ grS ]𝓅 ≼ aS
  → Delta ∶ aS ∥ bR ≼
    ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → Delta ; grS ⊢ K c ·¹ (` ((xpos ↑ˡ sum BR) ↑ˡ mm)) ∶ U ∣ eps
  → Fin.toℕ xpos ≡ 0
select-front-force-notmob {mm} BL BR {Delta} {g} {Pat} {grS} {aS} {bR} xpos fr tfrG ¬u0 ¬ux lpS PrecS Prec1 redexS
  with Fin.toℕ xpos Nat.≟ 0
... | yes e0 = e0
... | no  ne = ⊥-elim (com-xS-min ¬ux ¬u0 lpS PrecS Prec1 cnt1 beforeW 1<=c ¬beforeW)
  where
    x : 𝔽 (sum BL + sum BR + mm)
    x = (xpos ↑ˡ sum BR) ↑ˡ mm
    Sb : Struct (sum BL + sum BR + mm)
    Sb = (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
         ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
         ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR))
    cnt1 : count x Sb ≡ 1
    cnt1 = count-handle-groupᴸ BL BR g xpos
    1<=c : 1 Nat.≤ count x grS
    1<=c = barevar-arg-count (¬ux ∘ unr⇒mobile) redexS
    0<BL : 0 Nat.< sum BL
    0<BL = Nat.≤-trans (Nat.s≤s Nat.z≤n) (toℕ<n xpos)
    fr0 : 𝔽 (sum BL)
    fr0 = Fin.fromℕ< 0<BL
    tfr0 : Fin.toℕ fr0 ≡ 0
    tfr0 = toℕ-fromℕ< 0<BL
    frlift≡ : (fr0 ↑ˡ sum BR) ↑ˡ mm ≡ fr
    frlift≡ = toℕ-injective (toℕ-↑ˡ (fr0 ↑ˡ sum BR) mm ■ toℕ-↑ˡ fr0 (sum BR) ■ tfr0 ■ sym tfrG)
    beforeW : before fr x Sb
    beforeW = subst (\ y -> before y x Sb) frlift≡
                (before-com-binderᴸ-gen BL BR g fr0 xpos tfr0 ne)
    ¬beforeW : ¬ before fr x grS
    ¬beforeW = choice-¬before ¬ux ¬u0 redexS

------------------------------------------------------------------------
-- RIGHT-block bare-variable front-force (branch handle).
------------------------------------------------------------------------

branch-front-force-notmob : ∀ {mm} (BL BR : BindGroup)
  {Delta : Ctx (sum BL + sum BR + mm)}
  {g : Struct mm} {Pat : CxPat (sum BL + sum BR + mm)}
  {grR aR bL : Struct (sum BL + sum BR + mm)}
  {U eps} {c}
  (xpos : 𝔽 (sum BR))
  (fr : 𝔽 (sum BL + sum BR + mm)) (tfrG : Fin.toℕ fr ≡ sum BL)
  → ¬ Mobile (lookup Delta fr)
  → ¬ Mobile (lookup Delta ((sum BL ↑ʳ xpos) ↑ˡ mm))
  → LeftPat Pat
  → Delta ∶ Pat [ grR ]𝓅 ≼ aR
  → Delta ∶ aR ∥ bL ≼
    ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → Delta ; grR ⊢ K c ·¹ (` ((sum BL ↑ʳ xpos) ↑ˡ mm)) ∶ U ∣ eps
  → Fin.toℕ xpos ≡ 0
branch-front-force-notmob {mm} BL BR {Delta} {g} {Pat} {grR} {aR} {bL} xpos fr tfrG ¬uy ¬ux lpR PrecR Prec1 redexR
  with Fin.toℕ xpos Nat.≟ 0
... | yes e0 = e0
... | no  ne = ⊥-elim (com-xS-min ¬ux ¬uy lpR PrecR Prec1 cnt1 beforeW 1<=c ¬beforeW)
  where
    x : 𝔽 (sum BL + sum BR + mm)
    x = (sum BL ↑ʳ xpos) ↑ˡ mm
    Sb : Struct (sum BL + sum BR + mm)
    Sb = (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
         ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ mm)
         ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR))
    cnt1 : count x Sb ≡ 1
    cnt1 = count-handle-groupᴿ BL BR g xpos
    1<=c : 1 Nat.≤ count x grR
    1<=c = barevar-arg-count (¬ux ∘ unr⇒mobile) redexR
    0<BR : 0 Nat.< sum BR
    0<BR = Nat.≤-trans (Nat.s≤s Nat.z≤n) (toℕ<n xpos)
    fr0 : 𝔽 (sum BR)
    fr0 = Fin.fromℕ< 0<BR
    tfr0 : Fin.toℕ fr0 ≡ 0
    tfr0 = toℕ-fromℕ< 0<BR
    frlift≡ : (sum BL ↑ʳ fr0) ↑ˡ mm ≡ fr
    frlift≡ = toℕ-injective
      ( toℕ-↑ˡ (sum BL ↑ʳ fr0) mm ■ toℕ-↑ʳ (sum BL) fr0
      ■ cong (sum BL +_) tfr0 ■ +-identityʳ (sum BL) ■ sym tfrG )
    beforeW : before fr x Sb
    beforeW = subst (λ y → before y x Sb) frlift≡
                (before-com-binderᴿ-gen BL BR g fr0 xpos tfr0 ne)
    ¬beforeW : ¬ before fr x grR
    ¬beforeW = choice-¬before ¬ux ¬uy redexR
