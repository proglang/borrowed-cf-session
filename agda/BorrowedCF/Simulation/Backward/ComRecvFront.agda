module BorrowedCF.Simulation.Backward.ComRecvFront where
-- Extracted BR-side front-force mirror of com-front-force-notmob (durable, reusable).
-- The recv handle at BR-local position xpos is co-located at the BR front
-- (toℕ xpos ≡ 0) when the BR front and the handle are both ¬Mobile.


open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; νσ-VSub; close-arg-var; head⊗′; ⟨⟩≄⊗;
         inv-U-ν-∥-shape; U-ν-singleton; inv-ν-chanCx; ν-inj; frameApp-reflect)
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋; U-⋯ₚ; U-cong)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (F-⋯f*-fuse; frame*-cong; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.Support.Strengthen
  using (Inverter*; strengthen-Tm-gen*; strengthen-Proc-gen*; ↑*-↑ˡ; ↑*-↑ʳ)
open import BorrowedCF.Simulation.Support.ReverseConfine using (strengthen-frame*; count-handle-comᴸ)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-comᴿ; before-com-binderᴿ; before-com-binderᴸ-gen)
open import BorrowedCF.Simulation.Support.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Support.RevGrindA
  using (com-¬before; choice-¬before; barevar-arg-count; invApp-arg)
open import BorrowedCF.Simulation.Support.RevComConfine
  using (frames-𝕀; com-xS-min; before-com-binderᴸ; ¬mobile-block-at; count-plug-add)
open import BorrowedCF.Simulation.Support.RevComImage using (com-image-block1; recv-image-block2; pos⇒suc)
open import BorrowedCF.Simulation.Support.InvFrame as IF using (inv-app; arg-type)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before; count-≼-eq)
open import BorrowedCF.Simulation.Support.Confine
  using (count; ≼⇒count≤; count-self; count-join-Dir; count-join-PS; count0⇒∉dom; +≡0)
open import BorrowedCF.Simulation.Support.Theorems.Com using (fn-send-dom)
open import BorrowedCF.Types using (new-dual; unr⇒mobile)
open import BorrowedCF.Context using (join; biasedDir; _∶_≼_; _⸴*_; _∥_)
import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅; LeftPat)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n; toℕ-fromℕ<)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Sum using ([_,_]′)
import Data.Sum as Sum
open TP using (BindGroup; structBinder; BindCtx; bindCtx⇒chanCtx)
open import BorrowedCF.Simulation.Support.ReverseInv using (⊗-inj)
open import BorrowedCF.Simulation.Backward.PhiInj using (plugΦ-inj-nonφ; U-notΦ; nΦ-∥)
open import BorrowedCF.Simulation.Support.Theorems.PhiTel
  using (Uν-flatΦ; plugΦ-++; Btel; _++Φ_; widthΦ; toℕ-wkΦ; widthΦ-Btel; widthΦ-++)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (leafσ)
open import BorrowedCF.Simulation.Backward.HandleId using (handleId-block1; handleId-block2)
open import BorrowedCF.Processes.Translation using (syncs; UChan; ϕ[_])
open import BorrowedCF.Simulation.Backward.ComConfineGen using (send-¬mobile; recv-¬mobile)
open import BorrowedCF.Simulation.Backward.ComMobileFront using (mobile-front-end-⊥)
open import BorrowedCF.Simulation.Backward.ComFire using (com-fire)
open import Data.List.Properties using (∷-injective)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2
  using (com-head≥1; com-head≥2; send-handle-≃msg-app; recv-handle-≃msg-app)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-groupᴿ; before-com-binderᴿ-gen)
open import BorrowedCF.Types using (Mobile)
open import BorrowedCF.Simulation.Backward.ComFrontEmpty using (send-block-empty)
open import BorrowedCF.Simulation.Support.Frames using (++ₛ-VSub)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (VSub-canonₛ)
open import BorrowedCF.Reduction.Base using (value-⋯; V-K; V-`)
import BorrowedCF.Simulation.Backward.ComReconcile as CR


-- recv-front-force-notmob : the BR-side mirror.  The recv handle sits at
-- BR-local position `xpos` (global `(sum BL ↑ʳ xpos) ↑ˡ mm`); if the BR-front
-- (global `fr`, toℕ ≡ sum BL) is ¬Mobile and the handle is ¬Mobile, the recv is
-- co-located at the BR front (`toℕ xpos ≡ 0`).  Uses the ᴿ confinement lemmas
-- (before-com-binderᴿ-gen / count-handle-groupᴿ, whose `wkˡ (sum BL)` index is
-- definitionally `sum BL ↑ʳ`) and choice-¬before (the recv arg is a bare var).
------------------------------------------------------------------------

recv-front-force-notmob : ∀ {mm} (BL BR : BindGroup)
  {Delta : Ctx (sum BL + sum BR + mm)}
  {g : Struct mm} {Pat : CxPat (sum BL + sum BR + mm)}
  {grR aR bL : Struct (sum BL + sum BR + mm)}
  {U eps}
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
  → Delta ; grR ⊢ K `recv ·¹ (` ((sum BL ↑ʳ xpos) ↑ˡ mm)) ∶ U ∣ eps
  → Fin.toℕ xpos ≡ 0
recv-front-force-notmob {mm} BL BR {Delta} {g} {Pat} {grR} {aR} {bL} xpos fr tfrG ¬uy ¬ux lpR PrecR Prec1 redexR
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

