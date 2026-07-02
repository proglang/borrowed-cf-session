module BorrowedCF.Simulation2.RevComConfine where

-- Reverse-direction confinement for RU-Com / RU-Choice.
--
-- CORE NEW INGREDIENT (impurity fact, machine-verified in ComHandleProbe):
-- an impure (𝕀) head redex cannot be placed ;-before a live borrow, because the
-- only two ;-before CxPat producers — TF-app₂ on an R-arrow and TF-⊗□ on a seq
-- pair — force the ;-later hole PURE (ℙ).  Formally: the frame stack above an 𝕀
-- redex is entirely LeftPat (every CxPat entry has direction 𝟙 or R, never L),
-- because the effect is 𝕀 at every level (𝕀 is ≤ϵ-maximal and the frame chain is
-- non-decreasing bottom→top).  This is the send/select-handle ≡ 0F confinement's
-- linchpin, absent for the PURE ops (drop/acq/lsplit/rsplit).

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern using (LeftPat; CxPat)
open import BorrowedCF.Reduction.Base
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Sum using (inj₁; inj₂)

open Nat.Variables

-- A single frame above an 𝕀 hole: its output effect is 𝕀 and its one CxPat
-- entry is LeftPat.
frame-𝕀 : ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame n} {U T ϵ} →
          Γ ; 𝒫 ⊢ E ∶ U ∣ 𝕀 ⟶ T ∣ ϵ → (ϵ ≡ 𝕀) × LeftPat 𝒫
frame-𝕀 (TF-app₁ {a} ≤ₐ appPar appLeft appRight x) with Arr.dir a
... | L = case (appLeft refl) of λ{ (() , _) }
... | R = sym (appRight refl .proj₁) , (inj₂ refl ∷ [])
... | 𝟙 = sym (appPar   refl .proj₁) , (inj₁ refl ∷ [])
frame-𝕀 (TF-app₂ {a} ≤ₐ appPar appLeft appRight x) with Arr.dir a
... | L = sym (appLeft refl .proj₂) , (inj₂ refl ∷ [])
... | R = case (appRight refl) of λ{ (_ , ()) }
... | 𝟙 = sym (appPar  refl .proj₂) , (inj₁ refl ∷ [])
frame-𝕀 (TF-□⊗ par seq⇒p x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-□⊗ seq seq⇒p x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-⊗□ par par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-⊗□ seq () x)
frame-𝕀 (TF-; uT x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`let par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`let seq x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`let⊗ par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`let⊗ seq x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`inj□ i) = refl , []
frame-𝕀 (TF-`case□ par x₁ x₂) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`case□ seq x₁ x₂) = refl , (inj₂ refl ∷ [])

-- The whole frame stack above an 𝕀 redex is LeftPat (and its top effect is 𝕀).
frames-𝕀 : ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E* : Frame* n} {U T ϵ} →
           Γ ; 𝒫 ⊢* E* ∶ U ∣ 𝕀 ⟶ T ∣ ϵ → (ϵ ≡ 𝕀) × LeftPat 𝒫
frames-𝕀 [] = refl , []
frames-𝕀 (E ∷⟨ U≃ , ϵ≤ ⟩ E*) with frames-𝕀 E*
... | refl , lp* with ϵ≤
...   | 𝕀≤𝕀 with frame-𝕀 E
...     | refl , lp = refl , ++⁺ lp lp*
