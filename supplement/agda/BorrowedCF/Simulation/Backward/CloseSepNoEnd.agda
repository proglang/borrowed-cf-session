-- | NoEnd bind-context lookups: the `end`-leaf twin of ChoiceSepNoBrn.  Reuses
--   CloseVacuityProbe.NoEnd and its ≃-respect lemmas, adding the small
--   ;-projections and the per-channel BindCtx lookup routing.
module BorrowedCF.Simulation.Backward.CloseSepNoEnd where

open import Data.Nat.ListAction using (sum)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec.Properties using (lookup-splitAt)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Context using (Ctx; _﹫_)
open import BorrowedCF.Reduction.Base using (ChanCx; chanCx-lookup)
open import BorrowedCF.Processes.Typed
  using (BindCtx; BindCtx′; nil; cons; last; cons-ret/acq; cons-acq
        ; bindCtx⇒chanCtx; bindCtx′⇒chanCtx)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe
  using (NoEnd; ¬noEnd-end; noEnd-≃)
open BorrowedCF.Simulation.Support.CloseVacuityProbe.NoEnd

open Fin.Patterns
open Nat.Variables

noEnd-;-fst : ∀ {n} {s₁ s₂ : 𝕊 n} → NoEnd (s₁ ; s₂) → NoEnd s₁
noEnd-;-fst (x ; _) = x

noEnd-;-snd : ∀ {n} {s₁ s₂ : 𝕊 n} → NoEnd (s₁ ; s₂) → NoEnd s₂
noEnd-;-snd (_ ; y) = y

noEnd-acq : ∀ {n} → NoEnd (acq {n})
noEnd-acq = NoEnd.acq

bindCtx′-lookup-NoEnd : ∀ {w} {Γ : Ctx w} {s} → BindCtx′ s Γ → NoEnd s
                      → (i : 𝔽 w) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoEnd s′)
bindCtx′-lookup-NoEnd (cons s₁ s₂ ¬sk s≃ b) NEs 0F =
  s₁ , refl , noEnd-;-fst (noEnd-≃ (≃-sym s≃) NEs)
bindCtx′-lookup-NoEnd (cons s₁ s₂ ¬sk s≃ b) NEs (suc i) =
  bindCtx′-lookup-NoEnd b (noEnd-;-snd (noEnd-≃ (≃-sym s≃) NEs)) i

bindCtx-lookup-NoEnd : ∀ {BG} {Γ : Ctx (sum BG)} {s} → BindCtx s BG Γ → NoEnd s
                     → (i : 𝔽 (sum BG)) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoEnd s′)
bindCtx-lookup-NoEnd (last x) NEs i = bindCtx′-lookup-NoEnd x NEs i
bindCtx-lookup-NoEnd {BG = n ∷ B} (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ x C) NEs i
  with Fin.splitAt n i in eq
... | inj₁ j =
  let s′ , ej , NE = bindCtx′-lookup-NoEnd x (noEnd-;-fst (noEnd-≃ (≃-sym s≃) NEs) ; NoEnd.ret) j
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ej) , NE
... | inj₂ k =
  let s′ , ek , NE = bindCtx-lookup-NoEnd C (NoEnd.acq ; noEnd-;-snd (noEnd-≃ (≃-sym s≃) NEs)) k
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ek) , NE
bindCtx-lookup-NoEnd (cons-acq C) NEs i =
  bindCtx-lookup-NoEnd C (NoEnd.acq ; NEs) i

⟨⟩-inj : {s₁ s₂ : 𝕊 0} → _≡_ {A = 𝕋} ⟨ s₁ ⟩ ⟨ s₂ ⟩ → s₁ ≡ s₂
⟨⟩-inj refl = refl

bindCtx-noEnd-not-end : ∀ {s BG} {Γ : Ctx (sum BG)} {i} {q} → BindCtx s BG Γ → NoEnd s
                      → (Γ ﹫ i) ≃ ⟨ end q ⟩ → ⊥
bindCtx-noEnd-not-end {i = i} {q = q} C NEs eqe
  with bindCtx-lookup-NoEnd C NEs i
... | s′ , e1 , NE =
  ¬noEnd-end (noEnd-≃ (≃-⟨⟩⁻¹ (subst (_≃ ⟨ end q ⟩) e1 eqe)) NE)
