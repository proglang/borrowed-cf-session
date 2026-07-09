-- | drop-goB : shape-dispatch for the reverse RU-Drop reflection (?1 context,
--   syncs B1>=1 so B1 = b :: c :: Bp).  Narrows to the good phi-drop shape
--   B1 = suc b1 :: c :: [], B2 = b2 :: [] and delegates to drop-goB-good.
module BorrowedCF.Simulation2.Backward.DropReflectGo where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
open import BorrowedCF.Simulation.RevAdmin using (_≈_)
open import BorrowedCF.Simulation2.Backward.Drop using (νσᵈ)
open import BorrowedCF.Simulation2.Backward.DropReflect using (drop-goB-good)
open import BorrowedCF.Reduction.Base using (ChanCx; Frame*; _[_]*)
open import BorrowedCF.Context using (Ctx; Struct)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (proj₁; proj₂; _,_; Σ-syntax; _×_)
open import Data.List using (_∷_; [])
open TP using (BindGroup; _;_⊢ₚ_)

open Fin.Patterns
pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

private
  φ-inj : ∀ {k} {f g : UP.Flag} {X Y : UP.Proc (suc k)} → UP.φ f X ≡ UP.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-inj refl = refl , refl
  ν-injU : ∀ {k} {X Y : UP.Proc (2 + k)} → UP.ν X ≡ UP.ν Y → X ≡ Y
  ν-injU refl = refl

drop-goB :
  ∀ {m n} (b c : ℕ) (Bp B₂ : BindGroup) (σ : m →ₛ n) (Vσ : VSub σ)
    {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (P₀ : TP.Proc (sum (b ∷ c ∷ Bp) + sum B₂ + m))
    (F : Frame* (3 + n)) {x : 𝔽 (2 + n)} {P₁ : UP.Proc (3 + n)}
  → Γ ; g ⊢ₚ TP.ν (b ∷ c ∷ Bp) B₂ P₀
  → UP.ν (UP.φ UP.drop (UP.⟪ F [ K `drop ·¹ 𝓒[ * × Fin.suc x × ` 0F ] ]* ⟫ UP.∥ P₁))
      ≡ U[ TP.ν (b ∷ c ∷ Bp) B₂ P₀ ] σ
  → Σ[ P′ ∈ TP.Proc m ]
      Star TR._─→ₚ_ (TP.ν (b ∷ c ∷ Bp) B₂ P₀) P′
      × (UP.ν (UP.φ UP.acq (UP.⟪ F [ * ]* ⟫ UP.∥ P₁)) ≈ U[ P′ ] σ)
drop-goB zero c Bp B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₁ (φ-inj (ν-injU bodyeq))
drop-goB (suc b₁) c (d ∷ Bp) B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
drop-goB (suc b₁) c [] [] σ Vσ Γ-S P₀ F ⊢P bodyeq
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
drop-goB (suc b₁) c [] (suc b₂h ∷ e ∷ B₂t) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
drop-goB (suc b₁) c [] (zero ∷ e ∷ B₂t) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
drop-goB (suc b₁) c [] (b₂ ∷ []) σ Vσ Γ-S P₀ F ⊢P bodyeq =
  drop-goB-good b₁ c b₂ σ Vσ (νσᵈ b₁ c b₂ σ) refl Γ-S P₀ F ⊢P bodyeq
