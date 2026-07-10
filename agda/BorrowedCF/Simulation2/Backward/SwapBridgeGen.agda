-- Test whether ν-swap′'s strict image bridge (SymmBridgeProbe Finding A) holds
-- on a NON-DEGENERATE instance (B₂ ≠ []), where a real φ-telescope transpose is
-- needed.  If `test = refl` typechecks, the strict bridge generalises past the
-- degenerate B₂ = [] instance; if not, NonEpsRoadblock's multi-link bridge stands.
module BorrowedCF.Simulation2.Backward.SwapBridgeGen where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Nat using (_+_)
open import Data.Nat.ListAction using (sum)
open import Data.List using (_∷_; [])
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open Fin.Patterns

-- Asymmetric concrete instance: B₁ has 2 blocks, B₂ has 1 (different telescopes).
module _ where
  B₁ B₂ : TP.BindGroup
  B₁ = 1 ∷ 1 ∷ []
  B₂ = 1 ∷ []

  P₀ : TP.Proc (sum B₁ + sum B₂ + 0)
  P₀ = TP.⟪ ` 0F ⟫

  σ₀ : 0 →ₛ 0
  σ₀ ()

  image : UP.Proc 0
  image = U[ TP.ν B₁ B₂ P₀ ] σ₀

  swapNbr : Σ[ S ∈ UP.Proc 0 ] (image UP.≋ S)
  swapNbr = _ , Eq*.return UP.ν-swap′

  Simg : UP.Proc 0
  Simg = proj₁ swapNbr

  P̃ : TP.Proc 0
  P̃ = TP.ν B₂ B₁ (P₀ TP.⋯ₚ swapᵣ (sum B₁) (sum B₂))

  test : Simg ≡ U[ P̃ ] σ₀
  test = refl

-- Another asymmetric instance: B₁ = 2 ∷ [], B₂ = 1 ∷ 1 ∷ [].
module _ where
  C₁ C₂ : TP.BindGroup
  C₁ = 2 ∷ []
  C₂ = 1 ∷ 1 ∷ []

  Q₀ : TP.Proc (sum C₁ + sum C₂ + 0)
  Q₀ = TP.⟪ ` 0F ⟫

  τ : 0 →ₛ 0
  τ ()

  Simg₂ : UP.Proc 0
  Simg₂ = proj₁ (_,_ {A = UP.Proc 0} {B = λ S → U[ TP.ν C₁ C₂ Q₀ ] τ UP.≋ S}
                     _ (Eq*.return UP.ν-swap′))

  test2 : Simg₂ ≡ U[ TP.ν C₂ C₁ (Q₀ TP.⋯ₚ swapᵣ (sum C₁) (sum C₂)) ] τ
  test2 = refl
