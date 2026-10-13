------------------------------------------------------------------------
-- P3c, step 4: `pres-LSplit` WITHOUT any side condition.
--
-- The two routes are dispatched on the rule's own indices, which is what
-- makes the premise-free statement possible: `Mobile` is not decidable
-- (`Types/Predicates.agda:183` quantifies over sessions modulo `≃`), so the
-- proof never decides it.
--
--   * `q = suc _`   the handle is INTERIOR to its group, hence immobile
--                   (`Shape.handle-interior-¬mobile`), so P3b's transport
--                   along `θL` applies (`Immobile.pres-LSplit-shape`).
--   * `q = 0`, `b₁ = suc _`
--                   the handle is the head of a group of width `≥ 2`, hence
--                   immobile (`Shape.handle-wide-¬mobile`); same route.
--   * `q = 0`, `b₁ = 0`
--                   the group has width one; `Mobile/pres-LSplit-mobile`
--                   erases the handle with `zapL` and needs no mobility
--                   fact whatsoever.
--
-- Matching `q` and `b₁` syntactically keeps every `subst` off the process:
-- in the third clause `q + suc b₁` IS `1` and `q + suc (suc b₁)` IS `2`.
--
-- Consequence for `Splits-STATUS.md`'s "IMPORTANT FINDING": R-LSplit does
-- lose `Mobile` at the split, but the configuration in which that matters
-- -- a mobile handle sharing its group with a second handle -- is not
-- typable, so preservation holds unconditionally.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit.Total where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Terms
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.LSplit.Immobile using (pres-LSplit-shape)
open import BorrowedCF.Safety.Preservation.LSplit.Mobile using (pres-LSplit-mobile)
open import BorrowedCF.Safety.Preservation.LSplit.Shape
  using (handle-interior-¬mobile; handle-wide-¬mobile)

open Nat.Variables
open Fin.Patterns

pres-LSplit : ∀ {m} {Γ : Ctx m} {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  ChanCx Γ →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (⟪ E [ K (`lsplit s) ·¹
                    (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
             (⟪ (E ⋯ᶠ* SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m})
                  [ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 0F))
                  ⊗ (` SplitRenamings.atk B₁ B₂ (sum B) {q + suc (suc b₁)} {m} (q ↑ʳ 1F)) ]* ⟫
               ∥ (P ⋯ₚ SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m}))
pres-LSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = suc q} {b₁ = b₁} {s = s} {E = E} {P = P}
  Γ-S ⊢P =
  pres-LSplit-shape {B₁ = B₁} {B₂ = B₂} {B = B} {q = suc q} {b₁ = b₁} {s = s} {E = E} {P = P}
    Γ-S (λ N ⊢B C → handle-interior-¬mobile B₁ Nat.z<s N ⊢B C) ⊢P
pres-LSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = zero} {b₁ = suc b₁} {s = s} {E = E} {P = P}
  Γ-S ⊢P =
  pres-LSplit-shape {B₁ = B₁} {B₂ = B₂} {B = B} {q = zero} {b₁ = suc b₁} {s = s} {E = E} {P = P}
    Γ-S (λ N ⊢B C → handle-wide-¬mobile B₁ N C) ⊢P
pres-LSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = zero} {b₁ = zero} {s = s} {E = E} {P = P}
  Γ-S ⊢P =
  pres-LSplit-mobile {B₁ = B₁} {B₂ = B₂} {B = B} {s = s} {E = E} {P = P} Γ-S ⊢P
