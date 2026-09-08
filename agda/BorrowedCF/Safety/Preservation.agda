-- Process preservation for the declarative typing of
-- "Context-Free Session Types with Borrowing".
--
--   preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q
--
-- The per-rule lemmas live in `Preservation.Basic` (R-Exp, R-New, R-Fork),
-- `Preservation.Handles` (R-Close, R-Discard, R-Drop, R-Acq),
-- `Preservation.Com` / `Preservation.Choice` (agent P2) and
-- `Preservation.LSplit` / `Preservation.RSplit` (agent P3).  R-Par, R-Bind and
-- R-Struct are handled here: the first two by induction, the third by
-- `Processes.Congruence._/_⊢-≋_`.
module BorrowedCF.Safety.Preservation where

open import Data.Vec.Relation.Unary.All as Allⱽ using ([]; _∷_)
open import Data.Nat.ListAction using (sum)

import Data.Vec.Relation.Unary.All.Properties as Allⱽ

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Processes.Congruence
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Reduction.Processes.Typed hiding (preservationₚ)
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Basic
open import BorrowedCF.Safety.Preservation.Handles
open import BorrowedCF.Safety.Preservation.Com using (pres-Com)
open import BorrowedCF.Safety.Preservation.Choice using (pres-Choice)
open import BorrowedCF.Safety.Preservation.RSplit using (pres-RSplit)
open import BorrowedCF.Safety.Preservation.LSplit.Total using (pres-LSplit)

open Variables
open Fin.Patterns

preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q
preservationₚ Γ-S ⊢P (R-Exp x)        = pres-Exp  Γ-S x ⊢P
preservationₚ Γ-S ⊢P (R-New E)        = pres-New  Γ-S E ⊢P
preservationₚ Γ-S ⊢P (R-Fork E V)     = pres-Fork Γ-S E V ⊢P
preservationₚ Γ-S ⊢P (R-Close {E₁ = E₁} {E₂ = E₂}) = pres-Close Γ-S {E₁ = E₁} {E₂ = E₂} ⊢P
preservationₚ Γ-S ⊢P (R-Discard {P = P₀} {E = E}) = pres-Discard Γ-S {E = E} {P = P₀} ⊢P
preservationₚ Γ-S ⊢P (R-Drop {P = P₀} {E = E}) = pres-Drop Γ-S {E = E} {P = P₀} ⊢P
preservationₚ Γ-S ⊢P (R-Acq {P = P₀} {E = E}) = pres-Acq Γ-S {E = E} {P = P₀} ⊢P
preservationₚ Γ-S ⊢P (R-Com {P = P₀} {E₁ = E₁} {E₂ = E₂} V) = pres-Com {E₁ = E₁} {E₂ = E₂} {P = P₀} Γ-S V ⊢P
preservationₚ Γ-S ⊢P (R-Choice E₁ E₂ i) = pres-Choice Γ-S E₁ E₂ i ⊢P
preservationₚ Γ-S ⊢P (R-LSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {P = P₀} {E = E}) =
  pres-LSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P₀} Γ-S ⊢P
preservationₚ Γ-S ⊢P (R-RSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {P = P₀} {E = E}) =
  pres-RSplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P₀} Γ-S ⊢P
preservationₚ Γ-S ⊢P (R-Par x)
  with _ , _ , ≤γ , ⊢P₁ , ⊢Q ← inv-∥ ⊢P
  = TP-Weaken ≤γ (TP-Par (preservationₚ Γ-S ⊢P₁ x) ⊢Q)
preservationₚ Γ-S ⊢P (R-Bind x)
  with _ , _ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢P′ ← inv-ν ⊢P
  = TP-Res N pol ⊢B₁ ⊢B₂ C C′
      (preservationₚ (Allⱽ.++⁺ (Allⱽ.++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) ⊢P′ x)
preservationₚ Γ-S ⊢P (R-Struct eq₁ x eq₂) =
  Γ-S / preservationₚ Γ-S (Γ-S / ⊢P ⊢-≋ eq₁) x ⊢-≋ eq₂
