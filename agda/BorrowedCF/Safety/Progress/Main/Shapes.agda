-- Which binder-group shapes a typed restriction can have.
--
-- `Blocked` (Safety/Blocked.agda) has a rule for `ν (suc b ∷ B) (suc b ∷ B)`
-- (B-Nu), one for `ν (0 ∷ suc b ∷ B) B` (B-NuAcqˡ) and one for
-- `ν B (0 ∷ suc b ∷ B)` (B-NuAcqʳ).  Every other shape of a binder group is
-- untypable, and `groupShape` says so: a group is either `suc b ∷ B` or
-- `0 ∷ suc b ∷ B`.  The three refutations are
--
--   * `[]`            -- `bindCtx-B≢[]` (Processes/Typed.agda),
--   * `0 ∷ []`        -- `bindCtx-single-0` below (a lone group of width 0 would
--                      have to skip the trailing `end p` of the session),
--   * `0 ∷ 0 ∷ B`     -- `bindGroup-0∷0` below (`⊢ᴮ` forbids a zero after the head).
--
-- `no-unit-app` rules out the twelfth constant in the leaf case of the progress
-- induction: `K `unit` is never applied.
--
-- Owner: agent G3.
module BorrowedCF.Safety.Progress.Main.Shapes where

open import Data.Nat.ListAction using (sum)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴸ_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Typed
import BorrowedCF.Context.Equivalence as 𝐄

open import BorrowedCF.Safety.Progress.Expr using (inv-app-fn/arg)

open Nat.Variables

--------------------------------------------------------------------------------
-- `K `unit` is never the function of an application.

no-unit-app : ∀ {n} {Γ : Ctx n} {γ : Struct n} {d} {w : Tm n} {T ϵ} →
  Γ ; γ ⊢ K `unit ·⟨ d ⟩ w ∶ T ∣ ϵ → ⊥
no-unit-app p
  with _ , _ , _ , _ , _ , _ , ⊢c , _ ← inv-app-fn/arg p
  with _ , eq , _ , `unit ← inv-K ⊢c = case eq of λ ()

--------------------------------------------------------------------------------
-- The two untypable group shapes.

private
  ¬skips-end : ∀ {s : 𝕊 0} {p : Pol} → ¬ Skips (s ; end p)
  ¬skips-end (_ ; ())

bindCtx-single-0 : ∀ {s : 𝕊 0} {p : Pol} {Γ : Ctx 0} →
  ¬ BindCtx (s ; end p) (0 ∷ []) Γ
bindCtx-single-0 (last (nil sk))             = ¬skips-end sk
bindCtx-single-0 (cons-ret/acq _ _ _ _ C _)  = bindCtx-B≢[] C
bindCtx-single-0 (cons-acq C _)              = bindCtx-B≢[] C

bindGroup-0∷0 : ∀ {B : BindGroup} → ¬ (⊢ᴮ (0 ∷ 0 ∷ B))
bindGroup-0∷0 (nz ∷ᴸ _) = case Nat.>-nonZero⁻¹ 0 ⦃ nz ⦄ of λ ()

--------------------------------------------------------------------------------
-- The classification.

data GroupShape : BindGroup → Set where
  head-full : ∀ b B → GroupShape (suc b ∷ B)
  head-sep  : ∀ b B → GroupShape (0 ∷ suc b ∷ B)

groupShape : ∀ {s : 𝕊 0} {p : Pol} (B : BindGroup) {Γ : Ctx (sum B)} →
  ⊢ᴮ B → BindCtx (s ; end p) B Γ → GroupShape B
groupShape []                 ⊢B C = ⊥-elim (bindCtx-B≢[] C)
groupShape (suc b ∷ B)        ⊢B C = head-full b B
groupShape (0 ∷ [])           ⊢B C = ⊥-elim (bindCtx-single-0 C)
groupShape (0 ∷ suc b ∷ B)    ⊢B C = head-sep b B
groupShape (0 ∷ zero ∷ B)     ⊢B C = ⊥-elim (bindGroup-0∷0 ⊢B)

--------------------------------------------------------------------------------
-- A closed process is typed under the empty structure.
--
-- `Struct 0` has no variables, so every closed structure collapses to `[]`.
-- The redex lemmas of `Safety/Progress/Redex.agda` all ask for `[] ; []`, and
-- this is what lets the theorem be stated for an arbitrary `γ : Struct 0`.

closed-struct : (γ : Struct 0) → ((V.[] {A = 𝕋}) ∶ γ ≈ [])
closed-struct (` ())
closed-struct []      = ≈-refl
closed-struct (α ∥ β) = ≈-trans (𝐄.∥-cong (closed-struct α) (closed-struct β)) ∥-unit₁
closed-struct (α ; β) = ≈-trans (;-cong (closed-struct α) (closed-struct β)) ;-unit₁

close-γ : ∀ {γ : Struct 0} {P : Proc 0} → [] ; γ ⊢ₚ P → [] ; [] ⊢ₚ P
close-γ {γ = γ} ⊢P = TP-Weaken (≼-refl (closed-struct γ)) ⊢P
