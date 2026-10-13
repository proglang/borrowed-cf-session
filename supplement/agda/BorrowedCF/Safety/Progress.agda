-- | Process progress (paper Theorem "Process progress").
--
--     progressₚ : [] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ ∃[ P′ ] P ─→ₚ P′
--
--   for a CLOSED process `P : Proc 0`.  (The theorem fails for open processes:
--   `x ∶ ⟨ ret ⟩ ⊢ₚ ⟪ drop x ⟫` neither reduces nor is `Blocked`, because
--   R-Drop needs the binder that gave `x` its session.)
--
--   Everything happens in `Safety/Progress/Main.agda`, which is parametrised
--   over the redex lemmas of `Safety/Progress/Redex.agda` (agent G1) and
--   `Safety/Progress/Sync.agda` (agent G2).  This module supplies them, so the
--   whole proof is free of postulates and of unproved assumptions.
--
--   Owner: agent G3.
module BorrowedCF.Safety.Progress where

open import Data.Nat.ListAction using (sum)
open import Data.Fin.Patterns using (0F)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base hiding (Blocked)
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_)

open import BorrowedCF.Simulation.BackwardSoup.Locate using (ProcessContext; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position using (weakenThrough)

open import BorrowedCF.Safety.Blocked

open import Data.Vec.Relation.Unary.All using () renaming ([] to []ᴬ)

import BorrowedCF.Safety.Progress.Redex as G1
import BorrowedCF.Safety.Progress.Sync  as G2
import BorrowedCF.Safety.Progress.Main  as Generic

open Nat.Variables

--------------------------------------------------------------------------------
-- The instances of the twelve module parameters, each with the type
-- `Safety/Progress/Main.agda` declares.  Naming them here rather than passing
-- them inline keeps a signature mismatch local to one line.  Only the two G2
-- lemmas need adapting: `plug-typing` is stated for an arbitrary context (here
-- the empty one, whose `ChanCx` is `[]ᴬ`) and `sync-redex` keeps its body
-- implicit.

private
  plug-typing :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (Q : Proc k) →
    [] ; [] ⊢ₚ plug ctx Q →
    Σ[ Δ ∈ Ctx k ] Σ[ σ ∈ Struct k ] ChanCx Δ × (Δ ; σ ⊢ₚ Q)
  plug-typing ctx Q ⊢P = G2.plug-typing ctx Q []ᴬ ⊢P

  sync-redex :
    ∀ {k b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
      (ctx : ProcessContext k 0)
      (Q : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
    [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) →
    0F ∈BC Q →
    head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC Q →
    Σ[ P′ ∈ Proc 0 ] (plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) ─→ₚ P′)
  sync-redex ctx Q ⊢P mem₁ mem₂ = G2.sync-redex ctx ⊢P mem₁ mem₂

  step-in-ctx :
    ∀ {k n : ℕ} {e e′ : Tm k} (ctx : ProcessContext k n) →
    e ⋯→ e′ → plug ctx ⟪ e ⟫ ─→ₚ plug ctx ⟪ e′ ⟫
  step-in-ctx = G1.step-in-ctx

  ∈AC⇒located-acq :
    ∀ {n : ℕ} {P : Proc n} {x : 𝔽 n} → x ∈AC P →
    Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ E ∈ Frame* k ] Σ[ d ∈ Dir ]
      P ≡ plug ctx ⟪ E [ K `acq ·⟨ d ⟩ (` weakenThrough ctx x) ]* ⟫
  ∈AC⇒located-acq = G1.∈AC⇒located-acq

  redex-new :
    ∀ {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) (s : 𝕊 0) →
    Σ[ P′ ∈ Proc n ] (plug ctx ⟪ E [ K (`new s) ·¹ * ]* ⟫ ─→ₚ P′)
  redex-new = G1.redex-new

  redex-fork :
    ∀ {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) {e : Tm k} → Value e →
    Σ[ P′ ∈ Proc n ] (plug ctx ⟪ E [ K `fork ·¹ e ]* ⟫ ─→ₚ P′)
  redex-fork = G1.redex-fork

  redex-lsplit :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K (`lsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′)
  redex-lsplit = G1.redex-lsplit

  redex-rsplit :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K (`rsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′)
  redex-rsplit = G1.redex-rsplit

  redex-drop :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
    [] ; [] ⊢ₚ plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ ─→ₚ P′)
  redex-drop = G1.redex-drop

  redex-discard :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
    [] ; [] ⊢ₚ plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ ─→ₚ P′)
  redex-discard = G1.redex-discard

  redex-acq-exposedˡ :
    ∀ {m k b : ℕ} {B₁ B₂ : BindGroup}
      (ctx₀ : ProcessContext m 0)
      (ctx₁ : ProcessContext k (sum (0 ∷ suc b ∷ B₁) + sum B₂ + m))
      (E : Frame* k) →
    Σ[ P′ ∈ Proc 0 ]
      (plug ctx₀ (ν (0 ∷ suc b ∷ B₁) B₂
         (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ 0F) ]* ⟫)) ─→ₚ P′)
  redex-acq-exposedˡ = G1.redex-acq-exposedˡ

  redex-acq-exposedʳ :
    ∀ {m k b : ℕ} {B₁ B₂ : BindGroup}
      (ctx₀ : ProcessContext m 0)
      (ctx₁ : ProcessContext k (sum B₁ + sum (0 ∷ suc b ∷ B₂) + m))
      (E : Frame* k) →
    Σ[ P′ ∈ Proc 0 ]
      (plug ctx₀ (ν B₁ (0 ∷ suc b ∷ B₂)
         (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ (head₂ B₁ b B₂)) ]* ⟫))
         ─→ₚ P′)
  redex-acq-exposedʳ = G1.redex-acq-exposedʳ

--------------------------------------------------------------------------------

module Inst = Generic
  plug-typing sync-redex
  step-in-ctx ∈AC⇒located-acq
  redex-new redex-fork redex-lsplit redex-rsplit redex-drop redex-discard
  redex-acq-exposedˡ redex-acq-exposedʳ

open Inst public using (go)

-- The paper's statement.
progressₚ : {γ : Struct 0} {P : Proc 0} →
  [] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)
progressₚ = Inst.progressₚ

-- The sharpened statement: `Blocked⁺` demands that EVERY separator-led side of
-- a restriction has its head outside AC(P), which `Blocked` does not.
progress⁺ₚ : {γ : Struct 0} {P : Proc 0} →
  [] ; γ ⊢ₚ P → Blocked⁺ P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)
progress⁺ₚ = Inst.progress⁺ₚ
