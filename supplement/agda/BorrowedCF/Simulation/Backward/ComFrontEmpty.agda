-- | ComFrontEmpty: in a well-typed com redex whose front handle (position 0F,
--   here abstracted as `x` with `toℕ x ≡ 0`) is `msg`-typed, the send's leading
--   width-0 bind-block cannot exist.
--
--   A leading width-0 block is a `cons-acq` marker exposing `BindCtx (acq ; s) B Γ`,
--   whose front leaf is acq-headed; the msg send at 0F clashes with acq via
--   `FrontBlock.front-acq-⊥` (leading atom-kind rigidity, `AtomHead.msg;≄acq;`).
--   Hence a com redex's send block-prefix `B₁ˢ` (with `sum B₁ˢ ≡ 0`) is empty.
--
--   NB: the front position is threaded as `(x : 𝔽 (sum …))` with `toℕ x ≡ 0`
--   rather than the literal `0F`, because over a neutral `sum B` the term `0F`
--   cannot be elaborated (`𝔽 (sum B)` does not reduce to `𝔽 (suc _)`); this is
--   exactly the idiom used by `FrontBlock.front-acq-⊥` / `front-block-nonzero`.
module BorrowedCF.Simulation.Backward.ComFrontEmpty where

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Simulation.Backward.FrontBlock using (front-acq-⊥)
import BorrowedCF.Processes.Typed as TP
open TP using (BindGroup; BindCtx; cons-acq; cons-ret/acq; nil)
open import BorrowedCF.Types.Syntax using (𝕊; msg; ‼; 𝕋)
open import BorrowedCF.Types.Equivalence using (_≃_)
open import BorrowedCF.Simulation.Support.Confine using (+≡0)
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_)

open Fin.Patterns

private variable
  Tᵐ : 𝕋

-- Lemma 1 (crux): a leading width-0 bind-block (`cons-acq`) makes the front
-- channel acq-headed, contradicting a msg-typed front handle.
consacq-front-msg-⊥ : ∀ {s : 𝕊 0} {B : BindGroup} {Γ : Ctx (sum B)} (x : 𝔽 (sum B))
  → BindCtx s (0 ∷ B) Γ → Fin.toℕ x ≡ 0
  → lookup Γ x ≃ ⟨ msg ‼ Tᵐ ⟩ → ⊥
consacq-front-msg-⊥ x (cons-acq C) tx lk = front-acq-⊥ _ x C tx lk
consacq-front-msg-⊥ x (cons-ret/acq s₁ s≃ (nil (_ ; ())) restC) tx lk

-- Lemma 2 (derived): a com redex send prefix `B₁ˢ` with `sum B₁ˢ ≡ 0` and a
-- msg-typed front handle must be empty.
send-block-empty : ∀ {s : 𝕊 0} {BL : BindGroup} {Γ : Ctx (sum BL)}
  → BindCtx s BL Γ → (B₁ˢ B₂ˢ : BindGroup) (qˢ b₁ˢ : ℕ)
  → BL ≡ B₁ˢ ++ (qˢ + suc b₁ˢ) ∷ B₂ˢ → sum B₁ˢ ≡ 0
  → (x : 𝔽 (sum BL)) → Fin.toℕ x ≡ 0
  → lookup Γ x ≃ ⟨ msg ‼ Tᵐ ⟩
  → B₁ˢ ≡ []
send-block-empty C [] B₂ˢ qˢ b₁ˢ BL≡ sum0 x tx lk = refl
send-block-empty C (c ∷ B₁ˢ') B₂ˢ qˢ b₁ˢ BL≡ sum0 x tx lk
  rewrite BL≡ with +≡0 {c} sum0
... | c≡0 , _ rewrite c≡0 = ⊥-elim (consacq-front-msg-⊥ x C tx lk)
