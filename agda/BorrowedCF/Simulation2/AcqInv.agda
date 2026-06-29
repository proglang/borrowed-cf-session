-- Inversion helpers for the R-Acq redex, mirroring InvFrame's lsplit/rsplit ones.
-- acq's domain is the session  acq ; s  (no ¬Skips premise — Skips has no acq case),
-- so the consumed handle is non-Unr directly.

module BorrowedCF.Simulation2.AcqInv where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (𝕊; Unr; Arr; _≃_; ≃-refl; ≃-sym; ≃-trans; unr-≃; _`→_; ⟨_⟩; _;_; _⟨_⟩→_; acq)
open import BorrowedCF.Context.Base using (Struct; Ctx)
open import BorrowedCF.Simulation2.HandleLinear using (¬Skips⇒¬Unr-seq)
open import BorrowedCF.Simulation2.InvFrame using (arg-type)

open Nat.Variables
open Fin.Patterns

fn-acq-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {T U a ϵ}
  → Γ ; β ⊢ K `acq ∶ T ⟨ a ⟩→ U ∣ ϵ → Σ[ s′ ∈ 𝕊 0 ] (⟨ acq ; s′ ⟩ ≃ T)
fn-acq-dom (T-Const (`acq {s = s′})) = s′ , ≃-refl
fn-acq-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let s′ , eq = fn-acq-dom d in s′ , ≃-trans eq dom≃
fn-acq-dom (T-Weaken _ d) = fn-acq-dom d

acq-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K `acq · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
acq-app-nonUnr d = go d
  where
    go : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {T ϵ}
       → Γ ; β ⊢ K `acq · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
    go (T-AppUnr _ _ ⊢fn ⊢arg) u =
      let s′ , eq = fn-acq-dom ⊢fn
      in ¬Skips⇒¬Unr-seq (λ ()) (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLin _ _ ⊢fn ⊢arg) u =
      let s′ , eq = fn-acq-dom ⊢fn
      in ¬Skips⇒¬Unr-seq (λ ()) (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLeft _ _ ⊢fn ⊢arg) u =
      let s′ , eq = fn-acq-dom ⊢fn
      in ¬Skips⇒¬Unr-seq (λ ()) (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppRight _ _ ⊢fn ⊢arg) u =
      let s′ , eq = fn-acq-dom ⊢fn
      in ¬Skips⇒¬Unr-seq (λ ()) (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-Conv _ _ d) u = go d u
    go (T-Weaken _ d) u = go d u
