-- | mobile-front-msg-; (verdict A, at the BIND-CONTEXT level) — CALIBRATED.
--
--   The requested UNRESTRICTED statement
--       New s → BindCtx s BL Γ → (front slot 0 Mobile) → (any msg channel x) → ;
--   is machine-checked FALSE here (`refutes-unrestricted`, EXIT 0): exactly the
--   `ComSeparatedCex` phenomenon.  A New ν session `s = msg` admits, via a leading
--   `cons-acq` marker followed by a `cons-ret/acq` borrow, a MOBILE front handle
--   `acq;ret` (Bounded through the structural borrow-return `ret`, NOT through s)
--   with a genuinely LIVE `msg` channel in a LATER block.  So the flat
--   bind-context judgement does not, by itself, co-locate the com.
--
--   What IS true and provable (this module's exports): a Mobile front at slot 0
--   over a New ν session FORCES a leading `cons-acq` zero-block, i.e. a pending
--   (dropped, not-yet-reacquired) borrow — `mobile-front⇒lead0`.  Equivalently,
--   whenever the send block is a real handle block (nonzero leading width, no
--   leading `cons-acq` — which `FrontBlock.front-block-nonzero′` already yields
--   from a msg-typed front), the front is NOT Mobile: `mobile-front-;` /
--   `mobile-front-msg-;`.  The remaining separated com can therefore only sit
--   behind a pending-acq marker, which `R-Acq` (untyped mirror `RU-Acquire`)
--   resolves first — matching `ComBackwardFails`'s verdict A.
--
--   The proof needs no left-cancellation and no HasT: a New ambient is `NoAcq`
--   (CloseVacuityProbe), a NoAcq front is never Mobile (`¬mobile-noAcq`), and the
--   only slot-0 blocks over a New ν whose ambient is NOT acq-prefixed are the
--   `last` block (ambient `s`) and the `cons-ret/acq` block (ambient `s₁;ret`,
--   `s₁` a NoAcq factor of `s`).
module BorrowedCF.Simulation.Backward.ComMobileFront where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe
  using (NoAcq; new⇒noAcq; noAcq-;-fst; noAcq-≃; ¬mobile-noAcq)
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_)
open import Data.Fin.Properties using (toℕ-injective)

open Fin.Patterns

private variable
  ℓ : ℕ
  sν Aˢ : 𝕊 0
  BL B′ : BindGroup
  Γ : Ctx ℓ

------------------------------------------------------------------------
-- slot 0 = toℕ f ≡ 0 pins f to 0F (over a nonempty context).
------------------------------------------------------------------------

xto0 : ∀ {N} (f : 𝔽 (suc N)) → Fin.toℕ f ≡ 0 → f ≡ 0F
xto0 f tf = toℕ-injective tf

------------------------------------------------------------------------
-- The front of a single block whose ambient Aˢ is NoAcq is never Mobile.
------------------------------------------------------------------------

front-cons-; : NoAcq Aˢ → BindCtx′ Aˢ Γ → (f : 𝔽 ℓ) → Fin.toℕ f ≡ 0
  → Mobile (lookup Γ f) → ⊥
front-cons-; NA (nil _) ()
front-cons-; NA (cons t₁ t₂ ¬sk eq _) f tf mob rewrite xto0 f tf =
  ¬mobile-noAcq (noAcq-;-fst (noAcq-≃ (≃-sym eq) NA)) mob

------------------------------------------------------------------------
-- A Mobile front (slot 0) over a New ν session forces a leading cons-acq
-- zero-block (a pending, not-yet-reacquired borrow).
------------------------------------------------------------------------

mobile-front⇒lead0 : New sν → BindCtx sν BL Γ
  → (f : 𝔽 (sum BL)) → Fin.toℕ f ≡ 0 → Mobile (lookup Γ f)
  → ∃[ B″ ] BL ≡ 0 ∷ B″
mobile-front⇒lead0 N (last bc) f tf mob =
  ⊥-elim (front-cons-; (new⇒noAcq N) bc f tf mob)
mobile-front⇒lead0 N (cons-ret/acq s₁ s≃ (nil (_ ; ())) rest) f tf mob
mobile-front⇒lead0 N (cons-ret/acq s₁ s≃ (cons t₁ t₂ ¬sk eq _) rest) f tf mob rewrite xto0 f tf =
  ⊥-elim (¬mobile-noAcq
    (noAcq-;-fst (noAcq-≃ (≃-sym eq)
      (NoAcq._;_ (noAcq-;-fst (noAcq-≃ (≃-sym s≃) (new⇒noAcq N))) NoAcq.ret)))
    mob)
mobile-front⇒lead0 N (cons-acq rest) f tf mob = _ , refl

------------------------------------------------------------------------
-- Corollaries: with a real (nonzero-leading) send block, the front is
-- not Mobile — so any putative msg channel is irrelevant, the front
-- Mobile hypothesis alone is absurd.
------------------------------------------------------------------------

mobile-front-; : New sν → BindCtx sν BL Γ → (∀ B″ → ¬ (BL ≡ 0 ∷ B″))
  → (f : 𝔽 (sum BL)) → Fin.toℕ f ≡ 0 → Mobile (lookup Γ f) → ⊥
mobile-front-; N C ¬lead f tf mob with mobile-front⇒lead0 N C f tf mob
... | B″ , eq = ¬lead B″ eq

mobile-front-msg-; : New sν → BindCtx sν BL Γ → (∀ B″ → ¬ (BL ≡ 0 ∷ B″))
  → (f : 𝔽 (sum BL)) → Fin.toℕ f ≡ 0 → Mobile (lookup Γ f)
  → (x : 𝔽 (sum BL)) → ∀ {Tᵐ} → lookup Γ x ≃ ⟨ msg ‼ Tᵐ ⟩ → ⊥
mobile-front-msg-; N C ¬lead f tf mob x eq = mobile-front-; N C ¬lead f tf mob

------------------------------------------------------------------------
-- The unrestricted statement (no leading-block hypothesis) is FALSE.
-- A New ν session s = msg carries a MOBILE acq;ret front (slot 0) with a
-- LIVE msg channel behind it, in a later block.
------------------------------------------------------------------------

private
  s0 : 𝕊 0
  s0 = msg ‼ `⊤

  s0-New : New s0
  s0-New = P.msg

  bc-cont : BindCtx′ (acq ; s0) (⟨ acq ⟩ ∷ ⟨ s0 ⟩ ∷ [])
  bc-cont = cons acq s0 (λ { (() ; _) }) ≃-refl
              (cons s0 skip (λ ()) ≃-skipʳ (nil skip))

  cexBC : BindCtx s0 (0 ∷ 1 ∷ 2 ∷ []) (⟨ acq ; ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ s0 ⟩ ∷ [])
  cexBC = cons-acq
    (cons-ret/acq acq {s₂ = s0} ≃-refl
      (cons (acq ; ret) skip (λ { (() ; _) }) ≃-skipʳ (nil skip))
      (last bc-cont))

  Γcex : Ctx 3
  Γcex = ⟨ acq ; ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ s0 ⟩ ∷ []

  cex-front-Mobile : Mobile (lookup Γcex 0F)
  cex-front-Mobile = P.⟨ ret , P.ret , ≃-refl ⟩

  cex-msg-behind : lookup Γcex 2F ≃ ⟨ msg ‼ `⊤ ⟩
  cex-msg-behind = ≃-refl

refutes-unrestricted :
  ( ∀ {s : 𝕊 0} {BL} {Γ : Ctx (sum BL)}
    → New s → BindCtx s BL Γ
    → (f : 𝔽 (sum BL)) → Fin.toℕ f ≡ 0 → Mobile (lookup Γ f)
    → (x : 𝔽 (sum BL)) → ∀ {Tᵐ} → lookup Γ x ≃ ⟨ msg ‼ Tᵐ ⟩ → ⊥ )
  → ⊥
refutes-unrestricted lem =
  lem s0-New cexBC 0F refl cex-front-Mobile 2F {Tᵐ = `⊤} cex-msg-behind
