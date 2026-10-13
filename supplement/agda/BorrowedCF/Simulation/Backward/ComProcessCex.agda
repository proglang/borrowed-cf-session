-- | DECISIVE PROCESS-LEVEL settlement of the multi-block backward-com question.
--   VERDICT (A): backward-com holds (via an admin-prefixed R-Acq reflection);
--   the separated firing com is NOT realized by a STUCK well-typed process.
--
--   THE OPEN QUESTION (from `ComMobileFront.refutes-unrestricted`).  The
--   BIND-CONTEXT statement "a Mobile front + a live msg channel behind it" is
--   machine-checked INHABITED.  Does a full WELL-TYPED PROCESS `Γ;g ⊢ₚ ν B₁ B₂ P`
--   realize the corresponding backward-com zero-branch — a STUCK com where
--   R-Com cannot fire (send behind the marker) and R-Acq cannot fire (no acq
--   thread)?  If yes ⟹ backward-com FALSE (verdict B).  If no ⟹ com closes (A).
--
--   THE PROCESS-LEVEL CONSTRAINT the bind-context level lacks.  A well-typed ν's
--   send-side bind group must satisfy `⊢ᴮ B₁` (`TP-Res`): every block AFTER the
--   first is NonZero.  Combined with the type-level fact that a Mobile front over
--   a New-capped ν ambient `s ; end p` FORCES a leading `cons-acq` zero-marker
--   (`ComMobileFront.mobile-front⇒lead0`), this pins the bind group to
--
--        B₁ ≡ 0 ∷ suc b₁ ∷ B′        (`mobile-front⇒RAcq-shape`, below)
--
--   which is EXACTLY the redex shape of `R-Acq`
--   (Reduction/Processes/Typed.agda: `ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪E[acq·0F]⟫ ∥ P)`).
--   Moreover the front channel (slot 0F) is `acq`-headed (`mobile⇒acq-head`:
--   Mobile ⟨s⟩ ⇒ s ≃ acq ; w), so `K acq · (` 0F)` is a well-typed elimination —
--   the R-Acq redex — and this pending borrow is a GENUINE acquire, not something
--   the com can delegate around: `¬mobile-acq : ¬ Mobile ⟨ acq ⟩` (a bare `acq`
--   borrow is not `send`-able, `Mobile T` failing on it).
--
--   Hence a Mobile-front separated com is not a stuck com: its ν is R-Acq-shaped,
--   the pending-acq marker resolves first by `R-Acq` (untyped mirror `RU-Acquire`,
--   whose flag `ϕ[ 0 ] ≡ acq` is acquire-ready — cf. `FrontCex`), and only then
--   does `R-Com` fire.  Backward-com holds by the admin-prefixed reflection; no
--   forward-reachability restriction and no calculus/statement redesign is forced
--   on THIS ground.  This is the process-level counterpart of `ComBackwardFails`'s
--   within-a-block verdict A and matches `ComMobileFront`'s bind-context calibration.
module BorrowedCF.Simulation.Backward.ComProcessCex where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; ⊢ᴮ_; last; cons; cons-acq; cons-ret/acq; nil)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe using (new-end⇒noAcq)
open import BorrowedCF.Simulation.Backward.ComMobileFront using (mobile-front⇒lead0)
open import BorrowedCF.Types.ContainsEnd using (HasT; seqʳ; bounded⇒hasT; ≃-hasT)
open import Data.Nat.ListAction using (sum)
open import Data.Nat using (NonZero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)

open Fin.Patterns

private variable
  ℓ : ℕ
  sˣ wˣ : 𝕊 0
  polˣ : Pol
  Bˣ : BindGroup
  Γˣ : Ctx ℓ

------------------------------------------------------------------------
-- The pending borrow is a GENUINE acquire: a bare `acq` channel is NOT
-- Mobile, hence not `send`-able — the com cannot delegate it away, it must
-- be `acq`-uired.  (`HasT` transports a Bounded terminal across ≃ onto the
-- terminal-free atom `acq`; same `ContainsEnd` mechanism as `ComBackwardFails.bad`.)
------------------------------------------------------------------------

not-hasT-acq : ¬ HasT (acq {0})
not-hasT-acq ()

¬mobile-acq : ¬ Mobile ⟨ acq {0} ⟩
¬mobile-acq (P.⟨ _ , Bw , eq ⟩) =
  not-hasT-acq (≃-hasT (≃-sym eq) (seqʳ (bounded⇒hasT Bw)))

------------------------------------------------------------------------
-- A Mobile front is `acq`-headed: `Mobile ⟨s⟩ ⇒ s ≃ acq ; w`.  So on the
-- front channel `0F` the term `K acq · (` 0F)` is the R-Acq redex.
------------------------------------------------------------------------

mobile⇒acq-head : Mobile ⟨ sˣ ⟩ → ∃[ w ] sˣ ≃ acq ; w
mobile⇒acq-head (P.⟨ w , _ , eq ⟩) = w , eq

------------------------------------------------------------------------
-- DECISIVE, GENERAL.  A well-typed ν whose send-side bind context (over a
-- New-capped ambient `s ; end p`) carries a Mobile front at slot 0F has
-- bind group `B ≡ 0 ∷ b ∷ B′` with `NonZero b` — EXACTLY R-Acq's redex
-- shape `zero ∷ suc b₁ ∷ B₁`.  So the separated com sits behind a
-- pending-acq marker that R-Acq resolves first: the com is not stuck.
--
-- `f : 𝔽 (sum B)` (the front slot) both selects the front AND witnesses
-- `sum B ≥ 1`, so the marker's continuation block is present.  `⊢ᴮ B`
-- (from TP-Res) forces that block NonZero.
------------------------------------------------------------------------

mobile-front⇒RAcq-shape :
  New sˣ → ⊢ᴮ Bˣ → BindCtx (sˣ ; end polˣ) Bˣ Γˣ →
  (f : 𝔽 (sum Bˣ)) → Fin.toℕ f ≡ 0 → Mobile (lookup Γˣ f) →
  ∃[ b ] ∃[ B′ ] (Bˣ ≡ 0 ∷ b ∷ B′) × NonZero b
mobile-front⇒RAcq-shape N ⊢B C f tf mob
  with mobile-front⇒lead0 (new-end⇒noAcq N) C f tf mob
mobile-front⇒RAcq-shape N ⊢B C f tf mob | [] , refl        = case f of λ ()
mobile-front⇒RAcq-shape N ⊢B C f tf mob | (b ∷ B′) , refl
  with ⊢B
... | nz ∷ _ = b , B′ , refl , nz

------------------------------------------------------------------------
-- CONCRETE CAPSTONE.  A genuinely inhabited separated-com bind context at
-- the ACTUAL TP-Res ambient `s0 ; end p` (New s0 = msg): a Mobile front
-- `⟨acq;ret⟩` at slot 0F with a LIVE (msg-headed) channel `⟨s0 ; end ⁇⟩`
-- behind it — mirroring `ComMobileFront.refutes-unrestricted`, now over the
-- End-capped ambient the ν actually carries.  Applying the theorem to it
-- yields the explicit R-Acq bind shape `0 ∷ 1 ∷ 2 ∷ []` = `zero ∷ suc 0 ∷ …`.
------------------------------------------------------------------------

private
  s0 : 𝕊 0
  s0 = msg ‼ `⊤

  S0 : 𝕊 0
  S0 = s0 ; end ⁇

  bc-cont : BindCtx′ (acq ; S0) (⟨ acq ⟩ ∷ ⟨ S0 ⟩ ∷ [])
  bc-cont = cons acq S0 (λ { (() ; _) }) ≃-refl
              (cons S0 skip (λ { (() ; _) }) ≃-skipʳ (nil skip))

  cexBC : BindCtx S0 (0 ∷ 1 ∷ 2 ∷ []) (⟨ acq ; ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ S0 ⟩ ∷ [])
  cexBC = cons-acq
    (cons-ret/acq acq {s₂ = S0} ≃-refl
      (cons (acq ; ret) skip (λ { (() ; _) }) ≃-skipʳ (nil skip))
      (last bc-cont))

  Γcex : Ctx 3
  Γcex = ⟨ acq ; ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ S0 ⟩ ∷ []

  cex-front-Mobile : Mobile (lookup Γcex 0F)
  cex-front-Mobile = P.⟨ ret , P.ret , ≃-refl ⟩

  ⊢B-cex : ⊢ᴮ (0 ∷ 1 ∷ 2 ∷ [])
  ⊢B-cex = _ ∷ _ ∷ []

-- The inhabited separated-com bind context IS R-Acq-shaped `0 ∷ 1 ∷ 2 ∷ []`.
cex-RAcq-shape : ∃[ b ] ∃[ B′ ] ((0 ∷ 1 ∷ 2 ∷ []) ≡ 0 ∷ b ∷ B′) × NonZero b
cex-RAcq-shape =
  mobile-front⇒RAcq-shape P.msg ⊢B-cex cexBC 0F refl cex-front-Mobile
