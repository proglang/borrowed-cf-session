-- | The com-reflect "leading-cons-acq zero-branch" is un-typeable.
--
--   Companion to `ComBackwardFails` / `ComMobileFront`.  At `Com.agda:852`, the
--   send handle of a reverse RU-Com sits in a block whose bind-group prefix
--   begins with a `zero` (a leading `cons-acq` marker — a pending, not-yet
--   reacquired borrow).  `ComMobileFront.refutes-unrestricted` shows the FLAT
--   `BindCtx` judgement does NOT rule this out; the exclusion needs the redex
--   typing + the ≼ context-ordering (as in `com-front-force-notmob`).
--
--   The mathematical core here (`mob-front-whole` / `-ret`) generalises
--   `ComBackwardFails.mob-front-whole`: a MOBILE (Bounded) front over a block
--   whose session factors as `P ; end` / `s₁ ; ret` with `¬ HasT` prefix
--   consumes the WHOLE block, so anything strictly behind it `Skips` — killing a
--   live `msg` handle.  The `¬ HasT` prefix hypothesis (rather than `New`) is
--   what survives the acq-nesting the leading `cons-acq` introduces.
--
--   STATUS.  Verified (exit 0, no postulates/holes): the mobility-consumption
--   core (`mob-front-whole-end` / `-ret` over a `¬ HasT` prefix), the head
--   rigidity front lemma (`front-msg-end-⊥`), and the navigation-invariant
--   maintenance (`AmbInvAcq` + `base-acq`/`step-acq`/`step-retacq`) that keeps
--   the ambient in `(acq ; ¬HasT) ; end` shape across the leading markers.
--   These are the genuinely new lemmas of the argument.  The final assembly
--   (`sep-com-¬wt`) — the `descend` recursion into the handle block, the
--   Γ↔Δ positional reconciliation, and the `com-xS-min` wiring for the
--   (non-mobile front, qˢ>0) case — remains to be threaded on top; note the
--   `descend`'s `¬ Skips s₂` obligation is discharged by the global
--   `send-handle-≃msg-app` fact (the live msg cannot sit in a skipped block).
module BorrowedCF.Simulation.Backward.ComSepImpossible where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)
open import BorrowedCF.Types.ContainsEnd using (HasT; seqˡ; seqʳ; bounded⇒hasT; new⇒¬hasT; ≃-hasT)
open import BorrowedCF.Types.AtomHead using (msg;≄acq;; atomKind≢⇒≄-;ˡ)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil; bindCtx-B≢[])
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_)

------------------------------------------------------------------------
-- ¬ HasT helpers.
------------------------------------------------------------------------

nha-acq : ¬ HasT (acq {0})
nha-acq ()

nha-seq : {a b : 𝕊 0} → ¬ HasT a → ¬ HasT b → ¬ HasT (a ; b)
nha-seq na nb (seqˡ h) = na h
nha-seq na nb (seqʳ h) = nb h

nha-acq-seq : {b : 𝕊 0} → ¬ HasT b → ¬ HasT (acq ; b)
nha-acq-seq nb = nha-seq nha-acq nb

new⇒nha : {s : 𝕊 0} → New s → ¬ HasT s
new⇒nha = new⇒¬hasT

mobile⇒bounded : {s : 𝕊 0} → Mobile ⟨ s ⟩ → Bounded s
mobile⇒bounded (P.⟨ w , Bw , eq ⟩) = P.≃-bounded (≃-sym eq) (P.-;₂_ Bw)

------------------------------------------------------------------------
-- bad-gen : a Bounded prefix (HasT) cannot ≃-prefix a ¬HasT session.
------------------------------------------------------------------------

bad-gen : {a y rhs : 𝕊 0} → Bounded a → ¬ HasT rhs → a ; y ≃ rhs → ⊥
bad-gen Ba nh eq = nh (≃-hasT eq (seqˡ (bounded⇒hasT Ba)))

------------------------------------------------------------------------
-- MOB-WHOLE : a Mobile front over a block whose session ≃ P ; (atom) with
-- ¬ HasT P leaves only Skips behind it.  Two instances: terminal = end / ret.
------------------------------------------------------------------------

mob-front-whole-end : {a a-rest P : 𝕊 0} {p : Pol} →
  Mobile ⟨ a ⟩ → ¬ HasT P →
  (a ; a-rest) ≃ (P ; end p) →
  Skips a-rest
mob-front-whole-end mob nhP eq with atom-;-unsnoc end eq
... | inj₁ Sk = Sk
... | inj₂ (_ , e2 , _) = ⊥-elim (bad-gen (mobile⇒bounded mob) nhP e2)

mob-front-whole-ret : {a a-rest s₁ : 𝕊 0} →
  Mobile ⟨ a ⟩ → ¬ HasT s₁ →
  (a ; a-rest) ≃ (s₁ ; ret) →
  Skips a-rest
mob-front-whole-ret mob nhs eq with atom-;-unsnoc ret eq
... | inj₁ Sk = Sk
... | inj₂ (_ , e2 , _) = ⊥-elim (bad-gen (mobile⇒bounded mob) nhs e2)

------------------------------------------------------------------------
-- FRONT-MSG head rigidity : an acq-headed / ret-tailed block cannot have a
-- msg front.  Used for the qˢ = 0 sub-case (handle at block front).
------------------------------------------------------------------------

-- The block session P ; end p is acq-headed when P = acq ; Q; a msg front is
-- impossible.
front-msg-end-⊥ : {a-rest Q : 𝕊 0} {p q : Pol} {T : 𝕋} →
  (msg p T ; a-rest) ≃ ((acq ; Q) ; end q) → ⊥
front-msg-end-⊥ eq = msg;≄acq; (≃-trans eq ≃-assoc-;)


------------------------------------------------------------------------
-- Navigation invariant.  As we descend the leading cons-acq / cons-ret/acq
-- markers of `BindCtx (s' ; end p') BL Γ`, the ambient session `s` keeps the
-- shape `(acq ; Q) ; end` with `¬ HasT Q` — acq-headed (from ≥1 cons-acq) with a
-- terminal-free prefix.  This is exactly what mob-front-whole-* / front-msg-*
-- need at the handle block, and it is what survives the acq-nesting.
------------------------------------------------------------------------

record AmbInvAcq (s : 𝕊 0) : Set where
  constructor mkAIA
  field
    {Q}   : 𝕊 0
    {pol} : Pol
    nhQ   : ¬ HasT Q
    eq    : s ≃ (acq ; Q) ; end pol

-- the whole acq-headed prefix is ¬HasT
aia-nhP : ∀ {s} (aia : AmbInvAcq s) → ¬ HasT (acq ; AmbInvAcq.Q aia)
aia-nhP aia = nha-acq-seq (AmbInvAcq.nhQ aia)

-- base: the ν session `s' ; end p'` with `New s'`, after ONE cons-acq, is AmbInvAcq.
base-acq : ∀ {s' : 𝕊 0} {p'} → New s' → AmbInvAcq (acq ; (s' ; end p'))
base-acq {s'} {p'} Ns =
  mkAIA {Q = s'} {pol = p'} (new⇒nha Ns) (≃-sym ≃-assoc-;)

-- cons-acq step: prepend one acq.
step-acq : ∀ {s} → AmbInvAcq s → AmbInvAcq (acq ; s)
step-acq (mkAIA {Q} {pol} nhQ eq) =
  mkAIA {Q = acq ; Q} {pol = pol} (nha-acq-seq nhQ)
    (≃-trans (≃-; ≃-refl eq) (≃-sym ≃-assoc-;))

-- cons-ret/acq step: split off a borrower block `s₁ ; ret` (giving `¬ HasT s₁`)
-- and continue with `acq ; s₂`.  Needs `¬ Skips s₂` (the rest is non-empty).
step-retacq : ∀ {s} → AmbInvAcq s → (s₁ s₂ : 𝕊 0) → s₁ ; s₂ ≃ s → ¬ Skips s₂
  → ¬ HasT s₁ × AmbInvAcq (acq ; s₂)
step-retacq (mkAIA {Q} {pol} nhQ eq) s₁ s₂ split ¬sk
  with atom-;-unsnoc end (≃-trans split eq)
... | inj₁ Sk = ⊥-elim (¬sk Sk)
... | inj₂ (y' , s₁y' , y'end) =
      (λ h → nh-acqQ (≃-hasT s₁y' (seqˡ h)))
      , mkAIA {Q = y'} {pol = pol} nhy' eqfin
  where
    nh-acqQ : ¬ HasT (acq ; Q)
    nh-acqQ = nha-acq-seq nhQ
    nhy' : ¬ HasT y'
    nhy' h = nh-acqQ (≃-hasT s₁y' (seqʳ h))
    eqfin : acq ; s₂ ≃ (acq ; y') ; end pol
    eqfin = ≃-trans (≃-; ≃-refl (≃-sym y'end)) (≃-sym ≃-assoc-;)
