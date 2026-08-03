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
open import BorrowedCF.Simulation.Backward.ComSepNoMsg
  using (NoMsg; noMsg-acq; noMsg-≃; noMsg-;-snd; bindCtx-noMsg-not-msg; _;_; skip)
import Data.Vec.Properties as VP
open import Data.Fin.Base using (_↑ʳ_; _↑ˡ_)
open import BorrowedCF.Processes.Typed using (bindCtx-inv-cons)
open Fin.Patterns

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


------------------------------------------------------------------------
-- Extra head-rigidity helper for cons-ret/acq handle blocks (session
-- `s₁ ; ret` with `s₁` acq-headed) and the acq-headed-witness extractor.
------------------------------------------------------------------------

nha-msg : ∀ {p T} → ¬ HasT (msg {0} p T)
nha-msg ()

front-msg-ret-⊥ : {a-rest s₁ y' Q : 𝕊 0} {p : Pol} {T : 𝕋} →
  (msg p T ; a-rest) ≃ (s₁ ; ret) → (s₁ ; y' ≃ acq ; Q) → ⊥
front-msg-ret-⊥ eq s₁y' with atom-;-unsnoc ret eq
... | inj₁ Sk = nha-msg (≃-hasT (≃-sym (≃-trans (≃-sym (≃-skipsʳ Sk)) eq)) (seqʳ HasT.ret))
... | inj₂ (y'' , msgy'' , _) =
      msg;≄acq; (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; msgy'' ≃-refl) s₁y'))

-- The borrower prefix `s₁` of a cons-ret/acq split is acq-headed.
retacq-acqhd : ∀ {s} → AmbInvAcq s → (s₁ s₂ : 𝕊 0) → s₁ ; s₂ ≃ s →
  ∃[ y' ] ∃[ Q ] (s₁ ; y' ≃ acq ; Q)
retacq-acqhd (mkAIA {Q} {pol} nhQ eq) s₁ s₂ split
  with atom-;-unsnoc end (≃-trans split eq)
... | inj₁ Sk = skip , (Q ; end pol) ,
      ≃-trans ≃-skipʳ (≃-trans (≃-trans (≃-sym (≃-skipsʳ Sk)) (≃-trans split eq)) ≃-assoc-;)
... | inj₂ (y' , s₁y' , _) = y' , Q , s₁y'


------------------------------------------------------------------------
-- Block analysis.  The handle block, unpacked as its front channel `a`
-- (session ⟨a⟩) with continuation `a-rest` and tail `BindCtx′ a-rest ΓBt`,
-- plus its session shape.  If the handle is the front (h = 0F) the block is
-- acq/ret-headed so a msg front is impossible; if the handle is behind the
-- front (h = suc _) the front is NECESSARILY non-Mobile (a Mobile front Skips
-- everything behind it, collapsing the tail to `nil`, forcing h = 0F).
------------------------------------------------------------------------

data BlockShape (SB : 𝕊 0) : Set where
  bsEnd : {Q : 𝕊 0} {p : Pol} → ¬ HasT Q → SB ≃ (acq ; Q) ; end p → BlockShape SB
  bsRet : {s₁ y' Q : 𝕊 0} → ¬ HasT s₁ → (s₁ ; y' ≃ acq ; Q) → SB ≃ s₁ ; ret → BlockShape SB

-- msg front vs the block session (head rigidity).
front-msg-shape-⊥ : {a a-rest SB : 𝕊 0} {T : 𝕋} →
  a ≃ msg ‼ T → a ; a-rest ≃ SB → BlockShape SB → ⊥
front-msg-shape-⊥ {a-rest = a-rest} a≃msg aeq (bsEnd nhQ eq) =
  front-msg-end-⊥ (≃-trans msgeq eq)
  where msgeq = ≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq
front-msg-shape-⊥ {a-rest = a-rest} a≃msg aeq (bsRet nhs₁ acqhd eq) =
  front-msg-ret-⊥ (≃-trans msgeq eq) acqhd
  where msgeq = ≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq

-- Mobile front Skips everything behind it.
mob-shape-skips : {a a-rest SB : 𝕊 0} →
  Mobile ⟨ a ⟩ → a ; a-rest ≃ SB → BlockShape SB → Skips a-rest
mob-shape-skips mob aeq (bsEnd nhQ eq) = mob-front-whole-end mob (nha-acq-seq nhQ) (≃-trans aeq eq)
mob-shape-skips mob aeq (bsRet nhs₁ acqhd eq) = mob-front-whole-ret mob nhs₁ (≃-trans aeq eq)

block-analysis : ∀ {w'} {SB a a-rest : 𝕊 0} {ΓBt : Ctx w'} {T : 𝕋} →
  a ; a-rest ≃ SB → BindCtx′ a-rest ΓBt → BlockShape SB →
  (h : 𝔽 (suc w')) → lookup (⟨ a ⟩ ∷ ΓBt) h ≃ ⟨ msg ‼ T ⟩ →
  ⊥ ⊎ (¬ Mobile ⟨ a ⟩)
block-analysis aeq bc-tail bs 0F hmsg =
  inj₁ (front-msg-shape-⊥ (≃-⟨⟩⁻¹ hmsg) aeq bs)
block-analysis {a-rest = a-rest} aeq bc-tail bs (suc h′) hmsg = inj₂ ¬mob-a
  where
    aux : ∀ {w''} {Γt : Ctx w''} → Skips a-rest → BindCtx′ a-rest Γt → 𝔽 w'' → ⊥
    aux sk (nil _) ()
    aux sk (cons _ _ ¬sk' _ _) _ = ¬sk' sk
    ¬mob-a : ¬ Mobile ⟨ _ ⟩
    ¬mob-a mob = aux (mob-shape-skips mob aeq bs) bc-tail h′


------------------------------------------------------------------------
-- ¬ Skips helpers.
------------------------------------------------------------------------

skips⇒¬hasT : {s : 𝕊 0} → Skips s → ¬ HasT s
skips⇒¬hasT Sk h = case (≃-hasT (≃-sym (skips⇒skip≃ Sk)) h) of λ ()

shape⇒¬skips : {SB : 𝕊 0} → BlockShape SB → ¬ Skips SB
shape⇒¬skips (bsEnd nhQ eq) Sk = skips⇒¬hasT Sk (≃-hasT (≃-sym eq) (seqʳ HasT.end))
shape⇒¬skips (bsRet nhs₁ acqhd eq) Sk = skips⇒¬hasT Sk (≃-hasT (≃-sym eq) (seqʳ HasT.ret))


------------------------------------------------------------------------
-- Navigation with the invariant `AmbInvAcq s ⊎ NoMsg s`.  Descending a
-- cons-ret/acq whose split-off tail Skips just degrades the ambient to NoMsg
-- (no live msg behind ⟹ contradiction at the handle block).  This is how the
-- `¬ Skips` obligation is discharged (by the live handle, not structurally).
------------------------------------------------------------------------

Inv : 𝕊 0 → Set
Inv s = AmbInvAcq s ⊎ NoMsg s

noMsg-acq-seq : {s : 𝕊 0} → NoMsg s → NoMsg (acq ; s)
noMsg-acq-seq nm = noMsg-acq ; nm

skips⇒noMsg : {s : 𝕊 0} → Skips s → NoMsg s
skips⇒noMsg Sk = noMsg-≃ (skips⇒skip≃ Sk) skip

inv-step-acq : ∀ {s} → Inv s → Inv (acq ; s)
inv-step-acq (inj₁ aia) = inj₁ (step-acq aia)
inv-step-acq (inj₂ nm)  = inj₂ (noMsg-acq-seq nm)

inv-step-retacq : ∀ {s s₁ s₂} → Inv s → s₁ ; s₂ ≃ s → Inv (acq ; s₂)
inv-step-retacq (inj₁ (mkAIA {Q} {pol} nhQ eq)) split
  with atom-;-unsnoc end (≃-trans split eq)
... | inj₁ Sk = inj₂ (noMsg-acq-seq (skips⇒noMsg Sk))
... | inj₂ (y' , s₁y' , y'end) =
      inj₁ (mkAIA {Q = y'} {pol = pol}
             (λ h → nha-acq-seq nhQ (≃-hasT s₁y' (seqʳ h)))
             (≃-trans (≃-; ≃-refl (≃-sym y'end)) (≃-sym ≃-assoc-;)))
inv-step-retacq (inj₂ nm) split = inj₂ (noMsg-acq-seq (noMsg-;-snd (noMsg-≃ (≃-sym split) nm)))

-- ↑ʳ distributes over + on the ℕ index.
