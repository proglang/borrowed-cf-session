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
open import BorrowedCF.Context using (Ctx; _⸴*_)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil; bindCtx-B≢[])
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_)
open import BorrowedCF.Simulation.Backward.ComSepNoMsg
  using (NoMsg; noMsg-acq; noMsg-≃; noMsg-msg-⊥; noMsg-;-snd; bindCtx-noMsg-not-msg; bindCtx′-lookup-NoMsg; _;_; skip; ret)
import Data.Vec.Properties as VP
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Properties using (lookup-++ʳ)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; toℕ-injective; toℕ<n)
open import Data.Fin using (splitAt)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Properties using (cast-is-id)
open import Data.List using (length)
open import Data.Fin.Base using (_↑ʳ_; _↑ˡ_)
open import BorrowedCF.Processes.Typed using (bindCtx-inv-cons)
open Fin.Patterns
open import BorrowedCF.Terms
open import BorrowedCF.Context using (Struct; _∶_≼_; _∥_)
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅; LeftPat)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Processes.Typed using (structBinder)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.RevComConfine using (com-xS-min)
open import BorrowedCF.Simulation.Support.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Support.RevGrindA using (com-¬before)
open import BorrowedCF.Simulation.Backward.ComFire using (send-arg-count)
open import BorrowedCF.Simulation.Backward.ComConfineGen using (send-¬mobile)
open import BorrowedCF.Simulation.Backward.ComSepBefore using (before-com-binderᴸ-later)
open import BorrowedCF.Types using (unr⇒mobile)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 using (send-handle-≃msg-app)
open import Data.Vec.Properties using (lookup-++ˡ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Fin using (fromℕ<)

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
-- Block analysis.  The handle block, unpacked as its front channel `a` with
-- continuation `a-rest` and tail `BindCtx′ a-rest ΓBt`, plus its session shape
-- (acq-headed, ending in end/ret with a ¬HasT prefix `Q`).  If the handle is
-- the front (h = 0F) a msg front is impossible (head rigidity); if it is behind
-- the front the front is NECESSARILY non-Mobile — a Mobile (Bounded) front makes
-- everything behind it `NoMsg`, so the live msg handle cannot sit there.
------------------------------------------------------------------------

skips⇒noMsg : {s : 𝕊 0} → Skips s → NoMsg s
skips⇒noMsg Sk = noMsg-≃ (skips⇒skip≃ Sk) skip

data BlockShape (SB : 𝕊 0) : Set where
  bsEnd : {Q : 𝕊 0} {p : Pol} → ¬ HasT Q → SB ≃ (acq ; Q) ; end p → BlockShape SB
  bsRet : {s₁ s₂ Q : 𝕊 0} {p : Pol} → ¬ HasT Q
        → (s₁ ; s₂ ≃ (acq ; Q) ; end p) → SB ≃ s₁ ; ret → BlockShape SB

skips-fst : {s₁ s₂ : 𝕊 0} → Skips (s₁ ; s₂) → Skips s₁
skips-fst (Sk ; _) = Sk

-- an acq-headed prefix witness from the block's ambient split.
split-acqhd : {s₁ s₂ Q : 𝕊 0} {p : Pol}
  → (s₁ ; s₂ ≃ (acq ; Q) ; end p) → ∃[ y' ] ∃[ Q' ] (s₁ ; y' ≃ acq ; Q')
split-acqhd {Q = Q} {p} split with atom-;-unsnoc end split
... | inj₁ Sk = skip , (Q ; end p) ,
      ≃-trans ≃-skipʳ (≃-trans (≃-trans (≃-sym (≃-skipsʳ Sk)) split) ≃-assoc-;)
... | inj₂ (y' , s₁y' , _) = y' , Q , s₁y'

front-msg-shape-⊥ : {a a-rest SB : 𝕊 0} {T : 𝕋} →
  a ≃ msg ‼ T → a ; a-rest ≃ SB → BlockShape SB → ⊥
front-msg-shape-⊥ a≃msg aeq (bsEnd nhQ eq) =
  front-msg-end-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq) eq)
front-msg-shape-⊥ a≃msg aeq (bsRet nhQ split eq) with split-acqhd split
... | y' , Q' , s₁y' =
      front-msg-ret-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq) eq) s₁y'

-- a Mobile (Bounded) front leaves only NoMsg behind it.
mob⇒noMsg-ar : {a a-rest SB : 𝕊 0} → Mobile ⟨ a ⟩ → BlockShape SB → a ; a-rest ≃ SB → NoMsg a-rest
mob⇒noMsg-ar mob (bsEnd nhQ eq) aeq =
  skips⇒noMsg (mob-front-whole-end mob (nha-acq-seq nhQ) (≃-trans aeq eq))
mob⇒noMsg-ar {a-rest = a-rest} mob (bsRet {s₁} {s₂} {Q} nhQ split eq) aeq
  with atom-;-unsnoc ret (≃-trans aeq eq)
... | inj₁ Sk = skips⇒noMsg Sk
... | inj₂ (y' , ay' , y'ret)
  with atom-;-unsnoc end (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; ay' ≃-refl) split))
...   | inj₁ Sky's₂ = noMsg-≃ (≃-sym arest≃ret) ret
        where
          Sky' : Skips y'
          Sky' = skips-fst Sky's₂
          arest≃ret : a-rest ≃ ret
          arest≃ret = ≃-trans (≃-sym y'ret)
                        (≃-trans (≃-; (≃-sym (skips⇒skip≃ Sky')) ≃-refl) ≃-skipˡ)
...   | inj₂ (y'' , ay'' , _) = ⊥-elim (bad-gen (mobile⇒bounded mob) (nha-acq-seq nhQ) ay'')

bindCtx′-noMsg-not-msg : ∀ {w} {Γ : Ctx w} {ar} {i : 𝔽 w} {T} →
  BindCtx′ ar Γ → NoMsg ar → lookup Γ i ≃ ⟨ msg ‼ T ⟩ → ⊥
bindCtx′-noMsg-not-msg {i = i} bt nm eq with bindCtx′-lookup-NoMsg bt nm i
... | s' , ej , NMs' =
      noMsg-msg-⊥ (noMsg-≃ (≃-⟨⟩⁻¹ (≃-trans (≃-reflexive (sym ej)) eq)) NMs')

block-analysis : ∀ {w'} {SB a a-rest : 𝕊 0} {ΓBt : Ctx w'} {T : 𝕋} →
  a ; a-rest ≃ SB → BindCtx′ a-rest ΓBt → BlockShape SB →
  (h : 𝔽 (suc w')) → lookup (⟨ a ⟩ ∷ ΓBt) h ≃ ⟨ msg ‼ T ⟩ →
  ⊥ ⊎ (¬ Mobile ⟨ a ⟩ × Fin.toℕ h ≢ 0)
block-analysis aeq bc-tail bs 0F hmsg =
  inj₁ (front-msg-shape-⊥ (≃-⟨⟩⁻¹ hmsg) aeq bs)
block-analysis aeq bc-tail bs (suc h′) hmsg = inj₂ (¬mob-a , λ ())
  where
    ¬mob-a : ¬ Mobile ⟨ _ ⟩
    ¬mob-a mob = bindCtx′-noMsg-not-msg bc-tail (mob⇒noMsg-ar mob bs aeq) hmsg

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


------------------------------------------------------------------------
-- descend : peel the leading `B₁` markers (maintaining Inv), returning the
-- handle-block sub-context Γh with a toℕ-based lookup reconciliation.
------------------------------------------------------------------------

0<len++ : ∀ (B₁ : BindGroup) (hb : ℕ) (B₂ : BindGroup) → 0 Nat.< length (B₁ ++ hb ∷ B₂)
0<len++ []       hb B₂ = Nat.s≤s Nat.z≤n
0<len++ (b ∷ B₁) hb B₂ = Nat.s≤s Nat.z≤n

descend : ∀ {s} (B₁ : BindGroup) (hb : ℕ) (B₂ : BindGroup)
    {Γ : Ctx (sum (B₁ ++ hb ∷ B₂))} → Inv s
  → BindCtx s (B₁ ++ hb ∷ B₂) Γ
  → Σ[ Γh ∈ Ctx (sum (hb ∷ B₂)) ] Σ[ sh ∈ 𝕊 0 ]
      Inv sh × BindCtx sh (hb ∷ B₂) Γh
      × (∀ (p : 𝔽 (sum (B₁ ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
          → Fin.toℕ p ≡ sum B₁ + Fin.toℕ k → lookup Γ p ≡ lookup Γh k)
descend {s} [] hb B₂ {Γ} inv C =
  Γ , s , inv , C , λ p k tp → cong (lookup Γ) (toℕ-injective tp)
descend (b ∷ B₁) hb B₂ {Γ} inv C
  with bindCtx-inv-cons {B = B₁ ++ hb ∷ B₂} (0<len++ B₁ hb B₂) C
... | inj₂ (refl , C') = descend B₁ hb B₂ (inv-step-acq inv) C'
... | inj₁ (s₁ , s₂ , Γ₁' , Γ₂' , split , refl , _ , C') =
      let Γh , sh , inv-h , C-h , rec = descend B₁ hb B₂ (inv-step-retacq inv split) C'
      in Γh , sh , inv-h , C-h , recon Γh rec
  where
    recon : (Γh : Ctx (sum (hb ∷ B₂)))
      → (∀ (p' : 𝔽 (sum (B₁ ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
          → Fin.toℕ p' ≡ sum B₁ + Fin.toℕ k → lookup Γ₂' p' ≡ lookup Γh k)
      → (p : 𝔽 (sum ((b ∷ B₁) ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
      → Fin.toℕ p ≡ sum (b ∷ B₁) + Fin.toℕ k → lookup (Γ₁' ⸴* Γ₂') p ≡ lookup Γh k
    recon Γh rec p k tp with splitAt b p in seq
    ... | inj₁ j = ⊥-elim (Nat.<-irrefl refl (Nat.≤-<-trans b≤p p<b))
      where
        p≡j : j ↑ˡ _ ≡ p
        p≡j = splitAt⁻¹-↑ˡ seq
        tj : Fin.toℕ p ≡ Fin.toℕ j
        tj = sym (cong Fin.toℕ p≡j) ■ toℕ-↑ˡ j _
        p<b : Fin.toℕ p Nat.< b
        p<b = subst (Nat._< b) (sym tj) (toℕ<n j)
        b≤p : b Nat.≤ Fin.toℕ p
        b≤p = subst (b Nat.≤_) (sym tp)
                (Nat.≤-trans (Nat.m≤m+n b (sum B₁ + Fin.toℕ k))
                  (Nat.≤-reflexive (sym (Nat.+-assoc b (sum B₁) (Fin.toℕ k)))))
    ... | inj₂ p'' =
          cong (lookup (Γ₁' ⸴* Γ₂')) (sym (splitAt⁻¹-↑ʳ seq))
            ■ lookup-++ʳ Γ₁' Γ₂' p'' ■ rec p'' k tp''
      where
        p≡ : b ↑ʳ p'' ≡ p
        p≡ = splitAt⁻¹-↑ʳ seq
        tp'' : Fin.toℕ p'' ≡ sum B₁ + Fin.toℕ k
        tp'' = Nat.+-cancelˡ-≡ b _ _
                 (sym (toℕ-↑ʳ b p'') ■ cong Fin.toℕ p≡ ■ tp ■ Nat.+-assoc b (sum B₁) (Fin.toℕ k))


------------------------------------------------------------------------
-- extract-block : the handle block (last / cons-ret/acq) → block-analysis.
------------------------------------------------------------------------

extract-block : ∀ {sh : 𝕊 0} {W'} {B₂ : BindGroup} {Γh : Ctx (suc W' + sum B₂)} {T : 𝕋}
  → AmbInvAcq sh → BindCtx sh (suc W' ∷ B₂) Γh
  → (k : 𝔽 (suc W' + sum B₂)) → Fin.toℕ k Nat.< suc W' → lookup Γh k ≃ ⟨ msg ‼ T ⟩
  → ⊥ ⊎ (¬ Mobile (lookup Γh 0F) × Fin.toℕ k ≢ 0)
extract-block aia (last (cons a ar ¬sk aeq bt)) k k<sW' hmsg =
  block-analysis aeq bt (bsEnd (AmbInvAcq.nhQ aia) (AmbInvAcq.eq aia)) k hmsg
extract-block {W' = W'} {B₂ = B₂} aia
  (cons-ret/acq s₁ {Γ₁ = Γ1} {Γ₂ = Γ2} split (cons a ar ¬sk aeq bt) rest) k k<sW' hmsg =
  Sum.map (λ z → z) (λ (¬m , k₁≢0) → ¬m , (λ e → k₁≢0 (tk₁ ■ e)))
    (block-analysis aeq bt
       (bsRet (AmbInvAcq.nhQ aia) (≃-trans split (AmbInvAcq.eq aia)) ≃-refl)
       k₁ hmsg₁)
  where
    k₁ : 𝔽 (suc W')
    k₁ = fromℕ< k<sW'
    tk₁ : Fin.toℕ k₁ ≡ Fin.toℕ k
    tk₁ = toℕ-fromℕ< k<sW'
    k≡ : k ≡ k₁ ↑ˡ sum B₂
    k≡ = toℕ-injective (sym (toℕ-↑ˡ k₁ (sum B₂) ■ tk₁))
    hmsg₁ : lookup Γ1 k₁ ≃ ⟨ msg ‼ _ ⟩
    hmsg₁ = subst (_≃ _)
             (cong (lookup (Γ1 ⸴* Γ2)) k≡ ■ lookup-++ˡ Γ1 Γ2 k₁) hmsg

------------------------------------------------------------------------
-- The export: the com-reflect leading-cons-acq zero-branch is un-typeable.
------------------------------------------------------------------------

sep-com-¬wt : ∀ {m} (BL BR : BindGroup)
  {Γ₁ : Ctx (sum BL)} {Γ₂ : Ctx (sum BR)} {Γ : Ctx m}
  {s' : 𝕊 0} {p' : Pol} {rest B₂ˢ : BindGroup} {qˢ b₁ˢ : ℕ}
  {g : Struct m} {𝒫ˢ : CxPat (sum BL + sum BR + m)}
  {γrˢ α β : Struct (sum BL + sum BR + m)}
  {aS : Tm (sum BL + sum BR + m)} {xS : 𝔽 (sum BL + sum BR + m)} {U : 𝕋}
  → New s'
  → BindCtx (s' ; end p') BL Γ₁
  → LeftPat 𝒫ˢ
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ; γrˢ ⊢ K `send ·¹ (aS ⊗ (` xS)) ∶ U ∣ 𝕀
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ 𝒫ˢ [ γrˢ ]𝓅 ≼ α
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ α ∥ β ≼
      ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → BL ≡ zero ∷ rest ++ (qˢ + suc b₁ˢ) ∷ B₂ˢ
  → Fin.toℕ xS ≡ sum (zero ∷ rest) + qˢ
  → ⊥
sep-com-¬wt {m} BL BR {Γ₁} {Γ₂} {Γ} {s'} {p'} {rest} {B₂ˢ} {qˢ} {b₁ˢ}
            {g} {𝒫ˢ} {γrˢ} {α} {β} {aS} {xS} {U}
            Nnew C lpˢ ⊢redexˢ ≼ˢ ≼₁ BLeq xtoℕ0
  rewrite BLeq ■ cong (λ w → zero ∷ rest ++ w ∷ B₂ˢ) (Nat.+-suc qˢ b₁ˢ)
  with bindCtx-inv-cons {B = rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ} (0<len++ rest (suc (qˢ + b₁ˢ)) B₂ˢ) C
... | inj₁ (_ , _ , _ , _ , _ , _ , nil (_ ; ()) , _)
... | inj₂ (_ , C1)
  with descend rest (suc (qˢ + b₁ˢ)) B₂ˢ (inj₁ (base-acq Nnew)) C1
... | Γh , sh , inv-h , C-h , recon = go inv-h
  where
    Δ : Ctx (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ) + sum BR + m)
    Δ = (Γ₁ ⸴* Γ₂) ⸴* Γ
    hbsum : ℕ
    hbsum = suc (qˢ + b₁ˢ) + sum B₂ˢ
    qˢ<hb : qˢ Nat.< suc (qˢ + b₁ˢ)
    qˢ<hb = Nat.s≤s (Nat.m≤m+n qˢ b₁ˢ)
    khandle : 𝔽 (sum (suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    khandle = fromℕ< (Nat.<-≤-trans qˢ<hb (Nat.m≤m+n (suc (qˢ + b₁ˢ)) (sum B₂ˢ)))
    tkh : Fin.toℕ khandle ≡ qˢ
    tkh = toℕ-fromℕ< _
    xlt : sum rest + qˢ Nat.< sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ)
    xlt = subst (sum rest + qˢ Nat.<_) (sym (sum-++ rest (suc (qˢ + b₁ˢ) ∷ B₂ˢ)))
            (Nat.+-monoʳ-< (sum rest) (Nat.<-≤-trans qˢ<hb (Nat.m≤m+n (suc (qˢ + b₁ˢ)) (sum B₂ˢ))))
    xpos : 𝔽 (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    xpos = fromℕ< xlt
    txpos : Fin.toℕ xpos ≡ sum rest + qˢ
    txpos = toℕ-fromℕ< xlt
    xposG≡xS : (xpos ↑ˡ sum BR) ↑ˡ m ≡ xS
    xposG≡xS = toℕ-injective
      (toℕ-↑ˡ (xpos ↑ˡ sum BR) m ■ toℕ-↑ˡ xpos (sum BR) ■ txpos ■ sym xtoℕ0)
    lookupΔ : lookup Δ ((xpos ↑ˡ sum BR) ↑ˡ m) ≡ lookup Γ₁ xpos
    lookupΔ = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (xpos ↑ˡ sum BR) ■ lookup-++ˡ Γ₁ Γ₂ xpos
    Δhandle≃ : ∀ {T} → lookup Δ xS ≃ ⟨ msg ‼ T ⟩ → lookup Γ₁ xpos ≃ ⟨ msg ‼ T ⟩
    Δhandle≃ msg≃ = subst (_≃ _) (cong (lookup Δ) (sym xposG≡xS) ■ lookupΔ) msg≃
    reconxk : lookup Γ₁ xpos ≡ lookup Γh khandle
    reconxk = recon xpos khandle (txpos ■ cong (sum rest +_) (sym tkh))
    handle≃ : ∀ {T} → lookup Δ xS ≃ ⟨ msg ‼ T ⟩ → lookup Γh khandle ≃ ⟨ msg ‼ T ⟩
    handle≃ msg≃ = subst (_≃ _) reconxk (Δhandle≃ msg≃)
    flt : sum rest Nat.< sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ)
    flt = Nat.≤-<-trans (Nat.m≤m+n (sum rest) qˢ) xlt
    fpos : 𝔽 (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    fpos = fromℕ< flt
    tfpos : Fin.toℕ fpos ≡ sum rest
    tfpos = toℕ-fromℕ< flt
    lookupΔf : lookup Δ ((fpos ↑ˡ sum BR) ↑ˡ m) ≡ lookup Γ₁ fpos
    lookupΔf = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (fpos ↑ˡ sum BR) ■ lookup-++ˡ Γ₁ Γ₂ fpos
    reconf : lookup Γ₁ fpos ≡ lookup Γh 0F
    reconf = recon fpos 0F (tfpos ■ sym (Nat.+-identityʳ (sum rest)))
    comxs : ¬ Mobile (lookup Γh 0F) → qˢ ≢ 0 → ⊥
    comxs ¬mob0 qˢ≢0 with send-handle-≃msg-app ⊢redexˢ
    ... | T , msg≃ =
      com-xS-min ¬uxS ¬uy lpˢ ≼ˢ ≼₁ cnt1 bfr 1≤cS ¬bfr
      where
        BLr : BindGroup
        BLr = zero ∷ rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ
        γ₁ : Struct (sum BLr + sum BR + m)
        γ₁ = (structBinder BLr 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BLr) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BLr + sum BR))
        ¬uxS : ¬ Mobile (lookup Δ xS)
        ¬uxS = send-¬mobile ⊢redexˢ
        ¬uy : ¬ Mobile (lookup Δ ((fpos ↑ˡ sum BR) ↑ˡ m))
        ¬uy = subst (λ v → ¬ Mobile v) (sym (lookupΔf ■ reconf)) ¬mob0
        cnt1 = subst (λ v → count v γ₁ ≡ 1) xposG≡xS
                 (count-handle-groupᴸ BLr BR g xpos)
        bfr = subst (λ v → before ((fpos ↑ˡ sum BR) ↑ˡ m) v γ₁) xposG≡xS
                (before-com-binderᴸ-later (zero ∷ rest) (suc (qˢ + b₁ˢ) ∷ B₂ˢ) BR g
                  fpos xpos tfpos txpos qˢ≢0)
        1≤cS : 1 Nat.≤ count xS γrˢ
        1≤cS = send-arg-count (λ u → ¬uxS (unr⇒mobile u)) ⊢redexˢ
        ¬bfr : ¬ before ((fpos ↑ˡ sum BR) ↑ˡ m) xS γrˢ
        ¬bfr = com-¬before {𝒫ˢ = 𝒫ˢ} ¬uxS ¬uy ⊢redexˢ ≼ˢ ≼₁ cnt1
    go : Inv sh → ⊥
    go (inj₂ nm) with send-handle-≃msg-app ⊢redexˢ
    ... | T , msg≃ = bindCtx-noMsg-not-msg C-h nm (handle≃ msg≃)
    go (inj₁ aia) with send-handle-≃msg-app ⊢redexˢ
    ... | T , msg≃
      with extract-block aia C-h khandle
             (subst (Nat._< suc (qˢ + b₁ˢ)) (sym tkh) qˢ<hb) (handle≃ msg≃)
    ...   | inj₁ bot = bot
    ...   | inj₂ (¬mob0 , k≢0) = comxs ¬mob0 (λ q0 → k≢0 (tkh ■ q0))
