-- | A THIRD counterexample hunt (2026-09-03), and the one that bites:
--   `Position.AcqNonFirstGroupHead` -- and with it `ImpureRedexHead` for
--   `drop` -- is FALSE for `Processes/Typed.agda`'s `BindCtx` as it stands.
--
--   PLAN.md §6/§7 tightened the SPLIT CONSTANTS (`lsplit`/`rsplit` now demand
--   `¬ Skips` of both components) and `BindCtx` (`cons-ret/acq` gained
--   `¬ Skips s₂`, both group constructors gained `AcqHeadCtx`).  The reason
--   given for the `rsplit` premise was: splitting the head `⟨ acq ; t ⟩` of a
--   non-first group as `⟨ skip ; (acq ; t) ⟩` would leave a head `⟨ ret ⟩`
--   whose `acq` has moved into the NEXT group.  That is blocked for the term
--   that PERFORMS the split -- but NOT in `BindCtx` itself, which `TP-Res`
--   quantifies over freely: `cons-ret/acq` still admits `s₁ ≡ skip`, i.e. a
--   group that does no work at all and passes its `acq` on.  The next group
--   then governs `acq ; acq ; ⋯`, and its SECOND handle can carry the second
--   `acq` -- an acq-headed handle at offset 1.
--
--   `bad` below is such a `BindCtx`, at a `⊢ᴮ`-legal group shape, reached from
--   a `New`-derived top-level session; `refuted` is the machine-checked
--   refutation of `Position/Crux.agda`'s `nonFirstGroup-interior-noAcq`, on
--   which `acq-non-first-group-head` depends.
--
--   THE FIX, NOW ADOPTED in `Processes/Typed.agda`:  `AcqHeadCtx` says what
--   its own doc comment says --
--
--       AcqHeadCtx (⟨ s ⟩ ∷ _) = Σ[ t ∈ 𝕊 0 ] (s ≃ acq ; t)
--       AcqHeadCtx _           = ⊥
--
--   instead of the strictly weaker `¬ Skips s`.  `bad` below is STILL a legal
--   `BindCtx` (its own next group IS acq-headed) and `refuted` therefore still
--   stands: the P3 metatheorem is false for a `BindCtx` taken in isolation, and
--   `Crux.nonFirstGroup-interior-noAcq` now carries the `AcqHeadCtx` premise
--   that `bad` cannot satisfy from ABOVE.  `blocked` is exactly that missing
--   premise: the `⟨ ret ⟩`-headed group `bad` governs may no longer sit under
--   any binder, so the top-level `BindCtx` of §1 (the former `top`) is gone.
module BorrowedCF.Simulation.BackwardSoup.Examples.StrictGroupGap where

open import Data.Nat.ListAction using (sum)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Types.AtomCons using (acq-;-≄ret)
open import BorrowedCF.Types.NoTerm using (NoTerm; noTerm-;-snd; ¬noTerm-end)
open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe using (NoRet)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (NoAcq; ¬noAcq-acq; noAcq-≃; noAcq-;-fst)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (GroupOf; head-group; next-group; groupOffset; groupIndex)

open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The bad `BindCtx`.

-- The innermost group governs TWO acqs and spends them on TWO handles: the
-- head `⟨ acq ⟩` and -- at offset 1 -- `⟨ acq ; end ‼ ⟩`.
inner : 𝐓.BindCtx (acq ; (acq ; end ‼)) (2 L.∷ L.[])
          (⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
inner =
  𝐓.last (𝐓.cons acq (acq ; end ‼) (λ { (() ; _) }) ≃-refl
           (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip)))

-- The `cons-ret/acq` node whose own session `s₁` SKIPS: its group is the lone
-- handle `⟨ ret ⟩` and the governing `acq` is passed on to `inner`.  Every
-- premise of `cons-ret/acq` is satisfied: `¬ Skips s₂` holds (`s₂` is
-- `acq ; end ‼`) and `AcqHeadCtx Γ₂` holds (`inner`'s head is `⟨ acq ⟩`).
-- `bad` keeps its own `acqHead` (its next group IS acq-headed) ...
bad-acqHead-ok : 𝐓.AcqHeadCtx (⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
bad-acqHead-ok = skip , ≃-sym ≃-skipʳ

bad : 𝐓.BindCtx (acq ; end ‼) (1 L.∷ 2 L.∷ L.[])
        ((⟨ ret ⟩ ∷ []) V.++ (⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ []))
bad =
  𝐓.cons-ret/acq skip ≃-skipˡ (λ { (() ; _) })
    (𝐓.cons ret skip (λ { (_ ; ()) }) (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (𝐓.nil skip))
    inner
    bad-acqHead-ok

-- Under the OLD `AcqHeadCtx` (`¬ Skips s`) `bad` was moreover reachable from a
-- `New`-derived top-level session at a `⊢ᴮ`-legal shape, by
--
--   top : 𝐓.BindCtx (skip ; end ‼) (1 ∷ 1 ∷ 2 ∷ [])
--           ((⟨ ret ⟩ ∷ []) V.++ ((⟨ ret ⟩ ∷ []) V.++ (⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])))
--   top = 𝐓.cons-ret/acq skip ≃-refl (λ ())
--           (𝐓.cons ret skip … (𝐓.nil skip)) bad (λ ())
--
-- so `TP-Res` accepted it.  That last `(λ ())` is exactly what `blocked` (§3)
-- now refutes: `bad`'s group list is headed by `⟨ ret ⟩`, which carries no
-- `acq`.  The shape and the `⊢ᴮ`/`New` data are kept as a record.
top-New : New (skip {0})
top-New = New.skip

top-⊢ᴮ : 𝐓.⊢ᴮ (1 L.∷ 1 L.∷ 2 L.∷ L.[])
top-⊢ᴮ = _ ∷ᴬ (_ ∷ᴬ []ᴬ)

------------------------------------------------------------------------
-- 2.  The refutation.

grp : GroupOf (1 L.∷ 2 L.∷ L.[]) (1 Fin.↑ʳ (1F Fin.↑ˡ 0))
grp = next-group 1 (head-group L.[] 1F)

grp-index : 0 Nat.< groupIndex grp
grp-index = Nat.s≤s Nat.z≤n

grp-offset : 0 Nat.< groupOffset grp
grp-offset = Nat.s≤s Nat.z≤n

private
  ⟨⟩≃′ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃′ ⟨ eq ⟩ = eq

-- The statement of `Position/Crux.agda`'s `nonFirstGroup-interior-noAcq`, as
-- the previous pass posed it (no `AcqHeadCtx` premise, no `⊢ᴮ`).
NonFirstGroupInteriorNoAcq : Set
NonFirstGroupInteriorNoAcq =
  ∀ {B} {Γ : Ctx (sum B)} {g : 𝕊 0} → NoAcq g → 𝐓.BindCtx (acq ; g) B Γ →
  ∀ {i} (grp : GroupOf B i) → 0 Nat.< groupOffset grp →
  Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′

refuted : ¬ NonFirstGroupInteriorNoAcq
refuted f with f {g = end ‼} NoAcq.end bad grp grp-offset
... | s′ , eq , na = ¬noAcq-acq (noAcq-;-fst (noAcq-≃ (⟨⟩≃′ (≃-sym eq)) na))

-- The offending handle is even MOBILE, so `∥/;-transmute` is free to reorder
-- it and the binder's prescribed `;`-order does not exclude it either.
interior-mobile : Mobile ⟨ acq ; end ‼ ⟩
interior-mobile = ⟨ end ‼ , end , ≃-refl ⟩

------------------------------------------------------------------------
-- 3.  What the strengthened premise blocks.

-- The `acqHead` argument of the former `top` -- whose second group is headed
-- by `⟨ ret ⟩` -- is not derivable.
blocked : ¬ 𝐓.AcqHeadCtx (⟨ ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
blocked (t , eq) = acq-;-≄ret eq

------------------------------------------------------------------------
-- 4.  A SECOND laxity, independent of the first: `mobile-head-alone`.
--
--   PLAN.md §6 argues that mobility stays sound because "a handle
--   `⟨ acq ; s′ ⟩` with `Bounded s′` carries its group's terminator; `cons`
--   forbids handles after a terminator, `AcqHeadCtx` forbids a skip handle
--   before it, so a Mobile handle is the only handle of its group".  `cons`
--   forbids handles after a SKIPS remainder, which is not the same thing:
--   `Bounded s′` is satisfied by an `end` tip as well as by a `ret` tip, and
--   a `ret` may still follow an `end`.  The group below is a legal
--   `BindCtx′` whose HEAD is Mobile and which nonetheless has a second
--   handle.

mobileGroup : 𝐓.BindCtx′ ((acq ; end ‼) ; ret) (⟨ acq ; end ‼ ⟩ ∷ ⟨ ret ⟩ ∷ [])
mobileGroup =
  𝐓.cons (acq ; end ‼) ret (λ { ((() ; _) ; _) }) ≃-refl
    (𝐓.cons ret skip (λ ()) ≃-skipʳ (𝐓.nil skip))

-- ... so "everything after a Mobile handle skips" is refutable, for a group
-- chain of exactly the `cons-ret/acq` shape `u ; ret` with `NoRet u`.
MobileHeadAlone : Set
MobileHeadAlone =
  ∀ {u s₁ s₂ : 𝕊 0} → NoRet u → Mobile ⟨ s₁ ⟩ → s₁ ; s₂ ≃ u ; ret → Skips s₂

mobile-head-alone-refuted : ¬ MobileHeadAlone
mobile-head-alone-refuted f =
  case f {u = acq ; end ‼} {s₁ = acq ; end ‼} {s₂ = ret}
         (NoRet.acq NoRet.; NoRet.end) interior-mobile ≃-refl
  of λ ()

-- THE FIX, NOW ADOPTED (`Types/NoTerm.agda`): replace `NoRet u` by `NoTerm u`
-- -- no `ret` AND no `end` -- which is exactly what a `New`-derived session
-- gives.  The witness above is `u = acq ; end ‼`, whose `end` is precisely
-- what `NoTerm` forbids, so it no longer applies; and with `NoTerm u` the
-- claim IS provable (`NoTerm.bounded-tail-skips`), which is what
-- `Position/Crux.agda`'s `mobile-head-alone` runs on.
noTerm-would-block : ¬ NoTerm {0} (acq ; end ‼)
noTerm-would-block nt = ¬noTerm-end (noTerm-;-snd nt)
