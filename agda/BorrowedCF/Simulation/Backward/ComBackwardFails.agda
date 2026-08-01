-- | DECISIVE SETTLEMENT of the multi-block backward-com question (verdict A).
--
--   QUESTION.  Backward simulation would require: whenever the UNTYPED image
--   `U[ P ]` fires `RU-Com`, the well-typed source `P` can (after admin steps)
--   fire `R-Com`.  The threat to this is a "separated firing com": an
--   `RU-Com` on the untyped image whose send sits, on the TYPED side, at a
--   NON-front channel (`toℕ ≠ 0`) behind a MOBILE front — so that `R-Com`
--   (whose send is forced to typed `0F`) cannot fire and no admin step relocates
--   it.  If such a well-typed `P` existed, backward-com would be FALSE over
--   arbitrary well-typed `P` (verdict B).
--
--   STEP 2 IS NOT THE OBSTRUCTION.  In `U[ ν B1 B2 P ] σ` (Processes/Translation)
--   every channel of a bind group `B1` is mapped by `Ub[_]`/`UB[_]` to the SAME
--   underlying untyped data channel — the ν's `0F`, shifted through the φ-nest as
--   `wkΦ Φ 0F` (blocks differ only in their φ sync cells).  Hence `RU-Com`
--   (Reduction/Processes/Untyped) fires on `plugΦ Φ (⟪send on wkΦ Φ 0F⟫ ∥ ...)`
--   for a send on ANY B1 channel, regardless of its typed index or the front
--   φ-cell's flag.  So the untyped image genuinely steps; the linchpin is instead
--   whether a well-typed source can PLACE that send behind a mobile front.
--
--   STEP 1 IS THE OBSTRUCTION (this module).  It cannot.  A `ν` carries a `New`
--   session `s` (Predicates.New: no `acq`/`ret`/`end` internally), so a mobile
--   front — which must be `acq`-headed with a `Bounded` continuation (Mobile ⟨s⟩
--   ⇒ s ≃ acq ; w, Bounded w) — can only arise as the borrower block of a
--   `cons-acq` marker, whose block session is `acq ; (s ; end p)`.  We prove
--   that in such a block a mobile front CONSUMES THE WHOLE BLOCK: anything
--   strictly behind it `Skips` (carries no com).  The mechanism is
--   `New ∩ Bounded = ∅`, discharged WITHOUT any left-cancellation postulate —
--   the existing `atom-;-unsnoc` peels the trailing atoms until the residual
--   forces the front `≃ acq` (a non-Bounded, hence non-mobile, session).
--
--   VERDICT (A): the separated firing com is NOT a well-typed reachable image;
--   the RU-Com send is always co-located at its block's front, so `R-Com` fires
--   (after resolving any leading `cons-acq` marker by `R-Acq`, whose untyped
--   mirror is `RU-Acquire`).  Backward-com holds; it needs no
--   forward-reachability restriction on THIS ground.
module BorrowedCF.Simulation.Backward.ComBackwardFails where

open import BorrowedCF.Prelude

open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded; skips⊥bounded; ≃-bounded)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed using (BindCtx′)
open BindCtx′

------------------------------------------------------------------------
-- ROOT: a session is never simultaneously New and Bounded.
--   (New's leaves are `-`/msg/skip; Bounded's leaves are end/ret.)
------------------------------------------------------------------------

new∧bounded⇒⊥ : {n : ℕ} {s : 𝕊 n} -> New s -> Bounded s -> ⊥
new∧bounded⇒⊥ (P._;_ N1 _) (P._;₁_ B _) = new∧bounded⇒⊥ N1 B
new∧bounded⇒⊥ (P._;_ _ N2) (P.-;₂_ B)   = new∧bounded⇒⊥ N2 B
new∧bounded⇒⊥ (P.mu N)     (P.mu B)      = new∧bounded⇒⊥ N B
new∧bounded⇒⊥ (P.brn N1 _) (P.brn B1 _)  = new∧bounded⇒⊥ N1 B1

------------------------------------------------------------------------
-- A mobile channel's session is Bounded, hence never New.
------------------------------------------------------------------------

mobile⇒bounded : {s : 𝕊 zero} -> Mobile ⟨ s ⟩ -> Bounded s
mobile⇒bounded (P.⟨ w , Bw , eq ⟩) = ≃-bounded (≃-sym eq) (P.-;₂_ Bw)

mobile⇒¬new : {s : 𝕊 zero} -> Mobile ⟨ s ⟩ -> ¬ (New s)
mobile⇒¬new mob Ns = new∧bounded⇒⊥ Ns (mobile⇒bounded mob)

------------------------------------------------------------------------
-- Small absurdities used by the unsnoc cascade.
------------------------------------------------------------------------

notB-acq : ¬ (Bounded (acq {zero}))
notB-acq ()

notB-acqmsg : ¬ (Bounded (acq {zero} ; msg ‼ `⊤))
notB-acqmsg (P._;₁_ () _)
notB-acqmsg (P.-;₂_ ())

skips-;-projl : {s1 s2 : 𝕊 zero} -> Skips (s1 ; s2) -> Skips s1
skips-;-projl (sk ; _) = sk

------------------------------------------------------------------------
-- MOB-WHOLE (canonical com session `msg `⊤`).  A mobile front over the
-- New-ν borrower block `acq ; (msg `⊤ ; end p)` leaves only `Skips`
-- behind it.  Proof: peel trailing atoms with `atom-;-unsnoc`; every
-- deeper branch forces the front `≃ acq` / `≃ acq;msg` / `Skips` — each
-- contradicts `Bounded s_a`.  No leading-atom cancellation is used.
------------------------------------------------------------------------

whole-aux : {sa sb : 𝕊 zero} {p : Pol} ->
  Bounded sa ->
  (sa ; sb) ≃ ((acq ; (msg ‼ `⊤)) ; end p) ->
  Skips sb
whole-aux Bsa e with atom-;-unsnoc end e
... | inj₁ Sk = Sk
... | inj₂ (_ , e2 , _) with atom-;-unsnoc msg e2
...   | inj₁ Sk' = ⊥-elim (notB-acqmsg (≃-bounded (≃-trans (≃-sym (≃-skipsʳ Sk')) e2) Bsa))
...   | inj₂ (_ , e3 , _) with atom-;-unsnoc acq (≃-trans e3 (≃-sym ≃-skipˡ))
...     | inj₁ Sk'' = ⊥-elim (notB-acq (≃-bounded (≃-trans (≃-sym (≃-skipsʳ Sk'')) e3) Bsa))
...     | inj₂ (_ , e4 , _) = ⊥-elim (skips⊥bounded (skips-;-projl (≃-skips (≃-sym e4) skip)) Bsa)

mob-front-whole : {sa sb : 𝕊 zero} {p : Pol} ->
  Mobile ⟨ sa ⟩ ->
  (sa ; sb) ≃ (acq ; (msg ‼ `⊤ ; end p)) ->
  Skips sb
mob-front-whole mob eq =
  whole-aux (mobile⇒bounded mob) (≃-trans eq (≃-sym ≃-assoc-;))

------------------------------------------------------------------------
-- DECISIVE: the `BindCtx′` block a separated-firing com would require is
-- UNINHABITED.  For the New-ν borrower block `acq ; (msg `⊤ ; end p)`,
-- no split has a MOBILE front channel `⟨sa⟩` with a LIVE (`¬ Skips`)
-- channel `⟨sb⟩` strictly behind it.  Hence the well-typed source of a
-- separated com cannot be typed: construction fails at step (1).
------------------------------------------------------------------------

sep-block-impossible :
  {k : ℕ} {sa sb : 𝕊 zero} {p : Pol} {G : Ctx k} ->
  Mobile ⟨ sa ⟩ ->
  ¬ (Skips sb) ->
  ¬ (BindCtx′ (acq ; (msg ‼ `⊤ ; end p)) (⟨ sa ⟩ ∷ ⟨ sb ⟩ ∷ G))
sep-block-impossible mob notSb (cons _ s2 _ split (cons _ s3 _ split2 _)) =
  notSb (skips-;-projl
    (mob-front-whole mob (≃-trans (≃-; ≃-refl split2) split)))
