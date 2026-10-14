-- | The admin-prefix `a-acq` absorption for the multi-block backward com-reflect.
--
--   In the rescuable (second) outcome, the untyped image fires `RU-Com` on the
--   Mobile-fronted redex, giving `Q` with the `cons-acq` front's `φ acq` cell
--   still PENDING; the typed side does `R-Acq` then `R-Com`, giving `P′`; and
--   `Q ≈ U[P′]σ` must hold — the single administrative `a-acq` (= `RU-Acquire`)
--   being absorbed by `≈`.
--
--   Below: the `a-acq` generator's move IS an `≈` link (trivially, since
--   `─→ᵃ ⊆ ≈`), machine-checked at its EXACT telescoped shape.  The load-bearing
--   subtlety is whether the reflection's intermediate `Q` matches that shape —
--   see the analysis note after `aacq-absorb`.
module BorrowedCF.Simulation.Backward.AdminPrefix where

open import BorrowedCF.Prelude
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*)
open import BorrowedCF.Simulation.Support.RevAdmin using (a-acq; _≈_; ─→ᵃ⇒≈)
open UR using (Φ*)
open import BorrowedCF.Terms.Base using (Tm)

-- The `a-acq` administrative move (= untyped `RU-Acquire`) is an `≈` link, at
-- its exact telescoped shape: a `φ acq c` cell wrapping an `acq`-thread plus the
-- rest `P` collapses to the resolved channel triple with `P` unweakened.
aacq-absorb : ∀ {n k} (Φ : Φ* (2 + n) k) (F : Frame* k) (c e : Tm k) (P : UP.Proc k) → _
aacq-absorb Φ F c e P = ─→ᵃ⇒≈ (a-acq Φ F {c} {e} {P})

-- ── SHAPE-MATCH ANALYSIS (the load-bearing subtlety) ────────────────────────
--   `a-acq` above resolves a `φ acq` cell that sits at telescope depth `Φ` with
--   NOTHING after it except the `acq`-thread ∥ P.  In the reflection, the
--   `cons-acq` front is B₁'s FIRST block, so its `φ acq` cell is the OUTERMOST
--   telescope cell (`Φ = []φ` before it) with the REST of the telescope (the
--   com handle β's φ-cells) AFTER it:  `ν (φ acq c (plugΦ rest leaf))`.
--
--   • CO-LOCATED com (β = the acq handle's own continuation, i.e. the acquired
--     ν-front channel): after `RU-Com` the com-contractum sits directly inside
--     the `φ acq` cell, so `plugΦ rest leaf ≡ (acq-thread ∥ com-contractum)` and
--     `aacq-absorb` applies with `P := com-contractum`.  Absorption is a REAL ≈
--     link.  (This is the case that actually arises: R-Com fires on `0F`, the
--     just-acquired front, so the com IS at the front, co-located with the acq.)
--
--   • GENUINELY-SEPARATED com (β a strictly later channel, distinct from the
--     acq handle): the `cons-acq` `φ acq` cell is BEFORE β's telescope cells, so
--     `plugΦ rest leaf` heads with β's `φ`-cell, NOT `acq-thread ∥ P`.  Aligning
--     it with the `a-acq` shape needs the `cons-acq` `φ acq` cell COMMUTED past
--     β's cells (a `νφ`/up-to-φ reordering).  Whether that commutation is a valid
--     `≈` link is the open point gated by the linked-φ machinery.
--
--   VERDICT: the a-acq absorption is machine-confirmed as an `≈` link for the
--   `a-acq` shape (co-located case = the one the admin-prefixed R-Acq;R-Com trace
--   actually produces, since R-Acq brings the acquired channel to `0F` and R-Com
--   fires THERE).  A separated-β trace would additionally need the φ-commutation;
--   but the admin-prefixed reflection is naturally co-located, so the second
--   outcome (B) holds with `aacq-absorb` as the absorption link.
