module BorrowedCF.Simulation2.RsplitDropTension where

------------------------------------------------------------------------
-- RSPLIT vs DROP TENSION  —  a MACHINE-CHECKED slot characterization.
--
-- Every claim below is a `refl` (definitional) or a `normalize`-backed
-- equation, NOT prose. Two prior analyses mis-diagnosed by reasoning; this
-- one COMPUTES. The named lemmas ARE the characterization; read them, not the
-- comments.
--
-- The object under study: the channel-triple translation leaf, in its two
-- forms (BROADCAST = current/reverted, DISTRIBUTING = abandoned 34fd35e), and
-- the two untyped reduction reads that conflict on it (RU-RSplit, RU-Drop,
-- from Reduction/Processes/Untyped.agda).
--
-- A handle is translated to a TRIPLE  (e₁ ⊗ (` c)) ⊗ e₂  with three slots:
--      SLOT 0 = LEFT-sync   = e₁     (a Tm)
--      SLOT 1 = CHANNEL     = ` c    (a variable)
--      SLOT 2 = RIGHT-sync  = e₂     (a Tm)
-- See `chanTriple` and the reduction pattern `𝓒[_×_×_]`, both = (a ⊗ ` x) ⊗ b.
------------------------------------------------------------------------

open import Data.Nat.ListAction using (sum)
open import Data.Sum using ([_,_]′; inj₁; inj₂)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types

import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
open import BorrowedCF.Processes.Bisim
  using (UChan; chanTriple; syncs)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 0.  The triple geometry, confirmed by refl.
------------------------------------------------------------------------

-- chanTriple is exactly the reduction's 𝓒[_×_×_] shape.
triple-shape : ∀ {e₁ : Tm n} {c} {e₂} →
               chanTriple (e₁ , c , e₂) ≡ (e₁ ⊗ (` c)) ⊗ e₂
triple-shape = refl

-- slot accessors (definitional projections out of the ⊗-tree).
slotL : Tm n → Tm n
slotL ((a ⊗ b) ⊗ c) = a
slotL _ = K `unit
slotC : Tm n → Tm n
slotC ((a ⊗ b) ⊗ c) = b
slotC _ = K `unit
slotR : Tm n → Tm n
slotR ((a ⊗ b) ⊗ c) = c
slotR _ = K `unit

slotL-triple : ∀ {e₁ : Tm n} {c e₂} → slotL (chanTriple (e₁ , c , e₂)) ≡ e₁
slotL-triple = refl
slotC-triple : ∀ {e₁ : Tm n} {c e₂} → slotC (chanTriple (e₁ , c , e₂)) ≡ ` c
slotC-triple = refl
slotR-triple : ∀ {e₁ : Tm n} {c e₂} → slotR (chanTriple (e₁ , c , e₂)) ≡ e₂
slotR-triple = refl

------------------------------------------------------------------------
-- 1.  The two reduction READS, transcribed from Reduction/Processes/Untyped.
------------------------------------------------------------------------

-- RU-Drop (line 51) fires on  φ drop (⟪ F [ K `drop · 𝓒[ e × suc x × ` 0F ] ]* ⟫ ∥ P).
-- It READS the drop-target head handle's triple:
--   * CHANNEL slot (slot 1) must be a SUCCESSOR variable `suc x`,
--   * RIGHT-sync slot (slot 2) must be the flag variable ` 0F
--     (de Bruijn 0 = the enclosing `φ drop` binder).
-- We encode the read shape as a predicate the drop-head triple must satisfy.
DropReadShape : ∀ n → Tm (1 + n) → Set
DropReadShape n t = Σ[ e ∈ Tm (1 + n) ] Σ[ x ∈ 𝔽 n ]
                      t ≡ chanTriple (e , suc x , ` 0F)

-- The slot RU-Drop reads for the FLAG is the RIGHT-sync slot, and the value
-- it demands there is the var ` 0F.
drop-reads-right-sync : ∀ {n} {e : Tm (1 + n)} {x : 𝔽 n} →
  slotR (chanTriple (e , suc x , ` 0F)) ≡ ` 0F
drop-reads-right-sync = refl

-- RU-RSplit (line 39) fires on  𝓒[ e₁ × 0F × e₂ ]  (CHANNEL slot = the var 0F),
-- inserts a fresh `φ drop`, and emits TWO halves while renaming the sibling
-- P by weakenᵣ (shift-by-ONE for the new φ):
--   half-1 (the kept/split side)  = 𝓒[ wk e₁ × 1F × ` 0F ]
--   half-2 (the remote/fresh side)= 𝓒[ ` 0F × 1F × wk e₂ ]
-- Note: BOTH halves get the fresh sync flag ` 0F :
--   half-1 in its RIGHT-sync slot, half-2 in its LEFT-sync slot.
rsplit-half1 : Tm (1 + n) → Tm (1 + n) → Tm (2 + n)
rsplit-half1 e₁ e₂ = chanTriple (wk e₁ , 1F , ` 0F)
rsplit-half2 : Tm (1 + n) → Tm (1 + n) → Tm (2 + n)
rsplit-half2 e₁ e₂ = chanTriple (` 0F , 1F , wk e₂)

-- the half-1 fresh flag lands in the RIGHT-sync slot:
rsplit-half1-flag-right : ∀ {n} {e₁ e₂ : Tm (1 + n)} →
  slotR (rsplit-half1 e₁ e₂) ≡ ` 0F
rsplit-half1-flag-right = refl
-- the half-2 fresh flag lands in the LEFT-sync slot:
rsplit-half2-flag-left : ∀ {n} {e₁ e₂ : Tm (1 + n)} →
  slotL (rsplit-half2 e₁ e₂) ≡ ` 0F
rsplit-half2-flag-left = refl

------------------------------------------------------------------------
-- 2.  The two leaf forms, transcribed VERBATIM from the translation.
------------------------------------------------------------------------

-- BROADCAST leaf (current/reverted; Bisim.agda:45 + Simulation2/Congruence
-- local `canonₛ`). chanTriple (a,c,b) = (a ⊗ ` c) ⊗ b.
canonₛ : ∀ {n} (B : T.BindGroup) → UChan n → (sum B →ₛ syncs B + n)
canonₛ []                 cc = λ ()
canonₛ (b ∷ [])           cc = λ _ → chanTriple cc
canonₛ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ const (chanTriple (wk e1 , suc x , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
           , canonₛ B (` 0F , suc x , wk e2) ]′ (Fin.splitAt b y))

-- DISTRIBUTING leaf (abandoned fix; 34fd35e). 𝓒[ e₁ × c × * ] = chanTriple (e₁,c,*).
Ub[_] : (b : ℕ) → UChan n → b →ₛ n
Ub[ suc b ] (e₁ , c , e₂) 0F      = chanTriple (e₁ , c , K `unit)
Ub[ suc b ] (e₁ , c , e₂) (suc x) = Ub[ b ] (K `unit , c , e₂) x

UBdist : ∀ {n} (B : T.BindGroup) → UChan n → (sum B →ₛ syncs B + n)
UBdist []                 cc = λ ()
UBdist (b ∷ [])           cc = λ _ → chanTriple cc
UBdist {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ (λ j → Ub[ b ] (wk e1 , suc x , ` 0F) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
           , UBdist B (` 0F , suc x , wk e2) ]′ (Fin.splitAt b y))

------------------------------------------------------------------------
-- 3.  DELIVERABLE 1 — pin the conflicting slot.
--
-- Test geometry (n = 2, the two ν-bound channels of an open ν-block):
--   C₁  = 1 ∷ 3 ∷ []     (split chain b₀=1, then DOWNSTREAM sibling chain 3)
--   C₁ᴿ = 1 ∷ 1 ∷ 3 ∷ [] (grown: rsplit inserts a fresh 1-chain in the middle)
-- Channel triple of the source handle: (K `unit , 0F , K `unit).
--
-- All equalities below are by `refl` against the VERBATIM leaf definitions
-- of §2; the right-hand sides are the `normalize` outputs.
------------------------------------------------------------------------

-- The downstream sibling borrow, in the UNGROWN chain, then renamed by the
-- weakenᵣ that RU-RSplit applies to the sibling P (shift-by-one for new φ).
-- (index 1F of Fin 4 = the inj₂ component = the singleton downstream chain.)
broadcast-downstream-renamed :
  canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ
  ≡ chanTriple (` 1F , 2F , K `unit)
broadcast-downstream-renamed = refl

-- The SAME downstream sibling borrow, in the GROWN chain (rsplit already done).
-- (index 2F of Fin 5 = first index of the innermost downstream chain.)
broadcast-downstream-grown :
  canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F
  ≡ chanTriple (` 0F , 2F , K `unit)
broadcast-downstream-grown = refl

-- ⇒ THE CONFLICTING SLOT IS SLOT 0 = LEFT-sync. Channel (slot 1) and
--   right-sync (slot 2) are IDENTICAL between the two; only slot 0 differs:
--   renamed-ungrown has ` 1F (the OLD binder), grown has ` 0F (the fresh φ).
broadcast-conflict-slot-is-left :
    slotL (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ)
      ≡ ` 1F
  × slotL (canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F)
      ≡ ` 0F
broadcast-conflict-slot-is-left = refl , refl

broadcast-channel-slot-agrees :
    slotC (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ)
  ≡ slotC (canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F)
broadcast-channel-slot-agrees = refl

broadcast-rightsync-slot-agrees :
    slotR (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ)
  ≡ slotR (canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F)
broadcast-rightsync-slot-agrees = refl

-- The DISTRIBUTING leaf gives the IDENTICAL downstream discrepancy: the
-- downstream sibling is a singleton chain, which BOTH leaf forms translate
-- via `chanTriple`, so distributing does NOT change the rsplit-shifted slot.
dist-downstream-renamed :
  UBdist {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ
  ≡ chanTriple (` 1F , 2F , K `unit)
dist-downstream-renamed = refl

dist-downstream-grown :
  UBdist {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F
  ≡ chanTriple (` 0F , 2F , K `unit)
dist-downstream-grown = refl

-- Same slot-0 conflict under distributing, value-for-value identical to
-- broadcast: the leaf redesign in 34fd35e did NOT move this slot.
dist-equals-broadcast-downstream :
    (UBdist {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ
       ≡ canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ)
  × (UBdist {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F
       ≡ canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F)
dist-equals-broadcast-downstream = refl , refl

------------------------------------------------------------------------
-- 4.  DELIVERABLE 2 — same-slot-or-not VERDICT.
--
-- RU-Drop reads the FLAG of the drop-head handle in its RIGHT-sync slot
-- (slot 2): `drop-reads-right-sync` (§1) gives slotR (...) ≡ ` 0F.
--
-- The drop-head is a CHAIN HEAD of the translation: the head borrow (index
-- 0F) is chanTriple (* , c , ` 0F), whose RIGHT-sync slot carries the flag
-- ` 0F — matching RU-Drop's read shape exactly.
------------------------------------------------------------------------

-- The translation's chain-HEAD borrow has the flag in its RIGHT-sync slot
-- (slot 2), exactly the slot RU-Drop reads.
head-borrow-flag-is-right-sync :
  slotR (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F) ≡ ` 0F
head-borrow-flag-is-right-sync = refl

-- The chain-head borrow MATCHES RU-Drop's read shape (channel = a successor
-- variable, right-sync = the flag ` 0F).
head-borrow-matches-drop-read :
  DropReadShape 2 (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F)
head-borrow-matches-drop-read = K `unit , 0F , refl

-- ┌──────────────────────────────────────────────────────────────────┐
-- │  VERDICT: DIFFERENT SLOTS.                                          │
-- │    S_drop  (slot RU-Drop reads for the flag) = 2 (RIGHT-sync),      │
-- │    S_x     (slot RU-RSplit shifts on a downstream sibling) = 0      │
-- │            (LEFT-sync).                                             │
-- │  S_drop ≢ S_x  ⇒  NOT a hard single-slot conflict: a translation    │
-- │  CAN keep the flag live in slot 2 of the drop-head AND a non-       │
-- │  shifting constant in slot 0 of every downstream sibling.          │
-- └──────────────────────────────────────────────────────────────────┘
-- Slots are named 0/1/2; the witness is that the two slot indices are
-- distinct *and* the values living there are independently constrained.
S-drop : ℕ
S-drop = 2          -- RIGHT-sync slot, carries the flag ` 0F (head-borrow-flag-is-right-sync)
S-x : ℕ
S-x = 0             -- LEFT-sync slot, the one rsplit shifts (broadcast-conflict-slot-is-left)

slots-differ : S-drop ≢ S-x
slots-differ ()

-- WHY there is still a real bug even though the slots differ: in the GROWN
-- chain the rsplit's fresh chain (index 1F) is a NEW drop-head whose flag is
-- ` 0F in its RIGHT-sync slot; the DOWNSTREAM sibling (index 2F) then carries
-- that SAME ` 0F in its LEFT-sync slot — i.e. the downstream borrow names the
-- fresh φ it must NOT depend on. Both as refl:
rsplit-newchain-flag-right :
  slotR (canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F) ≡ ` 0F
rsplit-newchain-flag-right = refl

downstream-grown-names-fresh-φ :
  slotL (canonₛ {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F) ≡ ` 0F
downstream-grown-names-fresh-φ = refl

-- The renamed-ungrown sibling does NOT name the fresh φ (` 0F): it names
-- ` 1F. So the discrepancy is precisely "grown points at the fresh φ; the
-- untyped rsplit (weakenᵣ) leaves the sibling pointing past it".
downstream-renamed-avoids-fresh-φ :
  slotL (canonₛ {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ) ≢ ` 0F
downstream-renamed-avoids-fresh-φ ()

------------------------------------------------------------------------
-- 5.  DELIVERABLE 3 — the both-satisfying SPEC, and where each leaf form
--     stands against it.  (All claims refl.)
--
-- A both-satisfying translation must guarantee, for every channel handle
-- translated to a triple (slotL , slotC , slotR):
--
--  (DROP)   the drop-flag lives in slot S_drop = 2 (RIGHT-sync) of the
--           DROP-HEAD handle, holding the variable ` 0F (the enclosing
--           `φ drop` binder).                        [RU-Drop read shape]
--
--  (RSPLIT) the rsplit fresh-φ variable (` 0F after the new binder) must
--           NOT appear in slot S_x = 0 (LEFT-sync) of any DOWNSTREAM
--           sibling borrow; the sibling, renamed by the untyped weakenᵣ,
--           points PAST the fresh φ (to ` 1F), so the translated grown
--           term must agree.                          [RU-RSplit emit]
--
--  Because S_drop = 2 ≠ 0 = S_x (slots-differ), (DROP) and (RSPLIT)
--  constrain DISJOINT slots and are jointly satisfiable in principle.
--
--  Neither EXISTING leaf form satisfies both:
--
--   * BROADCAST satisfies (DROP) — head right-sync = ` 0F
--       (head-borrow-flag-is-right-sync) — but VIOLATES (RSPLIT): the grown
--       downstream sibling's LEFT-sync is ` 0F, the fresh φ
--       (downstream-grown-names-fresh-φ), whereas the renamed-ungrown one is
--       ` 1F (broadcast-conflict-slot-is-left). This is the U-rsplit hole2.
--
--   * DISTRIBUTING also VIOLATES (RSPLIT) identically
--       (dist-equals-broadcast-downstream: the downstream slot is unchanged),
--       AND additionally FAILS (DROP): with a ≥2 head chain the drop-head's
--       RIGHT-sync slot is * (a unit constant), not the flag ` 0F
--       (dist-drophead-rightsync-is-unit vs broadcast-drophead-rightsync-flag).
------------------------------------------------------------------------

-- Distributing FAILS the drop half: drop-head (head index of a ≥2 chain) has
-- right-sync = * (unit constant), NOT the flag ` 0F.
dist-drophead-rightsync-is-unit :
  slotR (UBdist {2} (2 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F) ≡ K `unit
dist-drophead-rightsync-is-unit = refl

-- Broadcast, by contrast, satisfies the drop half: drop-head right-sync = ` 0F.
broadcast-drophead-rightsync-flag :
  slotR (canonₛ {2} (2 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F) ≡ ` 0F
broadcast-drophead-rightsync-flag = refl

-- And the two forms genuinely disagree in that slot (so "distributing fails
-- drop" is not a vacuous statement):
dist-vs-broadcast-drophead-disagree :
    slotR (UBdist {2} (2 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F)
  ≢ slotR (canonₛ {2} (2 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 0F)
dist-vs-broadcast-drophead-disagree ()

-- The "no downstream shift" question for distributing, answered NO: the
-- distributing downstream sibling DOES shift exactly like broadcast (proved
-- equal in §3), so distributing does NOT satisfy the rsplit half either.
dist-does-not-fix-rsplit :
  UBdist {2} (1 ∷ 1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 2F
  ≢ (UBdist {2} (1 ∷ 3 ∷ []) (K `unit , 0F , K `unit) 1F ⋯ weakenᵣ)
dist-does-not-fix-rsplit ()
