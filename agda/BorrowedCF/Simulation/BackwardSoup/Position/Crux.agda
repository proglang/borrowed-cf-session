{-# OPTIONS --allow-unsolved-metas #-}

-- | Phase 3, THE CRUX (`BackwardSoup/PLAN.md` §9, P3).
--
--   `Position.agda` STATES the metatheorem (`ImpureRedexHead`,
--   `PairArgRedexHead`, `DropFirstGroupSingleton`, `AcqNonFirstGroupHead`)
--   and proves all its combinatorial ingredients; it loads with 0 goals.
--   This module is the proof attempt.
--
--   CURRENT STATE (this pass).  The piece of NEW THEORY the previous pass
--   isolated as THE GAP -- a FRONT-atom peel for `acq`, dual to what
--   `Types/AtomUnsnoc.agda` builds for the LAST atom -- is now BUILT and
--   hole-free, in `Types/AtomCons.agda`: `Cons a w z` witnesses `w ≃ a ; z`,
--   `≃-cons` transports it, and `atom-;-cons` (`acq-;-split` at `acq`) splits
--   `s₁ ; s₂ ≃ acq ; t` into "the `acq` is at the front of `s₁`" or "`s₁`
--   skips and the `acq` is at the front of `s₂`".  With it,
--   `nonFirstGroup-interior-noAcq` and `acq-non-first-group-head` are PROVED
--   here -- modulo ONE hole, `acqHeadCtx⇒acqHeaded` (§1a).
--
--   ★ THAT HOLE IS NOT FILLABLE, AND THE REASON IS A GAP IN
--     `Processes/Typed.agda`, NOT IN THIS PROOF. ★
--
--   `Examples/StrictGroupGap.agda` (NEW, 0 goals, no pragma) machine-checks
--   two counterexamples to the metatheorem as `BindCtx` currently stands:
--
--     * `refuted`: `cons-ret/acq` still admits `s₁ ≡ skip` -- a group that
--       does no work and hands its `acq` on -- so a `⊢ᴮ`-legal group list
--       reachable from a `New`-derived session can govern `acq ; acq ; ⋯` and
--       put an ACQ-HEADED handle at offset 1 of a group.  That refutes
--       `nonFirstGroup-interior-noAcq` as the previous pass stated it, hence
--       `AcqNonFirstGroupHead`, and (through the same `⟨ ret ⟩`-headed
--       non-first group) `ImpureRedexHead` for `drop`.
--       FIX: `AcqHeadCtx` must say what its own doc comment says --
--       `AcqHeadCtx (⟨ s ⟩ ∷ _) = Σ[ t ] (s ≃ acq ; t)` instead of
--       `¬ Skips s`.  Everything in §1a below is written against exactly that
--       (`AcqHeaded`), so the change turns `acqHeadCtx⇒acqHeaded` into `id`.
--
--     * `mobile-head-alone-refuted`: `Bounded s′` in `Mobile ⟨ acq ; s′ ⟩` is
--       satisfied by an `end` tip as well as a `ret` tip, and `cons` only
--       forbids handles after a SKIPS remainder, so a Mobile handle need NOT
--       be the last of its group (`mobileGroup` is a legal `BindCtx′` with a
--       Mobile head and a second handle).  `mobile-head-alone`, which
--       `impure-redex-head`'s "same group, non-first" branch needs in order to
--       apply `before-mono-≼` against a group head that may itself be Mobile,
--       is therefore FALSE too, and PLAN.md §6's mobility-soundness argument
--       needs a matching premise (a group's terminator must end the group).
--
--   §1a-§1d are general-purpose, PROVED infrastructure: `first-group-noAcq`
--   (a witness-exposing generalisation of `Position.first-group-¬mobile`),
--   the `acq` peel (`acq-peel`, `bindCtx′-acq-interior`, `consRetAcq-peel`),
--   `TypeWalk` (a generic walker propagating a `≃`-fact about a fixed global
--   variable from its own thread's typing up through a resolved `Binder`'s
--   `below`), `acq-handle-≃acq`/`Q-acq-type`/`Q-drop-type` (domain extraction
--   for `acq`/`drop`, mirroring `Support.Theorems.DropShape`'s
--   `drop-handle-≃ret`), and `dropGroupShape`.
--
--   PROVED HERE ORIGINALLY, as the (iv)-ingredient: for the impure constants
--   whose domain session carries no `acq` -- `discard : ⟨ skip ⟩`,
--   `drop : ⟨ ret ⟩`, `recv : ⟨ msg ⁇ T ⟩`, `end p : ⟨ end p ⟩` -- the
--   consumed handle is NOT MOBILE, hence `∥′-tm-;` can never reorder it and
--   `before-mono-≼` applies to it directly.  (`select`/`branch` consume a
--   `⟨ brn p s₁ s₂ ⟩`; `Types/AtomCons.agda`'s `¬cons-brn` now settles those
--   too, an atom never sitting in front of a `brn`.  `send` consumes a PAIR,
--   and `Position.pair-arg-not-var` is what handles that case.)
module BorrowedCF.Simulation.BackwardSoup.Position.Crux where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓

import Data.List.Relation.Unary.All as Allᴸ

open import BorrowedCF.Types.AtomCons
  using (acq-;-split; acq-;-¬skips; acq-;-≄ret)
open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; ¬noRet-ret; noRet-;-fst
        ; RetTip; noRet-front-cons; retTip-Sc-skips; retTip-≃ )
open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (drop-handle-≃ret)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position

open 𝐓 using
  ( BindGroup; BindCtx; BindCtx′; AcqHeadCtx; structBinder; structNSeq
  ; last; cons-ret/acq; cons-acq; nil; cons
  ; _;_⊢ₚ_; inv-ν; inv-∥; inv-⟪⟫ )

open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The impure constants with an `acq`-free domain session.

data NoAcqDomain : Const → Set where
  `discard : NoAcqDomain `discard
  `drop    : NoAcqDomain `drop
  `recv    : NoAcqDomain `recv
  `end     : ∀ {p} → NoAcqDomain (`end p)

private
  fn-dom-noAcq :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    NoAcqDomain c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] (⟨ s ⟩ ≃ Tᵈ) × NoAcq s
  fn-dom-noAcq `discard (T-Const `discard) = skip , ≃-refl , skip
  fn-dom-noAcq `drop (T-Const `drop) = ret , ≃-refl , ret
  fn-dom-noAcq `recv (T-Const (`recv {T = T} _)) = msg ⁇ T , ≃-refl , msg
  fn-dom-noAcq `end (T-Const `end) = end _ , ≃-refl , end
  fn-dom-noAcq nd (T-Conv (dom≃ `→ _) _ d) =
    let s , eq , na = fn-dom-noAcq nd d in s , ≃-trans eq dom≃ , na
  fn-dom-noAcq nd (T-Weaken _ d) = fn-dom-noAcq nd d

  handle-noAcq-app :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {d} {T ϵ} →
    NoAcqDomain c → Γ ; γ ⊢ K c ·⟨ d ⟩ (` x) ∶ T ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ s ⟩) × NoAcq s
  handle-noAcq-app nd (T-AppUnr _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppLin _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppLeft _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppRight _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-Conv _ _ d) = handle-noAcq-app nd d
  handle-noAcq-app nd (T-Weaken _ d) = handle-noAcq-app nd d

-- PROVED.  The handle such a constant consumes is not mobile, so
-- `before-mono-≼` may be applied to it (ingredient (iii)/(iv) of the sketch).
impure-handle-noAcq :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {T ϵ} →
  NoAcqDomain c → Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ →
  Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ s ⟩) × NoAcq s
impure-handle-noAcq = handle-noAcq-app

impure-handle-¬mobile :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {T ϵ} →
  NoAcqDomain c → Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ → ¬ Mobile (Γ ﹫ x)
impure-handle-¬mobile nd ⊢app mob
  with impure-handle-noAcq nd ⊢app
... | s , eq , na = ¬mobile-noAcq na (mobile-≃ eq mob)

------------------------------------------------------------------------
-- 1a.  NoAcq witnesses, and the FRONT-ATOM PEEL for `acq`.
--
--   `first-group-noAcq` generalises `Position.first-group-¬mobile` to expose
--   the WITNESS session, needed to contradict `Γ ﹫ x ≃ ⟨ acq ; s ⟩` directly
--   (via `noAcq-;-fst` / `¬noAcq-acq`) without going through `Mobile`'s
--   `Bounded` side condition at all.
--
--   `Types/AtomCons.agda` (NEW, hole-free) supplies what the previous pass
--   recorded as THE GAP: the FRONT-atom dual of `Types/AtomUnsnoc.agda`'s
--   `atom-;-unsnoc`.  `acq-;-split` says that in `s₁ ; s₂ ≃ acq ; g` the `acq`
--   sits ENTIRELY inside ONE factor, at THAT factor's own front: either `s₁`
--   skips and `s₂ ≃ acq ; g`, or `s₁ ≃ acq ; h` with `h ; s₂ ≃ g` -- and then
--   `NoAcq g` yields `NoAcq h` and `NoAcq s₂` at once.  (`Cons` needs no `brn`
--   constructor, because `_;_` distributes over `brn` only on the RIGHT; that
--   is what makes the front peel much shorter than `AtomUnsnoc`.)

private
  bindCtx′-noAcq : ∀ {n} {Γ : Ctx n} {s : 𝕊 0} → NoAcq s → BindCtx′ s Γ →
    (z : 𝔽 n) → Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ z) ≃ ⟨ s′ ⟩) × NoAcq s′
  bindCtx′-noAcq NAs (cons s₁ s₂ _ s-split C) zero =
    s₁ , ≃-refl , noAcq-;-fst (noAcq-≃ (≃-sym s-split) NAs)
  bindCtx′-noAcq NAs (cons s₁ s₂ _ s-split C) (suc z) =
    bindCtx′-noAcq (noAcq-;-snd (noAcq-≃ (≃-sym s-split) NAs)) C z

  first-group-noAcq :
    ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
    New s → BindCtx (s ; end p) B Γ →
    ∀ {i} (g : GroupOf B i) → groupIndex g ≡ 0 →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
  first-group-noAcq N (last C) {i} g idx = bindCtx′-noAcq (new-end⇒noAcq N) C i
  first-group-noAcq {Γ = Γ} N (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front _ _)
    (head-group B′ q) idx =
    let s′ , eq , na = bindCtx′-noAcq (noAcq-front (new-end⇒noAcq N) s≃) front q
    in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ˡ Γ₁ Γ₂ q)) eq , na
  first-group-noAcq N (cons-acq C _) (head-group B′ ()) idx

------------------------------------------------------------------------
-- ★ THE ONE REMAINING GAP ★  --  and it is a GAP IN `Processes/Typed.agda`,
-- not in this proof: `AcqNonFirstGroupHead` is FALSE for `BindCtx` as it
-- stands.  See `Examples/StrictGroupGap.agda` for the machine-checked
-- counterexample and the recommended premise change.
--
-- `AcqHeaded Γ` says what `Processes/Typed.agda`'s `AcqHeadCtx` DOC COMMENT
-- says -- "the first bound handle of a non-first group must carry the group's
-- `acq`" -- rather than what its DEFINITION says (the strictly weaker
-- `¬ Skips s`).  Everything below is proved from `AcqHeaded`; the single
-- unfilled hole is the step from the one to the other.  With `AcqHeadCtx`
-- redefined as
--
--     AcqHeadCtx (⟨ s ⟩ ∷ _) = Σ[ t ∈ 𝕊 0 ] (s ≃ acq ; t)
--     AcqHeadCtx _           = ⊥
--
-- the hole is discharged by `id` and this module's `acq-non-first-group-head`
-- becomes hole-free.

AcqHeaded : ∀ {n} → Ctx n → Set
AcqHeaded (⟨ s ⟩ ∷ _) = Σ[ t ∈ 𝕊 0 ] (s ≃ acq ; t)
AcqHeaded _ = ⊥

acqHeadCtx⇒acqHeaded : ∀ {n} {Γ : Ctx n} → AcqHeadCtx Γ → AcqHeaded Γ
acqHeadCtx⇒acqHeaded = {!!}   -- HOLE 0 (FALSE as `AcqHeadCtx` stands)

private
  -- The peel itself, in the form the `BindCtx` chains use.
  acq-peel : ∀ {n} {s₁ s₂ g : 𝕊 n} → NoAcq g → ¬ Skips s₁ → s₁ ; s₂ ≃ acq ; g →
    (Σ[ h ∈ 𝕊 n ] (s₁ ≃ acq ; h) × NoAcq h) × NoAcq s₂
  acq-peel NAg ¬sk split with acq-;-split split
  ... | inj₁ (Sk , _) = ⊥-elim (¬sk Sk)
  ... | inj₂ (h , eq , hs≃g) =
    let NAhs = noAcq-≃ (≃-sym hs≃g) NAg
    in (h , eq , noAcq-;-fst NAhs) , noAcq-;-snd NAhs

  -- Every NON-HEAD handle of an acq-headed group is acq-free: the head takes
  -- the whole `acq`, and `acq-peel` leaves a `NoAcq` remainder for the rest of
  -- the `BindCtx′` chain.
  bindCtx′-acq-interior :
    ∀ {n} {Γ : Ctx (suc n)} {g : 𝕊 0} → NoAcq g → BindCtx′ (acq ; g) Γ →
    AcqHeaded Γ → (z : 𝔽 n) →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ suc z) ≃ ⟨ s′ ⟩) × NoAcq s′
  bindCtx′-acq-interior NAg (cons s₁ s₂ _ split C′) (t , u≃) z =
    bindCtx′-noAcq (proj₂ (acq-peel NAg (λ Sk → acq-;-¬skips Sk u≃) split)) C′ z

  -- At a `cons-ret/acq` node under an acq-headed context the `acq` goes to the
  -- node's OWN group: `acq-;-split`'s first alternative (`Skips s₁`, the acq
  -- escaping into the rest) would make the group's session `≃ ret`, and its
  -- head handle is acq-headed, so `ret ≃ acq ; ⋯` -- refuted by `acq-;-≄ret`.
  consRetAcq-peel :
    ∀ {n k} {Γ₁ : Ctx n} {Γ₂ : Ctx k} {s₁ s₂ g : 𝕊 0} →
    NoAcq g → s₁ ; s₂ ≃ acq ; g → BindCtx′ (s₁ ; ret) Γ₁ → AcqHeaded (Γ₁ ⸴* Γ₂) →
    AcqHeaded Γ₁
      × (Σ[ h ∈ 𝕊 0 ] (s₁ ; ret ≃ acq ; (h ; ret)) × NoAcq (h ; ret))
      × NoAcq s₂
  consRetAcq-peel NAg s≃ (nil (_ ; ())) ah
  consRetAcq-peel NAg s≃ (cons u₁ u₂ _ split C″) (t , u≃) with acq-;-split s≃
  ... | inj₂ (h , s₁≃ , hs≃g) =
    let NAhs = noAcq-≃ (≃-sym hs≃g) NAg in
    (t , u≃)
      , (h , ≃-trans (≃-; s₁≃ ≃-refl) ≃-assoc-; , (noAcq-;-fst NAhs NoAcq.; NoAcq.ret))
      , noAcq-;-snd NAhs
  ... | inj₁ (Sk , _) =
    ⊥-elim (acq-;-≄ret (≃-trans (≃-sym (≃-trans split (≃-skipsˡ Sk)))
                                (≃-trans (≃-; u≃ ≃-refl) ≃-assoc-;)))

-- PROVED (from `AcqHeaded`).  An interior handle -- offset > 0 in its group --
-- of a group list governed by `acq ; g` with `g` acq-free carries no `acq`.
-- `Allᴸ.All NonZero B` (i.e. `⊢ᴮ` of the enclosing list) rules out the
-- `cons-acq` node, whose empty group would stack a SECOND `acq` in front of
-- the governing session.
nonFirstGroup-interior-noAcq :
  ∀ {B} {Γ : Ctx (sum B)} {g : 𝕊 0} → NoAcq g → BindCtx (acq ; g) B Γ →
  AcqHeaded Γ → Allᴸ.All NonZero B →
  ∀ {i} (grp : GroupOf B i) → 0 Nat.< groupOffset grp →
  Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
nonFirstGroup-interior-noAcq NAg (last C) ah nz (head-group _ (suc j)) 0<off =
  bindCtx′-acq-interior NAg C ah (j ↑ˡ 0)
nonFirstGroup-interior-noAcq NAg (last C) ah nz (head-group _ zero) ()
nonFirstGroup-interior-noAcq NAg (last C) ah nz (next-group _ ()) 0<off
nonFirstGroup-interior-noAcq NAg
  (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest ah′) ah nz
  (head-group B′ (suc q)) 0<off
  with consRetAcq-peel NAg s≃ front ah
... | ah₁ , (h , frontEq , NAhret) , _ =
  let s′ , eq , na = bindCtx′-acq-interior NAhret (𝐓.bindCtx′-≃ frontEq front) ah₁ q
  in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ˡ Γ₁ Γ₂ (suc q))) eq , na
nonFirstGroup-interior-noAcq NAg
  (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest ah′) ah nz
  (head-group B′ zero) ()
nonFirstGroup-interior-noAcq NAg
  (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest ah′) ah nz
  (next-group n g′) 0<off
  with consRetAcq-peel NAg s≃ front ah
... | _ , _ , NAs₂ =
  let s′ , eq , na =
        nonFirstGroup-interior-noAcq NAs₂ rest (acqHeadCtx⇒acqHeaded ah′)
          (Allᴸ.tail nz) g′ 0<off
  in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) eq , na
nonFirstGroup-interior-noAcq NAg (cons-acq C ah′) ah nz grp 0<off =
  ⊥-elim (case Nat.>-nonZero⁻¹ 0 ⦃ Allᴸ.head nz ⦄ of λ ())

-- The composite for a LATER group's interior (offset > 0): descend past
-- however many groups precede `grp`'s own group, landing on
-- `nonFirstGroup-interior-noAcq` once `groupIndex grp` is confirmed `> 0`.
-- `⊢ᴮ (b ∷ B)` IS `Allᴸ.All NonZero B`, so it is passed on unchanged.
private
  laterGroup-interior-noAcq :
    ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} → New s →
    BindCtx (s ; end p) B Γ → 𝐓.⊢ᴮ B →
    ∀ {i} (grp : GroupOf B i) →
    0 Nat.< groupIndex grp → 0 Nat.< groupOffset grp →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
  laterGroup-interior-noAcq N (last C) ⊢B (head-group B′ j) () 0<off
  laterGroup-interior-noAcq N (last C) ⊢B (next-group _ ()) 0<gi 0<off
  laterGroup-interior-noAcq {Γ = Γ} N
    (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest ah)
    ⊢B (next-group n g′) 0<gi 0<off =
    let s′ , eq , na =
          nonFirstGroup-interior-noAcq
            (noAcq-;-snd (noAcq-≃ (≃-sym s≃) (new-end⇒noAcq N))) rest
            (acqHeadCtx⇒acqHeaded ah) ⊢B g′ 0<off
    in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) eq , na
  laterGroup-interior-noAcq N (cons-ret/acq s₁ s≃ _ front rest ah) ⊢B
    (head-group B′ j) () 0<off
  laterGroup-interior-noAcq N (cons-acq C ah) ⊢B (next-group .0 g′) 0<gi 0<off =
    nonFirstGroup-interior-noAcq (new-end⇒noAcq N) C (acqHeadCtx⇒acqHeaded ah) ⊢B g′ 0<off

------------------------------------------------------------------------
-- 1b.  A generic walker: propagate a `≃`-fact about the fixed global
--      variable `x` from the deepest typing of `Q` (the thread it sits in)
--      up through a `ProcessContext`.  The channel context `Γ` is untouched
--      by `TP-Par`/`TP-Weaken` (only the struct changes) and only GROWS, by
--      prefixing, at `TP-Res`; `weakenThrough` tracks exactly which
--      position in the growing vector is `x`, so the fact transports
--      unconditionally -- no linearity/`Mobile` side condition needed,
--      unlike `Position.ContextOrder`'s `count`/`before` walk.

private
  module TypeWalk {k : ℕ} (Q : 𝐓.Proc k) (x : 𝔽 k) (wrap : 𝕊 0 → 𝕊 0)
    (Q-type : ∀ {Γ : Ctx k} {γ : Struct k} →
              Γ ; γ ⊢ₚ Q → Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ wrap s′ ⟩))
    where

    ctx-type :
      ∀ {n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n} →
      Γ ; γ ⊢ₚ plug below Q →
      (y : 𝔽 n) → weakenThrough below y ≡ x →
      Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ y) ≃ ⟨ wrap s′ ⟩)
    ctx-type hole ⊢P y refl = Q-type ⊢P
    ctx-type (par-left ctx P₂) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , ⊢left , _ = ctx-type ctx ⊢left y eq
    ctx-type (par-right P₁ ctx) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , _ , ⊢right = ctx-type ctx ⊢right y eq
    ctx-type (bind B₁ B₂ ctx) {Γ} ⊢P y eq with inv-ν ⊢P
    ... | Γ₁ , Γ₂ , _ , _ , _ , _ , _ , _ , _ , ⊢body =
      let s′ , eq′ = ctx-type ctx ⊢body ((sum B₁ + sum B₂) ↑ʳ y) eq
      in s′ , subst (_≃ ⟨ wrap s′ ⟩) (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ y) eq′

------------------------------------------------------------------------
-- 1c.  `acq`'s domain, extracted (mirrors `DropShape.drop-handle-≃ret`),
--      and the small arithmetic/type glue `acq-non-first-group-head` needs.

private
  fn-acq-dom : ∀ {n} {Γ : Ctx n} {β : Struct n} {Tᵈ U a ϵ} →
    Γ ; β ⊢ K `acq ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] (⟨ acq ; s ⟩ ≃ Tᵈ)
  fn-acq-dom (T-Const `acq) = _ , ≃-refl
  fn-acq-dom (T-Conv (dom≃ `→ _) _ d) = let s , eq = fn-acq-dom d in s , ≃-trans eq dom≃
  fn-acq-dom (T-Weaken _ d) = fn-acq-dom d

  acq-handle-≃acq : ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {U ϵ} →
    Γ ; γ ⊢ K `acq ·¹ (` x) ∶ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; s ⟩)
  acq-handle-≃acq (T-AppUnr _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in s , ≃-trans (arg-type ⊢arg) (≃-sym eq)
  acq-handle-≃acq (T-AppLin _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in s , ≃-trans (arg-type ⊢arg) (≃-sym eq)
  acq-handle-≃acq (T-Conv _ _ d) = acq-handle-≃acq d
  acq-handle-≃acq (T-Weaken _ d) = acq-handle-≃acq d

  Q-acq-type : ∀ {k} (E : Frame* k) (x : 𝔽 k) →
    ∀ {Γ : Ctx k} {γ : Struct k} →
    Γ ; γ ⊢ₚ 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; s′ ⟩)
  Q-acq-type E x ⊢Q =
    let ⊢e = inv-⟪⟫ ⊢Q
        _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole = ⊢[]*⁻¹ E (K `acq ·¹ (` x)) ⊢e
    in acq-handle-≃acq ⊢hole

  Q-drop-type : ∀ {k} (E : Frame* k) (x : 𝔽 k) →
    ∀ {Γ : Ctx k} {γ : Struct k} →
    Γ ; γ ⊢ₚ 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ ret ⟩)
  Q-drop-type E x ⊢Q =
    let ⊢e = inv-⟪⟫ ⊢Q
        _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole = ⊢[]*⁻¹ E (K `drop ·¹ (` x)) ⊢e
    in ret , drop-handle-≃ret ⊢hole

  ⟨⟩≃′ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃′ ⟨ eq ⟩ = eq

  -- `x`'s ACTUAL session, `≃ ⟨ acq ; s ⟩`, cannot ALSO be NoAcq.
  acq-vs-noAcq : ∀ {s a : 𝕊 0} → NoAcq a → a ≃ acq ; s → ⊥
  acq-vs-noAcq NAa eq = ¬noAcq-acq (noAcq-;-fst (noAcq-≃ eq NAa))

  0≢⇒0< : ∀ {n : ℕ} → n ≢ 0 → 0 Nat.< n
  0≢⇒0< {zero} ne = ⊥-elim (ne refl)
  0≢⇒0< {suc n} ne = Nat.s≤s Nat.z≤n

------------------------------------------------------------------------
-- 1d.  `drop`'s group shape, generalised off `Support.Theorems.DropShape`'s
--      canonical `0F` position.  This is PURELY `BindCtx`-level (no term
--      syntax at all): the ORIGINAL `drop-b₁-zero`/`drop-B₁-cons` interleave
--      this argument with `strengthen-frame`/`inv-⟪⟫`/`inv-∥` purely to dig
--      the hole's typing (`Γ ﹫ 0F ≃ ⟨ ret ⟩`) out of the canonical term
--      shape `ν (suc b₁ ∷ B₁) B₂ (⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫
--      ∥ (P ⋯ₚ weakenᵣ))`; once that fact is available some OTHER way (here:
--      `Position.binderTyping` + §1b's `TypeWalk`, at whatever index `resolve`
--      names, not literally `0F`), the REST of the argument is identical.
--      Ready to discharge `?2` once `?0` supplies `HeadOfFirstGroup`.

private
  dropGroupShape :
    ∀ {b₁ B′} {Δ₁ : Ctx (sum (suc b₁ ∷ B′))} {s p} → New s →
    BindCtx (s ; end p) (suc b₁ ∷ B′) Δ₁ →
    (Δ₁ ﹫ (zero ↑ˡ sum B′)) ≃ ⟨ ret ⟩ →
    (b₁ ≡ 0) × (B′ ≢ [])
  dropGroupShape {b₁} {[]} N (last (cons s₁ s₂ ¬sk s-split rest)) head≃ret =
    ⊥-elim (¬noRet-ret (noRet-≃ (⟨⟩≃′ head≃ret)
      (noRet-;-fst (noRet-≃ (≃-sym s-split) (NoRet._;_ (new⇒noRet N) NoRet.end)))))
  dropGroupShape {zero} {c₀ ∷ B″} N C head≃ret = refl , (λ ())
  dropGroupShape {suc b₁} {c₀ ∷ B″} N
    (cons-ret/acq sh {s₂} frontSplit _ (cons s₁ʰ s₂ʰ ¬sk₁ s≃₁ (cons _ _ ¬skTail _ _)) _ _)
    head≃ret =
    ⊥-elim (¬skTail (retTip-Sc-skips retTipBorrow (⟨⟩≃′ head≃ret)))
    where
    noRet-sh : NoRet sh
    noRet-sh = noRet-;-fst (noRet-≃ (≃-sym frontSplit) (NoRet._;_ (new⇒noRet N) NoRet.end))
    retTipBorrow : RetTip (s₁ʰ ; s₂ʰ)
    retTipBorrow = retTip-≃ (≃-sym s≃₁) (noRet-front-cons noRet-sh)

------------------------------------------------------------------------
-- 2.  THE REMAINING HOLES.
--
-- Each is exactly the statement of the corresponding `Position.*` type.
-- Everything they need is available:
--
--   * `Position.resolve` / `Binder`             -- which `ν` binds the handle;
--   * `Position.structBinder-before`,
--     `Position.group-head-before`              -- the order the binder
--                                                  PRESCRIBES inside a group;
--   * `Position.first-group-¬mobile`,
--     `impure-handle-¬mobile` above             -- immobility of the handles
--                                                  the comparison mentions;
--   * `Position.before-mono-≼`, `count-≼-eq`,
--     `¬unr-handle`                             -- `≼` neither creates a `;`
--                                                  nor changes multiplicities;
--   * `Position.focusTyping-binders`/
--     `Position.binderTyping`                   -- the `TP-Res` payload of the
--                                                  owning binder;
--   * `ThreadOrder.thread-¬before`/
--     `thread-pair-¬before`, `ContextOrder.ctx-¬before-direct`/
--     `-pair`                                   -- Phase 4a: the ACTUAL
--                                                  structure the derivation
--                                                  forces, walked down to the
--                                                  redex thread.
--
-- `acq-non-first-group-head` (restated -- see `Position.agda`'s
-- `AcqNonFirstGroupHead`) is PROVED below, modulo the single hole
-- `acqHeadCtx⇒acqHeaded` (§1a): it needs only the "offset > 0 implies NoAcq" half
-- of Position.agda's case (iv), because `x`'s OWN acq-typing comes directly
-- from `acq`'s typing rule (§1c/§1b), not from a forward "group head implies
-- acq-typed" derivation the other two holes still need.
--
-- `impure-redex-head` / `pair-arg-redex-head` remain OPEN, and are FALSE for
-- `BindCtx` as it stands (`Examples/StrictGroupGap.agda`, quoted in the
-- header).  What they need, ONCE the two premises named there are in place:
--
--   (a) case (iv), "x IS the head of a later group": the FORWARD direction
--       "later-group head implies acq-typed", which `consRetAcq-peel` (§1a) now
--       supplies from `AcqHeaded` -- then each impure constant's domain
--       refutes `≃ acq ; t`: `⟨ skip ⟩` by `AtomCons.atom-;-¬skips`,
--       `⟨ ret ⟩` / `⟨ end p ⟩` / `⟨ msg ⁇ T ⟩` by `atom-;-atom`,
--       `⟨ brn p s₁ s₂ ⟩` by `¬cons-brn`, and `send`'s pair by
--       `Position.pair-arg-not-var`;
--   (b) case (iii), "same group, offset > 0": `group-head-before` puts the
--       group's own head `;`-before `x`, and `ctx-¬before-direct` refutes
--       that -- but it wants `¬ Mobile` of BOTH.  For `x` that is
--       `impure-handle-¬mobile` (extended to `select`/`branch` by
--       `¬cons-brn`); for the head it is `first-group-¬mobile` when the group
--       is the first, and otherwise `mobile-head-alone` -- WHICH IS FALSE as
--       `BindCtx′` stands (`mobile-head-alone-refuted`);
--   (c) the plumbing: lift `before` from `structBinder B₁` into the body
--       structure `TP-Res` prescribes (two `before-⋯ᵣ` steps plus
--       `ContextOrder.bind-before`), and bound `count y` of a binder-local
--       variable in that structure by 1 (`structNSeq` lists each variable
--       once; `count-⋯ᵣwkʳ-↑ʳ` / `count-weaken*-shift` of
--       `Support/StructDom.agda` move the other two components out of the
--       way).  This is the only genuinely mechanical part left, and it is
--       INDEPENDENT of the two premise questions.

impure-redex-head : ImpureRedexHead
impure-redex-head = {!!}   -- HOLE 1

pair-arg-redex-head : PairArgRedexHead
pair-arg-redex-head = {!!} -- HOLE 2

drop-first-group-singleton : DropFirstGroupSingleton
drop-first-group-singleton {ctx = ctx} {E = E} {x = x} ⊢plug
  with resolve ctx x
... | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  with impure-redex-head ⊢plug `drop
... | gi≡0 , off≡0
  with binderTyping bnd 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with TypeWalk.ctx-type 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ x (λ _ → ret) (Q-drop-type E x)
         below ⊢body (local ↑ˡ mid) index-eq
... | _ , eqRet
  with sideOf B₁ B₂ local
... | inl i
  with groupOf B₁ i | gi≡0 | off≡0
... | head-group B′ zero | _ | _ =
  let localEq = V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ ((zero ↑ˡ sum B′) ↑ˡ sum B₂) ■ V.lookup-++ˡ Γ₁ Γ₂ (zero ↑ˡ sum B′)
      b₁≡0 , B′≢[] = dropGroupShape N C (subst (_≃ ⟨ ret ⟩) localEq eqRet)
  in cong suc b₁≡0 , B′≢[]
... | head-group B′ (suc q) | _ | ()
... | next-group b g′ | () | _
drop-first-group-singleton {ctx = ctx} {E = E} {x = x} ⊢plug
  | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  | gi≡0 , off≡0
  | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  | _ , eqRet
  | inr i
  with groupOf B₂ i | gi≡0 | off≡0
... | head-group B″ zero | _ | _ =
  let localEq = V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (sum B₁ ↑ʳ (zero ↑ˡ sum B″)) ■ V.lookup-++ʳ Γ₁ Γ₂ (zero ↑ˡ sum B″)
      b₁≡0 , B″≢[] = dropGroupShape (new-dual N) C′ (subst (_≃ ⟨ ret ⟩) localEq eqRet)
  in cong suc b₁≡0 , B″≢[]
... | head-group B″ (suc q) | _ | ()
... | next-group b g′ | () | _

-- `?4` (restated from `AcqSecondGroupHead`, see `Position.agda`), PROVED
-- modulo `nonFirstGroup-interior-noAcq` (§1a) -- see the header comment
-- above for why this one hole does not also block on the "later-group
-- head ⟹ acq-typed" direction the other three still need.
acq-non-first-group-head : AcqNonFirstGroupHead
acq-non-first-group-head {ctx = ctx} {E = E} {x = x} ⊢plug
  with resolve ctx x
... | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  with binderTyping bnd 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with TypeWalk.ctx-type 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ x (λ s → acq ; s) (Q-acq-type E x)
         below ⊢body (local ↑ˡ mid) index-eq
... | sAcq , eqAcq
  with sideOf B₁ B₂ local
... | inl i
  with groupOf B₁ i
... | g
  with V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (i ↑ˡ sum B₂) ■ V.lookup-++ˡ Γ₁ Γ₂ i
... | localEq
  with subst (_≃ ⟨ acq ; sAcq ⟩) localEq eqAcq
... | eqAcq₁
  with groupIndex g Nat.≟ 0
... | yes gi≡0 =
  let s′ , eq′ , na′ = first-group-noAcq N C g gi≡0
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₁)))
... | no gi≢0
  with groupOffset g Nat.≟ 0
... | yes off≡0 = 0≢⇒0< gi≢0 , off≡0
... | no off≢0 =
  let s′ , eq′ , na′ = laterGroup-interior-noAcq N C ⊢B₁ g (0≢⇒0< gi≢0) (0≢⇒0< off≢0)
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₁)))
acq-non-first-group-head {ctx = ctx} {E = E} {x = x} ⊢plug
  | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  | sAcq , eqAcq
  | inr i
  with groupOf B₂ i
... | g
  with V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (sum B₁ ↑ʳ i) ■ V.lookup-++ʳ Γ₁ Γ₂ i
... | localEq
  with subst (_≃ ⟨ acq ; sAcq ⟩) localEq eqAcq
... | eqAcq₂
  with groupIndex g Nat.≟ 0
... | yes gi≡0 =
  let s′ , eq′ , na′ = first-group-noAcq (new-dual N) C′ g gi≡0
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₂)))
... | no gi≢0
  with groupOffset g Nat.≟ 0
... | yes off≡0 = 0≢⇒0< gi≢0 , off≡0
... | no off≢0 =
  let s′ , eq′ , na′ = laterGroup-interior-noAcq (new-dual N) C′ ⊢B₂ g (0≢⇒0< gi≢0) (0≢⇒0< off≢0)
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₂)))
