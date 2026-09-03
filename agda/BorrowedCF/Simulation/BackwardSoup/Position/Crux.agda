-- | Phase 3, THE CRUX (`BackwardSoup/PLAN.md` §9, P3) -- CLOSED.
--
--   `Position.agda` STATES the metatheorem (`ImpureRedexHead`,
--   `PairArgRedexHead`, `DropFirstGroupSingleton`, `AcqNonFirstGroupHead`)
--   and proves all its combinatorial ingredients; this module proves it.
--   Both load with 0 goals and no pragma.
--
--   TWO PREMISE CHANGES made the proof go through; `Examples/StrictGroupGap.agda`
--   machine-checks that neither is optional.
--
--   (1) `Processes/Typed.agda`'s `AcqHeadCtx` now says what its doc comment
--       says -- `AcqHeadCtx (⟨ s ⟩ ∷ _) = Σ[ t ] (s ≃ acq ; t)` -- instead of
--       the strictly weaker `¬ Skips s`.  Under the old reading
--       `cons-ret/acq` admitted `s₁ ≡ skip`, a group that does no work and
--       hands its `acq` on, so a `⊢ᴮ`-legal group list could govern
--       `acq ; acq ; ⋯` and put an ACQ-HEADED handle at offset 1 of a group
--       (`StrictGroupGap.refuted`).  With the strong reading, §1a's
--       `nonFirstGroup-interior-noAcq` and §1a''s `laterGroup-head-acq` -- the
--       two directions of "the group's `acq` sits on its HEAD and nowhere
--       else" -- both go through.
--
--   (2) `Types/NoTerm.agda` (NEW) supplies the premise PLAN.md §6's mobility
--       argument was missing.  `Bounded s′` in `Mobile ⟨ acq ; s′ ⟩` is
--       satisfied by an `end` tip as well as by a `ret` tip, so `NoRet` is not
--       enough to make a Mobile handle the LAST of its group
--       (`StrictGroupGap.mobile-head-alone-refuted`).  `NoTerm` -- no `ret`
--       AND no `end`, which is exactly what `New` gives -- is, and §1a′'s
--       `mobile-head-alone` / `group-head-¬mobile` are the result.
--
--   The new theory of the previous pass, `Types/AtomCons.agda`, is what both
--   halves of (1) run on: `Cons a w z` witnesses `w ≃ a ; z`, `≃-cons`
--   transports it, and `atom-;-cons` (`acq-;-split` at `acq`) splits
--   `s₁ ; s₂ ≃ acq ; t` into "the `acq` is at the front of `s₁`" or "`s₁`
--   skips and the `acq` is at the front of `s₂`".
--
--   LAYOUT.
--     §1   `impure-handle-¬mobile` for the `acq`-free domains (`NoAcqDomain`).
--     §1a  the `acq` peel (`acq-peel`, `bindCtx′-acq-interior`,
--          `consRetAcq-peel`) and `nonFirstGroup-interior-noAcq`: an INTERIOR
--          handle of a non-first group carries no `acq`.
--     §1a′ `mobile-head-alone`: a group's terminator ENDS the group, so a
--          Mobile handle at offset 0 is its group's only handle; hence
--          `group-head-¬mobile`, the immobility of the comparison partner.
--     §1a″ `laterGroup-head-acq`: the head of a non-first group IS acq-typed.
--     §1b  `TypeWalk` / `TypeWalkP`: generic walkers carrying a fact about the
--          redex handle from its own thread's typing up to the owning binder.
--     §1c  `acq`'s and `drop`'s domains, extracted.
--     §1d  `dropGroupShape`, `drop`'s group shape at an arbitrary position.
--     §1e  what an impure handle-consuming constant may NOT consume: neither
--          a MOBILE nor an ACQ-HEADED handle, for all seven constants.
--     §1f  the plumbing: `before` and `count` lifted from `structBinder Bᵢ`
--          into the body structure `TP-Res` prescribes.
--     §1g  the two halves, abstracted over the redex thread: `head-not-later`
--          (case (iv)) and `offset-zero-inl/inr` (case (iii)).
--     §2   the four theorems.
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
  using (acq-;-split; acq-;-¬skips; acq-;-≄ret
        ; acq-;-≄end; acq-;-≄msg; acq-;-¬brn)
open import BorrowedCF.Types.NoTerm
  using ( NoTerm; new⇒noTerm; noTerm-acq; noTerm-split
        ; TermAtom; termAtom-ret; termAtom-end; bounded-tail-skips )
open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; ¬noRet-ret; noRet-;-fst
        ; RetTip; noRet-front-cons; retTip-Sc-skips; retTip-≃ )
open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (drop-handle-≃ret)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position
open import BorrowedCF.Simulation.BackwardSoup.Position.ContextOrder
  using (ctx-¬before-direct; ctx-¬before-pair)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.StructDom
  using ( count-⋯ᵣwkʳ-↑ˡ; count-⋯ᵣwkʳ-↑ʳ; count-structBinder-lt
        ; count-weaken*-lo; count-weaken*-shift; ⋯ᵣwkˡ≡⋯weaken* )
import BorrowedCF.Context.Substitution as 𝐂

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
-- `AcqHeadCtx Γ` -- "the first bound handle of a non-first group carries the
-- group's `acq`", `Σ[ t ] (s ≃ acq ; t)` -- is the premise that makes the
-- section below true.  `Examples/StrictGroupGap.agda`'s `refuted` is the
-- machine-checked counterexample to the previous, weaker reading
-- (`¬ Skips s`); `blocked` is the derivation step the strong reading kills.

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
    AcqHeadCtx Γ → (z : 𝔽 n) →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ suc z) ≃ ⟨ s′ ⟩) × NoAcq s′
  bindCtx′-acq-interior NAg (cons s₁ s₂ _ split C′) (t , u≃) z =
    bindCtx′-noAcq (proj₂ (acq-peel NAg (λ Sk → acq-;-¬skips Sk u≃) split)) C′ z

  -- At a `cons-ret/acq` node under an acq-headed context the `acq` goes to the
  -- node's OWN group: `acq-;-split`'s first alternative (`Skips s₁`, the acq
  -- escaping into the rest) would make the group's session `≃ ret`, and its
  -- head handle is acq-headed, so `ret ≃ acq ; ⋯` -- refuted by `acq-;-≄ret`.
  consRetAcq-peel :
    ∀ {n k} {Γ₁ : Ctx n} {Γ₂ : Ctx k} {s₁ s₂ g : 𝕊 0} →
    NoAcq g → s₁ ; s₂ ≃ acq ; g → BindCtx′ (s₁ ; ret) Γ₁ → AcqHeadCtx (Γ₁ ⸴* Γ₂) →
    AcqHeadCtx Γ₁
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

-- PROVED (from `AcqHeadCtx`).  An interior handle -- offset > 0 in its group --
-- of a group list governed by `acq ; g` with `g` acq-free carries no `acq`.
-- `Allᴸ.All NonZero B` (i.e. `⊢ᴮ` of the enclosing list) rules out the
-- `cons-acq` node, whose empty group would stack a SECOND `acq` in front of
-- the governing session.
nonFirstGroup-interior-noAcq :
  ∀ {B} {Γ : Ctx (sum B)} {g : 𝕊 0} → NoAcq g → BindCtx (acq ; g) B Γ →
  AcqHeadCtx Γ → Allᴸ.All NonZero B →
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
        nonFirstGroup-interior-noAcq NAs₂ rest ah′
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
            ah ⊢B g′ 0<off
    in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) eq , na
  laterGroup-interior-noAcq N (cons-ret/acq s₁ s≃ _ front rest ah) ⊢B
    (head-group B′ j) () 0<off
  laterGroup-interior-noAcq N (cons-acq C ah) ⊢B (next-group .0 g′) 0<gi 0<off =
    nonFirstGroup-interior-noAcq (new-end⇒noAcq N) C ah ⊢B g′ 0<off

------------------------------------------------------------------------
-- 1a'.  `mobile-head-alone`: A GROUP'S TERMINATOR ENDS THE GROUP.
--
--   `Examples/StrictGroupGap.agda` §4 refutes PLAN.md §6's version of this
--   claim, which used `NoRet` for the body of a group chain: `Bounded s'` in
--   `Mobile ⟨ acq ; s' ⟩` is satisfied by an `end` tip as well as by a `ret`
--   tip, so a `NoRet` body may still hide a terminator.  `Types/NoTerm.agda`
--   supplies the correct premise -- `NoTerm`, no `ret` AND no `end`, which is
--   exactly what a `New`-derived session gives -- and `bounded-tail-skips` is
--   the one-line consequence: in a chain `q ; τ` whose ONLY terminator is the
--   trailing atom `τ`, a BOUNDED handle already reaches it, so everything
--   after it skips and the `BindCtx'` chain stops (`cons` demands `¬ Skips`).
--
--   The invariant carried through the `BindCtx` induction is "the group list
--   is governed by `c ≃ q ; τ` with `NoTerm q` and `τ ∈ {ret, end p}`":
--     * the top-level session is `s ; end p` with `New s`;
--     * a `cons-ret/acq` node's own group chain is `s₁ ; ret`, and `¬ Skips s₂`
--       forces the trailing `τ` into `s₂` (`noTerm-split`), leaving `s₁` a
--       `NoTerm` prefix of `q`;
--     * the node's REMAINDER is `acq ; s₂ ≃ (acq ; q') ; τ`, and prefixing an
--       `acq` preserves `NoTerm`.  Likewise for `cons-acq`.

private
  block-mobile-head-width1 :
    ∀ {n} {Γ : Ctx (suc n)} {c q τ : 𝕊 0} →
    TermAtom τ → NoTerm q → c ≃ q ; τ → BindCtx′ c Γ →
    Mobile (Γ ﹫ 0F) → n ≡ 0
  block-mobile-head-width1 A NTq eq (cons u₁ rest ¬sk split (nil _)) mob = refl
  block-mobile-head-width1 A NTq eq
    (cons u₁ rest ¬sk split (cons _ _ ¬sk′ _ _)) ⟨ w , Bw , u≃ ⟩ =
    ⊥-elim (¬sk′ (bounded-tail-skips A NTq
                    (≃-bounded (≃-sym u≃) (-;₂ Bw)) (≃-trans split eq)))

  bindCtx-mobile-head-alone :
    ∀ {B} {Γ : Ctx (sum B)} {c q τ : 𝕊 0} →
    TermAtom τ → NoTerm q → c ≃ q ; τ → BindCtx c B Γ →
    ∀ {i} (grp : GroupOf B i) → groupOffset grp ≡ 0 → Mobile (Γ ﹫ i) →
    groupWidth grp ≡ 1
  bindCtx-mobile-head-alone A NTq eq (last C) (head-group L.[] zero) off mob =
    cong suc (sym (+-identityʳ _) ■ block-mobile-head-width1 A NTq eq C mob)
  bindCtx-mobile-head-alone A NTq eq (last C) (head-group L.[] (suc j)) () mob
  bindCtx-mobile-head-alone A NTq eq (last C) (next-group _ ()) off mob
  bindCtx-mobile-head-alone A NTq eq
    (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ ¬sk₂ front rest ah)
    (head-group B′ zero) off mob
    with noTerm-split A NTq ¬sk₂ (≃-trans s≃ eq)
  ... | q′ , NTs₁ , NTq′ , s₂≃ =
    cong suc (block-mobile-head-width1 termAtom-ret NTs₁ ≃-refl front
                (subst Mobile (V.lookup-++ˡ Γ₁ Γ₂ 0F) mob))
  bindCtx-mobile-head-alone A NTq eq (cons-ret/acq _ _ _ _ _ _)
    (head-group B′ (suc j)) () mob
  bindCtx-mobile-head-alone A NTq eq
    (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ ¬sk₂ front rest ah)
    (next-group b g′) off mob
    with noTerm-split A NTq ¬sk₂ (≃-trans s≃ eq)
  ... | q′ , NTs₁ , NTq′ , s₂≃ =
    bindCtx-mobile-head-alone A (noTerm-acq NTq′)
      (≃-trans (≃-; ≃-refl s₂≃) (≃-sym ≃-assoc-;)) rest g′ off
      (subst Mobile (V.lookup-++ʳ Γ₁ Γ₂ _) mob)
  bindCtx-mobile-head-alone A NTq eq (cons-acq C ah) (head-group _ ()) off mob
  bindCtx-mobile-head-alone A NTq eq (cons-acq C ah) (next-group .0 g′) off mob =
    bindCtx-mobile-head-alone A (noTerm-acq NTq)
      (≃-trans (≃-; ≃-refl eq) (≃-sym ≃-assoc-;)) C g′ off mob

-- PROVED.  A MOBILE handle at offset 0 is the ONLY handle of its group: its
-- `Bounded` continuation carries the group's terminator, and nothing may
-- follow a terminator inside one group.
mobile-head-alone :
  ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
  New s → BindCtx (s ; end p) B Γ →
  ∀ {i} (grp : GroupOf B i) → groupOffset grp ≡ 0 → Mobile (Γ ﹫ i) →
  groupWidth grp ≡ 1
mobile-head-alone N C =
  bindCtx-mobile-head-alone termAtom-end (new⇒noTerm N) ≃-refl C

-- ... so the HEAD of the group of a handle at a POSITIVE offset is immobile:
-- were it mobile its group would have width 1 and admit no such handle.
-- (This subsumes `Position.first-group-¬mobile` for the comparison partner:
-- no case distinction on the group index is needed.)
group-head-¬mobile :
  ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
  New s → BindCtx (s ; end p) B Γ →
  ∀ {i} (g : GroupOf B i) → 0 Nat.< groupOffset g →
  ¬ Mobile (Γ ﹫ groupHeadIx g)
group-head-¬mobile N C g 0<off mob =
  case Nat.≤-trans 0<off (Nat.s≤s⁻¹ off<1) of λ ()
  where
  w≡1 : groupWidth g ≡ 1
  w≡1 = sym (groupHead-width g)
      ■ mobile-head-alone N C (groupHeadOf g) (groupHead-offset g) mob
  off<1 : groupOffset g Nat.< 1
  off<1 = subst (groupOffset g Nat.<_) w≡1 (groupOffset<width g)

------------------------------------------------------------------------
-- 1a''.  The FORWARD direction: a NON-FIRST group's head IS acq-typed.
--
--   This is `AcqHeadCtx` read off, now that it says `Σ[ t ] (s ≃ acq ; t)`:
--   the premise of `cons-ret/acq` / `cons-acq` pins the head of the group
--   list that FOLLOWS the node, and the head of a group list is the head of
--   its first group.  `allGroupHeads-acq` propagates it down the chain, and
--   `laterGroup-head-acq` is the one step that supplies it: the first group
--   of a `BindCtx` is the SECOND group of its parent.

private
  𝔽⇒0< : ∀ {b} → 𝔽 b → 0 Nat.< b
  𝔽⇒0< zero    = Nat.s≤s Nat.z≤n
  𝔽⇒0< (suc _) = Nat.s≤s Nat.z≤n

  -- The head of a non-empty block is the head of the whole context.
  acqHead-++ˡ : ∀ {n k} {Γ₁ : Ctx n} {Γ₂ : Ctx k} {c : 𝕊 0} →
    BindCtx′ c Γ₁ → 0 Nat.< n → AcqHeadCtx (Γ₁ ⸴* Γ₂) → AcqHeadCtx Γ₁
  acqHead-++ˡ (cons _ _ _ _ _) _ ah = ah
  acqHead-++ˡ (nil _) () ah

  block-head-acq : ∀ {n} {Γ : Ctx n} {c : 𝕊 0} → BindCtx′ c Γ → AcqHeadCtx Γ →
    (z : 𝔽 n) → Fin.toℕ z ≡ 0 → Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ z) ≃ ⟨ acq ; t ⟩)
  block-head-acq (cons _ _ _ _ _) (t , u≃) zero refl = t , ⟨ u≃ ⟩
  block-head-acq (cons _ _ _ _ _) ah (suc z) ()

  allGroupHeads-acq :
    ∀ {B} {Γ : Ctx (sum B)} {c : 𝕊 0} → BindCtx c B Γ → AcqHeadCtx Γ →
    ∀ {i} (grp : GroupOf B i) → groupOffset grp ≡ 0 →
    Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ acq ; t ⟩)
  allGroupHeads-acq (last C) ah (head-group L.[] j) off =
    block-head-acq C ah (j ↑ˡ 0) (Fin.toℕ-↑ˡ j 0 ■ off)
  allGroupHeads-acq (last C) ah (next-group _ ()) off
  allGroupHeads-acq (cons-ret/acq _ {Γ₁ = Γ₁} {Γ₂ = Γ₂} _ _ front rest ah′) ah
    (head-group B′ j) off =
    let t , e = block-head-acq front (acqHead-++ˡ front (𝔽⇒0< j) ah) j off
    in t , subst (_≃ ⟨ acq ; t ⟩) (sym (V.lookup-++ˡ Γ₁ Γ₂ j)) e
  allGroupHeads-acq (cons-ret/acq _ {Γ₁ = Γ₁} {Γ₂ = Γ₂} _ _ front rest ah′) ah
    (next-group b g′) off =
    let t , e = allGroupHeads-acq rest ah′ g′ off
    in t , subst (_≃ ⟨ acq ; t ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) e
  allGroupHeads-acq (cons-acq C ah′) ah (head-group _ ()) off
  allGroupHeads-acq (cons-acq C ah′) ah (next-group .0 g′) off =
    allGroupHeads-acq C ah′ g′ off

-- PROVED.  The head of a group that is not the FIRST one carries the group's
-- `acq` -- the converse of `nonFirstGroup-interior-noAcq`, and what refutes
-- an impure constant sitting there.
laterGroup-head-acq :
  ∀ {B} {Γ : Ctx (sum B)} {c : 𝕊 0} → BindCtx c B Γ →
  ∀ {i} (grp : GroupOf B i) → 0 Nat.< groupIndex grp → groupOffset grp ≡ 0 →
  Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ acq ; t ⟩)
laterGroup-head-acq (last C) (head-group _ _) () off
laterGroup-head-acq (last C) (next-group _ ()) 0<gi off
laterGroup-head-acq (cons-ret/acq _ _ _ _ _ _) (head-group _ _) () off
laterGroup-head-acq (cons-ret/acq _ {Γ₁ = Γ₁} {Γ₂ = Γ₂} _ _ front rest ah)
  (next-group b g′) 0<gi off =
  let t , e = allGroupHeads-acq rest ah g′ off
  in t , subst (_≃ ⟨ acq ; t ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) e
laterGroup-head-acq (cons-acq C ah) (head-group _ ()) 0<gi off
laterGroup-head-acq (cons-acq C ah) (next-group .0 g′) 0<gi off =
  allGroupHeads-acq C ah g′ off

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

  -- The same walk for an ARBITRARY predicate on the handle's type: the
  -- lookup is literally unchanged along the path, so anything transports.
  module TypeWalkP {k : ℕ} (Q : 𝐓.Proc k) (x : 𝔽 k) (Pr : 𝕋 → Set)
    (Q-type : ∀ {Γ : Ctx k} {γ : Struct k} → Γ ; γ ⊢ₚ Q → Pr (Γ ﹫ x))
    where

    ctx-type :
      ∀ {n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n} →
      Γ ; γ ⊢ₚ plug below Q →
      (y : 𝔽 n) → weakenThrough below y ≡ x → Pr (Γ ﹫ y)
    ctx-type hole ⊢P y refl = Q-type ⊢P
    ctx-type (par-left ctx P₂) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , ⊢left , _ = ctx-type ctx ⊢left y eq
    ctx-type (par-right P₁ ctx) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , _ , ⊢right = ctx-type ctx ⊢right y eq
    ctx-type (bind B₁ B₂ ctx) {Γ} ⊢P y eq with inv-ν ⊢P
    ... | Γ₁ , Γ₂ , _ , _ , _ , _ , _ , _ , _ , ⊢body =
      subst Pr (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ y)
        (ctx-type ctx ⊢body ((sum B₁ + sum B₂) ↑ʳ y) eq)

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
-- 1e.  What an IMPURE handle-consuming constant may NOT consume.
--
--   Two facts about the domain of every `ImpureHandleConst`, in the two
--   forms the crux needs:
--     * it is not MOBILE -- so `before-mono-≼` applies to the handle
--       (`∥′-tm-;` cannot reorder it);
--     * it is not ACQ-HEADED -- so the handle is not the head of a non-first
--       group (`laterGroup-head-acq`).
--   `discard`/`drop`/`recv`/`end p` are settled by `NoAcq`; `select`/`branch`
--   consume a `brn`, in front of which no atom can sit (`AtomCons.¬cons-brn`,
--   packaged as `acq-;-¬brn`); `send` consumes a PAIR whose handle component
--   is `⟨ msg ‼ T ⟩`.

private
  impure-fn-dom-¬mobile :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ → ¬ Mobile Tᵈ
  impure-fn-dom-¬mobile `discard (T-Const `discard)   = ¬mobile-noAcq NoAcq.skip
  impure-fn-dom-¬mobile `drop    (T-Const `drop)      = ¬mobile-noAcq NoAcq.ret
  impure-fn-dom-¬mobile `recv    (T-Const (`recv _))  = ¬mobile-noAcq NoAcq.msg
  impure-fn-dom-¬mobile `end     (T-Const `end)       = ¬mobile-noAcq NoAcq.end
  impure-fn-dom-¬mobile `select  (T-Const `select)    = λ{ ⟨ _ , _ , e ⟩ → acq-;-¬brn e }
  impure-fn-dom-¬mobile `branch  (T-Const `branch)    = λ{ ⟨ _ , _ , e ⟩ → acq-;-¬brn e }
  impure-fn-dom-¬mobile `send    (T-Const (`send _))  =
    λ{ (_ ⊗ m) → ¬mobile-noAcq NoAcq.msg m }
  impure-fn-dom-¬mobile ic (T-Conv (dom≃ `→ _) _ d) =
    impure-fn-dom-¬mobile ic d ∘ mobile-≃ (≃-sym dom≃)
  impure-fn-dom-¬mobile ic (T-Weaken _ d) = impure-fn-dom-¬mobile ic d

  impure-fn-dom-¬acq :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    ∀ {t : 𝕊 0} → ¬ (Tᵈ ≃ ⟨ acq ; t ⟩)
  impure-fn-dom-¬acq `discard (T-Const `discard)  eq = acq-;-¬skips Skips.skip (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `drop    (T-Const `drop)     eq = acq-;-≄ret (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `recv    (T-Const (`recv _)) eq = acq-;-≄msg (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `end     (T-Const `end)      eq = acq-;-≄end (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `select  (T-Const `select)   eq = acq-;-¬brn (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `branch  (T-Const `branch)   eq = acq-;-¬brn (⟨⟩≃′ eq)
  impure-fn-dom-¬acq `send    (T-Const (`send _)) ()
  impure-fn-dom-¬acq ic (T-Conv (dom≃ `→ _) _ d) eq =
    impure-fn-dom-¬acq ic d (≃-trans dom≃ eq)
  impure-fn-dom-¬acq ic (T-Weaken _ d) eq = impure-fn-dom-¬acq ic d eq

  -- ... and the same for the SECOND COMPONENT of a pair domain (only `send`
  -- has one, and there the component is `⟨ msg ‼ T ⟩`).
  impure-fn-snd-¬mobile :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    ∀ {T₁ T₂ : 𝕋} {d} → T₁ ⊗⟨ d ⟩ T₂ ≃ Tᵈ → ¬ Mobile T₂
  impure-fn-snd-¬mobile `discard (T-Const `discard)  ()
  impure-fn-snd-¬mobile `drop    (T-Const `drop)     ()
  impure-fn-snd-¬mobile `recv    (T-Const (`recv _)) ()
  impure-fn-snd-¬mobile `select  (T-Const `select)   ()
  impure-fn-snd-¬mobile `branch  (T-Const `branch)   ()
  impure-fn-snd-¬mobile `end     (T-Const `end)      ()
  impure-fn-snd-¬mobile `send    (T-Const (`send _)) (_ ⊗ e₂) =
    ¬mobile-noAcq NoAcq.msg ∘ mobile-≃ e₂
  impure-fn-snd-¬mobile ic (T-Conv (dom≃ `→ _) _ d) eq =
    impure-fn-snd-¬mobile ic d (≃-trans eq (≃-sym dom≃))
  impure-fn-snd-¬mobile ic (T-Weaken _ d) eq = impure-fn-snd-¬mobile ic d eq

  impure-fn-snd-¬acq :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    ∀ {T₁ T₂ : 𝕋} {d} → T₁ ⊗⟨ d ⟩ T₂ ≃ Tᵈ →
    ∀ {t : 𝕊 0} → ¬ (T₂ ≃ ⟨ acq ; t ⟩)
  impure-fn-snd-¬acq `discard (T-Const `discard)  ()
  impure-fn-snd-¬acq `drop    (T-Const `drop)     ()
  impure-fn-snd-¬acq `recv    (T-Const (`recv _)) ()
  impure-fn-snd-¬acq `select  (T-Const `select)   ()
  impure-fn-snd-¬acq `branch  (T-Const `branch)   ()
  impure-fn-snd-¬acq `end     (T-Const `end)      ()
  impure-fn-snd-¬acq `send    (T-Const (`send _)) (_ ⊗ e₂) eq =
    acq-;-≄msg (⟨⟩≃′ (≃-trans (≃-sym e₂) eq))
  impure-fn-snd-¬acq ic (T-Conv (dom≃ `→ _) _ d) eq =
    impure-fn-snd-¬acq ic d (≃-trans eq (≃-sym dom≃))
  impure-fn-snd-¬acq ic (T-Weaken _ d) eq = impure-fn-snd-¬acq ic d eq

  -- Lifting to the redex `K c ·⟨ d ⟩ (` x)` / `K c ·⟨ d ⟩ (w ⊗ (` x))`.
  app-¬mobile :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {d} {T ϵ} →
    ImpureHandleConst c → Γ ; γ ⊢ K c ·⟨ d ⟩ (` x) ∶ T ∣ ϵ → ¬ Mobile (Γ ﹫ x)
  app-¬mobile ic (T-AppUnr _ _ ⊢fn ⊢arg) =
    impure-fn-dom-¬mobile ic ⊢fn ∘ mobile-≃ (arg-type ⊢arg)
  app-¬mobile ic (T-AppLin _ _ ⊢fn ⊢arg) =
    impure-fn-dom-¬mobile ic ⊢fn ∘ mobile-≃ (arg-type ⊢arg)
  app-¬mobile ic (T-AppLeft _ _ ⊢fn ⊢arg) =
    impure-fn-dom-¬mobile ic ⊢fn ∘ mobile-≃ (arg-type ⊢arg)
  app-¬mobile ic (T-AppRight _ _ ⊢fn ⊢arg) =
    impure-fn-dom-¬mobile ic ⊢fn ∘ mobile-≃ (arg-type ⊢arg)
  app-¬mobile ic (T-Conv _ _ d) = app-¬mobile ic d
  app-¬mobile ic (T-Weaken _ d) = app-¬mobile ic d

  app-¬acq :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {d} {T ϵ} →
    ImpureHandleConst c → Γ ; γ ⊢ K c ·⟨ d ⟩ (` x) ∶ T ∣ ϵ →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; t ⟩))
  app-¬acq ic (T-AppUnr _ _ ⊢fn ⊢arg) (t , eq) =
    impure-fn-dom-¬acq ic ⊢fn (≃-trans (≃-sym (arg-type ⊢arg)) eq)
  app-¬acq ic (T-AppLin _ _ ⊢fn ⊢arg) (t , eq) =
    impure-fn-dom-¬acq ic ⊢fn (≃-trans (≃-sym (arg-type ⊢arg)) eq)
  app-¬acq ic (T-AppLeft _ _ ⊢fn ⊢arg) (t , eq) =
    impure-fn-dom-¬acq ic ⊢fn (≃-trans (≃-sym (arg-type ⊢arg)) eq)
  app-¬acq ic (T-AppRight _ _ ⊢fn ⊢arg) (t , eq) =
    impure-fn-dom-¬acq ic ⊢fn (≃-trans (≃-sym (arg-type ⊢arg)) eq)
  app-¬acq ic (T-Conv _ _ d) = app-¬acq ic d
  app-¬acq ic (T-Weaken _ d) = app-¬acq ic d

  snd-¬mobile :
    ∀ {n} {Γ : Ctx n} {β γ : Struct n} {c} {w : Tm n} {x : 𝔽 n} {Tᵈ U a ϵ ϵ′} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ ⊢ w ⊗ (` x) ∶ Tᵈ ∣ ϵ′ → ¬ Mobile (Γ ﹫ x)
  snd-¬mobile ic ⊢fn ⊢pair with inv-⊗ ⊢pair
  ... | _ , _ , _ , _ , _ , _ , _ , _ , tyEq , _ , _ , _ , ⊢x =
    impure-fn-snd-¬mobile ic ⊢fn tyEq ∘ mobile-≃ (arg-type ⊢x)

  snd-¬acq :
    ∀ {n} {Γ : Ctx n} {β γ : Struct n} {c} {w : Tm n} {x : 𝔽 n} {Tᵈ U a ϵ ϵ′} →
    ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ ⊢ w ⊗ (` x) ∶ Tᵈ ∣ ϵ′ →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; t ⟩))
  snd-¬acq ic ⊢fn ⊢pair with inv-⊗ ⊢pair
  ... | _ , _ , _ , _ , _ , _ , _ , _ , tyEq , _ , _ , _ , ⊢x =
    λ{ (t , eq) → impure-fn-snd-¬acq ic ⊢fn tyEq (≃-trans (≃-sym (arg-type ⊢x)) eq) }

  pair-¬mobile :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {w : Tm n} {x : 𝔽 n} {d} {T ϵ} →
    ImpureHandleConst c → Γ ; γ ⊢ K c ·⟨ d ⟩ (w ⊗ (` x)) ∶ T ∣ ϵ →
    ¬ Mobile (Γ ﹫ x)
  pair-¬mobile ic (T-AppUnr _ _ ⊢fn ⊢arg) = snd-¬mobile ic ⊢fn ⊢arg
  pair-¬mobile ic (T-AppLin _ _ ⊢fn ⊢arg) = snd-¬mobile ic ⊢fn ⊢arg
  pair-¬mobile ic (T-AppLeft _ _ ⊢fn ⊢arg) = snd-¬mobile ic ⊢fn ⊢arg
  pair-¬mobile ic (T-AppRight _ _ ⊢fn ⊢arg) = snd-¬mobile ic ⊢fn ⊢arg
  pair-¬mobile ic (T-Conv _ _ d) = pair-¬mobile ic d
  pair-¬mobile ic (T-Weaken _ d) = pair-¬mobile ic d

  pair-¬acq :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {w : Tm n} {x : 𝔽 n} {d} {T ϵ} →
    ImpureHandleConst c → Γ ; γ ⊢ K c ·⟨ d ⟩ (w ⊗ (` x)) ∶ T ∣ ϵ →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; t ⟩))
  pair-¬acq ic (T-AppUnr _ _ ⊢fn ⊢arg) = snd-¬acq ic ⊢fn ⊢arg
  pair-¬acq ic (T-AppLin _ _ ⊢fn ⊢arg) = snd-¬acq ic ⊢fn ⊢arg
  pair-¬acq ic (T-AppLeft _ _ ⊢fn ⊢arg) = snd-¬acq ic ⊢fn ⊢arg
  pair-¬acq ic (T-AppRight _ _ ⊢fn ⊢arg) = snd-¬acq ic ⊢fn ⊢arg
  pair-¬acq ic (T-Conv _ _ d) = pair-¬acq ic d
  pair-¬acq ic (T-Weaken _ d) = pair-¬acq ic d

------------------------------------------------------------------------
-- 1f.  The plumbing: lift `before` and `count` from `structBinder B₁` /
--      `structBinder B₂` into the body structure that `TP-Res` prescribes,
--
--        (structBinder B₁ ⋯ᵣ wkʳ (sum B₂) ⋯ᵣ wkʳ mid)
--          ∥ (structBinder B₂ ⋯ᵣ wkˡ (sum B₁) ⋯ᵣ wkʳ mid)
--          ∥ (γ′ ⋯ᵣ weaken* (sum B₁ + sum B₂)),
--
--      and bound a binder-local variable's multiplicity there by 1
--      (`structBinder` lists each of its variables exactly ONCE, and the two
--      other components do not mention it at all).

private
  ↑ʳ-inj′ : (p : ℕ) {q : ℕ} {i j : 𝔽 q} → p ↑ʳ i ≡ p ↑ʳ j → i ≡ j
  ↑ʳ-inj′ p {i = i} {j} = Fin.↑ʳ-injective p i j

  ↑ˡ-inj′ : ∀ {p} (q : ℕ) {i j : 𝔽 p} → i ↑ˡ q ≡ j ↑ˡ q → i ≡ j
  ↑ˡ-inj′ q {i} {j} = Fin.↑ˡ-injective q i j

  bodyOf : (B₁ B₂ : BindGroup) {mid : ℕ} (γ′ : Struct mid) →
           Struct (sum B₁ + sum B₂ + mid)
  bodyOf B₁ B₂ {mid} γ′ =
      (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
    ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ mid)
    ∥ (γ′ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))

  count-body-inl : ∀ (B₁ B₂ : BindGroup) {mid} (γ′ : Struct mid) (i : 𝔽 (sum B₁)) →
    count ((i ↑ˡ sum B₂) ↑ˡ mid) (bodyOf B₁ B₂ γ′) ≡ 1
  count-body-inl B₁ B₂ {mid} γ′ i = cong₂ _+_ (cong₂ _+_ c1 c2) c3
    where
    ti : Fin.toℕ (i ↑ˡ sum B₂) ≡ Fin.toℕ i
    ti = Fin.toℕ-↑ˡ i (sum B₂)
    c1 : count ((i ↑ˡ sum B₂) ↑ˡ mid)
           (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ mid) ≡ 1
    c1 = count-⋯ᵣwkʳ-↑ˡ mid (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (i ↑ˡ sum B₂)
       ■ count-⋯ᵣwkʳ-↑ˡ (sum B₂) (structBinder B₁) i
       ■ count-structBinder-lt B₁ i (Fin.toℕ<n i)
    c2 : count ((i ↑ˡ sum B₂) ↑ˡ mid)
           (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ mid) ≡ 0
    c2 = count-⋯ᵣwkʳ-↑ˡ mid (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (i ↑ˡ sum B₂)
       ■ cong (count (i ↑ˡ sum B₂)) (⋯ᵣwkˡ≡⋯weaken* (sum B₁) (structBinder B₂))
       ■ count-weaken*-lo (sum B₁) (structBinder B₂) (i ↑ˡ sum B₂)
           (subst (Nat._< sum B₁) (sym ti) (Fin.toℕ<n i))
    c3 : count ((i ↑ˡ sum B₂) ↑ˡ mid)
           (γ′ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ≡ 0
    c3 = count-weaken*-lo (sum B₁ + sum B₂) γ′ ((i ↑ˡ sum B₂) ↑ˡ mid)
           (subst (Nat._< sum B₁ + sum B₂)
                  (sym (Fin.toℕ-↑ˡ (i ↑ˡ sum B₂) mid ■ ti))
                  (Nat.≤-trans (Fin.toℕ<n i) (Nat.m≤m+n (sum B₁) (sum B₂))))

  count-body-inr : ∀ (B₁ B₂ : BindGroup) {mid} (γ′ : Struct mid) (i : 𝔽 (sum B₂)) →
    count ((sum B₁ ↑ʳ i) ↑ˡ mid) (bodyOf B₁ B₂ γ′) ≡ 1
  count-body-inr B₁ B₂ {mid} γ′ i = cong₂ _+_ (cong₂ _+_ c1 c2) c3
    where
    ti : Fin.toℕ (sum B₁ ↑ʳ i) ≡ sum B₁ + Fin.toℕ i
    ti = Fin.toℕ-↑ʳ (sum B₁) i
    c1 : count ((sum B₁ ↑ʳ i) ↑ˡ mid)
           (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ mid) ≡ 0
    c1 = count-⋯ᵣwkʳ-↑ˡ mid (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (sum B₁ ↑ʳ i)
       ■ count-⋯ᵣwkʳ-↑ʳ (sum B₂) (structBinder B₁) i
    c2 : count ((sum B₁ ↑ʳ i) ↑ˡ mid)
           (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ mid) ≡ 1
    c2 = count-⋯ᵣwkʳ-↑ˡ mid (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (sum B₁ ↑ʳ i)
       ■ cong (count (sum B₁ ↑ʳ i)) (⋯ᵣwkˡ≡⋯weaken* (sum B₁) (structBinder B₂))
       ■ count-weaken*-shift (sum B₁) (structBinder B₂) i
       ■ count-structBinder-lt B₂ i (Fin.toℕ<n i)
    c3 : count ((sum B₁ ↑ʳ i) ↑ˡ mid)
           (γ′ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ≡ 0
    c3 = count-weaken*-lo (sum B₁ + sum B₂) γ′ ((sum B₁ ↑ʳ i) ↑ˡ mid)
           (subst (Nat._< sum B₁ + sum B₂)
                  (sym (Fin.toℕ-↑ˡ (sum B₁ ↑ʳ i) mid ■ ti))
                  (Nat.+-monoʳ-< (sum B₁) (Fin.toℕ<n i)))

  before-body-inl : ∀ (B₁ B₂ : BindGroup) {mid} (γ′ : Struct mid)
    {i j : 𝔽 (sum B₁)} → before i j (structBinder B₁) →
    before ((i ↑ˡ sum B₂) ↑ˡ mid) ((j ↑ˡ sum B₂) ↑ˡ mid) (bodyOf B₁ B₂ γ′)
  before-body-inl B₁ B₂ {mid} γ′ b =
    inj₁ (inj₁ (before-⋯ᵣ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) (𝐂.wkʳ mid) (↑ˡ-inj′ mid)
           (before-⋯ᵣ (structBinder B₁) (𝐂.wkʳ (sum B₂)) (↑ˡ-inj′ (sum B₂)) b)))

  before-body-inr : ∀ (B₁ B₂ : BindGroup) {mid} (γ′ : Struct mid)
    {i j : 𝔽 (sum B₂)} → before i j (structBinder B₂) →
    before ((sum B₁ ↑ʳ i) ↑ˡ mid) ((sum B₁ ↑ʳ j) ↑ˡ mid) (bodyOf B₁ B₂ γ′)
  before-body-inr B₁ B₂ {mid} γ′ b =
    inj₁ (inj₂ (before-⋯ᵣ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) (𝐂.wkʳ mid) (↑ˡ-inj′ mid)
                 (before-⋯ᵣ (structBinder B₂) (𝐂.wkˡ (sum B₁)) (↑ʳ-inj′ (sum B₁)) b)))

  lookup-inl : ∀ {mid} (B₁ B₂ : BindGroup)
    (Γ₁ : Ctx (sum B₁)) (Γ₂ : Ctx (sum B₂)) (Γ′ : Ctx mid) (j : 𝔽 (sum B₁)) →
    ((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((j ↑ˡ sum B₂) ↑ˡ mid) ≡ Γ₁ ﹫ j
  lookup-inl B₁ B₂ Γ₁ Γ₂ Γ′ j =
    V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (j ↑ˡ sum B₂) ■ V.lookup-++ˡ Γ₁ Γ₂ j

  lookup-inr : ∀ {mid} (B₁ B₂ : BindGroup)
    (Γ₁ : Ctx (sum B₁)) (Γ₂ : Ctx (sum B₂)) (Γ′ : Ctx mid) (j : 𝔽 (sum B₂)) →
    ((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((sum B₁ ↑ʳ j) ↑ˡ mid) ≡ Γ₂ ﹫ j
  lookup-inr B₁ B₂ Γ₁ Γ₂ Γ′ j =
    V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (sum B₁ ↑ʳ j) ■ V.lookup-++ʳ Γ₁ Γ₂ j

------------------------------------------------------------------------
-- 1g.  The two halves of the crux, abstracted over the redex thread.
--
--   `head-not-later`: the handle is not the head of a LATER group, because
--   such a head is acq-typed (`laterGroup-head-acq`) and no impure constant
--   consumes an acq-headed handle (§1e).
--
--   `offset-zero-*`: the handle is at offset 0 of its group, because the
--   group's HEAD would otherwise be `;`-BEFORE it (`group-head-before`),
--   which `before-mono-≼` forbids: neither handle is mobile -- `x` by §1e,
--   the head by `group-head-¬mobile` (§1a′) -- so `ctx-¬before-*` applies.

private
  head-not-later :
    ∀ {B} {Γ : Ctx (sum B)} {c : 𝕊 0} → BindCtx c B Γ →
    ∀ {i} (g : GroupOf B i) → groupOffset g ≡ 0 →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ acq ; t ⟩)) →
    groupIndex g ≡ 0
  head-not-later C g off ¬ah with groupIndex g Nat.≟ 0
  ... | yes gi≡0 = gi≡0
  ... | no gi≢0 = ⊥-elim (¬ah (laterGroup-head-acq C g (0≢⇒0< gi≢0) off))

  NoBefore : ∀ {k n} (below : ProcessContext k n) (Q : 𝐓.Proc k) (x : 𝔽 k) → Set
  NoBefore {k} {n} below Q x =
    ∀ {Γ : Ctx n} {γ : Struct n} → Γ ; γ ⊢ₚ plug below Q →
    (y y′ : 𝔽 n) → weakenThrough below y ≡ x → y′ ≢ y →
    ¬ Mobile (Γ ﹫ y) → ¬ Mobile (Γ ﹫ y′) →
    count y γ Nat.≤ 1 → ¬ before y′ y γ

  offset-zero-inl :
    ∀ {k mid} (B₁ B₂ : BindGroup) (γ′ : Struct mid)
      {Γ₁ : Ctx (sum B₁)} {Γ₂ : Ctx (sum B₂)} {Γ′ : Ctx mid}
      (below : ProcessContext k (sum B₁ + sum B₂ + mid)) (Q : 𝐓.Proc k) (x : 𝔽 k)
      {s : 𝕊 0} {p} →
    (∀ {Δ : Ctx k} {δ : Struct k} → Δ ; δ ⊢ₚ Q → ¬ Mobile (Δ ﹫ x)) →
    NoBefore below Q x →
    New s → BindCtx (s ; end p) B₁ Γ₁ →
    ((Γ₁ ⸴* Γ₂) ⸴* Γ′ ; bodyOf B₁ B₂ γ′ ⊢ₚ plug below Q) →
    (i : 𝔽 (sum B₁)) → weakenThrough below ((i ↑ˡ sum B₂) ↑ˡ mid) ≡ x →
    (g : GroupOf B₁ i) → groupOffset g ≡ 0
  offset-zero-inl {mid = mid} B₁ B₂ γ′ {Γ₁} {Γ₂} {Γ′} below Q x
    Q-¬mob ¬bef N C ⊢body i idx g
    with groupOffset g Nat.≟ 0
  ... | yes off≡0 = off≡0
  ... | no off≢0 =
    ⊥-elim (¬bef ⊢body ((i ↑ˡ sum B₂) ↑ˡ mid) ((groupHeadIx g ↑ˡ sum B₂) ↑ˡ mid)
             idx y′≢y ¬mx ¬my′
             (Nat.≤-reflexive (count-body-inl B₁ B₂ γ′ i))
             (before-body-inl B₁ B₂ γ′ (group-head-before B₁ g 0<off)))
    where
    0<off = 0≢⇒0< off≢0
    y′≢y : ((groupHeadIx g ↑ˡ sum B₂) ↑ˡ mid) ≢ ((i ↑ˡ sum B₂) ↑ˡ mid)
    y′≢y e = groupHeadIx≢ g 0<off (↑ˡ-inj′ (sum B₂) (↑ˡ-inj′ mid e))
    ¬mx : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((i ↑ˡ sum B₂) ↑ˡ mid))
    ¬mx = TypeWalkP.ctx-type Q x (λ T → ¬ Mobile T) Q-¬mob below ⊢body _ idx
    ¬my′ : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((groupHeadIx g ↑ˡ sum B₂) ↑ˡ mid))
    ¬my′ = subst (λ T → ¬ Mobile T)
             (sym (lookup-inl B₁ B₂ Γ₁ Γ₂ Γ′ (groupHeadIx g)))
             (group-head-¬mobile N C g 0<off)

  offset-zero-inr :
    ∀ {k mid} (B₁ B₂ : BindGroup) (γ′ : Struct mid)
      {Γ₁ : Ctx (sum B₁)} {Γ₂ : Ctx (sum B₂)} {Γ′ : Ctx mid}
      (below : ProcessContext k (sum B₁ + sum B₂ + mid)) (Q : 𝐓.Proc k) (x : 𝔽 k)
      {s : 𝕊 0} {p} →
    (∀ {Δ : Ctx k} {δ : Struct k} → Δ ; δ ⊢ₚ Q → ¬ Mobile (Δ ﹫ x)) →
    NoBefore below Q x →
    New s → BindCtx (s ; end p) B₂ Γ₂ →
    ((Γ₁ ⸴* Γ₂) ⸴* Γ′ ; bodyOf B₁ B₂ γ′ ⊢ₚ plug below Q) →
    (i : 𝔽 (sum B₂)) → weakenThrough below ((sum B₁ ↑ʳ i) ↑ˡ mid) ≡ x →
    (g : GroupOf B₂ i) → groupOffset g ≡ 0
  offset-zero-inr {mid = mid} B₁ B₂ γ′ {Γ₁} {Γ₂} {Γ′} below Q x
    Q-¬mob ¬bef N C ⊢body i idx g
    with groupOffset g Nat.≟ 0
  ... | yes off≡0 = off≡0
  ... | no off≢0 =
    ⊥-elim (¬bef ⊢body ((sum B₁ ↑ʳ i) ↑ˡ mid) ((sum B₁ ↑ʳ groupHeadIx g) ↑ˡ mid)
             idx y′≢y ¬mx ¬my′
             (Nat.≤-reflexive (count-body-inr B₁ B₂ γ′ i))
             (before-body-inr B₁ B₂ γ′ (group-head-before B₂ g 0<off)))
    where
    0<off = 0≢⇒0< off≢0
    y′≢y : ((sum B₁ ↑ʳ groupHeadIx g) ↑ˡ mid) ≢ ((sum B₁ ↑ʳ i) ↑ˡ mid)
    y′≢y e = groupHeadIx≢ g 0<off (↑ʳ-inj′ (sum B₁) (↑ˡ-inj′ mid e))
    ¬mx : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((sum B₁ ↑ʳ i) ↑ˡ mid))
    ¬mx = TypeWalkP.ctx-type Q x (λ T → ¬ Mobile T) Q-¬mob below ⊢body _ idx
    ¬my′ : ¬ Mobile (((Γ₁ ⸴* Γ₂) ⸴* Γ′) ﹫ ((sum B₁ ↑ʳ groupHeadIx g) ↑ˡ mid))
    ¬my′ = subst (λ T → ¬ Mobile T)
             (sym (lookup-inr B₁ B₂ Γ₁ Γ₂ Γ′ (groupHeadIx g)))
             (group-head-¬mobile N C g 0<off)

  -- The thread-level facts, for the two hole shapes.
  Q-¬mob-direct :
    ∀ {k} (E : Frame* k) (c : Const) (x : 𝔽 k) → ImpureHandleConst c →
    ∀ {Δ : Ctx k} {δ : Struct k} →
    Δ ; δ ⊢ₚ 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ → ¬ Mobile (Δ ﹫ x)
  Q-¬mob-direct E c x ic ⊢Q =
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole =
          ⊢[]*⁻¹ E (K c ·¹ (` x)) (inv-⟪⟫ ⊢Q)
    in app-¬mobile ic ⊢hole

  Q-¬acq-direct :
    ∀ {k} (E : Frame* k) (c : Const) (x : 𝔽 k) → ImpureHandleConst c →
    ∀ {Δ : Ctx k} {δ : Struct k} →
    Δ ; δ ⊢ₚ 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Δ ﹫ x) ≃ ⟨ acq ; t ⟩))
  Q-¬acq-direct E c x ic ⊢Q =
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole =
          ⊢[]*⁻¹ E (K c ·¹ (` x)) (inv-⟪⟫ ⊢Q)
    in app-¬acq ic ⊢hole

  Q-¬mob-pair :
    ∀ {k} (E : Frame* k) (c : Const) (w : Tm k) (x : 𝔽 k) → ImpureHandleConst c →
    ∀ {Δ : Ctx k} {δ : Struct k} →
    Δ ; δ ⊢ₚ 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ → ¬ Mobile (Δ ﹫ x)
  Q-¬mob-pair E c w x ic ⊢Q =
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole =
          ⊢[]*⁻¹ E (K c ·¹ (w ⊗ (` x))) (inv-⟪⟫ ⊢Q)
    in pair-¬mobile ic ⊢hole

  Q-¬acq-pair :
    ∀ {k} (E : Frame* k) (c : Const) (w : Tm k) (x : 𝔽 k) → ImpureHandleConst c →
    ∀ {Δ : Ctx k} {δ : Struct k} →
    Δ ; δ ⊢ₚ 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ →
    ¬ (Σ[ t ∈ 𝕊 0 ] ((Δ ﹫ x) ≃ ⟨ acq ; t ⟩))
  Q-¬acq-pair E c w x ic ⊢Q =
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole =
          ⊢[]*⁻¹ E (K c ·¹ (w ⊗ (` x))) (inv-⟪⟫ ⊢Q)
    in pair-¬acq ic ⊢hole

------------------------------------------------------------------------
-- 2.  THE FOUR THEOREMS.
--
-- Each is exactly the statement of the corresponding `Position.*` type.
--
--   * `Position.resolve` / `Binder`             -- which `ν` binds the handle;
--   * `Position.binderTyping`                   -- the `TP-Res` payload of the
--                                                  owning binder;
--   * `Position.group-head-before`              -- the order the binder
--                                                  PRESCRIBES inside a group;
--   * `Position.before-mono-≼`, `count-≼-eq`,
--     `¬unr-handle`                             -- `≼` neither creates a `;`
--                                                  nor changes multiplicities;
--   * `ThreadOrder.thread-¬before` /
--     `ContextOrder.ctx-¬before-direct`/`-pair` -- Phase 4a: the ACTUAL
--                                                  structure the derivation
--                                                  forces, walked down to the
--                                                  redex thread.
--
-- `impure-redex-head` / `pair-arg-redex-head` split as the sketch in
-- `Position.agda` §7 does:
--
--   (iii) "same group, offset > 0" (`offset-zero-inl/inr`, §1g):
--         `group-head-before` puts the group's own head `;`-before `x`, and
--         `ctx-¬before-*` refutes that.  It wants `¬ Mobile` of BOTH: for `x`
--         that is §1e, for the head `group-head-¬mobile` (§1a′) -- a Mobile
--         head would make its group a singleton, leaving no room for `x`.
--         The linearity bound `count x γ ≤ 1` is §1f's `count-body-*`
--         (`structBinder` lists each variable exactly once).
--   (iv)  "x IS the head of a later group" (`head-not-later`, §1g): such a
--         head is acq-typed (`laterGroup-head-acq`, §1a″), and no impure
--         constant consumes an acq-headed handle (§1e): `⟨ skip ⟩` by
--         `AtomCons.acq-;-¬skips`, `⟨ ret ⟩` / `⟨ end p ⟩` / `⟨ msg ⁇ T ⟩` by
--         `acq-;-≄ret/≄end/≄msg`, `⟨ brn p s₁ s₂ ⟩` by `acq-;-¬brn`, and
--         `send`'s pair component by the same `msg` refutation.
--
-- `drop-first-group-singleton` then adds `drop`'s group SHAPE (§1d), and
-- `acq-non-first-group-head` is the mirror image, using `first-group-noAcq`
-- and `laterGroup-interior-noAcq` (§1a) against `acq`'s own typing (§1c).

AcqHeadedT : 𝕋 → Set
AcqHeadedT T = Σ[ t ∈ 𝕊 0 ] (T ≃ ⟨ acq ; t ⟩)

-- The binder is taken EXPLICITLY: `drop-first-group-singleton` needs the
-- statement about the binder it has already destructured, and
-- `HeadOfFirstGroup (resolve ctx x)` does not reduce there.
impure-redex-head′ :
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {c : Const} {x : 𝔽 k}
    (bnd : Binder ctx x) →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ →
  ImpureHandleConst c → HeadOfFirstGroup bnd
impure-redex-head′ {E = E} {c = c} {x = x}
  bnd@(binder {mid} B₁ B₂ above below dec local index-eq) ⊢plug ic
  with binderTyping bnd 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with sideOf B₁ B₂ local
... | inl i =
  let off≡0 = offset-zero-inl B₁ B₂ γ′ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ′ = Γ′} below 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x
                (Q-¬mob-direct E c x ic) (ctx-¬before-direct below {E = E} {c = c} {x = x} ic)
                N C ⊢body i index-eq (groupOf B₁ i)
      ¬ah = subst (λ T → ¬ AcqHeadedT T) (lookup-inl B₁ B₂ Γ₁ Γ₂ Γ′ i)
              (TypeWalkP.ctx-type 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x (λ T → ¬ AcqHeadedT T)
                 (Q-¬acq-direct E c x ic) below ⊢body _ index-eq)
  in head-not-later C (groupOf B₁ i) off≡0 ¬ah , off≡0
... | inr i =
  let off≡0 = offset-zero-inr B₁ B₂ γ′ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ′ = Γ′} below 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x
                (Q-¬mob-direct E c x ic) (ctx-¬before-direct below {E = E} {c = c} {x = x} ic)
                (new-dual N) C′ ⊢body i index-eq (groupOf B₂ i)
      ¬ah = subst (λ T → ¬ AcqHeadedT T) (lookup-inr B₁ B₂ Γ₁ Γ₂ Γ′ i)
              (TypeWalkP.ctx-type 𝐓.⟪ E [ K c ·¹ (` x) ]* ⟫ x (λ T → ¬ AcqHeadedT T)
                 (Q-¬acq-direct E c x ic) below ⊢body _ index-eq)
  in head-not-later C′ (groupOf B₂ i) off≡0 ¬ah , off≡0

impure-redex-head : ImpureRedexHead
impure-redex-head {ctx = ctx} {E = E} {c = c} {x = x} =
  impure-redex-head′ {E = E} {c = c} {x = x} (resolve ctx x)

pair-arg-redex-head′ :
  ∀ {k} {ctx : ProcessContext k 0} {E : Frame* k} {c : Const}
    {w : Tm k} {x : 𝔽 k} (bnd : Binder ctx x) →
  [] ; [] ⊢ₚ plug ctx 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ →
  ImpureHandleConst c → HeadOfFirstGroup bnd
pair-arg-redex-head′ {E = E} {c = c} {w = w} {x = x}
  bnd@(binder {mid} B₁ B₂ above below dec local index-eq) ⊢plug ic
  with binderTyping bnd 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with sideOf B₁ B₂ local
... | inl i =
  let off≡0 = offset-zero-inl B₁ B₂ γ′ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ′ = Γ′} below 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x
                (Q-¬mob-pair E c w x ic) (ctx-¬before-pair below {E = E} {c = c} {w = w} {x = x} ic)
                N C ⊢body i index-eq (groupOf B₁ i)
      ¬ah = subst (λ T → ¬ AcqHeadedT T) (lookup-inl B₁ B₂ Γ₁ Γ₂ Γ′ i)
              (TypeWalkP.ctx-type 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x (λ T → ¬ AcqHeadedT T)
                 (Q-¬acq-pair E c w x ic) below ⊢body _ index-eq)
  in head-not-later C (groupOf B₁ i) off≡0 ¬ah , off≡0
... | inr i =
  let off≡0 = offset-zero-inr B₁ B₂ γ′ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ′ = Γ′} below 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x
                (Q-¬mob-pair E c w x ic) (ctx-¬before-pair below {E = E} {c = c} {w = w} {x = x} ic)
                (new-dual N) C′ ⊢body i index-eq (groupOf B₂ i)
      ¬ah = subst (λ T → ¬ AcqHeadedT T) (lookup-inr B₁ B₂ Γ₁ Γ₂ Γ′ i)
              (TypeWalkP.ctx-type 𝐓.⟪ E [ K c ·¹ (w ⊗ (` x)) ]* ⟫ x (λ T → ¬ AcqHeadedT T)
                 (Q-¬acq-pair E c w x ic) below ⊢body _ index-eq)
  in head-not-later C′ (groupOf B₂ i) off≡0 ¬ah , off≡0

pair-arg-redex-head : PairArgRedexHead
pair-arg-redex-head {ctx = ctx} {E = E} {c = c} {w = w} {x = x} =
  pair-arg-redex-head′ {E = E} {c = c} {w = w} {x = x} (resolve ctx x)

drop-first-group-singleton : DropFirstGroupSingleton
drop-first-group-singleton {ctx = ctx} {E = E} {x = x} ⊢plug
  with resolve ctx x
... | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  with impure-redex-head′ {E = E} {c = `drop} {x = x} bnd ⊢plug `drop
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
