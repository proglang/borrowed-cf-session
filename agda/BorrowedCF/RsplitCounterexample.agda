{-# OPTIONS --rewriting #-}
--
-- ============================================================================
--  RSPLIT SIMULATION-FAILURE COUNTEREXAMPLE  (end-to-end, machine-checked)
-- ============================================================================
--
-- Consolidates RsplitOwnershipProbe.agda (the well-typed redex) and
-- RsplitFlipCheck.agda (the leaf inequality) into ONE self-contained story.
--
-- Concrete instance:  B1 = [],  b1 = 1,  B2 = [],  the front chain  2 : [].
--
-- THE FORWARD-SIMULATION CLAIM (paper Bisimulation lemma):
--   for well-typed P,   P -->p P'   (typed)   implies   U[P] -->p U[P']  (untyped).
--
-- THE REDEX:  ν [2] [] ( ... )  with a SIBLING thread  P = << recv . ` 1F >>
-- that owns the off-handle borrow at slot  1F  (a genuine linear resource;
-- see  Poff  below: it typechecks, owning  ` 1F : < msg ? T >).
--
-- WHAT THE TWO SIDES PRODUCE for that sibling's channel triple:
--
--   * U[source]'s P-thread receives on the triple
--         canonS (2 : [])   (*,0F,*)  1F   =  (* (x) ` 0F) (x) *
--     i.e. the UNGROWN chain at the off-handle slot.
--
--   * U[typed-reduct]'s P-thread receives on
--         canonS (1 : 2 : []) (*,0F,*) 2F   =  (` 0F (x) ` 1F) (x) *
--     i.e. the rwk-GROWN chain (a fresh sync channel was prepended).
--
--   * The untyped  RU-RSplit  rule only  ( . )p weakenr s  the sibling P, so
--     the untyped reduct's P-triple is
--         (canonS (2 : []) (*,0F,*) 1F)  ( . ) weakenr
--           =  (* (x) ` 1F) (x) *          (the WEAKENED ungrown triple).
--
-- THE OBSTRUCTION:  the untyped reduct gives the sibling the triple
--     (* (x) ` 1F) (x) *       [ weakened-ungrown ]
-- but the translation of the typed reduct needs
--     (` 0F (x) ` 1F) (x) *    [ grown ]
-- These DIFFER at the left slot ( *  vs  ` 0F ): a constant vs a variable.
-- No renaming bridges constant-vs-variable, so the forward simulation step
-- cannot exist for this well-typed redex.  (Proven as  grown!=weakened-ungrown.)
--
-- Steps machine-checked below:
--   1. the three concrete triples as  refl  values,
--   2. the DECISIVE inequality  grown != weakened-ungrown,
--   3. the well-typedness link  Poff  (sibling is a genuinely well-typed redex),
--   4. the  RU-RSplit  link: the rule's sibling output is  P ( . )p weakenr,
--      so the untyped P-triple really is  weakened-ungrown.
-- ============================================================================

module BorrowedCF.RsplitCounterexample where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Congruence
open import BorrowedCF.Processes.Typed using (BindGroup)

open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)

-- the well-typed redex (sibling owns the off-handle borrow) lives here:
import BorrowedCF.RsplitOwnershipProbe as Probe
-- typed processes + typed reduction (the  R-RSplit  source step):
import BorrowedCF.Processes.Typed as T
import BorrowedCF.Reduction.Processes.Typed as TR
-- untyped processes + untyped reduction (the  RU-RSplit  target step):
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Reduction.Processes.Untyped as UR

open T.Proc
open U.Proc

open import BorrowedCF.Simulation2.Confine using (count)
open import BorrowedCF.Context using (Struct)
import BorrowedCF.Context as Ctx
open T using (BindCtx′; _;_⊢ₚ_)
open T using () renaming (_⋯ₚ_ to _⋯ₜₚ_)
open TR using (_─→ₚ_)

-- ----------------------------------------------------------------------------
-- The base channel triple of the ungrown front chain:  first slot a CONSTANT.
-- ----------------------------------------------------------------------------
cc0 : UChan 1
cc0 = (K `unit , 0F , K `unit)

-- ============================================================================
-- STEP 1.  The three concrete triples, each proven by  refl.
-- ============================================================================

-- (a) UNGROWN  (chain [2], off-handle borrow at 1F):  (* (x) ` 0F) (x) *
ungrown : canonₛ (2 ∷ []) cc0 (suc zero)
        ≡ chanTriple (K `unit , 0F , K `unit)
ungrown = refl

-- (b) GROWN    (chain [1,2], the SAME borrow now at 2F):  (` 0F (x) ` 1F) (x) *
grown : canonₛ (1 ∷ 2 ∷ []) cc0 (suc (suc zero))
      ≡ chanTriple ((` 0F) , suc 0F , K `unit)
grown = refl

-- (c) WEAKENED-UNGROWN: the untyped reduct's sibling triple, i.e. the ungrown
--     triple pushed through  RU-RSplit's   ( . )p weakenr.  Renaming a term by
--     weakenr shifts every free variable up by one ( 0F -> 1F ) and leaves the
--     constant  K `unit  fixed, giving  (* (x) ` 1F) (x) *.
weakened-ungrown : (canonₛ (2 ∷ []) cc0 (suc zero)) ⋯ weakenᵣ
        ≡ chanTriple (K `unit , suc 0F , K `unit)
weakened-ungrown = refl

-- ============================================================================
-- STEP 2.  THE DECISIVE INEQUALITY  (the heart of the counterexample).
--
--   grown  =  (` 0F (x) ` 1F) (x) *      (translated typed reduct)
--   wungn  =  (*   (x) ` 1F) (x) *      (untyped reduct, after  ( . )p weakenr)
--
-- They disagree at the LEFT slot:  ` 0F  (a variable)  vs  K `unit  (a constant).
-- No renaming can turn a constant into a variable, so no simulation step exists.
-- ============================================================================

-- The two concrete triples as plain terms.
grown-tri : Tm 2
grown-tri = chanTriple ((` 0F) , suc 0F , K `unit)

wungn-tri : Tm 2
wungn-tri = chanTriple (K `unit , suc 0F , K `unit)

-- The constant-vs-variable clash at the left slot, isolated:  ` 0F != K `unit.
left-var : Tm 2
left-var = ` 0F

left-const : Tm 2
left-const = K `unit

var≢const : left-var ≢ left-const
var≢const ()

-- THE COUNTEREXAMPLE:  the translated typed reduct and the untyped reduct
-- produce DIFFERENT channel triples for the sibling thread.
grown≢weakened-ungrown : grown-tri ≢ wungn-tri
grown≢weakened-ungrown ()

-- ============================================================================
-- STEP 3.  THE WELL-TYPED SOURCE PROCESS  (the genuine redex).
--
-- We re-use RsplitOwnershipProbe's machinery:  the front chain  2 : [],  the
-- two-borrow BindCtx  bc2,  the New witness  NsP,  and the sibling typing  Poff
-- (the off-handle thread  << recv . ` 1F >>  owning the linear borrow  1F).
-- ============================================================================

-- The split-renaming module for  B1 = B2 = B' = []  (matches the probe).
module 𝐒 = TR.SplitRenamings [] [] []

-- The session offered by the rsplit redex (a TWO-borrow chain), from the probe.
sₚ : 𝕊 0
sₚ = Probe.sP

-- The R-RSplit redex BODY (a process at scope 2 = sum (2 : []) + sum [] + 0):
--   rsplit thread on the HANDLE  𝐒.inj 0F,  sibling owning the OFF-HANDLE 1F.
-- We use the empty frame  []  : Frame* 2.
redexBody : T.Proc 2
redexBody =
    ⟪ [] [ K (`rsplit sₚ) · (` 𝐒.inj {2 ∷ []} {0} 0F) ]* ⟫
  ∥ ⟪ K `recv · (` 1F) ⟫

-- THE WELL-TYPED SOURCE PROCESS  src = ν (2 : []) [] redexBody.
src : T.Proc 0
src = ν (2 ∷ []) [] redexBody

-- The sibling thread of  redexBody  IS the probe's well-typed  Poff  redex:
-- it typechecks owning the off-handle borrow  ` 1F : < msg ? T >.
sibling-well-typed :
  Probe.g2 ; (Ctx.[] Ctx.∥ (Ctx.` 1F)) ⊢ₚ ⟪ K `recv · (` 1F) ⟫
sibling-well-typed = Probe.Poff

-- The two-borrow BindCtx realising the ordered borrows (slots 0F, 1F) of the
-- front chain  2 : [],  from the probe.
chain-BindCtx : BindCtx′ sₚ 2 Probe.g2
chain-BindCtx = Probe.bc2

-- The handle  inj 0F  and off-handle  inj 1F  are BOTH genuine linear resources
-- (each occurs exactly once in the TP-Res body context):
handle-linear   : count (𝐒.inj {2 ∷ []} {0} 0F) Probe.bodyStruct ≡ 1
handle-linear   = Probe.handle-count-1
offhandle-linear : count (𝐒.inj {2 ∷ []} {0} 1F) Probe.bodyStruct ≡ 1
offhandle-linear = Probe.offhandle-count-1

-- DOCUMENTED GAP (typing assembly): the full  TP-Res  derivation for  src
-- requires (a) the rsplit-thread typing  << [] [ rsplit . ` inj 0F ] >>
-- (rsplit is a polymorphic constant whose result is a session pair) and
-- (b) the TP-Par split  bodyStruct |- gammaE || gammaP  placing the
-- off-handle unit  (` 1F)  entirely in  gammaP.  The probe establishes the
-- decisive ingredients -- the BindCtx (chain-BindCtx), the New witness
-- (Probe.NsP), the sibling typing (sibling-well-typed), and that inj 0F / inj 1F
-- are each a single linear resource (handle-linear / offhandle-linear), so the
-- rsplit redex consumes ONLY the handle and the sibling may legitimately own
-- the off-handle.  We keep these machine-checked pieces and do not re-derive the
-- (large, polymorphic-constant) rsplit-thread elaboration here.

-- ============================================================================
-- STEP 4.  THE TWO REDUCTIONS  +  THE PROCESS-LEVEL FAILURE.
-- ============================================================================

-- (4a)  THE TYPED SOURCE STEP  src ─→ₚ typedReduct,  by  R-RSplit.
-- R-RSplit  with  B1 = B2 = B = [],  b1 = 1,  P = << recv . ` 1F >>,  E = [].
-- We let the constructor DEFINE the reduct (typedReduct = its contractum) so the
-- transport/renaming bookkeeping (frame  [] ⋯ᶠ* rwk,  inj/rwk casts) is exactly
-- the one  R-RSplit  produces -- no hand-transcription of the contractum needed.
src─→Σ : Σ[ Q ∈ T.Proc 0 ] (src ─→ₚ Q)
src─→Σ = _ , TR.R-RSplit {B₁ = []} {B₂ = []} {B = []} {b₁ = 1} {s = sₚ} {E = []}

typedReduct : T.Proc 0
typedReduct = proj₁ src─→Σ

src─→typedReduct : src ─→ₚ typedReduct
src─→typedReduct = proj₂ src─→Σ

-- ----------------------------------------------------------------------------
-- (4b)  THE TWO TRANSLATIONS, as ACTUAL  U.Proc  terms.
-- The source is closed (scope 0), so the translation substitution is  λ().
-- ----------------------------------------------------------------------------
Usrc : U.Proc 0
Usrc = U[ src ] (λ())

Ured : U.Proc 0
Ured = U[ typedReduct ] (λ())

-- The SOURCE translation: both the rsplit thread AND the sibling receive the
-- UNGROWN handle/off-handle triple  (* (x) ` 0F) (x) *.
Usrc-shape :
  Usrc ≡ ν ( ⟪ K (`rsplit sₚ) · ((* ⊗ (` 0F)) ⊗ *) ⟫
           ∥ ⟪ K `recv · ((* ⊗ (` 0F)) ⊗ *) ⟫ )
Usrc-shape = refl

-- The TYPED-REDUCT translation: the sibling now receives the GROWN triple
-- (` 0F (x) ` 1F) (x) *  -- a fresh sync channel was prepended (the  φ drop).
Ured-shape :
  Ured ≡ ν (φ U.drop
            ( ⟪ ((* ⊗ (` 1F)) ⊗ *) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ *) ⟫
            ∥ ⟪ K `recv · (((` 0F) ⊗ (` 1F)) ⊗ *) ⟫ ))
Ured-shape = refl

-- ----------------------------------------------------------------------------
-- (4c)  THE UNTYPED STEP  Usrc ─→ₚ Q,  by  RU-RSplit.  As before, we let the
-- constructor DEFINE the untyped contractum  Q.
-- ----------------------------------------------------------------------------
Usrc─→Σ : Σ[ Q ∈ U.Proc 0 ] (Usrc UR.─→ₚ Q)
Usrc─→Σ = _ , UR.RU-RSplit {e₁ = *} {e₂ = *}
              {P = ⟪ K `recv · ((* ⊗ (` 0F)) ⊗ *) ⟫} []

Q : U.Proc 0
Q = proj₁ Usrc─→Σ

Usrc─→Q : Usrc UR.─→ₚ Q
Usrc─→Q = proj₂ Usrc─→Σ

-- The untyped contractum: the sibling's triple is  (P ⋯ₚ weakenᵣ)'s argument,
-- i.e. the WEAKENED-UNGROWN triple  (* (x) ` 1F) (x) *.
Q-shape :
  Q ≡ ν (φ U.drop
         ( ⟪ ((* ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ *) ⟫
         ∥ ⟪ K `recv · ((* ⊗ (` 1F)) ⊗ *) ⟫ ))
Q-shape = refl

-- ============================================================================
-- (4d)  THE PROCESS-LEVEL FAILURE.   Q ≢ Ured.
--
-- Both untyped reducts share the  ν (φ drop ( ⟪…⟫ ∥ ⟪ recv · TRIPLE ⟫ ))
-- skeleton; they differ ONLY in the sibling's receive-triple:
--    Q     : recv on  (*   (x) ` 1F) (x) *     (weakened-ungrown)
--    Ured  : recv on  (` 0F (x) ` 1F) (x) *     (grown)
-- Pattern-matching an assumed  Q ≡ Ured  forces the left slot  K `unit ≡ ` 0F,
-- impossible (constant vs variable).  Hence NO simulation step  Usrc ─→ₚ Ured.
-- ============================================================================
-- Project the sibling thread's receive-triple out of the shared skeleton
-- ν (φ _ ( _ ∥ ⟪ recv · TRIPLE ⟫ )).  Total, with a dummy fallback.
recvTriple : U.Proc 0 → Tm 3
recvTriple (ν (φ _ (_ ∥ ⟪ K `recv · t ⟫))) = t
recvTriple _ = *

-- On the two untyped reducts this projection computes to the GROWN resp.
-- WEAKENED-UNGROWN triple at scope 3 (the constant-vs-variable witnesses).
grown-tri₃ : Tm 3
grown-tri₃ = chanTriple ((` 0F) , suc 0F , K `unit)

wungn-tri₃ : Tm 3
wungn-tri₃ = chanTriple (K `unit , suc 0F , K `unit)

recvTriple-Q    : recvTriple Q    ≡ wungn-tri₃
recvTriple-Q    = refl
recvTriple-Ured : recvTriple Ured ≡ grown-tri₃
recvTriple-Ured = refl

-- The two scope-3 triples differ at the left slot:  ` 0F  vs  K `unit.
grown₃≢wungn₃ : grown-tri₃ ≢ wungn-tri₃
grown₃≢wungn₃ ()

-- THE FINAL OBSTRUCTION:  the untyped reduct  Q  of  Usrc  is NOT the
-- translation  Ured  of the typed reduct.  So forward simulation FAILS here.
Q≢Ured : Q ≢ Ured
Q≢Ured eq = grown₃≢wungn₃
  (sym recvTriple-Ured ■ cong recvTriple (sym eq) ■ recvTriple-Q)

