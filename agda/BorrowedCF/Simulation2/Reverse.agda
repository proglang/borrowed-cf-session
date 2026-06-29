module BorrowedCF.Simulation2.Reverse where

-- | REVERSE direction of the bisimulation (reflection / image-closure).
--
--   sim← : for a well-typed source P translating to U[ P ] σ, every UNTYPED
--   step U[ P ] σ ─→ₚ Q is the image of a TYPED step P ─→ₚ P′ with
--   Q ≋ U[ P′ ] σ.
--
--   This is a SCOPING kickoff.  It establishes:
--     * the sim← statement (case-split on ALL untyped RU-* constructors),
--     * the translation-inversion lemmas it needs (inv-U-∥, inv-U-⟪⟫ PROVEN;
--       inv-U-ν stated + partially attacked),
--     * the easy/structural cases proven where possible,
--     * the hard redex-inversions as CLEARLY-NOTED interaction holes.
--
--   We do NOT import BorrowedCF.Simulation2.Congruence (mid-edit elsewhere);
--   anything that needs the reverse of U-≋ is left a noted hole.

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.TranslationProperties
  using (≡→≋; U-cong)
-- Reusable reverse-direction inversion helpers (channel-var contradictions,
-- value reflection, and the typed expression-reduction reflection ⋯→-reflect
-- that powers RU-Exp) live in BorrowedCF.Simulation2.ReverseInv.
open import BorrowedCF.Simulation2.ReverseInv using (⋯→-reflect)
import Data.Sum as Sum
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; ⊢-≋; bindCtx⇒chanCtx)

------------------------------------------------------------------------
-- Expression-reduction REFLECTION through a value substitution.
--
--   The reverse of Frames.⋯→-⋯ₛ: substituting VALUES into a term cannot
--   create new head redexes (a value never reduces, and a variable maps to a
--   value), so every step of  e₀ ⋯ σ  is the image of a step of e₀.
------------------------------------------------------------------------

-- A value has no head reduction.
value-no-head : {t : Tm n} → Value t → {e₂ : Tm n} → ¬ (t ─→ e₂)
value-no-head V-`         ()
value-no-head V-K         ()
value-no-head V-λ         ()
value-no-head (V-⊗ V₁ V₂) ()
value-no-head (V-⊕ V)     ()

-- A term that is a value never reduces.
value-↛ : {t : Tm n} → Value t → {e₂ : Tm n} → ¬ (t ⋯→ e₂)
value-↛ V (E-□ hred)             = value-no-head V hred
value-↛ V (E-Ctx (□· _)  red)    with V
... | ()
value-↛ V (E-Ctx (_ ·□)  red)    with V
... | ()
value-↛ V (E-Ctx (□⊗ _)  red)    with V
... | V-⊗ V₁ V₂ = value-↛ V₁ red
value-↛ V (E-Ctx (_ ⊗□)  red)    with V
... | V-⊗ V₁ V₂ = value-↛ V₂ red
value-↛ V (E-Ctx (□; _)  red)    with V
... | ()
value-↛ V (E-Ctx (`let-`in _)  red) with V
... | ()
value-↛ V (E-Ctx (`let⊗-`in _) red) with V
... | ()
value-↛ V (E-Ctx (`inj□ i) red)  with V
... | V-⊕ V′ = value-↛ V′ red
value-↛ V (E-Ctx `case□`of⟨ _ ; _ ⟩ red) with V
... | ()

-- Value reflection: under a VSub, a substituted term is a value iff the
-- source term is.  (Needed to recover the source-side Value side conditions of
-- the head reductions.)
value-⋯⁻¹ : (σ : m →ₛ n) → VSub σ → (e₀ : Tm m) → Value (e₀ ⋯ σ) → Value e₀
value-⋯⁻¹ σ Vσ (` x)               V = V-`
value-⋯⁻¹ σ Vσ (K c)               V = V-K
value-⋯⁻¹ σ Vσ (ƛ e)               V = V-λ
value-⋯⁻¹ σ Vσ (e₁ ⊗ e₂) (V-⊗ V₁ V₂) =
  V-⊗ (value-⋯⁻¹ σ Vσ e₁ V₁) (value-⋯⁻¹ σ Vσ e₂ V₂)
value-⋯⁻¹ σ Vσ (`inj i e)  (V-⊕ V)    = V-⊕ (value-⋯⁻¹ σ Vσ e V)

-- NOTE (reflection of expression reduction): a TYPING-FREE reflection
--   ⋯→-reflect : VSub σ → (e₀ ⋯ σ) ⋯→ e₂ → Σ e₀′. e₀ ⋯→ e₀′ × e₂ ≡ e₀′ ⋯ σ
--   is mathematically FALSE for an arbitrary value substitution: a variable
--   may map to a λ (or ⊗ / inj) value, so σ can CREATE a head redex that the
--   source e₀ does not have (e.g. e₀ = (` x) · v with σ x = ƛ body).  Ruling
--   this out needs the source typing: a channel-typed variable can never head
--   an application / let⊗ / case.  The helpers below (value-↛, value-no-head,
--   value-⋯⁻¹) are the SOUND, typing-free fragments and are reused elsewhere;
--   the full reflection is carried as the RU-Exp hole (see sim←ᵍ).


------------------------------------------------------------------------
-- Translation-inversion lemmas.
--
-- U[_] has exactly three structural clauses (Bisim.agda:50-56):
--     U[ ⟪ e ⟫     ] σ = ⟪ e ⋯ σ ⟫
--     U[ P ∥ Q     ] σ = U[ P ] σ ∥ U[ Q ] σ
--     U[ ν B₁ B₂ P ] σ = ν (φ-telescope …)
-- so the head constructor of U[ P ] σ is determined by the head of P.  The
-- inversion lemmas below read P off the head of U[ P ] σ.
------------------------------------------------------------------------

-- inv-U-⟪⟫ : a translated thread came from a source thread.
inv-U-⟪⟫ : (P : TP.Proc m) (σ : m →ₛ n) {e : Tm n}
         → U[ P ] σ ≡ UP.⟪ e ⟫
         → Σ[ e₀ ∈ Tm m ] (P ≡ TP.⟪ e₀ ⟫ × e ≡ e₀ ⋯ σ)
inv-U-⟪⟫ (TP.⟪ e₀ ⟫)    σ refl = e₀ , refl , refl
inv-U-⟪⟫ (P TP.∥ Q)     σ ()
inv-U-⟪⟫ (TP.ν B₁ B₂ P) σ ()

-- inv-U-∥ : a translated parallel composition came from a source one, and the
-- two sides are themselves translation images.
inv-U-∥ : (P : TP.Proc m) (σ : m →ₛ n) {A B : UP.Proc n}
        → U[ P ] σ ≡ A UP.∥ B
        → Σ[ P₁ ∈ TP.Proc m ] Σ[ P₂ ∈ TP.Proc m ]
            (P ≡ P₁ TP.∥ P₂ × A ≡ U[ P₁ ] σ × B ≡ U[ P₂ ] σ)
inv-U-∥ (TP.⟪ e₀ ⟫)    σ ()
inv-U-∥ (P TP.∥ Q)     σ refl = P , Q , refl , refl , refl
inv-U-∥ (TP.ν B₁ B₂ P) σ ()

-- inv-U-ν : a translated restriction came from a source restriction.  HARD:
-- the source ν B₁ B₂ P translates to a single untyped ν wrapping a φ-nest of
-- depth (syncs B₁ + syncs B₂) (Bisim.agda:52-56 via UB[_]).  Recovering
-- B₁,B₂,P from the φ-telescope is the structural crux.  We can read off the
-- head (P must be a TP.ν) immediately, which is all the statement below
-- claims — it is PROVEN hole-free.  The harder content (relating the untyped
-- body X to the precise UB-telescope, i.e. X ≡ φ-nest over U[ P₀ ] (UB-σ)) is
-- DELIBERATELY OMITTED from this kickoff statement; the channel-op cases that
-- need it (RU-Res and all ν-headed redexes) carry the body-recovery debt in
-- their own holes (see assessment).
--
-- BODY (priority #1).  We additionally return the body equation
--   UP.ν X ≡ U[ TP.ν B₁ B₂ P₀ ] σ
-- which — combined with P ≡ TP.ν B₁ B₂ P₀ — pins X to the exact φ-telescope
-- that U[_] builds for ν B₁ B₂ P₀ at σ:  X is definitionally
--   UB[ B₁ ] (*,0F,*) (λ σ₁ → UB[ B₂ ] (*, weaken* (syncs B₁) 1F ,*)
--     (λ σ₂ → U[ P₀ ] bigσ))     (Bisim.agda U[ ν … ]).
-- So the φ-nest depth (syncs B₁ + syncs B₂) and the chanTriple/UB data are all
-- recovered; this is what the ν-headed redex inversions consume.  (We cannot
-- recover B₁,B₂ as LISTS from the depth alone — only syncs Bᵢ + sum Bᵢ — but
-- that is fine for ≋, since the body equation already names a concrete B₁,B₂.)
inv-U-ν : (P : TP.Proc m) (σ : m →ₛ n) {X : UP.Proc (2 + n)}
        → U[ P ] σ ≡ UP.ν X
        → Σ[ B₁ ∈ TP.BindGroup ] Σ[ B₂ ∈ TP.BindGroup ]
            Σ[ P₀ ∈ TP.Proc (sum B₁ + sum B₂ + m) ]
            (P ≡ TP.ν B₁ B₂ P₀ × UP.ν X ≡ U[ TP.ν B₁ B₂ P₀ ] σ)
inv-U-ν (TP.⟪ e₀ ⟫)    σ ()
inv-U-ν (P TP.∥ Q)     σ ()
inv-U-ν (TP.ν B₁ B₂ P) σ refl = B₁ , B₂ , P , refl , refl

------------------------------------------------------------------------
-- The reverse-simulation statement.
------------------------------------------------------------------------

sim← : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
     → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
     → {Q : UP.Proc n} → U[ P ] σ UR.─→ₚ Q
     → Σ[ P′ ∈ TP.Proc m ] (P TR.─→ₚ P′ × Q UP.≋ U[ P′ ] σ)

-- The untyped step has LHS index U[ P ] σ, a stuck application, so a direct
-- `with` case-split on it gets a SplitError (UnificationStuck).  We generalise:
-- abstract the LHS to a fresh variable R with a proof R ≡ U[ P ] σ, split on
-- the reduction (now R is a variable so every RU-* constructor unifies), and
-- read P back off the equality with the inv-U-* lemmas.
sim←ᵍ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
      → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
      → {R Q : UP.Proc n} → R ≡ U[ P ] σ → R UR.─→ₚ Q
      → Σ[ P′ ∈ TP.Proc m ] (P TR.─→ₚ P′ × Q UP.≋ U[ P′ ] σ)

sim← σ Vσ Γ-S ⊢P red = sim←ᵍ σ Vσ Γ-S ⊢P refl red

------------------------------------------------------------------------
-- RU-Exp : R = ⟪ e₁ ⟫ steps by an expression reduction e₁ ⋯→ e₂.
--   eq : ⟪ e₁ ⟫ ≡ U[ P ] σ  ⇒ via inv-U-⟪⟫, P = ⟪ e₀ ⟫ with e₁ ≡ e₀ ⋯ σ.
--   We then need to REFLECT the substituted step e₀ ⋯ σ ⋯→ e₂ back to a source
--   step e₀ ⋯→ e₀′ with e₂ ≡ e₀′ ⋯ σ, and conclude TR.R-Exp.
--   HOLE — and the reason it is hard is now PINNED DOWN: a TYPING-FREE
--   reflection lemma  ⋯→-reflect : VSub σ → e₀ ⋯ σ ⋯→ e₂ → Σ e₀′. …  is
--   mathematically FALSE.  A value substitution may map a variable to a λ / ⊗ /
--   inj value and thereby CREATE a head redex absent from e₀ (e.g. e₀ = (` x)·v
--   with σ x = ƛ b, or `let⊗ (` x) `in e with σ x a pair — exactly the channel
--   triple shape U[_] uses!).  The source step only exists because ⊢P + ChanCx Γ
--   force every free variable of e₀ to be CHANNEL-typed, hence never in function
--   / pair-elim / case head position.  So a SOUND reflection must thread the
--   thread's typing (inv-⟪⟫ ⊢P).  The sound, typing-free fragments are proven
--   above as value-↛ / value-no-head / value-⋯⁻¹ (these ARE the pieces a typed
--   reflection reuses); the typed reflection itself is the remaining work.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Exp {e₁ = e₁} {e₂ = e₂} step)
  with e₀ , refl , refl ← inv-U-⟪⟫ P σ (sym eq)
  -- P = ⟪ e₀ ⟫, e₁ ≡ e₀ ⋯ σ, step : e₀ ⋯ σ ⋯→ e₂.  Reflect the substituted step
  -- back to a source step via the typed reflection (ReverseInv.⋯→-reflect): the
  -- source typing inv-⟪⟫ ⊢P + ChanCx Γ-S rule out a VSub manufacturing a head
  -- redex at a channel-typed variable.
  with e₀′ , s , refl ← ⋯→-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ step =
  TP.⟪ e₀′ ⟫ , TR.R-Exp s , ε

------------------------------------------------------------------------
-- RU-Par : R = A ∥ B and A steps.  eq + inv-U-∥ gives P = P₁ ∥ P₂ with
--   A ≡ U[ P₁ ] σ; recurse (sim←ᵍ) on the left at refl, reassemble with
--   TR.R-Par + UP.∥-cong.  STRUCTURAL — provable once inv-∥ (typing inversion)
--   feeds the left sub-derivation.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Par sub)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Par sub)
sim←ᵍ σ Vσ Γ-S {P = P₁ TP.∥ P₂}   ⊢P refl (UR.RU-Par sub)
  with _ , _ , _ , ⊢P₁ , _ ← inv-∥ ⊢P
  with P₁′ , step₁ , c₁ ← sim←ᵍ σ Vσ Γ-S ⊢P₁ refl sub =
  P₁′ TP.∥ P₂ , TR.R-Par step₁ , UP.∥-cong c₁ ε

------------------------------------------------------------------------
-- RU-Res : R = ν X and X steps (sub : X ─→ₚ X′).  inv-U-ν (now PROVEN with its
--   body) gives P = ν B₁ B₂ P₀ and ν X ≡ U[ ν B₁ B₂ P₀ ] σ, pinning X to the
--   φ-telescope  UB[B₁] (*,0,*) (UB[B₂] (…) (U[ P₀ ] bigσ))  of depth
--   syncs B₁ + syncs B₂.  RESIDUAL = φ-nest peeling: the inner step `sub` may
--   fire (a) inside U[ P₀ ] bigσ — reflect via the IH at bigσ and re-wrap to
--   TR.R-Bind — OR (b) on one of the administrative φ sync cells (RU-Sync /
--   RU-Drop / RU-Acquire / RU-Cleanup), which has NO typed counterpart at the
--   ν B₁ B₂ binder.  So a faithful reflection needs a decomposition lemma
--     (φ-nest) ─→ₚ X′  ⇒  (inner step on U[P₀]bigσ reflectable) ⊎ (admin φ move),
--   i.e. the same φ-nest engine the forward channel-op cases use, run in reverse.
--   When syncs B₁ = syncs B₂ = 0 (no φ binders) the nest IS U[ P₀ ] bigσ and the
--   IH applies directly; the general case is the open work.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Res {Q = X′} sub) =
  {! RU-Res: φ-nest peeling — IH at U[P₀]bigσ then TR.R-Bind, vs administrative φ moves with no typed image. Needs the reverse φ-nest decomposition (UB σ-algebra). !}

------------------------------------------------------------------------
-- RU-Sync : R = φ x P′.  But U[_] never heads with φ (clauses are ⟪⟫/∥/ν), so
--   eq : φ x P′ ≡ U[ P ] σ is absurd by case on P.  VACUOUS at top level
--   (only reachable under an inner RU-Res recursion, where the φ is real).
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}    ⊢P () (UR.RU-Sync sub)
sim←ᵍ σ Vσ Γ-S {P = P TP.∥ Q}    ⊢P () (UR.RU-Sync sub)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Sync sub)

------------------------------------------------------------------------
-- Channel-op / state-transition redex inversions.  Each constrains R (= U[ P ]
-- σ via eq) to a specific ν/φ + frame shape; inverting through U[_] to the
-- source redex is the hard work.  Left as noted holes.
------------------------------------------------------------------------
-- RU-Fork / RU-New : thread redexes.  inv-U-⟪⟫ gives P = ⟪ e₀ ⟫ with
--   e₀ ⋯ σ ≡ F [ K fork · e ]* (resp. F [ K (new s) · * ]*).  RESIDUAL = a
--   frame-plug reflection through σ: recover a source frame F₀ and source redex
--   with e₀ ≡ F₀ [ K fork · e′ ]*, F ≡ frame*-⋯ F₀ σ, e ≡ e′ ⋯ σ.  This is the
--   Frame* analogue of ReverseInv.⋯→-reflect (induct on e₀, peel each frame via
--   the head-shape inversions, refute a var head via var-app-absurd); fork/new
--   are structural constants so never appear in σ's channel image.  Then
--   TR.R-Fork / TR.R-New, with U-cong wrapping the result (New also needs the
--   reverse of the forward rnew-bridge ν(φacq(φacq …)) ≋ U[ν(0∷1)(0∷1)…]).
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Fork F V) =
  {! RU-Fork → TR.R-Fork: frame*-plug reflection through σ (Frame* analogue of ⋯→-reflect). !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-New F) =
  {! RU-New → TR.R-New: frame*-plug reflection through σ + reverse rnew-bridge. !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-LSplit F) =
  {! RU-LSplit → TR.R-LSplit: inv-U-ν + recognise the U[_]-image of the lsplit redex inside the φ-nest. Design point: B-shape / SplitRenamings.inj alignment (cf. forward LSplit.agda). !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-RSplit F) =
  {! RU-RSplit → TR.R-RSplit: inv-U-ν + φ-drop allocation match (RSplit allocates a fresh unset φ). Design point: 1∷suc b₁ binder insertion. !}
-- RU-Drop : R = φ drop (…).  φ-headed, so vacuous at top level (U[_] heads with
-- ⟪⟫/∥/ν only); only reachable under an inner RU-Sync/RU-Res recursion.
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Drop F)
sim←ᵍ σ Vσ Γ-S {P = P TP.∥ Q}     ⊢P () (UR.RU-Drop F)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Drop F)
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Acquire F) =
  {! RU-Acquire → TR.R-Acq: φ acq→done. inv-U-ν + zero∷suc b₁ binder shape + done-flag handling (RU-Cleanup pairs with it). !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Close F₁ F₂) =
  {! RU-Close → TR.R-Close: inv-U-ν + two-frame plug inversion + L.[1]L.[1] binder match. !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Com F₁ F₂ V) =
  {! RU-Com → TR.R-Com: send/recv rendezvous. inv-U-ν + BindCtx typing + frame-plug*; HARDEST — mirror forward Com.agda (962 ln) in reverse. !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Choice F₁ F₂ k) =
  {! RU-Choice → TR.R-Choice: select/branch. inv-U-ν + BindCtx typing + frame-plug*, like RU-Com. !}
-- RU-Cleanup : R = φ done P.  U[_] never heads with φ (clauses are ⟪⟫/∥/ν), so
-- eq : φ done P ≡ U[ Pₛ ] σ is absurd by case on Pₛ.  VACUOUS at top level
-- (only reachable under an inner RU-Res recursion, where the φ is real).
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () UR.RU-Cleanup
sim←ᵍ σ Vσ Γ-S {P = P TP.∥ Q}     ⊢P () UR.RU-Cleanup
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () UR.RU-Cleanup

------------------------------------------------------------------------
-- RU-Struct : R ≋ R′, inner : R′ ─→ₚ Q′, c₂ : Q′ ≋ Q  ⊢  R ─→ₚ Q.
--
--   VERDICT (investigated): NOT provable at the current sim← granularity, and
--   the obstruction is on the INPUT ≋ (c₁), not the output.  The output slack is
--   fine — given a source step P ─→ₚ P′ with Q′ ≋ U[ P′ ] σ, transitivity
--   Q ≋ Q′ ≋ U[ P′ ] σ (gmap/◅◅) absorbs c₂.  But to run the IH on `inner` we
--   need R′ to be the translation image U[ P₀ ] σ of SOME source P₀ with P
--   suitably related to P₀ — i.e. a REVERSE-U-≋ lemma
--       R ≋ S → Σ P₀. (S ≡ U[ P₀ ] σ) × (P ≋ P₀ source-side)
--   and this is FALSE in general: untyped ≋ contains φ-nest administrative moves
--   (ν-swap / ν-comm transposing φ-binders, φ-cong) that carry U[ P ] σ to
--   processes NOT literally in the U[_] image, so S need not factor as U[ P₀ ] σ.
--   The honest fixes (do NOT apply here — they change the sim← statement, which
--   is owned upstream): (a) strengthen the codomain to reduction-up-to-≋ on BOTH
--   sides (replace Q ≋ U[P′]σ by ∃ S. P ─→ₚ P′ × U[P′]σ ≋ S ≋ Q and let the
--   relation be ≋-closed on the left), or (b) prove a confluence/normalisation
--   lemma that every R ≋ U[P]σ reduces iff its U[_]-normal form does.  Either is
--   a design change beyond Reverse.agda; flagged for the statement owner.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Struct c₁ inner c₂) =
  {! RU-Struct: blocked on reverse-U-≋ (FALSE in general — φ-nest admin ≋ leaves the U[_] image). Needs a sim← codomain strengthening (reduction-up-to-≋ on both sides); see note above. !}
