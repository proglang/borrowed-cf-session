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
-- value reflection) live in BorrowedCF.Simulation2.ReverseInv; the typed
-- expression-reduction reflection they feed (⋯→-reflect) is blocked on
-- frame-plug non-invertibility, so RU-Exp below carries that single residual.
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
  with e₀ , refl , refl ← inv-U-⟪⟫ P σ (sym eq) =
  -- inversion done: P = ⟪ e₀ ⟫, e₁ ≡ e₀ ⋯ σ, ⊢e₀ = inv-⟪⟫ ⊢P, step : e₀ ⋯ σ ⋯→ e₂.
  -- RESIDUAL = the typed reflection  ⋯→-reflect e₀ (inv-⟪⟫ ⊢P) Γ-S σ Vσ step :
  --   Σ e₀′. (e₀ ⋯→ e₀′) × (e₂ ≡ e₀′ ⋯ σ), then  ⟪ e₀′ ⟫ , TR.R-Exp _ , ≡→≋ (cong ⟪_⟫ _).
  -- ReverseInv has every SOUND ingredient (value-step, value-⋯⁻¹, var-app-absurd,
  -- chanvar-not*) hole-free; only the frame-plug inversion (E-Ctx split is
  -- UnificationStuck — _[_] is not constructor-headed) blocks the final assembly.
  {! RU-Exp residual: ⋯→-reflect (frame-plug inversion via unique-frame) !}

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
-- RU-Res : R = ν X and X steps.  eq + inv-U-ν gives P = ν B₁ B₂ P₀.  The inner
--   step happens under the φ-telescope at the big UB-composite substitution;
--   the IH must be applied at THAT σ, and the result re-wrapped to TR.R-Bind.
--   PARTIAL: needs inv-U-ν exposing the body precisely + UB substitution algebra.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Res {Q = X′} sub) =
  {! RU-Res: inv-U-ν P σ eq → P=ν B₁ B₂ P₀; recurse under the φ-telescope at the UB-composite σ; rewrap TR.R-Bind. Needs inv-U-ν body + UB σ-algebra. !}

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
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Fork F V) =
  {! RU-Fork → TR.R-Fork: inv-U-⟪⟫ + frame*-plug inversion (recognise U[⟪F[fork·e]⟫]); same frame-plug bridge as forward R-Fork. !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-New F) =
  {! RU-New → TR.R-New: inv-U-⟪⟫ + frame*-plug inversion + reverse of forward rnew-bridge (ν(φacq(φacq …)) ≋ U[ν(0∷1∷[])(0∷1∷[])…]). !}
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
-- RU-Struct : R ≋ R′ ─→ₚ Q′ ≋ Q.  To reflect this we need the REVERSE of U-≋
--   (a source ≋ whose image is the given untyped ≋), then ⊢-≋ to retype and
--   recurse.  U-≋ lives in Simulation2.Congruence which we MAY NOT import here.
--   HOLE: needs reverse-U-≋ : R ≋ U[ P ] σ → Σ P₀. R ≡ U[ P₀ ] σ × P ≋ P₀ (or a
--   ≋-variant), then ⊢-≋ + recurse + stitch c₂.
------------------------------------------------------------------------
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Struct c₁ inner c₂) =
  {! RU-Struct: needs reverse of U-≋ (Simulation2.Congruence, currently unimportable) + ⊢-≋ retype + recurse + stitch c₂. !}
