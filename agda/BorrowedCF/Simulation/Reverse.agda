module BorrowedCF.Simulation.Reverse where

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
--   We do NOT import BorrowedCF.Simulation.Congruence (mid-edit elsewhere);
--   anything that needs the reverse of U-≋ is left a noted hole.

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Simulation.TranslationProperties
  using (≡→≋; U-cong; Value-subst)
open import BorrowedCF.Simulation.RevPeelH
  using ( subst-redU; sc-subst-redU; ∣-subst-redU; ≈-substU; subst-≋U
        ; Pfx-red; Pfx-≈; Pfx-≋; snoc-eq; Pfx-snoc; substφ-¬∥
        ; U-substσP; VSub-leafσP; reasm; reasm-eq )
open import BorrowedCF.Simulation.Theorems.DropQH
  using (Bφ; Pfx; leafσ; Uν-flat; subst-φ; subst-Bφ; ss-U; uipℕ)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
-- Reusable reverse-direction inversion helpers (channel-var contradictions,
-- value reflection, and the typed expression-reduction reflection ⋯→-reflect
-- that powers RU-Exp) live in BorrowedCF.Simulation.ReverseInv.
open import BorrowedCF.Simulation.ReverseInv
  using (⋯→-reflect; frameApp-reflect; headK; plugApp-not-value;
         rnew-bridge; new-arg-notVar;
         inv-U-ν-∥-shape; U-ν-singleton; νσ; ν-inj;
         νσ-VSub; inv-ν-chanCx; close-bridge;
         νσ-φfree; νσ-φfree-VSub; U-ν-φfree-eq;
         head⊗′; close-arg-var; pair-not-chan; ⟨⟩≄⊗)
open import BorrowedCF.Simulation.InvFrame using (strengthen-frame; inv-app; inv-pair; arg-type)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.RevLSplit
  using (lsplit-go; lsplit-arg-chan; fin-split)
open import BorrowedCF.Simulation.RevRSplit
  using (rsplit-go; rsplit-arg-chan)
open import BorrowedCF.Simulation.RevCom using (com-go)
open import BorrowedCF.Simulation.RevChoice using (choice-go)
open import BorrowedCF.Simulation.RevClose using (close-go)
open import BorrowedCF.Simulation.RevAcq using (acq-go)
open import BorrowedCF.Simulation.RevComConfine
  using (frames-𝕀; leftPat-¬before; leftPat-pullOut-∥-≼; before-com-binderᴸ; com-xS-min)
open import BorrowedCF.Simulation.ReverseConfine using (count-handle-comᴸ)
open import BorrowedCF.Simulation.BeforeOrder using (before)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation.RevComImage using (com-image-block1; pos⇒suc)
open import BorrowedCF.Simulation.RevGrindA using (chanCx-¬Unr; com-¬before)
open import BorrowedCF.Context.Pattern using (LeftPat; CxPat; _[_]𝓅)
open import BorrowedCF.Simulation.Confine using (count; ≼⇒count≤; count-self; count-join-Dir; count-join-PS)
open import BorrowedCF.Simulation.Theorems.Com
  using (fn-send-dom; pair₂-handle; send-handle-≃msg-app; ⊗≃₂)
import Data.Sum as Sum
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin
  using (_─→ᵃ_; _≈_; ≋⇒≈; ─→ᵃ⇒≈; ≈-refl; ≈-trans; ≈-sym;
         ≈-ν-cong; ≈-φ-cong; ≈-∥-congˡ; a-discard; a-sync; a-res; a-par; admin⇒red)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import BorrowedCF.Simulation.RevCongStrong using (sc; ∣_∣)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Context using (Ctx; Struct; biasedDir; _∶_≼_; join)
open TP using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; ⊢-≋; bindCtx⇒chanCtx; structBinder)

------------------------------------------------------------------------
-- Typed-side reflexive-transitive closure of process reduction.
--
--   The reverse-simulation codomain is the MIRROR of the forward sim→ ⊎
--   codomain (Theorems.agda): there U[P]σ ─→ₚ* U[P′]σ on the UNTYPED side; here
--   we need P ─→ₚ* P′ on the TYPED side, so a skip-padded redex can R-Discard*
--   its padding and THEN fire the real step (the RU-Close inj₁ / skip-padding
--   blocker is exactly this).  Single steps inject as  s ◅ ε.
------------------------------------------------------------------------

infix 4 _TR─→ₚ*_
_TR─→ₚ*_ : {n : ℕ} → TP.Proc n → TP.Proc n → Set
_TR─→ₚ*_ = Star TR._─→ₚ_

------------------------------------------------------------------------
-- D2 : "one untyped step + an OPTIONAL cleanup".
--
--   A single typed step may be TWO untyped steps through an administrative
--   intermediate flag-state (R-Acq = RU-Acquire ; RU-Cleanup, via the `done`
--   cell; Theorems.agda:418).  Observing ONE untyped step in reverse can leave
--   us at that intermediate, which is OUTSIDE every U[_]-image (images carry
--   only drop/acq flags, never done).  So the reverse codomain lets the OUTPUT
--   Q take at most ONE further untyped step before matching the image.  The
--   relation is the GENERAL ≤1-step  (Q ≡ Q′) ⊎ (Q ─→ₚ Q′)  rather than a
--   RU-Cleanup-restricted one so it composes through RU-Struct (a ≋-wrapped
--   cleanup is a RU-Struct step, not a literal RU-Cleanup constructor).
------------------------------------------------------------------------

infix 4 _─→ᶜ?_
_─→ᶜ?_ : {n : ℕ} → UP.Proc n → UP.Proc n → Set
Q ─→ᶜ? Q′ = (Q ≡ Q′) Sum.⊎ (Q UR.─→ₚ Q′)

private
  φ-injU : ∀ {k} {f g : UP.Flag} {X Y : UP.Proc (suc k)} →
           UP.φ f X ≡ UP.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-injU refl = refl , refl

  wrapPfx : ∀ {n k : ℕ} (D : TP.BindGroup) (r : ℕ) (kEq : k ≡ L.length D + (2 + n))
            (f : UP.Flag) (W : UP.Proc (suc k)) → f ≡ ϕ[ r ] →
            Pfx (D ++ r ∷ []) (subst UP.Proc (cong suc kEq ■ sym (snoc-eq D r (2 + n))) W)
            ≡ Pfx D (subst UP.Proc kEq (UP.φ f W))
  wrapPfx {n} {k} D r kEq f W fq =
      Pfx-snoc D r (subst UP.Proc (cong suc kEq ■ sym (snoc-eq D r (2 + n))) W)
    ■ cong (Pfx D)
        ( cong (UP.φ ϕ[ r ])
            ( ss-U (cong suc kEq ■ sym (snoc-eq D r (2 + n))) (snoc-eq D r (2 + n)) {t = W}
            ■ cong (λ e → subst UP.Proc e W) (uipℕ _ (cong suc kEq)) )
        ■ cong (λ ff → UP.φ ff (subst UP.Proc (cong suc kEq) W)) (sym fq)
        ■ sym (subst-φ kEq W) )

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
value-↛ V (E-Ctx (app₁ _ _ _)  red)    with V
... | ()
value-↛ V (E-Ctx (app₂ _ _ _)  red)    with V
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
value-⋯⁻¹ σ Vσ (ƛ d e)             V = V-λ
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

-- WEAK reverse simulation, UP TO ≋ on the input, MULTI-STEP on the typed side
-- (the exact mirror of the forward sim→ ⊎ codomain in Theorems.agda).  The
-- input is taken up to untyped ≋ — `R ≋ U[ P ] σ` instead of a bare image —
-- so RU-Struct's structural-congruence premise `c₁ : R ≋ R′` is absorbable
-- (recurse at R′ ≋ U[ P ] σ); the codomain is `P ─→ₚ* P′` so a skip-padded
-- redex may R-Discard* its padding before firing the real step.
sim←ᴬ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
     → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
     → {R Q : UP.Proc n} → R ≈ U[ P ] σ → (red : R UR.─→ₚ Q)
     → Acc Nat._<_ (sc red) → Acc Nat._<_ ∣ red ∣
     → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
         (P TR─→ₚ* P′ × Q ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)

-- The untyped step has LHS index U[ P ] σ, a stuck application, so a direct
-- `with` case-split on it gets a SplitError (UnificationStuck).  We generalise:
-- abstract the LHS to a fresh variable R with a proof R ≡ U[ P ] σ, split on
-- the reduction (now R is a variable so every RU-* constructor unifies), and
-- read P back off the equality with the inv-U-* lemmas.  This is the inversion
-- ENGINE: it keeps the strict `≡` image on the input (the inv-U-* lemmas need
-- propositional equality), and the codomain is the MULTI-STEP P ─→ₚ* P′.
sim←ᵍᴬ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
      → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
      → {R Q : UP.Proc n} → R ≡ U[ P ] σ → (red : R UR.─→ₚ Q)
      → Acc Nat._<_ (sc red) → Acc Nat._<_ ∣ red ∣
      → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
          (P TR─→ₚ* P′ × Q ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)

-- syncs-of : the (<=singleton) phi-free shape of a bind group, or a >=2 witness.
syncs-of : (B : TP.BindGroup)
         → (syncs B ≡ 0) Sum.⊎ (Σ[ b ∈ ℕ ] Σ[ c ∈ ℕ ] Σ[ Bp ∈ TP.BindGroup ] (B ≡ b ∷ c ∷ Bp))
syncs-of []           = Sum.inj₁ refl
syncs-of (b ∷ [])     = Sum.inj₁ refl
syncs-of (b ∷ c ∷ Bp) = Sum.inj₂ (b , c , Bp , refl)

-- simRes : RU-Res reflection, factored out so it does NOT re-generalise the
-- scope index (a where-local helper would break the sigma : m -> n alignment).
simResᴬ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
       → {g : Struct m}
       → (B₁ B₂ : TP.BindGroup) (P₀ : TP.Proc (sum B₁ + sum B₂ + m))
       → Γ ; g ⊢ₚ TP.ν B₁ B₂ P₀
       → (X X′ : UP.Proc (2 + n)) → (sub : X UR.─→ₚ X′)
       → UP.ν X ≡ U[ TP.ν B₁ B₂ P₀ ] σ
       → (syncs B₁ ≡ 0) Sum.⊎ _ → (syncs B₂ ≡ 0) Sum.⊎ _
       → Acc Nat._<_ (sc sub) → Acc Nat._<_ ∣ sub ∣
       → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
           (TP.ν B₁ B₂ P₀ TR─→ₚ* P′ × UP.ν X′ ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)

-- peel₁ᴬ : walk the group-1 cells of the flattened telescope.  D₁ = peeled
-- prefix (its cells wrap the layer via Pfx), r₀ ∷ rest₁ = remaining blocks.
-- The layer scope k is kept free so the descent passes sub-derivations
-- unchanged (structural); all transports live in kEq/E/Zeq/topEq.
peel₁ᴬ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m}
  → (B₁ B₂ : TP.BindGroup) (P₀ : TP.Proc (sum B₁ + sum B₂ + m))
  → Γ ; g ⊢ₚ TP.ν B₁ B₂ P₀
  → (D₁ : TP.BindGroup) (r₀ : ℕ) (rest₁ : TP.BindGroup)
  → B₁ ≡ D₁ ++ r₀ ∷ rest₁
  → {k : ℕ} (kEq : k ≡ L.length D₁ + (2 + n))
  → (E : syncs B₁ + (2 + n) ≡ syncs (r₀ ∷ rest₁) + k)
  → (Zk Zk′ : UP.Proc k)
  → Zk ≡ Bφ (r₀ ∷ rest₁) (subst UP.Proc E (Bφ B₂ (U[ P₀ ] (leafσ σ B₁ B₂))))
  → (subk : Zk UR.─→ₚ Zk′)
  → UP.ν (Pfx D₁ (subst UP.Proc kEq Zk)) ≡ U[ TP.ν B₁ B₂ P₀ ] σ
  → Acc Nat._<_ (sc subk) → Acc Nat._<_ ∣ subk ∣
  → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
      (TP.ν B₁ B₂ P₀ TR─→ₚ* P′ × UP.ν (Pfx D₁ (subst UP.Proc kEq Zk′)) ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)

-- peel₂ᴬ : group-1 exhausted (B₁ ≡ D₁X ++ [ l₁ ]); walk group-2's cells.
-- WW = D₁X ++ D₂ is the total peeled prefix.
peel₂ᴬ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m}
  → (B₁ B₂ : TP.BindGroup) (P₀ : TP.Proc (sum B₁ + sum B₂ + m))
  → Γ ; g ⊢ₚ TP.ν B₁ B₂ P₀
  → (D₁X : TP.BindGroup) (l₁ : ℕ) → B₁ ≡ D₁X ++ l₁ ∷ []
  → (D₂ : TP.BindGroup) (r₂ : ℕ) (rest₂ : TP.BindGroup) → B₂ ≡ D₂ ++ r₂ ∷ rest₂
  → (WW : TP.BindGroup) → WW ≡ D₁X ++ D₂
  → {k : ℕ} (kEq : k ≡ L.length WW + (2 + n))
  → (E : syncs B₂ + (syncs B₁ + (2 + n)) ≡ syncs (r₂ ∷ rest₂) + k)
  → (Zk Zk′ : UP.Proc k)
  → Zk ≡ Bφ (r₂ ∷ rest₂) (subst UP.Proc E (U[ P₀ ] (leafσ σ B₁ B₂)))
  → (subk : Zk UR.─→ₚ Zk′)
  → UP.ν (Pfx WW (subst UP.Proc kEq Zk)) ≡ U[ TP.ν B₁ B₂ P₀ ] σ
  → Acc Nat._<_ (sc subk) → Acc Nat._<_ ∣ subk ∣
  → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
      (TP.ν B₁ B₂ P₀ TR─→ₚ* P′ × UP.ν (Pfx WW (subst UP.Proc kEq Zk′)) ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)

-- Public entry, ≋-closed on the input.  When R IS literally the image
-- (the ε / reflexive prefix) it is the engine at refl; a genuine ≋ prefix
-- needs the reverse-U-≋ factorisation (the same blocker carried by the
-- RU-Struct case) and is left a noted hole.
sim←ᴬ σ Vσ Γ-S ⊢P ε red ac sz = sim←ᵍᴬ σ Vσ Γ-S ⊢P refl red ac sz
sim←ᴬ σ Vσ Γ-S ⊢P (c ◅ cs) red ac sz =
  {! sim← non-ε (2026-07 STATE, post Com/Choice/Close/Acq/Discard closes).
     Input links are now ≋-chains OR a-discard admin steps (RevAdmin gained
     a-discard; ─→ᵃ is no longer uninhabited).  MACHINE-CONFIRMED (RevPhiNest
     header): the reduction-transport route (≋*-sim + recurse) is
     non-terminating (∥-comm wraps grow the reduction; ∥-red-inv).  A
     terminating closure = the φ-decomposition ENGINE: process the chain from
     the image end; ∥-comm/assoc/unit invert STRICTLY onto a rearranged source
     (inv-U-∥ + U[_]-homomorphism, chain shortens); ν-swap/ν-comm/ν-ext invert
     strictly only on φ-FREE telescopes — with φs present the image escapes up
     to φ-permutation (U-≋'s NuSwap-scale machinery gives the forward bridges),
     and νφ-comm′ escapes outright (RevUCong.U-≋-escapes); the escape class is
     closed under φ-comm/φ-ext/∥-embedding, so the engine needs a φ-scattered
     image characterization (≋-normalization) with a φ-head-count measure, plus
     red-⋯ₚ (RedRename, PROVEN) to replay under assocSwapᵣ, plus a-discard link
     transport (discard-step confluence).  Research-scale; all leaf ingredients
     exist, the normalization development does not. !}

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
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Exp {e₁ = e₁} {e₂ = e₂} step) ac sz
  with e₀ , refl , refl ← inv-U-⟪⟫ P σ (sym eq)
  -- P = ⟪ e₀ ⟫, e₁ ≡ e₀ ⋯ σ, step : e₀ ⋯ σ ⋯→ e₂.  Reflect the substituted step
  -- back to a source step via the typed reflection (ReverseInv.⋯→-reflect): the
  -- source typing inv-⟪⟫ ⊢P + ChanCx Γ-S rule out a VSub manufacturing a head
  -- redex at a channel-typed variable.
  with e₀′ , s , refl ← ⋯→-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ step =
  TP.⟪ e₀′ ⟫ , _ , TR.R-Exp s ◅ ε , Sum.inj₁ refl , ε

------------------------------------------------------------------------
-- RU-Par : R = A ∥ B and A steps.  eq + inv-U-∥ gives P = P₁ ∥ P₂ with
--   A ≡ U[ P₁ ] σ; recurse (sim←ᵍ) on the left at refl, reassemble with
--   TR.R-Par + UP.∥-cong.  STRUCTURAL — provable once inv-∥ (typing inversion)
--   feeds the left sub-derivation.
------------------------------------------------------------------------
sim←ᵍᴬ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Par sub) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Par sub) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = P₁ TP.∥ P₂}   ⊢P refl (UR.RU-Par sub) ac (acc rsz)
  with _ , _ , _ , ⊢P₁ , _ ← inv-∥ ⊢P
  with P₁′ , Q₁′ , step₁ , cl₁ , c₁ ← sim←ᵍᴬ σ Vσ Γ-S ⊢P₁ refl sub ac (rsz Nat.≤-refl) =
  P₁′ TP.∥ P₂ , Q₁′ UP.∥ U[ P₂ ] σ , ⋆-gmap (TP._∥ P₂) TR.R-Par step₁ ,
  Sum.map (cong (λ z → z UP.∥ U[ P₂ ] σ)) UR.RU-Par cl₁ , ≈-∥-congˡ c₁

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
--   IH applies directly (split B₁,B₂ into []/singleton, ν-inj the body eq, recurse
--   sim←ᵍ at bigσ via inv-ν's P₀ typing + bindCtx⇒chanCtx + a bigσ VSub built from
--   ++ₛ-VSub/weaken-VSub, re-wrap TR.R-Bind + ν-cong); this φ-free sub-case is the
--   clean part.  The φ-bearing case (syncs ≥ 1) is blocked: branch (b)'s admin φ
--   move (RU-Drop/RU-Acquire/RU-Cleanup flipping a sync cell) carries U[P]σ to a
--   process OUTSIDE the U[_] image, so it has no typed counterpart at the binder
--   and needs the SAME codomain-≋ strengthening as RU-Struct (reduction-up-to-≋
--   on both sides) — a sim← statement change owned upstream.
------------------------------------------------------------------------
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Res {P = X} {Q = X′} sub) ac (acc rsz)
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  -- φ-free sub-case is dispatched (on the (<=singleton) shape of B₁,B₂) in
  -- simRes.  The φ-bearing case (some Bᵢ >= 2 ==> syncs >= 1) is the documented
  -- codomain-≋ blocker (admin φ moves leave the U[_] image), a noted hole in simRes.
  = simResᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢P X X′ sub bodyeq (syncs-of B₁) (syncs-of B₂) ac (rsz Nat.≤-refl)

------------------------------------------------------------------------
-- RU-Sync : R = φ x P′.  But U[_] never heads with φ (clauses are ⟪⟫/∥/ν), so
--   eq : φ x P′ ≡ U[ P ] σ is absurd by case on P.  VACUOUS at top level
--   (only reachable under an inner RU-Res recursion, where the φ is real).
------------------------------------------------------------------------
sim←ᵍᴬ σ Vσ Γ-S {P = TP.⟪ e ⟫}    ⊢P () (UR.RU-Sync sub) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = P TP.∥ Q}    ⊢P () (UR.RU-Sync sub) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Sync sub) ac sz

------------------------------------------------------------------------
-- Channel-op / state-transition redex inversions.  Each constrains R (= U[ P ]
-- σ via eq) to a specific ν/φ + frame shape; inverting through U[_] to the
-- source redex is the hard work.  Left as noted holes.
------------------------------------------------------------------------
-- RU-Fork / RU-New : thread redexes.  inv-U-⟪⟫ gives P = ⟪ e₀ ⟫ with
--   e₀ ⋯ σ ≡ F [ K fork · e ]* (resp. F [ K (new s) · * ]*).  The frame-plug
--   reflection through σ is now DONE: ReverseInv.frameApp-reflect (the Frame*
--   analogue of ⋯→-reflect — inducts on e₀, peels each frame via the head-shape
--   reflectors headApp/head⊗′/headSeq/headInj′/headLet/headLetpair/headCase,
--   refutes a var head via plugApp-not-value since F [ a · b ]* is never a value
--   and a VSub maps a var to a value) recovers F₀, arg₀ with e₀ ≡ F₀ [ K c · arg₀
--   ]*, F ≡ frame*-⋯ F₀ σ Vσ, arg ≡ arg₀ ⋯ σ.  RU-Fork is CLOSED below.  RU-New
--   uses the same frameApp-reflect (c = `new s) but is BLOCKED on the ⊗-swap (see
--   its note).  frameApp-reflect ALSO supplies the redex-inversion half of every
--   ν-headed channel-op redex (LSplit/RSplit/Close/Com/Choice).
sim←ᵍᴬ σ Vσ Γ-S ⊢P eq (UR.RU-Fork F V) ac sz
  with e₀ , refl , feq ← inv-U-⟪⟫ _ σ (sym eq)
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ `fork F (sym feq) =
  TP.⟪ F₀ [ K `unit ]* ⟫ TP.∥ TP.⟪ arg₀ ·¹ K `unit ⟫ , _ ,
  TR.R-Fork F₀ (value-⋯⁻¹ σ Vσ arg₀ (subst Value argeq V)) ◅ ε , Sum.inj₁ refl ,
  ≋⇒≈ (≡→≋ (cong₂ UP._∥_
        (cong UP.⟪_⟫ (cong (_[ K `unit ]*) Feq ■ sym (frame-plug* F₀ σ Vσ)))
        (cong (λ z → UP.⟪ z ·¹ K `unit ⟫) argeq)))
-- RU-New : the LHS redex K (`new s) · * is an applied constant, so the source
--   frame F₀ + source redex are recovered by frameApp-reflect (c = `new s, arg₀
--   forced to K `unit since a unit-typed source var is ruled out by ChanCx, like
--   fork).  The TYPED step is TR.R-New F₀.  BLOCKED on the SAME design mismatch
--   as the forward R-New (Theorems.agda R-New note): the RU-New output pairs the
--   two channel triples as  C[`0F×3F×*] ⊗ C[`1F×2F×*]  whereas U[ R-New's typed
--   rhs ] σ pairs them SWAPPED (`1F⊗`0F leaf order); the differing a⊗b vs b⊗a is
--   an expression-internal ⊗ inside << >> that NO untyped ≋ rule (all renaming-
--   based ∥/ν/φ moves) can reorder.  Reverse inherits this verbatim (≋ is
--   symmetric).  Fix is the same swap in Reduction/Processes/Untyped.agda RU-New
--   OR the typed R-New body OR Bisim.agda U[_] — all outside this module's scope.
-- RU-New : redex K (`new s) · *.  frameApp-reflect recovers F₀ and arg₀;
--   strengthen-frame + new-arg-notVar rules out a variable argument (new's
--   domain is `⊤, never a channel), forcing arg₀ ≡ K `unit, i.e. an R-New
--   redex.  The codomain ≋ is the (now reusable) rnew-bridge — the SAME bridge
--   the forward R-New uses; the ⊗-swap is reconciled there (the U[ν…] leaf order
--   `1F⊗`0F substitutes the two channel triples into the unswapped pair tL).
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-New {s = s} F) ac sz
  with e₀ , refl , feq ← inv-U-⟪⟫ P σ (sym eq)
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ-S e₀ (inv-⟪⟫ ⊢P) σ Vσ (`new s) F (sym feq)
  with headK σ arg₀ (sym argeq)
... | Sum.inj₁ (x , refl)
      with _ , (_ , _ , ⊢redex) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢P)
      = ⊥-elim (new-arg-notVar Γ-S ⊢redex)
... | Sum.inj₂ refl =
  TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
    TP.⟪ (F₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 1F) ⊗ (` 0F) ]* ⟫ , _ ,
  TR.R-New F₀ ◅ ε , Sum.inj₁ refl ,
  ≋⇒≈ (subst (λ z → UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
                  (z ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ _ ]* ⟫))
                UP.≋ _)
        (sym Feq) (rnew-bridge F₀ σ Vσ))
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-LSplit {s = s} {e₁ = e₁} {e₂ = e₂} {P = P₁} F) ac sz
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PL , P₁t , refl , Leq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢P₁t ← inv-∥ ⊢body
  with F₀ , argᴸ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`lsplit s)
           F (sym Leq′)
  with _ , (_ , _ , ⊢plug) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢PL)
  with _ , _ , _ , _ , ⊢argᴸ , ch ← lsplit-arg-chan ⊢plug
  with x , argᴸ≡ ← close-arg-var argᴸ ⊢argᴸ ch (νσ b₁ b₂ σ) (sym argeq)
  with z , _ , xeq ← com-image-block1 b₁ b₂ σ Vσ x (argeq ■ cong (_⋯ νσ b₁ b₂ σ) argᴸ≡)
  with b₁' , b₁≡ ← fin-split b₁ z =
  lsplit-go σ Vσ (Fin.toℕ z) b₁' b₂ Γ-S b₁ b₁≡ z refl
    (argᴸ≡ ■ cong `_ xeq) ⊢P Feq argeq Resteq
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-RSplit {s = s} {e₁ = e₁} {e₂ = e₂} {P = P₁} F) ac sz
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PL , P₁t , refl , Leq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢P₁t ← inv-∥ ⊢body
  with F₀ , argᴸ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`rsplit s)
           F (sym Leq′)
  with _ , (_ , _ , ⊢plug) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢PL)
  with _ , _ , _ , _ , ⊢argᴸ , ch ← rsplit-arg-chan ⊢plug
  with x , argᴸ≡ ← close-arg-var argᴸ ⊢argᴸ ch (νσ b₁ b₂ σ) (sym argeq)
  with z , _ , xeq ← com-image-block1 b₁ b₂ σ Vσ x (argeq ■ cong (_⋯ νσ b₁ b₂ σ) argᴸ≡)
  with b₁' , b₁≡ ← fin-split b₁ z =
  rsplit-go σ Vσ (Fin.toℕ z) b₁' b₂ Γ-S b₁ b₁≡ z refl
    (argᴸ≡ ■ cong `_ xeq) ⊢P Feq argeq Resteq
-- RU-Drop : R = φ drop (…).  φ-headed, so vacuous at top level (U[_] heads with
-- ⟪⟫/∥/ν only); only reachable under an inner RU-Sync/RU-Res recursion.
sim←ᵍᴬ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Drop F) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = P TP.∥ Q}     ⊢P () (UR.RU-Drop F) ac sz
sim←ᵍᴬ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Drop F) ac sz
sim←ᵍᴬ σ Vσ Γ-S ⊢P eq (UR.RU-Acquire F) ac sz = acq-go σ Vσ Γ-S F ⊢P eq
-- RU-Close.  PARTIAL — the structural inversion is PROVEN (ReverseInv:
--   inv-U-ν reads P = ν B₁ B₂ P₀ off the ν head; the RU-Close LHS body is
--   ∥-headed, so inv-U-ν-∥-shape forces syncs B₁ = syncs B₂ = 0, i.e. B₁ = b₁ ∷
--   [], B₂ = b₂ ∷ [] singletons — each endpoint carries one handle, as a
--   well-typed close demands; U-ν-singleton then collapses the empty φ-telescope
--   so the ν body is literally U[ P₀ ] (νσ b₁ b₂ σ) — see the `with`-stack here,
--   which type-checks).  RESIDUAL (the remaining hole): from the collapsed body
--   recover P₀ = ⟪eL⟫ ∥ ⟪eR⟫ (U[_]-of-∥ is ∥, of-thread is thread), then
--   frameApp-reflect (c = `end ‼ / `end ⁇) each substituted close redex back to a
--   source frame + its channel-var argument (`0F)/(`1F), fire TR.R-Close, and
--   reconcile the codomain with the forward `thr`/frame-plug* bridge (R-Close in
--   Theorems.agda).  That per-thread typed reflection needs inv-ν → inv-∥ →
--   inv-⟪⟫ to type eL/eR in the binder-extended ChanCx (bindCtx⇒chanCtx) plus the
--   forward-mirror ≋ — the large remaining piece; B-shape + φ-collapse are DONE.
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Close F₁ F₂) ac sz
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  -- bodyeq′ : (F₁⋯ᶠ*wk2)[end‼·𝓒[e₁×0F×e₁′]]* ∥ (F₂⋯ᶠ*wk2)[end⁇·𝓒[e₂×1F×e₂′]]*
  --           ≡ U[ P₀ ] (νσ b₁ b₂ σ)
  with PL , PR , refl , Leq , Req ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with _ , _ , _ , ⊢PL , ⊢PR ← inv-∥ ⊢body
  with F₀ᴸ , argᴸ , refl , FeqL , argeqL
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`end ‼)
           (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (sym Leq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`end ⁇)
           (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (sym Req′)
  = close-go σ Vσ Γ-S b₁ b₂ ⊢P FeqL argeqL FeqR argeqR
-- RU-Com.  Body ν(⟪..⟫ ∥ (⟪..⟫ ∥ P)) is ∥-headed, so the SAME structural
--   inversion as RU-Close applies: inv-U-ν + inv-U-ν-∥-shape force B₁,B₂ to
--   singletons (syncs 0), U-ν-singleton collapses the φ-telescope, giving body ≡
--   U[ P₀ ] (νσ b₁ b₂ σ) with P₀ = ⟪eS⟫ ∥ (⟪eR⟫ ∥ P).  RESIDUAL: frameApp-reflect
--   the send redex K `send · (e ⊗ 𝓒[…]) (head⊗ on the argument, not a bare chan
--   var) and the recv redex K `recv · 𝓒[…]; the recv channel INDEX (wkʳ/wkˡ
--   geometry) is fixed only by the BindCtx chain — the same typing-driven index
--   pin the forward U-com (Theorems/Com.agda, 962 ln) needs, mirrored.  Large but
--   UNgated; structural shape/collapse PROVEN above (reuse for Close/Com/Choice).
sim←ᵍᴬ {m = m} σ Vσ Γ-S {g = g} {P = P} ⊢P eq (UR.RU-Com F₁ F₂ V) ac sz
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , _ , _ , _ , _ , _ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  -- bodyeq′ : ⟪F₁[send·(e⊗𝓒[e₁×0F×e₁′])]⟫ ∥ (⟪F₂[recv·𝓒[e₂×1F×e₂′]]⟫ ∥ P₁)
  --           ≡ U[ P₀ ] (νσ b₁ b₂ σ)
  with PS , Prest , refl , Seq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with PR , Pr , refl , Req , Preq ← inv-U-∥ Prest (νσ b₁ b₂ σ) (sym Resteq)
  with eS , refl , Seq′ ← inv-U-⟪⟫ PS (νσ b₁ b₂ σ) (sym Seq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with αcom , βcom , αβ≼ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with _ , _ , _ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with F₀ˢ , argˢ , refl , FeqS , argeqS
       ← frameApp-reflect Γ′-S eS (inv-⟪⟫ ⊢PS) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `send
           F₁ (sym Seq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `recv
           F₂ (sym Req′)
  = com-go σ Vσ Γ-S b₁ b₂ V ⊢P FeqS argeqS FeqR argeqR Preq

-- RU-Choice.  Identical shape to RU-Com (ν, ∥-headed body): same inv-U-ν-∥-shape
--   + U-ν-singleton collapse; RESIDUAL = frameApp-reflect the select/branch
--   redexes + `inj wrapping on the codomain, mirroring forward U-choice.
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Choice F₁ F₂ k) ac sz
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PS , Prest , refl , Seq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with PR , Pr , refl , Req , Preq ← inv-U-∥ Prest (νσ b₁ b₂ σ) (sym Resteq)
  with eS , refl , Seq′ ← inv-U-⟪⟫ PS (νσ b₁ b₂ σ) (sym Seq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with _ , _ , _ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with _ , _ , _ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with F₀ˢ , argˢ , refl , FeqS , argeqS
       ← frameApp-reflect Γ′-S eS (inv-⟪⟫ ⊢PS) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`select k)
           F₁ (sym Seq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `branch
           F₂ (sym Req′)
  = choice-go σ Vσ Γ-S b₁ b₂ k ⊢P FeqS argeqS FeqR argeqR Preq
-- RU-Discard : R = ⟪ F [ discard · e ]* ⟫ steps to ⟪ F [ * ]* ⟫ (silent term
-- consuming a leading skip/discard).  ⟪⟫-headed, so mirrors RU-Fork/RU-Exp; the
-- typed counterpart is TR.R-Discard.  Left a noted hole for the reverse.
sim←ᵍᴬ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Discard F V) ac sz =
  P , _ , ε , Sum.inj₁ refl ,
  subst (UP.⟪ F [ * ]* ⟫ ≈_) eq (≈-sym (─→ᵃ⇒≈ (a-discard F V)))

------------------------------------------------------------------------
-- RU-Struct : R ≋ R′, inner : R′ ─→ₚ Q′, c₂ : Q′ ≋ Q  ⊢  R ─→ₚ Q.
--
--   With the statement now ≋-CLOSED on the input (sim← takes R ≋ U[ P ] σ) and
--   the codomain reduction-up-to-≋ / multi-step, this case is NO LONGER blocked
--   at the granularity: the structural-congruence premise c₁ is ABSORBABLE.
--   From eq : R ≡ U[ P ] σ and c₁ : R ≋ R′ we get  R′ ≋ U[ P ] σ
--   (= ≋-trans (≋-sym c₁) (≡→≋ eq)), so we recurse on `inner` through the public
--   ≋-input simulator sim←, obtaining P′, P ─→ₚ* P′, Q′ ≋ U[ P′ ] σ.  The output
--   ≋ then absorbs c₂ by transitivity: Q ≋ Q′ ≋ U[ P′ ] σ.  The residual reverse-
--   U-≋ work (factoring a genuine ≋ prefix through the U[_] image) is now ISOLATED
--   in sim←'s non-ε branch (the c ◅ cs hole) — the single place where the φ-nest
--   administrative moves that leave the U[_] image must be handled.
------------------------------------------------------------------------
sim←ᵍᴬ σ Vσ Γ-S ⊢P eq (UR.RU-Struct c₁ inner c₂) (acc rs) sz
  with sim←ᴬ σ Vσ Γ-S ⊢P (≋⇒≈ (Eq*.symmetric _ c₁ ◅◅ ≡→≋ eq)) inner (rs Nat.≤-refl) (<-wellFounded ∣ inner ∣)
... | P′ , Q″ , steps , Sum.inj₁ refl , Q″≋ =
  P′ , _ , steps , Sum.inj₁ refl , ≋⇒≈ (Eq*.symmetric _ c₂) ◅◅ Q″≋
... | P′ , Q″ , steps , Sum.inj₂ st , Q″≋ =
  P′ , Q″ , steps , Sum.inj₂ (UR.RU-Struct (Eq*.symmetric _ c₂) st ε) , Q″≋


------------------------------------------------------------------------
-- simRes clauses.  phi-free (both syncs 0): recurse the IH at the phi-free
-- leaf U[ P₀ ] σ′, re-wrap R-Bind, reconcile codomain via U-ν-phifree.
-- phi-bearing (some syncs >= 1): documented codomain-≋ blocker.
simResᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP X X′ sub bodyeq (Sum.inj₁ s₁) (Sum.inj₁ s₂) ac sz
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢ₚP
  with P₀′ , Q₀′ , steps , cl₀ , c ← sim←ᵍᴬ (νσ-φfree B₁ B₂ σ s₁ s₂) (νσ-φfree-VSub B₁ B₂ σ Vσ s₁ s₂) Γ′-S ⊢body (ν-inj (bodyeq ■ U-ν-φfree-eq B₁ B₂ P₀ σ s₁ s₂)) sub ac sz =
  TP.ν B₁ B₂ P₀′ , UP.ν Q₀′ , ⋆-gmap (TP.ν B₁ B₂) TR.R-Bind steps
  , Sum.map (cong UP.ν) UR.RU-Res cl₀
  , subst (UP.ν Q₀′ ≈_) (sym (U-ν-φfree-eq B₁ B₂ P₀′ σ s₁ s₂)) (≈-ν-cong c)
simResᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP X X′ sub bodyeq (Sum.inj₂ (b , c , Bp , refl)) _ ac sz =
  peel₁ᴬ σ Vσ Γ-S (b ∷ c ∷ Bp) B₂ P₀ ⊢ₚP [] b (c ∷ Bp) refl refl refl X X′
    (ν-inj (bodyeq ■ Uν-flat σ (b ∷ c ∷ Bp) B₂ P₀)) sub bodyeq ac sz
simResᴬ σ Vσ Γ-S [] B₂ P₀ ⊢ₚP X X′ sub bodyeq (Sum.inj₁ s₁) (Sum.inj₂ _) ac sz
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢ₚP
simResᴬ σ Vσ Γ-S (b₁ ∷ []) B₂ P₀ ⊢ₚP X X′ sub bodyeq (Sum.inj₁ s₁) (Sum.inj₂ _) ac sz =
  peel₁ᴬ σ Vσ Γ-S (b₁ ∷ []) B₂ P₀ ⊢ₚP [] b₁ [] refl refl refl X X′
    (ν-inj (bodyeq ■ Uν-flat σ (b₁ ∷ []) B₂ P₀)) sub bodyeq ac sz
simResᴬ σ Vσ Γ-S (b₁ ∷ x₁ ∷ B₁t) B₂ P₀ ⊢ₚP X X′ sub bodyeq (Sum.inj₁ ()) (Sum.inj₂ _) ac sz

------------------------------------------------------------------------
-- peel₁ᴬ definitions.
------------------------------------------------------------------------

-- rest₁ exhausted: hand over to the group-2 walk.
peel₁ᴬ σ Vσ Γ-S B₁ [] P₀ ⊢ₚP D₁ r₀ [] B₁eq kEq E Zk Zk′ Zeq subk topEq ac sz
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢ₚP
peel₁ᴬ σ Vσ Γ-S B₁ (b₂ ∷ B₂t) P₀ ⊢ₚP D₁ r₀ [] B₁eq kEq E Zk Zk′ Zeq subk topEq ac sz =
  peel₂ᴬ σ Vσ Γ-S B₁ (b₂ ∷ B₂t) P₀ ⊢ₚP D₁ r₀ B₁eq [] b₂ B₂t refl D₁ (sym (++-identityʳ D₁)) kEq
    (cong (syncs (b₂ ∷ B₂t) +_) E) Zk Zk′
    (Zeq ■ subst-Bφ E (b₂ ∷ B₂t) (U[ P₀ ] (leafσ σ B₁ (b₂ ∷ B₂t))))
    subk topEq ac sz

-- head-constructor clashes at a cons-cons layer (the layer is φ-headed).
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Exp step) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Fork F V) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-New F) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Discard F V) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Par sp) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Res sp) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-LSplit F) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-RSplit F) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Acquire F) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Close F₁ F₂) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Com F₁ F₂ V) topEq ac sz
  with () ← Zeq
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Choice F₁ F₂ k₀) topEq ac sz
  with () ← Zeq

-- descend one cell.
peel₁ᴬ {n = n} σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq {k} kEq E (UP.φ f B₀) (UP.φ f′ B₀′) Zeq
       (UR.RU-Sync sp) topEq ac (acc rsz)
  with feq , beq ← φ-injU Zeq
  with P′ , Q′ , steps , cl , c≈ ←
    peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP (D₁ ++ r₀ ∷ []) c D′
      (B₁eq ■ sym (++-assoc D₁ (r₀ ∷ []) (c ∷ D′)))
      (cong suc kEq ■ sym (snoc-eq D₁ r₀ (2 + n)))
      (E ■ sym (+-suc (syncs (c ∷ D′)) k))
      B₀ B₀′
      (beq ■ cong (Bφ (c ∷ D′)) (ss-U E (sym (+-suc (syncs (c ∷ D′)) k))
        {t = Bφ B₂ (U[ P₀ ] (leafσ σ B₁ B₂))}))
      sp
      (cong UP.ν (wrapPfx D₁ r₀ kEq f B₀ feq) ■ topEq)
      ac (rsz Nat.≤-refl)
  = P′ , Q′ , steps ,
    subst (λ z → (UP.ν z ≡ Q′) Sum.⊎ (UP.ν z UR.─→ₚ Q′)) (wrapPfx D₁ r₀ kEq f B₀′ feq) cl , c≈

-- the Struct bounce: commute the layer congruence to the top and re-enter
-- sim←ᴬ with the RU-Struct count strictly decreased.
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ r₀ (c ∷ D′) B₁eq {k} kEq E _ _ Zeq
       (UR.RU-Struct c₁ i c₂) topEq (acc rs) sz
  with sim←ᴬ σ Vσ Γ-S ⊢ₚP
         (≈-trans (≈-sym (≈-ν-cong (Pfx-≈ D₁ (≈-substU kEq (≋⇒≈ c₁))))) (≋⇒≈ (≡→≋ topEq)))
         (UR.RU-Res (proj₁ (Pfx-red D₁ (subst-redU kEq i))))
         (rs (subst (Nat._< suc (sc i))
               (sym (proj₂ (Pfx-red D₁ (subst-redU kEq i)) ■ sc-subst-redU kEq i))
               Nat.≤-refl))
         (<-wellFounded _)
... | P′ , Q″ , steps , Sum.inj₁ refl , c≈ =
  P′ , _ , steps , Sum.inj₁ refl ,
  ≈-trans (≈-sym (≈-ν-cong (Pfx-≈ D₁ (≈-substU kEq (≋⇒≈ c₂))))) c≈
... | P′ , Q″ , steps , Sum.inj₂ st , c≈ =
  P′ , Q″ , steps ,
  Sum.inj₂ (UR.RU-Struct (UP.ν-cong (Pfx-≋ D₁ (subst-≋U kEq (Eq*.symmetric _ c₂)))) st ε) , c≈

-- RU-Drop: only the innermost cell can match.
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ zero (c ∷ D′) B₁eq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  with () ← proj₁ (φ-injU Zeq)
peel₁ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁ (suc r̂) (c ∷ d ∷ D″) B₁eq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  with () ← proj₂ (φ-injU Zeq)
peel₁ᴬ σ Vσ Γ-S B₁ [] P₀ ⊢ₚP D₁ (suc r̂) (c ∷ []) B₁eq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢ₚP
peel₁ᴬ σ Vσ Γ-S B₁ (b₂ ∷ e₂ ∷ B₂t) P₀ ⊢ₚP D₁ (suc r̂) (c ∷ []) B₁eq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  = ⊥-elim (substφ-¬∥ E (sym (proj₂ (φ-injU Zeq))))
peel₁ᴬ σ Vσ Γ-S B₁ (b₂ ∷ []) P₀ ⊢ₚP D₁ (suc r̂) (c ∷ []) B₁eq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  = {! fire-in₁: the innermost cell sits after the width-(suc r̂) block at
       list position ∣D₁∣ of group 1 (B₂ = b₂ ∷ [] singleton).  Reflect the
       redex through subst E ∘ leafσ (U-substσP + inv-U-∥ + frameApp-reflect +
       close-arg-var), pin the handle with drop-image₁, then r̂ = 0 → fire
       R-Drop {B₁ = D₁} with the leaf-dwk/reasm recon; r̂ = suc _ →
       drop-wide₁-⊥. !}

------------------------------------------------------------------------
-- peel₂ᴬ definitions.
------------------------------------------------------------------------

-- rest₂ exhausted: the layer IS the leaf; recurse the main inversion engine.
peel₂ᴬ {m = m} {n = n} σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ [] B₂eq WW WWeq {k} kEq E Zk Zk′ Zeq subk topEq ac sz
  with refl ← WWeq
  with refl ← B₁eq
  with refl ← B₂eq
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢ₚP
  with P₀′ , Q₀′ , steps , cl , c≈ ←
    sim←ᵍᴬ (λ i → subst Tm E (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []) i))
      (λ i → Value-subst E (VSub-leafσP σ Vσ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []) i))
      Γ′-S ⊢body
      (Zeq ■ U-substσP E (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ [])) P₀)
      subk ac sz
  = TP.ν (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []) P₀′ ,
    UP.ν (Pfx (D₁X ++ D₂) (subst UP.Proc kEq Q₀′)) ,
    ⋆-gmap (TP.ν (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ [])) TR.R-Bind steps ,
    Sum.map (cong (λ z → UP.ν (Pfx (D₁X ++ D₂) (subst UP.Proc kEq z))))
            (λ r → UR.RU-Res (proj₁ (Pfx-red (D₁X ++ D₂) (subst-redU kEq r)))) cl ,
    ≈-trans (≈-ν-cong (Pfx-≈ (D₁X ++ D₂) (≈-substU kEq
      (≈-trans c≈ (≋⇒≈ (≡→≋ (sym (U-substσP E (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ [])) P₀′))))))))
      (≋⇒≈ (≡→≋ recon≡))
  where
    recon≡ : ∀ {P₀′ : TP.Proc (sum (D₁X ++ l₁ ∷ []) + sum (D₂ ++ r₂ ∷ []) + m)} →
             UP.ν (Pfx (D₁X ++ D₂) (subst UP.Proc kEq
               (subst UP.Proc E (U[ P₀′ ] (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []))))))
             ≡ U[ TP.ν (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []) P₀′ ] σ
    recon≡ {P₀′} =
        cong UP.ν
          ( cong (Pfx (D₁X ++ D₂))
              ( ss-U E kEq {t = U[ P₀′ ] (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []))}
              ■ cong (λ e → subst UP.Proc e (U[ P₀′ ] (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []))))
                  (uipℕ _ (reasm-eq D₁X l₁ D₂ r₂ (2 + n))) )
          ■ sym (reasm D₁X l₁ D₂ r₂ (U[ P₀′ ] (leafσ σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ [])))) )
      ■ sym (Uν-flat σ (D₁X ++ l₁ ∷ []) (D₂ ++ r₂ ∷ []) P₀′)

-- head-constructor clashes at a cons-cons layer.
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Exp step) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Fork F V) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-New F) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Discard F V) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Par sp) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Res sp) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-LSplit F) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-RSplit F) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Acquire F) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Close F₁ F₂) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Com F₁ F₂ V) topEq ac sz
  with () ← Zeq
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Choice F₁ F₂ k₀) topEq ac sz
  with () ← Zeq

-- descend one group-2 cell.
peel₂ᴬ {n = n} σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq {k} kEq E (UP.φ f B₀) (UP.φ f′ B₀′) Zeq
       (UR.RU-Sync sp) topEq ac (acc rsz)
  with feq , beq ← φ-injU Zeq
  with P′ , Q′ , steps , cl , c≈ ←
    peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq (D₂ ++ r₂ ∷ []) c₂ D₂′
      (B₂eq ■ sym (++-assoc D₂ (r₂ ∷ []) (c₂ ∷ D₂′)))
      (WW ++ r₂ ∷ []) (cong (_++ r₂ ∷ []) WWeq ■ ++-assoc D₁X D₂ (r₂ ∷ []))
      (cong suc kEq ■ sym (snoc-eq WW r₂ (2 + n)))
      (E ■ sym (+-suc (syncs (c₂ ∷ D₂′)) k))
      B₀ B₀′
      (beq ■ cong (Bφ (c₂ ∷ D₂′)) (ss-U E (sym (+-suc (syncs (c₂ ∷ D₂′)) k))
        {t = U[ P₀ ] (leafσ σ B₁ B₂)}))
      sp
      (cong UP.ν (wrapPfx WW r₂ kEq f B₀ feq) ■ topEq)
      ac (rsz Nat.≤-refl)
  = P′ , Q′ , steps ,
    subst (λ z → (UP.ν z ≡ Q′) Sum.⊎ (UP.ν z UR.─→ₚ Q′)) (wrapPfx WW r₂ kEq f B₀′ feq) cl , c≈

-- the Struct bounce (group-2 flavour).
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ r₂ (c₂ ∷ D₂′) B₂eq WW WWeq {k} kEq E _ _ Zeq
       (UR.RU-Struct c₁ i c₂c) topEq (acc rs) sz
  with sim←ᴬ σ Vσ Γ-S ⊢ₚP
         (≈-trans (≈-sym (≈-ν-cong (Pfx-≈ WW (≈-substU kEq (≋⇒≈ c₁))))) (≋⇒≈ (≡→≋ topEq)))
         (UR.RU-Res (proj₁ (Pfx-red WW (subst-redU kEq i))))
         (rs (subst (Nat._< suc (sc i))
               (sym (proj₂ (Pfx-red WW (subst-redU kEq i)) ■ sc-subst-redU kEq i))
               Nat.≤-refl))
         (<-wellFounded _)
... | P′ , Q″ , steps , Sum.inj₁ refl , c≈ =
  P′ , _ , steps , Sum.inj₁ refl ,
  ≈-trans (≈-sym (≈-ν-cong (Pfx-≈ WW (≈-substU kEq (≋⇒≈ c₂c))))) c≈
... | P′ , Q″ , steps , Sum.inj₂ st , c≈ =
  P′ , Q″ , steps ,
  Sum.inj₂ (UR.RU-Struct (UP.ν-cong (Pfx-≋ WW (subst-≋U kEq (Eq*.symmetric _ c₂c)))) st ε) , c≈

-- RU-Drop: only the innermost cell can match.
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ zero (c₂ ∷ D₂′) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  with () ← proj₁ (φ-injU Zeq)
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ (suc r̂) (c₂ ∷ d₂ ∷ D₂″) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  with () ← proj₂ (φ-injU Zeq)
peel₂ᴬ σ Vσ Γ-S B₁ B₂ P₀ ⊢ₚP D₁X l₁ B₁eq D₂ (suc r̂) (c₂ ∷ []) B₂eq WW WWeq kEq E _ _ Zeq (UR.RU-Drop F) topEq ac sz
  = {! fire-in₂: the innermost cell sits after the width-(suc r̂) block at
       list position ∣D₂∣ of group 2.  Reflect through subst E ∘ leafσ, pin
       with drop-image₂, then r̂ = 0 → fire the R-Struct(ν-swap)∘R-Drop∘
       (ν-swap) composite with the leaf-dwk/reasm recon; r̂ = suc _ →
       drop-wide₂-⊥. !}

------------------------------------------------------------------------
-- Public entry: seed the well-founded recursion on the RU-Struct count.
------------------------------------------------------------------------

sim← : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
     → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
     → {R Q : UP.Proc n} → R ≈ U[ P ] σ → (red : R UR.─→ₚ Q)
     → Σ[ P′ ∈ TP.Proc m ] Σ[ Q′ ∈ UP.Proc n ]
         (P TR─→ₚ* P′ × Q ─→ᶜ? Q′ × Q′ ≈ U[ P′ ] σ)
sim← σ Vσ Γ-S ⊢P ch red = sim←ᴬ σ Vσ Γ-S ⊢P ch red (<-wellFounded (sc red)) (<-wellFounded ∣ red ∣)
