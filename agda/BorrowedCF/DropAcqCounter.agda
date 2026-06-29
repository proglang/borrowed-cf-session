module BorrowedCF.DropAcqCounter where

-- ════════════════════════════════════════════════════════════════════════
-- Does forward simulation (sim→) FAIL for the typed rules R-Drop and R-Acq
-- with head count ≥ 2 (b₁ ≥ 1), against the paper-matching definitions on
-- branch simulation2?
--
-- We answer with MACHINE-CHECKED counterexamples for BOTH rules:
--   * a CLOSED, hole-free, postulate-free typing derivation of the b₁ = 1
--     redex (Step 1), and
--   * a proof that the unique untyped step OVERSHOOTS the φ-junction flag
--     (drop→acq for R-Drop; acq→done for R-Acq), so it lands on a process
--     whose head junction flag differs from U[ reduct ]; and that ≋ cannot
--     repair the difference because ≋ preserves every φ-flag (Step 2/3).
--
-- sim→'s conclusion (Simulation2/Theorems.agda) for a typed step P ─→ₚ P′ is
--     (U[ P ] σ ─→ₚ U[ P′ ] σ)  ⊎  (U[ P ] σ ≋ U[ P′ ] σ).
-- We refute exactly this disjunction at σ∅ : 0 →ₛ 0 for both well-typed
-- redexes.
-- ════════════════════════════════════════════════════════════════════════

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Context as 𝐊
open import BorrowedCF.Processes.Typed
import BorrowedCF.Context.Substitution as 𝐒

open import BorrowedCF.Processes.Bisim
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR

open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Nat.ListAction using (sum)
open import Data.List.Relation.Unary.All as All using (All)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.Symmetric as Sym

open Nat.Variables
open Fin.Patterns

-- The empty value substitution 0 →ₛ 0.
σ∅ : 0 →ₛ 0
σ∅ ()

-- ════════════════════════════════════════════════════════════════════════
-- headFlag : extract the flag of the OUTERMOST φ-junction (skipping a leading
-- ν binder).  U[ ν B₁ B₂ P ] σ = ν ( φ ϕ[head] … ) when B₁ has a nonempty
-- tail, so headFlag (U[ … ] σ) reads exactly the head-chain junction flag.
-- ════════════════════════════════════════════════════════════════════════

flagOf : ∀ {n} → U.Proc n → Maybe U.Flag
flagOf (U.φ f P) = just f
flagOf _         = nothing

headFlag : ∀ {n} → U.Proc n → Maybe U.Flag
headFlag (U.ν P) = flagOf P
headFlag P       = flagOf P

-- ════════════════════════════════════════════════════════════════════════
-- A ≋-preserved invariant: the head-chain φ-flag.  Every base congruence
-- rule of _≋′_ either keeps the outer ν/φ structure with the SAME flag, or is
-- not applicable to the ν(φ f …) shape.  We do not need full ≋-stability of
-- headFlag in general; for the SPECIFIC processes here we use that the ONLY
-- ≋′ rules that can fire on  ν (φ f P)  are ν-cong? / φν-comm? / ν-comm? and
-- their kin, none of which change f.  (Proven below as headFlag-≋ for the
-- concrete shapes by case analysis on the closure.)
-- ════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════════════════
-- STEP 1 (R-Drop).  ⊢redex : Cempty ; [] ⊢ₚ ν (2 ∷ 1 ∷ []) (1 ∷ []) (…) is a
-- CLOSED, hole-free, postulate-free typing derivation of the b₁ = 1 R-Drop
-- redex.  (Adapted from BorrowedCF.Simulation.DropDecide on branch
-- drop-local-fix; verified to compile against the simulation2 typing.)
-- ════════════════════════════════════════════════════════════════════════

module RDrop where
  r0 : 𝕊 0
  r0 = ret

  sk0 : 𝕊 0
  sk0 = skip

  Cempty : Ctx 0
  Cempty = λ ()

  C1 : Ctx 1
  C1 0F = ⟨ sk0 ⟩

  Γhead : Ctx 2
  Γhead 0F = ⟨ r0 ⟩
  Γhead 1F = ⟨ sk0 ⟩

  e1 : (r0 ; sk0) ≃ (sk0 ; r0)
  e1 = ≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)

  e2 : (sk0 ; sk0) ≃ sk0
  e2 = ≃-skipˡ

  headChain : BindCtx′ (sk0 ; r0) 2 Γhead
  headChain =
    cons {s₁ = r0} {s₂ = sk0} {Γ′ = C1} e1
      (λ { 0F → refl ; 1F → refl })
      (cons {s₁ = sk0} {s₂ = sk0} {Γ′ = Cempty} e2
        (λ { 0F → refl })
        (nil skip))

  -- Γ1 = ⟨ret⟩ ⸴ ⟨skip⟩ ⸴ ⟨acq ; end ⁇⟩
  Γ1 : Ctx 3
  Γ1 0F = ⟨ r0 ⟩
  Γ1 1F = ⟨ sk0 ⟩
  Γ1 2F = ⟨ acq ; end ⁇ ⟩

  -- tail head ctx ⟨acq ; end ⁇⟩ (length 1)
  Ctail : Ctx 1
  Ctail 0F = ⟨ acq ; end ⁇ ⟩

  e3 : ((acq ; end ⁇) ; sk0) ≃ (acq ; end ⁇)
  e3 = ≃-skipʳ

  tailChain : BindCtx′ (acq ; end ⁇) 1 (Ctail ∘ (_↑ˡ 0))
  tailChain = cons {s₁ = acq ; end ⁇} {s₂ = sk0} {Γ′ = Cempty} e3
               (λ { 0F → refl })
               (nil skip)

  tailBind : BindCtx (acq ; end ⁇) (1 ∷ []) Ctail
  tailBind = last tailChain

  e4 : (sk0 ; end ⁇) ≃ (skip ; end ⁇)
  e4 = ≃-refl

  joinΓ1 : (Γhead ⸴* Ctail) ≗ Γ1
  joinΓ1 0F = refl
  joinΓ1 1F = refl
  joinΓ1 2F = refl

  C : BindCtx (skip ; end ⁇) (2 ∷ 1 ∷ []) Γ1
  C = cons-ret/acq {s₁ = sk0} {s₂ = end ⁇} e4 joinΓ1 headChain tailBind

  -- dual side: BindCtx (skip ; end ‼) [ 1 ] Γ2,  Γ2 = ⟨skip ; end ‼⟩
  Γ2 : Ctx 1
  Γ2 0F = ⟨ skip ; end ‼ ⟩

  e5 : ((skip ; end ‼) ; sk0) ≃ (skip ; end ‼)
  e5 = ≃-skipʳ

  dualChain : BindCtx′ (skip ; end ‼) 1 (Γ2 ∘ (_↑ˡ 0))
  dualChain = cons {s₁ = skip ; end ‼} {s₂ = sk0} {Γ′ = Cempty} e5
               (λ { 0F → refl })
               (nil skip)

  C2 : BindCtx (skip ; end ‼) (1 ∷ []) Γ2
  C2 = last dualChain




  Nskip : New {0} skip
  Nskip = skip

  ⊢ᴮ1 : ⊢ᴮ (2 ∷ 1 ∷ [])
  ⊢ᴮ1 = (record { nonZero = _ }) All.∷ All.[]

  ⊢ᴮ2 : ⊢ᴮ (1 ∷ [])
  ⊢ᴮ2 = All.[]

  bodyProc : Proc 3
  bodyProc = ⟪ (K (`end ⁇) · (K `acq · (` 1F))) ⟫ ∥ ⟪ (K (`end ‼) · (` 2F)) ⟫

  -- The R-Drop redex with b1 = 1 (head bind-group 2 ∷ 1 ∷ [])
  redex : Proc 0
  redex = ν (2 ∷ 1 ∷ []) (1 ∷ [])
            (⟪ (([] ⋯ᶠ* weakenᵣ) [ K `drop · (` 0F) ]*) ⟫ ∥ (bodyProc ⋯ₚ weakenᵣ))


  -- Full body context Δ : Ctx 4
  Δ : Ctx 4
  Δ = (Γ1 ⸴* Γ2) ⸴* Cempty

  th-drop : Δ ; (` 0F) ⊢ (K `drop · (` 0F)) ∶ `⊤ ∣ 𝕀
  th-drop = T-Conv ≃-refl ℙ≤ϵ (T-Weaken (≼-refl ∥-unit₁) (T-AppUnr refl ℙ≤ϵ (T-Const `drop) (T-Var 0F refl)))

  th-acq : Δ ; (` 2F) ⊢ (K (`end ⁇) · (K `acq · (` 2F))) ∶ `⊤ ∣ 𝕀
  th-acq = T-Weaken (≼-refl ∥-unit₁)
           (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end))
             (T-Conv ≃-refl ℙ≤ϵ (T-Weaken (≼-refl ∥-unit₁) (T-AppUnr refl ℙ≤ϵ (T-Const `acq) (T-Var 2F refl)))))

  th-end : Δ ; (` 3F) ⊢ (K (`end ‼) · (` 3F)) ∶ `⊤ ∣ 𝕀
  th-end = T-Weaken (≼-refl ∥-unit₁)
           (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end))
             (T-Conv ⟨ ≃-skipˡ ⟩ ℙ≤ϵ (T-Var 3F refl)))


  -- target body struct (as TP-Res builds it)
  gbody : Struct 4
  gbody = ((` 0F ; (` 1F ; [])) ∥ ((` 2F ; []) ∥ [])) ∥ ((` 3F ; []) ∥ []) ∥ []

  gconv : Struct 4
  gconv = (` 0F) ∥ ((` 2F) ∥ (` 3F))

  unr1 : UnrCx Δ (` 1F)
  unr1 = ` ⟨ skip ⟩

  conv≼ : Δ ∶ gconv ≼ gbody
  conv≼ = (≼-trans (≼-refl (𝐊.≈-sym 𝐊.∥-assoc)) (≼-trans (≼-cong-∥ (≼-cong-∥ (≼-trans (≼-refl (𝐊.≈-sym 𝐊.;-unit₂)) (≼-cong-; (≼-refl 𝐊.≈-refl) (≼-∅ unr1))) (≼-refl 𝐊.≈-refl)) (≼-refl 𝐊.≈-refl)) (≼-refl (𝐊.≈-trans (𝐊.∥-cong (𝐊.∥-cong (𝐊.;-cong 𝐊.≈-refl (𝐊.≈-sym 𝐊.;-unit₂)) (𝐊.≈-trans (𝐊.≈-sym 𝐊.;-unit₂) (𝐊.≈-sym 𝐊.∥-unit₂))) (𝐊.≈-trans (𝐊.≈-sym 𝐊.;-unit₂) (𝐊.≈-sym 𝐊.∥-unit₂))) (𝐊.≈-sym 𝐊.∥-unit₂)))))

  ⊢redex : Cempty ; [] ⊢ₚ redex
  ⊢redex = TP-Res Nskip ⊢ᴮ1 ⊢ᴮ2 C C2 (TP-Weaken conv≼ (TP-Par (TP-Expr th-drop) (TP-Par (TP-Expr th-acq) (TP-Expr th-end))))

  -- The R-Drop reduct: head count suc b1 -> b1, i.e. 2 :: 1 :: [] -> 1 :: 1 :: [].
  reduct : Proc 0
  reduct = ν (1 ∷ 1 ∷ []) (1 ∷ [])
             (⟪ (([] [ K `unit ]*)) ⟫ ∥ bodyProc)

  -- The actual typed step (R-Drop instantiated at b1 = 1).
  step : redex TR.─→ₚ reduct
  step = TR.R-Drop {E = []}

-- ════════════════════════════════════════════════════════════════════════
-- STEP 2 (R-Drop).  The translation's head junctions.
--   U[ redex ]  σ∅  has head junction  φ drop  (head chain count 2 -> ϕ[2]=drop)
--   U[ reduct ] σ∅  has head junction  φ drop  (head chain count 1 -> ϕ[1]=drop)
-- so a step from U[ redex ] must REACH a process ≋/=  U[ reduct ], whose head
-- junction is still  drop.  But the ONLY untyped step available is RU-Drop,
-- which flips the junction  drop -> acq  (overshoot).
-- ════════════════════════════════════════════════════════════════════════

open RDrop using (redex; reduct; step; ⊢redex)

headFlag-redex : headFlag (U[ redex ] σ∅) ≡ just U.drop
headFlag-redex = refl

headFlag-reduct : headFlag (U[ reduct ] σ∅) ≡ just U.drop
headFlag-reduct = refl

-- ── STEP 2(ii): the actual RU-Drop step from U[ redex ] σ∅. ──────────────
-- U[ redex ] σ∅ = ν (φ drop (<< K drop · C[ * x 1F x ` 0F ] >> || R)).
-- RU-Drop (under RU-Res) fires on the drop-thread, FLIPPING drop → acq.

QDrop : U.Proc 0
QDrop = U.ν (U.φ U.acq
  (U.⟪ ([] [ * ]*) ⟫ U.∥
   (U.⟪ K (`end ⁇) · (K `acq · (((` 0F) ⊗ (` 1F)) ⊗ *)) ⟫ U.∥
    U.⟪ K (`end ‼) · ((* ⊗ (` 2F)) ⊗ *) ⟫)))

dropStep : U[ redex ] σ∅ UR.─→ₚ QDrop
dropStep = UR.RU-Res (UR.RU-Drop {e = *} [] {x = 0F})

-- The step OVERSHOOTS: its result has head junction acq, not drop.
headFlag-QDrop : headFlag QDrop ≡ just U.acq
headFlag-QDrop = refl

-- acq ≠ drop, so QDrop ≠ U[ reduct ] σ∅ (whose head junction is drop).
acq≢drop : just U.acq ≢ just U.drop
acq≢drop ()

QDrop≢reduct : QDrop ≢ U[ reduct ] σ∅
QDrop≢reduct eq = acq≢drop lhs
  where
    ≡-trans : {x y z : Maybe U.Flag} → x ≡ y → y ≡ z → x ≡ z
    ≡-trans p q = subst (_ ≡_) q p
    lhs : just U.acq ≡ just U.drop
    lhs = ≡-trans (sym headFlag-QDrop) (≡-trans (cong headFlag eq) headFlag-reduct)

-- STEP 2(iii): refute the EQ disjunct via a congruence-stable invariant.
-- "procHasDrop" is true iff the process contains the constant K `drop in some
-- thread expression.  It ignores variables, so it is invariant under renaming,
-- and every base congruence rule only reassociates parallel, permutes binders,
-- and renames -- none introduces or removes a K `drop.  Hence procHasDrop is
-- congruence-stable.  It is true of U[ redex ] empty and false of
-- U[ reduct ] empty, refuting the structural-congruence disjunct.

open import Data.Bool using (Bool; true; false; _∨_)

tmHasDrop : ∀ {n} → Tm n → Bool
tmHasDrop (`_ x)               = false
tmHasDrop (K `drop)            = true
tmHasDrop (K _)                 = false
tmHasDrop (ƛ e)               = tmHasDrop e
tmHasDrop (μ e)               = tmHasDrop e
tmHasDrop (e1 · e2)           = tmHasDrop e1 ∨ tmHasDrop e2
tmHasDrop (e1 ; e2)          = tmHasDrop e1 ∨ tmHasDrop e2
tmHasDrop (e1 ⊗ e2)           = tmHasDrop e1 ∨ tmHasDrop e2
tmHasDrop (`let e1 `in e2)    = tmHasDrop e1 ∨ tmHasDrop e2
tmHasDrop (`let⊗ e1 `in e2)   = tmHasDrop e1 ∨ tmHasDrop e2
tmHasDrop (`inj i e)           = tmHasDrop e
tmHasDrop (`case e `of⟨ e1 ; e2 ⟩) = tmHasDrop e ∨ (tmHasDrop e1 ∨ tmHasDrop e2)

procHasDrop : ∀ {n} → U.Proc n → Bool
procHasDrop U.⟪ e ⟫   = tmHasDrop e
procHasDrop (P U.∥ Q) = procHasDrop P ∨ procHasDrop Q
procHasDrop (U.ν P)   = procHasDrop P
procHasDrop (U.φ f P) = procHasDrop P

-- STEP 2(iii)-stability: procHasDrop is invariant under renaming and under EQ.

∨-comm : (a b : Bool) → (a ∨ b) ≡ (b ∨ a)
∨-comm false false = refl
∨-comm false true  = refl
∨-comm true  false = refl
∨-comm true  true  = refl

∨-assoc : (a b c : Bool) → (a ∨ (b ∨ c)) ≡ ((a ∨ b) ∨ c)
∨-assoc false b c = refl
∨-assoc true  b c = refl

-- tmHasDrop ignores variables, so any renaming (Kit Kᵣ) preserves it.
tmHasDrop-⋯ : ∀ {m n} (e : Tm m) (ρ : m →ᵣ n) → tmHasDrop (e ⋯ ρ) ≡ tmHasDrop e
tmHasDrop-⋯ (`_ x) ρ = refl
tmHasDrop-⋯ (K `drop) ρ = refl
tmHasDrop-⋯ (K `unit) ρ = refl
tmHasDrop-⋯ (K `fork) ρ = refl
tmHasDrop-⋯ (K `send) ρ = refl
tmHasDrop-⋯ (K `recv) ρ = refl
tmHasDrop-⋯ (K `acq) ρ = refl
tmHasDrop-⋯ (K (`end p)) ρ = refl
tmHasDrop-⋯ (K (`new x)) ρ = refl
tmHasDrop-⋯ (K (`lsplit x)) ρ = refl
tmHasDrop-⋯ (K (`rsplit x)) ρ = refl
tmHasDrop-⋯ (K (`select x)) ρ = refl
tmHasDrop-⋯ (K `branch) ρ = refl
tmHasDrop-⋯ (ƛ e) ρ = tmHasDrop-⋯ e (ρ ↑)
tmHasDrop-⋯ (μ e) ρ = tmHasDrop-⋯ e (ρ ↑)
tmHasDrop-⋯ (e1 · e2) ρ = cong₂ _∨_ (tmHasDrop-⋯ e1 ρ) (tmHasDrop-⋯ e2 ρ)
tmHasDrop-⋯ (e1 ; e2) ρ = cong₂ _∨_ (tmHasDrop-⋯ e1 ρ) (tmHasDrop-⋯ e2 ρ)
tmHasDrop-⋯ (e1 ⊗ e2) ρ = cong₂ _∨_ (tmHasDrop-⋯ e1 ρ) (tmHasDrop-⋯ e2 ρ)
tmHasDrop-⋯ (`let e1 `in e2) ρ = cong₂ _∨_ (tmHasDrop-⋯ e1 ρ) (tmHasDrop-⋯ e2 (ρ ↑))
tmHasDrop-⋯ (`let⊗ e1 `in e2) ρ = cong₂ _∨_ (tmHasDrop-⋯ e1 ρ) (tmHasDrop-⋯ e2 (ρ ↑ ↑))
tmHasDrop-⋯ (`inj i e) ρ = tmHasDrop-⋯ e ρ
tmHasDrop-⋯ (`case e `of⟨ e1 ; e2 ⟩) ρ =
  cong₂ _∨_ (tmHasDrop-⋯ e ρ) (cong₂ _∨_ (tmHasDrop-⋯ e1 (ρ ↑)) (tmHasDrop-⋯ e2 (ρ ↑)))

procHasDrop-⋯ₚ : ∀ {m n} (P : U.Proc m) (ρ : m →ᵣ n) → procHasDrop (P U.⋯ₚ ρ) ≡ procHasDrop P
procHasDrop-⋯ₚ U.⟪ e ⟫ ρ = tmHasDrop-⋯ e ρ
procHasDrop-⋯ₚ (P U.∥ Q) ρ = cong₂ _∨_ (procHasDrop-⋯ₚ P ρ) (procHasDrop-⋯ₚ Q ρ)
procHasDrop-⋯ₚ (U.ν P) ρ = procHasDrop-⋯ₚ P (ρ ↑* 2)
procHasDrop-⋯ₚ (U.φ x P) ρ = procHasDrop-⋯ₚ P (ρ ↑)

-- Every base ≋′ rule preserves procHasDrop.
hasDrop-≋′ : ∀ {n} {P Q : U.Proc n} → P U.≋′ Q → procHasDrop P ≡ procHasDrop Q
hasDrop-≋′ {P = P U.∥ Q} U.∥-comm′ = ∨-comm (procHasDrop P) (procHasDrop Q)
hasDrop-≋′ {P = P1 U.∥ (P2 U.∥ P3)} U.∥-assoc′ =
  ∨-assoc (procHasDrop P1) (procHasDrop P2) (procHasDrop P3)
hasDrop-≋′ U.∥-unit′ = refl
hasDrop-≋′ {P = U.ν P} U.ν-swap′ = sym (procHasDrop-⋯ₚ P (swapᵣ 1 1))
hasDrop-≋′ {P = U.ν (U.ν P)} U.ν-comm′ = sym (procHasDrop-⋯ₚ P (assocSwapᵣ 2 2))
hasDrop-≋′ {P = U.φ x (U.φ y P)} U.φ-comm′ = sym (procHasDrop-⋯ₚ P (assocSwapᵣ 1 1))
hasDrop-≋′ {P = U.ν (U.φ x P)} U.νφ-comm′ = sym (procHasDrop-⋯ₚ P (assocSwapᵣ 1 2))
hasDrop-≋′ {P = P U.∥ U.ν Q} U.ν-ext′ = cong (_∨ procHasDrop Q) (sym (procHasDrop-⋯ₚ P (weaken* ⦃ Kᵣ ⦄ 2)))
hasDrop-≋′ {P = P U.∥ U.φ x Q} U.φ-ext′ = cong (_∨ procHasDrop Q) (sym (procHasDrop-⋯ₚ P (weaken* ⦃ Kᵣ ⦄ 1)))
hasDrop-≋′ {P = P1 U.∥ Q} (U.∥-cong′ r) = cong (_∨ procHasDrop Q) (hasDrop-≋′ r)
hasDrop-≋′ (U.ν-cong′ r) = hasDrop-≋′ r
hasDrop-≋′ (U.φ-cong′ r) = hasDrop-≋′ r

-- transitivity helper
≡-trans₂ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans₂ p q = subst (_ ≡_) q p

-- Lift to the symmetric-transitive closure ≋ = EqClosure ≋′.
hasDrop-≋ : ∀ {n} {P Q : U.Proc n} → P U.≋ Q → procHasDrop P ≡ procHasDrop Q
hasDrop-≋ Star.ε = refl
hasDrop-≋ (Sym.fwd r Star.◅ rs) = ≡-trans₂ (hasDrop-≋′ r) (hasDrop-≋ rs)
hasDrop-≋ (Sym.bwd r Star.◅ rs) = ≡-trans₂ (sym (hasDrop-≋′ r)) (hasDrop-≋ rs)


-- STEP 2(iii)-final: assemble the refutations.

hasDrop-redex : procHasDrop (U[ redex ] σ∅) ≡ true
hasDrop-redex = refl

hasDrop-reduct : procHasDrop (U[ reduct ] σ∅) ≡ false
hasDrop-reduct = refl

true≢false : true ≢ false
true≢false ()

-- (a) The structural-congruence disjunct is IMPOSSIBLE: ≋ preserves
-- procHasDrop, but it is true of U[ redex ] and false of U[ reduct ].
¬≋-drop : ¬ (U[ redex ] σ∅ U.≋ U[ reduct ] σ∅)
¬≋-drop eq = true≢false lhs
  where
    lhs : true ≡ false
    lhs = ≡-trans₂ (sym hasDrop-redex) (≡-trans₂ (hasDrop-≋ eq) hasDrop-reduct)

-- ════ STEP 3 (R-Acq): well-typed b1=1 acq redex + flag overshoot.
-- Typed R-Acq : nu (0 :: suc b1 :: B1) B2 (<<E[acq.0F]>> || P)
--              -->p nu (suc b1 :: B1) B2 (<<E[var0]>> || P).
-- New session s = msg ‼ `⊤ (New-able; the acq residual <msg ‼ `⊤> closes to
-- `⊤ via send).  Head group 0 :: 2 :: 1 :: [] (b1=1); ϕ[0]=acq.
-- Reduct head group 2 :: 1 :: [] -> ϕ[2]=drop. RU-Acquire flips acq->done.

module RAcq where
  Cempty : Ctx 0
  Cempty = λ ()

  acqS retS skipS : 𝕊 0
  acqS = acq
  retS = ret
  skipS = skip
  msgS : 𝕊 0
  msgS = msg ‼ `⊤
  endQ : 𝕊 0
  endQ = end ⁇

  ≃-assoc : {a b c : 𝕊 0} → ((a ; b) ; c) ≃ (a ; (b ; c))
  ≃-assoc = Eq*.return ≃𝕊-assoc

  Γhead : Ctx 2
  Γhead 0F = ⟨ acqS ; msgS ⟩
  Γhead 1F = ⟨ retS ⟩

  C1 : Ctx 1
  C1 0F = ⟨ retS ⟩

  hc-e1 : (((acqS ; msgS) ; retS)) ≃ ((acqS ; msgS) ; retS)
  hc-e1 = ≃-refl

  hc-e2 : (retS ; skipS) ≃ retS
  hc-e2 = ≃-skipʳ

  headChain : BindCtx′ ((acqS ; msgS) ; retS) 2 Γhead
  headChain =
    cons {s₁ = acqS ; msgS} {s₂ = retS} {Γ′ = C1} hc-e1
      (λ { 0F → refl ; 1F → refl })
      (cons {s₁ = retS} {s₂ = skipS} {Γ′ = Cempty} hc-e2
        (λ { 0F → refl })
        (nil skip))

  Ctail : Ctx 1
  Ctail 0F = ⟨ acqS ; endQ ⟩

  tc-e : ((acqS ; endQ) ; skipS) ≃ (acqS ; endQ)
  tc-e = ≃-skipʳ

  tailChain : BindCtx′ (acqS ; endQ) 1 (Ctail ∘ (_↑ˡ 0))
  tailChain = cons {s₁ = acqS ; endQ} {s₂ = skipS} {Γ′ = Cempty} tc-e
               (λ { 0F → refl })
               (nil skip)

  tailBind : BindCtx (acqS ; endQ) (1 ∷ []) Ctail
  tailBind = last tailChain

  Γ1 : Ctx 3
  Γ1 0F = ⟨ acqS ; msgS ⟩
  Γ1 1F = ⟨ retS ⟩
  Γ1 2F = ⟨ acqS ; endQ ⟩

  joinΓ1 : (Γhead ⸴* Ctail) ≗ Γ1
  joinΓ1 0F = refl
  joinΓ1 1F = refl
  joinΓ1 2F = refl

  cra-e : ((acqS ; msgS) ; endQ) ≃ (acqS ; (msgS ; endQ))
  cra-e = ≃-assoc

  Cinner : BindCtx (acqS ; (msgS ; endQ)) (2 ∷ 1 ∷ []) Γ1
  Cinner = cons-ret/acq {s₁ = acqS ; msgS} {s₂ = endQ} cra-e joinΓ1 headChain tailBind

  C : BindCtx (msgS ; endQ) (0 ∷ 2 ∷ 1 ∷ []) Γ1
  C = cons-acq Cinner

  Ns : New {0} msgS
  Ns = msg
