module BorrowedCF.Simulation2.HeadMin where

-- ============================================================================
--  head-min?  —  is the operative channel of a HEAD (channel-op) redex the
--  ;-MINIMAL live non-Unr borrow of the thread's ordered context?
--
--  This is the port of OrderPincer.agda (written against the OLD, function-first
--  application calculus) to the CURRENT, DIRECTED / argument-first calculus.
--
--  VERDICT (machine-checked below): head-min is STILL FALSE.
--
--  The argument-first change (T-AppLeft concludes  γ_arg ; γ_fn) repairs the
--  L-directed route, but leaves T-AppRight untouched: an R-directed application
--  is FUNCTION-first, both in the evaluation order (Frame `app₂ Vfun R` requires
--  the function to be a Value) AND in the ordered context (T-AppRight concludes
--  γ_fn ; γ_arg).  So an R-directed function VALUE `V = ƛ R …` — typed by T-Abs
--  with a *linear* (non-Unr) R-arrow, whose Γ-unr obligation is therefore
--  vacuous — may CAPTURE a live linear borrow `y` in γ_fn; the head channel-op
--  redex `drop ·¹ ` x` sits in γ_arg.  Hence  y  ;-strictly-before  x  while  y
--  is a live non-Unr borrow  ⟹  head-min is FALSE, exactly as before.
--
--  Concretely (all machine-checked):
--     Γc ; ((` 1F) ; ([] ∥ (` 0F))) ⊢ₚ ⟪ (ƛ R ((drop ·¹ ` 2F) ; ` 0F)) ·ᴿ (drop ·¹ ` 0F) ⟫
--  with  Γc 0F = Γc 1F = ⟨ ret ⟩  (both linear).  The head redex is  drop ·¹ ` 0F
--  (channel op on ` 0F), reached through the frame  app₂ (ƛ R …) R (value),
--  yet borrow 1F is a live non-Unr borrow ;-BEFORE 0F.
-- ============================================================================

open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (Unr)
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed

open Fin.Patterns
open Nat.Variables

-- ── The two-slot channel context: both slots are linear ⟨ ret ⟩. ──
Γc : Ctx 2
Γc = ⟨ ret ⟩ F.∷ ⟨ ret ⟩ F.∷ (λ ())

¬u0 : ¬ Unr (Γc 0F)
¬u0 (⟨ () ⟩)

¬u1 : ¬ Unr (Γc 1F)
¬u1 (⟨ () ⟩)

-- ── The R-directed, LINEAR, S-mobility, impure arrow captured by the value. ──
aR : Arr
aR = record
  { lin = 𝟙 ; dir = R ; mob = S ; eff = 𝕀
  ; ω⇒M = λ () ; ω⇒𝟙 = λ () }

-- ── The captured function value: ƛ R ((drop ·¹ ` 2F) ; ` 0F). ──
-- Body scope = 3.  0F = bound argument (: `⊤), 1F = old 0F, 2F = old 1F (= y).
Vbody : Tm 3
Vbody = (K `drop ·¹ (` 2F)) ; (` 0F)

Vfun : Tm 2
Vfun = ƛ R Vbody

Vfun-value : Value Vfun
Vfun-value = V-λ

-- body Struct  =  join R (` 0F) (wk (` 1F))  =  (` 2F) ; (` 0F).
⊢drop-y : (`⊤ ⸴ Γc) ; ((` 2F) ; (` 0F)) ⊢ Vbody ∶ `⊤ ∣ 𝕀
⊢drop-y =
  T-Seq `⊤
    (T-Conv ≃-refl ℙ≤ϵ
      (T-Weaken (≼-refl ∥-unit₁)
        (T-AppUnr refl ℙ≤ϵ (T-Const `drop)
          (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 2F refl)))))
    (T-Conv `⊤ ℙ≤ϵ (T-Var 0F refl))

⊢Vfun : Γc ; (` 1F) ⊢ Vfun ∶ `⊤ ⟨ aR ⟩→ `⊤ ∣ ℙ
⊢Vfun = T-Abs (λ ()) (λ ()) ⊢drop-y

-- ── The head channel-op redex  drop ·¹ ` 0F, typed at Struct ([] ∥ (` 0F)). ──
redex : Tm 2
redex = K `drop ·¹ (` 0F)

⊢redex : Γc ; ([] ∥ (` 0F)) ⊢ redex ∶ `⊤ ∣ ℙ
⊢redex = T-AppUnr refl ℙ≤ϵ (T-Const `drop)
           (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))

redex-blocked : Blocked redex
redex-blocked = K `drop , 𝟙 , (` 0F) , V-` , refl

-- ============================================================================
--  THE APPLICATION, via T-AppRight:  Γc ; (γ_fn ; γ_arg) = (` 1F) ; ([] ∥ ` 0F).
--  The function's borrow 1F lands ;-BEFORE the head-redex channel 0F.
-- ============================================================================
whole : Tm 2
whole = Vfun ·ᴿ redex

⊢whole : Γc ; ((` 1F) ; ([] ∥ (` 0F))) ⊢ whole ∶ `⊤ ∣ 𝕀
⊢whole = T-AppRight refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ ⊢Vfun) ⊢redex

⊢thread : Γc ; ((` 1F) ; ([] ∥ (` 0F))) ⊢ₚ ⟪ whole ⟫
⊢thread = TP-Expr ⊢whole

-- ── The FRAME* decomposition witnessing  drop ·¹ ` 0F  IS the head redex. ──
F* : Frame* 2
F* = app₂ Vfun R (λ{ (inj₂ refl) → V-λ }) ∷ []

frame-plug : F* [ redex ]* ≡ whole
frame-plug = refl

-- ============================================================================
--  ;-PRECEDENCE and the REFUTATION of head-min.
-- ============================================================================
count-occ : 𝔽 n → Struct n → Set
count-occ x (` z)   = x ≡ z
count-occ x []      = ⊥
count-occ x (α ∥ β) = count-occ x α ⊎ count-occ x β
count-occ x (α ; β) = count-occ x α ⊎ count-occ x β

data _≺⟨_⟩_ {n} (x : 𝔽 n) : Struct n → 𝔽 n → Set where
  here  : ∀ {α β} {y} → count-occ x α → count-occ y β → x ≺⟨ α ; β ⟩ y
  left  : ∀ {α β} {y} → x ≺⟨ α ⟩ y → x ≺⟨ α ; β ⟩ y
  right : ∀ {α β} {y} → x ≺⟨ β ⟩ y → x ≺⟨ α ; β ⟩ y
  parL  : ∀ {α β} {y} → x ≺⟨ α ⟩ y → x ≺⟨ α ∥ β ⟩ y
  parR  : ∀ {α β} {y} → x ≺⟨ β ⟩ y → x ≺⟨ α ∥ β ⟩ y

-- In the witness Struct (` 1F) ; ([] ∥ (` 0F)):  1F ≺ 0F.
1F≺0F : _≺⟨_⟩_ {2} 1F ((` 1F) ; ([] ∥ (` 0F))) 0F
1F≺0F = here refl (inj₂ refl)

-- head-min, stated for THIS thread, and its DISPROOF.
head-min-at : (α : Struct 2) (x : 𝔽 2) → Set
head-min-at α x = ∀ y → ¬ Unr (Γc y) → count-occ y α → ¬ (y ≺⟨ α ⟩ x)

-- head-min FAILS for the witness: 0F is NOT ;-minimal (1F sits ;-before it).
head-min-false : ¬ head-min-at ((` 1F) ; ([] ∥ (` 0F))) 0F
head-min-false hm = hm 1F ¬u1 (inj₁ refl) 1F≺0F
