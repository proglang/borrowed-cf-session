module BorrowedCF.Simulation2.OrderPincer where

-- ============================================================================
--  head-min?  —  is the operative channel of a HEAD redex the ;-MINIMAL live
--  non-Unr borrow of the thread's ordered context?
--
--  VERDICT: FALSE.  The candidate counterexample from the task (the frame
--  `V ·□`) is genuinely well-typed via T-AppRight, whose conclusion Struct is
--  γ_function ; γ_argument  (the FUNCTION's context ;-BEFORE the argument's).
--  A function VALUE `V = ƛ …` may — by T-Abs with an R-directed *linear* arrow
--  — capture a live linear borrow `y` in γ_function; the head redex `c · ` x`
--  sits in the argument γ_argument.  Hence  y  ;-strictly-before  x  while  y
--  is a live non-Unr borrow  ⟹  head-min is FALSE.
--
--  Concretely we build, machine-checked:
--     Γc ; ((` 1F) ; (` 0F)) ⊢ₚ ⟪ (ƛ ((drop · ` 2F) ; ` 0F)) · (drop · ` 0F) ⟫
--  with  Γc 0F = Γc 1F = ⟨ ret ⟩  (both linear).  The head redex is  drop · ` 0F
--  (channel op on ` 0F), yet borrow 1F is a live non-Unr borrow ;-BEFORE 0F.
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

-- Both slots are non-unrestricted (ret ∉ Skips).
¬u0 : ¬ Unr (Γc 0F)
¬u0 (⟨ () ⟩)

¬u1 : ¬ Unr (Γc 1F)
¬u1 (⟨ () ⟩)

-- ============================================================================
--  The R-directed, LINEAR, S-mobility, impure arrow used by the captured
--  function value V.  It is *not* Unr, so T-Abs's Γ-unr obligation is vacuous,
--  and it *is* R-directed, so it drives T-AppRight (γ_fn ; γ_arg).
-- ============================================================================
aR : Arr
aR = record
  { lin = 𝟙
  ; dir = R
  ; mob = S
  ; eff = 𝕀
  ; ω⇒M = λ ()
  ; ω⇒𝟙 = λ ()
  }

-- ── The captured function value: ƛ ((drop · ` 2F) ; ` 0F). ──
-- Body scope = 3.  0F = bound argument (: `⊤), 1F = old 0F, 2F = old 1F (= y).
-- It consumes y (2F) via drop, then returns the argument (0F).
Vbody : Tm 3
Vbody = (K `drop · (` 2F)) ; (` 0F)

Vfun : Tm 2
Vfun = ƛ Vbody

-- ── Vfun is a Value. ──
Vfun-value : Value Vfun
Vfun-value = V-λ

-- ============================================================================
--  Typing of the captured function.  γ_function = (` 1F): it holds the LIVE
--  linear borrow y = old slot 1F.  Arrow is aR (R-directed, linear).
-- ============================================================================

-- body Struct  =  join R (` 0F) (wk (` 1F))  =  (` 2F) ; (` 0F).
⊢drop-y : (`⊤ ⸴ Γc) ; ((` 2F) ; (` 0F)) ⊢ Vbody ∶ `⊤ ∣ 𝕀
⊢drop-y =
  T-Conv ≃-refl ℙ≤ϵ
    (T-Seq `⊤
       (T-Weaken (≼-refl ∥-unit₁)
          (T-AppUnr refl ℙ≤ϵ (T-Const `drop)
             (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 2F refl))))
       (T-Conv `⊤ ℙ≤ϵ (T-Var 0F refl)))

⊢Vfun : Γc ; (` 1F) ⊢ Vfun ∶ `⊤ ⟨ aR ⟩→ `⊤ ∣ ℙ
⊢Vfun = T-Abs (λ ()) (λ ()) ⊢drop-y

-- ============================================================================
--  The head redex  drop · ` 0F  (channel op on ` 0F), typed at Struct (` 0F).
-- ============================================================================
redex : Tm 2
redex = K `drop · (` 0F)

⊢redex : Γc ; (` 0F) ⊢ redex ∶ `⊤ ∣ ℙ
⊢redex =
  T-Weaken (≼-refl ∥-unit₁)
    (T-AppUnr refl ℙ≤ϵ (T-Const `drop)
       (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))

-- ── ` 0F is a Value (channel var), so redex is the head Blocked redex. ──
redex-blocked : Blocked redex
redex-blocked = K `drop , (` 0F) , V-` , refl

-- ============================================================================
--  THE APPLICATION, via T-AppRight:  Γc ; (γ_fn ; γ_arg) = (` 1F) ; (` 0F).
--  The function's borrow 1F lands ;-BEFORE the head-redex channel 0F.
-- ============================================================================
whole : Tm 2
whole = Vfun · redex

⊢whole : Γc ; ((` 1F) ; (` 0F)) ⊢ whole ∶ `⊤ ∣ 𝕀
⊢whole = T-AppRight refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ ⊢Vfun) ⊢redex

-- ── The full well-typed THREAD. ──
⊢thread : Γc ; ((` 1F) ; (` 0F)) ⊢ₚ ⟪ whole ⟫
⊢thread = TP-Expr ⊢whole

-- ============================================================================
--  The FRAME* decomposition witnessing that  drop · ` 0F  is the HEAD redex.
--  F = [ Vfun-value ·□ ]  and  F [ redex ]* ≡ whole.
-- ============================================================================
F* : Frame* 2
F* = (Vfun-value ·□) ∷ []

frame-plug : F* [ redex ]* ≡ whole
frame-plug = refl

-- ============================================================================
--  ;-PRECEDENCE and the REFUTATION of head-min.
--
--  head-min would assert: in a well-typed thread whose ordered context is α,
--  with head-redex channel x, no OTHER live non-Unr borrow y is ;-strictly-
--  before x in α.  We formalise "y ;-strictly-before x" positionally and show
--  the witness above violates it: 1F is ;-before 0F, both live & non-Unr.
--
--  `;-before` : x occurs in a left ;-operand whose right operand contains y.
-- ============================================================================
-- occurrence of a leaf in a Struct (positional, decidable-by-refl for closed γ)
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

-- In the witness Struct (` 1F) ; (` 0F):  1F ≺ 0F  (1F is ;-before 0F).
1F≺0F : _≺⟨_⟩_ {2} 1F ((` 1F) ; (` 0F)) 0F
1F≺0F = here refl refl

-- ============================================================================
--  head-min, stated for THIS thread, and its DISPROOF.
--
--  We phrase head-min as the property that would be USED by the reverse
--  channel cases: "the head-redex channel x=0F is such that no live non-Unr
--  borrow is ;-strictly-before it".  The witness exhibits y=1F ;-before x=0F
--  with y live (in Γc, ⟨ ret ⟩) and non-Unr — a direct refutation.
-- ============================================================================

-- The statement "x is ;-minimal among live non-Unr borrows of α":
head-min-at : (α : Struct 2) (x : 𝔽 2) → Set
head-min-at α x = ∀ y → ¬ Unr (Γc y) → count-occ y α → ¬ (y ≺⟨ α ⟩ x)

-- head-min FAILS for the witness: 0F is NOT ;-minimal (1F sits ;-before it).
head-min-false : ¬ head-min-at ((` 1F) ; (` 0F)) 0F
head-min-false hm = hm 1F ¬u1 (inj₁ refl) 1F≺0F
