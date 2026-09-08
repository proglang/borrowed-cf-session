-- | From a BC / AC membership witness to a LOCATED thread (agent G1, wave 2).
--
--   `Safety/Blocked.agda` (agent F) records "the handle `x` is consumed
--   somewhere in `P`" as the inductive predicates `_∈BC_` / `_∈AC_`.  The
--   redex lemmas of `Safety/Progress/Redex.agda` want the same information in
--   the form `Simulation/BackwardSoup/` speaks: a `ProcessContext` whose hole
--   is the thread that holds the redex, and the image of `x` at that hole.
--   The two are the same induction: `∥ˡ` / `∥ʳ` / `res` extend the context by
--   `par-left` / `par-right` / `bind`, and `weakenThrough` follows along
--   definitionally, because `weakenThrough (bind B₁ B₂ ctx) x` IS
--   `weakenThrough ctx ((sum B₁ + sum B₂) ↑ʳ x)`, exactly the index that the
--   `res` constructor of `_∈BC_` / `_∈AC_` uses.
module BorrowedCF.Safety.Progress.Redex.Located where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (Dir)
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed using (Proc; ⟪_⟫; _∥_; ν)

open import BorrowedCF.Safety.Blocked
  using ( _∈BC_; _∈AC_; _∈BCe_; _∈ACe_; thr; ∥ˡ; ∥ʳ; res
        ; BCRedex; bc-send; bc-recv; bc-select; bc-branch; bc-end
        ; ACRedex; ac-acq
        ; send; recv; select; branch; end; acq )

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position using (weakenThrough)

open Nat.Variables
open Variables

------------------------------------------------------------------------
-- 1.  The thread level: a `_∈BCe_` / `_∈ACe_` witness IS a frame stack with
--     a constant application at the bottom.

∈BCe⇒shape :
  {x : 𝔽 n} {e : Tm n} → x ∈BCe e →
  Σ[ E ∈ Frame* n ] Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ w ∈ Tm n ]
    (e ≡ E [ K c ·⟨ d ⟩ w ]*) × BCRedex x (K c ·⟨ d ⟩ w)
∈BCe⇒shape (send E V)   = E , _ , _ , _ , refl , bc-send V
∈BCe⇒shape (recv E)     = E , _ , _ , _ , refl , bc-recv
∈BCe⇒shape (select E i) = E , _ , _ , _ , refl , bc-select i
∈BCe⇒shape (branch E)   = E , _ , _ , _ , refl , bc-branch
∈BCe⇒shape (end E p)    = E , _ , _ , _ , refl , bc-end p

∈ACe⇒shape :
  {x : 𝔽 n} {e : Tm n} → x ∈ACe e →
  Σ[ E ∈ Frame* n ] Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ w ∈ Tm n ]
    (e ≡ E [ K c ·⟨ d ⟩ w ]*) × ACRedex x (K c ·⟨ d ⟩ w)
∈ACe⇒shape (acq E) = E , _ , _ , _ , refl , ac-acq

------------------------------------------------------------------------
-- 2.  The process level.

∈BC⇒located :
  {P : Proc n} {x : 𝔽 n} → x ∈BC P →
  Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ E ∈ Frame* k ]
  Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ w ∈ Tm k ]
    (P ≡ plug ctx ⟪ E [ K c ·⟨ d ⟩ w ]* ⟫)
      × BCRedex (weakenThrough ctx x) (K c ·⟨ d ⟩ w)
∈BC⇒located (thr mem)
  with E , c , d , w , refl , bc ← ∈BCe⇒shape mem =
  _ , hole , E , c , d , w , refl , bc
∈BC⇒located {P = P ∥ Q} (∥ˡ mem)
  with _ , ctx , E , c , d , w , refl , bc ← ∈BC⇒located mem =
  _ , par-left ctx Q , E , c , d , w , refl , bc
∈BC⇒located {P = P ∥ Q} (∥ʳ mem)
  with _ , ctx , E , c , d , w , refl , bc ← ∈BC⇒located mem =
  _ , par-right P ctx , E , c , d , w , refl , bc
∈BC⇒located {P = ν B₁ B₂ P} (res mem)
  with _ , ctx , E , c , d , w , refl , bc ← ∈BC⇒located mem =
  _ , bind B₁ B₂ ctx , E , c , d , w , refl , bc

∈AC⇒located :
  {P : Proc n} {x : 𝔽 n} → x ∈AC P →
  Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ E ∈ Frame* k ]
  Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ w ∈ Tm k ]
    (P ≡ plug ctx ⟪ E [ K c ·⟨ d ⟩ w ]* ⟫)
      × ACRedex (weakenThrough ctx x) (K c ·⟨ d ⟩ w)
∈AC⇒located (thr mem)
  with E , c , d , w , refl , ac ← ∈ACe⇒shape mem =
  _ , hole , E , c , d , w , refl , ac
∈AC⇒located {P = P ∥ Q} (∥ˡ mem)
  with _ , ctx , E , c , d , w , refl , ac ← ∈AC⇒located mem =
  _ , par-left ctx Q , E , c , d , w , refl , ac
∈AC⇒located {P = P ∥ Q} (∥ʳ mem)
  with _ , ctx , E , c , d , w , refl , ac ← ∈AC⇒located mem =
  _ , par-right P ctx , E , c , d , w , refl , ac
∈AC⇒located {P = ν B₁ B₂ P} (res mem)
  with _ , ctx , E , c , d , w , refl , ac ← ∈AC⇒located mem =
  _ , bind B₁ B₂ ctx , E , c , d , w , refl , ac

------------------------------------------------------------------------
-- 3.  The specialised `_∈AC_` form: the constant is `acq` and the argument is
--     the variable itself.  (`ACRedex` has a single constructor, so the
--     pattern match is complete.)

∈AC⇒located-acq :
  {P : Proc n} {x : 𝔽 n} → x ∈AC P →
  Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ E ∈ Frame* k ] Σ[ d ∈ Dir ]
    P ≡ plug ctx ⟪ E [ K `acq ·⟨ d ⟩ (` weakenThrough ctx x) ]* ⟫
∈AC⇒located-acq mem
  with _ , ctx , E , _ , d , _ , eq , ac-acq ← ∈AC⇒located mem =
  _ , ctx , E , d , eq
