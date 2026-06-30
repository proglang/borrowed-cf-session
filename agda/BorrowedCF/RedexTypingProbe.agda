module BorrowedCF.RedexTypingProbe where

open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed

open Fin.Patterns
open Nat.Variables

import BorrowedCF.RsplitOwnershipProbe as P

-- ============================================================================
-- The handle slot 0F of the chain context g2 has type < msg ! T >.
-- ============================================================================
handle-type : P.g2 0F ≡ ⟨ msg ‼ `⊤ ⟩
handle-type = refl

-- The off-handle 1F has type < msg ? T >.
offhandle-type : P.g2 1F ≡ ⟨ msg ⁇ `⊤ ⟩
offhandle-type = refl

-- ============================================================================
-- POSITIVE: rsplit applied to the handle, producing the PAIR, DOES typecheck.
-- We pick s = msg ! T, s' = skip, so < s ; s' > == < msg ! T ; skip > =~= < msg ! T >.
-- rsplit needs the arg :: < s ; s' > with not Skips s.
-- ============================================================================
nskips : ¬ Skips {0} (msg ‼ `⊤)
nskips ()

-- The argument ` 0F converted from < msg ! T > to < msg ! T ; skip >.
arg-conv : P.g2 ; (` 0F) ⊢ ` 0F ∶ ⟨ msg ‼ `⊤ ; skip ⟩ ∣ ℙ
arg-conv = T-Conv ⟨ ≃-sym ≃-skipʳ ⟩ ℙ≤ϵ (T-Var 0F refl)

-- rsplit . ` 0F typechecks with the PAIR result type.
rsplit-pair :
  P.g2 ; ([] ∥ (` 0F)) ⊢ K (`rsplit (msg ‼ `⊤)) · (` 0F)
       ∶ ⟨ (msg ‼ `⊤) ; ret ⟩ ⊗¹ ⟨ acq ; skip ⟩ ∣ ℙ
rsplit-pair = T-AppLin refl ℙ≤ϵ (T-Const (`rsplit nskips skip)) arg-conv


-- ============================================================================
-- inj 0F (handle) reduces to slot 0F; off-handle to 1F (B1 = B2 = B = []).
-- ============================================================================
open import BorrowedCF.Reduction.Processes.Typed as TR using ()
module SR = TR.SplitRenamings [] [] []

inj0 : SR.inj {2 ∷ []} {0} 0F ≡ 0F
inj0 = refl

inj1 : SR.inj {2 ∷ []} {0} 1F ≡ 1F
inj1 = refl

-- ============================================================================
-- OBSTRUCTION (A): the EMPTY FRAME thread requires TP-Expr's body :: `T at I.
-- rsplit's result is a TENSOR pair < _ ; _ > (x)1 < _ ; _ >, which is NEVER
-- =~= `T.  So << K (rsplit ...) . (` 0F) >> CANNOT be a well-typed thread.
-- ============================================================================
pair-not-unit :
  ¬ ( (⟨ (msg ‼ `⊤) ; ret ⟩ ⊗¹ ⟨ acq ; skip ⟩) ≃ `⊤ )
pair-not-unit ()

-- ============================================================================
-- OBSTRUCTION (B): the counterexample uses K (rsplit sP) with the WHOLE sP as
-- the rsplit session parameter. Then the argument must be < sP ; s' >.  But the
-- handle has type < msg ! T > and  sP = msg ! T ; (msg ? T ; skip).
-- We exhibit the rsplit-sP result type for the record.
-- ============================================================================
sP-pair-not-unit :
  ¬ ( (⟨ P.sP ; ret ⟩ ⊗¹ ⟨ acq ; skip ⟩) ≃ `⊤ )
sP-pair-not-unit ()


-- ============================================================================
-- THE DECISIVE NO-DERIVATION THEOREM (empty-frame rsplit thread is ILL-TYPED).
--
-- The counterexample's redexBody uses the EMPTY frame [], so its rsplit thread
-- is exactly  << K (rsplit sP) . (` 0F) >>.  By TP-Expr this thread is well-
-- typed iff the body has type `T at effect I.  We prove NO such body typing
-- exists: rsplit's result is a tensor pair, never =~= `T.  Hence  src  is NOT
-- well-typed -- the rsplit counterexample's source process is VACUOUS.
-- ============================================================================

open import BorrowedCF.Terms using (inv-K)

-- Codomain extraction from an arrow equivalence (mirrors RsInv.T-dom).
≃-cod : ∀ {m} {T U R R′ : Ty 𝕥 m} {a a′}
      → (T ⟨ a ⟩→ R) ≃ (U ⟨ a′ ⟩→ R′) → R ≃ R′
≃-cod (_ `→ eq) = eq

-- The constant  rsplit sP  has ONLY the rsplit type; its codomain is a tensor.
-- Invert  |- rsplit sP : V  to read the codomain off as a tensor pair.
rsplit-const-cod-tensor :
  ∀ {V : 𝕋} {Targ Tres a}
  → ⊢ `rsplit P.sP ∶ V
  → V ≃ (Targ ⟨ a ⟩→ Tres)
  → Σ[ s′ ∈ 𝕊 0 ] (Tres ≃ (⟨ P.sP ; ret ⟩ ⊗¹ ⟨ acq ; s′ ⟩))
rsplit-const-cod-tensor (`rsplit ¬sk s′) Veq = s′ , ≃-sym (≃-cod Veq)

-- Helper: the application head  K (rsplit sP)  typed at any arrow forces the
-- arrow's codomain to be a (rsplit) tensor.
head-cod-tensor :
  ∀ {m} {Γ : Ctx m} {γ} {Targ Tres a ϵ}
  → Γ ; γ ⊢ K (`rsplit P.sP) ∶ (Targ ⟨ a ⟩→ Tres) ∣ ϵ
  → Σ[ s′ ∈ 𝕊 0 ] (Tres ≃ (⟨ P.sP ; ret ⟩ ⊗¹ ⟨ acq ; s′ ⟩))
head-cod-tensor ⊢f with inv-K ⊢f
... | _ , U≃ , _ , ⊢c = rsplit-const-cod-tensor ⊢c U≃

-- A tensor is never =~= `T  (general form).
tensor≄⊤ : ∀ {m} {T U : Ty 𝕥 m} {d} → ¬ ((T ⊗⟨ d ⟩ U) ≃ `⊤)
tensor≄⊤ ()

-- THE OBSTRUCTION: no body typing  Gamma ; gamma |- rsplit sP . ` 0F : `T | eps.
-- (Quantified over ALL contexts/structs/effects -- fully general.)
rsplit-app-not-unit :
  ∀ {m} {Γ : Ctx (suc m)} {γ} {ϵ}
  → ¬ ( Γ ; γ ⊢ K (`rsplit P.sP) · (` 0F) ∶ `⊤ ∣ ϵ )
rsplit-app-not-unit (T-AppUnr {U = U} _ _ ⊢f _) =
  let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-sym Teq)
rsplit-app-not-unit (T-AppLin {U = U} _ _ ⊢f _) =
  let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-sym Teq)
rsplit-app-not-unit (T-AppLeft {U = U} _ _ ⊢f _) =
  let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-sym Teq)
rsplit-app-not-unit (T-AppRight {U = U} _ _ ⊢f _) =
  let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-sym Teq)
rsplit-app-not-unit (T-Conv T≃ _ d) = rsplit-app-not-unit-conv T≃ d
  where
    rsplit-app-not-unit-conv :
      ∀ {m} {Γ : Ctx (suc m)} {γ} {T ϵ}
      → T ≃ `⊤ → Γ ; γ ⊢ K (`rsplit P.sP) · (` 0F) ∶ T ∣ ϵ → ⊥
    rsplit-app-not-unit-conv T≃ (T-AppUnr _ _ ⊢f _) =
      let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-trans (≃-sym Teq) T≃)
    rsplit-app-not-unit-conv T≃ (T-AppLin _ _ ⊢f _) =
      let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-trans (≃-sym Teq) T≃)
    rsplit-app-not-unit-conv T≃ (T-AppLeft _ _ ⊢f _) =
      let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-trans (≃-sym Teq) T≃)
    rsplit-app-not-unit-conv T≃ (T-AppRight _ _ ⊢f _) =
      let _ , Teq = head-cod-tensor ⊢f in tensor≄⊤ (≃-trans (≃-sym Teq) T≃)
    rsplit-app-not-unit-conv T≃ (T-Conv T≃′ _ d) =
      rsplit-app-not-unit-conv (≃-trans T≃′ T≃) d
    rsplit-app-not-unit-conv T≃ (T-Weaken _ d) = rsplit-app-not-unit-conv T≃ d
rsplit-app-not-unit (T-Weaken _ d) = rsplit-app-not-unit d

-- TP-Expr requires the thread body :: `T at I.  Combined with the above, the
-- empty-frame rsplit thread has NO TP-Expr typing in ANY context/struct.
rsplit-thread-not-typed :
  ∀ {m} {Γ : Ctx (suc m)} {γ}
  → ¬ ( Γ ; γ ⊢ₚ ⟪ K (`rsplit P.sP) · (` 0F) ⟫ )
rsplit-thread-not-typed d = rsplit-app-not-unit (inv-⟪⟫ d)
