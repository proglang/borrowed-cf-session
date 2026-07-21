-- | Backward simulation — the RU-Exp constructor of the `Base` residual,
--   restricted to the pure-congruence core ≋ of ≈.
--
--   `Base` (UpToPhiEngineWF) must reflect a non-administrative untyped step
--   against a process R ≈ U[ P ] σ.  Here we close the RU-Exp case with the
--   input narrowed from ≈ to ≋: `⟪ e₁ ⟫ ≋ U[ P ] σ`.  A single thread is
--   binder-free, so the νcount/φcount invariants force `U[ P ] σ` binder-free,
--   hence P is a ∥/⟪⟫-tree; the live-thread multiset then pins the redex to a
--   single source thread, which the strict reflector `bwd-exp` steps.
module BorrowedCF.Simulation.Backward.BaseExp where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR

open import BorrowedCF.Simulation.Backward.Leaf using (bwd-exp)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈; ≈-trans)
open import BorrowedCF.Simulation.Support.Normal.Form using (pars)
open import BorrowedCF.Simulation.Support.Normal.Invariant using (≋-νcount; ≋-φcount)
open import BorrowedCF.Simulation.Support.Normal.Flat
  using (Flat; fthr; fpar; flat?; threads; live; isUnit?;
         ≋-threads; pars-↭; pars-live1; ≋-sym)
open import BorrowedCF.Simulation.Support.Normal.Prenex using (pars-++)

open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭-length; ↭-singleton-inv)

open UP using (_≋_; ∥-cong; ∥-unitˡ; ∥-unitʳ)

------------------------------------------------------------------------
-- A stepping expression is not the spent `unit`, so its live-thread list
-- is a singleton.
------------------------------------------------------------------------

⋯→-live : ∀ {n} {e₁ e₂ : Tm n} → e₁ ⋯→ e₂ → live e₁ ≡ e₁ ∷ []
⋯→-live (E-□ (E-App _))              = refl
⋯→-live (E-□ (E-Seq _))              = refl
⋯→-live (E-□ (E-Let _))              = refl
⋯→-live (E-□ (E-PairElim _ _))       = refl
⋯→-live (E-□ (E-SumElim _))          = refl
⋯→-live (E-□ E-Unfold)               = refl
⋯→-live (E-Ctx (app₁ _ _ _) _)       = refl
⋯→-live (E-Ctx (app₂ _ _ _) _)       = refl
⋯→-live (E-Ctx (□⊗ _) _)             = refl
⋯→-live (E-Ctx (_ ⊗□) _)             = refl
⋯→-live (E-Ctx (□; _) _)          = refl
⋯→-live (E-Ctx (`let-`in _) _)       = refl
⋯→-live (E-Ctx (`let⊗-`in _) _)      = refl
⋯→-live (E-Ctx (`inj□ _) _)          = refl
⋯→-live (E-Ctx (`case□`of⟨ _ ; _ ⟩) _) = refl

------------------------------------------------------------------------
-- A binder-free process is ≋ to the parallel composition of its threads.
------------------------------------------------------------------------

flat-pars : ∀ {n} {R : UP.Proc n} → Flat R → R ≋ pars (threads R)
flat-pars (fthr {e})       = ≋-sym (pars-live1 e)
flat-pars (fpar {P} {Q} f g) =
  ∥-cong (flat-pars f) (flat-pars g) ◅◅ pars-++ (threads P) (threads Q)

------------------------------------------------------------------------
-- Splitting a singleton multiset across a ∥: exactly one side is live.
------------------------------------------------------------------------

splitThreads : ∀ {n} {a : Tm n} (xs ys : List (Tm n))
  → (a ∷ []) ↭ (xs ++ ys)
  → ((a ∷ []) ↭ xs × ys ≡ []) ⊎ (xs ≡ [] × (a ∷ []) ↭ ys)
splitThreads []       []       p with ↭-length p
... | ()
splitThreads []       (y ∷ ys) p = inj₂ (refl , p)
splitThreads {a = a} (x ∷ xs) []       p =
  inj₁ (subst ((a ∷ []) ↭_) (L.++-identityʳ (x ∷ xs)) p , refl)
splitThreads (x ∷ xs) (y ∷ ys) p
  with Nat.m+n≡0⇒n≡0 (L.length xs) (sym (suc⁻¹ (↭-length p ■ L.length-++ (x ∷ xs))))
... | ()

------------------------------------------------------------------------
-- Pinning a single-thread image: ⟪ a ⟫ ≋ ⟪ b ⟫ with `a` stepping forces b ≡ a.
------------------------------------------------------------------------

thread-pin : ∀ {n} {a b : Tm n} {a′} → UP.⟪ a ⟫ ≋ UP.⟪ b ⟫ → a ⋯→ a′ → b ≡ a
thread-pin {a = a} {b} c step with isUnit? b
... | inj₂ eqb =
      L.∷-injectiveˡ
        (sym eqb ■ ↭-singleton-inv
          (↭-sym (subst (_↭ live b) (⋯→-live step) (≋-threads fthr fthr c))))
... | inj₁ refl
      with ↭-length (subst (_↭ live (K `unit)) (⋯→-live step) (≋-threads fthr fthr c))
...   | ()

------------------------------------------------------------------------
-- Helpers for rebuilding the reverse codomain at a ∥.
------------------------------------------------------------------------

liftThread : ∀ {n} {Q : UP.Proc n} {a : Tm n} → Flat Q → (a ∷ []) ↭ threads Q → UP.⟪ a ⟫ ≋ Q
liftThread fQ perm = ≋-sym ∥-unitʳ ◅◅ pars-↭ perm ◅◅ ≋-sym (flat-pars fQ)

deadThread : ∀ {n} {Q : UP.Proc n} → Flat Q → threads Q ≡ [] → Q ≋ UP.⟪ K `unit ⟫
deadThread {Q = Q} fQ eq = subst (λ z → Q ≋ pars z) eq (flat-pars fQ)

R-Parʳ : ∀ {n} {A B C : TP.Proc n} → B TR.─→ₚ C → (A TP.∥ B) TR.─→ₚ (A TP.∥ C)
R-Parʳ s = TR.R-Struct TP.∥-comm (TR.R-Par s) TP.∥-comm

------------------------------------------------------------------------
-- The RU-Exp constructor of `Base`, restricted to the ≋ core.
------------------------------------------------------------------------

base-exp-≋ :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {e₁ e₂ : Tm n}
  → UP.⟪ e₁ ⟫ ≋ U[ P ] σ
  → e₁ ⋯→ e₂
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × UP.⟪ e₂ ⟫ ≈ U[ P′ ] σ)
base-exp-≋ σ Vσ Γ-S {P = TP.⟪ e₀ ⟫} ⊢P c step =
  bwd-exp σ Vσ Γ-S ⊢P (cong UP.⟪_⟫ (thread-pin c step)) step
base-exp-≋ σ Vσ Γ-S {P = P₁ TP.∥ P₂} ⊢P c step
  with TP.inv-∥ ⊢P
... | _ , _ , _ , ⊢P₁ , ⊢P₂
  with flat? (U[ P₁ TP.∥ P₂ ] σ) (sym (≋-νcount c)) (sym (≋-φcount c))
... | fpar f₁ f₂
  with splitThreads (threads (U[ P₁ ] σ)) (threads (U[ P₂ ] σ))
        (subst (_↭ (threads (U[ P₁ ] σ) ++ threads (U[ P₂ ] σ))) (⋯→-live step)
               (≋-threads fthr (fpar f₁ f₂) c))
... | inj₁ (permL , L2≡[]) =
      let P₁′ , star₁ , co = base-exp-≋ σ Vσ Γ-S {P = P₁} ⊢P₁ (liftThread f₁ permL) step
      in  P₁′ TP.∥ P₂
        , ⋆-gmap (TP._∥ P₂) (λ s → TR.R-Par {Q = P₂} s) star₁
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong ε (deadThread f₂ L2≡[]) ◅◅ ∥-unitʳ)))
... | inj₂ (L1≡[] , permR) =
      let P₂′ , star₂ , co = base-exp-≋ σ Vσ Γ-S {P = P₂} ⊢P₂ (liftThread f₂ permR) step
      in  P₁ TP.∥ P₂′
        , ⋆-gmap (P₁ TP.∥_) R-Parʳ star₂
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong (deadThread f₁ L1≡[]) ε ◅◅ ∥-unitˡ)))
base-exp-≋ σ Vσ Γ-S {P = TP.ν B₁ B₂ P₀} ⊢P c step with ≋-νcount c
... | ()
