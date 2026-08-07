-- | Backward simulation — the RU-Fork and RU-New constructors of the `Base`
--   residual, restricted to the pure-congruence core ≋ of ≈.
--
--   Same architecture as BaseExp (the RU-Exp case): a single thread is
--   binder-free, so the νcount/φcount invariants force `U[ P ] σ` binder-free,
--   hence P is a ∥/⟪⟫-tree; the live-thread multiset then pins the redex to a
--   single source thread, which the strict reflectors `bwd-fork` / `bwd-new`
--   step.  The flat-multiset helpers mirror BaseExp (re-proved locally rather
--   than imported, to keep the two case files independent).
module BorrowedCF.Simulation.Backward.BaseForkNew where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR

open import BorrowedCF.Simulation.Backward.Leaf using (bwd-fork; bwd-new)
open import BorrowedCF.Simulation.Forward.New using (tL)
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
-- A plugged application redex is never the spent `unit`, so its
-- live-thread list is a singleton.
------------------------------------------------------------------------

frame-live : ∀ {n} (E : Frame n) (t : Tm n) → live (E [ t ]) ≡ (E [ t ]) ∷ []
frame-live (app₁ e d V?)  t = refl
frame-live (app₂ e d V?)  t = refl
frame-live (□⊗ e₂)        t = refl
frame-live (V₁ ⊗□)        t = refl
frame-live (□; e₂)        t = refl
frame-live (`let-`in e′)  t = refl
frame-live (`let⊗-`in e′) t = refl
frame-live (`inj□ i)      t = refl
frame-live (`case□`of⟨ e₁ ; e₂ ⟩) t = refl

plug·-live : ∀ {n} (F : Frame* n) (a : Tm n) (d : Dir) (b : Tm n)
  → live (F [ a ·⟨ d ⟩ b ]*) ≡ (F [ a ·⟨ d ⟩ b ]*) ∷ []
plug·-live []      a d b = refl
plug·-live (E ∷ F) a d b = frame-live E (F [ a ·⟨ d ⟩ b ]*)

------------------------------------------------------------------------
-- Flat-multiset helpers, mirroring BaseExp.
------------------------------------------------------------------------

flat-pars : ∀ {n} {R : UP.Proc n} → Flat R → R ≋ pars (threads R)
flat-pars (fthr {e})       = ≋-sym (pars-live1 e)
flat-pars (fpar {P} {Q} f g) =
  ∥-cong (flat-pars f) (flat-pars g) ◅◅ pars-++ (threads P) (threads Q)

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

-- Pinning a single-thread image: ⟪ a ⟫ ≋ ⟪ b ⟫ with `a` live forces b ≡ a.
thread-pin : ∀ {n} {a b : Tm n} → live a ≡ a ∷ [] → UP.⟪ a ⟫ ≋ UP.⟪ b ⟫ → b ≡ a
thread-pin {a = a} {b} la c with isUnit? b
... | inj₂ eqb =
      L.∷-injectiveˡ
        (sym eqb ■ ↭-singleton-inv
          (↭-sym (subst (_↭ live b) la (≋-threads fthr fthr c))))
... | inj₁ refl
      with ↭-length (subst (_↭ live (K `unit)) la (≋-threads fthr fthr c))
...   | ()

liftThread : ∀ {n} {Q : UP.Proc n} {a : Tm n} → Flat Q → (a ∷ []) ↭ threads Q → UP.⟪ a ⟫ ≋ Q
liftThread fQ perm = ≋-sym ∥-unitʳ ◅◅ pars-↭ perm ◅◅ ≋-sym (flat-pars fQ)

deadThread : ∀ {n} {Q : UP.Proc n} → Flat Q → threads Q ≡ [] → Q ≋ UP.⟪ K `unit ⟫
deadThread {Q = Q} fQ eq = subst (λ z → Q ≋ pars z) eq (flat-pars fQ)

R-Parʳ : ∀ {n} {A B C : TP.Proc n} → B TR.─→ₚ C → (A TP.∥ B) TR.─→ₚ (A TP.∥ C)
R-Parʳ s = TR.R-Struct TP.∥-comm (TR.R-Par s) TP.∥-comm

------------------------------------------------------------------------
-- The RU-Fork constructor of `Base`, restricted to the ≋ core.
------------------------------------------------------------------------

base-fork-≋ :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {F : Frame* n} {e : Tm n} (V : Value e)
  → UP.⟪ F [ K `fork ·¹ e ]* ⟫ ≋ U[ P ] σ
  → Σ[ P′ ∈ TP.Proc m ]
      (Star TR._─→ₚ_ P P′ × (UP.⟪ F [ * ]* ⟫ UP.∥ UP.⟪ e ·¹ * ⟫) ≈ U[ P′ ] σ)
base-fork-≋ σ Vσ Γ-S {P = TP.⟪ e₀ ⟫} ⊢P {F = F} {e = e} V c =
  bwd-fork σ Vσ Γ-S ⊢P {F = F} V
    (cong UP.⟪_⟫ (thread-pin (plug·-live F (K `fork) 𝟙 e) c))
base-fork-≋ σ Vσ Γ-S {P = P₁ TP.∥ P₂} ⊢P {F = F} {e = e} V c
  with TP.inv-∥ ⊢P
... | _ , _ , _ , ⊢P₁ , ⊢P₂
  with flat? (U[ P₁ TP.∥ P₂ ] σ) (sym (≋-νcount c)) (sym (≋-φcount c))
... | fpar f₁ f₂
  with splitThreads (threads (U[ P₁ ] σ)) (threads (U[ P₂ ] σ))
        (subst (_↭ (threads (U[ P₁ ] σ) ++ threads (U[ P₂ ] σ)))
               (plug·-live F (K `fork) 𝟙 e)
               (≋-threads fthr (fpar f₁ f₂) c))
... | inj₁ (permL , L2≡[]) =
      let P₁′ , star₁ , co = base-fork-≋ σ Vσ Γ-S {P = P₁} ⊢P₁ {F = F} V (liftThread f₁ permL)
      in  P₁′ TP.∥ P₂
        , ⋆-gmap (TP._∥ P₂) (λ s → TR.R-Par {Q = P₂} s) star₁
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong ε (deadThread f₂ L2≡[]) ◅◅ ∥-unitʳ)))
... | inj₂ (L1≡[] , permR) =
      let P₂′ , star₂ , co = base-fork-≋ σ Vσ Γ-S {P = P₂} ⊢P₂ {F = F} V (liftThread f₂ permR)
      in  P₁ TP.∥ P₂′
        , ⋆-gmap (P₁ TP.∥_) R-Parʳ star₂
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong (deadThread f₁ L1≡[]) ε ◅◅ ∥-unitˡ)))
base-fork-≋ σ Vσ Γ-S {P = TP.ν B₁ B₂ P₀} ⊢P V c with ≋-νcount c
... | ()

------------------------------------------------------------------------
-- The RU-New constructor of `Base`, restricted to the ≋ core.
------------------------------------------------------------------------

base-new-≋ :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {s : 𝕊 0} {F : Frame* n}
  → UP.⟪ F [ K (`new s) ·¹ * ]* ⟫ ≋ U[ P ] σ
  → Σ[ P′ ∈ TP.Proc m ]
      (Star TR._─→ₚ_ P P′ ×
       UP.ν (UP.φ UP.acq (` 0F) (UP.φ UP.acq (` 2F) UP.⟪
          (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫))
         ≈ U[ P′ ] σ)
base-new-≋ σ Vσ Γ-S {P = TP.⟪ e₀ ⟫} ⊢P {s = s} {F = F} c =
  bwd-new σ Vσ Γ-S ⊢P {s = s} {F = F}
    (cong UP.⟪_⟫ (thread-pin (plug·-live F (K (`new s)) 𝟙 *) c))
base-new-≋ σ Vσ Γ-S {P = P₁ TP.∥ P₂} ⊢P {s = s} {F = F} c
  with TP.inv-∥ ⊢P
... | _ , _ , _ , ⊢P₁ , ⊢P₂
  with flat? (U[ P₁ TP.∥ P₂ ] σ) (sym (≋-νcount c)) (sym (≋-φcount c))
... | fpar f₁ f₂
  with splitThreads (threads (U[ P₁ ] σ)) (threads (U[ P₂ ] σ))
        (subst (_↭ (threads (U[ P₁ ] σ) ++ threads (U[ P₂ ] σ)))
               (plug·-live F (K (`new s)) 𝟙 *)
               (≋-threads fthr (fpar f₁ f₂) c))
... | inj₁ (permL , L2≡[]) =
      let P₁′ , star₁ , co = base-new-≋ σ Vσ Γ-S {P = P₁} ⊢P₁ {s = s} {F = F} (liftThread f₁ permL)
      in  P₁′ TP.∥ P₂
        , ⋆-gmap (TP._∥ P₂) (λ s → TR.R-Par {Q = P₂} s) star₁
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong ε (deadThread f₂ L2≡[]) ◅◅ ∥-unitʳ)))
... | inj₂ (L1≡[] , permR) =
      let P₂′ , star₂ , co = base-new-≋ σ Vσ Γ-S {P = P₂} ⊢P₂ {s = s} {F = F} (liftThread f₂ permR)
      in  P₁ TP.∥ P₂′
        , ⋆-gmap (P₁ TP.∥_) R-Parʳ star₂
        , ≈-trans co (≋⇒≈ (≋-sym (∥-cong (deadThread f₁ L1≡[]) ε ◅◅ ∥-unitˡ)))
base-new-≋ σ Vσ Γ-S {P = TP.ν B₁ B₂ P₀} ⊢P c with ≋-νcount c
... | ()
