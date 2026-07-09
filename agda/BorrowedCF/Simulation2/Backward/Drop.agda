-- | Backward simulation, RU-Drop.  Reflects one untyped φ-drop step back to a
--   typed R-Drop step in the CLEAN single-step codomain.
--
--   Unlike RU-Acquire (ν-headed, dispatched at the top level of sim←ᵍ), the
--   untyped RU-Drop is φ-HEADED, so it only fires under an RU-Res peel — i.e.
--   inside simRes's φ-bearing case (Backward.agda ?1, syncs B₁ ≥ 1).  The redex
--   thread is  ⟪ F [ K drop · 𝓒[ * × suc x × ` 0F ] ]* ⟫,  and the drop flips the
--   head sync cell drop → acq.
--
--   The reflection is only well-posed when the typed head bind block has WIDTH 1
--   (b₁ ≡ 0): #acq is a strict ≈-invariant (Backward.DropNotAdmin), a genuine
--   φ-drop increments #acq by one, and the typed R-Drop reduct  ν (b₁ ∷ B₁) B₂ …
--   carries a head-φ flag  ϕ[ b₁ ]  which equals the untyped `acq only when
--   b₁ ≡ 0.  The width-1 forcing is the impurity front-confinement (drop is 𝕀,
--   Terms.agda:162): the active drop redex sits at the FRONT handle 0F of the
--   head block, and the image geometry pins the drop cell (right slot ` 0F) to
--   the block's LAST entry — front = last ⇒ width 1.
module BorrowedCF.Simulation2.Backward.Drop where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Processes.Bisim using (Ub[_])
open import BorrowedCF.Simulation.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; close-arg-var; head⊗′; U-ν-singleton; frameApp-reflect;
         frame-fusion-gen; frame-cong)
open import BorrowedCF.Simulation.RevUCong using (U-not-φ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋; U-cong; Ub-V)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Theorems.SplitsH2 using (frame*-cong)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx; chanCx-⸴*)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Base using (NonZero)
open TP using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)
open import Data.List.Relation.Unary.All as All using (All)

open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- Head-inversion lemmas (local copies; Reverse.agda imports this module).
------------------------------------------------------------------------

private
  inv-U-⟪⟫ : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) {e : Tm n}
           → U[ P ] σ ≡ UP.⟪ e ⟫
           → Σ[ e₀ ∈ Tm m ] (P ≡ TP.⟪ e₀ ⟫ × e ≡ e₀ ⋯ σ)
  inv-U-⟪⟫ (TP.⟪ e₀ ⟫)    σ refl = e₀ , refl , refl
  inv-U-⟪⟫ (P TP.∥ Q)     σ ()
  inv-U-⟪⟫ (TP.ν B₁ B₂ P) σ ()

  inv-U-∥ : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) {A B : UP.Proc n}
          → U[ P ] σ ≡ A UP.∥ B
          → Σ[ P₁ ∈ TP.Proc m ] Σ[ P₂ ∈ TP.Proc m ]
              (P ≡ P₁ TP.∥ P₂ × A ≡ U[ P₁ ] σ × B ≡ U[ P₂ ] σ)
  inv-U-∥ (TP.⟪ e₀ ⟫)    σ ()
  inv-U-∥ (P TP.∥ Q)     σ refl = P , Q , refl , refl , refl
  inv-U-∥ (TP.ν B₁ B₂ P) σ ()

  inv-U-ν : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) {X : UP.Proc (2 + n)}
          → UP.ν X ≡ U[ P ] σ
          → Σ[ B₁ ∈ TP.BindGroup ] Σ[ B₂ ∈ TP.BindGroup ]
              Σ[ P₀ ∈ TP.Proc (sum B₁ + sum B₂ + m) ]
              (P ≡ TP.ν B₁ B₂ P₀ × UP.ν X ≡ U[ TP.ν B₁ B₂ P₀ ] σ)
  inv-U-ν (TP.⟪ e₀ ⟫)    σ ()
  inv-U-ν (P TP.∥ Q)     σ ()
  inv-U-ν (TP.ν B₁ B₂ P) σ eq = B₁ , B₂ , P , refl , eq

  φ-inj : ∀ {k} {f g : UP.Flag} {X Y : UP.Proc (suc k)} →
          UP.φ f X ≡ UP.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-inj refl = refl , refl

  ν-injU : ∀ {k} {X Y : UP.Proc (2 + k)} → UP.ν X ≡ UP.ν Y → X ≡ Y
  ν-injU refl = refl

  ∥-injU : ∀ {k} {A B C D : UP.Proc k} → (A UP.∥ B) ≡ (C UP.∥ D) → (A ≡ C) × (B ≡ D)
  ∥-injU refl = refl , refl

------------------------------------------------------------------------
-- drop typing extractors.
------------------------------------------------------------------------

fn-drop-dom : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu a ϵ}
  → Γ ; α ⊢ K `drop ∶ T ⟨ a ⟩→ Uu ∣ ϵ
  → ⟨ ret ⟩ ≃ T
fn-drop-dom (T-Const `drop) = ≃-refl
fn-drop-dom (T-Conv (dom≃ `→ _) _ d) = ≃-trans (fn-drop-dom d) dom≃
fn-drop-dom (T-Weaken _ d) = fn-drop-dom d

drop-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `drop ·¹ arg ∶ Uu ∣ ϵ
  → Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ ret ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
drop-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = _ , _ , _ , fn-drop-dom ⊢fn , ⊢arg
drop-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = _ , _ , _ , fn-drop-dom ⊢fn , ⊢arg
drop-arg-decomp (T-Conv _ _ d) = drop-arg-decomp d
drop-arg-decomp (T-Weaken _ d) = drop-arg-decomp d

------------------------------------------------------------------------
-- νσᵈ : the φ-body substitution for the drop good shape
--   B₁ = suc b₁ ∷ c ∷ [] , B₂ = b₂ ∷ [] .  The 2-block first group is exactly
--   what makes the image head with φ; U[_] of this good shape peels to
--   ν (φ drop (U[ body ] (νσᵈ …))) by refl.
------------------------------------------------------------------------

νσᵈ : ∀ {m n} (b₁ c b₂ : ℕ) (σ : m →ₛ n)
    → (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m) →ₛ (3 + n)
νσᵈ b₁ c b₂ σ =
  ((λ x → ([ Ub[ suc b₁ ] (wk * , 1F , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ 0
            , Ub[ c + 0 ] (` 0F , 1F , wk *) ]′ (Fin.splitAt (suc b₁) x))
            ⋯ weaken* ⦃ Kᵣ ⦄ 0)
    ++ₛ Ub[ b₂ + 0 ] (* , 2F , *))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0)

drop-bodyeq : ∀ {m n} (b₁ c b₂ : ℕ) (σ : m →ₛ n)
              (P₀ : TP.Proc (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m))
            → U[ TP.ν (suc b₁ ∷ c ∷ []) (b₂ ∷ []) P₀ ] σ
              ≡ UP.ν (UP.φ UP.drop (U[ P₀ ] (νσᵈ b₁ c b₂ σ)))
drop-bodyeq b₁ c b₂ σ P₀ = refl

νσᵈ-VSub : ∀ {m n} (b₁ c b₂ : ℕ) (σ : m →ₛ n) → VSub σ → VSub (νσᵈ b₁ c b₂ σ)
νσᵈ-VSub {m} {n} b₁ c b₂ σ Vσ i with Fin.splitAt (sum (suc b₁ ∷ c ∷ []) + (b₂ + 0)) i
... | Sum.inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
... | Sum.inj₁ d with Fin.splitAt (sum (suc b₁ ∷ c ∷ [])) d
...   | Sum.inj₂ w = Ub-V (b₂ + 0) * 2F * V-K V-K w
...   | Sum.inj₁ e = value-⋯ (inner e) (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
  where
    inner : (e : 𝔽 (sum (suc b₁ ∷ c ∷ []))) →
            Value ([ Ub[ suc b₁ ] (wk * , 1F , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ 0
                   , Ub[ c + 0 ] (` 0F , 1F , wk *) ]′ (Fin.splitAt (suc b₁) e))
    inner e with Fin.splitAt (suc b₁) e
    ... | Sum.inj₁ v = value-⋯ (Ub-V (suc b₁) (wk *) 1F (` 0F) V-K V-` v)
                         (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
    ... | Sum.inj₂ w′ = Ub-V (c + 0) (` 0F) 1F (wk *) V-` V-K w′

------------------------------------------------------------------------
-- Ub[_] right-slot keying.  The drop handle's distinguishing feature is the
-- RIGHT slot ` 0F (unlike com, which keys on the middle channel).  Ub[_]'s
-- recursion places the block's e₂ ONLY at the last index; every earlier index
-- has right slot *.
------------------------------------------------------------------------

-- A block whose e₂ is * never yields a chanTriple with right slot ` 0F.
Ub-e₂*-noRight0F : ∀ {N} b (e₁ : Tm (suc N)) (c : 𝔽 (suc N)) (v : 𝔽 (suc b)) {a} {d : 𝔽 (suc N)}
  → Ub[ suc b ] (e₁ , c , *) v ≡ 𝓒[ a × d × ` 0F ] → ⊥
Ub-e₂*-noRight0F zero     e₁ c 0F          eq = case proj₂ (⊗-inj eq) of λ ()
Ub-e₂*-noRight0F (suc b') e₁ c 0F          eq = case proj₂ (⊗-inj eq) of λ ()
Ub-e₂*-noRight0F (suc b') e₁ c (Fin.suc v) eq = Ub-e₂*-noRight0F b' * c v eq

-- The head block (e₂ = ` 0F): a right-slot ` 0F pins v to the LAST index fromℕ b.
Ub-right0F⇒last : ∀ {N} b (e₁ : Tm (suc N)) (c : 𝔽 (suc N)) (v : 𝔽 (suc b)) {a} {d : 𝔽 (suc N)}
  → Ub[ suc b ] (e₁ , c , ` 0F) v ≡ 𝓒[ a × d × ` 0F ]
  → v ≡ Fin.fromℕ b
Ub-right0F⇒last zero     e₁ c 0F          eq = refl
Ub-right0F⇒last (suc b') e₁ c 0F          eq = case proj₂ (⊗-inj eq) of λ ()
Ub-right0F⇒last (suc b') e₁ c (Fin.suc v) eq = cong Fin.suc (Ub-right0F⇒last b' * c v eq)

------------------------------------------------------------------------
-- νσᵈ σ-region refuters.  The σ-region maps each σ-value through
-- weaken 2 ⋯ weaken 1 ⋯ weaken 0, pushing all its variables above 0F, so it
-- can never be a chanTriple with right slot ` 0F.
------------------------------------------------------------------------

shiftᵈ : ∀ {n} → Tm n → Tm (3 + n)
shiftᵈ t = t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0

σregᵈ-var : ∀ {n} {t : Tm n} → Value t → shiftᵈ t ≡ ` 0F → ⊥
σregᵈ-var V-`       ()
σregᵈ-var V-K       ()
σregᵈ-var V-λ       ()
σregᵈ-var (V-⊗ _ _) ()
σregᵈ-var (V-⊕ _)   ()

σregᵈ-pair : ∀ {n} {t : Tm n} → Value t → ∀ {a : Tm (3 + n)} → shiftᵈ t ≡ a ⊗ (` 0F) → ⊥
σregᵈ-pair V-`       ()
σregᵈ-pair V-K       ()
σregᵈ-pair V-λ       ()
σregᵈ-pair (V-⊕ _)   ()
σregᵈ-pair (V-⊗ V₁ V₂) eq = σregᵈ-var V₂ (proj₂ (⊗-inj eq))
