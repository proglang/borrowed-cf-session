-- | drop-goB : the good-shape core of the reverse RU-Drop reflection.  Assembles
--   the proven pieces: invert to good shape → drop-front-force (b₁≡0) →
--   drop-confine (weakenᵣ factoring) → R-Drop → flag-flip recon (drop-bodyeq0 +
--   drop-collapse).  Mirrors acq-goB.
module BorrowedCF.Simulation.Backward.DropReflect where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; close-arg-var; frameApp-reflect)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋; U-cong; U-⋯ₚ)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Backward.Drop
  using (νσᵈ; νσᵈ-VSub; drop-arg-decomp; drop-bodyeq; drop-image)
open import BorrowedCF.Simulation.Backward.DropGo using (drop-front-force)
open import BorrowedCF.Simulation.Backward.DropConfine using (drop-confine)
open import BorrowedCF.Simulation.Backward.DropGoB using (νσᵈ⁰; drop-bodyeq0)
open import BorrowedCF.Simulation.Backward.DropConfine using () renaming ()
open import BorrowedCF.Simulation.Backward.DropCollapse using (drop-collapse)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (frame*-cong; F-⋯f*-fuse; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.Backward.Drop using () renaming ()
open import BorrowedCF.Reduction.Base using (ChanCx; chanCx-⸴*; Frame*; _[_]*; _⋯ᶠ*_; ⊢[]*⁻¹)
open import BorrowedCF.Context using (Ctx; Struct)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open import Data.Product using (proj₁; proj₂; _,_; Σ-syntax; _×_)
open TP using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx; _⋯ₚ_)

open Fin.Patterns
pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

private
  φ-inj : ∀ {k} {f g : UP.Flag} {X Y : UP.Proc (suc k)} → UP.φ f X ≡ UP.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-inj refl = refl , refl
  ν-injU : ∀ {k} {X Y : UP.Proc (2 + k)} → UP.ν X ≡ UP.ν Y → X ≡ Y
  ν-injU refl = refl
  inv-U-∥ : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) {A B : UP.Proc n}
          → U[ P ] σ ≡ A UP.∥ B
          → Σ[ P₁ ∈ TP.Proc m ] Σ[ P₂ ∈ TP.Proc m ] (P ≡ P₁ TP.∥ P₂ × A ≡ U[ P₁ ] σ × B ≡ U[ P₂ ] σ)
  inv-U-∥ (TP.⟪ e₀ ⟫)    σ ()
  inv-U-∥ (P TP.∥ Q)     σ refl = P , Q , refl , refl , refl
  inv-U-∥ (TP.ν B₁ B₂ P) σ ()
  inv-U-⟪⟫ : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) {e : Tm n}
           → U[ P ] σ ≡ UP.⟪ e ⟫ → Σ[ e₀ ∈ Tm m ] (P ≡ TP.⟪ e₀ ⟫ × e ≡ e₀ ⋯ σ)
  inv-U-⟪⟫ (TP.⟪ e₀ ⟫)    σ refl = e₀ , refl , refl
  inv-U-⟪⟫ (P TP.∥ Q)     σ ()
  inv-U-⟪⟫ (TP.ν B₁ B₂ P) σ ()

-- good-shape core: B₁ = suc b₁ ∷ c ∷ [] (φ drop head), B₂ = b₂ ∷ [].
drop-goB-good :
  ∀ {m n} (b₁ c b₂ : ℕ) (σ : m →ₛ n) (Vσ : VSub σ)
    (σᵈ : (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m) →ₛ (3 + n))
    (σᵈ≡ : σᵈ ≡ νσᵈ b₁ c b₂ σ)
    {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (P₀ : TP.Proc (sum (suc b₁ ∷ c ∷ []) + sum (b₂ ∷ []) + m))
    (F : Frame* (3 + n)) {x : 𝔽 (2 + n)} {P₁ : UP.Proc (3 + n)}
  → Γ ; g ⊢ₚ TP.ν (suc b₁ ∷ c ∷ []) (b₂ ∷ []) P₀
  → UP.ν (UP.φ UP.drop (UP.⟪ F [ K `drop ·¹ 𝓒[ * × Fin.suc x × ` 0F ] ]* ⟫ UP.∥ P₁))
      ≡ U[ TP.ν (suc b₁ ∷ c ∷ []) (b₂ ∷ []) P₀ ] σ
  → Σ[ P′ ∈ TP.Proc m ]
      Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ c ∷ []) (b₂ ∷ []) P₀) P′
      × (UP.ν (UP.φ UP.acq (UP.⟪ F [ * ]* ⟫ UP.∥ P₁)) ≈ U[ P′ ] σ)
drop-goB-good b₁ c b₂ σ Vσ σᵈ σᵈ≡ Γ-S P₀ F {x} {P₁} ⊢P bodyeq
  with Γ₁ , Γ₂ , s' , p' , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with leafeq ← proj₂ (φ-inj (ν-injU bodyeq))
  with PL , Pr , refl , Leq , Preq ← inv-U-∥ P₀ σᵈ (sym (leafeq ■ cong (U[ P₀ ]) (sym σᵈ≡)))
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL σᵈ (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢Pr ← inv-∥ ⊢body
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) σᵈ (subst VSub (sym σᵈ≡) (νσᵈ-VSub b₁ c b₂ σ Vσ)) `drop F (sym Leq′)
  with 𝒫 , γr , _ , _ , _ , _ , ≼F , _ , _ , ⊢F , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `drop ·¹ arg₀) (inv-⟪⟫ ⊢PL)
  with β′ , Rt , ϵ′ , ret≃ , ⊢argty ← drop-arg-decomp ⊢redex
  with xx , refl ← close-arg-var arg₀ ⊢argty ret≃ σᵈ (sym argeq)
  with refl ← drop-front-force σ Vσ Γ-S b₁ c b₂ σᵈ σᵈ≡ {F₀ = F₀} {arg = ` xx} {P₀ᵣ = Pr} {a = *} {xd = x} ⊢P argeq
  with refl ← drop-image 0 c b₂ σ Vσ xx (argeq ■ cong (λ f → f xx) σᵈ≡)
  with refl ← σᵈ≡
  with E , Eeq , Pp , Peq ← drop-confine c b₂ Γ-S {F₀ = F₀} {P₀ᵣ = Pr} ⊢P
  = TP.ν (0 ∷ c ∷ []) (b₂ ∷ []) (TP.⟪ E [ * ]* ⟫ TP.∥ Pp)
  , subst₂ (λ f p → Star TR._─→ₚ_ (TP.ν (1 ∷ c ∷ []) (b₂ ∷ [])
              (TP.⟪ f [ K `drop ·¹ (` 0F) ]* ⟫ TP.∥ p))
              (TP.ν (0 ∷ c ∷ []) (b₂ ∷ []) (TP.⟪ E [ * ]* ⟫ TP.∥ Pp)))
           (sym Eeq) (sym Peq)
           (TR.R-Drop {b₁ = 0} {B₁ = c ∷ []} {B₂ = b₂ ∷ []} {P = Pp} {E = E} ◅ ε)
  , ≋⇒≈ (≡→≋ recon-eq)
  where
    ν0 = νσᵈ 0 c b₂ σ
    Vν0 = νσᵈ-VSub 0 c b₂ σ Vσ
    Vwν0 = ·ₖ-VSubᵣ weakenᵣ Vν0
    Vd0 : VSub (νσᵈ⁰ c b₂ σ)
    Vd0 i = subst Value (sym (drop-collapse c b₂ σ i)) (Vν0 (Fin.suc i))
    wν0≗d0 : (weakenᵣ ·ₖ ν0) ≗ νσᵈ⁰ c b₂ σ
    wν0≗d0 i = sym (drop-collapse c b₂ σ i)
    threadEq : F ≡ frame*-⋯ E (νσᵈ⁰ c b₂ σ) Vd0
    threadEq = Feq
             ■ cong (λ X → frame*-⋯ X ν0 Vν0) Eeq
             ■ F-⋯f*-fuse E Vν0 Vwν0
             ■ frame*-cong E Vwν0 Vd0 wν0≗d0
    restEq : P₁ ≡ U[ Pp ] (νσᵈ⁰ c b₂ σ)
    restEq = Preq
           ■ cong (λ X → U[ X ] ν0) Peq
           ■ U-⋯ₚ Pp
           ■ U-cong Pp wν0≗d0
    recon-eq : UP.ν (UP.φ UP.acq (UP.⟪ F [ * ]* ⟫ UP.∥ P₁))
             ≡ U[ TP.ν (0 ∷ c ∷ []) (b₂ ∷ []) (TP.⟪ E [ * ]* ⟫ TP.∥ Pp) ] σ
    recon-eq = cong (λ Z → UP.ν (UP.φ UP.acq Z))
                 (cong₂ UP._∥_
                   (cong UP.⟪_⟫ (cong (_[ * ]*) threadEq ■ sym (frame-plug* E (νσᵈ⁰ c b₂ σ) Vd0)))
                   restEq)
             ■ sym (drop-bodyeq0 c b₂ σ (TP.⟪ E [ * ]* ⟫ TP.∥ Pp))
