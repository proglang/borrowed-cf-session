-- | Backward simulation, RU-LSplit probe — the BOUNDARY of the pinning
--   composite.
--
--   PinBase's Stage-1 composite renaming has three legs:
--
--       ρ  =  wkTel (tel (nf P₁))  ·ₖ  ρC  ·ₖ  fwd w
--
--   (the redex ν-body's own telescope weakening, the `ctx-thread` leg through
--   the one-hole context, and the witness leg into the image's block form).
--   This module proves each leg maps NON-ambient variables to NON-ambient
--   variables, and composes the three into the single side condition the
--   σ-escape refutation (PinAmb.σ-escape-refute) needs:
--
--       ∀ z → ρ 0F ≢ wkTel (BTel (tel (prenexᵗ P)) n) z
--
--   — the variable bound by the redex's own ν never lands in the ambient
--   (`wkTel`) range of the image block telescope.  The ctx-thread legs are
--   `liftRen`/`renTel`/`wkTel` composites, separated from the ambient range by
--   injectivity (`wk*-inj`); the witness leg is `WitnessAmb.bound-pres` for the
--   AmbWitness built from the SAME `≋`/`image-block-~` chain `image-pin` uses.
--
--   Exports the strengthened Stage-1 pinning (`pin-lsplit-redex-bound`):
--   PinBase's `pin-lsplit-redex` plus the boundary fact, consumed by
--   Backward.PinLSplit to close the AMBIENT case of `pin-lsplit-fire`.
module BorrowedCF.Simulation.Backward.PinBound where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (𝕊; 𝟙)
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Processes.Translation using (U[_])
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Simulation.Support.StepDecomp
  using (Ctx*; ∘ᴷ; _∥ᴷ_; _ᴷ∥_; νᴷ; φᴷ; _[_]ᴷ)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen)
open import BorrowedCF.Simulation.Support.Normal.Endo using (wkTel-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Flat using (live)
open import BorrowedCF.Simulation.Support.Normal.Witness using (fwd; thrs)
open import BorrowedCF.Simulation.Support.Normal.WitnessAmb
  using (AmbWitness; w; bound-pres; ambwitness-trans; ~-ambwitness; ≋-ambwitness)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BScope; BTel; Bσ; image-block-~)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Backward.BaseForkNew using (plug·-live)
open import BorrowedCF.Simulation.Backward.PinBase
  using (live-ren; ∈-live*; live*-∈⁻; unit-dead)

import BorrowedCF.Processes.Typed as 𝐓

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (∈-resp-↭)
open import Data.Product using (Σ-syntax; _×_; _,_)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Separating a lifted renaming from a weakening, on names.
------------------------------------------------------------------------

-- A lifted renaming hits the weakening range only from the weakening range.
↑*-wk⁻ : ∀ m {a b} (ξ : a →ᵣ b) (x : 𝔽 (m + a)) (v : 𝔽 b) →
         (ξ ↑* m) x ≡ weaken* ⦃ Kᵣ ⦄ m v →
         Σ[ y ∈ 𝔽 a ] ((x ≡ weaken* ⦃ Kᵣ ⦄ m y) × (ξ y ≡ v))
↑*-wk⁻ zero    ξ x       v eq = x , refl , eq
↑*-wk⁻ (suc m) ξ 0F      v ()
↑*-wk⁻ (suc m) ξ (suc x) v eq
  with y , xeq , veq ← ↑*-wk⁻ m ξ x v (Fin.suc-injective eq)
  = y , cong suc xeq , veq

-- A telescope's weakening is injective.
wkTel-inj : ∀ {a b} (t : Tel a b) {x y : 𝔽 a} → wkTel t x ≡ wkTel t y → x ≡ y
wkTel-inj []       eq = eq
wkTel-inj (tν t)   eq = wk*-inj 2 (wkTel-inj t eq)
wkTel-inj (tφ f t) eq = wk*-inj 1 (wkTel-inj t eq)

-- `liftRen` hits the rebased telescope's ambient range only ambiently.
liftRen-wkTel⁻ : ∀ {a b n′} (t : Tel a b) (ξ : a →ᵣ n′) (x : 𝔽 b) (v : 𝔽 n′) →
                 liftRen t ξ x ≡ wkTel (renTel t n′) v →
                 Σ[ y ∈ 𝔽 a ] ((x ≡ wkTel t y) × (ξ y ≡ v))
liftRen-wkTel⁻ []       ξ x v eq = x , refl , eq
liftRen-wkTel⁻ (tν t)   ξ x v eq
  with y′ , xeq , veq ← liftRen-wkTel⁻ t (ξ ↑* 2) x (weaken* ⦃ Kᵣ ⦄ 2 v) eq
  with y  , y′eq , ξeq ← ↑*-wk⁻ 2 ξ y′ v veq
  = y , (xeq ■ cong (wkTel t) y′eq) , ξeq
liftRen-wkTel⁻ (tφ f t) ξ x v eq
  with y′ , xeq , veq ← liftRen-wkTel⁻ t (ξ ↑) x (weaken* ⦃ Kᵣ ⦄ 1 v) eq
  with y  , y′eq , ξeq ← ↑*-wk⁻ 1 ξ y′ v veq
  = y , (xeq ■ cong (wkTel t) y′eq) , ξeq

------------------------------------------------------------------------
-- The two `combine` legs preserve non-ambience.
------------------------------------------------------------------------

combineˡ-∉ : ∀ {a j₁ j₂} (t₁ : Tel a j₁) (t₂ : Tel a j₂) {x : 𝔽 j₁} →
             (∀ y → x ≢ wkTel t₁ y) →
             ∀ z → liftRen t₁ (wkTel t₂) x ≢ wkTel (t₂ ++ᵗ renTel t₁ j₂) z
combineˡ-∉ {j₂ = j₂} t₁ t₂ {x} nb z eq
  with y , xeq , _ ← liftRen-wkTel⁻ t₁ (wkTel t₂) x (wkTel t₂ z)
        (eq ■ wkTel-++ᵗ t₂ (renTel t₁ j₂) z)
  = nb y xeq

combineʳ-∉ : ∀ {a j₁ j₂} (t₁ : Tel a j₁) (t₂ : Tel a j₂) {x : 𝔽 j₂} →
             (∀ y → x ≢ wkTel t₂ y) →
             ∀ z → wkTel (renTel t₁ j₂) x ≢ wkTel (t₂ ++ᵗ renTel t₁ j₂) z
combineʳ-∉ {j₂ = j₂} t₁ t₂ nb z eq =
  nb z (wkTel-inj (renTel t₁ j₂) (eq ■ wkTel-++ᵗ t₂ (renTel t₁ j₂) z))

------------------------------------------------------------------------
-- The ctx-thread leg, boundary-enriched.
------------------------------------------------------------------------

ctx-thread-bound :
  ∀ {n k} (C : Ctx* n k) (X : Proc k) {e : Tm (inner (nf X))} →
  e ∈ thr (nf X) →
  Σ[ ρ ∈ (inner (nf X) →ᵣ inner (nf (C [ X ]ᴷ))) ]
    (((e ⋯ ρ) ∈ thr (nf (C [ X ]ᴷ)))
     × (∀ {x} → (∀ y → x ≢ wkTel (tel (nf X)) y)
              → ∀ z → ρ x ≢ wkTel (tel (nf (C [ X ]ᴷ))) z))
ctx-thread-bound ∘ᴷ X {e} m =
  idₖ , subst (_∈ thr (nf X)) (sym (⋯-id e (λ _ → refl))) m , (λ nb → nb)
ctx-thread-bound (C ∥ᴷ Q) X {e} m
  with ρ₀ , m₀ , b₀ ← ctx-thread-bound C X m =
  let lft = liftRen (tel (nf (C [ X ]ᴷ))) (wkTel (tel (nf Q))) in
    (ρ₀ ·ₖ lft)
  , subst (_∈ thr (nf ((C [ X ]ᴷ) ∥ Q))) (fusion e ρ₀ lft)
      (∈-++⁺ˡ (∈-map⁺ (_⋯ lft) m₀))
  , (λ nb → combineˡ-∉ (tel (nf (C [ X ]ᴷ))) (tel (nf Q)) (b₀ nb))
ctx-thread-bound (P ᴷ∥ C) X {e} m
  with ρ₀ , m₀ , b₀ ← ctx-thread-bound C X m =
  let ρʳ = wkTel (renTel (tel (nf P)) (inner (nf (C [ X ]ᴷ)))) in
    (ρ₀ ·ₖ ρʳ)
  , subst (_∈ thr (nf (P ∥ (C [ X ]ᴷ)))) (fusion e ρ₀ ρʳ)
      (∈-++⁺ʳ (map (_⋯ liftRen (tel (nf P)) (wkTel (tel (nf (C [ X ]ᴷ))))) (thr (nf P)))
              (∈-map⁺ (_⋯ ρʳ) m₀))
  , (λ nb → combineʳ-∉ (tel (nf P)) (tel (nf (C [ X ]ᴷ))) (b₀ nb))
ctx-thread-bound (νᴷ C)   X m
  with ρ₀ , m₀ , b₀ ← ctx-thread-bound C X m
  = ρ₀ , m₀ , (λ nb z → b₀ nb (weaken* ⦃ Kᵣ ⦄ 2 z))
ctx-thread-bound (φᴷ f C) X m
  with ρ₀ , m₀ , b₀ ← ctx-thread-bound C X m
  = ρ₀ , m₀ , (λ nb z → b₀ nb (weaken* ⦃ Kᵣ ⦄ 1 z))

------------------------------------------------------------------------
-- The witness leg, via the AmbWitness of the same chain.
------------------------------------------------------------------------

image-pin-bound :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n) {Rt : Proc n} (c : Rt ≋ U[ P ] σ)
    {e : Tm (inner (nf Rt))} → e ∈ thr (nf Rt) → live e ≡ e ∷ [] →
  Σ[ ρ ∈ (inner (nf Rt) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P)) × (e† ⋯ Bσ (tel (prenexᵗ P)) σ ≡ e ⋯ ρ)
     × (∀ {x} → (∀ y → x ≢ wkTel (tel (nf Rt)) y)
              → ∀ z → ρ x ≢ wkTel (BTel (tel (prenexᵗ P)) n) z))
image-pin-bound {m} {n} P σ {Rt} c {e} mem le
  with aw ← ambwitness-trans (≋-ambwitness c) (~-ambwitness (image-block-~ P σ))
  with m₂ ← live*-∈⁻ _ (∈-resp-↭ (thrs (w aw))
              (∈-live* (∈-map⁺ (_⋯ fwd (w aw)) mem) (live-ren (fwd (w aw)) le)))
  with ∈-++⁻ (map (_⋯ Bσ (tel (prenexᵗ P)) σ) (thr (prenexᵗ P))) m₂
... | inj₂ (here q)   = ⊥-elim (unit-dead q (live-ren (fwd (w aw)) le))
... | inj₂ (there ())
... | inj₁ mm
  with e† , m† , qq ← ∈-map⁻ (_⋯ Bσ (tel (prenexᵗ P)) σ) mm
  = fwd (w aw) , e† , m† , sym qq , bound-pres aw

------------------------------------------------------------------------
-- The redex's own ν leg: its bound name is not ambient in the ν-body's NF.
------------------------------------------------------------------------

ν-head-∉ : ∀ {a b} (t : Tel (2 + a) b) (y : 𝔽 a) →
           wkTel t 0F ≢ wkTel (tν (t ++ᵗ [])) y
ν-head-∉ t y eq
  with wkTel-inj t (eq ■ wkTel-++ᵗ t [] (weaken* ⦃ Kᵣ ⦄ 2 y))
... | ()

------------------------------------------------------------------------
-- The strengthened Stage-1 pinning: PinBase.pin-redex + the boundary.
------------------------------------------------------------------------

pin-redex-bound :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n)
    {k} (C : Ctx* n k) {T : Tm (2 + k)} {P₁ : Proc (2 + k)} →
  live T ≡ T ∷ [] →
  C [ ν (⟪ T ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ →
  Σ[ ρ ∈ ((2 + k) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P)) × (e† ⋯ Bσ (tel (prenexᵗ P)) σ ≡ T ⋯ ρ)
     × (∀ z → ρ 0F ≢ wkTel (BTel (tel (prenexᵗ P)) n) z))
pin-redex-bound P σ C {T} {P₁} lt c
  with ρC , mC , bC ← ctx-thread-bound C (ν (⟪ T ⟫ ∥ P₁)) (here refl)
  with ρt , e† , m† , eq , bt ← image-pin-bound P σ c mC
        (live-ren ρC (live-ren (wkTel (tel (nf P₁))) lt))
  = ((wkTel (tel (nf P₁)) ·ₖ ρC) ·ₖ ρt) , e† , m†
  , (eq ■ cong (_⋯ ρt) (fusion T (wkTel (tel (nf P₁))) ρC)
        ■ fusion T (wkTel (tel (nf P₁)) ·ₖ ρC) ρt)
  , bt (bC (ν-head-∉ (tel (nf P₁))))

pin-lsplit-redex-bound :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n)
    {k} (C : Ctx* n k) (s : 𝕊 0) {e₁ e₂ : Tm (2 + k)} {P₁ : Proc (2 + k)}
    (F : Frame* (2 + k)) →
  C [ ν (⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ →
  Σ[ ρ ∈ ((2 + k) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P))
     × (e† ⋯ Bσ (tel (prenexᵗ P)) σ
          ≡ (F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]*) ⋯ ρ)
     × (∀ z → ρ 0F ≢ wkTel (BTel (tel (prenexᵗ P)) n) z))
pin-lsplit-redex-bound P σ C s {e₁} {e₂} {P₁} F c =
  pin-redex-bound P σ C (plug·-live F (K (`lsplit s)) 𝟙 ((e₁ ⊗ (` 0F)) ⊗ e₂)) c
