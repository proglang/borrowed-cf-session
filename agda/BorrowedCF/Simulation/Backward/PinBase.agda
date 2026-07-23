-- | Backward simulation, RU-LSplit probe — Stage 1: REDEX PINNING.
--
--   From  c : C [ ν (⟪ T ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ  with a LIVE redex thread T,
--   the normal-form witness theory (Normal.Witness) pins T to ONE typed prenex
--   thread: `≋-witness c` composed with `image-block-~ P σ` yields a renaming
--   carrying T into the image's block normal form, whose live-thread multiset
--   is the typed prenex threads under the accumulated substitution `Bσ`.  The
--   result is an on-the-nose equation
--
--       e† ⋯ Bσ (tel (prenexᵗ P)) σ ≡ T ⋯ ρ
--
--   for some e† ∈ thr (prenexᵗ P) — no ~ᵩ residue survives, because the
--   witness's `thrs` permutation is stated on `live*` and T is live.
--
--   STATUS: CLOSED (no holes).  Consumed by Backward.PinLSplit (Stages 2-4).
module BorrowedCF.Simulation.Backward.PinBase where

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
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Flat using (live; live*; isUnit?)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (Witness; mkW; fwd; bwd; inv₁; inv₂; thrs;
         witness-trans; ≋-witness; ~-witness; live-⋯)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BScope; BTel; Bσ; image-block-~)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Backward.BaseForkNew using (plug·-live)

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
-- Liveness is stable under renaming and locates threads in `live*`.
------------------------------------------------------------------------

live-ren : ∀ {a b} (ρ : a →ᵣ b) {e : Tm a} →
           live e ≡ e ∷ [] → live (e ⋯ ρ) ≡ (e ⋯ ρ) ∷ []
live-ren ρ {e} le = live-⋯ ρ e ■ cong (map (_⋯ ρ)) le

∈-live : ∀ {a} {e : Tm a} (x : Tm a) → e ∈ live x → e ≡ x
∈-live {e = e} x m with isUnit? x
∈-live {e = e} x m | inj₁ refl with m
... | ()
∈-live {e = e} x m | inj₂ eq with subst (e ∈_) eq m
... | here q = q
... | there ()

∈-live* : ∀ {a} {e : Tm a} {es : List (Tm a)} →
          e ∈ es → live e ≡ e ∷ [] → e ∈ live* es
∈-live* {es = x ∷ es} (here refl) le =
  subst (λ z → _ ∈ z ++ live* es) (sym le) (here refl)
∈-live* {es = x ∷ es} (there m)   le = ∈-++⁺ʳ (live x) (∈-live* m le)

live*-∈⁻ : ∀ {a} {e : Tm a} (es : List (Tm a)) → e ∈ live* es → e ∈ es
live*-∈⁻ (x ∷ es) m with ∈-++⁻ (live x) m
... | inj₁ mx = here (∈-live x mx)
... | inj₂ m′ = there (live*-∈⁻ es m′)

unit-dead : ∀ {a} {e : Tm a} → e ≡ K `unit → live e ≡ e ∷ [] → ⊥
unit-dead refl ()

------------------------------------------------------------------------
-- A thread of the body survives into the normal form of any plugging,
-- carried by a concrete composite renaming.
------------------------------------------------------------------------

ctx-thread : ∀ {n k} (C : Ctx* n k) (X : Proc k) {e : Tm (inner (nf X))} →
             e ∈ thr (nf X) →
             Σ[ ρ ∈ (inner (nf X) →ᵣ inner (nf (C [ X ]ᴷ))) ]
               ((e ⋯ ρ) ∈ thr (nf (C [ X ]ᴷ)))
ctx-thread ∘ᴷ X {e} m =
  idₖ , subst (_∈ thr (nf X)) (sym (⋯-id e (λ _ → refl))) m
ctx-thread (C ∥ᴷ Q) X {e} m
  with ρ₀ , m₀ ← ctx-thread C X m =
  let lft = liftRen (tel (nf (C [ X ]ᴷ))) (wkTel (tel (nf Q))) in
    (ρ₀ ·ₖ lft)
  , subst (_∈ thr (nf ((C [ X ]ᴷ) ∥ Q))) (fusion e ρ₀ lft)
      (∈-++⁺ˡ (∈-map⁺ (_⋯ lft) m₀))
ctx-thread (P ᴷ∥ C) X {e} m
  with ρ₀ , m₀ ← ctx-thread C X m =
  let ρʳ = wkTel (renTel (tel (nf P)) (inner (nf (C [ X ]ᴷ)))) in
    (ρ₀ ·ₖ ρʳ)
  , subst (_∈ thr (nf (P ∥ (C [ X ]ᴷ)))) (fusion e ρ₀ ρʳ)
      (∈-++⁺ʳ (map (_⋯ liftRen (tel (nf P)) (wkTel (tel (nf (C [ X ]ᴷ))))) (thr (nf P)))
              (∈-map⁺ (_⋯ ρʳ) m₀))
ctx-thread (νᴷ C)   X m with ρ₀ , m₀ ← ctx-thread C X m = ρ₀ , m₀
ctx-thread (φᴷ f C) X m with ρ₀ , m₀ ← ctx-thread C X m = ρ₀ , m₀

------------------------------------------------------------------------
-- Pinning a live thread of a ≋-preimage to a typed prenex thread.
------------------------------------------------------------------------

image-pin :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n) {Rt : Proc n} (c : Rt ≋ U[ P ] σ)
    {e : Tm (inner (nf Rt))} → e ∈ thr (nf Rt) → live e ≡ e ∷ [] →
  Σ[ ρ ∈ (inner (nf Rt) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P)) × (e† ⋯ Bσ (tel (prenexᵗ P)) σ ≡ e ⋯ ρ))
image-pin {m} {n} P σ {Rt} c {e} mem le
  with w ← witness-trans (≋-witness c) (~-witness (image-block-~ P σ))
  with m₂ ← live*-∈⁻ _ (∈-resp-↭ (thrs w)
              (∈-live* (∈-map⁺ (_⋯ fwd w) mem) (live-ren (fwd w) le)))
  with ∈-++⁻ (map (_⋯ Bσ (tel (prenexᵗ P)) σ) (thr (prenexᵗ P))) m₂
... | inj₂ (here q)   = ⊥-elim (unit-dead q (live-ren (fwd w) le))
... | inj₂ (there ())
... | inj₁ mm
  with e† , m† , qq ← ∈-map⁻ (_⋯ Bσ (tel (prenexᵗ P)) σ) mm
  = fwd w , e† , m† , sym qq

------------------------------------------------------------------------
-- The Stage-1 headline: a live thread of a ν-body, in context, is pinned.
------------------------------------------------------------------------

pin-redex :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n)
    {k} (C : Ctx* n k) {T : Tm (2 + k)} {P₁ : Proc (2 + k)} →
  live T ≡ T ∷ [] →
  C [ ν (⟪ T ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ →
  Σ[ ρ ∈ ((2 + k) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P)) × (e† ⋯ Bσ (tel (prenexᵗ P)) σ ≡ T ⋯ ρ))
pin-redex P σ C {T} {P₁} lt c
  with ρC , mC ← ctx-thread C (ν (⟪ T ⟫ ∥ P₁)) (here refl)
  with ρt , e† , m† , eq ← image-pin P σ c mC
        (live-ren ρC (live-ren (wkTel (tel (nf P₁))) lt))
  = ((wkTel (tel (nf P₁)) ·ₖ ρC) ·ₖ ρt) , e† , m†
  , (eq ■ cong (_⋯ ρt) (fusion T (wkTel (tel (nf P₁))) ρC)
        ■ fusion T (wkTel (tel (nf P₁)) ·ₖ ρC) ρt)

pin-lsplit-redex :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n)
    {k} (C : Ctx* n k) (s : 𝕊 0) {e₁ e₂ : Tm (2 + k)} {P₁ : Proc (2 + k)}
    (F : Frame* (2 + k)) →
  C [ ν (⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ →
  Σ[ ρ ∈ ((2 + k) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ e† ∈ Tm (inner (prenexᵗ P)) ]
    ((e† ∈ thr (prenexᵗ P))
     × (e† ⋯ Bσ (tel (prenexᵗ P)) σ
          ≡ (F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]*) ⋯ ρ))
pin-lsplit-redex P σ C s {e₁} {e₂} {P₁} F c =
  pin-redex P σ C (plug·-live F (K (`lsplit s)) 𝟙 ((e₁ ⊗ (` 0F)) ⊗ e₂)) c
