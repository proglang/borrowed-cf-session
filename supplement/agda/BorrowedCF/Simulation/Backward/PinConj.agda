-- | Backward simulation, RU-LSplit probe — Stage 2 (typing half): every
--   thread of the TYPED prenex normal form carries a typing derivation in a
--   channel context.
--
--   `prenex-soundᵗ` rewrites P to its prenex form; `TypedEq._/_⊢-≋_` transports
--   the typing across that typed ≋; `inv-ν-chanCx` walks the ν-telescope
--   (collecting the bind contexts, which stay channel contexts), and `inv-∥` /
--   `inv-⟪⟫` walk the flat thread list.  The result feeds `frameApp-reflect`
--   at the accumulated prenex-image substitution `Bσ` (PinLSplit).
--
--   STATUS: CLOSED (no holes).
module BorrowedCF.Simulation.Backward.PinConj where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP

open import BorrowedCF.TypedEq using (_/_⊢-≋_)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.ReverseInv using (inv-ν-chanCx)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (BScope; Bσ)
open import BorrowedCF.Simulation.Support.Normal.Image using (module νImage)
open import BorrowedCF.Simulation.Support.BlockPerm using (weaken*ᵣ~↑ʳ)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Fin.Base using () renaming (join to joinF)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ʳ; splitAt-↑ˡ)

-- Typing of one thread of a flat parallel composition.
⊢-pars-thread :
  ∀ {b} {Γ : Ctx b} {γ : Struct b} {es : List (Tm b)}
  → Γ ; γ ⊢ₚ parsᵗ es → {e : Tm b} → e ∈ es
  → Σ[ β ∈ Struct b ] (Γ ; β ⊢ e ∶ `⊤ ∣ 𝕀)
⊢-pars-thread {es = x ∷ es} ⊢p (here refl) =
  let _ , _ , _ , ⊢x , _ = inv-∥ ⊢p in _ , inv-⟪⟫ ⊢x
⊢-pars-thread {es = x ∷ es} ⊢p (there m) =
  let _ , _ , _ , _ , ⊢rest = inv-∥ ⊢p in ⊢-pars-thread ⊢rest m

-- Typing of one thread under a ν-telescope, in a channel context.
⊢-tel-thread :
  ∀ {m b} {Γ : Ctx m} {γ : Struct m} (Γ-S : ChanCx Γ)
    (t : TTel m b) {es : List (Tm b)}
  → Γ ; γ ⊢ₚ plugᵗ t (parsᵗ es) → {e : Tm b} → e ∈ es
  → Σ[ Γ* ∈ Ctx b ] Σ[ β ∈ Struct b ] (ChanCx Γ* × (Γ* ; β ⊢ e ∶ `⊤ ∣ 𝕀))
⊢-tel-thread {Γ = Γ} Γ-S []ᵗ ⊢p m
  with β , d ← ⊢-pars-thread ⊢p m
  = Γ , β , Γ-S , d
⊢-tel-thread Γ-S (tνᵗ B₁ B₂ t) ⊢p m
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢p
  = ⊢-tel-thread Γ′-S t ⊢body m

-- The headline: every thread of `prenexᵗ P` is typed, in a channel context.
⊢-prenex-thread :
  ∀ {m} {Γ : Ctx m} {γ : Struct m} (Γ-S : ChanCx Γ) {P : TP.Proc m}
  → Γ ; γ ⊢ₚ P → {e : Tm (inner (prenexᵗ P))} → e ∈ thr (prenexᵗ P)
  → Σ[ Γ* ∈ Ctx (inner (prenexᵗ P)) ] Σ[ β ∈ Struct (inner (prenexᵗ P)) ]
      (ChanCx Γ* × (Γ* ; β ⊢ e ∶ `⊤ ∣ 𝕀))
⊢-prenex-thread Γ-S {P = P} ⊢P m =
  ⊢-tel-thread Γ-S (tel (prenexᵗ P)) (Γ-S / ⊢P ⊢-≋ prenex-soundᵗ P) m

------------------------------------------------------------------------
-- Stage 2 (layout half): where a typed prenex variable sits.
------------------------------------------------------------------------

-- Splitting-at inversions, spelled on the repo's `splitAt`.
splitAt-inv₁ : ∀ {w a} (y : 𝔽 (w + a)) {z : 𝔽 w} →
               splitAt w y ≡ inj₁ z → y ≡ z ↑ˡ a
splitAt-inv₁ {w} {a} y seq =
  sym (join-splitAt w a y) ■ cong (joinF w a) seq

splitAt-inv₂ : ∀ {w a} (y : 𝔽 (w + a)) {y′ : 𝔽 a} →
               splitAt w y ≡ inj₂ y′ → y ≡ w ↑ʳ y′
splitAt-inv₂ {w} {a} y seq =
  sym (join-splitAt w a y) ■ cong (joinF w a) seq

-- A variable of the telescope's inner scope is either AMBIENT (the image of
-- an outer-scope variable) or belongs to exactly one `tνᵗ` node's bind blocks.
TNode : ∀ {m b} (t : TTel m b) (x : 𝔽 b) → Set
TNode {m} {b} t x =
  Σ[ a ∈ ℕ ] Σ[ t₁ ∈ TTel m a ] Σ[ B₁ ∈ TP.BindGroup ] Σ[ B₂ ∈ TP.BindGroup ]
  Σ[ t₂ ∈ TTel (sum B₁ + sum B₂ + a) b ]
    ((t ≡ t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂)
     × Σ[ z ∈ 𝔽 (sum B₁ + sum B₂) ] (x ≡ wkTelᵗ t₂ (z ↑ˡ a)))

tsplit : ∀ {m b} (t : TTel m b) (x : 𝔽 b) →
         (Σ[ y ∈ 𝔽 m ] (x ≡ wkTelᵗ t y)) ⊎ TNode t x
tsplit []ᵗ x = inj₁ (x , refl)
tsplit (tνᵗ B₁ B₂ t) x with tsplit t x
... | inj₂ (a , t₁ , C₁ , C₂ , t₂ , teq , z , xeq) =
      inj₂ (a , tνᵗ B₁ B₂ t₁ , C₁ , C₂ , t₂ , cong (tνᵗ B₁ B₂) teq , z , xeq)
... | inj₁ (y′ , xeq) with splitAt (sum B₁ + sum B₂) y′ in seq
...   | inj₁ z = inj₂ (_ , []ᵗ , B₁ , B₂ , t , refl , z ,
                   (xeq ■ cong (wkTelᵗ t) (splitAt-inv₁ y′ seq)))
...   | inj₂ y = inj₁ (y ,
                   (xeq ■ cong (wkTelᵗ t)
                     (splitAt-inv₂ y′ seq ■ sym (weaken*ᵣ~↑ʳ (sum B₁ + sum B₂) y))))

------------------------------------------------------------------------
-- The ambient action of the accumulated image substitution `Bσ`.
------------------------------------------------------------------------

-- The composite weakening `Bσ` applies to everything already in scope: at
-- each node, past the ν (2) and both φ-nests.  Right-nested so that the
-- soundness proof below is a plain `fusion` chain, no reassociation.
BσWk : ∀ {a b} (t : TTel a b) (n : ℕ) → n →ᵣ BScope t n
BσWk []ᵗ           n = idₖ
BσWk (tνᵗ B₁ B₂ t) n =
  weaken* ⦃ Kᵣ ⦄ 2 ·ₖ (weaken* ⦃ Kᵣ ⦄ (syncs B₁) ·ₖ (weaken* ⦃ Kᵣ ⦄ (syncs B₂)
    ·ₖ BσWk t (syncs B₂ + (syncs B₁ + (2 + n)))))

-- On an ambient variable, `Bσ` is the source substitution weakened.
Bσ-ambient : ∀ {a b n} (t : TTel a b) (σ : a →ₛ n) (y : 𝔽 a) →
             Bσ t σ (wkTelᵗ t y) ≡ σ y ⋯ BσWk t n
Bσ-ambient []ᵗ σ y = sym (⋯-id (σ y) (λ _ → refl))
Bσ-ambient {n = n} (tνᵗ B₁ B₂ t) σ y =
    Bσ-ambient t σ′ (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂) y)
  ■ cong (_⋯ BσWk t nB)
      ( cong σ′ (weaken*ᵣ~↑ʳ (sum B₁ + sum B₂) y)
      ■ cong [ _ , _ ]′ (splitAt-↑ʳ (sum B₁ + sum B₂) _ y) )
  ■ fusion (σ y ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁))
      (weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (BσWk t nB)
  ■ fusion (σ y ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ (syncs B₁)) _
  ■ fusion (σ y) (weaken* ⦃ Kᵣ ⦄ 2) _
  where
    nB = syncs B₂ + (syncs B₁ + (2 + n))
    open νImage B₁ B₂ σ

------------------------------------------------------------------------
-- Factoring `Bσ` at a telescope node.
------------------------------------------------------------------------

-- `BScope` and `Bσ` both fold layer-by-layer, so a telescope concatenation
-- factors on the nose (each cons case is the recursive call itself).
BScope-++ : ∀ {m a b} (t₁ : TTel m a) (s : TTel a b) (n : ℕ) →
            BScope (t₁ ++ᵗᵗ s) n ≡ BScope s (BScope t₁ n)
BScope-++ []ᵗ             s n = refl
BScope-++ (tνᵗ B₁ B₂ t₁) s n =
  BScope-++ t₁ s (syncs B₂ + (syncs B₁ + (2 + n)))

Bσ-++ : ∀ {m a b n} (t₁ : TTel m a) (s : TTel a b) (σ : m →ₛ n) (x : 𝔽 b) →
        Bσ (t₁ ++ᵗᵗ s) σ x
          ≡ subst Tm (sym (BScope-++ t₁ s n)) (Bσ s (Bσ t₁ σ) x)
Bσ-++ []ᵗ             s σ x = refl
Bσ-++ (tνᵗ B₁ B₂ t₁) s σ x = Bσ-++ t₁ s (νImage.σ′ B₁ B₂ σ) x

-- The bound part of one node's image substitution: its two σB nests over the
-- canonical channels (independent of the ambient substitution's values).
νHandle : ∀ (B₁ B₂ : TP.BindGroup) {a n} (τ : a →ₛ n) →
          sum B₁ + sum B₂ →ₛ (syncs B₂ + (syncs B₁ + (2 + n)))
νHandle B₁ B₂ τ =
  (λ i → νImage.σ₁ B₁ B₂ τ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ νImage.σ₂ B₁ B₂ τ

-- A node variable's image is that node's canonical handle, weakened past the
-- deeper layers: the whole-telescope analysis collapses to the SINGLE-NODE
-- handle analysis (SplitsH2.canonₛ-handleq) composed with `BσWk t₂`.
Bσ-node : ∀ {m a b n} (t₁ : TTel m a) (B₁ B₂ : TP.BindGroup)
            (t₂ : TTel (sum B₁ + sum B₂ + a) b)
            (σ : m →ₛ n) (z : 𝔽 (sum B₁ + sum B₂)) →
          Bσ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) σ (wkTelᵗ t₂ (z ↑ˡ a))
            ≡ subst Tm (sym (BScope-++ t₁ (tνᵗ B₁ B₂ t₂) n))
                (νHandle B₁ B₂ (Bσ t₁ σ) z
                   ⋯ BσWk t₂ (syncs B₂ + (syncs B₁ + (2 + BScope t₁ n))))
Bσ-node {a = a} {n = n} t₁ B₁ B₂ t₂ σ z =
    Bσ-++ t₁ (tνᵗ B₁ B₂ t₂) σ (wkTelᵗ t₂ (z ↑ˡ a))
  ■ cong (subst Tm (sym (BScope-++ t₁ (tνᵗ B₁ B₂ t₂) n)))
      ( Bσ-ambient t₂ (νImage.σ′ B₁ B₂ (Bσ t₁ σ)) (z ↑ˡ a)
      ■ cong (_⋯ BσWk t₂ (syncs B₂ + (syncs B₁ + (2 + BScope t₁ n))))
          (cong [ _ , _ ]′ (splitAt-↑ˡ (sum B₁ + sum B₂) z a)) )
