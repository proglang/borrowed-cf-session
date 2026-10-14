-- | Backward simulation, RU-LSplit — Stage D toolkit, part 1: telescope
--   STABILITY under growing one bind-group entry, and naturality of the
--   image substitution `Bσ` in the telescope's base renaming.
--
--   Contents:
--     * `syncs-mid` / `syncFlags-mid` / `ϕ-grow` — a bind group's sync data
--       ignores the VALUE of one entry (only the length and the per-entry
--       zero-test matter, and a grown entry stays nonzero).
--     * `tel-shape-≡` — a `Tel` is determined by its `shape` (and base).
--     * `blockShape` and `shape-BTel` — the image telescope's shape, read off
--       the typed telescope's sync data only.
--     * `BTel-≡` — two typed telescopes with the same block shape have the
--       same image telescope (up to the induced `BScope` transport).
--     * `Bσ-cong-at` — `Bσ t σ x` probes σ at ONE source variable at most.
--     * `BScope-⋯ᵗᵉˡ` / `Bσ-⋯ᵗᵉˡ` — re-basing the typed telescope along a
--       renaming is invisible to the image: `Bσ` is natural in the base.
--
--   STATUS: building.  Consumed by Backward.{PinHandle,PinReduct,PinLSplit}.
module BorrowedCF.Simulation.Backward.PinLwk where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP

open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; tν; tφ; _++ᵗ_) renaming ([] to []ᵀ)
open import BorrowedCF.Simulation.Support.Normal.Image
  using (Slot; sν; sφ; shape; shape-++ᵗ; shape-subst; shape-φTel;
         syncFlags; φTel; σB; module νImage)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1
  using (canonₛ; leafσ; leafσ-A₁; leafσ-B₁; leafσ-tail)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2
  using (leafσ-lwk-id)
open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ
  using (syncs-lwkq)
open import BorrowedCF.Terms using (module SplitRenamings)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BScope; BTel; Bσ)
open import BorrowedCF.Simulation.Backward.PinConj
  using (BScope-++; Bσ-++; Bσ-ambient; Bσ-node; BσWk; tsplit; νHandle;
         splitAt-inv₁; splitAt-inv₂)
open import BorrowedCF.Simulation.Support.BlockPerm using (weaken*ᵣ~↑ʳ; ↑*-split)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (∷-injective)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; ↑ʳ-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Sync data of a bind group ignores one entry's value.
------------------------------------------------------------------------

ϕ-grow : ∀ q b₁ → ϕ[ q + suc b₁ ] ≡ ϕ[ q + suc (suc b₁) ]
ϕ-grow zero    b₁ = refl
ϕ-grow (suc q) b₁ = refl

syncs-mid : ∀ (G₁ : TP.BindGroup) (x y : ℕ) (G₂ : TP.BindGroup) →
            syncs (G₁ ++ x ∷ G₂) ≡ syncs (G₁ ++ y ∷ G₂)
syncs-mid []            x y []      = refl
syncs-mid []            x y (_ ∷ _) = refl
syncs-mid (a ∷ [])      x y G₂      = cong suc (syncs-mid [] x y G₂)
syncs-mid (a ∷ b ∷ G₁)  x y G₂      = cong suc (syncs-mid (b ∷ G₁) x y G₂)

syncFlags-mid : ∀ (G₁ : TP.BindGroup) {x y : ℕ} → ϕ[ x ] ≡ ϕ[ y ] →
                (G₂ : TP.BindGroup) →
                syncFlags (G₁ ++ x ∷ G₂) ≡ syncFlags (G₁ ++ y ∷ G₂)
syncFlags-mid []           f []      = refl
syncFlags-mid []           f (g ∷ G₂) = cong (_∷ syncFlags (g ∷ G₂)) f
syncFlags-mid (a ∷ [])     f G₂      = cong (_ ∷_) (syncFlags-mid [] f G₂)
syncFlags-mid (a ∷ b ∷ G₁) f G₂      = cong (_ ∷_) (syncFlags-mid (b ∷ G₁) f G₂)

------------------------------------------------------------------------
-- A telescope is determined by its shape.
------------------------------------------------------------------------

private
  subst-tν : ∀ {n k k′} (eq : k ≡ k′) (t : Tel (2 + n) k) →
             subst (Tel n) eq (tν t) ≡ tν (subst (Tel (2 + n)) eq t)
  subst-tν refl t = refl

  subst-tφ : ∀ {n k k′} (eq : k ≡ k′) (f : _) (t : Tel (1 + n) k) →
             subst (Tel n) eq (tφ f t) ≡ tφ f (subst (Tel (1 + n)) eq t)
  subst-tφ refl f t = refl

  sφ-inj : ∀ {f g} → sφ f ≡ sφ g → f ≡ g
  sφ-inj refl = refl

tel-shape-≡ : ∀ {n m m′} (t : Tel n m) (t′ : Tel n m′) →
              shape t ≡ shape t′ →
              Σ[ eq ∈ m ≡ m′ ] (subst (Tel n) eq t ≡ t′)
tel-shape-≡ []ᵀ      []ᵀ       sh = refl , refl
tel-shape-≡ []ᵀ      (tν t′)   ()
tel-shape-≡ []ᵀ      (tφ f t′) ()
tel-shape-≡ (tν t)   []ᵀ       ()
tel-shape-≡ (tφ f t) []ᵀ       ()
tel-shape-≡ (tν t)   (tν t′)   sh
  with eq , teq ← tel-shape-≡ t t′ (proj₂ (∷-injective sh))
  = eq , (subst-tν eq t ■ cong tν teq)
tel-shape-≡ (tν t)   (tφ g t′) sh with () ← proj₁ (∷-injective sh)
tel-shape-≡ (tφ f t) (tν t′)   sh with () ← proj₁ (∷-injective sh)
tel-shape-≡ (tφ f t) (tφ g t′) sh
  with eq , teq ← tel-shape-≡ t t′ (proj₂ (∷-injective sh))
  = eq , ( subst-tφ eq f t
         ■ cong₂ tφ (sφ-inj (proj₁ (∷-injective sh))) teq )

------------------------------------------------------------------------
-- The image telescope's shape, from the typed telescope's sync data.
------------------------------------------------------------------------

blockShape : ∀ {a b} → TTel a b → List Slot
blockShape []ᵗ            = []
blockShape (tνᵗ B₁ B₂ t) =
  sν ∷ map sφ (syncFlags B₁) ++ map sφ (syncFlags B₂) ++ blockShape t

shape-BTel : ∀ {a b} (t : TTel a b) (n : ℕ) →
             shape (BTel t n) ≡ blockShape t
shape-BTel []ᵗ            n = refl
shape-BTel (tνᵗ B₁ B₂ t) n =
    shape-++ᵗ (tν (φTel B₁ (2 + n) ++ᵗ φTel B₂ (syncs B₁ + (2 + n))))
              (BTel t (syncs B₂ + (syncs B₁ + (2 + n))))
  ■ cong₂ _++_
      (cong (sν ∷_)
        ( shape-++ᵗ (φTel B₁ (2 + n)) (φTel B₂ (syncs B₁ + (2 + n)))
        ■ cong₂ _++_ (shape-φTel B₁ (2 + n))
                     (shape-φTel B₂ (syncs B₁ + (2 + n))) ))
      (shape-BTel t (syncs B₂ + (syncs B₁ + (2 + n))))
  ■ cong (sν ∷_)
      (L.++-assoc (map sφ (syncFlags B₁)) (map sφ (syncFlags B₂))
                  (blockShape t))

-- Two typed telescopes with the same block shape have the same image
-- telescope, up to the induced scope transport.
BTel-≡ : ∀ {a b a′ b′} (t : TTel a b) (t′ : TTel a′ b′) (n : ℕ) →
         blockShape t ≡ blockShape t′ →
         Σ[ eq ∈ BScope t n ≡ BScope t′ n ]
           (subst (Tel n) eq (BTel t n) ≡ BTel t′ n)
BTel-≡ t t′ n bs =
  tel-shape-≡ (BTel t n) (BTel t′ n)
    (shape-BTel t n ■ bs ■ sym (shape-BTel t′ n))

------------------------------------------------------------------------
-- `Bσ t σ x` probes σ at one source variable at most.
------------------------------------------------------------------------

Bσ-cong-at : ∀ {a b n} (t : TTel a b) {σ σ′ : a →ₛ n} (x : 𝔽 b) →
             ((y : 𝔽 a) → x ≡ wkTelᵗ t y → σ y ≡ σ′ y) →
             Bσ t σ x ≡ Bσ t σ′ x
Bσ-cong-at t {σ} {σ′} x cond with tsplit t x
... | inj₁ (y , xeq) =
      cong (Bσ t σ) xeq
    ■ Bσ-ambient t σ y
    ■ cong (_⋯ BσWk t _) (cond y xeq)
    ■ sym (Bσ-ambient t σ′ y)
    ■ cong (Bσ t σ′) (sym xeq)
Bσ-cong-at ._ {σ} {σ′} ._ cond
    | inj₂ (a′ , t₁ , C₁ , C₂ , t₂ , refl , z , refl) =
      Bσ-node t₁ C₁ C₂ t₂ σ z
    ■ sym (Bσ-node t₁ C₁ C₂ t₂ σ′ z)

------------------------------------------------------------------------
-- Naturality of Bσ in the base renaming.
------------------------------------------------------------------------

-- Re-basing is invisible to the image scope.
BScope-⋯ᵗᵉˡ : ∀ {a b a′} (t : TTel a b) (ρ : a →ᵣ a′) (N : ℕ) →
              BScope (t ⋯ᵗᵉˡ ρ) N ≡ BScope t N
BScope-⋯ᵗᵉˡ []ᵗ            ρ N = refl
BScope-⋯ᵗᵉˡ (tνᵗ C₁ C₂ t) ρ N =
  BScope-⋯ᵗᵉˡ t (ρ ↑* (sum C₁ + sum C₂)) (syncs C₂ + (syncs C₁ + (2 + N)))

-- ... and to the block shape.
blockShape-⋯ᵗᵉˡ : ∀ {a b a′} (t : TTel a b) (ρ : a →ᵣ a′) →
                  blockShape (t ⋯ᵗᵉˡ ρ) ≡ blockShape t
blockShape-⋯ᵗᵉˡ []ᵗ            ρ = refl
blockShape-⋯ᵗᵉˡ (tνᵗ C₁ C₂ t) ρ =
  cong (λ bs → sν ∷ map sφ (syncFlags C₁) ++ map sφ (syncFlags C₂) ++ bs)
       (blockShape-⋯ᵗᵉˡ t (ρ ↑* (sum C₁ + sum C₂)))

-- ↑* on the low (binder) region is the identity injection; on the high
-- (source) region it is the shifted renaming.
↑*-lo : ∀ {a a′} (ρ : a →ᵣ a′) (s : ℕ) (z : 𝔽 s) →
        (ρ ↑* s) (z ↑ˡ a) ≡ z ↑ˡ a′
↑*-lo {a} {a′} ρ s z =
    ↑*-split ρ s (z ↑ˡ a)
  ■ cong [ (_↑ˡ a′) , (λ k → s ↑ʳ ρ k) ]′ (splitAt-↑ˡ s z a)

↑*-hi : ∀ {a a′} (ρ : a →ᵣ a′) (s : ℕ) (w : 𝔽 a) →
        (ρ ↑* s) (s ↑ʳ w) ≡ s ↑ʳ ρ w
↑*-hi {a} {a′} ρ s w =
    ↑*-split ρ s (s ↑ʳ w)
  ■ cong [ (_↑ˡ a′) , (λ k → s ↑ʳ ρ k) ]′ (splitAt-↑ʳ s a w)

-- The single-node image substitution is natural in the source.
σ′-↑* : ∀ (C₁ C₂ : TP.BindGroup) {a a′ N} (ρ : a →ᵣ a′) (τ : a′ →ₛ N)
          (y : 𝔽 (sum C₁ + sum C₂ + a)) →
        νImage.σ′ C₁ C₂ τ ((ρ ↑* (sum C₁ + sum C₂)) y)
          ≡ νImage.σ′ C₁ C₂ (λ v → τ (ρ v)) y
σ′-↑* C₁ C₂ {a} {a′} {N} ρ τ y with splitAt (sum C₁ + sum C₂) y in seq
... | inj₁ z =
      cong (νImage.σ′ C₁ C₂ τ)
        ( cong (ρ ↑* (sum C₁ + sum C₂)) (splitAt-inv₁ y seq)
        ■ ↑*-lo ρ (sum C₁ + sum C₂) z )
    ■ redL
  where
    hd : 𝔽 (sum C₁ + sum C₂) → Tm (syncs C₂ + (syncs C₁ + (2 + N)))
    hd = _++ₛ_ {a = sum C₁} {b = sum C₂}
           (λ i → νImage.σ₁ C₁ C₂ τ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂))
           (νImage.σ₂ C₁ C₂ τ)
    redL : νImage.σ′ C₁ C₂ τ (z ↑ˡ a′) ≡ hd z
    redL = cong [ _ , _ ]′ (splitAt-↑ˡ (sum C₁ + sum C₂) z a′)
... | inj₂ w =
      cong (νImage.σ′ C₁ C₂ τ)
        ( cong (ρ ↑* (sum C₁ + sum C₂)) (splitAt-inv₂ y seq)
        ■ ↑*-hi ρ (sum C₁ + sum C₂) w )
    ■ redL
  where
    amb : 𝔽 a′ → Tm (syncs C₂ + (syncs C₁ + (2 + N)))
    amb = λ i → τ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₁)
                    ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C₂)
    redL : νImage.σ′ C₁ C₂ τ ((sum C₁ + sum C₂) ↑ʳ ρ w) ≡ amb (ρ w)
    redL = cong [ _ , _ ]′ (splitAt-↑ʳ (sum C₁ + sum C₂) a′ (ρ w))

-- Bσ is natural in the base renaming: re-base the telescope, pre-compose
-- the substitution.
Bσ-⋯ᵗᵉˡ : ∀ {a b a′ N} (t : TTel a b) (ρ : a →ᵣ a′) (τ : a′ →ₛ N)
            (x : 𝔽 b) →
          Bσ (t ⋯ᵗᵉˡ ρ) τ ((t ↑ᵗᵉˡ ρ) x)
            ≡ subst Tm (sym (BScope-⋯ᵗᵉˡ t ρ N)) (Bσ t (λ v → τ (ρ v)) x)
Bσ-⋯ᵗᵉˡ []ᵗ            ρ τ x = refl
Bσ-⋯ᵗᵉˡ (tνᵗ C₁ C₂ t) ρ τ x =
    Bσ-⋯ᵗᵉˡ t (ρ ↑* (sum C₁ + sum C₂)) (νImage.σ′ C₁ C₂ τ) x
  ■ cong (subst Tm (sym (BScope-⋯ᵗᵉˡ t (ρ ↑* (sum C₁ + sum C₂))
                          (syncs C₂ + (syncs C₁ + (2 + _))))))
      (Bσ-cong-at t x (λ y _ → σ′-↑* C₁ C₂ ρ τ y))

------------------------------------------------------------------------
-- Bridge to the forward theory: σB ≗ canonₛ, σ′ ≗ leafσ.
------------------------------------------------------------------------

private
  [,]-congʳ : ∀ {A B C : Set} {f : A → C} {g g′ : B → C} →
              (∀ b → g b ≡ g′ b) → (s : A ⊎ B) → [ f , g ]′ s ≡ [ f , g′ ]′ s
  [,]-congʳ h (inj₁ a) = refl
  [,]-congʳ h (inj₂ b) = h b

σB≗canonₛ : ∀ (B : TP.BindGroup) {N} (cc : UChan N) (y : 𝔽 (sum B)) →
            σB B cc y ≡ canonₛ B cc y
σB≗canonₛ (b ∷ [])            cc            y = refl
σB≗canonₛ (b ∷ B@(_ ∷ _)) {N} (e₁ , x , e₂) y =
  cong (subst Tm (+-suc (syncs B) N))
    ([,]-congʳ (σB≗canonₛ B (` 0F , suc x , wk e₂)) (splitAt b y))

σ′≗leafσ : ∀ (B₁ B₂ : TP.BindGroup) {m n} (σ : m →ₛ n)
             (y : 𝔽 (sum B₁ + sum B₂ + m)) →
           νImage.σ′ B₁ B₂ σ y ≡ leafσ σ B₁ B₂ y
σ′≗leafσ B₁ B₂ {m} {n} σ y = go (splitAt (sum B₁ + sum B₂) y) refl
  where
    go : (s : 𝔽 (sum B₁ + sum B₂) ⊎ 𝔽 m) →
         splitAt (sum B₁ + sum B₂) y ≡ s →
         νImage.σ′ B₁ B₂ σ y ≡ leafσ σ B₁ B₂ y
    go₁ : (z : 𝔽 (sum B₁ + sum B₂)) →
          splitAt (sum B₁ + sum B₂) y ≡ inj₁ z →
          (s₂ : 𝔽 (sum B₁) ⊎ 𝔽 (sum B₂)) → splitAt (sum B₁) z ≡ s₂ →
          νImage.σ′ B₁ B₂ σ y ≡ leafσ σ B₁ B₂ y
    go (inj₂ u) e1 = redσ ■ sym (leafσ-tail σ B₁ B₂ y u e1)
      where
        redσ : νImage.σ′ B₁ B₂ σ y
                 ≡ σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)
                     ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
        redσ = cong [ _ , _ ]′ e1
    go (inj₁ z) e1 = go₁ z e1 (splitAt (sum B₁) z) refl
    go₁ z e1 (inj₁ j) e2 =
        redσ
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (σB≗canonₛ B₁ (* , 0F , *) j)
      ■ sym (leafσ-A₁ σ B₁ B₂ y z j e1 e2)
      where
        redσ : νImage.σ′ B₁ B₂ σ y
                 ≡ νImage.σ₁ B₁ B₂ σ j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
        redσ = cong [ _ , _ ]′ e1 ■ cong [ _ , _ ]′ e2
    go₁ z e1 (inj₂ k) e2 =
        redσ
      ■ σB≗canonₛ B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *) k
      ■ sym (leafσ-B₁ σ B₁ B₂ y z k e1 e2)
      where
        redσ : νImage.σ′ B₁ B₂ σ y ≡ νImage.σ₂ B₁ B₂ σ k
        redσ = cong [ _ , _ ]′ e1 ■ cong [ _ , _ ]′ e2

------------------------------------------------------------------------
-- Single-node lwk-invisibility (off the consumed handle), at σ′.
------------------------------------------------------------------------

σ′-lwk : ∀ (B₁ B₂ B : TP.BindGroup) (q b₁ : ℕ) {m n} (σ : m →ₛ n)
           (i : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
         i ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
         subst (λ j → Tm (syncs B + (j + (2 + n)))) (syncs-lwkq B₁ {q} {b₁} {B₂})
           (νImage.σ′ (B₁ ++ (q + suc b₁) ∷ B₂) B σ i)
           ≡ νImage.σ′ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B σ
               (SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} i)
σ′-lwk B₁ B₂ B q b₁ {m} {n} σ i i≢ =
    cong (subst (λ j → Tm (syncs B + (j + (2 + n)))) (syncs-lwkq B₁ {q} {b₁} {B₂}))
      (σ′≗leafσ (B₁ ++ (q + suc b₁) ∷ B₂) B σ i)
  ■ leafσ-lwk-id σ B₁ B₂ B q b₁ i i≢
  ■ sym (σ′≗leafσ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B σ
          (SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} i))

------------------------------------------------------------------------
-- Transport helpers.
------------------------------------------------------------------------

subst-Tm-cong : ∀ {A : Set} (F : A → ℕ) {x y : A} (eq : x ≡ y) (t : Tm (F x)) →
                subst (λ j → Tm (F j)) eq t ≡ subst Tm (cong F eq) t
subst-Tm-cong F refl t = refl

subst-Tm-■ : ∀ {x y z : ℕ} (e₁ : x ≡ y) (e₂ : y ≡ z) (t : Tm x) →
             subst Tm e₂ (subst Tm e₁ t) ≡ subst Tm (e₁ ■ e₂) t
subst-Tm-■ refl refl t = refl

subst-Tm-irr : ∀ {x y : ℕ} (e e′ : x ≡ y) (t : Tm x) →
               subst Tm e t ≡ subst Tm e′ t
subst-Tm-irr e e′ t = cong (λ p → subst Tm p t) (Nat.≡-irrelevant e e′)

-- Bσ commutes with a codomain transport of the source substitution.
Bσ-subst-cod : ∀ {a b N N′} (t : TTel a b) (eq : N ≡ N′) (σ : a →ₛ N)
                 (x : 𝔽 b) →
               Bσ t (λ y → subst Tm eq (σ y)) x
                 ≡ subst Tm (cong (BScope t) eq) (Bσ t σ x)
Bσ-subst-cod t refl σ x = Bσ-cong-at t x (λ _ _ → refl)

-- The base weakening of a typed telescope is injective.
wkTelᵗ-inj : ∀ {a b} (t : TTel a b) {x y : 𝔽 a} →
             wkTelᵗ t x ≡ wkTelᵗ t y → x ≡ y
wkTelᵗ-inj []ᵗ            eq = eq
wkTelᵗ-inj (tνᵗ C₁ C₂ t) {x} {y} eq =
  ↑ʳ-injective (sum C₁ + sum C₂) x y
    ( sym (weaken*ᵣ~↑ʳ (sum C₁ + sum C₂) x)
    ■ wkTelᵗ-inj t eq
    ■ weaken*ᵣ~↑ʳ (sum C₁ + sum C₂) y )

------------------------------------------------------------------------
-- The telescope-level lwk-invisibility: growing one entry of a node's
-- FIRST group, off the consumed handle, is invisible to Bσ.
------------------------------------------------------------------------

module BσLwk {m n : ℕ} (σ : m →ₛ n)
             {aN : ℕ} (t₁ : TTel m aN)
             (G₁ G₂ : TP.BindGroup) (q b₁ : ℕ) (B : TP.BindGroup)
             {bN : ℕ}
             (t₂ : TTel (sum (G₁ ++ (q + suc b₁) ∷ G₂) + sum B + aN) bN)
  where

  C₁ C₁ᵍ : TP.BindGroup
  C₁  = G₁ ++ (q + suc b₁) ∷ G₂
  C₁ᵍ = G₁ ++ (q + suc (suc b₁)) ∷ G₂

  lwkᵃ : sum C₁ + sum B + aN →ᵣ sum C₁ᵍ + sum B + aN
  lwkᵃ = SplitRenamings.lwk G₁ G₂ (sum B) {q} {b₁} {aN}

  t₂ᵍ : TTel (sum C₁ᵍ + sum B + aN) (reScopeᵗ t₂ (sum C₁ᵍ + sum B + aN))
  t₂ᵍ = t₂ ⋯ᵗᵉˡ lwkᵃ

  ρᵀ : bN →ᵣ reScopeᵗ t₂ (sum C₁ᵍ + sum B + aN)
  ρᵀ = t₂ ↑ᵗᵉˡ lwkᵃ

  t : TTel m bN
  t  = t₁ ++ᵗᵗ tνᵗ C₁ B t₂

  t′ : TTel m (reScopeᵗ t₂ (sum C₁ᵍ + sum B + aN))
  t′ = t₁ ++ᵗᵗ tνᵗ C₁ᵍ B t₂ᵍ

  atkᵥ : 𝔽 (sum C₁ + sum B + aN)
  atkᵥ = SplitRenamings.atk G₁ G₂ (sum B) {q + suc b₁} {aN} (q ↑ʳ 0F)

  τ₀ : aN →ₛ BScope t₁ n
  τ₀ = Bσ t₁ σ

  Nold Nᵍ : ℕ
  Nold = syncs B + (syncs C₁ + (2 + BScope t₁ n))
  Nᵍ   = syncs B + (syncs C₁ᵍ + (2 + BScope t₁ n))

  ceq : Nold ≡ Nᵍ
  ceq = cong (λ j → syncs B + (j + (2 + BScope t₁ n))) (syncs-lwkq G₁ {q} {b₁} {G₂})

  eqB : BScope t n ≡ BScope t′ n
  eqB = BScope-++ t₁ (tνᵗ C₁ B t₂) n
      ■ cong (BScope t₂) ceq
      ■ sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ)
      ■ sym (BScope-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) n)

  Bσ-lwk-var : (v : 𝔽 bN) → v ≢ wkTelᵗ t₂ atkᵥ →
               Bσ t′ σ (ρᵀ v) ≡ subst Tm eqB (Bσ t σ v)
  Bσ-lwk-var v v≢ =
      Bσ-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) σ (ρᵀ v)
    ■ cong (subst Tm (sym (BScope-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) n)))
        ( Bσ-⋯ᵗᵉˡ t₂ lwkᵃ (νImage.σ′ C₁ᵍ B τ₀) v
        ■ cong (subst Tm (sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ)))
            ( Bσ-cong-at t₂ v cond
            ■ Bσ-subst-cod t₂ ceq (νImage.σ′ C₁ B τ₀) v ) )
    ■ cong (subst Tm (sym (BScope-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) n)))
        (subst-Tm-■ (cong (BScope t₂) ceq) (sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ)) X)
    ■ subst-Tm-■ (cong (BScope t₂) ceq ■ sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ))
                 (sym (BScope-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) n)) X
    ■ subst-Tm-irr _ (sym (BScope-++ t₁ (tνᵗ C₁ B t₂) n) ■ eqB) X
    ■ sym (subst-Tm-■ (sym (BScope-++ t₁ (tνᵗ C₁ B t₂) n)) eqB X)
    ■ cong (subst Tm eqB) (sym (Bσ-++ t₁ (tνᵗ C₁ B t₂) σ v))
    where
      X : Tm (BScope t₂ Nold)
      X = Bσ t₂ (νImage.σ′ C₁ B τ₀) v
      cond : (u : 𝔽 (sum C₁ + sum B + aN)) → v ≡ wkTelᵗ t₂ u →
             νImage.σ′ C₁ᵍ B τ₀ (lwkᵃ u) ≡ subst Tm ceq (νImage.σ′ C₁ B τ₀ u)
      cond u veq =
          sym (σ′-lwk G₁ G₂ B q b₁ τ₀ u
                (λ ueq → v≢ (veq ■ cong (wkTelᵗ t₂) ueq)))
        ■ subst-Tm-cong (λ j → syncs B + (j + (2 + BScope t₁ n)))
            (syncs-lwkq G₁ {q} {b₁} {G₂}) (νImage.σ′ C₁ B τ₀ u)
