-- | Backward simulation, RU-LSplit — Stage A (layout → rule arithmetic).
--
--   The NODE case of `pin-lsplit-fire` has the redex thread's channel variable
--   bound by a telescope node `tνᵗ B₁ B₂` sitting between a prefix `t₁` and a
--   suffix `t₂` of `prenexᵗ P`'s telescope.  The typed rule R-LSplit wants the
--   binding ν DIRECTLY above the redex thread, so the node must move to the
--   INNERMOST position — the mirror of TypedFocus's node-to-front.  Sinking is
--   the right direction here: the thread lives at the prenex inner scope, so
--   once the node is innermost NO strengthening/support analysis is needed —
--   the whole thread list sits directly under the node's ν.
--
--   Contents:
--     * `sinkN` / `node-to-backᵗ` — sink a chosen node below a telescope by
--       one adjacent `ν-comm′` per suffix binder (length-indexed recursion,
--       since each step rebases the remaining suffix).
--     * `sink-pin` — the sink renaming carries the node's own binder `z` to
--       the canonical low position `z ↑ˡ _` directly under the sunk ν.
--     * `blockAt` / `groupAt` — any position in a bind group decomposes as
--       R-LSplit's `B₁ ++ (q + suc b₁) ∷ B₂` with offset `q`; `atk-eq` turns
--       that into the rule's `𝐒.atk (q ↑ʳ 0F)` form (one `toℕ-injective`).
--     * `swap-mid` — the ν-swap arithmetic for a channel bound in the SECOND
--       group, and `step-plugᵗ` — R-Bind through a telescope.
--
--   STATUS: CLOSED (no holes).  Consumed by Backward.PinFire (Stages B/C).
module BorrowedCF.Simulation.Backward.PinFireBase where

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as TR

open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.BlockPerm using (weaken*ᵣ~↑ʳ)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug₁)
open import BorrowedCF.Simulation.Backward.PinConj using (splitAt-inv₁; splitAt-inv₂)
open import BorrowedCF.Terms using (module SplitRenamings)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Fin.Properties
  using (splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ-cast)
open import Data.Product using (Σ-syntax; _,_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)

------------------------------------------------------------------------
-- Telescope length (the sink recursion's measure).
------------------------------------------------------------------------

lenᵗ : ∀ {n k} → TTel n k → ℕ
lenᵗ []ᵗ           = zero
lenᵗ (tνᵗ B₁ B₂ t) = suc (lenᵗ t)

lenᵗ-⋯ᵗᵉˡ : ∀ {n k m} (t : TTel n k) (ρ : n →ᵣ m) → lenᵗ (t ⋯ᵗᵉˡ ρ) ≡ lenᵗ t
lenᵗ-⋯ᵗᵉˡ []ᵗ           ρ = refl
lenᵗ-⋯ᵗᵉˡ (tνᵗ B₁ B₂ t) ρ = cong suc (lenᵗ-⋯ᵗᵉˡ t (ρ ↑* (sum B₁ + sum B₂)))

------------------------------------------------------------------------
-- Sinking a ν-node below a telescope: the data.
------------------------------------------------------------------------

record Sunk (b a k : ℕ) : Set where
  constructor mkSunk
  field
    {sscope} : ℕ
    stel : TTel a sscope
    sρ   : k →ᵣ b + sscope

open Sunk public

sinkN : ∀ (l : ℕ) {a k} (b : ℕ) (t : TTel (b + a) k) → lenᵗ t ≡ l → Sunk b a k
sinkN l       b []ᵗ            _  = mkSunk []ᵗ idₖ
sinkN (suc l) b (tνᵗ C₁ C₂ t) eq =
  let Sk = sinkN l b (t ⋯ᵗᵉˡ assocSwapᵣ (sum C₁ + sum C₂) b)
            (lenᵗ-⋯ᵗᵉˡ t (assocSwapᵣ (sum C₁ + sum C₂) b) ■ Nat.suc-injective eq)
  in mkSunk (tνᵗ C₁ C₂ (stel Sk))
            ((t ↑ᵗᵉˡ assocSwapᵣ (sum C₁ + sum C₂) b) ·ₖ sρ Sk)

------------------------------------------------------------------------
-- Node to back: one adjacent ν-comm′ per suffix binder.
------------------------------------------------------------------------

node-to-backᵗ :
  ∀ (l : ℕ) {a k} (B₁ B₂ : BindGroup) (t : TTel (sum B₁ + sum B₂ + a) k)
    (eq : lenᵗ t ≡ l) (X : Proc k) →
  ν B₁ B₂ (plugᵗ t X)
    ≋ plugᵗ (stel (sinkN l (sum B₁ + sum B₂) t eq))
            (ν B₁ B₂ (X ⋯ₚ sρ (sinkN l (sum B₁ + sum B₂) t eq)))
node-to-backᵗ l B₁ B₂ []ᵗ _ X =
  ≡→≋ᵗ (cong (ν B₁ B₂) (sym (⋯ₚ-idᵣᵗ X (λ _ → refl))))
node-to-backᵗ (suc l) B₁ B₂ (tνᵗ C₁ C₂ t) eq X =
  Eq*.return ν-comm′
    ◅◅ ≡→≋ᵗ (cong (ν C₁ C₂ ∘ ν B₁ B₂) (plug-⋯ₚᵗ t X (assocSwapᵣ c b)))
    ◅◅ ν-cong (node-to-backᵗ l B₁ B₂ (t ⋯ᵗᵉˡ assocSwapᵣ c b) eq′
                 (X ⋯ₚ (t ↑ᵗᵉˡ assocSwapᵣ c b)))
    ◅◅ ≡→≋ᵗ (cong (λ Y → ν C₁ C₂ (plugᵗ (stel Sk) (ν B₁ B₂ Y)))
               (fusionₚ X (t ↑ᵗᵉˡ assocSwapᵣ c b) (sρ Sk)))
  where
    b = sum B₁ + sum B₂
    c = sum C₁ + sum C₂
    eq′ = lenᵗ-⋯ᵗᵉˡ t (assocSwapᵣ c b) ■ Nat.suc-injective eq
    Sk = sinkN l b (t ⋯ᵗᵉˡ assocSwapᵣ c b) eq′

------------------------------------------------------------------------
-- The sink renaming pins the node's own binders.
------------------------------------------------------------------------

-- A lifted renaming commutes with the weakening it was lifted past.
↑*-weaken*ᵣ : ∀ c {n m} (ρ : n →ᵣ m) (y : 𝔽 n) →
              (ρ ↑* c) (weaken* ⦃ Kᵣ ⦄ c y) ≡ weaken* ⦃ Kᵣ ⦄ c (ρ y)
↑*-weaken*ᵣ c ρ y =
    cong (ρ ↑* c) (weaken*ᵣ~↑ʳ c y)
  ■ ↑*≗wkˡʳ ρ c (c ↑ʳ y)
  ■ cong [ wkʳ _ , ρ ·ₖ wkˡ c ] (splitAt-↑ʳ c _ y)
  ■ sym (weaken*ᵣ~↑ʳ c (ρ y))

-- Naturality of a telescope's base weakening.
wkTel-natᵗ : ∀ {n k m} (t : TTel n k) (ρ : n →ᵣ m) (y : 𝔽 n) →
             (t ↑ᵗᵉˡ ρ) (wkTelᵗ t y) ≡ wkTelᵗ (t ⋯ᵗᵉˡ ρ) (ρ y)
wkTel-natᵗ []ᵗ           ρ y = refl
wkTel-natᵗ (tνᵗ B₁ B₂ t) ρ y =
    wkTel-natᵗ t (ρ ↑* c) (weaken* ⦃ Kᵣ ⦄ c y)
  ■ cong (wkTelᵗ (t ⋯ᵗᵉˡ (ρ ↑* c))) (↑*-weaken*ᵣ c ρ y)
  where c = sum B₁ + sum B₂

-- The middle block of an assocSwap lands at the bottom.
aswap-mid : ∀ c b {a} (z : 𝔽 b) →
            assocSwapᵣ c b {a} (weaken* ⦃ Kᵣ ⦄ c (z ↑ˡ a)) ≡ z ↑ˡ (c + a)
aswap-mid c b {a} z
  rewrite weaken*ᵣ~↑ʳ c (z ↑ˡ a)
        | splitAt-↑ʳ c (b + a) (z ↑ˡ a)
        | splitAt-↑ˡ b z a
  = refl

sink-pin : ∀ (l : ℕ) {a k} (b : ℕ) (t : TTel (b + a) k) (eq : lenᵗ t ≡ l)
           (z : 𝔽 b) →
           sρ (sinkN l b t eq) (wkTelᵗ t (z ↑ˡ a))
             ≡ z ↑ˡ sscope (sinkN l b t eq)
sink-pin l       b []ᵗ            _  z = refl
sink-pin (suc l) {a} b (tνᵗ C₁ C₂ t) eq z =
    cong (sρ Sk)
      ( wkTel-natᵗ t (assocSwapᵣ c b) (weaken* ⦃ Kᵣ ⦄ c (z ↑ˡ a))
      ■ cong (wkTelᵗ (t ⋯ᵗᵉˡ assocSwapᵣ c b)) (aswap-mid c b z) )
  ■ sink-pin l b (t ⋯ᵗᵉˡ assocSwapᵣ c b) eq′ z
  where
    c = sum C₁ + sum C₂
    eq′ = lenᵗ-⋯ᵗᵉˡ t (assocSwapᵣ c b) ■ Nat.suc-injective eq
    Sk = sinkN l b (t ⋯ᵗᵉˡ assocSwapᵣ c b) eq′

------------------------------------------------------------------------
-- The ν-swap arithmetic (channel bound in the SECOND group).
------------------------------------------------------------------------

swap-mid : ∀ g₁ g₂ {a} (z₂ : 𝔽 g₂) →
           swapᵣ g₁ g₂ {a} ((g₁ ↑ʳ z₂) ↑ˡ a) ≡ (z₂ ↑ˡ g₁) ↑ˡ a
swap-mid g₁ g₂ {a} z₂
  rewrite splitAt-↑ˡ (g₁ + g₂) (g₁ ↑ʳ z₂) a
        | splitAt-↑ʳ g₁ g₂ z₂
  = refl

------------------------------------------------------------------------
-- Any bind-group position is an R-LSplit handle position.
------------------------------------------------------------------------

record BlockAt (w : ℕ) (j : 𝔽 w) : Set where
  constructor mkBlockAt
  field
    bq bb₁ : ℕ
    weq    : w ≡ bq + suc bb₁
    jn     : Fin.toℕ j ≡ bq

blockAt : ∀ {w} (j : 𝔽 w) → BlockAt w j
blockAt {suc w} 0F      = mkBlockAt 0 w refl refl
blockAt {suc w} (suc j) with mkBlockAt q b₁ weq jn ← blockAt j =
  mkBlockAt (suc q) b₁ (cong suc weq) (cong suc jn)

record GroupAt (G : BindGroup) (z : 𝔽 (sum G)) : Set where
  constructor mkGroupAt
  field
    gB₁ gB₂ : BindGroup
    gq gb₁  : ℕ
    geq     : G ≡ gB₁ ++ (gq + suc gb₁) ∷ gB₂
    zn      : Fin.toℕ z ≡ sum gB₁ + gq

groupAt : ∀ (G : BindGroup) (z : 𝔽 (sum G)) → GroupAt G z
groupAt (w ∷ G) z with splitAt w z in seq
... | inj₁ j =
  let mkBlockAt q b₁ weq jn = blockAt j in
  mkGroupAt [] G q b₁ (cong (_∷ G) weq)
    (cong Fin.toℕ (splitAt-inv₁ z seq) ■ toℕ-↑ˡ j (sum G) ■ jn)
... | inj₂ z′ =
  let mkGroupAt B₁ B₂ q b₁ geq zn = groupAt G z′ in
  mkGroupAt (w ∷ B₁) B₂ q b₁ (cong (w ∷_) geq)
    ( cong Fin.toℕ (splitAt-inv₂ z seq) ■ toℕ-↑ʳ w z′
    ■ cong (w +_) zn ■ sym (+-assoc w (sum B₁) q) )

-- The rule's handle position, from the toℕ characterisation.
atk-eq : ∀ (B₁ B₂ : BindGroup) (q b₁ m a : ℕ)
           (v : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + m + a)) →
         Fin.toℕ v ≡ sum B₁ + q →
         v ≡ SplitRenamings.atk B₁ B₂ m {q + suc b₁} {a} (q ↑ʳ 0F)
atk-eq B₁ B₂ q b₁ m a v vn = toℕ-injective (vn ■ sym atkn)
  where
    atkn : Fin.toℕ (SplitRenamings.atk B₁ B₂ m {q + suc b₁} {a} (q ↑ʳ 0F))
             ≡ sum B₁ + q
    atkn =
        toℕ-↑ˡ _ a ■ toℕ-↑ˡ _ m
      ■ toℕ-cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) _
      ■ toℕ-↑ʳ (sum B₁) ((q ↑ʳ 0F) ↑ˡ sum B₂)
      ■ cong (sum B₁ +_)
          (toℕ-↑ˡ (q ↑ʳ 0F) (sum B₂) ■ toℕ-↑ʳ q 0F ■ +-identityʳ q)

------------------------------------------------------------------------
-- R-Bind through a telescope, and plugging under renaming (re-proof).
------------------------------------------------------------------------

step-plugᵗ : ∀ {m a} (T : TTel m a) {X Y : Proc a} →
             X TR.─→ₚ Y → plugᵗ T X TR.─→ₚ plugᵗ T Y
step-plugᵗ []ᵗ           r = r
step-plugᵗ (tνᵗ B₁ B₂ T) r = TR.R-Bind (step-plugᵗ T r)

frame-plug*ᵣ′ : ∀ {m p} (E : Frame* m) {t : Tm m} (ρ : m →ᵣ p) →
                (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ′ []       ρ = refl
frame-plug*ᵣ′ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ′ E* ρ)
