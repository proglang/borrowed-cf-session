-- | BACKWARD simulation — the CLEAN statement (current design, Route A).
--
--   Every untyped step of the translation is reflected by a typed step, UP TO
--   structural congruence ≋ on both sides.  The reflection is WEAK in exactly
--   one place: `discard, which the untyped runtime GCs on a spent ⟨skip⟩ handle
--   that the (ν-scoped) typed R-Discard cannot match on a bare thread — see
--   BorrowedCF.Simulation.DiscardProbe.  That silent GC is absorbed by ≈ =
--   EqClosure(≋ ∪ ─→ᵃ), whose ONLY administrative generator is now a-discard
--   (acquire's old `done`/cleanup GC is gone).  The old `─→ᶜ? trailing-cleanup
--   slack is therefore dropped; the typed side is ≤1 step (Star).
--
--   (A fully strong up-to-≋ statement — dropping ≈ for ≋ — is available only by
--    adding a thread-local typed discard rule; see the Q1 discussion.)
module BorrowedCF.Simulation2.Backward where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import BorrowedCF.Simulation.RevAdmin using (_≈_)

Backward-Sim : Set
Backward-Sim =
  ∀ {m} {n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
  → {R Q : UP.Proc n} → R ≈ U[ P ] σ → R UR.─→ₚ Q
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

-- ── sim← WIRING MAP (every untyped constructor MUST be dispatched; Agda's
--    coverage checker enforces completeness when sim← is assembled) ──
--   RU-Exp      → inv-U-⟪⟫ + ⋯→-reflect            leaf reflection
--   RU-Fork     → inv-U-⟪⟫ + frameApp-reflect      leaf reflection
--   RU-New      → frameApp-reflect + rnew inversion leaf reflection
--   RU-Discard  → silent (a-discard ⇒ ≈)           leaf (weak)
--   RU-LSplit   → lsplit-go   [RevLSplit]          channel-op reflection
--   RU-RSplit   → rsplit-go   [RevRSplit]          channel-op reflection
--   RU-Com      → com-go      [RevCom]             channel-op reflection
--   RU-Choice   → choice-go   [RevChoice]          channel-op reflection
--   RU-Close    → close-go    [RevClose]           channel-op reflection
--   RU-Acquire  → acq-go      [RevAcq]             channel-op reflection
--   RU-Par      → inv-U-∥ + recurse                inline (recursive)
--   RU-Sync     → vacuous at top level             inline
--   RU-Res      → simRes (φ-nest peel)             inline; ⊇ RU-Drop innermost  [HARD ×2]
--   RU-Struct   → non-ε ≈-chain engine             inline                       [HARD ×1]


open import BorrowedCF.Simulation2.Backward.Leaf using (bwd-exp; bwd-fork; bwd-new)
open import BorrowedCF.Simulation2.Backward.LSplit using (lsplit-reflect)
open import BorrowedCF.Simulation2.Backward.RSplit using (rsplit-reflect)
open import BorrowedCF.Simulation2.Backward.Choice using (choice-reflect)
open import BorrowedCF.Simulation2.Backward.Close using (close-reflect)
open import BorrowedCF.Simulation2.Backward.Com using (com-reflect)
open import BorrowedCF.Simulation2.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.ReverseInv
  using (inv-ν-chanCx; νσ-φfree; νσ-φfree-VSub; U-ν-φfree-eq; ν-inj)
open import BorrowedCF.Simulation.RevAdmin
  using (≈-sym; ≈-trans; ≋⇒≈; ─→ᵃ⇒≈; ≈-ν-cong; ≈-∥-congˡ; a-discard)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import Relation.Binary.PropositionalEquality as Eq
open TP using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)

-- syncs-of : the (≤singleton) φ-free shape of a bind group, or a ≥2 witness.
syncs-of : (B : TP.BindGroup)
         → (syncs B ≡ 0) ⊎ (Σ[ b ∈ ℕ ] Σ[ c ∈ ℕ ] Σ[ Bp ∈ TP.BindGroup ] (B ≡ b ∷ c ∷ Bp))
syncs-of []           = inj₁ refl
syncs-of (b ∷ [])     = inj₁ refl
syncs-of (b ∷ c ∷ Bp) = inj₂ (b , c , Bp , refl)

-- Mutual: sim← (≈-closed public entry), sim←ᵍ (≡-image inversion engine),
-- simRes (RU-Res φ-nest peel, factored out to keep the σ : m →ₛ n scope index).
sim←   : Backward-Sim
sim←ᵍ  : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
       → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
       → {R Q : UP.Proc n} → R ≡ U[ P ] σ → R UR.─→ₚ Q
       → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)
simRes : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ → {g : Struct m}
       → (B₁ B₂ : TP.BindGroup) (P₀ : TP.Proc (sum B₁ + sum B₂ + m))
       → Γ ; g ⊢ₚ TP.ν B₁ B₂ P₀
       → (X X′ : UP.Proc (2 + n)) → X UR.─→ₚ X′
       → UP.ν X ≡ U[ TP.ν B₁ B₂ P₀ ] σ
       → (syncs B₁ ≡ 0) ⊎ _ → (syncs B₂ ≡ 0) ⊎ _
       → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ (TP.ν B₁ B₂ P₀) P′ × UP.ν X′ ≈ U[ P′ ] σ)

-- sim← : ε prefix = engine at refl; genuine ≈-chain = documented non-ε hole.
sim← σ Vσ Γ-S ⊢P ε        red = sim←ᵍ σ Vσ Γ-S ⊢P refl red
sim← σ Vσ Γ-S ⊢P (c ◅ cs) red =
  {! non-ε ≈-chain engine — φ-scattered-image ≋-normalization (research-scale hole). !}

-- RU-Exp / RU-Fork : thread leaves (Backward.Leaf).
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Exp step) = bwd-exp  σ Vσ Γ-S ⊢P (sym eq) step
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Fork F V) = bwd-fork σ Vσ Γ-S ⊢P {F = F} V (sym eq)
-- RU-New : post-swap bridge reconcile pending — HOLE.
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-New {s = s} F) = bwd-new σ Vσ Γ-S ⊢P {s = s} {F = F} (sym eq)
-- RU-Discard : silent GC absorbed by a-discard.
sim←ᵍ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Discard F V) =
  P , ε , subst (UP.⟪ F [ * ]* ⟫ ≈_) eq (≈-sym (─→ᵃ⇒≈ (a-discard F V)))
-- RU-Par : recurse on the left, R-Par wrap.
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Par sub)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Par sub)
sim←ᵍ σ Vσ Γ-S {P = P₁ TP.∥ P₂}   ⊢P refl (UR.RU-Par sub)
  with _ , _ , _ , ⊢P₁ , _ ← inv-∥ ⊢P
  with P₁′ , step₁ , c₁ ← sim←ᵍ σ Vσ Γ-S ⊢P₁ refl sub =
  P₁′ TP.∥ P₂ , ⋆-gmap (TP._∥ P₂) TR.R-Par step₁ , ≈-∥-congˡ c₁
-- RU-Res : φ-nest peel (simRes).
sim←ᵍ σ Vσ Γ-S {P = P} ⊢P eq (UR.RU-Res {P = X} {Q = X′} sub)
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ (sym eq)
  = simRes σ Vσ Γ-S B₁ B₂ P₀ ⊢P X X′ sub bodyeq (syncs-of B₁) (syncs-of B₂)
-- RU-Sync : U[_] never heads with φ, vacuous at top level.
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Sync sub)
sim←ᵍ σ Vσ Γ-S {P = P TP.∥ Q}     ⊢P () (UR.RU-Sync sub)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Sync sub)
-- RU-Drop : φ-headed, vacuous at top level (only under an inner RU-Res).
sim←ᵍ σ Vσ Γ-S {P = TP.⟪ e ⟫}     ⊢P () (UR.RU-Drop F)
sim←ᵍ σ Vσ Γ-S {P = P TP.∥ Q}     ⊢P () (UR.RU-Drop F)
sim←ᵍ σ Vσ Γ-S {P = TP.ν B₁ B₂ P} ⊢P () (UR.RU-Drop F)
-- Channel-op reflections — ported into Backward.<Op>; holes until they land.
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-LSplit F)     = lsplit-reflect σ Vσ Γ-S ⊢P {F = F} (sym eq)
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-RSplit F)     = rsplit-reflect σ Vσ Γ-S ⊢P {F = F} (sym eq)
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Acquire F)    = {! acq-go (Backward.Acq) !}
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Close F₁ F₂)  = close-reflect σ Vσ Γ-S ⊢P {F₁ = F₁} {F₂ = F₂} (sym eq)
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Com F₁ F₂ V)  = com-reflect σ Vσ Γ-S ⊢P {F₁ = F₁} {F₂ = F₂} V (sym eq)
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Choice F₁ F₂ k) = choice-reflect σ Vσ Γ-S ⊢P {k = k} {F₁ = F₁} {F₂ = F₂} (sym eq)
-- RU-Struct : ≈-absorb both congruence links, recurse through sim←.
sim←ᵍ σ Vσ Γ-S ⊢P eq (UR.RU-Struct c₁ inner c₂)
  with P′ , steps , Q″≈ ← sim← σ Vσ Γ-S ⊢P (≋⇒≈ (Eq*.symmetric _ c₁ ◅◅ ≡→≋ eq)) inner =
  P′ , steps , ≈-trans (≋⇒≈ (Eq*.symmetric _ c₂)) Q″≈

-- simRes : φ-free recurse at the flat leaf; φ-bearing = documented holes.
simRes σ Vσ Γ-S B₁ B₂ P₀ ⊢P X X′ sub bodyeq (inj₁ s₁) (inj₁ s₂)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with P₀′ , steps , c ← sim←ᵍ (νσ-φfree B₁ B₂ σ s₁ s₂) (νσ-φfree-VSub B₁ B₂ σ Vσ s₁ s₂)
        Γ′-S ⊢body (ν-inj (Eq.trans bodyeq (U-ν-φfree-eq B₁ B₂ P₀ σ s₁ s₂))) sub =
  TP.ν B₁ B₂ P₀′ , ⋆-gmap (TP.ν B₁ B₂) TR.R-Bind steps ,
  subst (UP.ν X′ ≈_) (sym (U-ν-φfree-eq B₁ B₂ P₀′ σ s₁ s₂)) (≈-ν-cong c)
simRes σ Vσ Γ-S B₁ B₂ P₀ ⊢P X X′ sub bodyeq (inj₂ _) _ =
  {! RU-Res φ-bearing (syncs B₁ ≥ 1): Sync-descent + Struct-bounce (sc-measure WF)
     + innermost RU-Drop; needs R-Drop interior-block generalization (calculus change). !}
simRes σ Vσ Γ-S B₁ B₂ P₀ ⊢P X X′ sub bodyeq _ (inj₂ _) =
  {! RU-Res φ-bearing (syncs B₂ ≥ 1): same finding as the syncs B₁ ≥ 1 clause. !}
