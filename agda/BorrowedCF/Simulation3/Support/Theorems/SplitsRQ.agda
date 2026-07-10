module BorrowedCF.Simulation3.Support.Theorems.SplitsRQ where

-- | q-generalized rsplit helpers: the interior remote split fires at block
--   position q of a width-(q + suc b₁) block, SPLITTING it into two blocks
--   (q + 1) ∷ suc b₁ (a fresh sync boundary/φ-drop lands between them).  These
--   mirror the position-0 helpers in SplitsH2/SplitsH3 (drwk / 𝐒rwk-lo/hi /
--   P1r/P2r/P3r / canonₛ-rwk / sins / handle-L/R-rwk / sw-* / Brwk-slide /
--   leafσ-rwk-id) but thread the block position q, so rwk inserts at flat
--   position sum B₁ + q and the consumed handle sits at sum B₁ + q.
--
--   The φ-side count is WIDTH-AGNOSTIC (`syncs` inspects only the block-list
--   structure), so all sync-level proofs carry over verbatim; only the data
--   renaming drwkq and the handle normalizations depend on q.

open import BorrowedCF.Simulation3.Support.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Terms using (module SplitRenamings)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import BorrowedCF.Simulation3.Support.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open import BorrowedCF.Processes.Bisim using (syncs)
open import Data.List.Properties using (++-assoc)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Simulation3.Support.TranslationProperties
  using (UB-nat; Ub-nat; mapᶜ; U-cong; U-⋯ₚ; U-σ⋯)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation3.Support.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)

open import BorrowedCF.Simulation3.Support.Theorems.SplitsH3 public

-- ============================================================================
--   syncs / sum bookkeeping for the two-block rsplit reshape.
-- ============================================================================

-- syncs inspects only the block-list structure, discarding head widths.
syncs-head-irrel : ∀ (x y : ℕ) (B₂ : BindGroup) → syncs (x ∷ B₂) ≡ syncs (y ∷ B₂)
syncs-head-irrel x y []      = refl
syncs-head-irrel x y (c ∷ D) = refl

-- the rsplit-split bind group has exactly one more sync (the new boundary φ).
syncs-rwkq : ∀ (B₁ : BindGroup) (q : ℕ) {b₁ : ℕ} {B₂ : BindGroup} →
             syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ≡ suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂))
syncs-rwkq []            q {b₁} {B₂} = cong suc (syncs-head-irrel (suc b₁) (q + suc b₁) B₂)
syncs-rwkq (a ∷ [])      q {b₁} {B₂} = cong suc (syncs-rwkq [] q {b₁} {B₂})
syncs-rwkq (a ∷ d ∷ B₁″) q {b₁} {B₂} = cong suc (syncs-rwkq (d ∷ B₁″) q {b₁} {B₂})

-- the rsplit-split bind group has exactly one more data slot.
sum-rwkq : ∀ (B₁ : BindGroup) (q : ℕ) {b₁ B₂} →
           sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂))
sum-rwkq B₁ q {b₁} {B₂} =
    sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)
  ■ midstep (sum B₁) q b₁ (sum B₂)
  ■ cong suc (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
  where
    midstep : ∀ s q b c → s + ((q + 1) + (suc b + c)) ≡ suc (s + ((q + suc b) + c))
    midstep = solve 4 (λ s q b c →
      s :+ ((q :+ con 1) :+ (con 1 :+ b :+ c)) := con 1 :+ (s :+ ((q :+ (con 1 :+ b)) :+ c))) refl

sB₁≤sumC₁rq : ∀ (B₁ : BindGroup) {q b₁ B₂} → sum B₁ Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
sB₁≤sumC₁rq B₁ {q} {b₁} {B₂} =
  subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
    (Nat.m≤m+n (sum B₁) (sum ((q + suc b₁) ∷ B₂)))

-- ============================================================================
--   drwkq : data-level rwk on the C₁ block group, inserting a slot at flat
--   position sum B₁ + q (block position q, the ret/acq boundary).
-- ============================================================================
drwkq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) →
        sum (B₁ ++ (q + suc b₁) ∷ B₂) →ᵣ sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)
drwkq []        zero    b₁ B₂ i = weakenᵣ i
drwkq []        (suc q) b₁ B₂ i with i
... | zero   = zero
... | suc i′ = suc (drwkq [] q b₁ B₂ i′)
drwkq (a ∷ B₁') q b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ (q + 1) ∷ suc b₁ ∷ B₂)) , (λ r → a ↑ʳ drwkq B₁' q b₁ B₂ r) ]′ (splitAt a i)

-- drwkq preserves toℕ below the insertion point (flat position sum B₁ + q).
drwkq-lo : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) (j : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
           Fin.toℕ j Nat.< sum B₁ + q → Fin.toℕ (drwkq B₁ q b₁ B₂ j) ≡ Fin.toℕ j
drwkq-lo []        zero    b₁ B₂ j lt = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans lt Nat.z≤n))
drwkq-lo []        (suc q) b₁ B₂ j lt with j
... | zero   = refl
... | suc j′ = cong suc (drwkq-lo [] q b₁ B₂ j′ (Nat.s≤s⁻¹ lt))
drwkq-lo (a ∷ B₁') q b₁ B₂ j lt with drwkq-lo B₁' q b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ (q + suc b₁) ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwkq B₁' q b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        assoc2 : a + sum B₁' + q ≡ a + (sum B₁' + q)
        assoc2 = Nat.+-assoc a (sum B₁') q
        boundr : Fin.toℕ r Nat.< sum B₁' + q
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁' + q)
                   (subst (Nat._< a + (sum B₁' + q)) jℕ (subst (Fin.toℕ j Nat.<_) assoc2 lt))

-- drwkq shifts toℕ by one at/above the insertion point (flat position sum B₁ + q).
drwkq-hi : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) (j : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
           sum B₁ + q Nat.≤ Fin.toℕ j → Fin.toℕ (drwkq B₁ q b₁ B₂ j) ≡ suc (Fin.toℕ j)
drwkq-hi []        zero    b₁ B₂ j h = Fin.toℕ-↑ʳ 1 j
drwkq-hi []        (suc q) b₁ B₂ j h with j
... | zero   = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.s≤s Nat.z≤n) h))
... | suc j′ = cong suc (drwkq-hi [] q b₁ B₂ j′ (Nat.s≤s⁻¹ h))
drwkq-hi (a ∷ B₁') q b₁ B₂ j h with drwkq-hi B₁' q b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁' + q))) (subst (Nat._≤ Fin.toℕ j) assoc2 h)))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ (q + suc b₁) ∷ B₂))
        assoc2 : a + sum B₁' + q ≡ a + (sum B₁' + q)
        assoc2 = Nat.+-assoc a (sum B₁') q
... | inj₂ r = Fin.toℕ-↑ʳ a (drwkq B₁' q b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ (q + suc b₁) ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ (q + suc b₁) ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        assoc2 : a + sum B₁' + q ≡ a + (sum B₁' + q)
        assoc2 = Nat.+-assoc a (sum B₁') q
        boundr : sum B₁' + q Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁' + q) (Fin.toℕ r)
                   (subst (a + (sum B₁' + q) Nat.≤_) jℕ (subst (Nat._≤ Fin.toℕ j) assoc2 h))

-- ============================================================================
--   𝐒rwkq / P1rq / P2rq / P3rq : reconcile Typed's rwk (insert at sum B₁ + q)
--   with the data renaming drwkq on the three splitAt regions (A₁/B/tail).
-- ============================================================================
𝐒rwkq-lo : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
            Fin.toℕ x Nat.< sum B₁ + q →
            Fin.toℕ (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} x) ≡ Fin.toℕ x
𝐒rwkq-lo B₁ B₂ B {q} {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-lt weakenᵣ (sum B₁ + q) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁ + q
        lt′ = subst (Nat._< sum B₁ + q) (sym (Fin.toℕ-cast _ x)) lt

𝐒rwkq-hi : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
            sum B₁ + q Nat.≤ Fin.toℕ x →
            Fin.toℕ (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒rwkq-hi B₁ B₂ B {q} {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-ge weakenᵣ (sum B₁ + q) (Fin.cast _ x) h′
  ■ cong (sum B₁ + q +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ (sum B₁ + q)) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁ + q) (Fin.toℕ x Nat.∸ (sum B₁ + q))
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ + q Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ + q Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

P1rq : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
     SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
     ≡ (drwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1rq B₁ B₂ B {q} {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁ + q
... | yes lt = Fin.toℕ-injective
      ( 𝐒rwkq-lo B₁ B₂ B _ (subst (Nat._< sum B₁ + q) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ drwkq-lo B₁ q b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwkq B₁ q b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwkq B₁ q b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwkq B₁ q b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒rwkq-hi B₁ B₂ B _ (subst (sum B₁ + q Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ drwkq-hi B₁ q b₁ B₂ d h≤) )
  where h≤ : sum B₁ + q Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwkq B₁ q b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwkq B₁ q b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwkq B₁ q b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwkq B₁ q b₁ B₂ d) (sum B)

P2rq : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ} (w : 𝔽 (sum B)) →
     SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m)
     ≡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m
P2rq B₁ B₂ B {q} {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒rwkq-hi B₁ B₂ B _ (subst (sum B₁ + q Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁+q≤ B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ (q + suc b₁) ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc b₁) ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-rwkq B₁ q)
        sB₁+q≤ : ∀ (B₁ : T.BindGroup) → sum B₁ + q Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
        sB₁+q≤ B₁ = subst (sum B₁ + q Nat.≤_) (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                      (Nat.+-monoʳ-≤ (sum B₁) (Nat.≤-trans (Nat.m≤m+n q (suc b₁)) (Nat.m≤m+n (q + suc b₁) (sum B₂))))

P3rq : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ} (u : 𝔽 m) →
     SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u)
     ≡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u
P3rq B₁ B₂ B {q} {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒rwkq-hi B₁ B₂ B _ (subst (sum B₁ + q Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁+q≤ B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-rwkq B₁ q)
        sB₁+q≤ : ∀ (B₁ : T.BindGroup) → sum B₁ + q Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
        sB₁+q≤ B₁ = subst (sum B₁ + q Nat.≤_) (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                      (Nat.+-monoʳ-≤ (sum B₁) (Nat.≤-trans (Nat.m≤m+n q (suc b₁)) (Nat.m≤m+n (q + suc b₁) (sum B₂))))

-- ============================================================================
--   φ-drop bookkeeping: both split blocks have width ≥ 1, so their φ = drop.
-- ============================================================================
ϕq1-drop : ∀ (q : ℕ) → ϕ[ q + 1 ] ≡ U.drop
ϕq1-drop q = cong ϕ[_] (Nat.+-comm q 1)

ϕqsb-drop : ∀ (q b₁ : ℕ) → ϕ[ q + suc b₁ ] ≡ U.drop
ϕqsb-drop q b₁ = cong ϕ[_] (Nat.+-suc q b₁)

-- ============================================================================
--   sinsq : q-generalized sync-insertion renaming (the fresh φ from the split).
--   Inserts at flat position syncs (suc b₁ ∷ B₂) (leaf-side sync count), same as
--   the position-0 sins; the base case coincides with sins definitionally.
-- ============================================================================
sinsq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) {N} →
        syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N →ᵣ syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + N
sinsq []        q b₁ B₂ {N} =
  subst (λ z → syncs ((q + suc b₁) ∷ B₂) + N →ᵣ z)
    (+-suc (syncs ((q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (cong suc (syncs-head-irrel (q + suc b₁) (suc b₁) B₂)))
    (weakenᵣ ↑* syncs ((q + suc b₁) ∷ B₂))
sinsq (a ∷ B₁') q b₁ B₂ {N} =
  subst₂ _→ᵣ_
    (+-suc (syncs (B₁' ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + suc b₁) B₂)))
    (+-suc (syncs (B₁' ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + 1) (suc b₁ ∷ B₂))))
    (sinsq B₁' q b₁ B₂ {suc N})

private
  toℕ-subst𝔽q : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
  toℕ-subst𝔽q refl y = refl

sins-toℕ-hiq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N)) →
              syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ j →
              Fin.toℕ (sinsq B₁ q b₁ B₂ {N} j) ≡ suc (Fin.toℕ j)
sins-toℕ-hiq []        q b₁ B₂ {N} j h =
    toℕ-subst-cod COD (weakenᵣ ↑* SD) j
  ■ toℕ-↑*-ge weakenᵣ SD j h'
  ■ cong (SD +_) (cong suc (toℕ-reduce≥ j h'))
  ■ Nat.+-suc SD (Fin.toℕ j Nat.∸ SD)
  ■ cong suc (Nat.m+[n∸m]≡n h')
  where SD  = syncs ((q + suc b₁) ∷ B₂)
        COD = +-suc SD N ■ cong (_+ N) (cong suc (syncs-head-irrel (q + suc b₁) (suc b₁) B₂))
        h' : SD Nat.≤ Fin.toℕ j
        h' = subst (Nat._≤ Fin.toℕ j) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂) h
sins-toℕ-hiq (a ∷ B₁') q b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sinsq B₁' q b₁ B₂ {suc N}) j
  ■ sins-toℕ-hiq B₁' q b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-subst𝔽q (sym pL) j)) h)
  ■ cong suc (toℕ-subst𝔽q (sym pL) j)
  where
    pL = +-suc (syncs (B₁' ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + 1) (suc b₁ ∷ B₂)))

sins-toℕ-loq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + N)) →
              Fin.toℕ j Nat.< syncs (suc b₁ ∷ B₂) →
              Fin.toℕ (sinsq B₁ q b₁ B₂ {N} j) ≡ Fin.toℕ j
sins-toℕ-loq []        q b₁ B₂ {N} j h =
    toℕ-subst-cod COD (weakenᵣ ↑* SD) j
  ■ toℕ-↑*-lt weakenᵣ SD j h'
  where SD  = syncs ((q + suc b₁) ∷ B₂)
        COD = +-suc SD N ■ cong (_+ N) (cong suc (syncs-head-irrel (q + suc b₁) (suc b₁) B₂))
        h' : Fin.toℕ j Nat.< SD
        h' = subst (Fin.toℕ j Nat.<_) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂) h
sins-toℕ-loq (a ∷ B₁') q b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sinsq B₁' q b₁ B₂ {suc N}) j
  ■ sins-toℕ-loq B₁' q b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (Nat._< syncs (suc b₁ ∷ B₂)) (sym (toℕ-subst𝔽q (sym pL) j)) h)
  ■ toℕ-subst𝔽q (sym pL) j
  where
    pL = +-suc (syncs (B₁' ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (q + 1) (suc b₁ ∷ B₂)))

sD≤q : ∀ (B₁ : BindGroup) (q : ℕ) {b₁ B₂} → syncs (suc b₁ ∷ B₂) Nat.≤ syncs (B₁ ++ (q + suc b₁) ∷ B₂)
sD≤q []        q {b₁} {B₂} = Nat.≤-reflexive (syncs-head-irrel (suc b₁) (q + suc b₁) B₂)
sD≤q (a ∷ B₁') q {b₁} {B₂} =
  subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (syncs-cons a B₁' (q + suc b₁) B₂))
    (Nat.≤-trans (sD≤q B₁' q) (Nat.n≤1+n _))

sins-wkq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) {N} (v : 𝔽 N) →
          sinsq B₁ q b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) v)
          ≡ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) v
sins-wkq B₁ q b₁ B₂ {N} v = Fin.toℕ-injective
  ( sins-toℕ-hiq B₁ q b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) v)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) v))
        (Nat.≤-trans (sD≤q B₁ q) (Nat.m≤m+n (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) (Fin.toℕ v))))
  ■ cong suc (toℕ-weaken*ᵣ (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) v)
  ■ sym (toℕ-weaken*ᵣ (syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwkq B₁ q)) )

-- ============================================================================
--   canonₛ-rwk0q / canonₛ-rwkq : q-generalized canonₛ split naturality.  Off
--   the position-q handle, splitting block (q+suc b₁) → (q+1) ∷ suc b₁ inserts a
--   fresh sync (sinsq) into the canonical substitution.  Mirrors canonₛ-rwk.
-- ============================================================================
-- Ub at a NON-last position ignores e₂ and the width: agrees across widths for
-- equal-toℕ positions (both strictly before the last slot).
Ub-before : ∀ (w1 w2 : ℕ) {N} (e₁ e₂ e₂' : Tm N) (c : 𝔽 N) (p : 𝔽 w1) (p' : 𝔽 w2) →
            suc (Fin.toℕ p) Nat.< w1 → suc (Fin.toℕ p') Nat.< w2 → Fin.toℕ p ≡ Fin.toℕ p' →
            Ub[ w1 ] (e₁ , c , e₂) p ≡ Ub[ w2 ] (e₁ , c , e₂') p'
Ub-before (suc w1)       (suc zero)     e₁ e₂ e₂' c p       0F       lt1 (Nat.s≤s ()) eq
Ub-before (suc zero)     (suc (suc w2)) e₁ e₂ e₂' c 0F      p'       (Nat.s≤s ()) lt2 eq
Ub-before (suc (suc w1)) (suc (suc w2)) e₁ e₂ e₂' c zero    zero     lt1 lt2 eq = refl
Ub-before (suc (suc w1)) (suc (suc w2)) e₁ e₂ e₂' c zero    (suc p') lt1 lt2 ()
Ub-before (suc (suc w1)) (suc (suc w2)) e₁ e₂ e₂' c (suc p) zero     lt1 lt2 ()
Ub-before (suc (suc w1)) (suc (suc w2)) e₁ e₂ e₂' c (suc p) (suc p') lt1 lt2 eq =
  Ub-before (suc w1) (suc w2) * e₂ e₂' c p p' (Nat.s≤s⁻¹ lt1) (Nat.s≤s⁻¹ lt2) (Nat.suc-injective eq)

-- Ub peels a nonempty prefix: at a position ≥ pre, the first pre slots (which
-- carry e₁) are consumed to *, leaving Ub over the residual width.
Ub-after : ∀ (pre w' : ℕ) {N} (e₁ e₂ : Tm N) (c : 𝔽 N) (j : 𝔽 (pre + suc w')) (k : 𝔽 (suc w')) →
           1 Nat.≤ pre → Fin.toℕ j ≡ pre + Fin.toℕ k →
           Ub[ pre + suc w' ] (e₁ , c , e₂) j ≡ Ub[ suc w' ] (* , c , e₂) k
Ub-after (suc zero)      w' e₁ e₂ c (suc j') k _ eq =
  cong (Ub[ suc w' ] (* , c , e₂)) (Fin.toℕ-injective (Nat.suc-injective eq))
Ub-after (suc (suc pre)) w' e₁ e₂ c (suc j') k _ eq =
  Ub-after (suc pre) w' * e₂ c j' k (Nat.s≤s Nat.z≤n) (Nat.suc-injective eq)

-- ============================================================================
--   Front-drop for the in-scope canonₛ (mirrors ComHelpers1.canonₛ-suc-shift,
--   whose canonₛ is a different module).  Prepending one slot to the *-headed
--   head block at a shifted index drops to the smaller head block.
-- ============================================================================
Ub-fdrop : ∀ {N} (m : ℕ) (x : 𝔽 N) (e2 : Tm N) (j : 𝔽 m) →
           Ub[ suc m ] (* , x , e2) (Fin.suc j) ≡ Ub[ m ] (* , x , e2) j
Ub-fdrop zero    x e2 ()
Ub-fdrop (suc m) x e2 j = refl

canonₛ-fdrop : ∀ {N} (b : ℕ) (B : BindGroup) (x : 𝔽 N) (e2 : Tm N) (j : 𝔽 (b + sum B)) →
               canonₛ (suc b ∷ B) (* , x , e2) (Fin.suc j)
               ≡ subst (λ z → Tm (z + N)) (syncs-head-irrel b (suc b) B) (canonₛ (b ∷ B) (* , x , e2) j)
canonₛ-fdrop b []          x e2 j = Ub-fdrop (b + 0) x e2 j
canonₛ-fdrop {N} b (d ∷ B) x e2 j with Fin.splitAt b j
... | inj₁ j′ = cong (λ t → subst Tm (+-suc (syncs (d ∷ B)) N) (t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (d ∷ B))))
                     (Ub-fdrop b (suc x) (` 0F) j′)
... | inj₂ _  = refl

-- ============================================================================
--   sinsq-front : sinsq at (suc q) equals sinsq at q, up to the domain
--   transport that the front-drop of the RHS head block introduces.  Both are
--   fixed by their toℕ action (sins-toℕ-loq/hiq), independent of q.
-- ============================================================================
subst-cong+N : ∀ {N a a'} (σ : a ≡ a') (t : Tm (a + N)) →
               subst (λ z → Tm (z + N)) σ t ≡ subst Tm (cong (_+ N) σ) t
subst-cong+N refl t = refl

toℕ-substᵈ : ∀ {D A A'} (e : A' ≡ A) (ρ : A' →ᵣ D) (v : 𝔽 A) →
             Fin.toℕ (subst (λ w → w →ᵣ D) e ρ v) ≡ Fin.toℕ (ρ (subst 𝔽 (sym e) v))
toℕ-substᵈ refl ρ v = refl

sinsq-front : ∀ (q b₁ : ℕ) (B₂ : BindGroup) {N} (T : Tm (syncs ((q + suc b₁) ∷ B₂) + N)) →
              T ⋯ sinsq [] q b₁ B₂ {N}
              ≡ subst (λ z → Tm (z + N)) (syncs-head-irrel (q + suc b₁) (suc (q + suc b₁)) B₂) T
                ⋯ sinsq [] (suc q) b₁ B₂ {N}
sinsq-front q b₁ B₂ {N} T =
    ⋯-cong T (λ v → Fin.toℕ-injective (sym (ptwise v)))
  ■ sym (subst-⋯-dom-local (cong (_+ N) σ) T (sinsq [] (suc q) b₁ B₂ {N}))
  ■ cong (_⋯ sinsq [] (suc q) b₁ B₂ {N}) (sym (subst-cong+N σ T))
  where
    σ  = syncs-head-irrel (q + suc b₁) (suc (q + suc b₁)) B₂
    sT = syncs (suc b₁ ∷ B₂)
    D  = syncs ((suc q + 1) ∷ suc b₁ ∷ B₂) + N
    e' = sym (cong (_+ N) σ)
    ρ2 : syncs ((q + suc b₁) ∷ B₂) + N →ᵣ D
    ρ2 = subst (λ w → w →ᵣ D) e' (sinsq [] (suc q) b₁ B₂ {N})
    ptwise : ∀ v → Fin.toℕ (ρ2 v) ≡ Fin.toℕ (sinsq [] q b₁ B₂ {N} v)
    ptwise v with Fin.toℕ v Nat.<? sT
    ... | yes lt =
          toℕ-substᵈ e' (sinsq [] (suc q) b₁ B₂ {N}) v
        ■ sins-toℕ-loq [] (suc q) b₁ B₂ (subst 𝔽 (sym e') v)
            (subst (Nat._< sT) (sym (toℕ-subst𝔽q (sym e') v)) lt)
        ■ toℕ-subst𝔽q (sym e') v
        ■ sym (sins-toℕ-loq [] q b₁ B₂ v lt)
    ... | no ¬lt =
          toℕ-substᵈ e' (sinsq [] (suc q) b₁ B₂ {N}) v
        ■ sins-toℕ-hiq [] (suc q) b₁ B₂ (subst 𝔽 (sym e') v)
            (subst (sT Nat.≤_) (sym (toℕ-subst𝔽q (sym e') v)) (Nat.≮⇒≥ ¬lt))
        ■ cong suc (toℕ-subst𝔽q (sym e') v)
        ■ sym (sins-toℕ-hiq [] q b₁ B₂ v (Nat.≮⇒≥ ¬lt))

-- The head-slot sync reconciliation for the cons case: the tail-sync weakening
-- of the head chanTriple (K₀ weakened, off the fresh 0-slot) shifts by one under
-- sinsq, matching the grown tail-sync weakening.  Factored through weakenᵣ so the
-- pointwise renaming equality only touches positions ≥ 1 (where sinsq bumps).
head-sync : ∀ {N} (K₀ : Tm N) (q b₁ c : ℕ) (B : BindGroup) →
  subst Tm (+-suc (syncs (suc b₁ ∷ c ∷ B)) N) (wk K₀ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ c ∷ B)))
  ≡ subst Tm (+-suc (syncs (c ∷ B)) N) (wk K₀ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c ∷ B)))
    ⋯ sinsq [] (suc q) b₁ (c ∷ B) {N}
head-sync {N} K₀ q b₁ c B =
    sym (subst-⋯-cod-local (+-suc sT N) (wk K₀) (weaken* ⦃ Kᵣ ⦄ sT))
  ■ fusion K₀ weakenᵣ ρL
  ■ ⋯-cong K₀ ptwise
  ■ sym (fusion K₀ weakenᵣ ρR)
  ■ sym (fusion (wk K₀) (weaken* ⦃ Kᵣ ⦄ sB) ρR')
  ■ sym (subst-⋯-dom-local (+-suc sB N) (wk K₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB) (sinsq [] (suc q) b₁ (c ∷ B) {N}))
  where
    sT  = syncs (suc b₁ ∷ c ∷ B)
    sB  = syncs (c ∷ B)
    Cd  = syncs ((suc q + 1) ∷ suc b₁ ∷ c ∷ B) + N
    ρL  = subst (λ z → suc N →ᵣ z) (+-suc sT N) (weaken* ⦃ Kᵣ ⦄ sT)
    ρR' = subst (λ w → w →ᵣ Cd) (sym (+-suc sB N)) (sinsq [] (suc q) b₁ (c ∷ B) {N})
    ρR  = weaken* ⦃ Kᵣ ⦄ sB ·ₖ ρR'
    ptwise : ∀ w → (weakenᵣ ·ₖ ρL) w ≡ (weakenᵣ ·ₖ ρR) w
    ptwise w = Fin.toℕ-injective (lhsℕ ■ sym rhsℕ)
      where
        tw≡ : Fin.toℕ (weakenᵣ w) ≡ suc (Fin.toℕ w)
        tw≡ = refl
        lhsℕ : Fin.toℕ ((weakenᵣ ·ₖ ρL) w) ≡ sT + suc (Fin.toℕ w)
        lhsℕ = toℕ-subst-cod (+-suc sT N) (weaken* ⦃ Kᵣ ⦄ sT) (weakenᵣ w)
             ■ toℕ-weaken*ᵣ sT (weakenᵣ w)
             ■ cong (sT +_) tw≡
        pos≡ : Fin.toℕ (subst 𝔽 (sym (sym (+-suc sB N))) (weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ w))) ≡ sB + suc (Fin.toℕ w)
        pos≡ = toℕ-subst𝔽q (sym (sym (+-suc sB N))) (weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ w))
             ■ toℕ-weaken*ᵣ sB (weakenᵣ w)
             ■ cong (sB +_) tw≡
        hbound : sT Nat.≤ Fin.toℕ (subst 𝔽 (sym (sym (+-suc sB N))) (weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ w)))
        hbound = subst (sT Nat.≤_) (sym pos≡)
                   (subst (sT Nat.≤_) (sym (Nat.+-suc sB (Fin.toℕ w)))
                     (Nat.s≤s (Nat.m≤m+n sB (Fin.toℕ w))))
        rhsℕ : Fin.toℕ ((weakenᵣ ·ₖ ρR) w) ≡ sT + suc (Fin.toℕ w)
        rhsℕ = toℕ-substᵈ (sym (+-suc sB N)) (sinsq [] (suc q) b₁ (c ∷ B) {N}) (weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ w))
             ■ sins-toℕ-hiq [] (suc q) b₁ (c ∷ B) (subst 𝔽 (sym (sym (+-suc sB N))) (weaken* ⦃ Kᵣ ⦄ sB (weakenᵣ w))) hbound
             ■ cong suc pos≡

rwk0q-base : ∀ {N} (e₁ e₂ : Tm N) (x : 𝔽 N) (q b₁ : ℕ) (B₂ : BindGroup) →
             canonₛ ((suc q + 1) ∷ suc b₁ ∷ B₂) (e₁ , x , e₂) 0F
             ≡ canonₛ ((suc q + suc b₁) ∷ B₂) (e₁ , x , e₂) 0F ⋯ sinsq [] (suc q) b₁ B₂ {N}
rwk0q-base {N} e₁ e₂ x q b₁ []  =
    ⋯-id (Ub[ suc q + 1 ] (wk e₁ , suc x , ` 0F) 0F) (λ _ → refl)
  ■ Ub-before (suc q + 1) (suc q + suc b₁ + 0) (wk e₁) (` 0F) * (suc x) 0F 0F
      (Nat.s≤s (Nat.m≤n+m 1 q))
      (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.≤-trans (Nat.m≤n+m (suc b₁) q) (Nat.m≤m+n (q + suc b₁) 0)))) refl
  ■ sym (Ub-nat (suc q + suc b₁ + 0) (e₁ , x , *) weakenᵣ 0F)
  ■ sym (cong (_⋯ weakenᵣ)
      (Ub-before (suc q + suc b₁ + 0) (suc q + suc b₁ + 0) e₁ e₂ * x 0F 0F
        (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.≤-trans (Nat.m≤n+m (suc b₁) q) (Nat.m≤m+n (q + suc b₁) 0))))
        (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.≤-trans (Nat.m≤n+m (suc b₁) q) (Nat.m≤m+n (q + suc b₁) 0)))) refl))
rwk0q-base {N} e₁ e₂ x q b₁ (c ∷ B) =
    cong (λ K → subst Tm (+-suc sT N) (K ⋯ weaken* ⦃ Kᵣ ⦄ sT)) headL
  ■ head-sync K₀' q b₁ c B
  ■ cong (λ K → subst Tm (+-suc sB N) (K ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ sinsq [] (suc q) b₁ (c ∷ B) {N}) (sym headR)
  where
    sT  = syncs (suc b₁ ∷ c ∷ B)
    sB  = syncs (c ∷ B)
    K₀' = Ub[ suc q + suc b₁ ] (e₁ , x , *) 0F
    headL : Ub[ suc q + 1 ] (wk e₁ , suc x , ` 0F) 0F ≡ wk K₀'
    headL = Ub-before (suc q + 1) (suc q + suc b₁) (wk e₁) (` 0F) * (suc x) 0F 0F
              (Nat.s≤s (Nat.m≤n+m 1 q)) (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.m≤n+m (suc b₁) q))) refl
          ■ sym (Ub-nat (suc q + suc b₁) (e₁ , x , *) weakenᵣ 0F)
    headR : Ub[ suc q + suc b₁ ] (wk e₁ , suc x , ` 0F) 0F ≡ wk K₀'
    headR = Ub-before (suc q + suc b₁) (suc q + suc b₁) (wk e₁) (` 0F) * (suc x) 0F 0F
              (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.m≤n+m (suc b₁) q)))
              (Nat.s≤s (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.m≤n+m (suc b₁) q))) refl
          ■ sym (Ub-nat (suc q + suc b₁) (e₁ , x , *) weakenᵣ 0F)

canonₛ-rwk0q : ∀ {N} (cc : UChan N) (q b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum ((q + suc b₁) ∷ B₂))) →
             i ≢ ((q ↑ʳ 0F) ↑ˡ sum B₂) →
             canonₛ ((q + 1) ∷ suc b₁ ∷ B₂) cc (drwkq [] q b₁ B₂ i)
             ≡ canonₛ ((q + suc b₁) ∷ B₂) cc i ⋯ sinsq [] q b₁ B₂ {N}
canonₛ-rwk0q {N} cc zero    b₁ B₂ i i≢ =
    canonₛ-rwk0 cc b₁ B₂ i i≢
  ■ subst-Tm-uip (+-suc sD N) COD₀ (canonₛ (suc b₁ ∷ B₂) cc i ⋯ (weakenᵣ ↑* sD))
  ■ sym (subst-⋯-cod-local COD₀ (canonₛ (suc b₁ ∷ B₂) cc i) (weakenᵣ ↑* sD))
  where
    sD = syncs (suc b₁ ∷ B₂)
    COD₀ = +-suc sD N ■ cong (_+ N) (cong suc (syncs-head-irrel (suc b₁) (suc b₁) B₂))
canonₛ-rwk0q {N} (e₁ , x , e₂) (suc q) b₁ B₂ 0F       i≢ = rwk0q-base e₁ e₂ x q b₁ B₂
canonₛ-rwk0q {N} (e₁ , x , e₂) (suc q) b₁ B₂ (suc i′) i≢ =
    frontL
  ■ canonₛ-rwk0q (* , x , e₂) q b₁ B₂ i′ i′≢
  ■ sinsq-front q b₁ B₂ (canonₛ ((q + suc b₁) ∷ B₂) (* , x , e₂) i′)
  ■ sym (cong (_⋯ sinsq [] (suc q) b₁ B₂ {N}) frontR)
  where
    i′≢ : i′ ≢ ((q ↑ʳ 0F) ↑ˡ sum B₂)
    i′≢ e = i≢ (cong Fin.suc e)
    frontL : canonₛ ((suc q + 1) ∷ suc b₁ ∷ B₂) (e₁ , x , e₂) (Fin.suc (drwkq [] q b₁ B₂ i′))
             ≡ canonₛ ((q + 1) ∷ suc b₁ ∷ B₂) (* , x , e₂) (drwkq [] q b₁ B₂ i′)
    frontL = canonₛ-e₁ (q + 1) (suc b₁ ∷ B₂) e₁ * x e₂ (Fin.suc (drwkq [] q b₁ B₂ i′)) (λ ())
           ■ canonₛ-fdrop (q + 1) (suc b₁ ∷ B₂) x e₂ (drwkq [] q b₁ B₂ i′)
    frontR : canonₛ ((suc q + suc b₁) ∷ B₂) (e₁ , x , e₂) (Fin.suc i′)
             ≡ subst (λ z → Tm (z + N)) (syncs-head-irrel (q + suc b₁) (suc (q + suc b₁)) B₂)
                 (canonₛ ((q + suc b₁) ∷ B₂) (* , x , e₂) i′)
    frontR = canonₛ-e₁ (q + suc b₁) B₂ e₁ * x e₂ (Fin.suc i′) (λ ())
           ■ canonₛ-fdrop (q + suc b₁) B₂ x e₂ i′

canonₛ-rwkq : ∀ (B₁ : BindGroup) {N} (cc : UChan N) (q b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)) →
             canonₛ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) cc (drwkq B₁ q b₁ B₂ i)
             ≡ canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) cc i ⋯ sinsq B₁ q b₁ B₂ {N}
canonₛ-rwkq [] {N} cc q b₁ B₂ i i≢ =
    canonₛ-rwk0q cc q b₁ B₂ i (λ i≡ → i≢ (i≡ ■ sym cast≡q))
  where
    cast≡q : Fin.cast (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)) ≡ ((q ↑ʳ 0F) ↑ˡ sum B₂)
    cast≡q = Fin.toℕ-injective
      ( Fin.toℕ-cast (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
      ■ Fin.toℕ-↑ʳ (sum []) ((q ↑ʳ 0F) ↑ˡ sum B₂) )
canonₛ-rwkq (a ∷ []) {N} (e₁ , x , e₂) q b₁ B₂ i i≢
  with canonₛ-rwkq [] {suc N} (` 0F , suc x , wk e₂) q b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sinsq (a ∷ []) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD  = syncs ([] ++ (q + suc b₁) ∷ B₂)
    sDʳ = syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0 = sinsq [] q b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (q + suc b₁) B₂))
    pR = +-suc (syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (q + 1) (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ sDʳ v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hiq [] q b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ sD v))
            (Nat.≤-trans (sD≤q [] q) (Nat.m≤m+n sD (Fin.toℕ v))))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ sDʳ v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwkq [] q)) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ sDʳ
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)) (drwkq [] q b₁ B₂ r) =
      cong (subst Tm SS) (rec r r≢h)
    ■ sym ( cong (_⋯ sinsq (a ∷ []) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD  = syncs ([] ++ (q + suc b₁) ∷ B₂)
    sDʳ = syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0 = sinsq [] q b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (q + suc b₁) B₂))
    pR = +-suc (syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (q + 1) (suc b₁ ∷ B₂)))
    leafM = canonₛ ((q + suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢h : r ≢ Fin.cast (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    r≢h r≡ = i≢ ( sym (Fin.join-splitAt a (sum ([] ++ (q + suc b₁) ∷ B₂)) i)
                ■ cong (Fin.join a (sum ([] ++ (q + suc b₁) ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split-gen a [] (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) )
canonₛ-rwkq (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) q b₁ B₂ i i≢
  with canonₛ-rwkq (d ∷ B₁″) {suc N} (` 0F , suc x , wk e₂) q b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sinsq (a ∷ d ∷ B₁″) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sinsq (d ∷ B₁″) q b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + 1) (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ sDʳ v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hiq (d ∷ B₁″) q b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ sD v))
            (Nat.≤-trans (sD≤q (d ∷ B₁″) q) (Nat.m≤m+n sD (Fin.toℕ v))))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ sDʳ v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwkq (d ∷ B₁″) q)) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ sDʳ
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)) (drwkq (d ∷ B₁″) q b₁ B₂ r) =
      cong (subst Tm SS) (rec r r≢h)
    ■ sym ( cong (_⋯ sinsq (a ∷ d ∷ B₁″) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sinsq (d ∷ B₁″) q b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + 1) (suc b₁ ∷ B₂)))
    leafM = canonₛ ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢h : r ≢ Fin.cast (sym (sum-++ (d ∷ B₁″) ((q + suc b₁) ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    r≢h r≡ = i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) i)
                ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split-gen a (d ∷ B₁″) (q + suc b₁) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) )
