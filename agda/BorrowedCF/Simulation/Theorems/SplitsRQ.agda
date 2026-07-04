module BorrowedCF.Simulation.Theorems.SplitsRQ where

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

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import BorrowedCF.Simulation.BlockPerm
  using ( toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt )
open import BorrowedCF.Processes.Bisim using (syncs)

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
            Fin.toℕ (TR.SplitRenamings.rwk B₁ B₂ B {q} {b₁} {m} x) ≡ Fin.toℕ x
𝐒rwkq-lo B₁ B₂ B {q} {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-lt weakenᵣ (sum B₁ + q) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁ + q
        lt′ = subst (Nat._< sum B₁ + q) (sym (Fin.toℕ-cast _ x)) lt

𝐒rwkq-hi : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
            sum B₁ + q Nat.≤ Fin.toℕ x →
            Fin.toℕ (TR.SplitRenamings.rwk B₁ B₂ B {q} {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒rwkq-hi B₁ B₂ B {q} {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-ge weakenᵣ (sum B₁ + q) (Fin.cast _ x) h′
  ■ cong (sum B₁ + q +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ (sum B₁ + q)) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁ + q) (Fin.toℕ x Nat.∸ (sum B₁ + q))
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ + q Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ + q Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

P1rq : ∀ (B₁ B₂ B : T.BindGroup) {q b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))) →
     TR.SplitRenamings.rwk B₁ B₂ B {q} {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
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
     TR.SplitRenamings.rwk B₁ B₂ B {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m)
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
     TR.SplitRenamings.rwk B₁ B₂ B {q} {b₁} {m} ((sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u)
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
