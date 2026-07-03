module BorrowedCF.Simulation.StructDom where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain using (dom)
import BorrowedCF.Context.Substitution as 𝐒
open import BorrowedCF.Simulation.Confine
  using (dom-wk; count; ∉∪⁻; ∉∪⁺; count0⇒∉dom; ∉dom⇒count0; count-wk-zero; count-wk-suc; count-self; +≡0)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (structNSeq; structBinder; BindGroup)
open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; ∉⊥; x∈p∪q⁻)
open import Data.Fin.Base using (_↑ʳ_)
open import Data.Fin.Properties using (↑ʳ-injective; toℕ-cast; toℕ-↑ʳ)

open Nat.Variables
open Nat using (_≤_; _<_; _<?_; z≤n; s≤s; s≤s⁻¹; +-assoc; m≤m+n; ≤-trans; ≰⇒>; ≮⇒≥; +-cancelˡ-≤; +-cancelˡ-<; ≤⇒≯; <⇒≱; m+[n∸m]≡n)

-- A weaken* by k shifts every domain index up by k: a non-shifted variable
-- `x` lands at `k ↑ʳ x`, away from anything below k.
dom-weaken* : ∀ k (γ : Struct n) {x : 𝔽 n}
            → x ∉ dom γ → (k ↑ʳ x) ∉ dom (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k)
dom-weaken* k []      x∉ = ∉⊥
dom-weaken* k (` v) {x} x∉ k↑x∈ = x≢v (↑ʳ-injective k x v eq2)
  where
    x≢v : x ≢ v
    x≢v x≡v = x∉ (subst (λ z → x ∈ ⁅ z ⁆) x≡v (x∈⁅x⁆ x))
    eq1 : k ↑ʳ x ≡ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k v
    eq1 = x∈⁅y⁆⇒x≡y (𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k v) k↑x∈
    eq2 : k ↑ʳ x ≡ k ↑ʳ v
    eq2 = eq1 ■ 𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ k v
dom-weaken* k (α ∥ β) x∉ =
  let xa , xb = ∉∪⁻ x∉
  in λ k↑x∈ → [ dom-weaken* k α xa , dom-weaken* k β xb ]′
       (x∈p∪q⁻ (dom (α 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k)) (dom (β 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k)) k↑x∈)
dom-weaken* k (α ; β) x∉ =
  let xa , xb = ∉∪⁻ x∉
  in λ k↑x∈ → [ dom-weaken* k α xa , dom-weaken* k β xb ]′
       (x∈p∪q⁻ (dom (α 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k)) (dom (β 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ k)) k↑x∈)

-- count under a (toℕ-preserving) cast: it merely re-indexes the variable.
count-cast : ∀ {m m'} (eq : m ≡ m') (γ : Struct m) (z : 𝔽 m')
           → count z (cast eq γ) ≡ count (Fin.cast (sym eq) z) γ
count-cast eq []      z = refl
count-cast eq (` v) z with z Fin.≟ Fin.cast eq v | Fin.cast (sym eq) z Fin.≟ v
... | yes _   | yes _  = refl
... | no  _   | no  _  = refl
... | yes p   | no ¬q  = ⊥-elim (¬q (cong (Fin.cast (sym eq)) p ■ cc1))
  where cc1 : Fin.cast (sym eq) (Fin.cast eq v) ≡ v
        cc1 = Fin.toℕ-injective (toℕ-cast (sym eq) (Fin.cast eq v) ■ toℕ-cast eq v)
... | no ¬p   | yes q  = ⊥-elim (¬p (sym cc2 ■ cong (Fin.cast eq) q))
  where cc2 : Fin.cast eq (Fin.cast (sym eq) z) ≡ z
        cc2 = Fin.toℕ-injective (toℕ-cast eq (Fin.cast (sym eq) z) ■ toℕ-cast (sym eq) z)
count-cast eq (α ∥ β) z = cong₂ _+_ (count-cast eq α z) (count-cast eq β z)
count-cast eq (α ; β) z = cong₂ _+_ (count-cast eq α z) (count-cast eq β z)

-- structNSeq m occupies exactly the first m positions.  Now z ∈ 𝔽 m, so
-- ` m ≤ toℕ z ` is unsatisfiable (toℕ z < m always): the lemma is vacuous, but
-- kept so the structBinder lemmas can discharge their out-of-range branch.
count-structNSeq-ge : ∀ m (z : 𝔽 m) → m ≤ Fin.toℕ z → count z (structNSeq m) ≡ 0
count-structNSeq-ge (suc m') zero     ()
count-structNSeq-ge (suc m') (suc z') (s≤s le') =
  count-wk-suc (structNSeq m') z' ■ count-structNSeq-ge m' z' le'

-- A struct that occupies positions < L, shifted up by b, occupies < b + L:
-- above b + L the multiplicity is 0.
count-weaken*-bound : ∀ b {m} (L : ℕ) (γ : Struct m)
  → (∀ (w : 𝔽 m) → count w γ ≢ 0 → Fin.toℕ w < L)
  → (z : 𝔽 (b + m)) → b + L ≤ Fin.toℕ z → count z (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) ≡ 0
count-weaken*-bound b L []      hyp z le = refl
count-weaken*-bound b L (` v) hyp z le with z Fin.≟ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b v
... | no _    = refl
... | yes z≡  = ⊥-elim (Nat.≤⇒≯ L≤tv tv<L)
  where
    tv<L : Fin.toℕ v < L
    tv<L = hyp v (λ c0 → bust (sym (count-self v) ■ c0))
      where bust : 1 ≡ 0 → ⊥
            bust ()
    toℕz≡ : Fin.toℕ z ≡ b + Fin.toℕ v
    toℕz≡ = cong Fin.toℕ z≡ ■ cong Fin.toℕ (𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ b v) ■ Fin.toℕ-↑ʳ b v
    L≤tv : L ≤ Fin.toℕ v
    L≤tv = Nat.+-cancelˡ-≤ b L (Fin.toℕ v) (subst (b + L ≤_) toℕz≡ le)
count-weaken*-bound b L (α ∥ β) hyp z le =
  cong₂ _+_ (count-weaken*-bound b L α (λ w c → hyp w (λ e → c (proj₁ (+≡0 e)))) z le)
            (count-weaken*-bound b L β (λ w c → hyp w (λ e → c (proj₂ (+≡0 e)))) z le)
count-weaken*-bound b L (α ; β) hyp z le =
  cong₂ _+_ (count-weaken*-bound b L α (λ w c → hyp w (λ e → c (proj₁ (+≡0 e)))) z le)
            (count-weaken*-bound b L β (λ w c → hyp w (λ e → c (proj₂ (+≡0 e)))) z le)

-- count under a right-weakening ` δ ⋯ᵣ wkʳ M `.  `wkʳ M` is ` _↑ˡ M `, which
-- is toℕ-preserving: a leaf ` v ` lands at ` v ↑ˡ M `.
-- (a) probing at an injection ` z₀ ↑ˡ M ` reads the original multiplicity.
count-⋯ᵣwkʳ-↑ˡ : ∀ {K} M (δ : Struct K) (z₀ : 𝔽 K)
               → count (z₀ ↑ˡ M) (δ 𝐒.⋯ᵣ 𝐒.wkʳ M) ≡ count z₀ δ
count-⋯ᵣwkʳ-↑ˡ M []      z₀ = refl
count-⋯ᵣwkʳ-↑ˡ M (` v) z₀ with (z₀ ↑ˡ M) Fin.≟ (v ↑ˡ M) | z₀ Fin.≟ v
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes p | no ¬q = ⊥-elim (¬q (↑ˡ-injective M z₀ v p))
... | no ¬p | yes q = ⊥-elim (¬p (cong (_↑ˡ M) q))
count-⋯ᵣwkʳ-↑ˡ M (α ∥ β) z₀ = cong₂ _+_ (count-⋯ᵣwkʳ-↑ˡ M α z₀) (count-⋯ᵣwkʳ-↑ˡ M β z₀)
count-⋯ᵣwkʳ-↑ˡ M (α ; β) z₀ = cong₂ _+_ (count-⋯ᵣwkʳ-↑ˡ M α z₀) (count-⋯ᵣwkʳ-↑ˡ M β z₀)

-- (b) probing above the original width (a ` K ↑ʳ y ` index) reads 0.
count-⋯ᵣwkʳ-↑ʳ : ∀ {K} M (δ : Struct K) (y : 𝔽 M)
               → count (K ↑ʳ y) (δ 𝐒.⋯ᵣ 𝐒.wkʳ M) ≡ 0
count-⋯ᵣwkʳ-↑ʳ M []      y = refl
count-⋯ᵣwkʳ-↑ʳ {K} M (` v) y with (K ↑ʳ y) Fin.≟ (v ↑ˡ M)
... | no  _ = refl
... | yes p = ⊥-elim (↑ˡ≢↑ʳ (sym p))
count-⋯ᵣwkʳ-↑ʳ M (α ∥ β) y = cong₂ _+_ (count-⋯ᵣwkʳ-↑ʳ M α y) (count-⋯ᵣwkʳ-↑ʳ M β y)
count-⋯ᵣwkʳ-↑ʳ M (α ; β) y = cong₂ _+_ (count-⋯ᵣwkʳ-↑ʳ M α y) (count-⋯ᵣwkʳ-↑ʳ M β y)

-- ` δ ⋯ᵣ wkˡ b ` agrees with ` δ ⋯ weaken* b ` (weaken*~wkˡ), so the
-- weaken*-count lemmas transport across.
⋯ᵣwkˡ≡⋯weaken* : ∀ b {m} (δ : Struct m) → δ 𝐒.⋯ᵣ 𝐒.wkˡ b ≡ δ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b
⋯ᵣwkˡ≡⋯weaken* b δ = 𝐒.⋯-cong δ (λ x → sym (𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ b x))

-- structBinder B occupies exactly the first (sum B) positions: above it, count is 0.
count-structBinder-ge : (B : BindGroup) (z : 𝔽 (sum B))
                      → sum B ≤ Fin.toℕ z → count z (structBinder B) ≡ 0
count-structBinder-ge []        ()
count-structBinder-ge (b ∷ B') z le with Fin.splitAt b z in seq
... | inj₁ z₀ = ⊥-elim (<⇒≱ z<b (≤-trans (m≤m+n b (sum B')) le))
  where
    z≡ : z₀ ↑ˡ sum B' ≡ z
    z≡ = Fin.splitAt⁻¹-↑ˡ seq
    z<b : Fin.toℕ z < b
    z<b = subst (_< b) (sym (Fin.toℕ-↑ˡ z₀ (sum B')) ■ cong Fin.toℕ z≡) (Fin.toℕ<n z₀)
... | inj₂ y = cong₂ _+_ part1 part2
  where
    z≡ : z ≡ b ↑ʳ y
    z≡ = sym (Fin.splitAt⁻¹-↑ʳ {m = b} {n = sum B'} seq)
    part1 : count z (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B')) ≡ 0
    part1 = cong (λ u → count u (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B'))) z≡
          ■ count-⋯ᵣwkʳ-↑ʳ (sum B') (structNSeq b) y
    part2 : count z (structBinder B' 𝐒.⋯ᵣ 𝐒.wkˡ b) ≡ 0
    part2 = cong (count z) (⋯ᵣwkˡ≡⋯weaken* b (structBinder B'))
          ■ count-weaken*-bound b (sum B') (structBinder B') hyp z le
      where
        hyp : ∀ (w : 𝔽 (sum B')) → count w (structBinder B') ≢ 0 → Fin.toℕ w < sum B'
        hyp w c = ≰⇒> (λ sumB'≤w → c (count-structBinder-ge B' w sumB'≤w))

-- Below b, the shifted struct has multiplicity 0.
count-weaken*-lo : ∀ b {m} (γ : Struct m) (z : 𝔽 (b + m))
                 → Fin.toℕ z < b → count z (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) ≡ 0
count-weaken*-lo b []      z lt = refl
count-weaken*-lo b (` v) z lt with z Fin.≟ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b v
... | no _   = refl
... | yes z≡ = ⊥-elim (<⇒≱ lt (subst (b ≤_) (sym toℕz≡) (m≤m+n b (Fin.toℕ v))))
  where toℕz≡ : Fin.toℕ z ≡ b + Fin.toℕ v
        toℕz≡ = cong Fin.toℕ z≡ ■ cong Fin.toℕ (𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ b v) ■ Fin.toℕ-↑ʳ b v
count-weaken*-lo b (α ∥ β) z lt = cong₂ _+_ (count-weaken*-lo b α z lt) (count-weaken*-lo b β z lt)
count-weaken*-lo b (α ; β) z lt = cong₂ _+_ (count-weaken*-lo b α z lt) (count-weaken*-lo b β z lt)

-- A shift by b carries the multiplicity of w to position b ↑ʳ w.
count-weaken*-shift : ∀ b {m} (γ : Struct m) (w : 𝔽 m)
                    → count (b ↑ʳ w) (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) ≡ count w γ
count-weaken*-shift b []      w = refl
count-weaken*-shift b (` v) w with (b ↑ʳ w) Fin.≟ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b v | w Fin.≟ v
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes p | no ¬q = ⊥-elim (¬q (↑ʳ-injective b w v (p ■ 𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ b v)))
... | no ¬p | yes q = ⊥-elim (¬p (cong (b ↑ʳ_) q ■ sym (𝐒.weaken*~wkˡ ⦃ 𝐒.Kᵣ ⦄ b v)))
count-weaken*-shift b (α ∥ β) w = cong₂ _+_ (count-weaken*-shift b α w) (count-weaken*-shift b β w)
count-weaken*-shift b (α ; β) w = cong₂ _+_ (count-weaken*-shift b α w) (count-weaken*-shift b β w)

-- structNSeq m hits each of its first m positions exactly once.
count-structNSeq-lt : ∀ m (z : 𝔽 m) → Fin.toℕ z < m → count z (structNSeq m) ≡ 1
count-structNSeq-lt (suc m') zero    lt         = cong₂ _+_ (count-self (zero {m'})) (count-wk-zero (structNSeq m'))
count-structNSeq-lt (suc m') (suc z') (s≤s lt') = count-wk-suc (structNSeq m') z' ■ count-structNSeq-lt m' z' lt'

-- toℕ of a reduce≥ (local copy; BlockSwap's pulls in clashing Term names).
toℕ-reduce≥ : ∀ {m n} (i : 𝔽 (m + n)) (p : m ≤ Fin.toℕ i) → Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ m
toℕ-reduce≥ {zero}  i       p = refl
toℕ-reduce≥ {suc m} (suc i) p = toℕ-reduce≥ i (s≤s⁻¹ p)

-- structBinder B hits each of its first (sum B) positions exactly once.
count-structBinder-lt : (B : BindGroup) (z : 𝔽 (sum B))
                      → Fin.toℕ z < sum B → count z (structBinder B) ≡ 1
count-structBinder-lt (b ∷ B') z lt with Fin.splitAt b z in seq
... | inj₁ z₀ = cong₂ _+_ p1 p2
  where
    z≡ : z₀ ↑ˡ sum B' ≡ z
    z≡ = Fin.splitAt⁻¹-↑ˡ seq
    z<b : Fin.toℕ z < b
    z<b = subst (_< b) (sym (Fin.toℕ-↑ˡ z₀ (sum B')) ■ cong Fin.toℕ z≡) (Fin.toℕ<n z₀)
    z₀<b : Fin.toℕ z₀ < b
    z₀<b = Fin.toℕ<n z₀
    p1 : count z (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B')) ≡ 1
    p1 = cong (λ u → count u (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B'))) (sym z≡)
       ■ count-⋯ᵣwkʳ-↑ˡ (sum B') (structNSeq b) z₀
       ■ count-structNSeq-lt b z₀ z₀<b
    p2 : count z (structBinder B' 𝐒.⋯ᵣ 𝐒.wkˡ b) ≡ 0
    p2 = cong (count z) (⋯ᵣwkˡ≡⋯weaken* b (structBinder B'))
       ■ count-weaken*-lo b (structBinder B') z z<b
... | inj₂ y = cong₂ _+_ p1 p2
  where
    bw≡z : b ↑ʳ y ≡ z
    bw≡z = Fin.splitAt⁻¹-↑ʳ seq
    b+y≡z : b + Fin.toℕ y ≡ Fin.toℕ z
    b+y≡z = sym (toℕ-↑ʳ b y) ■ cong Fin.toℕ bw≡z
    w<sumB' : Fin.toℕ y < sum B'
    w<sumB' = +-cancelˡ-< b (Fin.toℕ y) (sum B')
                (subst (_< b + sum B') (sym b+y≡z) lt)
    p1 : count z (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B')) ≡ 0
    p1 = cong (λ u → count u (structNSeq b 𝐒.⋯ᵣ 𝐒.wkʳ (sum B'))) (sym bw≡z)
       ■ count-⋯ᵣwkʳ-↑ʳ (sum B') (structNSeq b) y
    p2 : count z (structBinder B' 𝐒.⋯ᵣ 𝐒.wkˡ b) ≡ 1
    p2 = cong (count z) (⋯ᵣwkˡ≡⋯weaken* b (structBinder B'))
       ■ cong (λ u → count u (structBinder B' 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b)) (sym bw≡z)
       ■ count-weaken*-shift b (structBinder B') y
       ■ count-structBinder-lt B' y w<sumB'

-- The strengthening precondition for the ν binder: the shifted hole (sum A₁+sum A₂)↑ʳ h
-- avoids the whole bind-context (both structBinders occupy only the first k positions,
-- and the substituted outer context is shifted up by k).
binder-precond : ∀ (A₁ A₂ : BindGroup) {n} (γ : Struct n) (h : 𝔽 n) → h ∉ dom γ
  → ((sum A₁ + sum A₂) ↑ʳ h) ∉
      dom ( (structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂) 𝐒.⋯ᵣ 𝐒.wkʳ n)
          ∥ (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁) 𝐒.⋯ᵣ 𝐒.wkʳ n)
          ∥ (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ (sum A₁ + sum A₂)) )
binder-precond A₁ A₂ {n} γ h h∉ =
  ∉∪⁺ (dom ((structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂) 𝐒.⋯ᵣ 𝐒.wkʳ n)
            ∥ (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁) 𝐒.⋯ᵣ 𝐒.wkʳ n)))
      (dom (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ kab))
      (∉∪⁺ (dom (structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂) 𝐒.⋯ᵣ 𝐒.wkʳ n))
           (dom (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁) 𝐒.⋯ᵣ 𝐒.wkʳ n)) p1 p2)
      (dom-weaken* kab γ h∉)
  where
    kab : ℕ
    kab = sum A₁ + sum A₂
    p1 : (kab ↑ʳ h) ∉ dom (structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂) 𝐒.⋯ᵣ 𝐒.wkʳ n)
    p1 = count0⇒∉dom (structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂) 𝐒.⋯ᵣ 𝐒.wkʳ n)
           (count-⋯ᵣwkʳ-↑ʳ n (structBinder A₁ 𝐒.⋯ᵣ 𝐒.wkʳ (sum A₂)) h)
    p2 : (kab ↑ʳ h) ∉ dom (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁) 𝐒.⋯ᵣ 𝐒.wkʳ n)
    p2 = count0⇒∉dom (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁) 𝐒.⋯ᵣ 𝐒.wkʳ n)
           (count-⋯ᵣwkʳ-↑ʳ n (structBinder A₂ 𝐒.⋯ᵣ 𝐒.wkˡ (sum A₁)) h)
