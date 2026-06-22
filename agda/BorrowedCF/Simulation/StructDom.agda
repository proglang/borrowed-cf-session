module BorrowedCF.Simulation.StructDom where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain using (dom)
import BorrowedCF.Context.Substitution as 𝐒
open import BorrowedCF.Simulation.Confine
  using (dom-wk; count; ∉∪⁻; ∉∪⁺; count0⇒∉dom; ∉dom⇒count0; count-wk-zero; count-wk-suc; count-self; +≡0)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (structNSeq; structBinder; structBinderWk; structBinder+²; BindGroup)
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
    eq2 = eq1 ■ 𝐒.weaken*~↑ʳ ⦃ 𝐒.Kᵣ ⦄ k v
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

-- structNSeq m occupies exactly the first m positions: above m, count is 0.
count-structNSeq-ge : ∀ m {n} (z : 𝔽 (m + n)) → m ≤ Fin.toℕ z → count z (structNSeq m) ≡ 0
count-structNSeq-ge zero    z        le        = refl
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
    toℕz≡ = cong Fin.toℕ z≡ ■ cong Fin.toℕ (𝐒.weaken*~↑ʳ ⦃ 𝐒.Kᵣ ⦄ b v) ■ Fin.toℕ-↑ʳ b v
    L≤tv : L ≤ Fin.toℕ v
    L≤tv = Nat.+-cancelˡ-≤ b L (Fin.toℕ v) (subst (b + L ≤_) toℕz≡ le)
count-weaken*-bound b L (α ∥ β) hyp z le =
  cong₂ _+_ (count-weaken*-bound b L α (λ w c → hyp w (λ e → c (proj₁ (+≡0 e)))) z le)
            (count-weaken*-bound b L β (λ w c → hyp w (λ e → c (proj₂ (+≡0 e)))) z le)
count-weaken*-bound b L (α ; β) hyp z le =
  cong₂ _+_ (count-weaken*-bound b L α (λ w c → hyp w (λ e → c (proj₁ (+≡0 e)))) z le)
            (count-weaken*-bound b L β (λ w c → hyp w (λ e → c (proj₂ (+≡0 e)))) z le)

-- structBinder B occupies exactly the first (sum B) positions: above it, count is 0.
count-structBinder-ge : (B : BindGroup) {n : ℕ} (z : 𝔽 (sum B + n))
                      → sum B ≤ Fin.toℕ z → count z (structBinder B) ≡ 0
count-structBinder-ge []        z le = refl
count-structBinder-ge (b ∷ B') {n} z le = cong₂ _+_ part1 part2
  where
    eq : b + (sum B' + n) ≡ (b + sum B') + n
    eq = sym (+-assoc b (sum B') n)
    part1 : count z (cast eq (structNSeq b)) ≡ 0
    part1 = count-cast eq (structNSeq b) z
          ■ count-structNSeq-ge b (Fin.cast (sym eq) z)
              (subst (b ≤_) (sym (toℕ-cast (sym eq) z)) (≤-trans (m≤m+n b (sum B')) le))
    part2 : count z (structBinderWk b B') ≡ 0
    part2 = count-cast eq (structBinder B' 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) z
          ■ count-weaken*-bound b (sum B') (structBinder B') hyp (Fin.cast (sym eq) z)
              (subst (b + sum B' ≤_) (sym (toℕ-cast (sym eq) z)) le)
      where
        hyp : ∀ (w : 𝔽 (sum B' + n)) → count w (structBinder B') ≢ 0 → Fin.toℕ w < sum B'
        hyp w c = ≰⇒> (λ sumB'≤w → c (count-structBinder-ge B' w sumB'≤w))

-- Below b, the shifted struct has multiplicity 0.
count-weaken*-lo : ∀ b {m} (γ : Struct m) (z : 𝔽 (b + m))
                 → Fin.toℕ z < b → count z (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) ≡ 0
count-weaken*-lo b []      z lt = refl
count-weaken*-lo b (` v) z lt with z Fin.≟ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b v
... | no _   = refl
... | yes z≡ = ⊥-elim (<⇒≱ lt (subst (b ≤_) (sym toℕz≡) (m≤m+n b (Fin.toℕ v))))
  where toℕz≡ : Fin.toℕ z ≡ b + Fin.toℕ v
        toℕz≡ = cong Fin.toℕ z≡ ■ cong Fin.toℕ (𝐒.weaken*~↑ʳ ⦃ 𝐒.Kᵣ ⦄ b v) ■ Fin.toℕ-↑ʳ b v
count-weaken*-lo b (α ∥ β) z lt = cong₂ _+_ (count-weaken*-lo b α z lt) (count-weaken*-lo b β z lt)
count-weaken*-lo b (α ; β) z lt = cong₂ _+_ (count-weaken*-lo b α z lt) (count-weaken*-lo b β z lt)

-- A shift by b carries the multiplicity of w to position b ↑ʳ w.
count-weaken*-shift : ∀ b {m} (γ : Struct m) (w : 𝔽 m)
                    → count (b ↑ʳ w) (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) ≡ count w γ
count-weaken*-shift b []      w = refl
count-weaken*-shift b (` v) w with (b ↑ʳ w) Fin.≟ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b v | w Fin.≟ v
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes p | no ¬q = ⊥-elim (¬q (↑ʳ-injective b w v (p ■ 𝐒.weaken*~↑ʳ ⦃ 𝐒.Kᵣ ⦄ b v)))
... | no ¬p | yes q = ⊥-elim (¬p (cong (b ↑ʳ_) q ■ sym (𝐒.weaken*~↑ʳ ⦃ 𝐒.Kᵣ ⦄ b v)))
count-weaken*-shift b (α ∥ β) w = cong₂ _+_ (count-weaken*-shift b α w) (count-weaken*-shift b β w)
count-weaken*-shift b (α ; β) w = cong₂ _+_ (count-weaken*-shift b α w) (count-weaken*-shift b β w)

-- structNSeq m hits each of its first m positions exactly once.
count-structNSeq-lt : ∀ m {n} (z : 𝔽 (m + n)) → Fin.toℕ z < m → count z (structNSeq m) ≡ 1
count-structNSeq-lt (suc m') {n} zero    lt         = cong₂ _+_ (count-self (zero {m' + n})) (count-wk-zero (structNSeq {n} m'))
count-structNSeq-lt (suc m') {n} (suc z') (s≤s lt') = count-wk-suc (structNSeq {n} m') z' ■ count-structNSeq-lt m' z' lt'

-- toℕ of a reduce≥ (local copy; BlockSwap's pulls in clashing Term names).
toℕ-reduce≥ : ∀ {m n} (i : 𝔽 (m + n)) (p : m ≤ Fin.toℕ i) → Fin.toℕ (Fin.reduce≥ i p) ≡ Fin.toℕ i Nat.∸ m
toℕ-reduce≥ {zero}  i       p = refl
toℕ-reduce≥ {suc m} (suc i) p = toℕ-reduce≥ i (s≤s⁻¹ p)

-- structBinder B hits each of its first (sum B) positions exactly once.
count-structBinder-lt : (B : BindGroup) {n : ℕ} (z : 𝔽 (sum B + n))
                      → Fin.toℕ z < sum B → count z (structBinder B) ≡ 1
count-structBinder-lt (b ∷ B') {n} z lt with Fin.toℕ z <? b
... | yes z<b = cong₂ _+_ p1 p2
  where
    eq : b + (sum B' + n) ≡ (b + sum B') + n
    eq = sym (+-assoc b (sum B') n)
    z<b' : Fin.toℕ (Fin.cast (sym eq) z) < b
    z<b' = subst (_< b) (sym (toℕ-cast (sym eq) z)) z<b
    p1 : count z (cast eq (structNSeq b)) ≡ 1
    p1 = count-cast eq (structNSeq b) z ■ count-structNSeq-lt b (Fin.cast (sym eq) z) z<b'
    p2 : count z (structBinderWk b B') ≡ 0
    p2 = count-cast eq (structBinder B' 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) z
       ■ count-weaken*-lo b (structBinder B') (Fin.cast (sym eq) z) z<b'
... | no z≮b = cong₂ _+_ p1 p2
  where
    eq : b + (sum B' + n) ≡ (b + sum B') + n
    eq = sym (+-assoc b (sum B') n)
    cz : 𝔽 (b + (sum B' + n))
    cz = Fin.cast (sym eq) z
    czℕ : Fin.toℕ cz ≡ Fin.toℕ z
    czℕ = toℕ-cast (sym eq) z
    b≤cz : b ≤ Fin.toℕ cz
    b≤cz = subst (b ≤_) (sym czℕ) (≮⇒≥ z≮b)
    w : 𝔽 (sum B' + n)
    w = Fin.reduce≥ cz b≤cz
    bw≡cz : b ↑ʳ w ≡ cz
    bw≡cz = Fin.toℕ-injective (toℕ-↑ʳ b w ■ cong (b +_) (toℕ-reduce≥ cz b≤cz) ■ m+[n∸m]≡n b≤cz)
    b+w≡cz : b + Fin.toℕ w ≡ Fin.toℕ cz
    b+w≡cz = cong (b +_) (toℕ-reduce≥ cz b≤cz) ■ m+[n∸m]≡n b≤cz
    w<sumB' : Fin.toℕ w < sum B'
    w<sumB' = +-cancelˡ-< b (Fin.toℕ w) (sum B')
                (subst (_< b + sum B') (sym b+w≡cz) (subst (_< b + sum B') (sym czℕ) lt))
    p1 : count z (cast eq (structNSeq b)) ≡ 0
    p1 = count-cast eq (structNSeq b) z ■ count-structNSeq-ge b cz b≤cz
    p2 : count z (structBinderWk b B') ≡ 1
    p2 = count-cast eq (structBinder B' 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b) z
       ■ cong (λ u → count u (structBinder B' 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ b)) (sym bw≡cz)
       ■ count-weaken*-shift b (structBinder B') w
       ■ count-structBinder-lt B' w w<sumB'

-- The strengthening precondition for the ν binder: the shifted hole (sum A₁+sum A₂)↑ʳ h
-- avoids the whole bind-context (both structBinders occupy only the first k positions,
-- and the substituted outer context is shifted up by k).
binder-precond : ∀ (A₁ A₂ : BindGroup) {n} (γ : Struct n) (h : 𝔽 n) → h ∉ dom γ
  → ((sum A₁ + sum A₂) ↑ʳ h) ∉
      dom ( structBinder+² (sum A₂) A₁
          ∥ structBinderWk (sum A₁) A₂
          ∥ (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ (sum A₁ + sum A₂)) )
binder-precond A₁ A₂ {n} γ h h∉ =
  ∉∪⁺ (dom (structBinder+² (sum A₂) A₁ ∥ structBinderWk (sum A₁) A₂))
      (dom (γ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ kab))
      (∉∪⁺ (dom (structBinder+² (sum A₂) A₁)) (dom (structBinderWk (sum A₁) A₂)) p1 p2)
      (dom-weaken* kab γ h∉)
  where
    kab : ℕ
    kab = sum A₁ + sum A₂
    khℕ : Fin.toℕ (kab ↑ʳ h) ≡ kab + Fin.toℕ h
    khℕ = toℕ-↑ʳ kab h
    eqA : sum A₁ + (sum A₂ + n) ≡ (sum A₁ + sum A₂) + n
    eqA = sym (+-assoc (sum A₁) (sum A₂) n)
    p1 : (kab ↑ʳ h) ∉ dom (structBinder+² (sum A₂) A₁)
    p1 = count0⇒∉dom (structBinder+² (sum A₂) A₁)
           ( count-cast eqA (structBinder A₁) (kab ↑ʳ h)
           ■ count-structBinder-ge A₁ (Fin.cast (sym eqA) (kab ↑ʳ h))
               (subst (sum A₁ ≤_) (sym (toℕ-cast (sym eqA) (kab ↑ʳ h) ■ khℕ))
                  (≤-trans (m≤m+n (sum A₁) (sum A₂)) (m≤m+n kab (Fin.toℕ h)))) )
    p2 : (kab ↑ʳ h) ∉ dom (structBinderWk (sum A₁) A₂)
    p2 = count0⇒∉dom (structBinderWk (sum A₁) A₂)
           ( count-cast eqA (structBinder A₂ 𝐒.⋯ 𝐒.weaken* ⦃ 𝐒.Kᵣ ⦄ (sum A₁)) (kab ↑ʳ h)
           ■ count-weaken*-bound (sum A₁) (sum A₂) (structBinder A₂) hyp (Fin.cast (sym eqA) (kab ↑ʳ h))
               (subst (kab ≤_) (sym (toℕ-cast (sym eqA) (kab ↑ʳ h) ■ khℕ)) (m≤m+n kab (Fin.toℕ h))) )
      where
        hyp : ∀ (w : 𝔽 (sum A₂ + n)) → count w (structBinder A₂) ≢ 0 → Fin.toℕ w < sum A₂
        hyp w c = ≰⇒> (λ le → c (count-structBinder-ge A₂ w le))
