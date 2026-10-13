-- | Effect algebra facts and the bridges between the declarative
--   `Seq⇒Pure` / purity side conditions and their algorithmic counterparts
--   (`A-Pair`'s `p/s ≡ seq → ϵ₂ ≡ ℙ` and `A-App`'s `EffCompat`).
module BorrowedCF.Completeness.Decl.Eff where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Algorithmic using (EffCompat)

open Nat.Variables

------------------------------------------------------------------------
-- The effect lattice (ℙ ≤ϵ 𝕀), re-exported under stable names.

open EffProperties public
  using (x≤x⊔y; x≤y⊔x; x≤y⇒x≤y⊔z; ⊔-mono-≤; ⊔-monoˡ-≤; ⊔-monoʳ-≤; ⊔-lub
        ; ⊔-comm; ⊔-assoc; 𝕀-maximum; ℙ-minimum)

≤ϵ-antisym : ϵ₁ ≤ϵ ϵ₂ → ϵ₂ ≤ϵ ϵ₁ → ϵ₁ ≡ ϵ₂
≤ϵ-antisym ℙ≤ϵ ℙ≤ϵ = refl
≤ϵ-antisym 𝕀≤𝕀 _   = refl

≤ϵ-reflexive : ϵ₁ ≡ ϵ₂ → ϵ₁ ≤ϵ ϵ₂
≤ϵ-reflexive refl = ≤ϵ-refl

-- ℙ is the bottom: anything below it is it.
≤ℙ⇒≡ℙ : ϵ ≤ϵ ℙ → ϵ ≡ ℙ
≤ℙ⇒≡ℙ ℙ≤ϵ = refl

-- Three-way least upper bound, the shape of A-App's effect.
⊔³-lub : ∀ {ϵ₃} → ϵ₁ ≤ϵ ϵ → ϵ₂ ≤ϵ ϵ → ϵ₃ ≤ϵ ϵ → (ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ ϵ₃) ≤ϵ ϵ
⊔³-lub p q r = ⊔-lub (⊔-lub p q) r

⊔ϵ-idem : ∀ ϵ → ϵ ⊔ϵ ϵ ≡ ϵ
⊔ϵ-idem ℙ = refl
⊔ϵ-idem 𝕀 = refl

⊔ϵ-ℙ : ∀ ϵ → ϵ ⊔ϵ ℙ ≡ ϵ
⊔ϵ-ℙ ℙ = refl
⊔ϵ-ℙ 𝕀 = refl

------------------------------------------------------------------------
-- Seq⇒Pure (declarative, T-Pair) ↔ `p/s ≡ seq → ϵ₂ ≡ ℙ` (algorithmic, A-Pair)

seq⇒pure⇒alg : ∀ {p/s} → Seq⇒Pure p/s ϵ₁ ϵ₂ → (p/s ≡ seq → ϵ₂ ≡ ℙ)
seq⇒pure⇒alg par ()
seq⇒pure⇒alg seq _ = refl

-- The other direction is `mk-seq⇒pure` (Context.agda): it weakens the two
-- effects to a pair that is related by Seq⇒Pure and stays below ϵ₁ ⊔ϵ ϵ₂.
alg⇒seq⇒pure :
  ∀ {p/s} → (p/s ≡ seq → ϵ₂ ≡ ℙ) →
  ∃[ ϵ₁′ ] ∃[ ϵ₂′ ] ϵ₁ ≤ϵ ϵ₁′ × ϵ₂ ≤ϵ ϵ₂′ × ϵ₁′ ≤ϵ (ϵ₁ ⊔ϵ ϵ₂) × Seq⇒Pure p/s ϵ₁′ ϵ₂′
alg⇒seq⇒pure = mk-seq⇒pure

-- Under Seq⇒Pure the declarative effect ϵ₁ already dominates the join, which
-- is the effect A-Pair reports.
seq⇒pure-⊔ : ∀ {p/s} → Seq⇒Pure p/s ϵ₁ ϵ₂ → ϵ₁ ⊔ϵ ϵ₂ ≡ ϵ₁
seq⇒pure-⊔ {ϵ₁ = ϵ} par = ⊔ϵ-idem ϵ
seq⇒pure-⊔ {ϵ₁ = ϵ} seq = ⊔ϵ-ℙ ϵ

seq⇒pure-≤ : ∀ {p/s} → Seq⇒Pure p/s ϵ₁ ϵ₂ → (ϵ₁ ⊔ϵ ϵ₂) ≤ϵ ϵ₁
seq⇒pure-≤ sp = ≤ϵ-reflexive (seq⇒pure-⊔ sp)

------------------------------------------------------------------------
-- EffCompat.  `EffCompat d ϵ₂ ϵ₁` is A-App's side condition with ϵ₁ the
-- effect of the FUNCTION and ϵ₂ that of the ARGUMENT: for L the function
-- must be pure (matching T-AppLeft), for R the argument (T-AppRight), and
-- for 𝟙 there is nothing to check (T-AppUnr / T-AppLin).

effCompat-𝟙 : ∀ {d} → d ≡ 𝟙 → EffCompat d ϵ₂ ϵ₁
effCompat-𝟙 refl = tt

effCompat-L : ∀ {d} → d ≡ L → ϵ₁ ≡ ℙ → EffCompat d ϵ₂ ϵ₁
effCompat-L refl refl = refl

effCompat-R : ∀ {d} → d ≡ R → ϵ₂ ≡ ℙ → EffCompat d ϵ₂ ϵ₁
effCompat-R refl refl = refl

-- The forms the main induction uses: the algorithmic effect is only known to
-- be BELOW the declarative one, and the declarative one is ℙ.
effCompat-L≤ : ∀ {d} → d ≡ L → ϵ₁ ≤ϵ ℙ → EffCompat d ϵ₂ ϵ₁
effCompat-L≤ d≡L ≤ℙ = effCompat-L d≡L (≤ℙ⇒≡ℙ ≤ℙ)

effCompat-R≤ : ∀ {d} → d ≡ R → ϵ₂ ≤ϵ ℙ → EffCompat d ϵ₂ ϵ₁
effCompat-R≤ d≡R ≤ℙ = effCompat-R d≡R (≤ℙ⇒≡ℙ ≤ℙ)

-- T-AppUnr gives `Arr.Unr a`, which forces the direction to be 𝟙.
effCompat-unr : (a : Arr) → Arr.Unr a → EffCompat (Arr.dir a) ϵ₂ ϵ₁
effCompat-unr a u = effCompat-𝟙 (Arr.ω⇒𝟙 a u)

-- T-AppLin gives `Arr.Is𝟙 a = lin ≡ 𝟙 × dir ≡ 𝟙`.
effCompat-lin : (a : Arr) → Arr.Is𝟙 a → EffCompat (Arr.dir a) ϵ₂ ϵ₁
effCompat-lin a (_ , d≡𝟙) = effCompat-𝟙 d≡𝟙
