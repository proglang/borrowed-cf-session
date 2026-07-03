module BorrowedCF.Simulation.Strengthen where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types using (𝕋; Eff; Arr; Dir; 𝟙; L; R)
open import BorrowedCF.Context.Base using (Struct; Ctx)
open import BorrowedCF.Context.Domain using (dom)
open import BorrowedCF.Context.Domain using (≼⇒dom⊆)
open import BorrowedCF.Simulation.Confine
open import BorrowedCF.Simulation.StructDom using (binder-precond)
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈p∪q⁺)
open import Data.Fin.Base using (punchIn; punchOut; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties using (punchIn-punchOut; ↑ʳ-injective; join-splitAt)
open import Data.Sum using (inj₁; inj₂)

open Nat.Variables
open Fin.Patterns

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v p q}
      → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl

pin : (x : 𝔽 (suc n)) → punchIn (suc x) ≗ (punchIn x ↑)
pin x 0F      = refl
pin x (suc j) = refl

pin² : (x : 𝔽 (suc n)) → punchIn (suc (suc x)) ≗ (punchIn x ↑ ↑)
pin² x j = pin (suc x) j ■ (pin x ~↑) j

-- Lifting a renaming by j leaves the first j positions untouched (↑ˡ region)
-- and shifts the rest (↑ʳ region) — the two facts that let us invert the
-- j-lifted thinning at a variable.
↑*-↑ˡ : ∀ {a b} (ρ : a →ᵣ b) j (y : 𝔽 j) → (ρ ↑* j) (y ↑ˡ a) ≡ y ↑ˡ b
↑*-↑ˡ ρ (suc j') 0F       = refl
↑*-↑ˡ ρ (suc j') (suc y') = cong suc (↑*-↑ˡ ρ j' y')

↑*-↑ʳ : ∀ {a b} (ρ : a →ᵣ b) j (w : 𝔽 a) → (ρ ↑* j) (j ↑ʳ w) ≡ j ↑ʳ ρ w
↑*-↑ʳ ρ zero     w = refl
↑*-↑ʳ ρ (suc j') w = cong suc (↑*-↑ʳ ρ j' w)

-- An "inverter" for a renaming ρ that misses position h: every var ≠ h has a
-- preimage.  This is the structure that lets a typing derivation factor through
-- ρ.  Passing ρ abstractly (rather than a fixed `punchIn`) means binders compose
-- DEFINITIONALLY (ρ ↑, ρ ↑* j) with no +-suc / +-assoc transport.
Inverter : ∀ {k N} → (k →ᵣ N) → 𝔽 N → Set
Inverter {k} {N} ρ h = (y : 𝔽 N) → y ≢ h → Σ[ y₀ ∈ 𝔽 k ] ρ y₀ ≡ y

inv↑ : ∀ {k N} {ρ : k →ᵣ N} {h : 𝔽 N} → Inverter ρ h → Inverter (ρ ↑) (suc h)
inv↑ inv 0F       ne = 0F , refl
inv↑ inv (suc y') ne = let y₀' , eq = inv y' (λ p → ne (cong suc p)) in suc y₀' , cong suc eq

inv↑* : ∀ {k N} {ρ : k →ᵣ N} {h : 𝔽 N} j → Inverter ρ h → Inverter (ρ ↑* j) (j ↑ʳ h)
inv↑* zero     inv = inv
inv↑* (suc j') inv = inv↑ (inv↑* j' inv)

-- A concrete thinning that skips a position p in scope N (N ≡ p + suc rest):
-- ρ⁻ = cast ∘ (weakenᵣ ↑* p), with both an Inverter and the skip property.
inv-weakenᵣ : ∀ {n} → Inverter (weakenᵣ {n}) zero
inv-weakenᵣ zero     ne = ⊥-elim (ne refl)
inv-weakenᵣ (suc y') ne = y' , refl

skip-weakenᵣ : ∀ {n} (y : 𝔽 n) → weakenᵣ y ≢ zero
skip-weakenᵣ y ()

skip↑ : ∀ {k N} {ρ : k →ᵣ N} {h : 𝔽 N} → (∀ y → ρ y ≢ h) → (∀ y → (ρ ↑) y ≢ suc h)
skip↑ sk zero     ()
skip↑ sk (suc y') p = sk y' (Fin.suc-injective p)

skip↑* : ∀ {k N} {ρ : k →ᵣ N} {h : 𝔽 N} j → (∀ y → ρ y ≢ h) → (∀ y → (ρ ↑* j) y ≢ j ↑ʳ h)
skip↑* zero     sk = sk
skip↑* (suc j') sk = skip↑ (skip↑* j' sk)

cast-inj : ∀ {m n} (eq : m ≡ n) {a b : 𝔽 m} → Fin.cast eq a ≡ Fin.cast eq b → a ≡ b
cast-inj eq {a} {b} p =
  Fin.toℕ-injective (sym (Fin.toℕ-cast eq a) ■ cong Fin.toℕ p ■ Fin.toℕ-cast eq b)

castLR : ∀ {m n} (eq : m ≡ n) (y : 𝔽 n) → Fin.cast eq (Fin.cast (sym eq) y) ≡ y
castLR eq y = Fin.toℕ-injective (Fin.toℕ-cast eq (Fin.cast (sym eq) y) ■ Fin.toℕ-cast (sym eq) y)

Inverter-cast : ∀ {k m n} (eq : m ≡ n) {ρ : k →ᵣ m} {h : 𝔽 m}
  → Inverter ρ h → Inverter (λ y → Fin.cast eq (ρ y)) (Fin.cast eq h)
Inverter-cast eq {ρ} {h} inv y y≢ =
  let y₀ , e = inv (Fin.cast (sym eq) y) (λ p → y≢ (sym (castLR eq y) ■ cong (Fin.cast eq) p))
  in y₀ , (cong (Fin.cast eq) e ■ castLR eq y)

skip-cast : ∀ {k m n} (eq : m ≡ n) {ρ : k →ᵣ m} {h : 𝔽 m}
  → (∀ y → ρ y ≢ h) → (∀ y → Fin.cast eq (ρ y) ≢ Fin.cast eq h)
skip-cast eq sk y p = sk y (cast-inj eq p)

mk-thin : ∀ {N} p rest (eq : p + suc rest ≡ N)
  → Σ[ ρ⁻ ∈ (p + rest) →ᵣ N ]
      Inverter ρ⁻ (Fin.cast eq (p ↑ʳ zero)) × (∀ y → ρ⁻ y ≢ Fin.cast eq (p ↑ʳ zero))
mk-thin p rest eq =
  (λ y → Fin.cast eq ((weakenᵣ ↑* p) y)) ,
  Inverter-cast eq (inv↑* p inv-weakenᵣ) ,
  skip-cast eq (skip↑* p skip-weakenᵣ)

-- Generalised strengthening: factor a typed expression through any renaming ρ
-- that misses h (witnessed by an Inverter).  Binders recurse with ρ ↑ / ρ ↑ ↑,
-- which compose DEFINITIONALLY — no +-suc/+-assoc transport anywhere.
strengthen-Tm-gen : {N : ℕ} {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff}
  → Γ ; γ ⊢ e ∶ T ∣ ϵ → {k : ℕ} (ρ : k →ᵣ N) (h : 𝔽 N)
  → Inverter ρ h → h ∉ dom γ → Σ[ e₀ ∈ Tm k ] e ≡ e₀ ⋯ ρ
strengthen-Tm-gen (T-Const {c = c} _) ρ h inv h∉ = K c , refl
strengthen-Tm-gen (T-Var x′ _) ρ h inv h∉ =
  let y₀ , yeq = inv x′ (λ x′≡h → h∉ (subst (λ z → h ∈ ⁅ z ⁆) (sym x′≡h) (x∈⁅x⁆ h)))
  in ` y₀ , cong `_ (sym yeq)
strengthen-Tm-gen {γ = γ} (T-Abs {a = a} _ _ ⊢e) ρ h inv h∉ =
  let e₀ , eq = strengthen-Tm-gen ⊢e (ρ ↑) (suc h) (inv↑ inv) (∉-abs-ctx-Dir (Arr.dir a) γ h∉)
  in ƛ (Arr.dir a) e₀ , cong (ƛ (Arr.dir a)) eq
strengthen-Tm-gen {γ = γ} (T-AbsRec _ _ ⊢e) ρ h inv h∉ =
  let e₀ , eq = strengthen-Tm-gen ⊢e (ρ ↑ ↑) (suc (suc h)) (inv↑ (inv↑ inv)) (∉-absrec-ctx γ h∉)
  in μ (ƛ 𝟙 e₀) , cong μ (cong (ƛ 𝟙) eq)
strengthen-Tm-gen (T-AppUnr _ _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm-gen (T-AppLin _ _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm-gen (T-AppLeft _ _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₂ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₁ x∈)))
  in e₁₀ ·ᴸ e₂₀ , cong₂ (_·⟨ L ⟩_) eq₁ eq₂
strengthen-Tm-gen (T-AppRight _ _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·ᴿ e₂₀ , cong₂ (_·⟨ R ⟩_) eq₁ eq₂
strengthen-Tm-gen (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let x₁ , x₂ = ∉-join-biased⁻ p/s γ₁ γ₂ h∉
      e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv x₁
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv x₂
  in e₁₀ ⊗ e₂₀ , cong₂ _⊗_ eq₁ eq₂
strengthen-Tm-gen (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ h∉
      e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv x₁
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ (ρ ↑) (suc h) (inv↑ inv) (∉-abs-ctx-PS p/s γ₂ x₂)
  in `let e₁₀ `in e₂₀ , cong₂ `let_`in_ eq₁ eq₂
strengthen-Tm-gen (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let x₁ , x₂ = ∉∪⁻ h∉
      e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv x₁
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ ρ h inv x₂
  in e₁₀ ; e₂₀ , cong₂ _;_ eq₁ eq₂
strengthen-Tm-gen (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ h∉
      e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ ρ h inv x₁
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ (ρ ↑ ↑) (suc (suc h)) (inv↑ (inv↑ inv)) (∉-letpair-ctx p/s d γ₂ x₂)
  in `let⊗ e₁₀ `in e₂₀ , cong₂ `let⊗_`in_ eq₁ eq₂
strengthen-Tm-gen (T-Inj {i = i} ⊢e) ρ h inv h∉ =
  let e₀ , eq = strengthen-Tm-gen ⊢e ρ h inv h∉
  in `inj i e₀ , cong (`inj i) eq
strengthen-Tm-gen (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) ρ h inv h∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ h∉
      e₀  , eq  = strengthen-Tm-gen ⊢e  ρ h inv x₁
      e₁₀ , eq₁ = strengthen-Tm-gen ⊢e₁ (ρ ↑) (suc h) (inv↑ inv) (∉-abs-ctx-PS p/s γ₂ x₂)
      e₂₀ , eq₂ = strengthen-Tm-gen ⊢e₂ (ρ ↑) (suc h) (inv↑ inv) (∉-abs-ctx-PS p/s γ₂ x₂)
  in `case e₀ `of⟨ e₁₀ ; e₂₀ ⟩ , cong₃ (λ a b c → `case a `of⟨ b ; c ⟩) eq eq₁ eq₂
strengthen-Tm-gen (T-Conv _ _ ⊢e) ρ h inv h∉ = strengthen-Tm-gen ⊢e ρ h inv h∉
strengthen-Tm-gen (T-Weaken γ≤ ⊢e) ρ h inv h∉ = strengthen-Tm-gen ⊢e ρ h inv (λ x∈ → h∉ (≼⇒dom⊆ γ≤ x∈))


strengthen-Tm : {Γ : Ctx (suc n)} {γ : Struct (suc n)} {e : Tm (suc n)} {T : 𝕋} {ϵ : Eff}
              → Γ ; γ ⊢ e ∶ T ∣ ϵ → (x : 𝔽 (suc n)) → x ∉ dom γ
              → Σ[ e₀ ∈ Tm n ] e ≡ e₀ ⋯ punchIn x
strengthen-Tm (T-Const {c = c} _) x _ = K c , refl
strengthen-Tm (T-Var x′ _) x x∉ = ` punchOut x≢x′ , cong `_ (sym (punchIn-punchOut x≢x′))
  where x≢x′ : x ≢ x′
        x≢x′ x≡ = x∉ (subst (λ z → x ∈ ⁅ z ⁆) x≡ (x∈⁅x⁆ x))
strengthen-Tm {γ = γ} (T-Abs {a = a} _ _ ⊢e) x x∉ =
  let e₀ , eq = strengthen-Tm ⊢e (suc x) (∉-abs-ctx-Dir (Arr.dir a) γ x∉)
  in ƛ (Arr.dir a) e₀ , cong (ƛ (Arr.dir a)) (eq ■ ⋯-cong e₀ (pin x))
strengthen-Tm {γ = γ} (T-AbsRec _ _ ⊢e) x x∉ =
  let e₀ , eq = strengthen-Tm ⊢e (suc (suc x)) (∉-absrec-ctx γ x∉)
  in μ (ƛ 𝟙 e₀) , cong μ (cong (ƛ 𝟙) (eq ■ ⋯-cong e₀ (pin² x)))
strengthen-Tm (T-AppUnr _ _ ⊢e₁ ⊢e₂) x x∉ =
  let e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm (T-AppLin _ _ ⊢e₁ ⊢e₂) x x∉ =
  let e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm (T-AppLeft _ _ ⊢e₁ ⊢e₂) x x∉ =
  let e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈)))
  in e₁₀ ·ᴸ e₂₀ , cong₂ (_·⟨ L ⟩_) eq₁ eq₂
strengthen-Tm (T-AppRight _ _ ⊢e₁ ⊢e₂) x x∉ =
  let e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·ᴿ e₂₀ , cong₂ (_·⟨ R ⟩_) eq₁ eq₂
strengthen-Tm (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) x x∉ =
  let x₁ , x₂ = ∉-join-biased⁻ p/s γ₁ γ₂ x∉
      e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x x₁
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x x₂
  in e₁₀ ⊗ e₂₀ , cong₂ _⊗_ eq₁ eq₂
strengthen-Tm (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) x x∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x x₁
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ (suc x) (∉-abs-ctx-PS p/s γ₂ x₂)
  in `let e₁₀ `in e₂₀ , cong₂ `let_`in_ eq₁ (eq₂ ■ ⋯-cong e₂₀ (pin x))
strengthen-Tm (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) x x∉ =
  let x₁ , x₂ = ∉∪⁻ x∉
      e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x x₁
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ x x₂
  in e₁₀ ; e₂₀ , cong₂ _;_ eq₁ eq₂
strengthen-Tm (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) x x∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      e₁₀ , eq₁ = strengthen-Tm ⊢e₁ x x₁
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ (suc (suc x)) (∉-letpair-ctx p/s d γ₂ x₂)
  in `let⊗ e₁₀ `in e₂₀ , cong₂ `let⊗_`in_ eq₁ (eq₂ ■ ⋯-cong e₂₀ (pin² x))
strengthen-Tm (T-Inj {i = i} ⊢e) x x∉ =
  let e₀ , eq = strengthen-Tm ⊢e x x∉
  in `inj i e₀ , cong (`inj i) eq
strengthen-Tm (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) x x∉ =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      e₀  , eq  = strengthen-Tm ⊢e  x x₁
      e₁₀ , eq₁ = strengthen-Tm ⊢e₁ (suc x) (∉-abs-ctx-PS p/s γ₂ x₂)
      e₂₀ , eq₂ = strengthen-Tm ⊢e₂ (suc x) (∉-abs-ctx-PS p/s γ₂ x₂)
  in `case e₀ `of⟨ e₁₀ ; e₂₀ ⟩ ,
     cong₃ (λ a b c → `case a `of⟨ b ; c ⟩) eq (eq₁ ■ ⋯-cong e₁₀ (pin x)) (eq₂ ■ ⋯-cong e₂₀ (pin x))
strengthen-Tm (T-Conv _ _ ⊢e) x x∉ = strengthen-Tm ⊢e x x∉
strengthen-Tm (T-Weaken γ≤ ⊢e) x x∉ = strengthen-Tm ⊢e x (λ x∈ → x∉ (≼⇒dom⊆ γ≤ x∈))


strengthen-Proc-gen : {N : ℕ} {Γ : Ctx N} {γ : Struct N} {P : Proc N}
  → Γ ; γ ⊢ₚ P → {k : ℕ} (ρ : k →ᵣ N) (h : 𝔽 N)
  → Inverter ρ h → h ∉ dom γ → Σ[ P₀ ∈ Proc k ] P ≡ P₀ ⋯ₚ ρ
strengthen-Proc-gen (TP-Expr ⊢e) ρ h inv h∉ =
  let e₀ , eq = strengthen-Tm-gen ⊢e ρ h inv h∉ in ⟪ e₀ ⟫ , cong ⟪_⟫ eq
strengthen-Proc-gen (TP-Par ⊢P ⊢Q) ρ h inv h∉ =
  let P₀ , eqP = strengthen-Proc-gen ⊢P ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₁ x∈)))
      Q₀ , eqQ = strengthen-Proc-gen ⊢Q ρ h inv (λ x∈ → h∉ (x∈p∪q⁺ (inj₂ x∈)))
  in P₀ ∥ Q₀ , cong₂ _∥_ eqP eqQ
strengthen-Proc-gen {γ = γ} (TP-Res {B₁ = A₁} {B₂ = A₂} N p ⊢B₁ ⊢B₂ C C′ ⊢P) ρ h inv h∉ =
  let P₀ , eq = strengthen-Proc-gen ⊢P (ρ ↑* (sum A₁ + sum A₂)) ((sum A₁ + sum A₂) ↑ʳ h)
                  (inv↑* (sum A₁ + sum A₂) inv) (binder-precond A₁ A₂ γ h h∉)
  in ν A₁ A₂ P₀ , cong (ν A₁ A₂) eq
strengthen-Proc-gen (TP-Weaken γ≤ ⊢P) ρ h inv h∉ =
  strengthen-Proc-gen ⊢P ρ h inv (λ x∈ → h∉ (≼⇒dom⊆ γ≤ x∈))

strengthen-Proc : {Γ : Ctx (suc n)} {γ : Struct (suc n)} {P : Proc (suc n)}
                → Γ ; γ ⊢ₚ P → (x : 𝔽 (suc n)) → x ∉ dom γ
                → Σ[ P₀ ∈ Proc n ] P ≡ P₀ ⋯ₚ punchIn x
strengthen-Proc d x x∉ =
  strengthen-Proc-gen d (punchIn x) x
    (λ y y≢x → let x≢y = λ x≡y → y≢x (sym x≡y) in punchOut x≢y , punchIn-punchOut x≢y) x∉


-- ============================================================================
--   MULTI-HANDLE (handle-SET) strengthening.  Generalises the single-handle
--   `Inverter ρ h` to `Inverter* ρ H`, where `H : 𝔽 N → Set` carves out an
--   arbitrary SET of missing handles: every var NOT in H has a preimage.  This
--   is the additive primitive that lets a typed term / process / frame factor
--   through a renaming missing a whole BLOCK of consumed channels at once
--   (RU-RSplit consumes the entire `suc b₁`-wide data block, not one handle).
--
--   The single-handle lemmas above are untouched (they drive the closed
--   U-com / U-choice / U-drop cases); everything here is strictly new names.
-- ============================================================================

Inverter* : ∀ {k N} → (k →ᵣ N) → (𝔽 N → Set) → Set
Inverter* {k} {N} ρ H = (y : 𝔽 N) → ¬ H y → Σ[ y₀ ∈ 𝔽 k ] ρ y₀ ≡ y

-- Shift a handle-set under one binder: 0F is fresh, suc z is a handle iff z was.
H↑ : ∀ {N} → (𝔽 N → Set) → (𝔽 (suc N) → Set)
H↑ H 0F      = ⊥
H↑ H (suc z) = H z

invH↑ : ∀ {k N} {ρ : k →ᵣ N} {H : 𝔽 N → Set}
      → Inverter* ρ H → Inverter* (ρ ↑) (H↑ H)
invH↑ inv 0F       _  = 0F , refl
invH↑ inv (suc y') ne = let y₀' , eq = inv y' ne in suc y₀' , cong suc eq

-- Shift a handle-set up by j positions (Σ-form: y is in the shifted set iff
-- it lies in the upper region and the un-shifted index was a handle).
H↑ʳ* : ∀ {N} (j : ℕ) → (𝔽 N → Set) → (𝔽 (j + N) → Set)
H↑ʳ* {N} j H y = Σ[ y₀ ∈ 𝔽 N ] (y ≡ j ↑ʳ y₀) × H y₀

invH↑ʳ* : ∀ {k N} {ρ : k →ᵣ N} {H : 𝔽 N → Set} (j : ℕ)
        → Inverter* ρ H → Inverter* (ρ ↑* j) (H↑ʳ* j H)
invH↑ʳ* {k} {N} {ρ} {H} j inv y ¬Hy with Fin.splitAt j y in seqo
... | inj₁ w = (w ↑ˡ k) ,
      (↑*-↑ˡ ρ j w ■ sym yeq)
  where yeq : y ≡ w ↑ˡ N
        yeq = sym (Fin.join-splitAt j N y) ■ cong (Fin.join j N) seqo
... | inj₂ w =
      let yeq : y ≡ j ↑ʳ w
          yeq = sym (Fin.join-splitAt j N y) ■ cong (Fin.join j N) seqo
          ¬Hw : ¬ H w
          ¬Hw hw = ¬Hy (w , yeq , hw)
          w₀ , req = inv w ¬Hw
      in (j ↑ʳ w₀) , (↑*-↑ʳ ρ j w₀ ■ cong (j ↑ʳ_) req ■ sym yeq)

-- Generalised strengthening (term level) through a renaming missing a SET H.
strengthen-Tm-gen* : {N : ℕ} {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff}
  → Γ ; γ ⊢ e ∶ T ∣ ϵ → {k : ℕ} (ρ : k →ᵣ N) (H : 𝔽 N → Set)
  → Inverter* ρ H → ((z : 𝔽 N) → H z → z ∉ dom γ) → Σ[ e₀ ∈ Tm k ] e ≡ e₀ ⋯ ρ
strengthen-Tm-gen* (T-Const {c = c} _) ρ H inv H∉ = K c , refl
strengthen-Tm-gen* (T-Var x′ _) ρ H inv H∉ =
  let y₀ , yeq = inv x′ (λ hx → H∉ x′ hx (x∈⁅x⁆ x′))
  in ` y₀ , cong `_ (sym yeq)
strengthen-Tm-gen* {γ = γ} (T-Abs {a = a} _ _ ⊢e) ρ H inv H∉ =
  let e₀ , eq = strengthen-Tm-gen* ⊢e (ρ ↑) (H↑ H) (invH↑ inv)
                  (λ { (suc z) hz → ∉-abs-ctx-Dir (Arr.dir a) γ (H∉ z hz) })
  in ƛ (Arr.dir a) e₀ , cong (ƛ (Arr.dir a)) eq
strengthen-Tm-gen* {γ = γ} (T-AbsRec _ _ ⊢e) ρ H inv H∉ =
  let e₀ , eq = strengthen-Tm-gen* ⊢e (ρ ↑ ↑) (H↑ (H↑ H)) (invH↑ (invH↑ inv))
                  (λ { (suc (suc z)) hz → ∉-absrec-ctx γ (H∉ z hz) })
  in μ (ƛ 𝟙 e₀) , cong μ (cong (ƛ 𝟙) eq)
strengthen-Tm-gen* (T-AppUnr _ _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm-gen* (T-AppLin _ _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·¹ e₂₀ , cong₂ (_·⟨ 𝟙 ⟩_) eq₁ eq₂
strengthen-Tm-gen* (T-AppLeft _ _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₂ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₁ x∈)))
  in e₁₀ ·ᴸ e₂₀ , cong₂ (_·⟨ L ⟩_) eq₁ eq₂
strengthen-Tm-gen* (T-AppRight _ _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₁ x∈)))
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₂ x∈)))
  in e₁₀ ·ᴿ e₂₀ , cong₂ (_·⟨ R ⟩_) eq₁ eq₂
strengthen-Tm-gen* (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz → let a , _ = ∉-join-biased⁻ p/s γ₁ γ₂ (H∉ z hz) in a)
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz → let _ , b = ∉-join-biased⁻ p/s γ₁ γ₂ (H∉ z hz) in b)
  in e₁₀ ⊗ e₂₀ , cong₂ _⊗_ eq₁ eq₂
strengthen-Tm-gen* (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz → let a , _ = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in a)
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv)
                    (λ { (suc z) hz → ∉-abs-ctx-PS p/s γ₂ (let _ , b = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in b) })
  in `let e₁₀ `in e₂₀ , cong₂ `let_`in_ eq₁ eq₂
strengthen-Tm-gen* (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz → let a , _ = ∉∪⁻ (H∉ z hz) in a)
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz → let _ , b = ∉∪⁻ (H∉ z hz) in b)
  in e₁₀ ; e₂₀ , cong₂ _;_ eq₁ eq₂
strengthen-Tm-gen* (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz → let a , _ = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in a)
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ (ρ ↑ ↑) (H↑ (H↑ H)) (invH↑ (invH↑ inv))
                    (λ { (suc (suc z)) hz → ∉-letpair-ctx p/s d γ₂ (let _ , b = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in b) })
  in `let⊗ e₁₀ `in e₂₀ , cong₂ `let⊗_`in_ eq₁ eq₂
strengthen-Tm-gen* (T-Inj {i = i} ⊢e) ρ H inv H∉ =
  let e₀ , eq = strengthen-Tm-gen* ⊢e ρ H inv H∉
  in `inj i e₀ , cong (`inj i) eq
strengthen-Tm-gen* (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) ρ H inv H∉ =
  let e₀  , eq  = strengthen-Tm-gen* ⊢e  ρ H inv (λ z hz → let a , _ = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in a)
      e₁₀ , eq₁ = strengthen-Tm-gen* ⊢e₁ (ρ ↑) (H↑ H) (invH↑ inv)
                    (λ { (suc z) hz → ∉-abs-ctx-PS p/s γ₂ (let _ , b = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in b) })
      e₂₀ , eq₂ = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv)
                    (λ { (suc z) hz → ∉-abs-ctx-PS p/s γ₂ (let _ , b = ∉-join-PS⁻ p/s γ₁ γ₂ (H∉ z hz) in b) })
  in `case e₀ `of⟨ e₁₀ ; e₂₀ ⟩ , cong₃ (λ a b c → `case a `of⟨ b ; c ⟩) eq eq₁ eq₂
strengthen-Tm-gen* (T-Conv _ _ ⊢e) ρ H inv H∉ = strengthen-Tm-gen* ⊢e ρ H inv H∉
strengthen-Tm-gen* (T-Weaken γ≤ ⊢e) ρ H inv H∉ =
  strengthen-Tm-gen* ⊢e ρ H inv (λ z hz x∈ → H∉ z hz (≼⇒dom⊆ γ≤ x∈))

-- Generalised strengthening (process level) through a renaming missing a SET H.
strengthen-Proc-gen* : {N : ℕ} {Γ : Ctx N} {γ : Struct N} {P : Proc N}
  → Γ ; γ ⊢ₚ P → {k : ℕ} (ρ : k →ᵣ N) (H : 𝔽 N → Set)
  → Inverter* ρ H → ((z : 𝔽 N) → H z → z ∉ dom γ) → Σ[ P₀ ∈ Proc k ] P ≡ P₀ ⋯ₚ ρ
strengthen-Proc-gen* (TP-Expr ⊢e) ρ H inv H∉ =
  let e₀ , eq = strengthen-Tm-gen* ⊢e ρ H inv H∉ in ⟪ e₀ ⟫ , cong ⟪_⟫ eq
strengthen-Proc-gen* (TP-Par ⊢P ⊢Q) ρ H inv H∉ =
  let P₀ , eqP = strengthen-Proc-gen* ⊢P ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₁ x∈)))
      Q₀ , eqQ = strengthen-Proc-gen* ⊢Q ρ H inv (λ z hz x∈ → H∉ z hz (x∈p∪q⁺ (inj₂ x∈)))
  in P₀ ∥ Q₀ , cong₂ _∥_ eqP eqQ
strengthen-Proc-gen* {γ = γ} (TP-Res {B₁ = A₁} {B₂ = A₂} N p ⊢B₁ ⊢B₂ C C′ ⊢P) ρ H inv H∉ =
  let P₀ , eq = strengthen-Proc-gen* ⊢P (ρ ↑* (sum A₁ + sum A₂)) (H↑ʳ* (sum A₁ + sum A₂) H)
                  (invH↑ʳ* (sum A₁ + sum A₂) inv)
                  (λ z → λ { (z₀ , zeq , Hz₀) →
                     subst (_∉ _) (sym zeq) (binder-precond A₁ A₂ γ z₀ (H∉ z₀ Hz₀)) })
  in ν A₁ A₂ P₀ , cong (ν A₁ A₂) eq
strengthen-Proc-gen* (TP-Weaken γ≤ ⊢P) ρ H inv H∉ =
  strengthen-Proc-gen* ⊢P ρ H inv (λ z hz x∈ → H∉ z hz (≼⇒dom⊆ γ≤ x∈))
