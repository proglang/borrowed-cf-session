module BorrowedCF.Simulation.Support.Confine where

open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Data.Nat.Solver using (module +-*-Solver)

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (Unr; Dir; 𝟙; L; R)
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Context.Subcontext
open import BorrowedCF.Context.Join
open import BorrowedCF.Context.Substitution using (wk)
open import Data.Fin.Subset using (_∈_; _∉_; _∪_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁺; x∈p∪q⁻; ∉⊥)

open Nat.Variables
open Nat using (_≤_; +-comm; +-assoc; +-identityʳ; ≤-reflexive; ≤-trans; +-mono-≤; z≤n)
open Variables

variable
  x y : 𝔽 n

-- Multiplicity of a variable in an ordered context.  Unlike `dom` (a Subset,
-- which forgets repetition), `count` tracks how many `` ` x `` leaves equal x —
-- the bookkeeping needed to express linearity of a single channel.
count : 𝔽 n → Struct n → ℕ
count x (` y) with x Fin.≟ y
... | yes _ = 1
... | no  _ = 0
count x []      = 0
count x (α ∥ β) = count x α + count x β
count x (α ; β) = count x α + count x β

-- A variable whose type is NOT unrestricted does not occur in an unrestricted
-- context, hence has count 0 there.
unrCx⇒count0 : ¬ Unr (Γ x) → UnrCx Γ α → count x α ≡ 0
unrCx⇒count0 ¬u []        = refl
unrCx⇒count0 ¬u (C₁ ∥ C₂) = cong₂ _+_ (unrCx⇒count0 ¬u C₁) (unrCx⇒count0 ¬u C₂)
unrCx⇒count0 ¬u (C₁ ; C₂) = cong₂ _+_ (unrCx⇒count0 ¬u C₁) (unrCx⇒count0 ¬u C₂)
unrCx⇒count0 {x = x} ¬u (`_ {y} py) with x Fin.≟ y
... | yes refl = ⊥-elim (¬u py)
... | no  _    = refl

-- `count x` is invariant under one-step ≈ — provided x is non-unrestricted, so
-- that the only duplicating rule (∥′-dup, on an UnrCx) leaves it untouched.
count-≈′ : ¬ Unr (Γ x) → Γ ∶ α ≈′ β → count x α ≡ count x β
count-≈′ {x = x} ¬u (;′-assoc {α} {β} {γ}) = +-assoc (count x α) (count x β) (count x γ)
count-≈′ ¬u (;′-cong₁ s) = cong (_+ _) (count-≈′ ¬u s)
count-≈′ ¬u (;′-cong₂ s) = cong (_ +_) (count-≈′ ¬u s)
count-≈′ {x = x} ¬u (∥′-unit {α}) = +-identityʳ (count x α)
count-≈′ {x = x} ¬u (∥′-assoc {α} {β} {γ}) = +-assoc (count x α) (count x β) (count x γ)
count-≈′ {x = x} ¬u (∥′-comm {α} {β}) = +-comm (count x α) (count x β)
count-≈′ ¬u (∥′-cong₁ s) = cong (_+ _) (count-≈′ ¬u s)
count-≈′ {x = x} ¬u (∥′-dup {α} U) =
  unrCx⇒count0 ¬u U ■ sym (cong₂ _+_ (unrCx⇒count0 ¬u U) (unrCx⇒count0 ¬u U))
count-≈′ ¬u (∥′-tm-; _) = refl

count-≈ : ¬ Unr (Γ x) → Γ ∶ α ≈ β → count x α ≡ count x β
count-≈ ¬u ε             = refl
count-≈ ¬u (fwd s ◅ rest) = count-≈′ ¬u s ■ count-≈ ¬u rest
count-≈ ¬u (bwd s ◅ rest) = sym (count-≈′ ¬u s) ■ count-≈ ¬u rest

-- The linearity lever: ≼ never increases the multiplicity of a non-unrestricted
-- variable (≼-∅ drops, ≼-wk rearranges, ≼-refl is ≈).  Count analogue of ≼⇒dom⊆.
≼⇒count≤ : ¬ Unr (Γ x) → Γ ∶ α ≼ β → count x α ≤ count x β
≼⇒count≤ ¬u (≼-refl eq) = ≤-reflexive (count-≈ ¬u eq)
≼⇒count≤ ¬u (≼-∅ _)     = z≤n
≼⇒count≤ {x = x} ¬u (≼-wk {α₁} {α₂} {β₁} {β₂}) = ≤-reflexive (lemma (count x α₁) (count x α₂) (count x β₁) (count x β₂))
  where
    lemma : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lemma a b c d = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl a b c d
      where open +-*-Solver
≼⇒count≤ ¬u (≼-trans x y) = ≤-trans (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)
≼⇒count≤ ¬u (≼-cong-; x y) = +-mono-≤ (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)
≼⇒count≤ ¬u (≼-cong-∥ x y) = +-mono-≤ (≼⇒count≤ ¬u x) (≼⇒count≤ ¬u y)

-- ───────────────────────────────────────────────────────────────────────────
-- dom helpers for the strengthening lemma (free-var ⊆ struct-domain).
-- Structs are passed EXPLICITLY: `dom` is non-injective, so implicit structs
-- under `dom` cannot be inferred.

∉∪⁻ : ∀ {X Y : Data.Fin.Subset.Subset n} → x ∉ X ∪ Y → (x ∉ X) × (x ∉ Y)
∉∪⁻ x∉ = (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈))) , (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))

∉∪⁺ : (X Y : Data.Fin.Subset.Subset n) → x ∉ X → x ∉ Y → x ∉ X ∪ Y
∉∪⁺ X Y x∉X x∉Y x∈ = [ x∉X , x∉Y ]′ (x∈p∪q⁻ X Y x∈)

∉-join-Dir⁺ : (d : Dir) (α β : Struct n) → x ∉ dom α → x ∉ dom β → x ∉ dom (join d α β)
∉-join-Dir⁺ 𝟙 α β a b = ∉∪⁺ (dom α) (dom β) a b
∉-join-Dir⁺ L α β a b = ∉∪⁺ (dom α) (dom β) a b
∉-join-Dir⁺ R α β a b = ∉∪⁺ (dom β) (dom α) b a

∉-join-PS⁺ : (p/s : ParSeq) (α β : Struct n) → x ∉ dom α → x ∉ dom β → x ∉ dom (join p/s α β)
∉-join-PS⁺ par α β a b = ∉∪⁺ (dom α) (dom β) a b
∉-join-PS⁺ seq α β a b = ∉∪⁺ (dom α) (dom β) a b

∉-join-PS⁻ : (p/s : ParSeq) (α β : Struct n) → x ∉ dom (join p/s α β) → (x ∉ dom α) × (x ∉ dom β)
∉-join-PS⁻ par α β x∉ = (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈))) , (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
∉-join-PS⁻ seq α β x∉ = (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈))) , (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))

∉-join-biased⁻ : (p/s : ParSeq) (α β : Struct n) → x ∉ dom (join (biasedDir p/s) α β) → (x ∉ dom α) × (x ∉ dom β)
∉-join-biased⁻ par α β x∉ = (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈))) , (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))
∉-join-biased⁻ seq α β x∉ = (λ x∈ → x∉ (x∈p∪q⁺ (inj₁ x∈))) , (λ x∈ → x∉ (x∈p∪q⁺ (inj₂ x∈)))

dom-wk : (γ : Struct n) {x : 𝔽 n} → x ∉ dom γ → suc x ∉ dom (wk γ)
dom-wk []      x∉ = ∉⊥
dom-wk (` y)   x∉ sx∈ = x∉ (subst (λ z → _ ∈ ⁅ z ⁆) (Fin.suc-injective (x∈⁅y⁆⇒x≡y _ sx∈)) (x∈⁅x⁆ _))
dom-wk (α ∥ β) x∉ = let xa , xb = ∉∪⁻ x∉ in λ sx∈ → [ dom-wk α xa , dom-wk β xb ]′ (x∈p∪q⁻ (dom (wk α)) (dom (wk β)) sx∈)
dom-wk (α ; β) x∉ = let xa , xb = ∉∪⁻ x∉ in λ sx∈ → [ dom-wk α xa , dom-wk β xb ]′ (x∈p∪q⁻ (dom (wk α)) (dom (wk β)) sx∈)

suc∉⁅zero⁆ : suc x ∉ dom (` zero)
suc∉⁅zero⁆ sx∈ with x∈⁅y⁆⇒x≡y zero sx∈
... | ()

suc²∉⁅suc-zero⁆ : suc (suc x) ∉ dom (` suc zero)
suc²∉⁅suc-zero⁆ sx∈ with x∈⁅y⁆⇒x≡y (suc zero) sx∈
... | ()

-- binder-context membership (built here, where Struct constructors are free).
∉-abs-ctx-Dir : (d : Dir) (γ : Struct n) {x : 𝔽 n} → x ∉ dom γ → suc x ∉ dom (join d (` zero) (wk γ))
∉-abs-ctx-Dir d γ x∉ = ∉-join-Dir⁺ d (` zero) (wk γ) suc∉⁅zero⁆ (dom-wk γ x∉)

∉-abs-ctx-PS : (p/s : ParSeq) (γ : Struct n) {x : 𝔽 n} → x ∉ dom γ → suc x ∉ dom (join p/s (` zero) (wk γ))
∉-abs-ctx-PS p/s γ x∉ = ∉-join-PS⁺ p/s (` zero) (wk γ) suc∉⁅zero⁆ (dom-wk γ x∉)

∉-absrec-ctx : (γ : Struct n) {x : 𝔽 n} → x ∉ dom γ → suc (suc x) ∉ dom (((` zero) ∥ (` suc zero)) ∥ wk (wk γ))
∉-absrec-ctx γ x∉ =
  ∉∪⁺ (dom ((` zero) ∥ (` suc zero))) (dom (wk (wk γ)))
    (∉∪⁺ (dom (` zero)) (dom (` suc zero)) suc∉⁅zero⁆ suc²∉⁅suc-zero⁆)
    (dom-wk (wk γ) (dom-wk γ x∉))

∉-letpair-ctx : (p/s : ParSeq) (d : Dir) (γ : Struct n) {x : 𝔽 n}
              → x ∉ dom γ → suc (suc x) ∉ dom (join p/s (join d (` zero) (` suc zero)) (wk (wk γ)))
∉-letpair-ctx p/s d γ x∉ =
  ∉-join-PS⁺ p/s (join d (` zero) (` suc zero)) (wk (wk γ))
    (∉-join-Dir⁺ d (` zero) (` suc zero) suc∉⁅zero⁆ suc²∉⁅suc-zero⁆)
    (dom-wk (wk γ) (dom-wk γ x∉))

-- ───────────────────────────────────────────────────────────────────────────
-- count ↔ dom bridge and additivity over `join`.

count-self : ∀ (x : 𝔽 n) → count x (` x) ≡ 1
count-self x with x Fin.≟ x
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

+≡0 : ∀ {a b} → a + b ≡ 0 → (a ≡ 0) × (b ≡ 0)
+≡0 {zero}  refl = refl , refl
+≡0 {suc a} ()

count0⇒∉dom : (γ : Struct n) {x : 𝔽 n} → count x γ ≡ 0 → x ∉ dom γ
count0⇒∉dom []      c0 = ∉⊥
count0⇒∉dom (` y) {x = x} c0 x∈ with x∈⁅y⁆⇒x≡y y x∈
... | refl = bust (sym (count-self x) ■ c0)
  where bust : 1 ≡ 0 → ⊥
        bust ()
count0⇒∉dom (α ∥ β) c0 =
  let cα , cβ = +≡0 c0 in ∉∪⁺ (dom α) (dom β) (count0⇒∉dom α cα) (count0⇒∉dom β cβ)
count0⇒∉dom (α ; β) c0 =
  let cα , cβ = +≡0 c0 in ∉∪⁺ (dom α) (dom β) (count0⇒∉dom α cα) (count0⇒∉dom β cβ)

count-join-Dir : (d : Dir) (x : 𝔽 n) (α β : Struct n) → count x (join d α β) ≡ count x α + count x β
count-join-Dir 𝟙 x α β = refl
count-join-Dir L x α β = refl
count-join-Dir R x α β = +-comm (count x β) (count x α)

count-join-PS : (p/s : ParSeq) (x : 𝔽 n) (α β : Struct n) → count x (join p/s α β) ≡ count x α + count x β
count-join-PS par x α β = refl
count-join-PS seq x α β = refl

∉dom⇒count0 : (γ : Struct n) {x : 𝔽 n} → x ∉ dom γ → count x γ ≡ 0
∉dom⇒count0 []      x∉ = refl
∉dom⇒count0 (` y) {x = x} x∉ with x Fin.≟ y
... | yes refl = ⊥-elim (x∉ (x∈⁅x⁆ x))
... | no  _    = refl
∉dom⇒count0 (α ∥ β) x∉ =
  let xa , xb = ∉∪⁻ x∉ in cong₂ _+_ (∉dom⇒count0 α xa) (∉dom⇒count0 β xb)
∉dom⇒count0 (α ; β) x∉ =
  let xa , xb = ∉∪⁻ x∉ in cong₂ _+_ (∉dom⇒count0 α xa) (∉dom⇒count0 β xb)

count-wk-zero : (γ : Struct n) → count zero (wk γ) ≡ 0
count-wk-zero []      = refl
count-wk-zero (` y)   = refl
count-wk-zero (α ∥ β) = cong₂ _+_ (count-wk-zero α) (count-wk-zero β)
count-wk-zero (α ; β) = cong₂ _+_ (count-wk-zero α) (count-wk-zero β)

count-wk-suc : (γ : Struct n) (x : 𝔽 n) → count (suc x) (wk γ) ≡ count x γ
count-wk-suc []      x = refl
count-wk-suc (` y)   x with suc x Fin.≟ suc y | x Fin.≟ y
... | yes _   | yes _  = refl
... | no  _   | no  _  = refl
... | yes sp  | no ¬p  = ⊥-elim (¬p (Fin.suc-injective sp))
... | no ¬sp  | yes p  = ⊥-elim (¬sp (cong suc p))
count-wk-suc (α ∥ β) x = cong₂ _+_ (count-wk-suc α x) (count-wk-suc β x)
count-wk-suc (α ; β) x = cong₂ _+_ (count-wk-suc α x) (count-wk-suc β x)
