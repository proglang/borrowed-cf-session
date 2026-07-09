module BorrowedCF.SplitCounter where

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Algorithmic
open import Data.Fin using () renaming (zero to Z)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-mono-≤; ≤-trans; ≤-refl; ≤-reflexive)
open import Relation.Nullary using (yes; no)
import Data.Sum as Sum

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

ΓL : Ctx 1
ΓL _ = ⟨ end ‼ ⟩

dv : ΓL ; ` Z ⊢ ` Z ∶ ⟨ end ‼ ⟩ ∣ ℙ
dv = T-Var Z refl

-- `x ⊗ `x is typeable with x = Z LINEAR (⟨ end ‼ ⟩ is a channel type, ¬Unr)
dPair : ΓL ; (` Z) ∥ (` Z) ⊢ (` Z) ⊗ (` Z) ∶ ⟨ end ‼ ⟩ ⊗⟨ 𝟙 ⟩ ⟨ end ‼ ⟩ ∣ ℙ
dPair = T-Pair par par dv dv

-- Leaf-occurrence count of a variable in a Struct.
cnt : {n : ℕ} → Struct n → 𝔽 n → ℕ
cnt (` y) x with x ≟F y
... | yes _ = 1
... | no  _ = 0
cnt [] x = 0
cnt (α ∥ β) x = cnt α x + cnt β x
cnt (α ; β) x = cnt α x + cnt β x

-- A variable whose type is not Unr occurs 0 times in any UnrCx.
unrcx-cnt0 : {n : ℕ} {Γ : Ctx n} {α : Struct n} {x : 𝔽 n} →
             UnrCx Γ α → (Unr (Γ x) → ⊥) → cnt α x ≡ 0
unrcx-cnt0 {α = ` y} {x} (` py) nu with x ≟F y
... | yes refl = ⊥-elim (nu py)
... | no  _    = refl
unrcx-cnt0 [] nu = refl
unrcx-cnt0 {α = α ∥ β} (Uα ∥ Uβ) nu = cong₂ _+_ (unrcx-cnt0 Uα nu) (unrcx-cnt0 Uβ nu)
unrcx-cnt0 {α = α ; β} (Uα ; Uβ) nu = cong₂ _+_ (unrcx-cnt0 Uα nu) (unrcx-cnt0 Uβ nu)

-- ≈′ preserves the count of a linear variable.
≈'-cnt : {n : ℕ} {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n} →
         (Unr (Γ x) → ⊥) → Γ ∶ α ≈′ β → cnt α x ≡ cnt β x
≈'-cnt {x = x} nu (;′-assoc {α = α} {β} {γ}) = +-assoc (cnt α x) (cnt β x) (cnt γ x)
≈'-cnt nu (;′-cong₁ e) = cong (_+ _) (≈'-cnt nu e)
≈'-cnt nu (;′-cong₂ e) = cong (_ +_) (≈'-cnt nu e)
≈'-cnt {x = x} nu (∥′-unit {α = α}) = +-identityʳ (cnt α x)
≈'-cnt {x = x} nu (∥′-assoc {α = α} {β} {γ}) = +-assoc (cnt α x) (cnt β x) (cnt γ x)
≈'-cnt {x = x} nu (∥′-comm {α = α} {β}) = +-comm (cnt α x) (cnt β x)
≈'-cnt nu (∥′-cong₁ e) = cong (_+ _) (≈'-cnt nu e)
≈'-cnt {x = x} nu (∥′-dup {α = α} U) with unrcx-cnt0 {x = x} U nu
... | c0 = c0 ■ sym (cong₂ _+_ c0 c0)
≈'-cnt nu (∥′-tm-; U) = refl

-- ≈ (equivalence closure) preserves the count of a linear variable.
≈-cnt : {n : ℕ} {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n} →
        (Unr (Γ x) → ⊥) → Γ ∶ α ≈ β → cnt α x ≡ cnt β x
≈-cnt nu ε = refl
≈-cnt nu (fwd e ◅ es) = ≈'-cnt nu e ■ ≈-cnt nu es
≈-cnt nu (bwd e ◅ es) = sym (≈'-cnt nu e) ■ ≈-cnt nu es

rearrange4 : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
rearrange4 a b c d =
  +-assoc a b (c + d)
  ■ cong (a +_) (sym (+-assoc b c d))
  ■ cong (λ z → a + (z + d)) (+-comm b c)
  ■ cong (a +_) (+-assoc c b d)
  ■ sym (+-assoc a c (b + d))

-- ≼ can only shrink the count of a linear variable.
≼-cnt : {n : ℕ} {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n} →
        (Unr (Γ x) → ⊥) → Γ ∶ α ≼ β → cnt α x ≤ cnt β x
≼-cnt nu (≼-refl e) = ≤-reflexive (≈-cnt nu e)
≼-cnt nu (≼-∅ U) = z≤n
≼-cnt {x = x} nu (≼-wk {α₁} {α₂} {β₁} {β₂}) =
  ≤-reflexive (rearrange4 (cnt α₁ x) (cnt α₂ x) (cnt β₁ x) (cnt β₂ x))
≼-cnt nu (≼-trans p q) = ≤-trans (≼-cnt nu p) (≼-cnt nu q)
≼-cnt nu (≼-cong-; p q) = +-mono-≤ (≼-cnt nu p) (≼-cnt nu q)
≼-cnt nu (≼-cong-∥ p q) = +-mono-≤ (≼-cnt nu p) (≼-cnt nu q)

-- Z is linear: Unr (⟨ end ‼ ⟩) is uninhabited.
Z-lin : Unr (ΓL Z) → ⊥
Z-lin ⟨ () ⟩

-- ≤γ-par hands us this ≼ for the typed term `x ⊗ `x above:
badGoal : ΓL ∶ ((` Z) ∥ (` Z)) ∥ ((` Z) ∥ (` Z)) ≼ ((` Z) ∥ (` Z))
badGoal = ≤γ-par {γ₁ = ` Z} {γ₂ = ` Z} par dv dv

-- ... but that ≼ forces 4 ≤ 2 on the linear variable Z.  Contradiction.
UNSOUND : ⊥
UNSOUND with ≼-cnt {x = Z} Z-lin badGoal
... | s≤s (s≤s ())
