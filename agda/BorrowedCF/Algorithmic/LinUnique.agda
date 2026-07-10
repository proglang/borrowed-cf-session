module BorrowedCF.Algorithmic.LinUnique where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; ∉⊥; x∈p∪q⁻; x∈p∪q⁺)
open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; +-comm; +-mono-≤)
open import Relation.Nullary using (yes; no)
import Data.Sum as Sum

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Algorithmic.Split

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

-- Leaf-occurrence count of a variable in a context.
cnt : {n : ℕ} → Struct n → 𝔽 n → ℕ
cnt (` y) x with x ≟F y
... | yes _ = 1
... | no  _ = 0
cnt [] x = 0
cnt (α ∥ β) x = cnt α x + cnt β x
cnt (α ; β) x = cnt α x + cnt β x

cnt-wk-suc : {n : ℕ} (γ : Struct n) (x : 𝔽 n) → cnt (𝐂.wk γ) (fs x) ≡ cnt γ x
cnt-wk-suc (` y) x with fs x ≟F fs y | x ≟F y
... | yes _    | yes _  = refl
... | yes refl | no x≢y = ⊥-elim (x≢y refl)
... | no fsx≢  | yes refl = ⊥-elim (fsx≢ refl)
... | no _     | no _   = refl
cnt-wk-suc [] x = refl
cnt-wk-suc (α ∥ β) x = cong₂ _+_ (cnt-wk-suc α x) (cnt-wk-suc β x)
cnt-wk-suc (α ; β) x = cong₂ _+_ (cnt-wk-suc α x) (cnt-wk-suc β x)

∈dom⇒cnt : {n : ℕ} (γ : Struct n) {y : 𝔽 n} → y ∈ dom γ → 1 ≤ cnt γ y
∈dom⇒cnt [] y∈ = ⊥-elim (∉⊥ y∈)
∈dom⇒cnt (` z) {y} y∈ with y ≟F z
... | yes _ = s≤s z≤n
... | no y≢z = ⊥-elim (y≢z (x∈⁅y⁆⇒x≡y z y∈))
∈dom⇒cnt (α ∥ β) {y} y∈ with x∈p∪q⁻ (dom α) (dom β) y∈
... | Sum.inj₁ y∈α = ≤-trans (∈dom⇒cnt α y∈α) (m≤m+n _ _)
... | Sum.inj₂ y∈β = ≤-trans (∈dom⇒cnt β y∈β) (m≤n+m _ _)
∈dom⇒cnt (α ; β) {y} y∈ with x∈p∪q⁻ (dom α) (dom β) y∈
... | Sum.inj₁ y∈α = ≤-trans (∈dom⇒cnt α y∈α) (m≤m+n _ _)
... | Sum.inj₂ y∈β = ≤-trans (∈dom⇒cnt β y∈β) (m≤n+m _ _)

open import BorrowedCF.DescendAbs using (∈tail)

cnt-join : ∀ {A} ⦃ _ : Join A ⦄ {n} (d : A) (α β : Struct n) (x : 𝔽 n) →
           cnt (join d α β) x ≡ cnt α x + cnt β x
cnt-join d α β x with joinDir d
... | 𝟙 = refl
... | L = refl
... | R = +-comm (cnt β x) (cnt α x)

cnt-fz : {n : ℕ} (x : 𝔽 n) → cnt {suc n} (` fz) (fs x) ≡ 0
cnt-fz x = refl

cnt-descend1 : ∀ {A} ⦃ _ : Join A ⦄ {n} (d : A) (γ : Struct n) (x : 𝔽 n) →
               cnt (join d (` fz) (𝐂.wk γ)) (fs x) ≡ cnt γ x
cnt-descend1 d γ x = cnt-join d (` fz) (𝐂.wk γ) (fs x) ■ cnt-wk-suc γ x

split≤ : (a b : ℕ) → 1 ≤ a + b → (1 ≤ a) Sum.⊎ (1 ≤ b)
split≤ zero b p = Sum.inj₂ p
split≤ (suc a) b p = Sum.inj₁ (s≤s z≤n)

cnt⇒∈dom : {n : ℕ} (γ : Struct n) {y : 𝔽 n} → 1 ≤ cnt γ y → y ∈ dom γ
cnt⇒∈dom (` z) {y} p with y ≟F z
... | yes refl = x∈⁅x⁆ z
cnt⇒∈dom (α ∥ β) {y} p with split≤ (cnt α y) (cnt β y) p
... | Sum.inj₁ pa = x∈p∪q⁺ (Sum.inj₁ (cnt⇒∈dom α pa))
... | Sum.inj₂ pb = x∈p∪q⁺ (Sum.inj₂ (cnt⇒∈dom β pb))
cnt⇒∈dom (α ; β) {y} p with split≤ (cnt α y) (cnt β y) p
... | Sum.inj₁ pa = x∈p∪q⁺ (Sum.inj₁ (cnt⇒∈dom α pa))
... | Sum.inj₂ pb = x∈p∪q⁺ (Sum.inj₂ (cnt⇒∈dom β pb))

cnt-descend2 : ∀ {A} ⦃ _ : Join A ⦄ {n} (ps : A) (d : Dir) (γ : Struct n) (x : 𝔽 n) →
               cnt (join ps (join d (` fz) (` fs fz)) (𝐂.wk (𝐂.wk γ))) (fs (fs x)) ≡ cnt γ x
cnt-descend2 ps d γ x =
  cnt-join ps (join d (` fz) (` fs fz)) (𝐂.wk (𝐂.wk γ)) (fs (fs x))
  ■ cong (_+ cnt (𝐂.wk (𝐂.wk γ)) (fs (fs x))) (cnt-join d (` fz) (` fs fz) (fs (fs x)))
  ■ cnt-wk-suc (𝐂.wk γ) (fs x) ■ cnt-wk-suc γ x

fv⇒cnt : {n : ℕ} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
         Γ ; γ ⊢ e ∶ T ∣ ϵ → {x : 𝔽 n} → x ∈ fv e → 1 ≤ cnt γ x
fv⇒cnt (T-Const ⊢c) x∈ = ⊥-elim (∉⊥ x∈)
fv⇒cnt (T-Var y refl) {x} x∈ with x ≟F y
... | yes _  = s≤s z≤n
... | no x≢y = ⊥-elim (x≢y (x∈⁅y⁆⇒x≡y y x∈))
fv⇒cnt {γ = γ} (T-Abs {a = a} _ _ d) {x} x∈ =
  subst (1 ≤_) (cnt-descend1 (Arr.dir a) γ x) (fv⇒cnt d (∈tail x∈))
fv⇒cnt {γ = γ} (T-AbsRec _ _ d) {x} x∈ =
  subst (1 ≤_) (cnt-wk-suc γ x) (help (fv⇒cnt d (∈tail (∈tail x∈))))
  where help : 1 ≤ cnt ((` fz) ∥ (` fs fz) ∥ 𝐂.wk (𝐂.wk γ)) (fs (fs x)) → 1 ≤ cnt (𝐂.wk γ) (fs x)
        help p = subst (1 ≤_) (cnt-wk-suc (𝐂.wk γ) (fs x)) p
fv⇒cnt {γ = γ₁ ∥ γ₂} (T-AppUnr {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) {x} x∈ with x∈p∪q⁻ (fv e₁) (fv e₂) x∈
... | Sum.inj₁ x∈₁ = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
... | Sum.inj₂ x∈₂ = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤n+m _ _)
fv⇒cnt {γ = γ₁ ∥ γ₂} (T-AppLin {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) {x} x∈ with x∈p∪q⁻ (fv e₁) (fv e₂) x∈
... | Sum.inj₁ x∈₁ = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
... | Sum.inj₂ x∈₂ = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤n+m _ _)
fv⇒cnt {γ = γ₂ ; γ₁} (T-AppLeft {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) {x} x∈ with x∈p∪q⁻ (fv e₁) (fv e₂) x∈
... | Sum.inj₁ x∈₁ = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤n+m _ _)
... | Sum.inj₂ x∈₂ = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤m+n _ _)
fv⇒cnt {γ = γ₁ ; γ₂} (T-AppRight {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) {x} x∈ with x∈p∪q⁻ (fv e₁) (fv e₂) x∈
... | Sum.inj₁ x∈₁ = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
... | Sum.inj₂ x∈₂ = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤n+m _ _)
fv⇒cnt {γ = γ} (T-Pair {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} _ d₁ d₂) {x} x∈ =
  subst (1 ≤_) (sym (cnt-join (biasedDir p/s) γ₁ γ₂ x)) (par-help (x∈p∪q⁻ (fv e₁) (fv e₂) x∈))
  where par-help : (x ∈ fv e₁) Sum.⊎ (x ∈ fv e₂) → 1 ≤ cnt γ₁ x + cnt γ₂ x
        par-help (Sum.inj₁ x∈₁) = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
        par-help (Sum.inj₂ x∈₂) = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤n+m _ _)
fv⇒cnt {γ = γ} (T-Let {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) {x} x∈ =
  subst (1 ≤_) (sym (cnt-join p/s γ₁ γ₂ x)) (let-help (x∈p∪q⁻ (fv e₁) (fvClose (fv e₂)) x∈))
  where let-help : (x ∈ fv e₁) Sum.⊎ (x ∈ fvClose (fv e₂)) → 1 ≤ cnt γ₁ x + cnt γ₂ x
        let-help (Sum.inj₁ x∈₁) = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
        let-help (Sum.inj₂ x∈₂) = ≤-trans (subst (1 ≤_) (cnt-descend1 p/s γ₂ x) (fv⇒cnt d₂ (∈tail x∈₂))) (m≤n+m _ _)
fv⇒cnt {γ = γ₁ ; γ₂} (T-Seq {e₁ = e₁} {e₂ = e₂} _ d₁ d₂) {x} x∈ with x∈p∪q⁻ (fv e₁) (fv e₂) x∈
... | Sum.inj₁ x∈₁ = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
... | Sum.inj₂ x∈₂ = ≤-trans (fv⇒cnt d₂ x∈₂) (m≤n+m _ _)
fv⇒cnt {γ = γ} (T-LetPair {e₁ = e₁} {d = dd} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) {x} x∈ =
  subst (1 ≤_) (sym (cnt-join p/s γ₁ γ₂ x)) (lp-help (x∈p∪q⁻ (fv e₁) (fvClose* 2 (fv e₂)) x∈))
  where lp-help : (x ∈ fv e₁) Sum.⊎ (x ∈ fvClose* 2 (fv e₂)) → 1 ≤ cnt γ₁ x + cnt γ₂ x
        lp-help (Sum.inj₁ x∈₁) = ≤-trans (fv⇒cnt d₁ x∈₁) (m≤m+n _ _)
        lp-help (Sum.inj₂ x∈₂) =
          ≤-trans (subst (1 ≤_) (cnt-descend2 p/s dd γ₂ x)
                    (fv⇒cnt d₂ (∈tail (∈tail (subst (x ∈_) (drop2≡tail² (fv e₂)) x∈₂))))) (m≤n+m _ _)
fv⇒cnt (T-Inj d) x∈ = fv⇒cnt d x∈
fv⇒cnt {γ = γ} (T-Case {e = ec} {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} de d₁ d₂) {x} x∈ =
  subst (1 ≤_) (sym (cnt-join p/s γ₁ γ₂ x)) (case-help (x∈p∪q⁻ (fv ec) (fvClose (fv e₁) ∪ fvClose (fv e₂)) x∈))
  where case-help : (x ∈ fv ec) Sum.⊎ (x ∈ fvClose (fv e₁) ∪ fvClose (fv e₂)) → 1 ≤ cnt γ₁ x + cnt γ₂ x
        case-help (Sum.inj₁ x∈e) = ≤-trans (fv⇒cnt de x∈e) (m≤m+n _ _)
        case-help (Sum.inj₂ x∈br) with x∈p∪q⁻ (fvClose (fv e₁)) (fvClose (fv e₂)) x∈br
        ... | Sum.inj₁ x∈₁ = ≤-trans (subst (1 ≤_) (cnt-descend1 p/s γ₂ x) (fv⇒cnt d₁ (∈tail x∈₁))) (m≤n+m _ _)
        ... | Sum.inj₂ x∈₂ = ≤-trans (subst (1 ≤_) (cnt-descend1 p/s γ₂ x) (fv⇒cnt d₂ (∈tail x∈₂))) (m≤n+m _ _)
fv⇒cnt (T-Conv _ _ d) x∈ = fv⇒cnt d x∈
fv⇒cnt {γ = γ₂} (T-Weaken {γ₁ = γ₁} γ≤ d) {x} x∈ =
  ∈dom⇒cnt γ₂ (≼⇒dom⊆ γ≤ (cnt⇒∈dom γ₁ (fv⇒cnt d x∈)))

open import Data.Fin.Subset.Properties using () renaming (_∈?_ to _∈?ₛ_)
open import BorrowedCF.Types.Predicates using (unr?)

LinUnique : {n : ℕ} → Ctx n → Struct n → Set
LinUnique {n} Γ γ = (x : 𝔽 n) → (Unr (Γ x) → ⊥) → cnt γ x ≤ 1

linUnique-join : ∀ {A} ⦃ _ : Join A ⦄ {n} {Γ : Ctx n} (a : A) {γ₁ γ₂ : Struct n} →
                 LinUnique Γ (join a γ₁ γ₂) → LinUnique Γ γ₁ × LinUnique Γ γ₂
linUnique-join a {γ₁} {γ₂} lu =
  (λ x ¬u → ≤-trans (m≤m+n (cnt γ₁ x) (cnt γ₂ x)) (subst (_≤ 1) (cnt-join a γ₁ γ₂ x) (lu x ¬u))) ,
  (λ x ¬u → ≤-trans (m≤n+m (cnt γ₂ x) (cnt γ₁ x)) (subst (_≤ 1) (cnt-join a γ₁ γ₂ x) (lu x ¬u)))

allCx-Unr-dom : {n : ℕ} {Γ : Ctx n} (γ : Struct n) →
                ({y : 𝔽 n} → y ∈ dom γ → Unr (Γ y)) → AllCx Unr Γ γ
allCx-Unr-dom (` z) f = ` f (x∈⁅x⁆ z)
allCx-Unr-dom [] f = []
allCx-Unr-dom (α ∥ β) f =
  allCx-Unr-dom α (λ y∈ → f (x∈p∪q⁺ (Sum.inj₁ y∈))) ∥ allCx-Unr-dom β (λ y∈ → f (x∈p∪q⁺ (Sum.inj₂ y∈)))
allCx-Unr-dom (α ; β) f =
  allCx-Unr-dom α (λ y∈ → f (x∈p∪q⁺ (Sum.inj₁ y∈))) ; allCx-Unr-dom β (λ y∈ → f (x∈p∪q⁺ (Sum.inj₂ y∈)))

2≰1 : 2 ≤ 1 → ⊥
2≰1 (s≤s ())

-- Under LinUnique, the sibling context contributes only Unr entries on the
-- free variables of the other subterm: linear-disjointness of siblings.
sibling-Unr : ∀ {A} ⦃ _ : Join A ⦄ {n} {Γ : Ctx n} (a : A) {γ₁ γ₂ : Struct n} {e : Tm n} {T ϵ} →
              LinUnique Γ (join a γ₁ γ₂) → Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → AllCx Unr Γ (γ₂ ↓ fv e)
sibling-Unr {Γ = Γ} a {γ₁} {γ₂} {e} lu d = allCx-Unr-dom (γ₂ ↓ fv e) go
  where go : {y : 𝔽 _} → y ∈ dom (γ₂ ↓ fv e) → Unr (Γ y)
        go {y} y∈ with unr? (Γ y)
        ... | yes u = u
        ... | no ¬u = ⊥-elim (2≰1 (≤-trans
              (+-mono-≤ (fv⇒cnt d (↓-dom γ₂ (fv e) y∈)) (∈dom⇒cnt γ₂ (↓-dom⊆dom γ₂ y∈)))
              (subst (_≤ 1) (cnt-join a γ₁ γ₂ y) (lu y ¬u))))

open import Data.Nat.Properties using (+-assoc; +-identityʳ; ≤-reflexive)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

unrcx-cnt0 : {n : ℕ} {Γ : Ctx n} {α : Struct n} {x : 𝔽 n} →
             UnrCx Γ α → (Unr (Γ x) → ⊥) → cnt α x ≡ 0
unrcx-cnt0 {α = ` z} {x} (` py) nu with x ≟F z
... | yes refl = ⊥-elim (nu py)
... | no  _    = refl
unrcx-cnt0 [] nu = refl
unrcx-cnt0 {α = α ∥ β} (Uα ∥ Uβ) nu = cong₂ _+_ (unrcx-cnt0 Uα nu) (unrcx-cnt0 Uβ nu)
unrcx-cnt0 {α = α ; β} (Uα ; Uβ) nu = cong₂ _+_ (unrcx-cnt0 Uα nu) (unrcx-cnt0 Uβ nu)

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

≈-cnt : {n : ℕ} {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n} →
        (Unr (Γ x) → ⊥) → Γ ∶ α ≈ β → cnt α x ≡ cnt β x
≈-cnt nu ε = refl
≈-cnt nu (fwd e ◅ es) = ≈'-cnt nu e ■ ≈-cnt nu es
≈-cnt nu (bwd e ◅ es) = sym (≈'-cnt nu e) ■ ≈-cnt nu es

rearrange4 : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
rearrange4 a b c d =
  +-assoc a b (c + d) ■ cong (a +_) (sym (+-assoc b c d))
  ■ cong (λ z → a + (z + d)) (+-comm b c) ■ cong (a +_) (+-assoc c b d)
  ■ sym (+-assoc a c (b + d))

≼-cnt : {n : ℕ} {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n} →
        (Unr (Γ x) → ⊥) → Γ ∶ α ≼ β → cnt α x ≤ cnt β x
≼-cnt nu (≼-refl e) = ≤-reflexive (≈-cnt nu e)
≼-cnt nu (≼-∅ U) = z≤n
≼-cnt {x = x} nu (≼-wk {α₁} {α₂} {β₁} {β₂}) =
  ≤-reflexive (rearrange4 (cnt α₁ x) (cnt α₂ x) (cnt β₁ x) (cnt β₂ x))
≼-cnt nu (≼-trans p q) = ≤-trans (≼-cnt nu p) (≼-cnt nu q)
≼-cnt nu (≼-cong-; p q) = +-mono-≤ (≼-cnt nu p) (≼-cnt nu q)
≼-cnt nu (≼-cong-∥ p q) = +-mono-≤ (≼-cnt nu p) (≼-cnt nu q)
