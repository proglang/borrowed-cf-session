-- | Completeness toolkit, part 1: how the restriction `_↓_` interacts with
--   `count`, `dom`, `_∈ₘ_`, `AllCx` and `wk`.  Pure structure algebra, no typing.
module BorrowedCF.Completeness.Split.Base where

open import Data.Fin.Subset
  using (Subset; Side; inside; outside; _∈_; _∉_; _⊆_; _∪_; ∁)
open import Data.Fin.Subset.Properties
  using (_∈?_; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁺; x∈p∪q⁻; x∈p⇒x∉∁p; x∉p⇒x∈∁p; x∈∁p⇒x∉p; x∉∁p⇒x∈p)
open import Relation.Nullary.Decidable using (decidable-stable)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution using (wk)
open import BorrowedCF.Simulation.Support.Confine
  using (count; ∉dom⇒count0; count0⇒∉dom; count-self; count-wk-zero; count-wk-suc)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (_∈ₘ_; before; mem-parInv; mem-seqInv; mem-parL; mem-parR; mem-seqL; mem-seqR)

open Nat.Variables
open Variables

private
  variable
    x y z u v : 𝔽 n

------------------------------------------------------------------------
-- 1.  `count` under restriction.

count-↓-∈ : (γ : Struct n) → x ∈ X → count x (γ ↓ X) ≡ count x γ
count-↓-∈ []      x∈ = refl
count-↓-∈ (α ∥ β) x∈ = cong₂ _+_ (count-↓-∈ α x∈) (count-↓-∈ β x∈)
count-↓-∈ (α ; β) x∈ = cong₂ _+_ (count-↓-∈ α x∈) (count-↓-∈ β x∈)
count-↓-∈ {x = x} {X = X} (` y) x∈ with y ∈? X
... | yes _ = refl
... | no y∉ with x Fin.≟ y
... | yes refl = ⊥-elim (y∉ x∈)
... | no _ = refl

count-↓-∉ : (γ : Struct n) → x ∉ X → count x (γ ↓ X) ≡ 0
count-↓-∉ []      x∉ = refl
count-↓-∉ (α ∥ β) x∉ = cong₂ _+_ (count-↓-∉ α x∉) (count-↓-∉ β x∉)
count-↓-∉ (α ; β) x∉ = cong₂ _+_ (count-↓-∉ α x∉) (count-↓-∉ β x∉)
count-↓-∉ {x = x} {X = X} (` y) x∉ with y ∈? X
... | no _ = refl
... | yes y∈ with x Fin.≟ y
... | yes refl = ⊥-elim (x∉ y∈)
... | no _ = refl

-- The stated form of the `count`/`↓` interaction.
count-↓ : (γ : Struct n) (x : 𝔽 n) (X : Subset n) →
  count x (γ ↓ X) ≡ (if does (x ∈? X) then count x γ else 0)
count-↓ γ x X with x ∈? X
... | yes x∈ = count-↓-∈ γ x∈
... | no  x∉ = count-↓-∉ γ x∉

count-↓≤ : (γ : Struct n) (x : 𝔽 n) (X : Subset n) → count x (γ ↓ X) Nat.≤ count x γ
count-↓≤ γ x X with x ∈? X
... | yes x∈ = Nat.≤-reflexive (count-↓-∈ γ x∈)
... | no  x∉ = Nat.≤-trans (Nat.≤-reflexive (count-↓-∉ γ x∉)) Nat.z≤n

------------------------------------------------------------------------
-- 2.  `_∈ₘ_` bridges.

mem⇒∈dom : (γ : Struct n) → x ∈ₘ γ → x ∈ dom γ
mem⇒∈dom {x = x} γ x∈ = decidable-stable (x ∈? dom γ) λ x∉ → x∈ (∉dom⇒count0 γ x∉)

∈dom⇒mem : (γ : Struct n) → x ∈ dom γ → x ∈ₘ γ
∈dom⇒mem γ x∈ c≡0 = count0⇒∉dom γ c≡0 x∈

mem-self : (x : 𝔽 n) → x ∈ₘ (` x)
mem-self x eq = Nat.0≢1+n (sym (sym (count-self x) ■ eq))

-- A variable of a restricted structure lies in the restricting set and in the
-- structure itself.
mem-↓⁻ : (γ : Struct n) → x ∈ₘ (γ ↓ X) → (x ∈ X) × (x ∈ₘ γ)
mem-↓⁻ {x = x} {X = X} γ x∈ with x ∈? X
... | yes x∈X = x∈X , λ c≡0 → x∈ (count-↓-∈ γ x∈X ■ c≡0)
... | no  x∉X = ⊥-elim (x∈ (count-↓-∉ γ x∉X))

mem-↓⁺ : (γ : Struct n) → x ∈ X → x ∈ₘ γ → x ∈ₘ (γ ↓ X)
mem-↓⁺ γ x∈X x∈ c≡0 = x∈ (sym (count-↓-∈ γ x∈X) ■ c≡0)

------------------------------------------------------------------------
-- 3.  `AllCx` and `_∈ₘ_`: pointwise ↔ structural.

allCx-mem : ∀ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} {α : Struct n} →
  AllCx P Γ α → x ∈ₘ α → P (Γ ﹫ x)
allCx-mem []      x∈ = ⊥-elim (x∈ refl)
allCx-mem {α = α₁ ∥ α₂} (C₁ ∥ C₂) x∈ =
  [ allCx-mem C₁ , allCx-mem C₂ ]′ (mem-parInv {α = α₁} {α₂} x∈)
allCx-mem {α = α₁ ; α₂} (C₁ ; C₂) x∈ =
  [ allCx-mem C₁ , allCx-mem C₂ ]′ (mem-seqInv {α = α₁} {α₂} x∈)
allCx-mem {x = x} (`_ {y} p) x∈ with x Fin.≟ y
... | yes refl = p
... | no  _    = ⊥-elim (x∈ refl)

mem-allCx : ∀ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} (α : Struct n) →
  (∀ z → z ∈ₘ α → P (Γ ﹫ z)) → AllCx P Γ α
mem-allCx []      f = []
mem-allCx (α ∥ β) f = mem-allCx α (λ z z∈ → f z (mem-parL {α = α} {β} z∈))
                    ∥ mem-allCx β (λ z z∈ → f z (mem-parR {α = α} {β} z∈))
mem-allCx (α ; β) f = mem-allCx α (λ z z∈ → f z (mem-parL {α = α} {β} z∈))
                    ; mem-allCx β (λ z z∈ → f z (mem-parR {α = α} {β} z∈))
mem-allCx (` y)   f = ` f y (mem-self y)

-- Pointwise `P` on the restricting set gives a `P`-restriction.
allCx-↓-pointwise : ∀ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} (γ : Struct n) {X : Subset n} →
  (∀ z → z ∈ X → P (Γ ﹫ z)) → AllCx P Γ (γ ↓ X)
allCx-↓-pointwise γ {X} f =
  mem-allCx (γ ↓ X) λ z z∈ → f z (mem-↓⁻ γ z∈ .proj₁)

------------------------------------------------------------------------
-- 4.  Restriction commutes with the structure formers.

↓-∥ : (α β : Struct n) (X : Subset n) → (α ∥ β) ↓ X ≡ (α ↓ X) ∥ (β ↓ X)
↓-∥ α β X = refl

↓-; : (α β : Struct n) (X : Subset n) → (α ; β) ↓ X ≡ (α ↓ X) ; (β ↓ X)
↓-; α β X = refl

-- (`join-↓` of Context/Join.agda, re-exported under the name the toolkit advertises.)
↓-join : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (α β : Struct n) {X : Subset n} →
  join a α β ↓ X ≡ join a (α ↓ X) (β ↓ X)
↓-join a α β = join-↓ a α β

-- Restriction under a binder.
↓-wk : (γ : Struct n) (b : Side) (X : Subset n) → wk γ ↓ (b ∷ X) ≡ wk (γ ↓ X)
↓-wk []      b X = refl
↓-wk (α ∥ β) b X = cong₂ _∥_ (↓-wk α b X) (↓-wk β b X)
↓-wk (α ; β) b X = cong₂ _;_ (↓-wk α b X) (↓-wk β b X)
↓-wk (` y)   b X with y ∈? X
... | yes _ = refl
... | no  _ = refl

↓-wk-tail : (γ : Struct n) (X : Subset (suc n)) → wk γ ↓ X ≡ wk (γ ↓ V.tail X)
↓-wk-tail γ (b ∷ X) = ↓-wk γ b X

↓-wk² : (γ : Struct n) (X : Subset (suc (suc n))) →
  wk (wk γ) ↓ X ≡ wk (wk (γ ↓ V.drop 2 X))
↓-wk² γ (b₁ ∷ b₂ ∷ X) = ↓-wk (wk γ) b₁ (b₂ ∷ X) ■ cong wk (↓-wk γ b₂ X)

------------------------------------------------------------------------
-- 5.  Monotonicity of restriction in the set (generalises `↓-strip≼`).

↓-↓-⊆ : (γ : Struct n) {X Y : Subset n} → X ⊆ Y → (γ ↓ Y) ↓ X ≡ γ ↓ X
↓-↓-⊆ []      X⊆Y = refl
↓-↓-⊆ (α ∥ β) X⊆Y = cong₂ _∥_ (↓-↓-⊆ α X⊆Y) (↓-↓-⊆ β X⊆Y)
↓-↓-⊆ (α ; β) X⊆Y = cong₂ _;_ (↓-↓-⊆ α X⊆Y) (↓-↓-⊆ β X⊆Y)
↓-↓-⊆ (` y) {X} {Y} X⊆Y with y ∈? Y
... | yes _ = refl
... | no y∉Y with y ∈? X
... | yes y∈X = ⊥-elim (y∉Y (X⊆Y y∈X))
... | no _ = refl

-- If X ⊆ Y and every variable of Y outside X is unrestricted, restricting to the
-- smaller set is a subcontext of restricting to the larger one.
↓-mono-⊆ : ∀ {Γ : Ctx n} (γ : Struct n) {X Y : Subset n} → X ⊆ Y →
  (∀ z → z ∈ Y → z ∉ X → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ X ≼ γ ↓ Y
↓-mono-⊆ []      X⊆Y u = ≼-refl refl
↓-mono-⊆ (α ∥ β) X⊆Y u = ≼-cong-∥ (↓-mono-⊆ α X⊆Y u) (↓-mono-⊆ β X⊆Y u)
↓-mono-⊆ (α ; β) X⊆Y u = ≼-cong-; (↓-mono-⊆ α X⊆Y u) (↓-mono-⊆ β X⊆Y u)
↓-mono-⊆ (` y) {X} {Y} X⊆Y u with y ∈? X | y ∈? Y
... | yes _   | yes _   = ≼-refl refl
... | yes y∈X | no  y∉Y = ⊥-elim (y∉Y (X⊆Y y∈X))
... | no  y∉X | yes y∈Y = ≼-∅ (` u y y∈Y y∉X)
... | no  _   | no  _   = ≼-refl refl

-- Same statement with the "difference" phrased as an `AllCx`.
↓-mono-⊆′ : ∀ {Γ : Ctx n} (γ : Struct n) {X Y : Subset n} → X ⊆ Y →
  AllCx Unr Γ (γ ↓ Y ↓ ∁ X) → Γ ∶ γ ↓ X ≼ γ ↓ Y
↓-mono-⊆′ γ {X} {Y} X⊆Y U =
  subst (_ ∶_≼ γ ↓ Y) (↓-↓-⊆ γ X⊆Y) (↓-strip≼ (γ ↓ Y) U)

------------------------------------------------------------------------
-- 6.  Finite distributivity of `⊎` over the leaves of two structures.
--     (∀u∀v. Mob u ⊎ Mob v) → (∀u. Mob u) ⊎ (∀v. Mob v) — constructive,
--     because the disjunctions are DATA we may match on.

private
  mob-dist₁ : {Γ : Ctx n} (u : 𝔽 n) (Q : Struct n) →
    (∀ v → v ∈ₘ Q → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)) →
    Mobile (Γ ﹫ u) ⊎ MobCx Γ Q
  mob-dist₁ u []    f = inj₂ []
  mob-dist₁ u (` v) f with f v (mem-self v)
  ... | inj₁ mob-u = inj₁ mob-u
  ... | inj₂ mob-v = inj₂ (` mob-v)
  mob-dist₁ u (Q₁ ∥ Q₂) f with mob-dist₁ u Q₁ (λ v v∈ → f v (mem-parL {α = Q₁} {Q₂} v∈))
  ... | inj₁ mob-u = inj₁ mob-u
  ... | inj₂ C₁ with mob-dist₁ u Q₂ (λ v v∈ → f v (mem-parR {α = Q₁} {Q₂} v∈))
  ... | inj₁ mob-u = inj₁ mob-u
  ... | inj₂ C₂ = inj₂ (C₁ ∥ C₂)
  mob-dist₁ u (Q₁ ; Q₂) f with mob-dist₁ u Q₁ (λ v v∈ → f v (mem-seqL {α = Q₁} {Q₂} v∈))
  ... | inj₁ mob-u = inj₁ mob-u
  ... | inj₂ C₁ with mob-dist₁ u Q₂ (λ v v∈ → f v (mem-seqR {α = Q₁} {Q₂} v∈))
  ... | inj₁ mob-u = inj₁ mob-u
  ... | inj₂ C₂ = inj₂ (C₁ ; C₂)

mob-dist : {Γ : Ctx n} (P Q : Struct n) →
  (∀ u v → u ∈ₘ P → v ∈ₘ Q → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)) →
  MobCx Γ P ⊎ MobCx Γ Q
mob-dist []    Q f = inj₁ []
mob-dist (` u) Q f with mob-dist₁ u Q (λ v v∈ → f u v (mem-self u) v∈)
... | inj₁ mob-u = inj₁ (` mob-u)
... | inj₂ CQ = inj₂ CQ
mob-dist (P₁ ∥ P₂) Q f with mob-dist P₁ Q (λ u v u∈ → f u v (mem-parL {α = P₁} {P₂} u∈))
... | inj₂ CQ = inj₂ CQ
... | inj₁ C₁ with mob-dist P₂ Q (λ u v u∈ → f u v (mem-parR {α = P₁} {P₂} u∈))
... | inj₂ CQ = inj₂ CQ
... | inj₁ C₂ = inj₁ (C₁ ∥ C₂)
mob-dist (P₁ ; P₂) Q f with mob-dist P₁ Q (λ u v u∈ → f u v (mem-seqL {α = P₁} {P₂} u∈))
... | inj₂ CQ = inj₂ CQ
... | inj₁ C₁ with mob-dist P₂ Q (λ u v u∈ → f u v (mem-seqR {α = P₁} {P₂} u∈))
... | inj₂ CQ = inj₂ CQ
... | inj₁ C₂ = inj₁ (C₁ ; C₂)

------------------------------------------------------------------------
-- 7.  The separation predicates: what `join d α β ≼ γ` tells us about the
--     `;`-order of γ.  `SepXY` forbids an X-variable strictly before a
--     Y-variable, UNLESS one of the two is mobile (mobile variables commute,
--     so they may straddle a `;`).  `SepYX` is the mirror image.

record SepXY (Γ : Ctx n) (X Y : Subset n) (γ : Struct n) : Set where
  constructor mkSepXY
  field getXY : ∀ u v → u ∈ X → v ∈ Y → before u v γ → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
open SepXY public

record SepYX (Γ : Ctx n) (X Y : Subset n) (γ : Struct n) : Set where
  constructor mkSepYX
  field getYX : ∀ u v → u ∈ Y → v ∈ X → before u v γ → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
open SepYX public

-- `join 𝟙 α β = α ∥ β` forbids both orders; `join L α β = α ; β` puts the
-- X-part first, so only "Y before X" is forbidden; `join R α β = β ; α` is
-- the mirror image.
Sep : Dir → Ctx n → Subset n → Subset n → Struct n → Set
Sep 𝟙 Γ X Y γ = SepXY Γ X Y γ × SepYX Γ X Y γ
Sep L Γ X Y γ = SepYX Γ X Y γ
Sep R Γ X Y γ = SepXY Γ X Y γ

-- Both are inherited by substructures.
sepXY-∥ˡ : ∀ {Γ : Ctx n} {X Y α β} → SepXY Γ X Y (α ∥ β) → SepXY Γ X Y α
sepXY-∥ˡ s = mkSepXY λ u v u∈ v∈ b → getXY s u v u∈ v∈ (inj₁ b)

sepXY-∥ʳ : ∀ {Γ : Ctx n} {X Y α β} → SepXY Γ X Y (α ∥ β) → SepXY Γ X Y β
sepXY-∥ʳ s = mkSepXY λ u v u∈ v∈ b → getXY s u v u∈ v∈ (inj₂ b)

sepXY-;ˡ : ∀ {Γ : Ctx n} {X Y α β} → SepXY Γ X Y (α ; β) → SepXY Γ X Y α
sepXY-;ˡ s = mkSepXY λ u v u∈ v∈ b → getXY s u v u∈ v∈ (inj₂ (inj₁ b))

sepXY-;ʳ : ∀ {Γ : Ctx n} {X Y α β} → SepXY Γ X Y (α ; β) → SepXY Γ X Y β
sepXY-;ʳ s = mkSepXY λ u v u∈ v∈ b → getXY s u v u∈ v∈ (inj₂ (inj₂ b))

sepYX-∥ˡ : ∀ {Γ : Ctx n} {X Y α β} → SepYX Γ X Y (α ∥ β) → SepYX Γ X Y α
sepYX-∥ˡ s = mkSepYX λ u v u∈ v∈ b → getYX s u v u∈ v∈ (inj₁ b)

sepYX-∥ʳ : ∀ {Γ : Ctx n} {X Y α β} → SepYX Γ X Y (α ∥ β) → SepYX Γ X Y β
sepYX-∥ʳ s = mkSepYX λ u v u∈ v∈ b → getYX s u v u∈ v∈ (inj₂ b)

sepYX-;ˡ : ∀ {Γ : Ctx n} {X Y α β} → SepYX Γ X Y (α ; β) → SepYX Γ X Y α
sepYX-;ˡ s = mkSepYX λ u v u∈ v∈ b → getYX s u v u∈ v∈ (inj₂ (inj₁ b))

sepYX-;ʳ : ∀ {Γ : Ctx n} {X Y α β} → SepYX Γ X Y (α ; β) → SepYX Γ X Y β
sepYX-;ʳ s = mkSepYX λ u v u∈ v∈ b → getYX s u v u∈ v∈ (inj₂ (inj₂ b))

sep-∥ˡ : ∀ (d : Dir) {Γ : Ctx n} {X Y α β} → Sep d Γ X Y (α ∥ β) → Sep d Γ X Y α
sep-∥ˡ 𝟙 (s₁ , s₂) = sepXY-∥ˡ s₁ , sepYX-∥ˡ s₂
sep-∥ˡ L s = sepYX-∥ˡ s
sep-∥ˡ R s = sepXY-∥ˡ s

sep-∥ʳ : ∀ (d : Dir) {Γ : Ctx n} {X Y α β} → Sep d Γ X Y (α ∥ β) → Sep d Γ X Y β
sep-∥ʳ 𝟙 (s₁ , s₂) = sepXY-∥ʳ s₁ , sepYX-∥ʳ s₂
sep-∥ʳ L s = sepYX-∥ʳ s
sep-∥ʳ R s = sepXY-∥ʳ s

sep-;ˡ : ∀ (d : Dir) {Γ : Ctx n} {X Y α β} → Sep d Γ X Y (α ; β) → Sep d Γ X Y α
sep-;ˡ 𝟙 (s₁ , s₂) = sepXY-;ˡ s₁ , sepYX-;ˡ s₂
sep-;ˡ L s = sepYX-;ˡ s
sep-;ˡ R s = sepXY-;ˡ s

sep-;ʳ : ∀ (d : Dir) {Γ : Ctx n} {X Y α β} → Sep d Γ X Y (α ; β) → Sep d Γ X Y β
sep-;ʳ 𝟙 (s₁ , s₂) = sepXY-;ʳ s₁ , sepYX-;ʳ s₂
sep-;ʳ L s = sepYX-;ʳ s
sep-;ʳ R s = sepXY-;ʳ s
