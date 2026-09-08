-- | Completeness toolkit, part 5: everything `canon-core` needs is EXTRACTED
--   from one admissible split `Γ ∶ join d α β ≼ γ` plus linearity of γ.
--
--     * `canon-disj` : X ∩ Y contains only unrestricted variables.
--     * `canon-out`  : everything of γ outside X ∪ Y is unrestricted.
--     * `canon-sep`  : the `;`-order of γ does not contradict the split
--                      (`Sep d`), with mobility witnesses where it looks like
--                      it does.
module BorrowedCF.Completeness.Split.Extract where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; _∪_; ∁)
open import Data.Fin.Subset.Properties using (_∈?_; x∈p∪q⁺; x∈p∪q⁻)
open import Relation.Nullary.Decidable using (decidable-stable)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Completeness.Base using (LinStruct)
open import BorrowedCF.Completeness.Split.Base
open import BorrowedCF.Completeness.Split.Lin using (count-join)
open import BorrowedCF.Completeness.Split.Order using (before-mob-≼; Esc; getEsc)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (_∈ₘ_; before; before⇒mem; count-≼-eq)

open Nat.Variables
open Variables

private
  variable
    A : Set

private
  -- 2 ≤ 1 is absurd.
  2≰1 : 2 Nat.≤ 1 → ⊥
  2≰1 (Nat.s≤s ())

  ∈dom-of-mem : {δ : Struct n} {x : 𝔽 n} {X : Subset n} (δ′ : Struct n) →
    δ′ ≡ δ → x ∈ₘ δ → dom δ ⊆ X → x ∈ X
  ∈dom-of-mem δ′ refl x∈ ⊆X = ⊆X (mem⇒∈dom δ′ x∈)

-- Convenience: a variable of δ lands in any superset of `dom δ`.
mem⇒∈ : (δ : Struct n) {x : 𝔽 n} {X : Subset n} → x ∈ₘ δ → dom δ ⊆ X → x ∈ X
mem⇒∈ δ x∈ ⊆X = ⊆X (mem⇒∈dom δ x∈)

------------------------------------------------------------------------
-- 1.  X ∩ Y is unrestricted.

canon-disj : ⦃ J : Join A ⦄ (a : A) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ → Γ ∶ join a α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)
canon-disj a X Y {α} {β} {γ} lin ≤γ dα dβ uX uY z z∈X z∈Y =
  decidable-stable (unr? _) λ ¬Uz →
    let z∈domα : z ∈ dom α
        z∈domα = decidable-stable (z ∈? dom α) λ z∉ → ¬Uz (uX z z∈X z∉)
        z∈domβ : z ∈ dom β
        z∈domβ = decidable-stable (z ∈? dom β) λ z∉ → ¬Uz (uY z z∈Y z∉)
        cα : 1 Nat.≤ count z α
        cα = Nat.n≢0⇒n>0 (∈dom⇒mem α z∈domα)
        cβ : 1 Nat.≤ count z β
        cβ = Nat.n≢0⇒n>0 (∈dom⇒mem β z∈domβ)
        two : 2 Nat.≤ count z (join a α β)
        two = Nat.≤-trans (Nat.+-mono-≤ cα cβ) (Nat.≤-reflexive (sym (count-join a z α β)))
    in 2≰1 (Nat.≤-trans two (Nat.≤-trans (Nat.≤-reflexive (count-≼-eq ¬Uz ≤γ)) (lin z ¬Uz)))

------------------------------------------------------------------------
-- 2.  Outside X ∪ Y, γ is unrestricted.

canon-out : ⦃ J : Join A ⦄ (a : A) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  Γ ∶ join a α β ≼ γ → dom α ⊆ X → dom β ⊆ Y →
  AllCx Unr Γ (γ ↓ ∁ (X ∪ Y))
canon-out a X Y {α} {β} {γ} ≤γ dα dβ =
  ↓-⊆ γ (⊆-∁⁺ dom⊆) (≼⇒extra-Unr ≤γ)
  where
  dom⊆ : dom (join a α β) ⊆ X ∪ Y
  dom⊆ {z} z∈ with x∈p∪q⁻ (dom α) (dom β) (subst (z ∈_) (dom-join a α β) z∈)
  ... | inj₁ z∈α = x∈p∪q⁺ (inj₁ (dα z∈α))
  ... | inj₂ z∈β = x∈p∪q⁺ (inj₂ (dβ z∈β))

------------------------------------------------------------------------
-- 3.  The separation property.

private
  module _ {n} {Γ : Ctx n} {X Y : Subset n}
           (disj : ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)) where

    -- Dispatch on `Unr` (decidable) before appealing to `before-mob-≼`.
    step : {α γ : Struct n} → Γ ∶ α ≼ γ →
      (u v : 𝔽 n) → before u v γ →
      (¬ Unr (Γ ﹫ u) → ¬ Unr (Γ ﹫ v) → before u v α → ⊥) →
      Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
    step ≤γ u v bef k with unr? (Γ ﹫ u)
    ... | yes Uu = inj₁ (unr⇒mobile Uu)
    ... | no ¬Uu with unr? (Γ ﹫ v)
    ...   | yes Uv = inj₂ (unr⇒mobile Uv)
    ...   | no ¬Uv with before-mob-≼ ¬Uu ¬Uv ≤γ bef
    ...     | inj₂ e = getEsc e
    ...     | inj₁ b = ⊥-elim (k ¬Uu ¬Uv b)

canon-sep : (d : Dir) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  Γ ∶ join d α β ≼ γ → dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)) →
  Sep d Γ X Y γ
canon-sep 𝟙 X Y {α} {β} ≤γ dα dβ disj =
    mkSepXY (λ u v u∈X v∈Y bef → step disj ≤γ u v bef λ ¬Uu ¬Uv →
      [ (λ bα → ¬Uv (disj v (mem⇒∈ α (proj₂ (before⇒mem α bα)) dα) v∈Y))
      , (λ bβ → ¬Uu (disj u u∈X (mem⇒∈ β (proj₁ (before⇒mem β bβ)) dβ)))
      ]′)
  , mkSepYX (λ u v u∈Y v∈X bef → step disj ≤γ u v bef λ ¬Uu ¬Uv →
      [ (λ bα → ¬Uu (disj u (mem⇒∈ α (proj₁ (before⇒mem α bα)) dα) u∈Y))
      , (λ bβ → ¬Uv (disj v v∈X (mem⇒∈ β (proj₂ (before⇒mem β bβ)) dβ)))
      ]′)
canon-sep L X Y {α} {β} ≤γ dα dβ disj =
  mkSepYX (λ u v u∈Y v∈X bef → step disj ≤γ u v bef λ ¬Uu ¬Uv →
    [ (λ (u∈α , _) → ¬Uu (disj u (mem⇒∈ α u∈α dα) u∈Y))
    , [ (λ bα → ¬Uu (disj u (mem⇒∈ α (proj₁ (before⇒mem α bα)) dα) u∈Y))
      , (λ bβ → ¬Uv (disj v v∈X (mem⇒∈ β (proj₂ (before⇒mem β bβ)) dβ)))
      ]′
    ]′)
canon-sep R X Y {α} {β} ≤γ dα dβ disj =
  mkSepXY (λ u v u∈X v∈Y bef → step disj ≤γ u v bef λ ¬Uu ¬Uv →
    [ (λ (u∈β , _) → ¬Uu (disj u u∈X (mem⇒∈ β u∈β dβ)))
    , [ (λ bβ → ¬Uu (disj u u∈X (mem⇒∈ β (proj₁ (before⇒mem β bβ)) dβ)))
      , (λ bα → ¬Uv (disj v (mem⇒∈ α (proj₂ (before⇒mem α bα)) dα) v∈Y))
      ]′
    ]′)
