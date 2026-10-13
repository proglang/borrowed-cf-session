-- | Completeness toolkit, part 2: `LinStruct` (every non-`Unr` variable occurs
--   at most once) is inherited by everything the completeness proof builds.
--
--   CALLING CONVENTION.  `LinStruct Γ γ` unfolds to a Π-type in which Γ occurs
--   only under `lookup`, so Agda can never solve Γ (or γ, or the binder types)
--   from a `LinStruct` argument or goal.  Every such argument is therefore
--   EXPLICIT here.  Only `lin-≼` keeps them implicit: there the `≼` argument
--   pins them down.
module BorrowedCF.Completeness.Split.Lin where

open import Data.Fin.Subset using (Subset)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution using (wk)
open import BorrowedCF.Completeness.Base using (LinStruct)
open import BorrowedCF.Completeness.Split.Base using (count-↓≤)
open import BorrowedCF.Simulation.Support.Confine
  using (count; ≼⇒count≤; count-wk-zero; count-wk-suc)

open Nat.Variables
open Variables
open Fin.Patterns

private
  variable
    A : Set

-- `count` is additive over any `join`, in one generic lemma.
count-join : ⦃ J : Join A ⦄ (a : A) (x : 𝔽 n) (α β : Struct n) →
  count x (join a α β) ≡ count x α + count x β
count-join a x α β with joinDir a
... | 𝟙 = refl
... | L = refl
... | R = Nat.+-comm (count x β) (count x α)

------------------------------------------------------------------------
-- Closure properties of `LinStruct`.

lin-≼ : {Γ : Ctx n} {γ₁ γ₂ : Struct n} → LinStruct Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → LinStruct Γ γ₁
lin-≼ lin ≤γ x ¬u = Nat.≤-trans (≼⇒count≤ ¬u ≤γ) (lin x ¬u)

lin-↓ : (Γ : Ctx n) (γ : Struct n) (X : Subset n) → LinStruct Γ γ → LinStruct Γ (γ ↓ X)
lin-↓ Γ γ X lin x ¬u = Nat.≤-trans (count-↓≤ γ x X) (lin x ¬u)

lin-join⁻ : ⦃ J : Join A ⦄ (a : A) (Γ : Ctx n) (α β : Struct n) →
  LinStruct Γ (join a α β) → LinStruct Γ α × LinStruct Γ β
lin-join⁻ a Γ α β lin =
    (λ x ¬u → Nat.≤-trans (Nat.m≤m+n (count x α) (count x β))
                          (Nat.≤-trans (Nat.≤-reflexive (sym (count-join a x α β))) (lin x ¬u)))
  , (λ x ¬u → Nat.≤-trans (Nat.m≤n+m (count x β) (count x α))
                          (Nat.≤-trans (Nat.≤-reflexive (sym (count-join a x α β))) (lin x ¬u)))

-- The `;`-shaped and `∥`-shaped instances, spelled out.
lin-;⁻ : (Γ : Ctx n) (α β : Struct n) → LinStruct Γ (α ; β) → LinStruct Γ α × LinStruct Γ β
lin-;⁻ = lin-join⁻ L

lin-∥⁻ : (Γ : Ctx n) (α β : Struct n) → LinStruct Γ (α ∥ β) → LinStruct Γ α × LinStruct Γ β
lin-∥⁻ = lin-join⁻ 𝟙

------------------------------------------------------------------------
-- Under binders.  `wk` is the structure renaming of Context/Substitution.

lin-wk : (T : 𝕋) (Γ : Ctx n) (γ : Struct n) → LinStruct Γ γ → LinStruct (T ⸴ Γ) (wk γ)
lin-wk T Γ γ lin zero    ¬u = Nat.≤-trans (Nat.≤-reflexive (count-wk-zero γ)) Nat.z≤n
lin-wk T Γ γ lin (suc y) ¬u = Nat.≤-trans (Nat.≤-reflexive (count-wk-suc γ y)) (lin y ¬u)

-- T-Abs / A-Abs / T-Let / T-Case / A-Case shape.
lin-bind : ⦃ J : Join A ⦄ (a : A) (T : 𝕋) (Γ : Ctx n) (γ : Struct n) →
  LinStruct Γ γ → LinStruct (T ⸴ Γ) (join a (` 0F) (wk γ))
lin-bind a T Γ γ lin zero ¬u = Nat.≤-reflexive eq
  where eq : count 0F (join a (` 0F) (wk γ)) ≡ 1
        eq = count-join a _ (` 0F) (wk γ) ■ cong (1 +_) (count-wk-zero γ)
lin-bind a T Γ γ lin (suc y) ¬u = Nat.≤-trans (Nat.≤-reflexive eq) (lin y ¬u)
  where eq : count (suc y) (join a (` 0F) (wk γ)) ≡ count y γ
        eq = count-join a _ (` 0F) (wk γ) ■ count-wk-suc γ y

-- T-LetPair / A-LetPair shape: two binders, joined among themselves by `d`
-- and with the twice-weakened structure by `a`.
lin-bind₂ : ⦃ J : Join A ⦄ (a : A) (d : Dir) (T U : 𝕋) (Γ : Ctx n) (γ : Struct n) →
  LinStruct Γ γ → LinStruct (T ⸴ U ⸴ Γ) (join a (join d (` 0F) (` 1F)) (wk (wk γ)))
lin-bind₂ a d T U Γ γ lin zero ¬u = Nat.≤-reflexive eq
  where eq : count 0F (join a (join d (` 0F) (` 1F)) (wk (wk γ))) ≡ 1
        eq = count-join a _ _ _
           ■ cong₂ _+_ (count-join d _ (` 0F) (` 1F)) (count-wk-zero (wk γ))
lin-bind₂ a d T U Γ γ lin (suc zero) ¬u = Nat.≤-reflexive eq
  where eq : count 1F (join a (join d (` 0F) (` 1F)) (wk (wk γ))) ≡ 1
        eq = count-join a _ _ _
           ■ cong₂ _+_ (count-join d _ (` 0F) (` 1F))
                       (count-wk-suc (wk γ) zero ■ count-wk-zero γ)
lin-bind₂ a d T U Γ γ lin (suc (suc y)) ¬u = Nat.≤-trans (Nat.≤-reflexive eq) (lin y ¬u)
  where eq : count (suc (suc y)) (join a (join d (` 0F) (` 1F)) (wk (wk γ))) ≡ count y γ
        eq = count-join a _ _ _
           ■ cong₂ _+_ (count-join d _ (` 0F) (` 1F))
                       (count-wk-suc (wk γ) (suc y) ■ count-wk-suc γ y)

-- T-AbsRec / A-AbsRec shape.
lin-bind-rec : (T U : 𝕋) (Γ : Ctx n) (γ : Struct n) →
  LinStruct Γ γ → LinStruct (T ⸴ U ⸴ Γ) ((` 0F) ∥ (` 1F) ∥ wk (wk γ))
lin-bind-rec T U Γ γ lin zero ¬u =
  Nat.≤-reflexive (cong (1 +_) (count-wk-zero (wk γ)))
lin-bind-rec T U Γ γ lin (suc zero) ¬u =
  Nat.≤-reflexive (cong (1 +_) (count-wk-suc (wk γ) zero ■ count-wk-zero γ))
lin-bind-rec T U Γ γ lin (suc (suc y)) ¬u =
  Nat.≤-trans (Nat.≤-reflexive (count-wk-suc (wk γ) (suc y) ■ count-wk-suc γ y)) (lin y ¬u)
