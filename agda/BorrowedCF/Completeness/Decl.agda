-- | Facts about DECLARATIVE derivations that the completeness induction needs.
--
--   * `fv⊆dom`     every free variable of the term occurs in the structure;
--   * `fv-cover`   the variables of the structure the term does not use are
--                  unrestricted (pointwise form: `fv-cover′`);
--   * `restrict`   a derivation can be confined to the free variables of its
--                  term, and `restrict-≼` says the confined structure is a
--                  subcontext of the original one.
--
--   The module also re-exports the effect bridges (`Decl.Eff`), the `Solved`
--   inversions (`Decl.Solved`), the subset/domain plumbing (`Decl.Subsets`)
--   and agent C1's `LinStruct` lemmas (`Split.Lin`).
module BorrowedCF.Completeness.Decl where

open import Data.Fin.Subset as S
  using (Subset; Side; inside; outside; _∈_; _∉_; _⊆_; _∪_; ∁; ⁅_⁆) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
  using ( _∈?_; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁺; x∈p∪q⁻; p⊆p∪q; q⊆p∪q
        ; x∈p⇒x∉∁p; x∈∁p⇒x∉p; x∉p⇒x∈∁p; ⊆-refl; ⊆-trans )
  renaming (∉⊥ to ∉⁅⁆)
open import Relation.Nullary.Decidable using (dec-true)

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Terms
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Algorithmic using (fv; fvClose; fvClose*; _∣fv[_])

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Completeness.Base using (LinStruct; SolvedCtx) public
open import BorrowedCF.Completeness.Decl.Subsets public
open import BorrowedCF.Completeness.Decl.Eff public
open import BorrowedCF.Completeness.Decl.Solved public
open import BorrowedCF.Completeness.Split.Lin public

open Nat.Variables

private variable
  e e₁ e₂ : Tm n

------------------------------------------------------------------------
-- 1.  Free variables occur in the structure.

fv⊆dom : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → fv e ⊆ dom γ
fv⊆dom (T-Const ⊢c)   y∈ = ⊥-elim (∉⁅⁆ y∈)
fv⊆dom (T-Var x T-eq) y∈ = y∈
fv⊆dom {γ = γ} (T-Abs {a = a} Γ-unr Γ-mob d) y∈ =
  ∈-bind⁻ (Arr.dir a) γ (fv⊆dom d (∈tail⁻ y∈))
fv⊆dom {γ = γ} (T-AbsRec Γ-unr a-unr d) y∈ =
  ∈-absrec⁻ γ (fv⊆dom d (∈tail⁻ (∈tail⁻ y∈)))
fv⊆dom (T-AppUnr a-unr ≤ₐ d₁ d₂) y∈ =
  x∈p∪q⁺ (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-AppLin a-par ≤ₐ d₁ d₂) y∈ =
  x∈p∪q⁺ (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-AppLeft aL ≤ₐ d₁ d₂) y∈ =
  x∈p∪q⁺ (Sum.swap (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈)))
fv⊆dom (T-AppRight aR ≤ₐ d₁ d₂) y∈ =
  x∈p∪q⁺ (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-Pair p/s {γ₁} {γ₂} seq⇒p d₁ d₂) y∈ =
  ∈-join⁺ (biasedDir p/s) γ₁ γ₂ (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-Let p/s {γ₁} {γ₂} d₁ d₂) y∈ =
  ∈-join⁺ p/s γ₁ γ₂
    (Sum.map (fv⊆dom d₁)
             (λ p → ∈-bind⁻ p/s γ₂ (fv⊆dom d₂ (∈tail⁻ p)))
             (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-Seq unr-T d₁ d₂) y∈ =
  x∈p∪q⁺ (Sum.map (fv⊆dom d₁) (fv⊆dom d₂) (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-LetPair {d = d} p/s {γ₁} {γ₂} d₁ d₂) y∈ =
  ∈-join⁺ p/s γ₁ γ₂
    (Sum.map (fv⊆dom d₁)
             (λ p → ∈-bind²⁻ p/s d γ₂ (fv⊆dom d₂ (∈drop⁻ 2 p)))
             (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-Inj d) y∈ = fv⊆dom d y∈
fv⊆dom (T-Case p/s {γ₁} {γ₂} d d₁ d₂) y∈ =
  ∈-join⁺ p/s γ₁ γ₂
    (Sum.map (fv⊆dom d)
             (λ p → [ (λ q → ∈-bind⁻ p/s γ₂ (fv⊆dom d₁ (∈tail⁻ q)))
                    , (λ q → ∈-bind⁻ p/s γ₂ (fv⊆dom d₂ (∈tail⁻ q))) ]′
                    (x∈p∪q⁻ _ _ p))
             (x∈p∪q⁻ _ _ y∈))
fv⊆dom (T-Conv T≃ ϵ≤ d) y∈ = fv⊆dom d y∈
fv⊆dom (T-Weaken γ≤ d)  y∈ = ≼⇒dom⊆ γ≤ (fv⊆dom d y∈)

------------------------------------------------------------------------
-- 2.  Structure variables the term does not use are unrestricted.

fv-cover′ : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → ∀ {y} → y ∈ dom γ → y ∉ fv e → Unr (Γ ﹫ y)
fv-cover′ (T-Const ⊢c)   y∈ y∉ = ⊥-elim (∉⁅⁆ y∈)
fv-cover′ (T-Var x T-eq) y∈ y∉ = ⊥-elim (y∉ y∈)
fv-cover′ {γ = γ} (T-Abs {a = a} Γ-unr Γ-mob d) y∈ y∉ =
  fv-cover′ d (∈-bind⁺ (Arr.dir a) γ y∈) (λ p → y∉ (∈tail⁺ p))
fv-cover′ {γ = γ} (T-AbsRec Γ-unr a-unr d) y∈ y∉ =
  fv-cover′ d (∈-absrec⁺ γ y∈) (λ p → y∉ (∈tail⁺ (∈tail⁺ p)))
fv-cover′ (T-AppUnr a-unr ≤ₐ d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q)))) ]′ (x∈p∪q⁻ _ _ y∈)
fv-cover′ (T-AppLin a-par ≤ₐ d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q)))) ]′ (x∈p∪q⁻ _ _ y∈)
fv-cover′ (T-AppLeft aL ≤ₐ d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q))))
  , (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q)))) ]′ (x∈p∪q⁻ _ _ y∈)
fv-cover′ (T-AppRight aR ≤ₐ d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q)))) ]′ (x∈p∪q⁻ _ _ y∈)
fv-cover′ (T-Pair p/s {γ₁} {γ₂} seq⇒p d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q)))) ]′
    (∈-join⁻ (biasedDir p/s) γ₁ γ₂ y∈)
fv-cover′ (T-Let p/s {γ₁} {γ₂} d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ (∈-bind⁺ p/s γ₂ p) (λ q → y∉ (x∈p∪q⁺ (inj₂ (∈tail⁺ q))))) ]′
    (∈-join⁻ p/s γ₁ γ₂ y∈)
fv-cover′ (T-Seq unr-T d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ p (λ q → y∉ (x∈p∪q⁺ (inj₂ q)))) ]′ (x∈p∪q⁻ _ _ y∈)
fv-cover′ (T-LetPair {d = d} p/s {γ₁} {γ₂} d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d₁ p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₂ (∈-bind²⁺ p/s d γ₂ p)
                        (λ q → y∉ (x∈p∪q⁺ (inj₂ (∈drop⁺ 2 q))))) ]′
    (∈-join⁻ p/s γ₁ γ₂ y∈)
fv-cover′ (T-Inj d) y∈ y∉ = fv-cover′ d y∈ y∉
fv-cover′ (T-Case p/s {γ₁} {γ₂} d d₁ d₂) y∈ y∉ =
  [ (λ p → fv-cover′ d p (λ q → y∉ (x∈p∪q⁺ (inj₁ q))))
  , (λ p → fv-cover′ d₁ (∈-bind⁺ p/s γ₂ p)
                        (λ q → y∉ (x∈p∪q⁺ (inj₂ (x∈p∪q⁺ (inj₁ (∈tail⁺ q))))))) ]′
    (∈-join⁻ p/s γ₁ γ₂ y∈)
fv-cover′ (T-Conv T≃ ϵ≤ d) y∈ y∉ = fv-cover′ d y∈ y∉
fv-cover′ {Γ = Γ} (T-Weaken {γ₁ = γ₁} {γ₂ = γ₂} γ≤ d) {y} y∈ y∉ with y ∈? dom γ₁
... | yes y∈₁ = fv-cover′ d y∈₁ y∉
... | no  y∉₁ = allCx-↓⁻ γ₂ (≼⇒extra-Unr γ≤) y∈ (x∉p⇒x∈∁p y∉₁)

fv-cover : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → AllCx Unr Γ (γ ↓ ∁ (fv e))
fv-cover {γ = γ} d = allCx-↓⁺ γ (λ y∈ y∈∁ → fv-cover′ d y∈ (x∈∁p⇒x∉p y∈∁))

------------------------------------------------------------------------
-- 3.  A derivation can be confined to the free variables of its term.

private
  -- Growing the restriction set on one side of a rule: the variables that come
  -- in are not free in that premise's term, hence unrestricted by `fv-cover′`.
  ∪ˡ : {Γ : Ctx n} (γ : Struct n) {X Y : Subset n} →
       (∀ {z} → z ∈ dom γ → z ∉ X → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ X ≼ γ ↓ (X ∪ Y)
  ∪ˡ γ u = ↓-≼-↓ γ (p⊆p∪q _) u

  ∪ʳ : {Γ : Ctx n} (γ : Struct n) {X Y : Subset n} →
       (∀ {z} → z ∈ dom γ → z ∉ Y → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ Y ≼ γ ↓ (X ∪ Y)
  ∪ʳ γ u = ↓-≼-↓ γ (q⊆p∪q _ _) u

restrict : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ↓ fv e ⊢ e ∶ T ∣ ϵ
restrict (T-Const ⊢c) = T-Const ⊢c
restrict (T-Var x T-eq) rewrite dec-true (x ∈? ⁅ x ⁆) (x∈⁅x⁆ x) = T-Var x T-eq
restrict {γ = γ} (T-Abs {a = a} {e = e} Γ-unr Γ-mob d) =
  T-Abs (allCx-↓ ∘ Γ-unr) (allCx-↓ ∘ Γ-mob)
    (subst-γ (↓-bind (Arr.dir a) γ (fvClose (fv e)))
      (T-Weaken (↓-≼-↓ (join (Arr.dir a) (` zero) (𝐂.wk γ))
                       (⊆-inside∷ ⊆-refl) (fv-cover′ d))
                (restrict d)))
restrict {γ = γ} (T-AbsRec {e = e} Γ-unr a-unr d) =
  T-AbsRec (allCx-↓ Γ-unr) a-unr
    (subst-γ (↓-absrec γ (fvClose (fvClose (fv e))))
      (T-Weaken (↓-≼-↓ (((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ))
                       (⊆-inside²∷-tail ⊆-refl) (fv-cover′ d))
                (restrict d)))
restrict (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} a-unr ≤ₐ d₁ d₂) =
  T-Weaken (≼-cong-∥ (∪ˡ γ₁ (fv-cover′ d₁)) (∪ʳ γ₂ (fv-cover′ d₂)))
           (T-AppUnr a-unr ≤ₐ (restrict d₁) (restrict d₂))
restrict (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} a-par ≤ₐ d₁ d₂) =
  T-Weaken (≼-cong-∥ (∪ˡ γ₁ (fv-cover′ d₁)) (∪ʳ γ₂ (fv-cover′ d₂)))
           (T-AppLin a-par ≤ₐ (restrict d₁) (restrict d₂))
restrict (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} aL ≤ₐ d₁ d₂) =
  T-Weaken (≼-cong-; (∪ʳ γ₂ (fv-cover′ d₂)) (∪ˡ γ₁ (fv-cover′ d₁)))
           (T-AppLeft aL ≤ₐ (restrict d₁) (restrict d₂))
restrict (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} aR ≤ₐ d₁ d₂) =
  T-Weaken (≼-cong-; (∪ˡ γ₁ (fv-cover′ d₁)) (∪ʳ γ₂ (fv-cover′ d₂)))
           (T-AppRight aR ≤ₐ (restrict d₁) (restrict d₂))
restrict (T-Pair p/s {γ₁} {γ₂} seq⇒p d₁ d₂) =
  subst-γ (sym (join-↓ (biasedDir p/s) γ₁ γ₂))
    (T-Pair p/s seq⇒p (T-Weaken (∪ˡ γ₁ (fv-cover′ d₁)) (restrict d₁))
                      (T-Weaken (∪ʳ γ₂ (fv-cover′ d₂)) (restrict d₂)))
restrict (T-Let {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) =
  subst-γ (sym (join-↓ p/s γ₁ γ₂))
    (T-Let p/s (T-Weaken (∪ˡ γ₁ (fv-cover′ d₁)) (restrict d₁))
               (subst-γ (↓-bind p/s γ₂ (fv e₁ ∪ fvClose (fv e₂)))
                 (T-Weaken (↓-≼-↓ (join p/s (` zero) (𝐂.wk γ₂))
                                  (⊆-inside∷ (q⊆p∪q _ _)) (fv-cover′ d₂))
                           (restrict d₂))))
restrict (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} unr-T d₁ d₂) =
  T-Weaken (≼-cong-; (∪ˡ γ₁ (fv-cover′ d₁)) (∪ʳ γ₂ (fv-cover′ d₂)))
           (T-Seq unr-T (restrict d₁) (restrict d₂))
restrict {e = `let⊗ e₁ `in e₂} (T-LetPair {d = d} p/s {γ₁} {γ₂} d₁ d₂) =
  subst-γ (sym (join-↓ p/s γ₁ γ₂))
    (T-LetPair p/s (T-Weaken (∪ˡ γ₁ (fv-cover′ d₁)) (restrict d₁))
                   (subst-γ (↓-bind² p/s d γ₂ (fv e₁ ∪ fvClose* 2 (fv e₂)))
                     (T-Weaken (↓-≼-↓ (join p/s (join d (` zero) (` suc zero))
                                            (𝐂.wk (𝐂.wk γ₂)))
                                      (⊆-inside²∷ (q⊆p∪q _ _)) (fv-cover′ d₂))
                               (restrict d₂))))
restrict (T-Inj d) = T-Inj (restrict d)
restrict (T-Case {e = e} {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d d₁ d₂) =
  subst-γ (sym (join-↓ p/s γ₁ γ₂))
    (T-Case p/s (T-Weaken (∪ˡ γ₁ (fv-cover′ d)) (restrict d))
                (subst-γ (↓-bind p/s γ₂ fvE)
                  (T-Weaken (↓-≼-↓ (join p/s (` zero) (𝐂.wk γ₂))
                                   (⊆-inside∷ (⊆-trans (p⊆p∪q _) (q⊆p∪q _ _)))
                                   (fv-cover′ d₁))
                            (restrict d₁)))
                (subst-γ (↓-bind p/s γ₂ fvE)
                  (T-Weaken (↓-≼-↓ (join p/s (` zero) (𝐂.wk γ₂))
                                   (⊆-inside∷ (⊆-trans (q⊆p∪q _ _) (q⊆p∪q _ _)))
                                   (fv-cover′ d₂))
                            (restrict d₂))))
  where fvE = fv e ∪ fvClose (fv e₁) ∪ fvClose (fv e₂)
restrict (T-Conv T≃ ϵ≤ d) = T-Conv T≃ ϵ≤ (restrict d)
restrict (T-Weaken γ≤ d)  = T-Weaken (↓-mono-≼ γ≤) (restrict d)

-- The same statement in the notation the algorithmic rules use.
restrict-∣fv : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ∣fv[ e ] ⊢ e ∶ T ∣ ϵ
restrict-∣fv = restrict

-- Confining the body of a binder to any set that covers its free variables.
-- These are the forms the T-Abs / T-Let / T-Case (and A-Let / A-Case) cases of
-- the main induction need: A-Case, for instance, types both branches under
-- `join p/s (` 0F) (𝐂.wk (γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂))))`, which is
-- `restrict-bind p/s γ (fvClose (fv e₁) ∪ fvClose (fv e₂))` applied to the
-- branch derivation.
restrict-bind : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) {Γ′ : Ctx (suc n)}
  (γ : Struct n) (X : Subset n) {e : Tm (suc n)} {U : 𝕋} {ϵ : Eff} →
  fvClose (fv e) ⊆ X →
  Γ′ ; join a (` zero) (𝐂.wk γ) ⊢ e ∶ U ∣ ϵ →
  Γ′ ; join a (` zero) (𝐂.wk (γ ↓ X)) ⊢ e ∶ U ∣ ϵ
restrict-bind a γ X ⊆X d =
  subst-γ (↓-bind a γ X)
    (T-Weaken (↓-≼-↓ (join a (` zero) (𝐂.wk γ)) (⊆-inside∷ ⊆X) (fv-cover′ d))
              (restrict d))

restrict-bind² : ∀ {A B : Set} ⦃ J : Join A ⦄ ⦃ J′ : Join B ⦄ (a : A) (b : B)
  {Γ′ : Ctx (2 + n)} (γ : Struct n) (X : Subset n) {e : Tm (2 + n)} {U : 𝕋} {ϵ : Eff} →
  fvClose* 2 (fv e) ⊆ X →
  Γ′ ; join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)) ⊢ e ∶ U ∣ ϵ →
  Γ′ ; join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk (γ ↓ X))) ⊢ e ∶ U ∣ ϵ
restrict-bind² a b γ X ⊆X d =
  subst-γ (↓-bind² a b γ X)
    (T-Weaken (↓-≼-↓ (join a (join b (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)))
                     (⊆-inside²∷ ⊆X) (fv-cover′ d))
              (restrict d))

restrict-absrec : {Γ′ : Ctx (2 + n)} (γ : Struct n) (X : Subset n)
  {e : Tm (2 + n)} {U : 𝕋} {ϵ : Eff} →
  fvClose (fvClose (fv e)) ⊆ X →
  Γ′ ; ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ) ⊢ e ∶ U ∣ ϵ →
  Γ′ ; ((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk (γ ↓ X)) ⊢ e ∶ U ∣ ϵ
restrict-absrec γ X ⊆X d =
  subst-γ (↓-absrec γ X)
    (T-Weaken (↓-≼-↓ (((` zero) ∥ (` suc zero)) ∥ 𝐂.wk (𝐂.wk γ))
                     (⊆-inside²∷-tail ⊆X) (fv-cover′ d))
              (restrict d))

-- The confined structure is a subcontext of the original one.
restrict-≼ : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ∶ γ ↓ fv e ≼ γ
restrict-≼ {γ = γ} d = ↓-strip≼ γ (fv-cover d)

------------------------------------------------------------------------
-- 4.  LinStruct.  Agent C1 proved these in Completeness/Split/Lin.agda
--     (`lin-≼`, `lin-↓`, `lin-join⁻`, `lin-;⁻`, `lin-∥⁻`, `lin-wk`, `lin-bind`,
--     `lin-bind₂`, `lin-bind-rec`); this module re-exports them rather than
--     duplicating the proofs.  The two names my task statement fixed are
--     aliases of C1's.

lin-join⁻′ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (Γ : Ctx n) (α β : Struct n) →
  LinStruct Γ (join a α β) → LinStruct Γ α × LinStruct Γ β
lin-join⁻′ = lin-join⁻

lin-bind′ : ∀ {A : Set} ⦃ J : Join A ⦄ (a : A) (T : 𝕋) (Γ : Ctx n) (γ : Struct n) →
  LinStruct Γ γ → LinStruct (T ⸴ Γ) (join a (` zero) (𝐂.wk γ))
lin-bind′ = lin-bind
