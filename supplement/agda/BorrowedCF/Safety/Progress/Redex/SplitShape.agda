-- | Every binder position is a SPLIT position (agent G1, wave 2).
--
--   `Simulation/BackwardSoup/Canonical.agda`'s `canon-lsplit` / `canon-rsplit`
--   ask for a `SplitShape B₁ B₂ local`: the group list of the handle's side
--   written as `G₁ ++ (q + suc b) ∷ G₂` with the handle at `splitIx G₁ G₂ q b`.
--   Unlike `HeadShape` and `AcqShape` this is no restriction at all -- ANY
--   position of ANY group is of that form, with `q` the offset and `b` the
--   number of handles behind it in the group.  `split-shape` builds the witness
--   from the `GroupOf` view.
--
--   `Simulation/BackwardSoup/Leaves/RSplit.agda` proves the same facts, but
--   inside a `private` block (its `split-shape`, lines 507-516), so they are
--   re-proved here rather than imported.  The `Fin.toℕ` bookkeeping is the same
--   as there: `SplitShape` pins the index up to a `Fin.cast` along `sum-++`, so
--   every step goes through `Fin.toℕ-injective`.
module BorrowedCF.Safety.Progress.Redex.SplitShape where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
import Data.Nat.Properties as NatP

open import BorrowedCF.Prelude

open import BorrowedCF.Processes.Typed using (BindGroup)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (SplitShape; split-l; split-r; splitIx)
open import BorrowedCF.Simulation.BackwardSoup.Locate using (ProcessContext)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using ( Binder; sideOf; SideOf; inl; inr
        ; GroupOf; head-group; next-group; groupOf )

open Nat.Variables
open Fin.Patterns

private
  fin-split : (b : ℕ) (z : 𝔽 b) → Σ[ rest ∈ ℕ ] b ≡ Fin.toℕ z + suc rest
  fin-split b z =
    b Nat.∸ suc q
    , sym (NatP.+-suc q (b Nat.∸ suc q) ■ NatP.m+[n∸m]≡n (Fin.toℕ<n z))
    where
    q = Fin.toℕ z

  splitIx-toℕ :
    (G₁ G₂ : BindGroup) (q b : ℕ) →
    Fin.toℕ (splitIx G₁ G₂ q b) ≡ sum G₁ + q
  splitIx-toℕ G₁ G₂ q b =
    Fin.toℕ-cast
      (sym (sum-++ G₁ ((q + suc b) L.∷ G₂)))
      (sum G₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum G₂))
    ■ Fin.toℕ-↑ʳ (sum G₁) ((q ↑ʳ 0F) ↑ˡ sum G₂)
    ■ cong (sum G₁ +_)
        (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (sum G₂)
         ■ Fin.toℕ-↑ʳ q 0F
         ■ NatP.+-identityʳ q)

  transportSplitShapeˡ :
    {B B′ C : BindGroup} {i : 𝔽 (sum B + sum C)} {i′ : 𝔽 (sum B′ + sum C)} →
    B ≡ B′ → Fin.toℕ i′ ≡ Fin.toℕ i → SplitShape B C i → SplitShape B′ C i′
  transportSplitShapeˡ refl same sh =
    subst (λ ix → SplitShape _ _ ix) (Fin.toℕ-injective (sym same)) sh

  transportSplitShapeʳ :
    {B B′ C : BindGroup} {i : 𝔽 (sum C + sum B)} {i′ : 𝔽 (sum C + sum B′)} →
    B ≡ B′ → Fin.toℕ i′ ≡ Fin.toℕ i → SplitShape C B i → SplitShape C B′ i′
  transportSplitShapeʳ refl same sh =
    subst (λ ix → SplitShape _ _ ix) (Fin.toℕ-injective (sym same)) sh

  leftPrefixIx :
    (G₀ B C : BindGroup) → 𝔽 (sum B) → 𝔽 (sum (G₀ L.++ B) + sum C)
  leftPrefixIx G₀ B C i =
    Fin.cast (cong (_+ sum C) (sym (sum-++ G₀ B))) ((sum G₀ ↑ʳ i) ↑ˡ sum C)

  leftPrefixIx-toℕ :
    (G₀ B C : BindGroup) (i : 𝔽 (sum B)) →
    Fin.toℕ (leftPrefixIx G₀ B C i) ≡ sum G₀ + Fin.toℕ i
  leftPrefixIx-toℕ G₀ B C i =
    Fin.toℕ-cast (cong (_+ sum C) (sym (sum-++ G₀ B))) ((sum G₀ ↑ʳ i) ↑ˡ sum C)
    ■ Fin.toℕ-↑ˡ (sum G₀ ↑ʳ i) (sum C)
    ■ Fin.toℕ-↑ʳ (sum G₀) i

  rightPrefixIx :
    (G₀ B C : BindGroup) → 𝔽 (sum B) → 𝔽 (sum C + sum (G₀ L.++ B))
  rightPrefixIx G₀ B C i =
    Fin.cast (cong (sum C +_) (sym (sum-++ G₀ B))) (sum C ↑ʳ (sum G₀ ↑ʳ i))

  rightPrefixIx-toℕ :
    (G₀ B C : BindGroup) (i : 𝔽 (sum B)) →
    Fin.toℕ (rightPrefixIx G₀ B C i) ≡ sum C + (sum G₀ + Fin.toℕ i)
  rightPrefixIx-toℕ G₀ B C i =
    Fin.toℕ-cast (cong (sum C +_) (sym (sum-++ G₀ B))) (sum C ↑ʳ (sum G₀ ↑ʳ i))
    ■ Fin.toℕ-↑ʳ (sum C) (sum G₀ ↑ʳ i)
    ■ cong (sum C +_) (Fin.toℕ-↑ʳ (sum G₀) i)

  head-split-left-prefix :
    (G₀ B C : BindGroup) {b : ℕ} (j : 𝔽 b) →
    SplitShape (G₀ L.++ (b L.∷ B)) C
      (leftPrefixIx G₀ (b L.∷ B) C (j ↑ˡ sum B))
  head-split-left-prefix G₀ B C {b = b} j
    with fin-split b j
  ... | rest , bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape (G₀ L.++ (z L.∷ B)) C
          (leftPrefixIx G₀ (z L.∷ B) C (j′ ↑ˡ sum B)))
      (sym bEq) build j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) → Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape (G₀ L.++ ((Fin.toℕ j + suc rest) L.∷ B)) C
        (leftPrefixIx G₀ ((Fin.toℕ j + suc rest) L.∷ B) C (j′ ↑ˡ sum B))
    build j′ j′Eq =
      subst
        (λ ix → SplitShape (G₀ L.++ ((Fin.toℕ j + suc rest) L.∷ B)) C ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ˡ (splitIx G₀ B (Fin.toℕ j) rest) (sum C)
          ■ splitIx-toℕ G₀ B (Fin.toℕ j) rest
          ■ cong (sum G₀ +_) (sym j′Eq)
          ■ sym
              (leftPrefixIx-toℕ G₀ ((Fin.toℕ j + suc rest) L.∷ B) C (j′ ↑ˡ sum B)
               ■ cong (sum G₀ +_) (Fin.toℕ-↑ˡ j′ (sum B)))))
        (split-l G₀ B (Fin.toℕ j) rest C)

  head-split-right-prefix :
    (G₀ B C : BindGroup) {b : ℕ} (j : 𝔽 b) →
    SplitShape C (G₀ L.++ (b L.∷ B))
      (rightPrefixIx G₀ (b L.∷ B) C (j ↑ˡ sum B))
  head-split-right-prefix G₀ B C {b = b} j
    with fin-split b j
  ... | rest , bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape C (G₀ L.++ (z L.∷ B))
          (rightPrefixIx G₀ (z L.∷ B) C (j′ ↑ˡ sum B)))
      (sym bEq) build j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) → Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape C (G₀ L.++ ((Fin.toℕ j + suc rest) L.∷ B))
        (rightPrefixIx G₀ ((Fin.toℕ j + suc rest) L.∷ B) C (j′ ↑ˡ sum B))
    build j′ j′Eq =
      subst
        (λ ix → SplitShape C (G₀ L.++ ((Fin.toℕ j + suc rest) L.∷ B)) ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ʳ (sum C) (splitIx G₀ B (Fin.toℕ j) rest)
          ■ cong (sum C +_) (splitIx-toℕ G₀ B (Fin.toℕ j) rest)
          ■ cong (sum C +_) (cong (sum G₀ +_) (sym j′Eq))
          ■ sym
              (rightPrefixIx-toℕ G₀ ((Fin.toℕ j + suc rest) L.∷ B) C (j′ ↑ˡ sum B)
               ■ cong (sum C +_) (cong (sum G₀ +_) (Fin.toℕ-↑ˡ j′ (sum B))))))
        (split-r C G₀ B (Fin.toℕ j) rest)

  group-split-left-prefix :
    (G₀ B C : BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i → SplitShape (G₀ L.++ B) C (leftPrefixIx G₀ B C i)
  group-split-left-prefix G₀ (b L.∷ B) C (head-group .B j) =
    head-split-left-prefix G₀ B C j
  group-split-left-prefix G₀ (b L.∷ B) C (next-group .b {i = i} g) =
    transportSplitShapeˡ groupEq same
      (group-split-left-prefix (G₀ L.++ (b L.∷ L.[])) B C g)
    where
    groupEq : (G₀ L.++ (b L.∷ L.[])) L.++ B ≡ G₀ L.++ (b L.∷ B)
    groupEq = L.++-assoc G₀ (b L.∷ L.[]) B

    sumPrefixEq : sum (G₀ L.++ (b L.∷ L.[])) ≡ sum G₀ + b
    sumPrefixEq =
      sum-++ G₀ (b L.∷ L.[]) ■ cong (sum G₀ +_) (NatP.+-identityʳ b)

    same :
      Fin.toℕ (leftPrefixIx G₀ (b L.∷ B) C (b ↑ʳ i)) ≡
      Fin.toℕ (leftPrefixIx (G₀ L.++ (b L.∷ L.[])) B C i)
    same =
      leftPrefixIx-toℕ G₀ (b L.∷ B) C (b ↑ʳ i)
      ■ cong (sum G₀ +_) (Fin.toℕ-↑ʳ b i)
      ■ sym (NatP.+-assoc (sum G₀) b (Fin.toℕ i))
      ■ cong (_+ Fin.toℕ i) (sym sumPrefixEq)
      ■ sym (leftPrefixIx-toℕ (G₀ L.++ (b L.∷ L.[])) B C i)

  group-split-right-prefix :
    (G₀ B C : BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i → SplitShape C (G₀ L.++ B) (rightPrefixIx G₀ B C i)
  group-split-right-prefix G₀ (b L.∷ B) C (head-group .B j) =
    head-split-right-prefix G₀ B C j
  group-split-right-prefix G₀ (b L.∷ B) C (next-group .b {i = i} g) =
    transportSplitShapeʳ groupEq same
      (group-split-right-prefix (G₀ L.++ (b L.∷ L.[])) B C g)
    where
    groupEq : (G₀ L.++ (b L.∷ L.[])) L.++ B ≡ G₀ L.++ (b L.∷ B)
    groupEq = L.++-assoc G₀ (b L.∷ L.[]) B

    sumPrefixEq : sum (G₀ L.++ (b L.∷ L.[])) ≡ sum G₀ + b
    sumPrefixEq =
      sum-++ G₀ (b L.∷ L.[]) ■ cong (sum G₀ +_) (NatP.+-identityʳ b)

    same :
      Fin.toℕ (rightPrefixIx G₀ (b L.∷ B) C (b ↑ʳ i)) ≡
      Fin.toℕ (rightPrefixIx (G₀ L.++ (b L.∷ L.[])) B C i)
    same =
      rightPrefixIx-toℕ G₀ (b L.∷ B) C (b ↑ʳ i)
      ■ cong (sum C +_)
          (cong (sum G₀ +_) (Fin.toℕ-↑ʳ b i)
           ■ sym (NatP.+-assoc (sum G₀) b (Fin.toℕ i))
           ■ cong (_+ Fin.toℕ i) (sym sumPrefixEq))
      ■ sym (rightPrefixIx-toℕ (G₀ L.++ (b L.∷ L.[])) B C i)

  group-split-left :
    (B C : BindGroup) {i : 𝔽 (sum B)} → GroupOf B i → SplitShape B C (i ↑ˡ sum C)
  group-split-left B C {i = i} g =
    transportSplitShapeˡ refl
      (Fin.toℕ-↑ˡ i (sum C) ■ sym (leftPrefixIx-toℕ L.[] B C i))
      (group-split-left-prefix L.[] B C g)

  group-split-right :
    (C B : BindGroup) {i : 𝔽 (sum B)} → GroupOf B i → SplitShape C B (sum C ↑ʳ i)
  group-split-right C B {i = i} g =
    transportSplitShapeʳ refl
      (Fin.toℕ-↑ʳ (sum C) i ■ sym (rightPrefixIx-toℕ L.[] B C i))
      (group-split-right-prefix L.[] B C g)

------------------------------------------------------------------------
-- Every binder position is a split position.

split-shape :
  {k n : ℕ} {ctx : ProcessContext k n} {x : 𝔽 k} (bnd : Binder ctx x) →
  SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
split-shape bnd
  with sideOf (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
... | inl i =
  group-split-left (Binder.B₁ bnd) (Binder.B₂ bnd) (groupOf (Binder.B₁ bnd) i)
... | inr i =
  group-split-right (Binder.B₁ bnd) (Binder.B₂ bnd) (groupOf (Binder.B₂ bnd) i)
