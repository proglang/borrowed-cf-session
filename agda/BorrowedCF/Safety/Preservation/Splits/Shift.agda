------------------------------------------------------------------------
-- The context lemma for the two split renamings.
--
-- `SplitRenamings.lwk` / `rwk` are NOT typed renamings of the ν-body
-- context: at the consumed handle the slot changes type.  Away from that
-- one variable they are, and that is exactly what `lsplit-lookup` /
-- `rsplit-lookup` state.  The Fin arithmetic comes from
-- `Simulation.Support.Theorems.SplitsLQ` / `SplitsRQ` (`dlwkq`, `drwkq`,
-- `P1q`..`P3q`, `P1rq`..`P3rq`); the data-level agreement of the two
-- binder contexts is the `Agree` produced by `lsplit-bindCtx` /
-- `rsplit-bindCtx`.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Shift where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed using (BindGroup)
open import BorrowedCF.Terms using (module SplitRenamings)
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Splits.Chain using (Agree; lookup-toℕ)

open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ
  using (dlwkq; dlwkq-lo; dlwkq-hi; P1q; P2q; P3q)
open import BorrowedCF.Simulation.Support.Theorems.SplitsRQ
  using (drwkq; drwkq-lo; drwkq-hi; P1rq; P2rq; P3rq)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Structural three-way split of a variable of the ν-body scope.

split3 : ∀ a b c (z : 𝔽 (a + b + c)) →
    (Σ[ d ∈ 𝔽 a ] z ≡ (d ↑ˡ b) ↑ˡ c)
  ⊎ (Σ[ w ∈ 𝔽 b ] z ≡ (a ↑ʳ w) ↑ˡ c)
  ⊎ (Σ[ u ∈ 𝔽 c ] z ≡ (a + b) ↑ʳ u)
split3 a b c z with splitAt (a + b) z in eq₁
... | inj₂ u = inj₂ (inj₂ (u , (sym (join-splitAt (a + b) c z) ■ cong (Fin.join (a + b) c) eq₁)))
... | inj₁ y with splitAt a y in eq₂
...   | inj₁ d = inj₁ (d , zeq)
        where zeq : z ≡ (d ↑ˡ b) ↑ˡ c
              zeq = sym (join-splitAt (a + b) c z)
                  ■ cong (Fin.join (a + b) c) eq₁
                  ■ cong (_↑ˡ c) (sym (join-splitAt a b y) ■ cong (Fin.join a b) eq₂)
...   | inj₂ w = inj₂ (inj₁ (w , zeq))
        where zeq : z ≡ (a ↑ʳ w) ↑ˡ c
              zeq = sym (join-splitAt (a + b) c z)
                  ■ cong (Fin.join (a + b) c) eq₁
                  ■ cong (_↑ˡ c) (sym (join-splitAt a b y) ■ cong (Fin.join a b) eq₂)

------------------------------------------------------------------------
-- The consumed handle sits at flat position `sum B₁ + q` of the first
-- binder context.

dh : ∀ (B₁ B₂ : BindGroup) (q b₁ : ℕ) → 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))
dh B₁ B₂ q b₁ = Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                         (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))

toℕ-dh : ∀ (B₁ B₂ : BindGroup) (q b₁ : ℕ) → Fin.toℕ (dh B₁ B₂ q b₁) ≡ sum B₁ + q
toℕ-dh B₁ B₂ q b₁ =
    Fin.toℕ-cast _ (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
  ■ Fin.toℕ-↑ʳ (sum B₁) ((q ↑ʳ 0F) ↑ˡ sum B₂)
  ■ cong (sum B₁ +_) (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (sum B₂)
                     ■ Fin.toℕ-↑ʳ q 0F
                     ■ Nat.+-identityʳ q)

-- `atk` at the split position is that flat position, embedded.
atk≡ : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ} →
  SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    ≡ ((dh B₁ B₂ q b₁ ↑ˡ sum B) ↑ˡ m)
atk≡ B₁ B₂ B = refl

private
  +1≡suc : ∀ n → n + 1 ≡ suc n
  +1≡suc n = Nat.+-comm n 1

------------------------------------------------------------------------
-- R-LSplit

lsplit-lookup : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ}
  (Γ₁  : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)))
  (Γ₂ : Ctx (sum B)) (Γ : Ctx m) →
  Agree (sum B₁ + q) Γ₁ Γ₁′ →
  ∀ (z : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
  z ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
  ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {m} z
    ≡ ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z
lsplit-lookup B₁ B₂ B {q} {b₁} {m} Γ₁ Γ₁′ Γ₂ Γ Ag z z≢
  with split3 (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) m z
... | inj₁ (d , refl) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P1q B₁ B₂ B d)
    ■ V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B)
    ■ V.lookup-++ˡ Γ₁′ Γ₂ (dlwkq B₁ q b₁ B₂ d)
    ■ Ag d (dlwkq B₁ q b₁ B₂ d) ne lo hi
    ■ sym (V.lookup-++ˡ Γ₁ Γ₂ d)
    ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (d ↑ˡ sum B))
  where
    ne : Fin.toℕ d ≢ sum B₁ + q
    ne eq = z≢ (cong (λ y → (y ↑ˡ sum B) ↑ˡ m)
                     (Fin.toℕ-injective (eq ■ sym (toℕ-dh B₁ B₂ q b₁))))
    lo : Fin.toℕ d Nat.< sum B₁ + q → Fin.toℕ (dlwkq B₁ q b₁ B₂ d) ≡ Fin.toℕ d
    lo lt = dlwkq-lo B₁ q b₁ B₂ d
              (subst (Fin.toℕ d Nat.<_) (sym (+1≡suc (sum B₁ + q))) (Nat.<-trans lt (Nat.n<1+n _)))
    hi : sum B₁ + q Nat.< Fin.toℕ d → Fin.toℕ (dlwkq B₁ q b₁ B₂ d) ≡ suc (Fin.toℕ d)
    hi gt = dlwkq-hi B₁ q b₁ B₂ d
              (subst (Nat._≤ Fin.toℕ d) (sym (+1≡suc (sum B₁ + q))) gt)
... | inj₂ (inj₁ (w , refl)) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P2q B₁ B₂ B w)
    ■ V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w)
    ■ V.lookup-++ʳ Γ₁′ Γ₂ w
    ■ sym (V.lookup-++ʳ Γ₁ Γ₂ w)
    ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w))
... | inj₂ (inj₂ (u , refl)) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P3q B₁ B₂ B u)
    ■ V.lookup-++ʳ (Γ₁′ ⸴* Γ₂) Γ u
    ■ sym (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ u)

------------------------------------------------------------------------
-- R-RSplit

rsplit-lookup : ∀ (B₁ B₂ B : BindGroup) {q b₁ m : ℕ}
  (Γ₁  : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂)))
  (Γ₁′ : Ctx (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)))
  (Γ₂ : Ctx (sum B)) (Γ : Ctx m) →
  Agree (sum B₁ + q) Γ₁ Γ₁′ →
  ∀ (z : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
  z ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
  ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫ SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} z
    ≡ ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z
rsplit-lookup B₁ B₂ B {q} {b₁} {m} Γ₁ Γ₁′ Γ₂ Γ Ag z z≢
  with split3 (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) m z
... | inj₁ (d , refl) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P1rq B₁ B₂ B d)
    ■ V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ (drwkq B₁ q b₁ B₂ d ↑ˡ sum B)
    ■ V.lookup-++ˡ Γ₁′ Γ₂ (drwkq B₁ q b₁ B₂ d)
    ■ Ag d (drwkq B₁ q b₁ B₂ d) ne (drwkq-lo B₁ q b₁ B₂ d)
           (λ gt → drwkq-hi B₁ q b₁ B₂ d (Nat.<⇒≤ gt))
    ■ sym (V.lookup-++ˡ Γ₁ Γ₂ d)
    ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (d ↑ˡ sum B))
  where
    ne : Fin.toℕ d ≢ sum B₁ + q
    ne eq = z≢ (cong (λ y → (y ↑ˡ sum B) ↑ˡ m)
                     (Fin.toℕ-injective (eq ■ sym (toℕ-dh B₁ B₂ q b₁))))
... | inj₂ (inj₁ (w , refl)) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P2rq B₁ B₂ B w)
    ■ V.lookup-++ˡ (Γ₁′ ⸴* Γ₂) Γ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w)
    ■ V.lookup-++ʳ Γ₁′ Γ₂ w
    ■ sym (V.lookup-++ʳ Γ₁ Γ₂ w)
    ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum (B₁ ++ (q + suc b₁) ∷ B₂) ↑ʳ w))
... | inj₂ (inj₂ (u , refl)) =
      cong (((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫_) (P3rq B₁ B₂ B u)
    ■ V.lookup-++ʳ (Γ₁′ ⸴* Γ₂) Γ u
    ■ sym (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ u)
