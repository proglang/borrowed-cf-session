-- | Phase 3 shared material for the two split leaves (`R-LSplit` and
--   `R-RSplit`; `ForwardSoup/PLAN.md`, §4, Phase 3, item 4).
--
--   Three groups of lemmas:
--
--     * a *positional* description of the binder environments.  `Ub-entry`
--       says which of the three slots of `Ub[ w ] (e₁ , c , e₂) p` is filled,
--       as a function of `toℕ p` alone; `UBFrom-lwk` lifts it to a whole
--       binder group whose middle block grew by one, and `source-target-lwk`
--       lifts *that* to `bindEnv`, along the renaming `SplitRenamings.lwk`.
--       Everything is stated numerically (`toℕ`), so it applies to `lwk` and
--       to `rwk` alike without a bespoke index calculus.
--
--     * the `blockAt`/`atk` position kit and the flag-list shape lemmas,
--       ported from the arity-0 proof `ForwardSoup/LSplit.agda`.
--
--     * the two-renaming frame coherences `T-ren-ren-coh`, `lift-ren-ren-coh`,
--       `Tᶠ-plug-ren-ren-coh`, `Tᶠ*-plug-ren-ren-coh` — the two-step version
--       of `Local/Frames.agda`'s `*-ren-coh` family, needed because the split
--       rules factor their frame through `E₀ ⋯ᶠ* ρ⁻ ⋯ᶠ* lwk`.
module BorrowedCF.Simulation.ForwardSoup.Local.SplitCommon where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.Solver using (module +-*-Solver)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ[_]; Tᶠ*[_]; T[_]-⋯ᵣ; T[_]-Env-cong)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalEndpoint)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ)
open import BorrowedCF.Simulation.Support.BlockPerm
  using (toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt)

open +-*-Solver using (solve; _:=_; _:+_; con)

open Nat.Variables
open Fin.Patterns

private
  variable d : ℕ

------------------------------------------------------------------------
-- Small arithmetic facts.

private
  ∸-pos : ∀ {a b : ℕ} → a Nat.< b → 0 Nat.< b Nat.∸ a
  ∸-pos {zero} {suc b} lt = Nat.s≤s Nat.z≤n
  ∸-pos {suc a} {suc b} lt = ∸-pos (Nat.s≤s⁻¹ lt)

  q<q+suc : ∀ (q b : ℕ) → q Nat.< q + suc b
  q<q+suc q b =
    subst (suc q Nat.≤_) (sym (Nat.+-suc q b)) (Nat.s≤s (Nat.m≤m+n q b))

  ∸-suc : ∀ {a u : ℕ} → a Nat.≤ u → suc u Nat.∸ a ≡ suc (u Nat.∸ a)
  ∸-suc {zero} le = refl
  ∸-suc {suc a} {suc u} le = ∸-suc (Nat.s≤s⁻¹ le)

  ∸-bound : ∀ {a s u : ℕ} → a Nat.≤ u → u Nat.< a + s → u Nat.∸ a Nat.< s
  ∸-bound {a = a} {s = s} {u = u} ge lt =
    Nat.+-cancelˡ-< a (u Nat.∸ a) s
      (subst (Nat._< a + s) (sym (Nat.m+[n∸m]≡n ge)) lt)

  -- The two shapes of a one-position insertion at `t`.
  trisect :
    ∀ {t u u′ : ℕ} → u ≢ t →
    (u Nat.< t → u′ ≡ u) → (t Nat.< u → u′ ≡ suc u) →
    (u Nat.< t × u′ ≡ u) ⊎ (t Nat.< u × u′ ≡ suc u)
  trisect {t = t} {u = u} notEq lo hi with u Nat.<? t
  ... | yes lt = inj₁ (lt , lo lt)
  ... | no ¬lt =
    inj₂ (gt , hi gt)
    where
    gt : t Nat.< u
    gt = Nat.≤∧≢⇒< (Nat.≮⇒≥ ¬lt) (notEq ∘ sym)

  shift-≥ :
    ∀ {t u u′ : ℕ} → u ≢ t →
    (u Nat.< t → u′ ≡ u) → (t Nat.< u → u′ ≡ suc u) →
    u Nat.≤ u′
  shift-≥ notEq lo hi with trisect notEq lo hi
  ... | inj₁ (_ , equal) = Nat.≤-reflexive (sym equal)
  ... | inj₂ (_ , equal) = Nat.≤-trans (Nat.n≤1+n _) (Nat.≤-reflexive (sym equal))

  shift-≤ :
    ∀ {t u u′ : ℕ} → u ≢ t →
    (u Nat.< t → u′ ≡ u) → (t Nat.< u → u′ ≡ suc u) →
    u′ Nat.≤ suc u
  shift-≤ notEq lo hi with trisect notEq lo hi
  ... | inj₁ (_ , equal) =
    Nat.≤-trans (Nat.≤-reflexive equal) (Nat.n≤1+n _)
  ... | inj₂ (_ , equal) = Nat.≤-reflexive equal

------------------------------------------------------------------------
-- Positional lookup in a concatenated environment.

++ₛ-lo :
  ∀ {a b : ℕ} (sigma₁ : Translation.Env a d) (sigma₂ : Translation.Env b d)
    (i : 𝔽 (a + b)) (p : 𝔽 a) →
  Fin.toℕ i ≡ Fin.toℕ p →
  (sigma₁ Translation.++ₛ sigma₂) i ≡ sigma₁ p
++ₛ-lo {b = b} sigma₁ sigma₂ i p equal =
  cong (sigma₁ Translation.++ₛ sigma₂)
    (Fin.toℕ-injective (equal ■ sym (Fin.toℕ-↑ˡ p b)))
  ■ ++ₛ-lookupˡ sigma₁ sigma₂ p

++ₛ-hi :
  ∀ {a b : ℕ} (sigma₁ : Translation.Env a d) (sigma₂ : Translation.Env b d)
    (i : 𝔽 (a + b)) (p : 𝔽 b) →
  Fin.toℕ i ≡ a + Fin.toℕ p →
  (sigma₁ Translation.++ₛ sigma₂) i ≡ sigma₂ p
++ₛ-hi {a = a} sigma₁ sigma₂ i p equal =
  cong (sigma₁ Translation.++ₛ sigma₂)
    (Fin.toℕ-injective (equal ■ sym (Fin.toℕ-↑ʳ a p)))
  ■ ++ₛ-lookupʳ sigma₁ sigma₂ p

------------------------------------------------------------------------
-- The entries of one borrow block.
--
--   `Ub[ w ] (e₁ , c , e₂)` puts `e₁` in the left slot of its first entry,
--   `e₂` in the right slot of its last one, and `*` everywhere else.

pick : ℕ → SoupTerm.Tm d → SoupTerm.Tm d
pick zero e = e
pick (suc _) e = SoupTerm.*

pick-* : (j : ℕ) → pick {d} j SoupTerm.* ≡ SoupTerm.*
pick-* zero = refl
pick-* (suc j) = refl

pick-pos :
  (j : ℕ) (e : SoupTerm.Tm d) → 0 Nat.< j → pick j e ≡ SoupTerm.*
pick-pos (suc j) e _ = refl

Ub-entry :
  ∀ w (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) (p : 𝔽 w) →
  Translation.Ub[ w ] (e₁ , c , e₂) p ≡
  Translation.chanTriple
    (pick (Fin.toℕ p) e₁ , c , pick (w Nat.∸ suc (Fin.toℕ p)) e₂)
Ub-entry (suc zero) c e₁ e₂ 0F = refl
Ub-entry (suc (suc w)) c e₁ e₂ 0F = refl
Ub-entry (suc (suc w)) c e₁ e₂ (suc p) =
  Ub-entry (suc w) c SoupTerm.* e₂ p
  ■ cong
      (λ z →
        Translation.chanTriple
          (z , c , pick (suc w Nat.∸ suc (Fin.toℕ p)) e₂))
      (pick-* (Fin.toℕ p))

-- Inserting one entry at position `t` of a block leaves every other entry
-- alone.
Ub-ins :
  ∀ (w w′ t : ℕ) (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (p : 𝔽 w) (p′ : 𝔽 w′) →
  w′ ≡ suc w →
  t Nat.< w →
  Fin.toℕ p ≢ t →
  (Fin.toℕ p Nat.< t → Fin.toℕ p′ ≡ Fin.toℕ p) →
  (t Nat.< Fin.toℕ p → Fin.toℕ p′ ≡ suc (Fin.toℕ p)) →
  Translation.Ub[ w ] (e₁ , c , e₂) p ≡
  Translation.Ub[ w′ ] (e₁ , c , e₂) p′
Ub-ins w w′ t c e₁ e₂ p p′ widthEq tlt notEq lo hi
  with trisect notEq lo hi
... | inj₁ (lt , equal) =
  Ub-entry w c e₁ e₂ p
  ■ cong₂ (λ head tail → Translation.chanTriple (head , c , tail))
      (cong (λ z → pick z e₁) (sym equal))
      ( pick-pos (w Nat.∸ suc (Fin.toℕ p)) e₂
          (∸-pos (Nat.≤-<-trans lt tlt))
      ■ sym
          (pick-pos (w′ Nat.∸ suc (Fin.toℕ p′)) e₂
            (∸-pos
              (subst₂ Nat._<_ (cong suc (sym equal)) (sym widthEq)
                (Nat.s≤s (Nat.<⇒≤ (Nat.≤-<-trans lt tlt))))))
      )
  ■ sym (Ub-entry w′ c e₁ e₂ p′)
... | inj₂ (gt , equal) =
  Ub-entry w c e₁ e₂ p
  ■ cong₂ (λ head tail → Translation.chanTriple (head , c , tail))
      ( pick-pos (Fin.toℕ p) e₁ (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
      ■ sym (pick-pos (Fin.toℕ p′) e₁
              (subst (0 Nat.<_) (sym equal) (Nat.s≤s Nat.z≤n)))
      )
      (cong (λ z → pick z e₂)
        (sym (cong₂ Nat._∸_ widthEq (cong suc equal))))
  ■ sym (Ub-entry w′ c e₁ e₂ p′)

------------------------------------------------------------------------
-- Splitting off the head block of a binder group with at least two blocks.

UBFrom-cons-lo :
  ∀ l b b′ (B : Typed.BindGroup) (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (y : 𝔽 (sum (b ∷ b′ ∷ B))) (p : 𝔽 b) →
  Fin.toℕ y ≡ Fin.toℕ p →
  proj₁ (Translation.UBFrom l (b ∷ b′ ∷ B) r (e₁ , c , e₂)) y ≡
  Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (r , l)) p
UBFrom-cons-lo l b b′ B r c e₁ e₂ y p equal
  with Translation.UBFrom (suc l) (b′ ∷ B) r
         (SoupTerm.`phi (r , l) , c , e₂)
... | sigma , flags =
  ++ₛ-lo (Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (r , l)))
    sigma y p equal

UBFrom-cons-hi :
  ∀ l b b′ (B : Typed.BindGroup) (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (y : 𝔽 (sum (b ∷ b′ ∷ B))) (p : 𝔽 (sum (b′ ∷ B))) →
  Fin.toℕ y ≡ b + Fin.toℕ p →
  proj₁ (Translation.UBFrom l (b ∷ b′ ∷ B) r (e₁ , c , e₂)) y ≡
  proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) r
          (SoupTerm.`phi (r , l) , c , e₂)) p
UBFrom-cons-hi l b b′ B r c e₁ e₂ y p equal
  with Translation.UBFrom (suc l) (b′ ∷ B) r
         (SoupTerm.`phi (r , l) , c , e₂)
... | sigma , flags =
  ++ₛ-hi (Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (r , l)))
    sigma y p equal

------------------------------------------------------------------------
-- Peeling one leading block off both sides of a group-insertion statement.
--
--   Stated for two *unrelated* tails, so that both the recursive case (the
--   split block sits further right) and the base case can use it.

private
  cons-step :
    ∀ l b₀ b′ (B : Typed.BindGroup) b″ (B′ : Typed.BindGroup) (t : ℕ)
      (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
      (w : 𝔽 (sum (b₀ ∷ b′ ∷ B))) (w′ : 𝔽 (sum (b₀ ∷ b″ ∷ B′))) →
    ( (p : 𝔽 (sum (b′ ∷ B))) (p′ : 𝔽 (sum (b″ ∷ B′))) →
      Fin.toℕ p ≢ t →
      (Fin.toℕ p Nat.< t → Fin.toℕ p′ ≡ Fin.toℕ p) →
      (t Nat.< Fin.toℕ p → Fin.toℕ p′ ≡ suc (Fin.toℕ p)) →
      proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) r
              (SoupTerm.`phi (r , l) , c , e₂)) p ≡
      proj₁ (Translation.UBFrom (suc l) (b″ ∷ B′) r
              (SoupTerm.`phi (r , l) , c , e₂)) p′ ) →
    Fin.toℕ w ≢ b₀ + t →
    (Fin.toℕ w Nat.< b₀ + t → Fin.toℕ w′ ≡ Fin.toℕ w) →
    (b₀ + t Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
    proj₁ (Translation.UBFrom l (b₀ ∷ b′ ∷ B) r (e₁ , c , e₂)) w ≡
    proj₁ (Translation.UBFrom l (b₀ ∷ b″ ∷ B′) r (e₁ , c , e₂)) w′
  cons-step l b₀ b′ B b″ B′ t r c e₁ e₂ w w′ rec notEq lo hi
    with Fin.toℕ w Nat.<? b₀
  ... | yes lt =
    UBFrom-cons-lo l b₀ b′ B r c e₁ e₂ w p (sym (Fin.toℕ-fromℕ< lt))
    ■ sym
        (UBFrom-cons-lo l b₀ b″ B′ r c e₁ e₂ w′ p
          (lo (Nat.<-≤-trans lt (Nat.m≤m+n b₀ t))
           ■ sym (Fin.toℕ-fromℕ< lt)))
    where
    p : 𝔽 b₀
    p = Fin.fromℕ< lt
  ... | no ¬lt =
    UBFrom-cons-hi l b₀ b′ B r c e₁ e₂ w p wSplit
    ■ rec p p′ notEq′ lo′ hi′
    ■ sym (UBFrom-cons-hi l b₀ b″ B′ r c e₁ e₂ w′ p′ w′Split)
    where
    ge : b₀ Nat.≤ Fin.toℕ w
    ge = Nat.≮⇒≥ ¬lt

    ge′ : b₀ Nat.≤ Fin.toℕ w′
    ge′ = Nat.≤-trans ge (shift-≥ notEq lo hi)

    p : 𝔽 (sum (b′ ∷ B))
    p = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n w))

    p′ : 𝔽 (sum (b″ ∷ B′))
    p′ = Fin.fromℕ< (∸-bound ge′ (Fin.toℕ<n w′))

    pℕ : Fin.toℕ p ≡ Fin.toℕ w Nat.∸ b₀
    pℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n w))

    p′ℕ : Fin.toℕ p′ ≡ Fin.toℕ w′ Nat.∸ b₀
    p′ℕ = Fin.toℕ-fromℕ< (∸-bound ge′ (Fin.toℕ<n w′))

    wSplit : Fin.toℕ w ≡ b₀ + Fin.toℕ p
    wSplit = sym (cong (b₀ +_) pℕ ■ Nat.m+[n∸m]≡n ge)

    w′Split : Fin.toℕ w′ ≡ b₀ + Fin.toℕ p′
    w′Split = sym (cong (b₀ +_) p′ℕ ■ Nat.m+[n∸m]≡n ge′)

    notEq′ : Fin.toℕ p ≢ t
    notEq′ same = notEq (wSplit ■ cong (b₀ +_) same)

    lo′ : Fin.toℕ p Nat.< t → Fin.toℕ p′ ≡ Fin.toℕ p
    lo′ lt =
      p′ℕ
      ■ cong (Nat._∸ b₀)
          (lo (subst (Nat._< b₀ + t) (sym wSplit) (Nat.+-monoʳ-< b₀ lt)))
      ■ sym pℕ

    hi′ : t Nat.< Fin.toℕ p → Fin.toℕ p′ ≡ suc (Fin.toℕ p)
    hi′ gt =
      p′ℕ
      ■ cong (Nat._∸ b₀)
          (hi (subst (b₀ + t Nat.<_) (sym wSplit) (Nat.+-monoʳ-< b₀ gt)))
      ■ ∸-suc ge
      ■ cong suc (sym pℕ)

------------------------------------------------------------------------
-- The binder group of the reduct differs from the one of the redex by one
-- inserted borrow inside the block `q + suc b`.  Away from the split
-- position `sum B₁ + q`, the two environments agree.

UBFrom-lwk :
  ∀ l (B₁ B₂ : Typed.BindGroup) q b (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (w : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)))
    (w′ : 𝔽 (sum (B₁ ++ (q + suc (suc b)) ∷ B₂))) →
  Fin.toℕ w ≢ sum B₁ + q →
  (Fin.toℕ w Nat.< sum B₁ + q → Fin.toℕ w′ ≡ Fin.toℕ w) →
  (sum B₁ + q Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
  proj₁ (Translation.UBFrom l (B₁ ++ (q + suc b) ∷ B₂) r (e₁ , c , e₂)) w ≡
  proj₁ (Translation.UBFrom l (B₁ ++ (q + suc (suc b)) ∷ B₂) r
          (e₁ , c , e₂)) w′

UBFrom-lwk l [] [] q b r c e₁ e₂ w w′ notEq lo hi =
  Ub-ins ((q + suc b) + 0) ((q + suc (suc b)) + 0) q c e₁ e₂ w w′
    (cong (Nat._+ 0) (Nat.+-suc q (suc b)))
    (subst (q Nat.<_) (sym (Nat.+-identityʳ (q + suc b)))
      (q<q+suc q b))
    notEq lo hi

UBFrom-lwk l [] (b₂ ∷ B₂) q b r c e₁ e₂ w w′ notEq lo hi
  with Fin.toℕ w Nat.<? q + suc b
... | yes lt =
  UBFrom-cons-lo l (q + suc b) b₂ B₂ r c e₁ e₂ w p (sym pℕ)
  ■ Ub-ins (q + suc b) (q + suc (suc b)) q c e₁ (SoupTerm.`phi (r , l))
      p p′ (Nat.+-suc q (suc b)) (q<q+suc q b)
      (λ same → notEq (sym pℕ ■ same))
      (λ pLt → p′ℕ ■ lo (subst (Nat._< q) pℕ pLt) ■ sym pℕ)
      (λ pGt → p′ℕ ■ hi (subst (q Nat.<_) pℕ pGt) ■ cong suc (sym pℕ))
  ■ sym (UBFrom-cons-lo l (q + suc (suc b)) b₂ B₂ r c e₁ e₂ w′ p′ (sym p′ℕ))
  where
  p : 𝔽 (q + suc b)
  p = Fin.fromℕ< lt

  pℕ : Fin.toℕ p ≡ Fin.toℕ w
  pℕ = Fin.toℕ-fromℕ< lt

  bound : Fin.toℕ w′ Nat.< q + suc (suc b)
  bound =
    subst (suc (Fin.toℕ w′) Nat.≤_) (sym (Nat.+-suc q (suc b)))
      (Nat.s≤s (Nat.≤-trans (shift-≤ notEq lo hi) lt))

  p′ : 𝔽 (q + suc (suc b))
  p′ = Fin.fromℕ< bound

  p′ℕ : Fin.toℕ p′ ≡ Fin.toℕ w′
  p′ℕ = Fin.toℕ-fromℕ< bound

... | no ¬lt =
  UBFrom-cons-hi l (q + suc b) b₂ B₂ r c e₁ e₂ w p wSplit
  ■ sym (UBFrom-cons-hi l (q + suc (suc b)) b₂ B₂ r c e₁ e₂ w′ p w′Split)
  where
  ge : q + suc b Nat.≤ Fin.toℕ w
  ge = Nat.≮⇒≥ ¬lt

  gt : q Nat.< Fin.toℕ w
  gt = Nat.<-≤-trans (q<q+suc q b) ge

  p : 𝔽 (sum (b₂ ∷ B₂))
  p = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n w))

  pℕ : Fin.toℕ p ≡ Fin.toℕ w Nat.∸ (q + suc b)
  pℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n w))

  wSplit : Fin.toℕ w ≡ (q + suc b) + Fin.toℕ p
  wSplit = sym (cong ((q + suc b) +_) pℕ ■ Nat.m+[n∸m]≡n ge)

  w′Split : Fin.toℕ w′ ≡ (q + suc (suc b)) + Fin.toℕ p
  w′Split =
    hi gt
    ■ cong suc wSplit
    ■ sym (cong (Nat._+ Fin.toℕ p) (Nat.+-suc q (suc b)))

UBFrom-lwk l (b₀ ∷ []) B₂ q b r c e₁ e₂ w w′ notEq lo hi =
  cons-step l b₀ (q + suc b) B₂ (q + suc (suc b)) B₂ (0 + q) r c e₁ e₂ w w′
    (UBFrom-lwk (suc l) [] B₂ q b r c (SoupTerm.`phi (r , l)) e₂)
    (λ same → notEq (same ■ sym shape))
    (λ lt → lo (subst (Fin.toℕ w Nat.<_) (sym shape) lt))
    (λ gt → hi (subst (Nat._< Fin.toℕ w) (sym shape) gt))
  where
  shape : sum (b₀ ∷ []) + q ≡ b₀ + (0 + q)
  shape = Nat.+-assoc b₀ 0 q

UBFrom-lwk l (b₀ ∷ b₁ ∷ B₁) B₂ q b r c e₁ e₂ w w′ notEq lo hi =
  cons-step l b₀ b₁ (B₁ ++ (q + suc b) ∷ B₂) b₁ (B₁ ++ (q + suc (suc b)) ∷ B₂)
    (sum (b₁ ∷ B₁) + q) r c e₁ e₂ w w′
    (UBFrom-lwk (suc l) (b₁ ∷ B₁) B₂ q b r c (SoupTerm.`phi (r , l)) e₂)
    (λ same → notEq (same ■ sym shape))
    (λ lt → lo (subst (Fin.toℕ w Nat.<_) (sym shape) lt))
    (λ gt → hi (subst (Nat._< Fin.toℕ w) (sym shape) gt))
  where
  shape : sum (b₀ ∷ b₁ ∷ B₁) + q ≡ b₀ + (sum (b₁ ∷ B₁) + q)
  shape = Nat.+-assoc b₀ (sum (b₁ ∷ B₁)) q

UB-lwk :
  ∀ (B₁ B₂ : Typed.BindGroup) q b (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (w : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)))
    (w′ : 𝔽 (sum (B₁ ++ (q + suc (suc b)) ∷ B₂))) →
  Fin.toℕ w ≢ sum B₁ + q →
  (Fin.toℕ w Nat.< sum B₁ + q → Fin.toℕ w′ ≡ Fin.toℕ w) →
  (sum B₁ + q Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
  proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] r (e₁ , c , e₂)) w ≡
  proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b)) ∷ B₂ ] r (e₁ , c , e₂)) w′
UB-lwk = UBFrom-lwk zero

------------------------------------------------------------------------
-- The two numeric faces of `SplitRenamings.lwk`.
--
--   `lwk` is `ins (sum B₁ + q + 1)` between two casts, so it keeps every
--   position below the split point and shifts every position above it.  The
--   casts carry irrelevant equality proofs, so the two proofs below are
--   interchangeable with the ones inside `FinKits`.

private
  lwkEq₁ :
    ∀ s k b B C n → s + (k + suc b + B) + C + n ≡ s + k + 1 + (b + B + C + n)
  lwkEq₁ = solve 6 (λ s k b B C n →
    s :+ (k :+ (con 1 :+ b) :+ B) :+ C :+ n := s :+ k :+ con 1 :+ (b :+ B :+ C :+ n)) refl

  lwkEq₂ :
    ∀ s k b B C n →
    s + k + 1 + suc (b + B + C + n) ≡ s + (k + suc (suc b) + B) + C + n
  lwkEq₂ = solve 6 (λ s k b B C n →
    s :+ k :+ con 1 :+ (con 1 :+ (b :+ B :+ C :+ n)) := s :+ (k :+ (con 1 :+ (con 1 :+ b)) :+ B) :+ C :+ n) refl

  lwkCast₁ :
    ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ) →
    sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k ≡
    sum B₁ + q + 1 + (b₁ + sum B₂ + sum B + k)
  lwkCast₁ B₁ B₂ B q b₁ k =
    cong (λ z → z + sum B + k) (sum-++ B₁ ((q + suc b₁) ∷ B₂))
    ■ lwkEq₁ (sum B₁) q b₁ (sum B₂) (sum B) k

  lwkCast₂ :
    ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ) →
    sum B₁ + q + 1 + suc (b₁ + sum B₂ + sum B + k) ≡
    sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B + k
  lwkCast₂ B₁ B₂ B q b₁ k =
    lwkEq₂ (sum B₁) q b₁ (sum B₂) (sum B) k
    ■ cong (λ z → z + sum B + k) (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))

lwk-toℕ-lo :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  Fin.toℕ y Nat.< sum B₁ + q + 1 →
  Fin.toℕ (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k} y) ≡
  Fin.toℕ y
lwk-toℕ-lo B₁ B₂ B q b₁ k y lt =
  Fin.toℕ-cast (lwkCast₂ B₁ B₂ B q b₁ k)
    (Source._↑*_ Source.weakenᵣ (sum B₁ + q + 1) (Fin.cast (lwkCast₁ B₁ B₂ B q b₁ k) y))
  ■ toℕ-↑*-lt Source.weakenᵣ (sum B₁ + q + 1)
      (Fin.cast (lwkCast₁ B₁ B₂ B q b₁ k) y)
      (subst (Nat._< sum B₁ + q + 1)
        (sym (Fin.toℕ-cast (lwkCast₁ B₁ B₂ B q b₁ k) y)) lt)
  ■ Fin.toℕ-cast (lwkCast₁ B₁ B₂ B q b₁ k) y

lwk-toℕ-hi :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  sum B₁ + q + 1 Nat.≤ Fin.toℕ y →
  Fin.toℕ (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k} y) ≡
  suc (Fin.toℕ y)
lwk-toℕ-hi B₁ B₂ B q b₁ k y ge =
  Fin.toℕ-cast (lwkCast₂ B₁ B₂ B q b₁ k)
    (Source._↑*_ Source.weakenᵣ (sum B₁ + q + 1) casted)
  ■ toℕ-↑*-ge Source.weakenᵣ (sum B₁ + q + 1) casted ge′
  ■ cong (sum B₁ + q + 1 +_) (cong suc (toℕ-reduce≥ casted ge′))
  ■ Nat.+-suc (sum B₁ + q + 1) (Fin.toℕ casted Nat.∸ (sum B₁ + q + 1))
  ■ cong suc (Nat.m+[n∸m]≡n ge′)
  ■ cong suc (Fin.toℕ-cast (lwkCast₁ B₁ B₂ B q b₁ k) y)
  where
  casted : 𝔽 (sum B₁ + q + 1 + (b₁ + sum B₂ + sum B + k))
  casted = Fin.cast (lwkCast₁ B₁ B₂ B q b₁ k) y

  ge′ : sum B₁ + q + 1 Nat.≤ Fin.toℕ casted
  ge′ = subst (sum B₁ + q + 1 Nat.≤_)
          (sym (Fin.toℕ-cast (lwkCast₁ B₁ B₂ B q b₁ k) y)) ge

lwk-toℕ-≤ :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  Fin.toℕ (Source.SplitRenamings.lwk B₁ B₂ (sum B) {q} {b₁} {k} y) Nat.≤
  suc (Fin.toℕ y)
lwk-toℕ-≤ B₁ B₂ B q b₁ k y with Fin.toℕ y Nat.<? sum B₁ + q + 1
... | yes lt =
  Nat.≤-trans (Nat.≤-reflexive (lwk-toℕ-lo B₁ B₂ B q b₁ k y lt)) (Nat.n≤1+n _)
... | no ¬lt =
  Nat.≤-reflexive (lwk-toℕ-hi B₁ B₂ B q b₁ k y (Nat.≮⇒≥ ¬lt))

------------------------------------------------------------------------
-- Where the consumed handle sits.

atk-toℕ :
  ∀ (B₁ B₂ B : Typed.BindGroup) (w k : ℕ) (x : 𝔽 w) →
  Fin.toℕ (Source.SplitRenamings.atk B₁ B₂ (sum B) {w} {k} x) ≡
  sum B₁ + Fin.toℕ x
atk-toℕ B₁ B₂ B w k x =
  Fin.toℕ-↑ˡ _ k
  ■ Fin.toℕ-↑ˡ _ (sum B)
  ■ Fin.toℕ-cast (sym (sum-++ B₁ (w ∷ B₂))) (sum B₁ ↑ʳ (x ↑ˡ sum B₂))
  ■ Fin.toℕ-↑ʳ (sum B₁) (x ↑ˡ sum B₂)
  ■ cong (sum B₁ +_) (Fin.toℕ-↑ˡ x (sum B₂))

------------------------------------------------------------------------
-- The two group sizes.

sum-lwkq :
  ∀ (B₁ : Typed.BindGroup) {q b₁ : ℕ} {B₂ : Typed.BindGroup} →
  sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ≡
  suc (sum (B₁ ++ (q + suc b₁) ∷ B₂))
sum-lwkq B₁ {q} {b₁} {B₂} =
  sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)
  ■ cong (sum B₁ +_) (cong (Nat._+ sum B₂) (Nat.+-suc q (suc b₁)))
  ■ Nat.+-suc (sum B₁) ((q + suc b₁) + sum B₂)
  ■ cong suc (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))

split-point≤ :
  ∀ (B₁ : Typed.BindGroup) {q b₁ : ℕ} {B₂ : Typed.BindGroup} →
  sum B₁ + q + 1 Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
split-point≤ B₁ {q} {b₁} {B₂} =
  subst (sum B₁ + q + 1 Nat.≤_)
    (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
    (subst (Nat._≤ sum B₁ + ((q + suc b₁) + sum B₂))
      (sym (Nat.+-assoc (sum B₁) q 1))
      (Nat.+-monoʳ-≤ (sum B₁) q+1≤))
  where
  q+1≤ : q + 1 Nat.≤ (q + suc b₁) + sum B₂
  q+1≤ =
    Nat.≤-trans
      (Nat.+-monoʳ-≤ q (Nat.s≤s Nat.z≤n))
      (Nat.m≤m+n (q + suc b₁) (sum B₂))

------------------------------------------------------------------------
-- Positional lookup in a binder frame environment.

module _ {n k : ℕ} (G Bs : Typed.BindGroup) (channel : OrientedChannel n)
         (sigma : Translation.Env k (2 *ℕ n)) where
  private
    left right : 𝔽 (2 *ℕ n)
    left = physicalEndpoint channel 0F
    right = physicalEndpoint channel 1F

    envG : Translation.Env (sum G) (2 *ℕ n)
    envG =
      proj₁ (Translation.UB[ G ] left (SoupTerm.* , left , SoupTerm.*))

    envBs : Translation.Env (sum Bs) (2 *ℕ n)
    envBs =
      proj₁ (Translation.UB[ Bs ] right (SoupTerm.* , right , SoupTerm.*))

  bindEnv-group :
    (y : 𝔽 (sum G + sum Bs + k)) (w : 𝔽 (sum G)) →
    Fin.toℕ y ≡ Fin.toℕ w →
    bindEnv G Bs channel sigma y ≡
    proj₁ (Translation.UB[ G ]
            (physicalEndpoint channel 0F)
            (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)) w
  bindEnv-group y w equal =
    ++ₛ-lo (envG Translation.++ₛ envBs) sigma y (w ↑ˡ sum Bs)
      (equal ■ sym (Fin.toℕ-↑ˡ w (sum Bs)))
    ■ ++ₛ-lookupˡ envG envBs w

  bindEnv-mid :
    (y : 𝔽 (sum G + sum Bs + k)) (v : 𝔽 (sum Bs)) →
    Fin.toℕ y ≡ sum G + Fin.toℕ v →
    bindEnv G Bs channel sigma y ≡
    proj₁ (Translation.UB[ Bs ]
            (physicalEndpoint channel 1F)
            (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)) v
  bindEnv-mid y v equal =
    ++ₛ-lo (envG Translation.++ₛ envBs) sigma y (sum G ↑ʳ v)
      (equal ■ sym (Fin.toℕ-↑ʳ (sum G) v))
    ■ ++ₛ-lookupʳ envG envBs v

  bindEnv-outer :
    (y : 𝔽 (sum G + sum Bs + k)) (u : 𝔽 k) →
    Fin.toℕ y ≡ sum G + sum Bs + Fin.toℕ u →
    bindEnv G Bs channel sigma y ≡ sigma u
  bindEnv-outer y u equal =
    ++ₛ-hi (envG Translation.++ₛ envBs) sigma y u equal

------------------------------------------------------------------------
-- The environment agreement across `lwk`.
--
--   Every variable other than the consumed handle keeps its value when the
--   middle block of the first binder group grows by one.

module _ {n k : ℕ} (B₁ B₂ B : Typed.BindGroup) (q b₁ : ℕ)
         (channel : OrientedChannel n)
         (sigma : Translation.Env k (2 *ℕ n)) where
  private
    module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

    G G′ : Typed.BindGroup
    G = B₁ ++ (q + suc b₁) ∷ B₂
    G′ = B₁ ++ (q + suc (suc b₁)) ∷ B₂

    sizeEq : sum G′ ≡ suc (sum G)
    sizeEq = sum-lwkq B₁ {q} {b₁} {B₂}

    point≤ : sum B₁ + q + 1 Nat.≤ sum G
    point≤ = split-point≤ B₁ {q} {b₁} {B₂}

    atkℕ : Fin.toℕ (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)) ≡ sum B₁ + q
    atkℕ =
      atk-toℕ B₁ B₂ B (q + suc b₁) k (q ↑ʳ 0F)
      ■ cong (sum B₁ +_) (Fin.toℕ-↑ʳ q 0F ■ Nat.+-identityʳ q)

    +1 : ∀ (a : ℕ) → a + 1 ≡ suc a
    +1 a = Nat.+-comm a 1

    case-lo :
      (y : 𝔽 (sum G + sum B + k)) →
      Fin.toℕ y ≢ sum B₁ + q →
      Fin.toℕ y Nat.< sum G →
      bindEnv G B channel sigma y ≡
      bindEnv G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y)
    case-lo y notEqℕ ltG =
      bindEnv-group G B channel sigma y w (sym wℕ)
      ■ UB-lwk B₁ B₂ q b₁ (physicalEndpoint channel 0F)
          (physicalEndpoint channel 0F) SoupTerm.* SoupTerm.* w w′
          (λ same → notEqℕ (sym wℕ ■ same))
          (λ lt →
            w′ℕ
            ■ lwk-toℕ-lo B₁ B₂ B q b₁ k y
                (subst (Fin.toℕ y Nat.<_) (sym (+1 (sum B₁ + q)))
                  (Nat.<-trans
                    (Nat.≤-<-trans (Nat.≤-reflexive (sym wℕ)) lt)
                    (Nat.n<1+n _)))
            ■ sym wℕ)
          (λ gt →
            w′ℕ
            ■ lwk-toℕ-hi B₁ B₂ B q b₁ k y
                (subst (Nat._≤ Fin.toℕ y) (sym (+1 (sum B₁ + q)))
                  (Nat.≤-trans gt (Nat.≤-reflexive wℕ)))
            ■ cong suc (sym wℕ))
      ■ sym (bindEnv-group G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y) w′ (sym w′ℕ))
      where
      w : 𝔽 (sum G)
      w = Fin.fromℕ< ltG

      wℕ : Fin.toℕ w ≡ Fin.toℕ y
      wℕ = Fin.toℕ-fromℕ< ltG

      bound : Fin.toℕ (𝐒.lwk {q} {b₁} {k} y) Nat.< sum G′
      bound =
        subst (suc (Fin.toℕ (𝐒.lwk {q} {b₁} {k} y)) Nat.≤_) (sym sizeEq)
          (Nat.s≤s (Nat.≤-trans (lwk-toℕ-≤ B₁ B₂ B q b₁ k y) ltG))

      w′ : 𝔽 (sum G′)
      w′ = Fin.fromℕ< bound

      w′ℕ : Fin.toℕ w′ ≡ Fin.toℕ (𝐒.lwk {q} {b₁} {k} y)
      w′ℕ = Fin.toℕ-fromℕ< bound

    case-mid :
      (y : 𝔽 (sum G + sum B + k)) →
      sum G Nat.≤ Fin.toℕ y →
      Fin.toℕ y Nat.< sum G + sum B →
      bindEnv G B channel sigma y ≡
      bindEnv G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y)
    case-mid y geG ltGB =
      bindEnv-mid G B channel sigma y v yEq
      ■ sym (bindEnv-mid G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y) v lwkEq)
      where
      v : 𝔽 (sum B)
      v = Fin.fromℕ< (∸-bound geG ltGB)

      vℕ : Fin.toℕ v ≡ Fin.toℕ y Nat.∸ sum G
      vℕ = Fin.toℕ-fromℕ< (∸-bound geG ltGB)

      yEq : Fin.toℕ y ≡ sum G + Fin.toℕ v
      yEq = sym (cong (sum G +_) vℕ ■ Nat.m+[n∸m]≡n geG)

      lwkEq : Fin.toℕ (𝐒.lwk {q} {b₁} {k} y) ≡ sum G′ + Fin.toℕ v
      lwkEq =
        lwk-toℕ-hi B₁ B₂ B q b₁ k y (Nat.≤-trans point≤ geG)
        ■ cong suc yEq
        ■ sym (cong (Nat._+ Fin.toℕ v) sizeEq)

    case-outer :
      (y : 𝔽 (sum G + sum B + k)) →
      sum G + sum B Nat.≤ Fin.toℕ y →
      bindEnv G B channel sigma y ≡
      bindEnv G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y)
    case-outer y ge =
      bindEnv-outer G B channel sigma y u yEq
      ■ sym (bindEnv-outer G′ B channel sigma (𝐒.lwk {q} {b₁} {k} y) u lwkEq)
      where
      u : 𝔽 k
      u = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n y))

      uℕ : Fin.toℕ u ≡ Fin.toℕ y Nat.∸ (sum G + sum B)
      uℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n y))

      yEq : Fin.toℕ y ≡ sum G + sum B + Fin.toℕ u
      yEq = sym (cong (sum G + sum B +_) uℕ ■ Nat.m+[n∸m]≡n ge)

      lwkEq :
        Fin.toℕ (𝐒.lwk {q} {b₁} {k} y) ≡ sum G′ + sum B + Fin.toℕ u
      lwkEq =
        lwk-toℕ-hi B₁ B₂ B q b₁ k y
          (Nat.≤-trans point≤ (Nat.≤-trans (Nat.m≤m+n (sum G) (sum B)) ge))
        ■ cong suc yEq
        ■ sym (cong (λ z → z + sum B + Fin.toℕ u) sizeEq)

  source-target-lwk :
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
    y ≢ 𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F) →
    bindEnv (B₁ ++ (q + suc b₁) ∷ B₂) B channel sigma y ≡
    bindEnv (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B channel sigma
      (𝐒.lwk {q} {b₁} {k} y)
  source-target-lwk y notEq with Fin.toℕ y Nat.<? sum G
  ... | yes ltG =
    case-lo y (λ same → notEq (Fin.toℕ-injective (same ■ sym atkℕ))) ltG
  ... | no ¬ltG with Fin.toℕ y Nat.<? sum G + sum B
  ...   | yes ltGB = case-mid y (Nat.≮⇒≥ ¬ltG) ltGB
  ...   | no ¬ltGB = case-outer y (Nat.≮⇒≥ ¬ltGB)

------------------------------------------------------------------------
-- Flag lists.  The flag list of a binder group depends on the group only,
-- and the split does not change it: `ϕ[ q + suc b ] = ϕ[ q + suc (suc b) ]`
-- because both are positive.

positive-flag :
  ∀ (q b : ℕ) → Translation.ϕ[ q + suc b ] ≡ Translation.ϕ[ q + suc (suc b) ]
positive-flag zero b = refl
positive-flag (suc q) b = refl

bindFlags : Typed.BindGroup → List Soup.Flag
bindFlags [] = []
bindFlags (b ∷ []) = []
bindFlags (b ∷ B@(_ ∷ _)) = Translation.ϕ[ b ] ∷ bindFlags B

UBFrom-flags-shape :
  ∀ l (B : Typed.BindGroup) (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
  proj₂ (Translation.UBFrom l B r (e₁ , c , e₂)) ≡ bindFlags B
UBFrom-flags-shape l [] r c e₁ e₂ = refl
UBFrom-flags-shape l (b ∷ []) r c e₁ e₂ = refl
UBFrom-flags-shape l (b ∷ B@(b′ ∷ B′)) r c e₁ e₂
  with Translation.UBFrom (suc l) B r (SoupTerm.`phi (r , l) , c , e₂)
     | UBFrom-flags-shape (suc l) B r c (SoupTerm.`phi (r , l)) e₂
... | sigma , flags | equal = cong (Translation.ϕ[ b ] ∷_) equal

UB-flags-shape :
  ∀ (B : Typed.BindGroup) (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
  proj₂ (Translation.UB[ B ] r (e₁ , c , e₂)) ≡ bindFlags B
UB-flags-shape = UBFrom-flags-shape zero

bindFlags-lsplit :
  ∀ (B₁ B₂ : Typed.BindGroup) (q b : ℕ) →
  bindFlags (B₁ ++ (q + suc b) ∷ B₂) ≡
  bindFlags (B₁ ++ (q + suc (suc b)) ∷ B₂)
bindFlags-lsplit [] [] q b = refl
bindFlags-lsplit [] (b₂ ∷ B₂) q b =
  cong (λ z → z ∷ bindFlags (b₂ ∷ B₂)) (positive-flag q b)
bindFlags-lsplit (b₀ ∷ []) B₂ q b =
  cong (Translation.ϕ[ b₀ ] ∷_) (bindFlags-lsplit [] B₂ q b)
bindFlags-lsplit (b₀ ∷ b₁ ∷ B₁) B₂ q b =
  cong (Translation.ϕ[ b₀ ] ∷_) (bindFlags-lsplit (b₁ ∷ B₁) B₂ q b)

------------------------------------------------------------------------
-- The position kit: `blockAt B₁ B₂ w j` is position `j` of the middle block
-- of `B₁ ++ w ∷ B₂`, and `SplitRenamings.atk` is that position in the full
-- variable scope.

blockAt : ∀ (B₁ B₂ : Typed.BindGroup) w → 𝔽 w → 𝔽 (sum (B₁ ++ w ∷ B₂))
blockAt [] B₂ w x = x ↑ˡ sum B₂
blockAt (b ∷ B₁) B₂ w x = b ↑ʳ blockAt B₁ B₂ w x

blockAt-toℕ :
  ∀ (B₁ B₂ : Typed.BindGroup) w (x : 𝔽 w) →
  Fin.toℕ (blockAt B₁ B₂ w x) ≡ sum B₁ + Fin.toℕ x
blockAt-toℕ [] B₂ w x = Fin.toℕ-↑ˡ x (sum B₂)
blockAt-toℕ (b ∷ B₁) B₂ w x =
  Fin.toℕ-↑ʳ b (blockAt B₁ B₂ w x)
  ■ cong (b +_) (blockAt-toℕ B₁ B₂ w x)
  ■ sym (+-assoc b (sum B₁) (Fin.toℕ x))

private
  pos-split-gen :
    ∀ a (B₁ : Typed.BindGroup) c (B₂ : Typed.BindGroup)
      (i : 𝔽 (c + sum B₂)) →
    Fin.cast (sym (sum-++ (a ∷ B₁) (c ∷ B₂))) (sum (a ∷ B₁) ↑ʳ i) ≡
    a ↑ʳ Fin.cast (sym (sum-++ B₁ (c ∷ B₂))) (sum B₁ ↑ʳ i)
  pos-split-gen a B₁ c B₂ i = Fin.toℕ-injective
    ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁) (c ∷ B₂))) (sum (a ∷ B₁) ↑ʳ i)
    ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁)) i
    ■ +-assoc a (sum B₁) (Fin.toℕ i)
    ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁ (c ∷ B₂))) (sum B₁ ↑ʳ i))
          ■ cong (a +_)
              ( Fin.toℕ-cast (sym (sum-++ B₁ (c ∷ B₂))) (sum B₁ ↑ʳ i)
              ■ Fin.toℕ-↑ʳ (sum B₁) i ) ) )

  blockAt-cast :
    ∀ (B₁ B₂ : Typed.BindGroup) w (x : 𝔽 w) →
    blockAt B₁ B₂ w x ≡
    Fin.cast (sym (sum-++ B₁ (w ∷ B₂))) (sum B₁ ↑ʳ (x ↑ˡ sum B₂))
  blockAt-cast [] B₂ w x =
    sym (Fin.toℕ-injective
      ( Fin.toℕ-cast (sym (sum-++ [] (w ∷ B₂))) (sum [] ↑ʳ (x ↑ˡ sum B₂))
      ■ Fin.toℕ-↑ʳ (sum []) (x ↑ˡ sum B₂) ))
  blockAt-cast (b ∷ B₁) B₂ w x =
    cong (b ↑ʳ_) (blockAt-cast B₁ B₂ w x)
    ■ sym (pos-split-gen b B₁ w B₂ (x ↑ˡ sum B₂))

atk-blockAt :
  ∀ (B₁ B₂ B : Typed.BindGroup) w (k : ℕ) (x : 𝔽 w) →
  Source.SplitRenamings.atk B₁ B₂ (sum B) {w} {k} x ≡
  blockAt B₁ B₂ w x ↑ˡ sum B ↑ˡ k
atk-blockAt B₁ B₂ B w k x =
  cong (λ z → z ↑ˡ sum B ↑ˡ k) (sym (blockAt-cast B₁ B₂ w x))

------------------------------------------------------------------------
-- The three handles of an lsplit, inside one block.

private
  ub-+0 :
    ∀ w (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) (p : 𝔽 w) →
    Translation.Ub[ w + 0 ] (e₁ , c , e₂) (p ↑ˡ 0) ≡
    Translation.Ub[ w ] (e₁ , c , e₂) p
  ub-+0 zero c e₁ e₂ ()
  ub-+0 (suc zero) c e₁ e₂ 0F = refl
  ub-+0 (suc (suc w)) c e₁ e₂ 0F = refl
  ub-+0 (suc (suc w)) c e₁ e₂ (suc p) = ub-+0 (suc w) c SoupTerm.* e₂ p

  ub-suc-zero :
    ∀ q b (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
    Translation.Ub[ suc q + suc b ] (e₁ , c , e₂) (suc q ↑ʳ 0F) ≡
    Translation.Ub[ q + suc b ] (SoupTerm.* , c , e₂) (q ↑ʳ 0F)
  ub-suc-zero zero b c e₁ e₂ = refl
  ub-suc-zero (suc q) b c e₁ e₂ = refl

  ub-suc-zero′ :
    ∀ q b (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
    Translation.Ub[ suc q + suc (suc b) ] (e₁ , c , e₂) (suc q ↑ʳ 0F) ≡
    Translation.Ub[ q + suc (suc b) ] (SoupTerm.* , c , e₂) (q ↑ʳ 0F)
  ub-suc-zero′ zero b c e₁ e₂ = refl
  ub-suc-zero′ (suc q) b c e₁ e₂ = refl

  ub-suc-one′ :
    ∀ q b (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
    Translation.Ub[ suc q + suc (suc b) ] (e₁ , c , e₂) (suc q ↑ʳ 1F) ≡
    Translation.Ub[ q + suc (suc b) ] (SoupTerm.* , c , e₂) (q ↑ʳ 1F)
  ub-suc-one′ zero b c e₁ e₂ = refl
  ub-suc-one′ (suc q) b c e₁ e₂ = refl

  ub-lsplit :
    ∀ q b (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) →
    Σ[ e₁′ ∈ SoupTerm.Tm d ]
    Σ[ e₂′ ∈ SoupTerm.Tm d ]
      (Translation.Ub[ q + suc b ] (e₁ , c , e₂) (q ↑ʳ 0F) ≡
       Translation.chanTriple (e₁′ , c , e₂′))
    × (Translation.Ub[ q + suc (suc b) ] (e₁ , c , e₂) (q ↑ʳ 0F) ≡
       Translation.chanTriple (e₁′ , c , SoupTerm.*))
    × (Translation.Ub[ q + suc (suc b) ] (e₁ , c , e₂) (q ↑ʳ 1F) ≡
       Translation.chanTriple (SoupTerm.* , c , e₂′))
  ub-lsplit zero zero c e₁ e₂ = e₁ , e₂ , refl , refl , refl
  ub-lsplit zero (suc b) c e₁ e₂ = e₁ , SoupTerm.* , refl , refl , refl
  ub-lsplit (suc q) b c e₁ e₂ with ub-lsplit q b c SoupTerm.* e₂
  ... | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
    e₁′ , e₂′ ,
    (ub-suc-zero q b c e₁ e₂ ■ eq₀) ,
    (ub-suc-zero′ q b c e₁ e₂ ■ eq₁) ,
    (ub-suc-one′ q b c e₁ e₂ ■ eq₂)

UBFrom-lookupʳ :
  ∀ l b (B : Typed.BindGroup) (r c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
    (x : 𝔽 (sum B)) →
  proj₁ (Translation.UBFrom l (b ∷ B) r (e₁ , c , e₂)) (b ↑ʳ x) ≡
  proj₁ (Translation.UBFrom (suc l) B r
          (SoupTerm.`phi (r , l) , c , e₂)) x
UBFrom-lookupʳ l b [] r c e₁ e₂ ()
UBFrom-lookupʳ l b (b′ ∷ B) r c e₁ e₂ x
  with Translation.UBFrom (suc l) (b′ ∷ B) r
         (SoupTerm.`phi (r , l) , c , e₂)
... | sigma , flags =
  ++ₛ-lookupʳ (Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (r , l))) sigma x

------------------------------------------------------------------------
-- …and the same three handles inside a whole binder group.

group-lsplit-shape-from :
  ∀ l (B₁ B₂ : Typed.BindGroup) q b (r c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d) →
  Σ[ e₁′ ∈ SoupTerm.Tm d ]
  Σ[ e₂′ ∈ SoupTerm.Tm d ]
    (proj₁ (Translation.UBFrom l (B₁ ++ (q + suc b) ∷ B₂) r (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)) ≡
     Translation.chanTriple (e₁′ , c , e₂′))
  × (proj₁ (Translation.UBFrom l (B₁ ++ (q + suc (suc b)) ∷ B₂) r
      (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F)) ≡
     Translation.chanTriple (e₁′ , c , SoupTerm.*))
  × (proj₁ (Translation.UBFrom l (B₁ ++ (q + suc (suc b)) ∷ B₂) r
      (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F)) ≡
     Translation.chanTriple (SoupTerm.* , c , e₂′))
group-lsplit-shape-from l [] [] q b r c e₁ e₂ =
  let h = ub-lsplit q b c e₁ e₂ in
  proj₁ h , proj₁ (proj₂ h) ,
  (ub-+0 (q + suc b) c e₁ e₂ (q ↑ʳ 0F) ■ proj₁ (proj₂ (proj₂ h))) ,
  (ub-+0 (q + suc (suc b)) c e₁ e₂ (q ↑ʳ 0F)
   ■ proj₁ (proj₂ (proj₂ (proj₂ h)))) ,
  (ub-+0 (q + suc (suc b)) c e₁ e₂ (q ↑ʳ 1F)
   ■ proj₂ (proj₂ (proj₂ (proj₂ h))))
group-lsplit-shape-from l [] (b₂ ∷ B₂) q b r c e₁ e₂
  with Translation.UBFrom (suc l) (b₂ ∷ B₂) r
         (SoupTerm.`phi (r , l) , c , e₂)
     | ub-lsplit q b c e₁ (SoupTerm.`phi (r , l))
... | sigma , flags | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
  e₁′ , e₂′ ,
  (++ₛ-lookupˡ
     (Translation.Ub[ q + suc b ] (e₁ , c , SoupTerm.`phi (r , l)))
     sigma (q ↑ʳ 0F)
   ■ eq₀) ,
  (++ₛ-lookupˡ
     (Translation.Ub[ q + suc (suc b) ] (e₁ , c , SoupTerm.`phi (r , l)))
     sigma (q ↑ʳ 0F)
   ■ eq₁) ,
  (++ₛ-lookupˡ
     (Translation.Ub[ q + suc (suc b) ] (e₁ , c , SoupTerm.`phi (r , l)))
     sigma (q ↑ʳ 1F)
   ■ eq₂)
group-lsplit-shape-from l (b₀ ∷ B₁) B₂ q b r c e₁ e₂
  with Translation.UBFrom (suc l) (B₁ ++ (q + suc b) ∷ B₂) r
         (SoupTerm.`phi (r , l) , c , e₂) in ubEq
     | Translation.UBFrom (suc l) (B₁ ++ (q + suc (suc b)) ∷ B₂) r
         (SoupTerm.`phi (r , l) , c , e₂) in ubEq′
     | group-lsplit-shape-from (suc l) B₁ B₂ q b r c
         (SoupTerm.`phi (r , l)) e₂
... | sigma₀ , flags₀ | sigma₁ , flags₁ | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
  e₁′ , e₂′ ,
  (UBFrom-lookupʳ l b₀ (B₁ ++ (q + suc b) ∷ B₂) r c e₁ e₂
     (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F))
   ■ cong (λ result → proj₁ result (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F))) ubEq
   ■ eq₀) ,
  (UBFrom-lookupʳ l b₀ (B₁ ++ (q + suc (suc b)) ∷ B₂) r c e₁ e₂
     (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F))
   ■ cong (λ result →
             proj₁ result (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F))) ubEq′
   ■ eq₁) ,
  (UBFrom-lookupʳ l b₀ (B₁ ++ (q + suc (suc b)) ∷ B₂) r c e₁ e₂
     (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F))
   ■ cong (λ result →
             proj₁ result (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F))) ubEq′
   ■ eq₂)

group-lsplit-shape :
  ∀ (B₁ B₂ : Typed.BindGroup) q b (r c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d) →
  Σ[ e₁′ ∈ SoupTerm.Tm d ]
  Σ[ e₂′ ∈ SoupTerm.Tm d ]
    (proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] r (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)) ≡
     Translation.chanTriple (e₁′ , c , e₂′))
  × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b)) ∷ B₂ ] r (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F)) ≡
     Translation.chanTriple (e₁′ , c , SoupTerm.*))
  × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b)) ∷ B₂ ] r (e₁ , c , e₂))
      (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F)) ≡
     Translation.chanTriple (SoupTerm.* , c , e₂′))
group-lsplit-shape = group-lsplit-shape-from zero

------------------------------------------------------------------------
-- Translating a source term under *two* renamings.
--
--   The split rules factor their evaluation frame as `E₀ ⋯ᶠ* ρ⁻ ⋯ᶠ* lwk`,
--   with the environment agreement only available on the image of `ρ⁻`; the
--   one-renaming lemmas of `Local/Frames.agda` do not apply.

T-ren-ren-coh :
  ∀ {a b c : ℕ} (e : Source.Tm a)
    (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
    (sigma₁ : Translation.Env b d) (sigma₂ : Translation.Env c d) →
  ((x : 𝔽 a) → sigma₁ (θ x) ≡ sigma₂ (κ (θ x))) →
  Translation.T[ Source._⋯_ e θ ] sigma₁ ≡
  Translation.T[ Source._⋯_ (Source._⋯_ e θ) κ ] sigma₂
T-ren-ren-coh e θ κ sigma₁ sigma₂ coh =
  T[_]-⋯ᵣ e θ sigma₁
  ■ T[_]-Env-cong e coh
  ■ sym (T[_]-⋯ᵣ e θ (sigma₂ ∘ κ))
  ■ sym (T[_]-⋯ᵣ (Source._⋯_ e θ) κ sigma₂)

lift-ren-ren-coh :
  ∀ {a b c : ℕ}
    (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
    (sigma₁ : Translation.Env b d) (sigma₂ : Translation.Env c d) →
  ((x : 𝔽 a) → sigma₁ (θ x) ≡ sigma₂ (κ (θ x))) →
  (x : 𝔽 (1 + a)) →
  Translation.liftEnv sigma₁ ((θ Source.↑ᵣ) x) ≡
  Translation.liftEnv sigma₂ ((κ Source.↑ᵣ) ((θ Source.↑ᵣ) x))
lift-ren-ren-coh θ κ sigma₁ sigma₂ coh 0F = refl
lift-ren-ren-coh θ κ sigma₁ sigma₂ coh (suc x) = cong SoupTerm.wk (coh x)

Tᶠ-plug-ren-ren-coh :
  ∀ {a b c : ℕ} (F₀ : SourceReduction.Frame a)
    (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
    (sigma₁ : Translation.Env b d) (sigma₂ : Translation.Env c d)
    (Vsigma₁ : ValueEnv sigma₁) (Vsigma₂ : ValueEnv sigma₂) →
  ((x : 𝔽 a) → sigma₁ (θ x) ≡ sigma₂ (κ (θ x))) →
  (t : SoupTerm.Tm d) →
  SoupExpression._[_]
    (Tᶠ[ SourceReduction._⋯ᶠ_ F₀ θ ] {σ = sigma₁} Vsigma₁) t ≡
  SoupExpression._[_]
    (Tᶠ[ SourceReduction._⋯ᶠ_ (SourceReduction._⋯ᶠ_ F₀ θ) κ ]
      {σ = sigma₂} Vsigma₂) t
Tᶠ-plug-ren-ren-coh (SourceReduction.app₁ e dir V?)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → t SoupTerm.·⟨ dir ⟩ z) (T-ren-ren-coh e θ κ sigma₁ sigma₂ coh)
Tᶠ-plug-ren-ren-coh (SourceReduction.app₂ e dir V?)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → z SoupTerm.·⟨ dir ⟩ t) (T-ren-ren-coh e θ κ sigma₁ sigma₂ coh)
Tᶠ-plug-ren-ren-coh (SourceReduction.□⊗ e)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → t SoupTerm.⊗ z) (T-ren-ren-coh e θ κ sigma₁ sigma₂ coh)
Tᶠ-plug-ren-ren-coh (V SourceReduction.⊗□)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → z SoupTerm.⊗ t)
    (T-ren-ren-coh (SourceReduction.vTm V) θ κ sigma₁ sigma₂ coh)
Tᶠ-plug-ren-ren-coh (SourceReduction.□; e)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → t SoupTerm.; z) (T-ren-ren-coh e θ κ sigma₁ sigma₂ coh)
Tᶠ-plug-ren-ren-coh (SourceReduction.`let-`in e)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → SoupTerm.`let t `in z)
    (T-ren-ren-coh e (θ Source.↑ᵣ) (κ Source.↑ᵣ)
      (Translation.liftEnv sigma₁) (Translation.liftEnv sigma₂)
      (lift-ren-ren-coh θ κ sigma₁ sigma₂ coh))
Tᶠ-plug-ren-ren-coh (SourceReduction.`let⊗-`in e)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong (λ z → SoupTerm.`let⊗ t `in z)
    (T-ren-ren-coh e ((θ Source.↑ᵣ) Source.↑ᵣ) ((κ Source.↑ᵣ) Source.↑ᵣ)
      (Translation.liftEnv (Translation.liftEnv sigma₁))
      (Translation.liftEnv (Translation.liftEnv sigma₂))
      (lift-ren-ren-coh (θ Source.↑ᵣ) (κ Source.↑ᵣ)
        (Translation.liftEnv sigma₁) (Translation.liftEnv sigma₂)
        (lift-ren-ren-coh θ κ sigma₁ sigma₂ coh)))
Tᶠ-plug-ren-ren-coh (SourceReduction.`inj□ i)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t = refl
Tᶠ-plug-ren-ren-coh (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩)
  θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  cong₂ (λ z₁ z₂ → SoupTerm.`case t `of⟨ z₁ ; z₂ ⟩)
    (T-ren-ren-coh e₁ (θ Source.↑ᵣ) (κ Source.↑ᵣ)
      (Translation.liftEnv sigma₁) (Translation.liftEnv sigma₂)
      (lift-ren-ren-coh θ κ sigma₁ sigma₂ coh))
    (T-ren-ren-coh e₂ (θ Source.↑ᵣ) (κ Source.↑ᵣ)
      (Translation.liftEnv sigma₁) (Translation.liftEnv sigma₂)
      (lift-ren-ren-coh θ κ sigma₁ sigma₂ coh))

Tᶠ*-plug-ren-ren-coh :
  ∀ {a b c : ℕ} (E : SourceReduction.Frame* a)
    (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
    (sigma₁ : Translation.Env b d) (sigma₂ : Translation.Env c d)
    (Vsigma₁ : ValueEnv sigma₁) (Vsigma₂ : ValueEnv sigma₂) →
  ((x : 𝔽 a) → sigma₁ (θ x) ≡ sigma₂ (κ (θ x))) →
  (t : SoupTerm.Tm d) →
  SoupExpression._[_]*
    (Tᶠ*[ SourceReduction._⋯ᶠ*_ E θ ] {σ = sigma₁} Vsigma₁) t ≡
  SoupExpression._[_]*
    (Tᶠ*[ SourceReduction._⋯ᶠ*_ (SourceReduction._⋯ᶠ*_ E θ) κ ]
      {σ = sigma₂} Vsigma₂) t
Tᶠ*-plug-ren-ren-coh [] θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t = refl
Tᶠ*-plug-ren-ren-coh (F₀ ∷ E) θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t =
  Tᶠ-plug-ren-ren-coh F₀ θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh
    (SoupExpression._[_]*
      (Tᶠ*[ SourceReduction._⋯ᶠ*_ E θ ] {σ = sigma₁} Vsigma₁) t)
  ■ cong
      (SoupExpression._[_]
        (Tᶠ[ SourceReduction._⋯ᶠ_ (SourceReduction._⋯ᶠ_ F₀ θ) κ ]
          {σ = sigma₂} Vsigma₂))
      (Tᶠ*-plug-ren-ren-coh E θ κ sigma₁ sigma₂ Vsigma₁ Vsigma₂ coh t)
