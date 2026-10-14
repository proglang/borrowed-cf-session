-- | The toℕ spec layer for the ALIGNED realisation coherences
--   (`RealiseCohProof`).  Every block-permutation renaming in sight —
--   Factor's `bswapRen`/`dragRen` composites on the one hand, the
--   Congruence engine's `Φᵗ` / `assocSwapᵣ`-factor composites on the
--   other — is characterised by a ℕ-level SPEC (`asF` for a block move,
--   `lift↑` for lifting under binders), and the two sides are matched
--   region by region.  This is what lets `RealiseCohProof` route the
--   thread coherences through `subEqComm-gen` / `subEq-gen`.
module BorrowedCF.Simulation.Support.Normal.RealiseCohNat where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Translation using (syncs)
open import BorrowedCF.Processes.Typed using (BindGroup)
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; []; tν; tφ; _++ᵗ_)
open import BorrowedCF.Simulation.Support.Normal.Image
  using (φTel; φTelᵣ; scope≡)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift1; shift2)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
  using (Run; rnil; rφ; bubν⁻; bubφ⁻)
open import BorrowedCF.Simulation.Support.Normal.Factor using (dragRen; bswapRen)
open import BorrowedCF.Simulation.Support.TypedPrenex
  using (TTel; []ᵗ; tνᵗ; _⋯ᵗᵉˡ_)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (BTel)
open import BorrowedCF.Simulation.Support.BlockPerm
  using ( toℕ-assoc-lt; toℕ-assoc-mid; toℕ-assoc-ge
        ; toℕ-swapᵣ-lt; toℕ-swapᵣ-mid; toℕ-swapᵣ-ge
        ; toℕ-assoc↑*-fix-ge )
open import BorrowedCF.Simulation.Support.CongruenceH2
  using (Φᵗ; Φᵗ-A; Φᵗ-Adata; Φᵗ-B; lift-fix-ge; ρacc-fix-ge; ρω-fix-ge)

open import Data.Bool using (T)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- ℕ-level combinators: block-move spec and binder lift.
------------------------------------------------------------------------

-- `asF a b`: move the lowest `a`-chunk up past the next `b`-chunk.
asF : ℕ → ℕ → ℕ → ℕ
asF a b k = if k Nat.<ᵇ a then b + k else (if k Nat.<ᵇ a + b then k Nat.∸ a else k)

-- `lift↑ c F`: F lifted under c inert binders.
lift↑ : ℕ → (ℕ → ℕ) → ℕ → ℕ
lift↑ zero    F k       = F k
lift↑ (suc c) F zero    = zero
lift↑ (suc c) F (suc k) = suc (lift↑ c F k)

private
  Tb⇒≡ : ∀ b → T b → b ≡ true
  Tb⇒≡ true  _ = refl
  Tb⇒≡ false ()

  ¬Tb⇒≡ : ∀ b → (T b → ⊥) → b ≡ false
  ¬Tb⇒≡ true  h = ⊥-elim (h _)
  ¬Tb⇒≡ false _ = refl

  <ᵇ-true : ∀ {k a} → k Nat.< a → (k Nat.<ᵇ a) ≡ true
  <ᵇ-true lt = Tb⇒≡ _ (Nat.<⇒<ᵇ lt)

  <ᵇ-false : ∀ {k a} → a Nat.≤ k → (k Nat.<ᵇ a) ≡ false
  <ᵇ-false {k} {a} ge = ¬Tb⇒≡ _ (λ t → Nat.<⇒≱ (Nat.<ᵇ⇒< k a t) ge)

asF-lt : ∀ a b {k} → k Nat.< a → asF a b k ≡ b + k
asF-lt a b {k} lt =
  cong (λ z → if z then b + k else (if k Nat.<ᵇ a + b then k Nat.∸ a else k))
       (<ᵇ-true lt)

asF-mid : ∀ a b {k} → a Nat.≤ k → k Nat.< a + b → asF a b k ≡ k Nat.∸ a
asF-mid a b {k} ge lt =
  cong₂ (λ z₁ z₂ → if z₁ then b + k else (if z₂ then k Nat.∸ a else k))
        (<ᵇ-false ge) (<ᵇ-true lt)

asF-ge : ∀ a b {k} → a + b Nat.≤ k → asF a b k ≡ k
asF-ge a b {k} ge =
  cong₂ (λ z₁ z₂ → if z₁ then b + k else (if z₂ then k Nat.∸ a else k))
        (<ᵇ-false (Nat.≤-trans (Nat.m≤m+n a b) ge)) (<ᵇ-false ge)

asF-0 : ∀ c k → asF 0 c k ≡ k
asF-0 c k with k Nat.<ᵇ c
... | true  = refl
... | false = refl

lift↑-lt : ∀ {c k} (F : ℕ → ℕ) → k Nat.< c → lift↑ c F k ≡ k
lift↑-lt {suc c} {zero}  F lt = refl
lift↑-lt {suc c} {suc k} F lt = cong suc (lift↑-lt F (Nat.s≤s⁻¹ lt))

lift↑-ge : ∀ c (F : ℕ → ℕ) m → lift↑ c F (c + m) ≡ c + F m
lift↑-ge zero    F m = refl
lift↑-ge (suc c) F m = cong suc (lift↑-ge c F m)

lift↑-ge′ : ∀ {c k} (F : ℕ → ℕ) → c Nat.≤ k → lift↑ c F k ≡ c + F (k Nat.∸ c)
lift↑-ge′ {c} {k} F ge =
  cong (lift↑ c F) (sym (Nat.m+[n∸m]≡n ge)) ■ lift↑-ge c F (k Nat.∸ c)

lift↑-+ : ∀ c j (F : ℕ → ℕ) k → lift↑ c (lift↑ j F) k ≡ lift↑ (c + j) F k
lift↑-+ zero    j F k       = refl
lift↑-+ (suc c) j F zero    = refl
lift↑-+ (suc c) j F (suc k) = cong suc (lift↑-+ c j F k)

lift↑-cong : ∀ c {F G : ℕ → ℕ} → (∀ k → F k ≡ G k) →
             ∀ k → lift↑ c F k ≡ lift↑ c G k
lift↑-cong zero    h k       = h k
lift↑-cong (suc c) h zero    = refl
lift↑-cong (suc c) h (suc k) = cong suc (lift↑-cong c h k)

lift↑-id : ∀ c {F : ℕ → ℕ} → (∀ k → F k ≡ k) → ∀ k → lift↑ c F k ≡ k
lift↑-id zero    h k       = h k
lift↑-id (suc c) h zero    = refl
lift↑-id (suc c) h (suc k) = cong suc (lift↑-id c h k)

lift↑-∘ : ∀ c (F G : ℕ → ℕ) k →
          lift↑ c F (lift↑ c G k) ≡ lift↑ c (λ z → F (G z)) k
lift↑-∘ zero    F G k       = refl
lift↑-∘ (suc c) F G zero    = refl
lift↑-∘ (suc c) F G (suc k) = cong suc (lift↑-∘ c F G k)

------------------------------------------------------------------------
-- ℕ arithmetic helpers.
------------------------------------------------------------------------

private
  ∸-cancelˡ′ : ∀ x y z → (x + y) Nat.∸ (x + z) ≡ y Nat.∸ z
  ∸-cancelˡ′ zero    y z = refl
  ∸-cancelˡ′ (suc x) y z = ∸-cancelˡ′ x y z

  -- c + ((k ∸ c) ∸ a) ≡ k ∸ a, when a + c ≤ k.
  midshuffle : ∀ a c k → a + c Nat.≤ k → c + ((k Nat.∸ c) Nat.∸ a) ≡ k Nat.∸ a
  midshuffle a c k ge =
      cong (c +_) (Nat.∸-+-assoc k c a)
    ■ sym (Nat.+-∸-assoc c {k} {c + a} (subst (Nat._≤ k) (Nat.+-comm a c) ge))
    ■ ∸-cancelˡ′ c k a

  -- a ≤ k ∸ c, when a + c ≤ k.
  ∸-lb : ∀ a c k → a + c Nat.≤ k → a Nat.≤ k Nat.∸ c
  ∸-lb a c k ge =
    subst (Nat._≤ k Nat.∸ c) (Nat.m+n∸n≡m a c) (Nat.∸-monoˡ-≤ c ge)

  -- k ∸ c < a + j, when c ≤ k and k < a + c + j.
  ∸-ub : ∀ a c j k → c Nat.≤ k → k Nat.< a + c + j → k Nat.∸ c Nat.< a + j
  ∸-ub a c j k c≤k lt =
    Nat.+-cancelˡ-< c (k Nat.∸ c) (a + j)
      (subst (Nat._< c + (a + j)) (sym (Nat.m+[n∸m]≡n c≤k))
        (subst (k Nat.<_)
          (solve 3 (λ a' c' j' → a' :+ c' :+ j' := c' :+ (a' :+ j'))
                 refl a c j)
          lt))

------------------------------------------------------------------------
-- The two composite-fusion laws on specs.
------------------------------------------------------------------------

private
  step-lo : ∀ a c j k → k Nat.< a →
            lift↑ c (asF a j) (asF a c k) ≡ asF a (c + j) k
  step-lo a c j k lt =
      cong (lift↑ c (asF a j)) (asF-lt a c lt)
    ■ lift↑-ge c (asF a j) k
    ■ cong (c +_) (asF-lt a j lt)
    ■ sym (Nat.+-assoc c j k)
    ■ sym (asF-lt a (c + j) lt)

  step-mid1 : ∀ a c j k → a Nat.≤ k → k Nat.< a + c →
              lift↑ c (asF a j) (asF a c k) ≡ asF a (c + j) k
  step-mid1 a c j k ge lt2 =
      cong (lift↑ c (asF a j)) (asF-mid a c ge lt2)
    ■ lift↑-lt (asF a j)
        (Nat.+-cancelˡ-< a (k Nat.∸ a) c
          (subst (Nat._< a + c) (sym (Nat.m+[n∸m]≡n ge)) lt2))
    ■ sym (asF-mid a (c + j) ge (Nat.<-≤-trans lt2 (Nat.+-monoʳ-≤ a (Nat.m≤m+n c j))))

  step-mid2 : ∀ a c j k → a + c Nat.≤ k → k Nat.< a + c + j →
              lift↑ c (asF a j) (asF a c k) ≡ asF a (c + j) k
  step-mid2 a c j k ge2 lt3 =
      cong (lift↑ c (asF a j)) (asF-ge a c ge2)
    ■ lift↑-ge′ (asF a j) c≤k
    ■ cong (c +_) (asF-mid a j (∸-lb a c k ge2) (∸-ub a c j k c≤k lt3))
    ■ midshuffle a c k ge2
    ■ sym (asF-mid a (c + j) (Nat.≤-trans (Nat.m≤m+n a c) ge2)
            (subst (k Nat.<_) (Nat.+-assoc a c j) lt3))
    where
      c≤k : c Nat.≤ k
      c≤k = Nat.≤-trans (Nat.m≤n+m c a) ge2

  step-hi : ∀ a c j k → a + c + j Nat.≤ k →
            lift↑ c (asF a j) (asF a c k) ≡ asF a (c + j) k
  step-hi a c j k ge3 =
      cong (lift↑ c (asF a j)) (asF-ge a c ge2)
    ■ lift↑-ge′ (asF a j) c≤k
    ■ cong (c +_) (asF-ge a j aj≤)
    ■ Nat.m+[n∸m]≡n c≤k
    ■ sym (asF-ge a (c + j) (subst (Nat._≤ k) (Nat.+-assoc a c j) ge3))
    where
      ge2 : a + c Nat.≤ k
      ge2 = Nat.≤-trans (Nat.m≤m+n (a + c) j) ge3
      c≤k : c Nat.≤ k
      c≤k = Nat.≤-trans (Nat.m≤n+m c a) ge2
      aj≤ : a + j Nat.≤ k Nat.∸ c
      aj≤ = subst (Nat._≤ k Nat.∸ c) (Nat.m+n∸m≡n c (a + j))
              (Nat.∸-monoˡ-≤ c
                (subst (Nat._≤ k)
                  (solve 3 (λ a' c' j' → a' :+ c' :+ j' := c' :+ (a' :+ j'))
                         refl a c j)
                  ge3))

-- A width-`a` block that has already crossed `c` cells crosses `j` more.
asF-stepgen : ∀ a c j k → lift↑ c (asF a j) (asF a c k) ≡ asF a (c + j) k
asF-stepgen a c j k with k Nat.<? a
... | yes lt = step-lo a c j k lt
... | no ¬lt with k Nat.<? (a + c)
...   | yes lt2 = step-mid1 a c j k (Nat.≮⇒≥ ¬lt) lt2
...   | no ¬lt2 with k Nat.<? (a + c + j)
...     | yes lt3 = step-mid2 a c j k (Nat.≮⇒≥ ¬lt2) lt3
...     | no ¬lt3 = step-hi a c j k (Nat.≮⇒≥ ¬lt3)

private
  drag-lo : ∀ lb c b m → m Nat.< lb →
            asF lb c (lift↑ lb (asF b c) m) ≡ asF (lb + b) c m
  drag-lo lb c b m lt =
      cong (asF lb c) (lift↑-lt (asF b c) lt)
    ■ asF-lt lb c lt
    ■ sym (asF-lt (lb + b) c (Nat.<-≤-trans lt (Nat.m≤m+n lb b)))

  drag-mid1 : ∀ lb c b m → lb Nat.≤ m → m Nat.< lb + b →
              asF lb c (lift↑ lb (asF b c) m) ≡ asF (lb + b) c m
  drag-mid1 lb c b m ge lt =
      cong (asF lb c) (lift↑-ge′ (asF b c) ge)
    ■ cong (λ z → asF lb c (lb + z)) (asF-lt b c m′lt)
    ■ asF-ge lb c (Nat.+-monoʳ-≤ lb (Nat.m≤m+n c (m Nat.∸ lb)))
    ■ solve 3 (λ lb' c' m' → lb' :+ (c' :+ m') := c' :+ (lb' :+ m'))
        refl lb c (m Nat.∸ lb)
    ■ cong (λ z → c + z) (Nat.m+[n∸m]≡n ge)
    ■ sym (asF-lt (lb + b) c lt)
    where
      m′lt : m Nat.∸ lb Nat.< b
      m′lt = Nat.+-cancelˡ-< lb (m Nat.∸ lb) b
               (subst (Nat._< lb + b) (sym (Nat.m+[n∸m]≡n ge)) lt)

  drag-mid2 : ∀ lb c b m → lb + b Nat.≤ m → m Nat.< lb + b + c →
              asF lb c (lift↑ lb (asF b c) m) ≡ asF (lb + b) c m
  drag-mid2 lb c b m ge2 lt3 =
      cong (asF lb c) (lift↑-ge′ (asF b c) lb≤m)
    ■ cong (λ z → asF lb c (lb + z)) (asF-mid b c b≤m′ m′lt)
    ■ asF-mid lb c (Nat.m≤m+n lb _) lb+z<lb+c
    ■ Nat.m+n∸m≡n lb ((m Nat.∸ lb) Nat.∸ b)
    ■ Nat.∸-+-assoc m lb b
    ■ sym (asF-mid (lb + b) c ge2 lt3)
    where
      lb≤m : lb Nat.≤ m
      lb≤m = Nat.≤-trans (Nat.m≤m+n lb b) ge2
      b≤m′ : b Nat.≤ m Nat.∸ lb
      b≤m′ = subst (Nat._≤ m Nat.∸ lb) (Nat.m+n∸m≡n lb b) (Nat.∸-monoˡ-≤ lb ge2)
      m′lt : m Nat.∸ lb Nat.< b + c
      m′lt = ∸-ub b lb c m lb≤m
               (subst (m Nat.<_)
                 (solve 3 (λ lb' b' c' → lb' :+ b' :+ c' := b' :+ lb' :+ c')
                        refl lb b c)
                 lt3)
      lb+z<lb+c : lb + ((m Nat.∸ lb) Nat.∸ b) Nat.< lb + c
      lb+z<lb+c = Nat.+-monoʳ-< lb
                  (Nat.+-cancelˡ-< b ((m Nat.∸ lb) Nat.∸ b) c
                    (subst (Nat._< b + c) (sym (Nat.m+[n∸m]≡n b≤m′)) m′lt))

  drag-hi : ∀ lb c b m → lb + b + c Nat.≤ m →
            asF lb c (lift↑ lb (asF b c) m) ≡ asF (lb + b) c m
  drag-hi lb c b m ge3 =
      cong (asF lb c) (lift↑-ge′ (asF b c) lb≤m)
    ■ cong (λ z → asF lb c (lb + z)) (asF-mge)
    ■ cong (asF lb c) (Nat.m+[n∸m]≡n lb≤m)
    ■ asF-ge lb c Lc≤m
    ■ sym (asF-ge (lb + b) c ge3)
    where
      lb≤m : lb Nat.≤ m
      lb≤m = Nat.≤-trans (Nat.m≤m+n lb b)
              (Nat.≤-trans (Nat.m≤m+n (lb + b) c) ge3)
      bc≤m′ : b + c Nat.≤ m Nat.∸ lb
      bc≤m′ = subst (Nat._≤ m Nat.∸ lb) (Nat.m+n∸m≡n lb (b + c))
                (Nat.∸-monoˡ-≤ lb
                  (subst (Nat._≤ m) (Nat.+-assoc lb b c) ge3))
      asF-mge : asF b c (m Nat.∸ lb) ≡ m Nat.∸ lb
      asF-mge = asF-ge b c bc≤m′
      Lc≤m : lb + c Nat.≤ m
      Lc≤m = Nat.≤-trans (Nat.+-monoˡ-≤ c (Nat.m≤m+n lb b)) ge3

-- The drag core: a `b`-wide block that still has to cross `c` cells joins
-- the `lb` cells already dragged out.
drag-step0 : ∀ lb c b m → asF lb c (lift↑ lb (asF b c) m) ≡ asF (lb + b) c m
drag-step0 lb c b m with m Nat.<? lb
... | yes lt = drag-lo lb c b m lt
... | no ¬lt with m Nat.<? (lb + b)
...   | yes lt2 = drag-mid1 lb c b m (Nat.≮⇒≥ ¬lt) lt2
...   | no ¬lt2 with m Nat.<? (lb + b + c)
...     | yes lt3 = drag-mid2 lb c b m (Nat.≮⇒≥ ¬lt2) lt3
...     | no ¬lt3 = drag-hi lb c b m (Nat.≮⇒≥ ¬lt3)

-- The two-block involution: swapping back is the identity.
asF-invol : ∀ a b k → asF b a (asF a b k) ≡ k
asF-invol a b k with k Nat.<? a
... | yes lt =
    cong (asF b a) (asF-lt a b lt)
  ■ asF-mid b a (Nat.m≤m+n b k) (Nat.+-monoʳ-< b lt)
  ■ Nat.m+n∸m≡n b k
... | no ¬lt with k Nat.<? (a + b)
...   | yes lt2 =
        cong (asF b a) (asF-mid a b (Nat.≮⇒≥ ¬lt) lt2)
      ■ asF-lt b a (Nat.+-cancelˡ-< a (k Nat.∸ a) b
          (subst (Nat._< a + b) (sym (Nat.m+[n∸m]≡n (Nat.≮⇒≥ ¬lt))) lt2))
      ■ Nat.m+[n∸m]≡n (Nat.≮⇒≥ ¬lt)
...   | no ¬lt2 =
        cong (asF b a) (asF-ge a b (Nat.≮⇒≥ ¬lt2))
      ■ asF-ge b a (subst (Nat._≤ k) (Nat.+-comm a b) (Nat.≮⇒≥ ¬lt2))

-- The flip commutation: the within-node run swap commutes with the
-- ν-pair swap sitting above it.
private
  flip-mid : ∀ s1 s2 k → s2 Nat.≤ k → k Nat.< s2 + s1 →
             asF s2 s1 (lift↑ (s1 + s2) (asF 1 1) k)
               ≡ lift↑ (s1 + s2) (asF 1 1) (asF s2 s1 k)
  flip-mid s1 s2 k ge lt2 =
      cong (asF s2 s1)
        (lift↑-lt (asF 1 1) (subst (k Nat.<_) (Nat.+-comm s2 s1) lt2))
    ■ asF-mid s2 s1 ge lt2
    ■ sym (lift↑-lt (asF 1 1)
        (Nat.<-≤-trans
          (Nat.+-cancelˡ-< s2 (k Nat.∸ s2) s1
            (subst (Nat._< s2 + s1) (sym (Nat.m+[n∸m]≡n ge)) lt2))
          (Nat.m≤m+n s1 s2)))
    ■ sym (cong (lift↑ (s1 + s2) (asF 1 1)) (asF-mid s2 s1 ge lt2))

  flip-ge : ∀ s1 s2 k → s2 + s1 Nat.≤ k →
            asF s2 s1 (lift↑ (s1 + s2) (asF 1 1) k)
              ≡ lift↑ (s1 + s2) (asF 1 1) (asF s2 s1 k)
  flip-ge s1 s2 k ge2 =
      asF-ge s2 s1 bound
    ■ sym (cong (lift↑ (s1 + s2) (asF 1 1)) (asF-ge s2 s1 ge2))
    where
      vEq : lift↑ (s1 + s2) (asF 1 1) k
              ≡ (s1 + s2) + asF 1 1 (k Nat.∸ (s1 + s2))
      vEq = lift↑-ge′ (asF 1 1) (subst (Nat._≤ k) (Nat.+-comm s2 s1) ge2)
      bound : s2 + s1 Nat.≤ lift↑ (s1 + s2) (asF 1 1) k
      bound = subst (s2 + s1 Nat.≤_) (sym vEq)
                (Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm s2 s1))
                  (Nat.m≤m+n (s1 + s2) (asF 1 1 (k Nat.∸ (s1 + s2)))))

flip-comm : ∀ s1 s2 k →
            asF s2 s1 (lift↑ (s1 + s2) (asF 1 1) k)
              ≡ lift↑ (s1 + s2) (asF 1 1) (asF s2 s1 k)
flip-comm s1 s2 k with k Nat.<? s2
... | yes lt =
    cong (asF s2 s1) (lift↑-lt (asF 1 1) (Nat.<-≤-trans lt (Nat.m≤n+m s2 s1)))
  ■ asF-lt s2 s1 lt
  ■ sym (lift↑-lt (asF 1 1) (Nat.+-monoʳ-< s1 lt))
  ■ sym (cong (lift↑ (s1 + s2) (asF 1 1)) (asF-lt s2 s1 lt))
... | no ¬lt with k Nat.<? (s2 + s1)
...   | yes lt2 = flip-mid s1 s2 k (Nat.≮⇒≥ ¬lt) lt2
...   | no ¬lt2 = flip-ge s1 s2 k (Nat.≮⇒≥ ¬lt2)

------------------------------------------------------------------------
-- Fin-level spec transfer.
------------------------------------------------------------------------

toℕ-subst𝔽 : ∀ {a b} (e : a ≡ b) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
toℕ-subst𝔽 refl y = refl

-- A renaming satisfies a ℕ-level spec when toℕ intertwines them.
Spec : ∀ {c d} → (c →ᵣ d) → (ℕ → ℕ) → Set
Spec ρ F = ∀ y → Fin.toℕ (ρ y) ≡ F (Fin.toℕ y)

spec-↑ : ∀ {c d} {ρ : c →ᵣ d} (F : ℕ → ℕ) → Spec ρ F → Spec (ρ ↑) (lift↑ 1 F)
spec-↑ F h 0F      = refl
spec-↑ F h (suc y) = cong suc (h y)

spec-↑* : ∀ {c d} {ρ : c →ᵣ d} (F : ℕ → ℕ) k → Spec ρ F → Spec (ρ ↑* k) (lift↑ k F)
spec-↑* F zero    h y = h y
spec-↑* F (suc k) h y =
  spec-↑ (lift↑ k F) (spec-↑* F k h) y ■ lift↑-+ 1 k F (Fin.toℕ y)

spec-·ᵣ : ∀ {c d e} {ρ₁ : c →ᵣ d} {ρ₂ : d →ᵣ e} (F₁ F₂ : ℕ → ℕ) →
          Spec ρ₁ F₁ → Spec ρ₂ F₂ → Spec (ρ₁ ·ₖ ρ₂) (λ k → F₂ (F₁ k))
spec-·ᵣ {ρ₁ = ρ₁} F₁ F₂ h₁ h₂ y = h₂ (ρ₁ y) ■ cong F₂ (h₁ y)

------------------------------------------------------------------------
-- Telescope cell counts.
------------------------------------------------------------------------

cntᵗ : ∀ {n k} → Tel n k → ℕ
cntᵗ []       = 0
cntᵗ (tν t)   = cntᵗ t + 2
cntᵗ (tφ _ t) = cntᵗ t + 1

spec-liftId : ∀ {c d} (t : Tel c d) (ρ : c →ᵣ c) (F : ℕ → ℕ) → Spec ρ F →
              Spec (liftId t ρ) (lift↑ (cntᵗ t) F)
spec-liftId []       ρ F h y = h y
spec-liftId (tν t)   ρ F h y =
  spec-liftId t (ρ ↑* 2) (lift↑ 2 F) (spec-↑* F 2 h) y ■ lift↑-+ (cntᵗ t) 2 F (Fin.toℕ y)
spec-liftId (tφ f t) ρ F h y =
  spec-liftId t (ρ ↑) (lift↑ 1 F) (spec-↑ F h) y ■ lift↑-+ (cntᵗ t) 1 F (Fin.toℕ y)

cntᵗ-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
           cntᵗ (t ++ᵗ s) ≡ cntᵗ t + cntᵗ s
cntᵗ-++ᵗ []       s = refl
cntᵗ-++ᵗ (tν t)   s =
    cong (_+ 2) (cntᵗ-++ᵗ t s)
  ■ solve 2 (λ x y → x :+ y :+ con 2 := x :+ con 2 :+ y) refl (cntᵗ t) (cntᵗ s)
cntᵗ-++ᵗ (tφ f t) s =
    cong (_+ 1) (cntᵗ-++ᵗ t s)
  ■ solve 2 (λ x y → x :+ y :+ con 1 := x :+ con 1 :+ y) refl (cntᵗ t) (cntᵗ s)

cntᵗ-shift1 : ∀ {n j} (s : Tel n j) → cntᵗ (shift1 s) ≡ cntᵗ s
cntᵗ-shift1 []       = refl
cntᵗ-shift1 (tν s)   = cong (_+ 2) (cntᵗ-shift1 s)
cntᵗ-shift1 (tφ f s) = cong (_+ 1) (cntᵗ-shift1 s)

cntᵗ-shift2 : ∀ {n j} (s : Tel n j) → cntᵗ (shift2 s) ≡ cntᵗ s
cntᵗ-shift2 []       = refl
cntᵗ-shift2 (tν s)   = cong (_+ 2) (cntᵗ-shift2 s)
cntᵗ-shift2 (tφ f s) = cong (_+ 1) (cntᵗ-shift2 s)

cntᵗ-subst : ∀ {n k k′} (e : k ≡ k′) (t : Tel n k) →
             cntᵗ (subst (Tel n) e t) ≡ cntᵗ t
cntᵗ-subst refl t = refl

cntᵗ-φTelᵣ : ∀ (B : BindGroup) (c : ℕ) → cntᵗ (φTelᵣ B c) ≡ syncs B
cntᵗ-φTelᵣ []              c = refl
cntᵗ-φTelᵣ (_ ∷ [])        c = refl
cntᵗ-φTelᵣ (b ∷ B@(_ ∷ _)) c =
  cong (_+ 1) (cntᵗ-φTelᵣ B (suc c)) ■ Nat.+-comm (syncs B) 1

cntᵗ-φTel : ∀ (B : BindGroup) (c : ℕ) → cntᵗ (φTel B c) ≡ syncs B
cntᵗ-φTel B c = cntᵗ-subst (scope≡ B c) (φTelᵣ B c) ■ cntᵗ-φTelᵣ B c

cntᵗ-nest : ∀ (B₁ B₂ : BindGroup) (c : ℕ) →
            cntᵗ (φTel B₁ c ++ᵗ φTel B₂ (syncs B₁ + c)) ≡ syncs B₁ + syncs B₂
cntᵗ-nest B₁ B₂ c =
    cntᵗ-++ᵗ (φTel B₁ c) (φTel B₂ (syncs B₁ + c))
  ■ cong₂ _+_ (cntᵗ-φTel B₁ c) (cntᵗ-φTel B₂ (syncs B₁ + c))

------------------------------------------------------------------------
-- Specs of the generator renamings.
------------------------------------------------------------------------

spec-assocSwap : ∀ a b {m} → Spec (assocSwapᵣ a b {m}) (asF a b)
spec-assocSwap a b x with Fin.toℕ x Nat.<? a
... | yes lt = toℕ-assoc-lt a b x lt ■ sym (asF-lt a b lt)
... | no ¬lt with Fin.toℕ x Nat.<? (a + b)
...   | yes lt2 = toℕ-assoc-mid a b x (Nat.≮⇒≥ ¬lt) lt2
                ■ sym (asF-mid a b (Nat.≮⇒≥ ¬lt) lt2)
...   | no ¬lt2 = toℕ-assoc-ge a b x (Nat.≮⇒≥ ¬lt2)
                ■ sym (asF-ge a b (Nat.≮⇒≥ ¬lt2))

spec-swapᵣ : ∀ a b {m} → Spec (swapᵣ a b {m}) (asF a b)
spec-swapᵣ a b x with Fin.toℕ x Nat.<? a
... | yes lt = toℕ-swapᵣ-lt a b x lt ■ sym (asF-lt a b lt)
... | no ¬lt with Fin.toℕ x Nat.<? (a + b)
...   | yes lt2 = toℕ-swapᵣ-mid a b x (Nat.≮⇒≥ ¬lt) lt2
                ■ sym (asF-mid a b (Nat.≮⇒≥ ¬lt) lt2)
...   | no ¬lt2 = toℕ-swapᵣ-ge a b x (Nat.≮⇒≥ ¬lt2)
                ■ sym (asF-ge a b (Nat.≮⇒≥ ¬lt2))

asF-b0 : ∀ a k → asF a 0 k ≡ k
asF-b0 a k with k Nat.<? a
... | yes lt  = asF-lt a 0 lt
... | no ¬lt  = asF-ge a 0
                  (subst (Nat._≤ k) (sym (Nat.+-identityʳ a)) (Nat.≮⇒≥ ¬lt))

------------------------------------------------------------------------
-- Specs of the Factor composites.
------------------------------------------------------------------------

spec-bubν⁻ : ∀ {n j} (s : Tel n j) → Spec (bubν⁻ s) (asF 2 (cntᵗ s))
spec-bubν⁻ []       y = sym (asF-b0 2 (Fin.toℕ y))
spec-bubν⁻ (tν s)   y =
    spec-·ᵣ (asF 2 (cntᵗ s)) (lift↑ (cntᵗ (shift2 s)) (asF 2 2))
            (spec-bubν⁻ s)
            (spec-liftId (shift2 s) (assocSwapᵣ 2 2) (asF 2 2) (spec-assocSwap 2 2)) y
  ■ cong (λ z → lift↑ z (asF 2 2) (asF 2 (cntᵗ s) (Fin.toℕ y))) (cntᵗ-shift2 s)
  ■ asF-stepgen 2 (cntᵗ s) 2 (Fin.toℕ y)
spec-bubν⁻ (tφ f s) y =
    spec-·ᵣ (asF 2 (cntᵗ s)) (lift↑ (cntᵗ (shift2 s)) (asF 2 1))
            (spec-bubν⁻ s)
            (spec-liftId (shift2 s) (assocSwapᵣ 2 1) (asF 2 1) (spec-assocSwap 2 1)) y
  ■ cong (λ z → lift↑ z (asF 2 1) (asF 2 (cntᵗ s) (Fin.toℕ y))) (cntᵗ-shift2 s)
  ■ asF-stepgen 2 (cntᵗ s) 1 (Fin.toℕ y)

spec-bubφ⁻ : ∀ {n j} (s : Tel n j) → Spec (bubφ⁻ s) (asF 1 (cntᵗ s))
spec-bubφ⁻ []       y = sym (asF-b0 1 (Fin.toℕ y))
spec-bubφ⁻ (tν s)   y =
    spec-·ᵣ (asF 1 (cntᵗ s)) (lift↑ (cntᵗ (shift1 s)) (asF 1 2))
            (spec-bubφ⁻ s)
            (spec-liftId (shift1 s) (assocSwapᵣ 1 2) (asF 1 2) (spec-assocSwap 1 2)) y
  ■ cong (λ z → lift↑ z (asF 1 2) (asF 1 (cntᵗ s) (Fin.toℕ y))) (cntᵗ-shift1 s)
  ■ asF-stepgen 1 (cntᵗ s) 2 (Fin.toℕ y)
spec-bubφ⁻ (tφ f s) y =
    spec-·ᵣ (asF 1 (cntᵗ s)) (lift↑ (cntᵗ (shift1 s)) (asF 1 1))
            (spec-bubφ⁻ s)
            (spec-liftId (shift1 s) (assocSwapᵣ 1 1) (asF 1 1) (spec-assocSwap 1 1)) y
  ■ cong (λ z → lift↑ z (asF 1 1) (asF 1 (cntᵗ s) (Fin.toℕ y))) (cntᵗ-shift1 s)
  ■ asF-stepgen 1 (cntᵗ s) 1 (Fin.toℕ y)

private
  dragfuseᵍ : ∀ tc rc c b k →
              lift↑ tc (asF rc c) (lift↑ (rc + tc) (asF b c) k)
                ≡ lift↑ tc (asF (rc + b) c) k
  dragfuseᵍ tc rc c b k =
      cong (lift↑ tc (asF rc c))
        ( cong (λ z → lift↑ z (asF b c) k) (Nat.+-comm rc tc)
        ■ sym (lift↑-+ tc rc (asF b c) k) )
    ■ lift↑-∘ tc (asF rc c) (lift↑ rc (asF b c)) k
    ■ lift↑-cong tc (λ z → drag-step0 rc c b z) k

spec-dragRen : ∀ {p j m k} (S : Tel p j) {r : Tel j m} (w : Run r) (t : Tel m k) →
               Spec (dragRen S w t) (lift↑ (cntᵗ t) (asF (cntᵗ r) (cntᵗ S)))
spec-dragRen S rnil t y =
  sym (lift↑-id (cntᵗ t) (λ k' → asF-0 (cntᵗ S) k') (Fin.toℕ y))
spec-dragRen S (rφ {f = f} {r = r} w) t y =
    spec-·ᵣ (lift↑ (cntᵗ (r ++ᵗ t)) (asF 1 (cntᵗ S)))
            (lift↑ (cntᵗ t) (asF (cntᵗ r) (cntᵗ (shift1 S))))
            (spec-liftId (r ++ᵗ t) (bubφ⁻ S) (asF 1 (cntᵗ S)) (spec-bubφ⁻ S))
            (spec-dragRen (shift1 S) w t) y
  ■ cong (λ z → lift↑ (cntᵗ t) (asF (cntᵗ r) z)
                  (lift↑ (cntᵗ (r ++ᵗ t)) (asF 1 (cntᵗ S)) (Fin.toℕ y)))
      (cntᵗ-shift1 S)
  ■ cong (λ z → lift↑ (cntᵗ t) (asF (cntᵗ r) (cntᵗ S))
                  (lift↑ z (asF 1 (cntᵗ S)) (Fin.toℕ y)))
      (cntᵗ-++ᵗ r t)
  ■ dragfuseᵍ (cntᵗ t) (cntᵗ r) (cntᵗ S) 1 (Fin.toℕ y)

spec-bswapRen : ∀ {n i m k} (a : Tel (2 + n) i) {rb : Tel (2 + i) m}
                (w : Run rb) (t : Tel m k) →
                Spec (bswapRen a w t)
                     (lift↑ (cntᵗ t) (asF (cntᵗ rb + 2) (cntᵗ a + 2)))
spec-bswapRen a {rb} w t y =
    spec-·ᵣ (lift↑ (cntᵗ (rb ++ᵗ t)) (asF 2 (cntᵗ a + 2)))
            (lift↑ (cntᵗ t) (asF (cntᵗ rb) (cntᵗ (shift2 a) + 2)))
            (spec-liftId (rb ++ᵗ t) (bubν⁻ (tν a)) (asF 2 (cntᵗ a + 2)) (spec-bubν⁻ (tν a)))
            (spec-dragRen (tν (shift2 a)) w t) y
  ■ cong (λ z → lift↑ (cntᵗ t) (asF (cntᵗ rb) (z + 2))
                  (lift↑ (cntᵗ (rb ++ᵗ t)) (asF 2 (cntᵗ a + 2)) (Fin.toℕ y)))
      (cntᵗ-shift2 a)
  ■ cong (λ z → lift↑ (cntᵗ t) (asF (cntᵗ rb) (cntᵗ a + 2))
                  (lift↑ z (asF 2 (cntᵗ a + 2)) (Fin.toℕ y)))
      (cntᵗ-++ᵗ rb t)
  ■ dragfuseᵍ (cntᵗ t) (cntᵗ rb) (cntᵗ a + 2) 2 (Fin.toℕ y)

------------------------------------------------------------------------
-- Cell count of an image block telescope: base-scope- and renaming-invariant.
------------------------------------------------------------------------

Bcnt : ∀ {a b} → TTel a b → ℕ
Bcnt []ᵗ           = 0
Bcnt (tνᵗ B₁ B₂ t) = ((syncs B₁ + syncs B₂) + Bcnt t) + 2

cntᵗ-BTel : ∀ {a b} (t : TTel a b) (n : ℕ) → cntᵗ (BTel t n) ≡ Bcnt t
cntᵗ-BTel []ᵗ           n = refl
cntᵗ-BTel (tνᵗ B₁ B₂ t) n =
  cong (_+ 2)
    ( cntᵗ-++ᵗ (φTel B₁ (2 + n) ++ᵗ φTel B₂ (syncs B₁ + (2 + n)))
               (BTel t (syncs B₂ + (syncs B₁ + (2 + n))))
    ■ cong₂ _+_ (cntᵗ-nest B₁ B₂ (2 + n))
                (cntᵗ-BTel t (syncs B₂ + (syncs B₁ + (2 + n)))) )

Bcnt-⋯ᵗᵉˡ : ∀ {a b m} (t : TTel a b) (χ : a →ᵣ m) → Bcnt (t ⋯ᵗᵉˡ χ) ≡ Bcnt t
Bcnt-⋯ᵗᵉˡ []ᵗ           χ = refl
Bcnt-⋯ᵗᵉˡ (tνᵗ B₁ B₂ t) χ =
  cong (_+ 2) (cong ((syncs B₁ + syncs B₂) +_)
    (Bcnt-⋯ᵗᵉˡ t (χ ↑* (sum B₁ + sum B₂))))

------------------------------------------------------------------------
-- toℕ-fixing of Φᵗ above the permuted prefix (port of the in-where
-- Φ-fix-ge of `subEqComm-gen`, against the module-level Φᵗ).
------------------------------------------------------------------------

Φᵗ-fixge : ∀ sA1 sA2 sB1 sB2 {n}
           (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))) →
           sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ x →
           Fin.toℕ (Φᵗ sA1 sA2 sB1 sB2 {n} x) ≡ Fin.toℕ x
Φᵗ-fixge sA1 sA2 sB1 sB2 {n} x ge = lΩ ■ x3N ■ x2N ■ x1N
  where
    ρacc = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
    Ωin = (assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))
    x1 = ((ρacc ↑* sA1) ↑* sA2) x
    x1N : Fin.toℕ x1 ≡ Fin.toℕ x
    x1N = lift-fix-ge (ρacc ↑* sA1) sA2 (sA1 + (2 + (sB2 + (sB1 + 2))))
            (λ w q → lift-fix-ge ρacc sA1 (2 + (sB2 + (sB1 + 2)))
                       (λ u q′ → ρacc-fix-ge sB1 sB2 u q′) w q) x ge
    x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
    x2N : Fin.toℕ x2 ≡ Fin.toℕ x1
    x2N = toℕ-assoc↑*-fix-ge sA2 sA1 sB2 x1
            (subst (sA2 + (sA1 + sB2) Nat.≤_) (sym x1N)
              (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1
                (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2))
                             (Nat.m≤n+m (sB2 + (sB1 + 2)) 2)))) ge))
    x3 = assocSwapᵣ sA2 sB2 x2
    x3N : Fin.toℕ x3 ≡ Fin.toℕ x2
    x3N = toℕ-assoc-ge sA2 sB2 x2
            (subst (sA2 + sB2 Nat.≤_) (sym (x2N ■ x1N))
              (Nat.≤-trans (Nat.+-monoʳ-≤ sA2
                (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2))
                  (Nat.≤-trans (Nat.m≤n+m (sB2 + (sB1 + 2)) 2)
                               (Nat.m≤n+m _ sA1)))) ge))
    lΩ : Fin.toℕ ((Ωin ↑* sB2) x3) ≡ Fin.toℕ x3
    lΩ = lift-fix-ge Ωin sB2 (sA2 + (sA1 + (sB1 + 2)))
           (λ w q → ρω-fix-ge sA1 sA2 sB1 w q) x3 geΩ
      where
        geΩ : sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤ Fin.toℕ x3
        geΩ = subst (sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤_)
                    (sym (x3N ■ x2N ■ x1N))
                (Nat.≤-trans (Nat.≤-reflexive reassoc) (Nat.≤-trans bump ge))
          where
            reassoc : sB2 + (sA2 + (sA1 + (sB1 + 2)))
                        ≡ sA2 + (sA1 + (sB2 + (sB1 + 2)))
            reassoc = solve 4 (λ w u v t →
                        w :+ (u :+ (v :+ (t :+ con 2)))
                        := u :+ (v :+ (w :+ (t :+ con 2)))) refl sB2 sA2 sA1 sB1
            bump : sA2 + (sA1 + (sB2 + (sB1 + 2)))
                     Nat.≤ sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
            bump = Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1
                     (Nat.m≤n+m (sB2 + (sB1 + 2)) 2))

------------------------------------------------------------------------
-- The bridges: Factor's composites match the Congruence composites.
------------------------------------------------------------------------

module Bridge (A₁ A₂ B₁ B₂ : BindGroup) {n₀ : ℕ} where
  private
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂

  n₁ᵇ : ℕ
  n₁ᵇ = sB2 + (sB1 + (2 + n₀))

  n₂ᵇ : ℕ
  n₂ᵇ = sA2 + (sA1 + (2 + n₁ᵇ))

  aᴮ : Tel (2 + n₀) n₁ᵇ
  aᴮ = φTel B₁ (2 + n₀) ++ᵗ φTel B₂ (sB1 + (2 + n₀))

  rᴬ : Tel (2 + n₁ᵇ) n₂ᵇ
  rᴬ = φTel A₁ (2 + n₁ᵇ) ++ᵗ φTel A₂ (sA1 + (2 + n₁ᵇ))

  eqΦ : sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n₀))))) ≡ n₂ᵇ
  eqΦ = solve 5 (λ a1 a2 b1 b2 nn →
          b2 :+ (b1 :+ (con 2 :+ (a2 :+ (a1 :+ (con 2 :+ nn)))))
          := a2 :+ (a1 :+ (con 2 :+ (b2 :+ (b1 :+ (con 2 :+ nn))))))
          refl sA1 sA2 sB1 sB2 n₀

  private
    cnt-rᴬ : cntᵗ rᴬ ≡ sA1 + sA2
    cnt-rᴬ = cntᵗ-nest A₁ A₂ (2 + n₁ᵇ)

    cnt-aᴮ : cntᵗ aᴮ ≡ sB1 + sB2
    cnt-aᴮ = cntᵗ-nest B₁ B₂ (2 + n₀)

    specᶠ : (w : Run rᴬ) (x : 𝔽 n₂ᵇ) →
            Fin.toℕ (bswapRen aᴮ w [] x)
              ≡ asF ((sA1 + sA2) + 2) ((sB1 + sB2) + 2) (Fin.toℕ x)
    specᶠ w x =
        spec-bswapRen aᴮ w [] x
      ■ cong₂ (λ u v → asF (u + 2) (v + 2) (Fin.toℕ x)) cnt-rᴬ cnt-aᴮ

  bridge-fwd : (w : Run rᴬ) (x : 𝔽 n₂ᵇ) →
               bswapRen aᴮ w [] x ≡ subst 𝔽 eqΦ (Φᵗ sA1 sA2 sB1 sB2 {n₀} x)
  bridge-fwd w x =
    Fin.toℕ-injective (specᶠ w x ■ match ■ sym (toℕ-subst𝔽 eqΦ _))
    where
      kx = Fin.toℕ x
      WA = sA1 + sA2
      WB = sB1 + sB2
      eShift : WB + 2 ≡ sB2 + (sB1 + 2)
      eShift = solve 2 (λ b1 b2 → b1 :+ b2 :+ con 2 := b2 :+ (b1 :+ con 2))
                 refl sB1 sB2
      eA2 : sA2 + sA1 + 2 ≡ WA + 2
      eA2 = solve 2 (λ a1 a2 → a2 :+ a1 :+ con 2 := a1 :+ a2 :+ con 2)
              refl sA1 sA2
      eA3 : WA + 2 ≡ sA2 + (sA1 + 2)
      eA3 = solve 2 (λ a1 a2 → a1 :+ a2 :+ con 2 := a2 :+ (a1 :+ con 2))
              refl sA1 sA2
      eB2 : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) ≡ (WA + 2) + (WB + 2)
      eB2 = solve 4 (λ a1 a2 b1 b2 →
              a2 :+ (a1 :+ (con 2 :+ (b2 :+ (b1 :+ con 2))))
              := (a1 :+ a2 :+ con 2) :+ (b1 :+ b2 :+ con 2))
              refl sA1 sA2 sB1 sB2
      match : asF (WA + 2) (WB + 2) kx ≡ Fin.toℕ (Φᵗ sA1 sA2 sB1 sB2 {n₀} x)
      match with kx Nat.<? (sA2 + sA1)
      ... | yes ltA =
            asF-lt (WA + 2) (WB + 2)
              (Nat.<-≤-trans ltA
                (Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm sA2 sA1))
                             (Nat.m≤m+n WA 2)))
          ■ cong (_+ kx) eShift
          ■ sym (Φᵗ-A sA1 sA2 sB1 sB2 x ltA)
      ... | no ¬ltA with kx Nat.<? (sA2 + sA1 + 2)
      ...   | yes ltAd =
              asF-lt (WA + 2) (WB + 2) (subst (kx Nat.<_) eA2 ltAd)
            ■ cong (_+ kx) eShift
            ■ sym (Φᵗ-Adata sA1 sA2 sB1 sB2 x (Nat.≮⇒≥ ¬ltA) ltAd)
      ...   | no ¬ltAd with kx Nat.<? (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))))
      ...     | yes ltB =
                asF-mid (WA + 2) (WB + 2)
                  (subst (Nat._≤ kx) eA2 (Nat.≮⇒≥ ¬ltAd))
                  (subst (kx Nat.<_) eB2 ltB)
              ■ cong (kx Nat.∸_) eA3
              ■ sym (Φᵗ-B sA1 sA2 sB1 sB2 x
                  (subst (Nat._≤ kx) (eA2 ■ eA3) (Nat.≮⇒≥ ¬ltAd)) ltB)
      ...     | no ¬ltB =
                asF-ge (WA + 2) (WB + 2)
                  (subst (Nat._≤ kx) eB2 (Nat.≮⇒≥ ¬ltB))
              ■ sym (Φᵗ-fixge sA1 sA2 sB1 sB2 x (Nat.≮⇒≥ ¬ltB))

module BridgeFlip (B₁ B₂ : BindGroup) {n₀ : ℕ} where
  private
    sB1 = syncs B₁ ; sB2 = syncs B₂

  n₁ᵇ : ℕ
  n₁ᵇ = sB2 + (sB1 + (2 + n₀))

  nestᴮ : Tel (2 + n₀) n₁ᵇ
  nestᴮ = φTel B₁ (2 + n₀) ++ᵗ φTel B₂ (sB1 + (2 + n₀))

  eqΨ : sB1 + (sB2 + (2 + n₀)) ≡ n₁ᵇ
  eqΨ = solve 3 (λ b1 b2 nn → b1 :+ (b2 :+ nn) := b2 :+ (b1 :+ nn))
          refl sB1 sB2 (2 + n₀)

  bridge-flip : (w : Run (φTel B₂ (sB1 + (2 + n₀)))) (x : 𝔽 n₁ᵇ) →
                (liftId nestᴮ (swapᵣ 1 1) ·ₖ dragRen (φTel B₁ (2 + n₀)) w []) x
                  ≡ subst 𝔽 eqΨ
                      ((assocSwapᵣ sB2 sB1 ·ₖ ((swapᵣ 1 1 ↑* sB2) ↑* sB1)) x)
  bridge-flip w x =
    Fin.toℕ-injective
      (mine ■ flip-comm sB1 sB2 (Fin.toℕ x) ■ sym theirs ■ sym (toℕ-subst𝔽 eqΨ _))
    where
      cnt-nestᴮ : cntᵗ nestᴮ ≡ sB1 + sB2
      cnt-nestᴮ = cntᵗ-nest B₁ B₂ (2 + n₀)
      mine : Fin.toℕ ((liftId nestᴮ (swapᵣ 1 1) ·ₖ dragRen (φTel B₁ (2 + n₀)) w []) x)
               ≡ asF sB2 sB1 (lift↑ (sB1 + sB2) (asF 1 1) (Fin.toℕ x))
      mine =
          spec-·ᵣ (lift↑ (cntᵗ nestᴮ) (asF 1 1))
                  (lift↑ 0 (asF (cntᵗ (φTel B₂ (sB1 + (2 + n₀))))
                               (cntᵗ (φTel B₁ (2 + n₀)))))
                  (spec-liftId nestᴮ (swapᵣ 1 1) (asF 1 1) (spec-swapᵣ 1 1))
                  (spec-dragRen (φTel B₁ (2 + n₀)) w []) x
        ■ cong₂ (λ u v → asF u v (lift↑ (cntᵗ nestᴮ) (asF 1 1) (Fin.toℕ x)))
            (cntᵗ-φTel B₂ (sB1 + (2 + n₀))) (cntᵗ-φTel B₁ (2 + n₀))
        ■ cong (λ z → asF sB2 sB1 (lift↑ z (asF 1 1) (Fin.toℕ x))) cnt-nestᴮ
      theirs : Fin.toℕ ((assocSwapᵣ sB2 sB1 ·ₖ ((swapᵣ 1 1 ↑* sB2) ↑* sB1)) x)
                 ≡ lift↑ (sB1 + sB2) (asF 1 1) (asF sB2 sB1 (Fin.toℕ x))
      theirs =
          spec-·ᵣ (asF sB2 sB1) (lift↑ sB1 (lift↑ sB2 (asF 1 1)))
                  (spec-assocSwap sB2 sB1)
                  (spec-↑* (lift↑ sB2 (asF 1 1)) sB1
                    (spec-↑* (asF 1 1) sB2 (spec-swapᵣ 1 1))) x
        ■ lift↑-+ sB1 sB2 (asF 1 1) (asF sB2 sB1 (Fin.toℕ x))
