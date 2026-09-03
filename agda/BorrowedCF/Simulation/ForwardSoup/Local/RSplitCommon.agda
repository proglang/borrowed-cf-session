-- | Phase 3 shared material for the `R-RSplit` leaf (`ForwardSoup/PLAN.md`,
--   §6.4, option 1).  It is the `rwk` counterpart of the `lwk` half of
--   `Local/SplitCommon.agda`, with `insertPhi` threaded through everywhere:
--
--     * the flag-list shape of the two binder groups (`prefixFlags`,
--       `bindFlags-rsplit-src`, `bindFlags-rsplit-tgt`), which is what tells
--       `RUS-RSplit` where the new sync boundary goes;
--     * the numeric faces of `SplitRenamings.rwk` and `SplitRenamings.inj`
--       (`rwk-toℕ-lo`/`-hi`/`-≤`, `injAt`, `inj-injAt`);
--     * the environment agreement `UBFrom-rwk` / `source-target-rwk`: away
--       from the consumed handle the reduct's environment is the redex's with
--       one φ-boundary inserted at slot `length B₁`;
--     * the three handle triples `group-rsplit-shape`.
module BorrowedCF.Simulation.ForwardSoup.Local.RSplitCommon where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.Solver using (module +-*-Solver)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalEndpoint)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (UB-phiFree-init)
open import BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport
  using (physicalEndpoint-distinct)
open import BorrowedCF.Simulation.ForwardSoup.Local.InsertSupport
  using ( insertPhi-below; insertPhi-above; Ub-insertPhi; UBFrom-insertPhi
        ; consumePhi-fixed⇒insertPhi-fixed
        )
open import BorrowedCF.Simulation.ForwardSoup.Local.SplitCommon
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ)
open import BorrowedCF.Simulation.Support.BlockPerm
  using (toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt)

open SoupReduction using (insertPhi)

open +-*-Solver using (solve; _:=_; _:+_; con)

open Nat.Variables
open Fin.Patterns

private
  variable d : ℕ

------------------------------------------------------------------------
-- Small arithmetic facts.  `∸-pos`, `∸-bound`, `∸-suc` and `q<q+suc` come
-- from `Local/SplitCommon.agda`.

private
  ∸-shift : ∀ (q b u : ℕ) → q Nat.≤ u → (q + b) Nat.∸ u ≡ b Nat.∸ (u Nat.∸ q)
  ∸-shift q b u le =
    cong ((q + b) Nat.∸_) (sym (Nat.m+[n∸m]≡n le))
    ■ sym (Nat.∸-+-assoc (q + b) q (u Nat.∸ q))
    ■ cong (Nat._∸ (u Nat.∸ q)) (Nat.m+n∸m≡n q b)

  ∸-split : ∀ (a b u : ℕ) → a + b Nat.≤ u → u Nat.∸ a ≡ b + (u Nat.∸ (a + b))
  ∸-split a b u le =
    sym (cong (b +_) (sym (Nat.∸-+-assoc u a b)) ■ Nat.m+[n∸m]≡n b≤)
    where
    b≤ : b Nat.≤ u Nat.∸ a
    b≤ = subst (Nat._≤ u Nat.∸ a) (Nat.m+n∸m≡n a b) (Nat.∸-monoˡ-≤ a le)

  q+1 : ∀ (q : ℕ) → q + 1 ≡ suc q
  q+1 q = Nat.+-comm q 1

  ↑ʳ0ℕ : ∀ (q : ℕ) {w : ℕ} → Fin.toℕ (q ↑ʳ (Fin.zero {w})) ≡ q
  ↑ʳ0ℕ q {w} = Fin.toℕ-↑ʳ q (Fin.zero {w}) ■ Nat.+-identityʳ q

------------------------------------------------------------------------
-- Flag lists.  The reduct's binder group has one extra `drop` boundary,
-- inserted at position `length B₁`.

prefixFlags : Typed.BindGroup → List Soup.Flag
prefixFlags [] = []
prefixFlags (b ∷ B) = Translation.ϕ[ b ] ∷ prefixFlags B

prefixFlags-length :
  (B : Typed.BindGroup) → L.length (prefixFlags B) ≡ L.length B
prefixFlags-length [] = refl
prefixFlags-length (b ∷ B) = cong suc (prefixFlags-length B)

bindFlags-split :
  ∀ (B₁ : Typed.BindGroup) (w : ℕ) (B₂ : Typed.BindGroup) →
  bindFlags (B₁ ++ w ∷ B₂) ≡ prefixFlags B₁ L.++ bindFlags (w ∷ B₂)
bindFlags-split [] w B₂ = refl
bindFlags-split (b ∷ []) w B₂ =
  cong (Translation.ϕ[ b ] ∷_) (bindFlags-split [] w B₂)
bindFlags-split (b ∷ b′ ∷ B₁) w B₂ =
  cong (Translation.ϕ[ b ] ∷_) (bindFlags-split (b′ ∷ B₁) w B₂)

private
  flagPos : ∀ (q b : ℕ) → Translation.ϕ[ q + suc b ] ≡ Soup.drop
  flagPos zero b = refl
  flagPos (suc q) b = refl

  bindFlags-head :
    ∀ (q b : ℕ) (B₂ : Typed.BindGroup) →
    bindFlags ((q + 1) ∷ suc b ∷ B₂) ≡ Soup.drop ∷ bindFlags ((q + suc b) ∷ B₂)
  bindFlags-head q b [] = cong (λ z → z ∷ []) (flagPos q 0)
  bindFlags-head q b (b₂ ∷ B₂) =
    cong₂ (λ u v → u ∷ v ∷ bindFlags (b₂ ∷ B₂))
      (flagPos q 0) (sym (flagPos q b))

bindFlags-rsplit-src :
  ∀ (B₁ B₂ : Typed.BindGroup) (q b : ℕ) →
  bindFlags (B₁ ++ (q + suc b) ∷ B₂) ≡
  prefixFlags B₁ L.++ bindFlags ((q + suc b) ∷ B₂)
bindFlags-rsplit-src B₁ B₂ q b = bindFlags-split B₁ (q + suc b) B₂

bindFlags-rsplit-tgt :
  ∀ (B₁ B₂ : Typed.BindGroup) (q b : ℕ) →
  bindFlags (B₁ ++ (q + 1) ∷ suc b ∷ B₂) ≡
  prefixFlags B₁ L.++ Soup.drop ∷ bindFlags ((q + suc b) ∷ B₂)
bindFlags-rsplit-tgt B₁ B₂ q b =
  bindFlags-split B₁ (q + 1) (suc b ∷ B₂)
  ■ cong (prefixFlags B₁ L.++_) (bindFlags-head q b B₂)

------------------------------------------------------------------------
-- `pick` commutes with `insertPhi`.

pick-insertPhi :
  (x : 𝔽 d) (s j : ℕ) (e : SoupTerm.Tm d) →
  insertPhi x s (pick j e) ≡ pick j (insertPhi x s e)
pick-insertPhi x s zero e = refl
pick-insertPhi x s (suc j) e = refl

------------------------------------------------------------------------
-- The entry of a block at the split position.

ub-split-entry :
  ∀ (w q b : ℕ) (c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d) (p : 𝔽 w) →
  w ≡ q + suc b → Fin.toℕ p ≡ q →
  Translation.Ub[ w ] (e₁ , c , e₂) p ≡
  Translation.chanTriple (pick q e₁ , c , pick b e₂)
ub-split-entry w q b c e₁ e₂ p wEq pEq =
  Ub-entry w c e₁ e₂ p
  ■ cong₂ (λ u v → Translation.chanTriple (pick u e₁ , c , pick v e₂))
      pEq
      ( cong₂ Nat._∸_ (wEq ■ Nat.+-suc q b) (cong suc pEq)
      ■ Nat.m+n∸m≡n q b )

------------------------------------------------------------------------
-- The two block comparisons of the split.

private
  block-lo :
    ∀ (W₁ W₂ q b s : ℕ) (x c : 𝔽 d) (e₁ e₂ t : SoupTerm.Tm d)
      (w : 𝔽 W₁) (w′ : 𝔽 W₂) →
    W₁ ≡ q + suc b → W₂ ≡ q + 1 →
    Fin.toℕ w Nat.< q → Fin.toℕ w′ ≡ Fin.toℕ w →
    insertPhi x s (Translation.Ub[ W₁ ] (e₁ , c , e₂) w) ≡
    Translation.Ub[ W₂ ] (insertPhi x s e₁ , c , t) w′
  block-lo W₁ W₂ q b s x c e₁ e₂ t w w′ w₁Eq w₂Eq lt w′ℕ =
    cong (insertPhi x s) (Ub-entry W₁ c e₁ e₂ w)
    ■ cong
        (λ z →
          Translation.chanTriple
            (insertPhi x s (pick (Fin.toℕ w) e₁) , c , insertPhi x s z))
        srcTail
    ■ cong (λ z → Translation.chanTriple (z , c , SoupTerm.*))
        ( pick-insertPhi x s (Fin.toℕ w) e₁
        ■ cong (λ u → pick u (insertPhi x s e₁)) (sym w′ℕ) )
    ■ cong
        (λ z →
          Translation.chanTriple
            (pick (Fin.toℕ w′) (insertPhi x s e₁) , c , z))
        (sym tgtTail)
    ■ sym (Ub-entry W₂ c (insertPhi x s e₁) t w′)
    where
    srcTail : pick (W₁ Nat.∸ suc (Fin.toℕ w)) e₂ ≡ SoupTerm.*
    srcTail =
      pick-pos (W₁ Nat.∸ suc (Fin.toℕ w)) e₂
        (∸-pos
          (subst (suc (Fin.toℕ w) Nat.<_) (sym w₁Eq)
            (Nat.≤-<-trans lt (q<q+suc q b))))

    tgtTail : pick (W₂ Nat.∸ suc (Fin.toℕ w′)) t ≡ SoupTerm.*
    tgtTail =
      pick-pos (W₂ Nat.∸ suc (Fin.toℕ w′)) t
        (∸-pos
          (subst (λ z → suc z Nat.< W₂) (sym w′ℕ)
            (subst (suc (Fin.toℕ w) Nat.<_) (sym w₂Eq)
              (Nat.≤-<-trans lt
                (subst (q Nat.<_) (sym (q+1 q)) (Nat.n<1+n q))))))

  block-hi :
    ∀ (W₁ W₂ q b s : ℕ) (x c : 𝔽 d) (e₁ e₂ t : SoupTerm.Tm d)
      (w : 𝔽 W₁) (w′ : 𝔽 W₂) →
    W₁ ≡ q + suc b → W₂ ≡ suc b →
    q Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ Fin.toℕ w Nat.∸ q →
    insertPhi x s (Translation.Ub[ W₁ ] (e₁ , c , e₂) w) ≡
    Translation.Ub[ W₂ ] (t , c , insertPhi x s e₂) w′
  block-hi W₁ W₂ q b s x c e₁ e₂ t w w′ w₁Eq w₂Eq gt w′ℕ =
    cong (insertPhi x s) (Ub-entry W₁ c e₁ e₂ w)
    ■ cong
        (λ z →
          Translation.chanTriple
            ( insertPhi x s z
            , c
            , insertPhi x s (pick (W₁ Nat.∸ suc (Fin.toℕ w)) e₂) ))
        srcHead
    ■ cong (λ z → Translation.chanTriple (SoupTerm.* , c , z))
        ( pick-insertPhi x s (W₁ Nat.∸ suc (Fin.toℕ w)) e₂
        ■ cong (λ u → pick u (insertPhi x s e₂)) tailEq )
    ■ cong
        (λ z →
          Translation.chanTriple
            (z , c , pick (W₂ Nat.∸ suc (Fin.toℕ w′)) (insertPhi x s e₂)))
        (sym tgtHead)
    ■ sym (Ub-entry W₂ c t (insertPhi x s e₂) w′)
    where
    srcHead : pick (Fin.toℕ w) e₁ ≡ SoupTerm.*
    srcHead = pick-pos (Fin.toℕ w) e₁ (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)

    tgtHead : pick (Fin.toℕ w′) t ≡ SoupTerm.*
    tgtHead =
      pick-pos (Fin.toℕ w′) t
        (subst (0 Nat.<_) (sym w′ℕ) (∸-pos gt))

    tailEq : W₁ Nat.∸ suc (Fin.toℕ w) ≡ W₂ Nat.∸ suc (Fin.toℕ w′)
    tailEq =
      cong (Nat._∸ suc (Fin.toℕ w)) (w₁Eq ■ Nat.+-suc q b)
      ■ ∸-shift q b (Fin.toℕ w) (Nat.<⇒≤ gt)
      ■ sym (cong₂ Nat._∸_ w₂Eq (cong suc w′ℕ))

------------------------------------------------------------------------
-- Peeling one leading block off both sides of the insertion statement.

private
  cons-step-ins :
    ∀ (l s b₀ b′ : ℕ) (B : Typed.BindGroup) (b″ : ℕ) (B′ : Typed.BindGroup)
      (t : ℕ) (x c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
      (w : 𝔽 (sum (b₀ ∷ b′ ∷ B))) (w′ : 𝔽 (sum (b₀ ∷ b″ ∷ B′))) →
    l Nat.< s →
    ( (p : 𝔽 (sum (b′ ∷ B))) (p′ : 𝔽 (sum (b″ ∷ B′))) →
      Fin.toℕ p ≢ t →
      (Fin.toℕ p Nat.< t → Fin.toℕ p′ ≡ Fin.toℕ p) →
      (t Nat.< Fin.toℕ p → Fin.toℕ p′ ≡ suc (Fin.toℕ p)) →
      insertPhi x s
        (proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) x
                 (SoupTerm.`phi (x , l) , c , e₂)) p) ≡
      proj₁ (Translation.UBFrom (suc l) (b″ ∷ B′) x
              (SoupTerm.`phi (x , l) , c , insertPhi x s e₂)) p′ ) →
    Fin.toℕ w ≢ b₀ + t →
    (Fin.toℕ w Nat.< b₀ + t → Fin.toℕ w′ ≡ Fin.toℕ w) →
    (b₀ + t Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
    insertPhi x s (proj₁ (Translation.UBFrom l (b₀ ∷ b′ ∷ B) x (e₁ , c , e₂)) w) ≡
    proj₁ (Translation.UBFrom l (b₀ ∷ b″ ∷ B′) x
            (insertPhi x s e₁ , c , insertPhi x s e₂)) w′
  cons-step-ins l s b₀ b′ B b″ B′ t x c e₁ e₂ w w′ l<s rec notEq lo hi
    with Fin.toℕ w Nat.<? b₀
  ... | yes lt =
    cong (insertPhi x s)
      (UBFrom-cons-lo l b₀ b′ B x c e₁ e₂ w p (sym (Fin.toℕ-fromℕ< lt)))
    ■ Ub-insertPhi b₀ x s e₁ (SoupTerm.`phi (x , l)) c p
    ■ cong
        (λ z → Translation.Ub[ b₀ ] (insertPhi x s e₁ , c , z) p)
        (insertPhi-below x s l l<s)
    ■ sym
        (UBFrom-cons-lo l b₀ b″ B′ x c (insertPhi x s e₁) (insertPhi x s e₂)
          w′ p
          (lo (Nat.<-≤-trans lt (Nat.m≤m+n b₀ t)) ■ sym (Fin.toℕ-fromℕ< lt)))
    where
    p : 𝔽 b₀
    p = Fin.fromℕ< lt
  ... | no ¬lt =
    cong (insertPhi x s)
      (UBFrom-cons-hi l b₀ b′ B x c e₁ e₂ w p wSplit)
    ■ rec p p′ notEq′ lo′ hi′
    ■ sym
        (UBFrom-cons-hi l b₀ b″ B′ x c (insertPhi x s e₁) (insertPhi x s e₂)
          w′ p′ w′Split)
    where
    ge : b₀ Nat.≤ Fin.toℕ w
    ge = Nat.≮⇒≥ ¬lt

    shift≥ : Fin.toℕ w Nat.≤ Fin.toℕ w′
    shift≥ with Fin.toℕ w Nat.<? b₀ + t
    ... | yes lt = Nat.≤-reflexive (sym (lo lt))
    ... | no ¬lt′ =
      Nat.≤-trans (Nat.n≤1+n _)
        (Nat.≤-reflexive
          (sym (hi (Nat.≤∧≢⇒< (Nat.≮⇒≥ ¬lt′) (notEq ∘ sym)))))

    ge′ : b₀ Nat.≤ Fin.toℕ w′
    ge′ = Nat.≤-trans ge shift≥

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
-- The environment of the reduct is the environment of the redex with one
-- φ-boundary inserted at slot `length B₁ + l`.

UBFrom-rwk :
  ∀ (l s : ℕ) (B₁ B₂ : Typed.BindGroup) (q b : ℕ) (x c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d)
    (w : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)))
    (w′ : 𝔽 (sum (B₁ ++ (q + 1) ∷ suc b ∷ B₂))) →
  s ≡ L.length B₁ + l →
  Fin.toℕ w ≢ sum B₁ + q →
  (Fin.toℕ w Nat.< sum B₁ + q → Fin.toℕ w′ ≡ Fin.toℕ w) →
  (sum B₁ + q Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
  insertPhi x s
    (proj₁ (Translation.UBFrom l (B₁ ++ (q + suc b) ∷ B₂) x (e₁ , c , e₂)) w) ≡
  proj₁ (Translation.UBFrom l (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x
          (insertPhi x s e₁ , c , insertPhi x s e₂)) w′

------------------------------------------------------------------------
-- Base case, last block.

UBFrom-rwk l s [] [] q b x c e₁ e₂ w w′ slotEq notEq lo hi
  with Fin.toℕ w Nat.<? q
... | yes lt =
  block-lo ((q + suc b) + 0) (q + 1) q b s x c e₁ e₂
    (SoupTerm.`phi (x , l)) w p′
    (Nat.+-identityʳ (q + suc b)) refl lt (p′ℕ ■ lo lt)
  ■ sym
      (UBFrom-cons-lo l (q + 1) (suc b) [] x c
        (insertPhi x s e₁) (insertPhi x s e₂) w′ p′ (sym p′ℕ))
  where
  bound : Fin.toℕ w′ Nat.< q + 1
  bound =
    subst (Nat._< q + 1) (sym (lo lt))
      (subst (Fin.toℕ w Nat.<_) (sym (q+1 q))
        (Nat.<-trans lt (Nat.n<1+n q)))

  p′ : 𝔽 (q + 1)
  p′ = Fin.fromℕ< bound

  p′ℕ : Fin.toℕ p′ ≡ Fin.toℕ w′
  p′ℕ = Fin.toℕ-fromℕ< bound

... | no ¬lt =
  block-hi ((q + suc b) + 0) (suc b + 0) q b s x c e₁ e₂
    (SoupTerm.`phi (x , l)) w p′
    (Nat.+-identityʳ (q + suc b)) (Nat.+-identityʳ (suc b)) gt p′ℕ′
  ■ sym
      (UBFrom-cons-hi l (q + 1) (suc b) [] x c
        (insertPhi x s e₁) (insertPhi x s e₂) w′ p′ split′)
  where
  gt : q Nat.< Fin.toℕ w
  gt = Nat.≤∧≢⇒< (Nat.≮⇒≥ ¬lt) (notEq ∘ sym)

  w′ℕ : Fin.toℕ w′ ≡ suc (Fin.toℕ w)
  w′ℕ = hi gt

  ge : q + 1 Nat.≤ Fin.toℕ w′
  ge =
    subst (Nat._≤ Fin.toℕ w′) (sym (q+1 q))
      (subst (suc q Nat.≤_) (sym w′ℕ) (Nat.s≤s (Nat.<⇒≤ gt)))

  p′ : 𝔽 (suc b + 0)
  p′ = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p′ℕ : Fin.toℕ p′ ≡ Fin.toℕ w′ Nat.∸ (q + 1)
  p′ℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p′ℕ′ : Fin.toℕ p′ ≡ Fin.toℕ w Nat.∸ q
  p′ℕ′ = p′ℕ ■ cong₂ Nat._∸_ w′ℕ (q+1 q)

  split′ : Fin.toℕ w′ ≡ (q + 1) + Fin.toℕ p′
  split′ = sym (cong ((q + 1) +_) p′ℕ ■ Nat.m+[n∸m]≡n ge)

------------------------------------------------------------------------
-- Base case, interior block.

UBFrom-rwk l s [] (b₂ ∷ B₂) q b x c e₁ e₂ w w′ slotEq notEq lo hi
  with Fin.toℕ w Nat.<? q + suc b
... | no ¬ltBlock =
  cong (insertPhi x s)
    (UBFrom-cons-hi l (q + suc b) b₂ B₂ x c e₁ e₂ w p wSplit)
  ■ UBFrom-insertPhi s (suc l) (Nat.≤-trans s≤l (Nat.n≤1+n l))
      (b₂ ∷ B₂) x c (SoupTerm.`phi (x , l)) e₂ p
  ■ cong
      (λ z →
        proj₁ (Translation.UBFrom (suc (suc l)) (b₂ ∷ B₂) x
                (z , c , insertPhi x s e₂)) p)
      (insertPhi-above x s l s≤l)
  ■ sym
      (UBFrom-cons-hi (suc l) (suc b) b₂ B₂ x c
        (SoupTerm.`phi (x , l)) (insertPhi x s e₂) p₂ p tailSplit)
  ■ sym
      (UBFrom-cons-hi l (q + 1) (suc b) (b₂ ∷ B₂) x c
        (insertPhi x s e₁) (insertPhi x s e₂) w′ p₂ split₂)
  where
  s≤l : s Nat.≤ l
  s≤l = Nat.≤-reflexive slotEq

  geBlock : q + suc b Nat.≤ Fin.toℕ w
  geBlock = Nat.≮⇒≥ ¬ltBlock

  gt : q Nat.< Fin.toℕ w
  gt = Nat.<-≤-trans (q<q+suc q b) geBlock

  w′ℕ : Fin.toℕ w′ ≡ suc (Fin.toℕ w)
  w′ℕ = hi gt

  p : 𝔽 (sum (b₂ ∷ B₂))
  p = Fin.fromℕ< (∸-bound geBlock (Fin.toℕ<n w))

  pℕ : Fin.toℕ p ≡ Fin.toℕ w Nat.∸ (q + suc b)
  pℕ = Fin.toℕ-fromℕ< (∸-bound geBlock (Fin.toℕ<n w))

  wSplit : Fin.toℕ w ≡ (q + suc b) + Fin.toℕ p
  wSplit = sym (cong ((q + suc b) +_) pℕ ■ Nat.m+[n∸m]≡n geBlock)

  ge : q + 1 Nat.≤ Fin.toℕ w′
  ge =
    subst (Nat._≤ Fin.toℕ w′) (sym (q+1 q))
      (subst (suc q Nat.≤_) (sym w′ℕ) (Nat.s≤s (Nat.<⇒≤ gt)))

  p₂ : 𝔽 (sum (suc b ∷ b₂ ∷ B₂))
  p₂ = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p₂ℕ : Fin.toℕ p₂ ≡ Fin.toℕ w′ Nat.∸ (q + 1)
  p₂ℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p₂ℕ′ : Fin.toℕ p₂ ≡ Fin.toℕ w Nat.∸ q
  p₂ℕ′ = p₂ℕ ■ cong₂ Nat._∸_ w′ℕ (q+1 q)

  split₂ : Fin.toℕ w′ ≡ (q + 1) + Fin.toℕ p₂
  split₂ = sym (cong ((q + 1) +_) p₂ℕ ■ Nat.m+[n∸m]≡n ge)

  tailSplit : Fin.toℕ p₂ ≡ suc b + Fin.toℕ p
  tailSplit =
    p₂ℕ′
    ■ ∸-split q (suc b) (Fin.toℕ w) geBlock
    ■ cong (suc b +_) (sym pℕ)

... | yes ltBlock with Fin.toℕ w Nat.<? q
...   | yes lt =
  cong (insertPhi x s)
    (UBFrom-cons-lo l (q + suc b) b₂ B₂ x c e₁ e₂ w p (sym pℕ))
  ■ block-lo (q + suc b) (q + 1) q b s x c e₁ (SoupTerm.`phi (x , l))
      (SoupTerm.`phi (x , l)) p p′ refl refl
      (subst (Nat._< q) (sym pℕ) lt) (p′ℕ ■ lo lt ■ sym pℕ)
  ■ sym
      (UBFrom-cons-lo l (q + 1) (suc b) (b₂ ∷ B₂) x c
        (insertPhi x s e₁) (insertPhi x s e₂) w′ p′ (sym p′ℕ))
  where
  p : 𝔽 (q + suc b)
  p = Fin.fromℕ< ltBlock

  pℕ : Fin.toℕ p ≡ Fin.toℕ w
  pℕ = Fin.toℕ-fromℕ< ltBlock

  bound : Fin.toℕ w′ Nat.< q + 1
  bound =
    subst (Nat._< q + 1) (sym (lo lt))
      (subst (Fin.toℕ w Nat.<_) (sym (q+1 q))
        (Nat.<-trans lt (Nat.n<1+n q)))

  p′ : 𝔽 (q + 1)
  p′ = Fin.fromℕ< bound

  p′ℕ : Fin.toℕ p′ ≡ Fin.toℕ w′
  p′ℕ = Fin.toℕ-fromℕ< bound

...   | no ¬lt =
  cong (insertPhi x s)
    (UBFrom-cons-lo l (q + suc b) b₂ B₂ x c e₁ e₂ w p (sym pℕ))
  ■ block-hi (q + suc b) (suc b) q b s x c e₁ (SoupTerm.`phi (x , l))
      (SoupTerm.`phi (x , l)) p p₃ refl refl
      (subst (q Nat.<_) (sym pℕ) gt)
      (p₃ℕ ■ cong (Nat._∸ q) (sym pℕ))
  ■ cong
      (λ z → Translation.Ub[ suc b ] (SoupTerm.`phi (x , l) , c , z) p₃)
      (insertPhi-above x s l s≤l)
  ■ sym
      (UBFrom-cons-lo (suc l) (suc b) b₂ B₂ x c
        (SoupTerm.`phi (x , l)) (insertPhi x s e₂) p₂ p₃ p₃ℕ₂)
  ■ sym
      (UBFrom-cons-hi l (q + 1) (suc b) (b₂ ∷ B₂) x c
        (insertPhi x s e₁) (insertPhi x s e₂) w′ p₂ split₂)
  where
  s≤l : s Nat.≤ l
  s≤l = Nat.≤-reflexive slotEq

  gt : q Nat.< Fin.toℕ w
  gt = Nat.≤∧≢⇒< (Nat.≮⇒≥ ¬lt) (notEq ∘ sym)

  w′ℕ : Fin.toℕ w′ ≡ suc (Fin.toℕ w)
  w′ℕ = hi gt

  p : 𝔽 (q + suc b)
  p = Fin.fromℕ< ltBlock

  pℕ : Fin.toℕ p ≡ Fin.toℕ w
  pℕ = Fin.toℕ-fromℕ< ltBlock

  ge : q + 1 Nat.≤ Fin.toℕ w′
  ge =
    subst (Nat._≤ Fin.toℕ w′) (sym (q+1 q))
      (subst (suc q Nat.≤_) (sym w′ℕ) (Nat.s≤s (Nat.<⇒≤ gt)))

  p₂ : 𝔽 (sum (suc b ∷ b₂ ∷ B₂))
  p₂ = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p₂ℕ : Fin.toℕ p₂ ≡ Fin.toℕ w′ Nat.∸ (q + 1)
  p₂ℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n w′))

  p₂ℕ′ : Fin.toℕ p₂ ≡ Fin.toℕ w Nat.∸ q
  p₂ℕ′ = p₂ℕ ■ cong₂ Nat._∸_ w′ℕ (q+1 q)

  split₂ : Fin.toℕ w′ ≡ (q + 1) + Fin.toℕ p₂
  split₂ = sym (cong ((q + 1) +_) p₂ℕ ■ Nat.m+[n∸m]≡n ge)

  p₃bound : Fin.toℕ w Nat.∸ q Nat.< suc b
  p₃bound = ∸-bound (Nat.<⇒≤ gt) ltBlock

  p₃ : 𝔽 (suc b)
  p₃ = Fin.fromℕ< p₃bound

  p₃ℕ : Fin.toℕ p₃ ≡ Fin.toℕ w Nat.∸ q
  p₃ℕ = Fin.toℕ-fromℕ< p₃bound

  p₃ℕ₂ : Fin.toℕ p₂ ≡ Fin.toℕ p₃
  p₃ℕ₂ = p₂ℕ′ ■ sym p₃ℕ

------------------------------------------------------------------------
-- Cons cases.

UBFrom-rwk l s (b₀ ∷ []) B₂ q b x c e₁ e₂ w w′ slotEq notEq lo hi =
  cons-step-ins l s b₀ (q + suc b) B₂ (q + 1) (suc b ∷ B₂) (0 + q) x c e₁ e₂
    w w′ l<s
    (λ p p′ ne lo′ hi′ →
      UBFrom-rwk (suc l) s [] B₂ q b x c (SoupTerm.`phi (x , l)) e₂ p p′
        slotEq ne lo′ hi′
      ■ cong
          (λ z →
            proj₁ (Translation.UBFrom (suc l) ((q + 1) ∷ suc b ∷ B₂) x
                    (z , c , insertPhi x s e₂)) p′)
          (insertPhi-below x s l l<s))
    (λ same → notEq (same ■ sym shape))
    (λ lt → lo (subst (Fin.toℕ w Nat.<_) (sym shape) lt))
    (λ gt → hi (subst (Nat._< Fin.toℕ w) (sym shape) gt))
  where
  shape : sum (b₀ ∷ []) + q ≡ b₀ + (0 + q)
  shape = Nat.+-assoc b₀ 0 q

  l<s : l Nat.< s
  l<s = subst (l Nat.<_) (sym slotEq) (Nat.s≤s Nat.≤-refl)

UBFrom-rwk l s (b₀ ∷ b₁ ∷ B₁) B₂ q b x c e₁ e₂ w w′ slotEq notEq lo hi =
  cons-step-ins l s b₀ b₁ (B₁ ++ (q + suc b) ∷ B₂)
    b₁ (B₁ ++ (q + 1) ∷ suc b ∷ B₂) (sum (b₁ ∷ B₁) + q) x c e₁ e₂ w w′ l<s
    (λ p p′ ne lo′ hi′ →
      UBFrom-rwk (suc l) s (b₁ ∷ B₁) B₂ q b x c (SoupTerm.`phi (x , l)) e₂
        p p′ slotEq′ ne lo′ hi′
      ■ cong
          (λ z →
            proj₁ (Translation.UBFrom (suc l)
                    ((b₁ ∷ B₁) ++ (q + 1) ∷ suc b ∷ B₂) x
                    (z , c , insertPhi x s e₂)) p′)
          (insertPhi-below x s l l<s))
    (λ same → notEq (same ■ sym shape))
    (λ lt → lo (subst (Fin.toℕ w Nat.<_) (sym shape) lt))
    (λ gt → hi (subst (Nat._< Fin.toℕ w) (sym shape) gt))
  where
  shape : sum (b₀ ∷ b₁ ∷ B₁) + q ≡ b₀ + (sum (b₁ ∷ B₁) + q)
  shape = Nat.+-assoc b₀ (sum (b₁ ∷ B₁)) q

  l<s : l Nat.< s
  l<s =
    subst (l Nat.<_) (sym slotEq)
      (Nat.s≤s (Nat.m≤n+m l (suc (L.length B₁))))

  slotEq′ : s ≡ L.length (b₁ ∷ B₁) + suc l
  slotEq′ = slotEq ■ sym (Nat.+-suc (suc (L.length B₁)) l)

UB-rwk :
  ∀ (B₁ B₂ : Typed.BindGroup) (q b : ℕ) (x c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d)
    (w : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)))
    (w′ : 𝔽 (sum (B₁ ++ (q + 1) ∷ suc b ∷ B₂))) →
  Fin.toℕ w ≢ sum B₁ + q →
  (Fin.toℕ w Nat.< sum B₁ + q → Fin.toℕ w′ ≡ Fin.toℕ w) →
  (sum B₁ + q Nat.< Fin.toℕ w → Fin.toℕ w′ ≡ suc (Fin.toℕ w)) →
  insertPhi x (L.length B₁)
    (proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] x (e₁ , c , e₂)) w) ≡
  proj₁ (Translation.UB[ B₁ ++ (q + 1) ∷ suc b ∷ B₂ ] x
          ( insertPhi x (L.length B₁) e₁
          , c
          , insertPhi x (L.length B₁) e₂ )) w′
UB-rwk B₁ B₂ q b x c e₁ e₂ w w′ =
  UBFrom-rwk 0 (L.length B₁) B₁ B₂ q b x c e₁ e₂ w w′
    (sym (Nat.+-identityʳ (L.length B₁)))

------------------------------------------------------------------------
-- Positions of the split block inside a binder group.

injAt :
  ∀ (B₁ Bm B₂ : Typed.BindGroup) →
  𝔽 (sum (Bm ++ B₂)) → 𝔽 (sum (B₁ ++ Bm ++ B₂))
injAt [] Bm B₂ z = z
injAt (b ∷ B₁) Bm B₂ z = b ↑ʳ injAt B₁ Bm B₂ z

injAt-toℕ :
  ∀ (B₁ Bm B₂ : Typed.BindGroup) (z : 𝔽 (sum (Bm ++ B₂))) →
  Fin.toℕ (injAt B₁ Bm B₂ z) ≡ sum B₁ + Fin.toℕ z
injAt-toℕ [] Bm B₂ z = refl
injAt-toℕ (b ∷ B₁) Bm B₂ z =
  Fin.toℕ-↑ʳ b (injAt B₁ Bm B₂ z)
  ■ cong (b +_) (injAt-toℕ B₁ Bm B₂ z)
  ■ sym (+-assoc b (sum B₁) (Fin.toℕ z))

private
  pos-split-inj :
    ∀ (a : ℕ) (B₁ Bs : Typed.BindGroup) (i : 𝔽 (sum Bs)) →
    Fin.cast (sym (sum-++ (a ∷ B₁) Bs)) (sum (a ∷ B₁) ↑ʳ i) ≡
    a ↑ʳ Fin.cast (sym (sum-++ B₁ Bs)) (sum B₁ ↑ʳ i)
  pos-split-inj a B₁ Bs i = Fin.toℕ-injective
    ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁) Bs)) (sum (a ∷ B₁) ↑ʳ i)
    ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁)) i
    ■ +-assoc a (sum B₁) (Fin.toℕ i)
    ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁ Bs)) (sum B₁ ↑ʳ i))
          ■ cong (a +_)
              ( Fin.toℕ-cast (sym (sum-++ B₁ Bs)) (sum B₁ ↑ʳ i)
              ■ Fin.toℕ-↑ʳ (sum B₁) i ) ) )

  injAt-cast :
    ∀ (B₁ Bm B₂ : Typed.BindGroup) (z : 𝔽 (sum (Bm ++ B₂))) →
    injAt B₁ Bm B₂ z ≡
    Fin.cast (sym (sum-++ B₁ (Bm ++ B₂))) (sum B₁ ↑ʳ z)
  injAt-cast [] Bm B₂ z =
    sym (Fin.toℕ-injective
      ( Fin.toℕ-cast (sym (sum-++ [] (Bm ++ B₂))) (sum [] ↑ʳ z)
      ■ Fin.toℕ-↑ʳ (sum []) z ))
  injAt-cast (b ∷ B₁) Bm B₂ z =
    cong (b ↑ʳ_) (injAt-cast B₁ Bm B₂ z)
    ■ sym (pos-split-inj b B₁ (Bm ++ B₂) z)

inj-injAt :
  ∀ (B₁ B₂ B Bm : Typed.BindGroup) (k : ℕ) (z : 𝔽 (sum (Bm ++ B₂))) →
  Source.SplitRenamings.inj B₁ B₂ (sum B) {Bm} {k} z ≡
  injAt B₁ Bm B₂ z ↑ˡ sum B ↑ˡ k
inj-injAt B₁ B₂ B Bm k z =
  cong (λ w → w ↑ˡ sum B ↑ˡ k) (sym (injAt-cast B₁ Bm B₂ z))

------------------------------------------------------------------------
-- The three handles of an rsplit inside a whole binder group.

group-rsplit-shape-from :
  ∀ (l s : ℕ) (B₁ B₂ : Typed.BindGroup) (q b : ℕ) (x c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d) →
  s ≡ L.length B₁ + l →
  Σ[ e₁′ ∈ SoupTerm.Tm d ]
  Σ[ e₂′ ∈ SoupTerm.Tm d ]
    (proj₁ (Translation.UBFrom l (B₁ ++ (q + suc b) ∷ B₂) x (e₁ , c , e₂))
      (injAt B₁ ((q + suc b) ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) ≡
     Translation.chanTriple (e₁′ , c , e₂′))
  × (proj₁ (Translation.UBFrom l (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x
             (insertPhi x s e₁ , c , insertPhi x s e₂))
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂
        ((q ↑ʳ 0F) ↑ˡ (suc b + sum B₂))) ≡
     Translation.chanTriple
       (insertPhi x s e₁′ , c , SoupTerm.`phi (x , s)))
  × (proj₁ (Translation.UBFrom l (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x
             (insertPhi x s e₁ , c , insertPhi x s e₂))
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂ ((q + 1) ↑ʳ 0F)) ≡
     Translation.chanTriple
       (SoupTerm.`phi (x , s) , c , insertPhi x s e₂′))

group-rsplit-shape-from l s [] [] q b x c e₁ e₂ slotEq =
  pick q e₁ , pick b e₂ ,
  ub-split-entry ((q + suc b) + 0) q b c e₁ e₂ ((q ↑ʳ 0F) ↑ˡ 0)
    (Nat.+-identityʳ (q + suc b))
    (Fin.toℕ-↑ˡ (q ↑ʳ 0F) 0 ■ ↑ʳ0ℕ q) ,
  ( UBFrom-cons-lo l (q + 1) (suc b) [] x c
      (insertPhi x s e₁) (insertPhi x s e₂)
      ((q ↑ʳ 0F) ↑ˡ (suc b + 0)) (q ↑ʳ 0F)
      (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (suc b + 0))
    ■ ub-split-entry (q + 1) q 0 c (insertPhi x s e₁)
        (SoupTerm.`phi (x , l)) (q ↑ʳ 0F) refl (↑ʳ0ℕ q)
    ■ cong₂ (λ u v → Translation.chanTriple (u , c , v))
        (sym (pick-insertPhi x s q e₁))
        (cong (λ z → SoupTerm.`phi (x , z)) (sym slotEq)) ) ,
  ( UBFrom-cons-hi l (q + 1) (suc b) [] x c
      (insertPhi x s e₁) (insertPhi x s e₂) ((q + 1) ↑ʳ 0F) 0F
      (Fin.toℕ-↑ʳ (q + 1) 0F)
    ■ ub-split-entry (suc b + 0) 0 b c (SoupTerm.`phi (x , l))
        (insertPhi x s e₂) 0F (Nat.+-identityʳ (suc b)) refl
    ■ cong₂ (λ u v → Translation.chanTriple (u , c , v))
        (cong (λ z → SoupTerm.`phi (x , z)) (sym slotEq))
        (sym (pick-insertPhi x s b e₂)) )

group-rsplit-shape-from l s [] (b₂ ∷ B₂) q b x c e₁ e₂ slotEq =
  pick q e₁ , pick b (SoupTerm.`phi (x , l)) ,
  ( UBFrom-cons-lo l (q + suc b) b₂ B₂ x c e₁ e₂
      ((q ↑ʳ 0F) ↑ˡ (b₂ + sum B₂)) (q ↑ʳ 0F)
      (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (b₂ + sum B₂))
    ■ ub-split-entry (q + suc b) q b c e₁ (SoupTerm.`phi (x , l))
        (q ↑ʳ 0F) refl (↑ʳ0ℕ q) ) ,
  ( UBFrom-cons-lo l (q + 1) (suc b) (b₂ ∷ B₂) x c
      (insertPhi x s e₁) (insertPhi x s e₂)
      ((q ↑ʳ 0F) ↑ˡ (suc b + (b₂ + sum B₂))) (q ↑ʳ 0F)
      (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (suc b + (b₂ + sum B₂)))
    ■ ub-split-entry (q + 1) q 0 c (insertPhi x s e₁)
        (SoupTerm.`phi (x , l)) (q ↑ʳ 0F) refl (↑ʳ0ℕ q)
    ■ cong₂ (λ u v → Translation.chanTriple (u , c , v))
        (sym (pick-insertPhi x s q e₁))
        (cong (λ z → SoupTerm.`phi (x , z)) (sym slotEq)) ) ,
  ( UBFrom-cons-hi l (q + 1) (suc b) (b₂ ∷ B₂) x c
      (insertPhi x s e₁) (insertPhi x s e₂) ((q + 1) ↑ʳ 0F) 0F
      (Fin.toℕ-↑ʳ (q + 1) 0F)
    ■ UBFrom-cons-lo (suc l) (suc b) b₂ B₂ x c
        (SoupTerm.`phi (x , l)) (insertPhi x s e₂) 0F 0F refl
    ■ ub-split-entry (suc b) 0 b c (SoupTerm.`phi (x , l))
        (SoupTerm.`phi (x , suc l)) 0F refl refl
    ■ cong₂ (λ u v → Translation.chanTriple (u , c , v))
        (cong (λ z → SoupTerm.`phi (x , z)) (sym slotEq))
        (sym
          ( pick-insertPhi x s b (SoupTerm.`phi (x , l))
          ■ cong (pick b)
              (insertPhi-above x s l (Nat.≤-reflexive slotEq)) )) )

group-rsplit-shape-from l s (b₀ ∷ B₁) B₂ q b x c e₁ e₂ slotEq
  with group-rsplit-shape-from (suc l) s B₁ B₂ q b x c
         (SoupTerm.`phi (x , l)) e₂ slotEq′
  where
  slotEq′ : s ≡ L.length B₁ + suc l
  slotEq′ = slotEq ■ sym (Nat.+-suc (L.length B₁) l)
... | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
  e₁′ , e₂′ ,
  ( UBFrom-lookupʳ l b₀ (B₁ ++ (q + suc b) ∷ B₂) x c e₁ e₂
      (injAt B₁ ((q + suc b) ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    ■ eq₀ ) ,
  ( UBFrom-lookupʳ l b₀ (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x c
      (insertPhi x s e₁) (insertPhi x s e₂)
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ (suc b + sum B₂)))
    ■ cong
        (λ z →
          proj₁ (Translation.UBFrom (suc l) (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x
                  (z , c , insertPhi x s e₂))
            (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂
              ((q ↑ʳ 0F) ↑ˡ (suc b + sum B₂))))
        (sym (insertPhi-below x s l l<s))
    ■ eq₁ ) ,
  ( UBFrom-lookupʳ l b₀ (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x c
      (insertPhi x s e₁) (insertPhi x s e₂)
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂ ((q + 1) ↑ʳ 0F))
    ■ cong
        (λ z →
          proj₁ (Translation.UBFrom (suc l) (B₁ ++ (q + 1) ∷ suc b ∷ B₂) x
                  (z , c , insertPhi x s e₂))
            (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂ ((q + 1) ↑ʳ 0F)))
        (sym (insertPhi-below x s l l<s))
    ■ eq₂ )
  where
  l<s : l Nat.< s
  l<s =
    subst (l Nat.<_) (sym slotEq)
      (Nat.s≤s (Nat.m≤n+m l (L.length B₁)))

group-rsplit-shape :
  ∀ (B₁ B₂ : Typed.BindGroup) (q b : ℕ) (x c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d) →
  Σ[ e₁′ ∈ SoupTerm.Tm d ]
  Σ[ e₂′ ∈ SoupTerm.Tm d ]
    (proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] x (e₁ , c , e₂))
      (injAt B₁ ((q + suc b) ∷ []) B₂ ((q ↑ʳ 0F) ↑ˡ sum B₂)) ≡
     Translation.chanTriple (e₁′ , c , e₂′))
  × (proj₁ (Translation.UB[ B₁ ++ (q + 1) ∷ suc b ∷ B₂ ] x
             ( insertPhi x (L.length B₁) e₁
             , c
             , insertPhi x (L.length B₁) e₂ ))
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂
        ((q ↑ʳ 0F) ↑ˡ (suc b + sum B₂))) ≡
     Translation.chanTriple
       ( insertPhi x (L.length B₁) e₁′
       , c
       , SoupTerm.`phi (x , L.length B₁) ))
  × (proj₁ (Translation.UB[ B₁ ++ (q + 1) ∷ suc b ∷ B₂ ] x
             ( insertPhi x (L.length B₁) e₁
             , c
             , insertPhi x (L.length B₁) e₂ ))
      (injAt B₁ ((q + 1) ∷ suc b ∷ []) B₂ ((q + 1) ↑ʳ 0F)) ≡
     Translation.chanTriple
       ( SoupTerm.`phi (x , L.length B₁)
       , c
       , insertPhi x (L.length B₁) e₂′ ))
group-rsplit-shape B₁ B₂ q b x c e₁ e₂ =
  group-rsplit-shape-from 0 (L.length B₁) B₁ B₂ q b x c e₁ e₂
    (sym (Nat.+-identityʳ (L.length B₁)))

------------------------------------------------------------------------
-- The two numeric faces of `SplitRenamings.rwk`.

private
  rwkEq₁ :
    ∀ s k b B C n → s + (k + suc b + B) + C + n ≡ s + k + (suc b + B + C + n)
  rwkEq₁ = solve 6 (λ s k b B C n →
    s :+ (k :+ (con 1 :+ b) :+ B) :+ C :+ n :=
    s :+ k :+ (con 1 :+ b :+ B :+ C :+ n)) refl

  rwkEq₂ :
    ∀ s k b B C n →
    s + k + suc (suc b + B + C + n) ≡ s + ((k + 1) + (suc b + B)) + C + n
  rwkEq₂ = solve 6 (λ s k b B C n →
    s :+ k :+ (con 1 :+ (con 1 :+ b :+ B :+ C :+ n)) :=
    s :+ ((k :+ con 1) :+ (con 1 :+ b :+ B)) :+ C :+ n) refl

  sumRSplitEq :
    ∀ s k b B → s + ((k + 1) + (suc b + B)) ≡ suc (s + ((k + suc b) + B))
  sumRSplitEq = solve 4 (λ s k b B →
    s :+ ((k :+ con 1) :+ (con 1 :+ b :+ B)) :=
    con 1 :+ (s :+ ((k :+ (con 1 :+ b)) :+ B))) refl

  rwkCast₁ :
    ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ) →
    sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k ≡
    sum B₁ + q + (suc b₁ + sum B₂ + sum B + k)
  rwkCast₁ B₁ B₂ B q b₁ k =
    cong (λ z → z + sum B + k) (sum-++ B₁ ((q + suc b₁) ∷ B₂))
    ■ rwkEq₁ (sum B₁) q b₁ (sum B₂) (sum B) k

  rwkCast₂ :
    ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ) →
    sum B₁ + q + suc (suc b₁ + sum B₂ + sum B + k) ≡
    sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B + k
  rwkCast₂ B₁ B₂ B q b₁ k =
    rwkEq₂ (sum B₁) q b₁ (sum B₂) (sum B) k
    ■ cong (λ z → z + sum B + k) (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))

rwk-toℕ-lo :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  Fin.toℕ y Nat.< sum B₁ + q →
  Fin.toℕ (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k} y) ≡
  Fin.toℕ y
rwk-toℕ-lo B₁ B₂ B q b₁ k y lt =
  Fin.toℕ-cast (rwkCast₂ B₁ B₂ B q b₁ k)
    (Source._↑*_ Source.weakenᵣ (sum B₁ + q)
      (Fin.cast (rwkCast₁ B₁ B₂ B q b₁ k) y))
  ■ toℕ-↑*-lt Source.weakenᵣ (sum B₁ + q)
      (Fin.cast (rwkCast₁ B₁ B₂ B q b₁ k) y)
      (subst (Nat._< sum B₁ + q)
        (sym (Fin.toℕ-cast (rwkCast₁ B₁ B₂ B q b₁ k) y)) lt)
  ■ Fin.toℕ-cast (rwkCast₁ B₁ B₂ B q b₁ k) y

rwk-toℕ-hi :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  sum B₁ + q Nat.≤ Fin.toℕ y →
  Fin.toℕ (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k} y) ≡
  suc (Fin.toℕ y)
rwk-toℕ-hi B₁ B₂ B q b₁ k y ge =
  Fin.toℕ-cast (rwkCast₂ B₁ B₂ B q b₁ k)
    (Source._↑*_ Source.weakenᵣ (sum B₁ + q) casted)
  ■ toℕ-↑*-ge Source.weakenᵣ (sum B₁ + q) casted ge′
  ■ cong (sum B₁ + q +_) (cong suc (toℕ-reduce≥ casted ge′))
  ■ Nat.+-suc (sum B₁ + q) (Fin.toℕ casted Nat.∸ (sum B₁ + q))
  ■ cong suc (Nat.m+[n∸m]≡n ge′)
  ■ cong suc (Fin.toℕ-cast (rwkCast₁ B₁ B₂ B q b₁ k) y)
  where
  casted : 𝔽 (sum B₁ + q + (suc b₁ + sum B₂ + sum B + k))
  casted = Fin.cast (rwkCast₁ B₁ B₂ B q b₁ k) y

  ge′ : sum B₁ + q Nat.≤ Fin.toℕ casted
  ge′ =
    subst (sum B₁ + q Nat.≤_)
      (sym (Fin.toℕ-cast (rwkCast₁ B₁ B₂ B q b₁ k) y)) ge

rwk-toℕ-≤ :
  ∀ (B₁ B₂ B : Typed.BindGroup) (q b₁ k : ℕ)
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
  Fin.toℕ (Source.SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {k} y) Nat.≤
  suc (Fin.toℕ y)
rwk-toℕ-≤ B₁ B₂ B q b₁ k y with Fin.toℕ y Nat.<? sum B₁ + q
... | yes lt =
  Nat.≤-trans (Nat.≤-reflexive (rwk-toℕ-lo B₁ B₂ B q b₁ k y lt))
    (Nat.n≤1+n _)
... | no ¬lt =
  Nat.≤-reflexive (rwk-toℕ-hi B₁ B₂ B q b₁ k y (Nat.≮⇒≥ ¬lt))

------------------------------------------------------------------------
-- The two group sizes.

sum-rsplit :
  ∀ (B₁ : Typed.BindGroup) {q b₁ : ℕ} {B₂ : Typed.BindGroup} →
  sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ≡ suc (sum (B₁ ++ (q + suc b₁) ∷ B₂))
sum-rsplit B₁ {q} {b₁} {B₂} =
  sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)
  ■ sumRSplitEq (sum B₁) q b₁ (sum B₂)
  ■ cong suc (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))

rsplit-point≤ :
  ∀ (B₁ : Typed.BindGroup) {q b₁ : ℕ} {B₂ : Typed.BindGroup} →
  sum B₁ + q Nat.≤ sum (B₁ ++ (q + suc b₁) ∷ B₂)
rsplit-point≤ B₁ {q} {b₁} {B₂} =
  subst (sum B₁ + q Nat.≤_) (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
    (Nat.+-monoʳ-≤ (sum B₁)
      (Nat.≤-trans (Nat.m≤m+n q (suc b₁))
        (Nat.m≤m+n (q + suc b₁) (sum B₂))))

------------------------------------------------------------------------
-- The environment agreement across `rwk`.

module _ {n k : ℕ} (B₁ B₂ B : Typed.BindGroup) (q b₁ : ℕ)
         (channel : OrientedChannel n)
         (sigma : Translation.Env k (2 *ℕ n))
         (sigmaFixed :
           (u : 𝔽 k) →
           insertPhi (physicalEndpoint channel 0F) (L.length B₁) (sigma u) ≡
           sigma u)
         where
  private
    module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

    G G′ : Typed.BindGroup
    G = B₁ ++ (q + suc b₁) ∷ B₂
    G′ = B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂

    left right : 𝔽 (2 *ℕ n)
    left = physicalEndpoint channel 0F
    right = physicalEndpoint channel 1F

    slot : ℕ
    slot = L.length B₁

    sizeEq : sum G′ ≡ suc (sum G)
    sizeEq = sum-rsplit B₁ {q} {b₁} {B₂}

    point≤ : sum B₁ + q Nat.≤ sum G
    point≤ = rsplit-point≤ B₁ {q} {b₁} {B₂}

    atkℕ : Fin.toℕ (𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F)) ≡ sum B₁ + q
    atkℕ =
      atk-toℕ B₁ B₂ B (q + suc b₁) k (q ↑ʳ 0F)
      ■ cong (sum B₁ +_) (Fin.toℕ-↑ʳ q 0F ■ Nat.+-identityʳ q)

    case-lo :
      (y : 𝔽 (sum G + sum B + k)) →
      Fin.toℕ y ≢ sum B₁ + q →
      Fin.toℕ y Nat.< sum G →
      insertPhi left slot (bindEnv G B channel sigma y) ≡
      bindEnv G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y)
    case-lo y notEqℕ ltG =
      cong (insertPhi left slot)
        (bindEnv-group G B channel sigma y w (sym wℕ))
      ■ UB-rwk B₁ B₂ q b₁ left left SoupTerm.* SoupTerm.* w w′
          (λ same → notEqℕ (sym wℕ ■ same))
          (λ lt →
            w′ℕ
            ■ rwk-toℕ-lo B₁ B₂ B q b₁ k y
                (Nat.≤-<-trans (Nat.≤-reflexive (sym wℕ)) lt)
            ■ sym wℕ)
          (λ gt →
            w′ℕ
            ■ rwk-toℕ-hi B₁ B₂ B q b₁ k y
                (Nat.≤-trans (Nat.<⇒≤ gt) (Nat.≤-reflexive wℕ))
            ■ cong suc (sym wℕ))
      ■ sym
          (bindEnv-group G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y) w′
            (sym w′ℕ))
      where
      w : 𝔽 (sum G)
      w = Fin.fromℕ< ltG

      wℕ : Fin.toℕ w ≡ Fin.toℕ y
      wℕ = Fin.toℕ-fromℕ< ltG

      bound : Fin.toℕ (𝐒.rwk {q} {b₁} {k} y) Nat.< sum G′
      bound =
        subst (suc (Fin.toℕ (𝐒.rwk {q} {b₁} {k} y)) Nat.≤_) (sym sizeEq)
          (Nat.s≤s (Nat.≤-trans (rwk-toℕ-≤ B₁ B₂ B q b₁ k y) ltG))

      w′ : 𝔽 (sum G′)
      w′ = Fin.fromℕ< bound

      w′ℕ : Fin.toℕ w′ ≡ Fin.toℕ (𝐒.rwk {q} {b₁} {k} y)
      w′ℕ = Fin.toℕ-fromℕ< bound

    case-mid :
      (y : 𝔽 (sum G + sum B + k)) →
      sum G Nat.≤ Fin.toℕ y →
      Fin.toℕ y Nat.< sum G + sum B →
      insertPhi left slot (bindEnv G B channel sigma y) ≡
      bindEnv G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y)
    case-mid y geG ltGB =
      cong (insertPhi left slot) (bindEnv-mid G B channel sigma y v yEq)
      ■ consumePhi-fixed⇒insertPhi-fixed left
          (proj₁ (Translation.UB[ B ] right (SoupTerm.* , right , SoupTerm.*)) v)
          (λ l₀ → UB-phiFree-init B left right l₀ ends-apart v)
          slot
      ■ sym (bindEnv-mid G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y) v rwkEq)
      where
      ends-apart : left ≢ right
      ends-apart = physicalEndpoint-distinct channel

      v : 𝔽 (sum B)
      v = Fin.fromℕ< (∸-bound geG ltGB)

      vℕ : Fin.toℕ v ≡ Fin.toℕ y Nat.∸ sum G
      vℕ = Fin.toℕ-fromℕ< (∸-bound geG ltGB)

      yEq : Fin.toℕ y ≡ sum G + Fin.toℕ v
      yEq = sym (cong (sum G +_) vℕ ■ Nat.m+[n∸m]≡n geG)

      rwkEq : Fin.toℕ (𝐒.rwk {q} {b₁} {k} y) ≡ sum G′ + Fin.toℕ v
      rwkEq =
        rwk-toℕ-hi B₁ B₂ B q b₁ k y (Nat.≤-trans point≤ geG)
        ■ cong suc yEq
        ■ sym (cong (Nat._+ Fin.toℕ v) sizeEq)

    case-outer :
      (y : 𝔽 (sum G + sum B + k)) →
      sum G + sum B Nat.≤ Fin.toℕ y →
      insertPhi left slot (bindEnv G B channel sigma y) ≡
      bindEnv G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y)
    case-outer y ge =
      cong (insertPhi left slot) (bindEnv-outer G B channel sigma y u yEq)
      ■ sigmaFixed u
      ■ sym (bindEnv-outer G′ B channel sigma (𝐒.rwk {q} {b₁} {k} y) u rwkEq)
      where
      u : 𝔽 k
      u = Fin.fromℕ< (∸-bound ge (Fin.toℕ<n y))

      uℕ : Fin.toℕ u ≡ Fin.toℕ y Nat.∸ (sum G + sum B)
      uℕ = Fin.toℕ-fromℕ< (∸-bound ge (Fin.toℕ<n y))

      yEq : Fin.toℕ y ≡ sum G + sum B + Fin.toℕ u
      yEq = sym (cong (sum G + sum B +_) uℕ ■ Nat.m+[n∸m]≡n ge)

      rwkEq :
        Fin.toℕ (𝐒.rwk {q} {b₁} {k} y) ≡ sum G′ + sum B + Fin.toℕ u
      rwkEq =
        rwk-toℕ-hi B₁ B₂ B q b₁ k y
          (Nat.≤-trans point≤ (Nat.≤-trans (Nat.m≤m+n (sum G) (sum B)) ge))
        ■ cong suc yEq
        ■ sym (cong (λ z → z + sum B + Fin.toℕ u) sizeEq)

  source-target-rwk :
    (y : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + k)) →
    y ≢ 𝐒.atk {q + suc b₁} {k} (q ↑ʳ 0F) →
    insertPhi (physicalEndpoint channel 0F) (L.length B₁)
      (bindEnv (B₁ ++ (q + suc b₁) ∷ B₂) B channel sigma y) ≡
    bindEnv (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B channel sigma
      (𝐒.rwk {q} {b₁} {k} y)
  source-target-rwk y notEq with Fin.toℕ y Nat.<? sum G
  ... | yes ltG =
    case-lo y (λ same → notEq (Fin.toℕ-injective (same ■ sym atkℕ))) ltG
  ... | no ¬ltG with Fin.toℕ y Nat.<? sum G + sum B
  ...   | yes ltGB = case-mid y (Nat.≮⇒≥ ¬ltG) ltGB
  ...   | no ¬ltGB = case-outer y (Nat.≮⇒≥ ¬ltGB)
