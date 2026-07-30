module BorrowedCF.Types.StartsObstruction where

-- Machine-checked obstruction to a *structural* leading-atom-kind predicate.
--
-- The ending analogue (AtomSnoc.EndsKind) works because `≃𝕊-distr` puts the
-- shared suffix `s` where the ENDING lives, and ending-in-`s` distributes into
-- both branches.  For the LEADING case the brn is at the HEAD and `s` is the
-- SUFFIX, so a branch that SKIPS defers its first action to `s`.  No purely
-- structural "starts-with-kind" predicate is `≃`-invariant: the natural fix
-- (allow a brn branch to skip — the "permissive" `SK` below) OVER-claims and
-- breaks under `≃𝕊-distr`, witnessed concretely here.

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomSnoc using (≃-distr; kindWk)

open Bin
open Nat.Variables

-- Permissive "s starts with an atom of kind k": a brn branch may either start
-- with k or skip entirely (deferring to whatever follows the brn).
data SK {n} (k : AtomKind n) : 𝕊 n → Set where
  here : {a : 𝕊 n} (A : Atom a) → atomKind A ≡ k → SK k a
  _-;₁ : {s₁ s₂ : 𝕊 n} → SK k s₁ → SK k (s₁ ; s₂)
  _;₂_ : {s₁ s₂ : 𝕊 n} → Skips s₁ → SK k s₂ → SK k (s₁ ; s₂)
  brn  : {p : Pol} {s₁ s₂ : 𝕊 n} → SK k s₁ ⊎ Skips s₁ → SK k s₂ ⊎ Skips s₂ → SK k (brn p s₁ s₂)
  mu   : {s : 𝕊 (suc n)} → SK (kindWk k) s → SK k (mu s)

module _ {p : Pol} where

  P Q : 𝕊 1
  P = brn p (end p) skip ; (` zero)
  Q = brn p (end p ; (` zero)) (skip ; (` zero))

  -- P is `≃`-accepted by the permissive predicate as "starting with end",
  -- although P's second branch is `skip ; ` 0 ≃ ` 0`, which really starts with
  -- the *variable* 0 — the predicate over-claims.
  inhab : SK (end p) P
  inhab = (brn (inj₁ (here end refl)) (inj₂ skip)) -;₁

  -- Q = distr(P) genuinely has NO leading atom of kind `end p`: its second
  -- branch `skip ; ` 0 ≃ ` 0` starts with the variable 0.
  ¬inhabQ : ¬ SK (end p) Q
  ¬inhabQ (brn _ (inj₁ ((here () _) -;₁)))
  ¬inhabQ (brn _ (inj₁ (skip ;₂ here `- ())))
  ¬inhabQ (brn _ (inj₂ (skip ; ())))

  P≃Q : P ≃ Q
  P≃Q = ≃-distr

  -- Therefore the permissive predicate is NOT preserved by `≃`.
  obstruction : ¬ (∀ {s₁ s₂ : 𝕊 1} → s₁ ≃ s₂ → SK (end p) s₁ → SK (end p) s₂)
  obstruction respects = ¬inhabQ (respects P≃Q inhab)
