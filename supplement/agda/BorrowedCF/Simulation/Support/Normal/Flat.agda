-- | Phase 1 of the normal-form uniqueness theorem: the BINDER-FREE fragment.
--
--   For processes built only from ⟪_⟫ and _∥_, the multiset of LIVE threads
--   (threads other than the spent `unit`) is a COMPLETE invariant of ≋:
--
--       nf-unique-flat : pars xs ≋ pars ys → live* xs ↭ live* ys      (soundness)
--       pars-↭         : xs ↭ ys → pars xs ≋ pars ys                  (completeness)
--
--   This is the decision gate for the whole plan: it exercises the invariant
--   presentation and the list-permutation machinery with ZERO index bookkeeping.
--
--   The fragment is genuinely closed, and that is where Normal.Invariant earns
--   its keep: νcount / φcount are ≋-invariants, so every intermediate process of
--   a ≋-chain between two binder-free endpoints is itself binder-free
--   (`flat?`).  Without that, a chain could in principle detour through a
--   ν/φ-bearing process and the induction would not go through.
module BorrowedCF.Simulation.Support.Normal.Flat where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form using (pars)
open import BorrowedCF.Simulation.Support.Normal.Invariant
  using (νcount; φcount; ≋′-νcount; ≋′-φcount; ≋-νcount; ≋-φcount)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive; prep; swap)
  renaming (refl to ↭refl; trans to ↭tr)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++-comm; ++⁺ʳ)
open import Data.Nat.Properties using (m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- Live threads.
------------------------------------------------------------------------

live : ∀ {n} → Tm n → List (Tm n)
live (K `unit) = []
live e         = e ∷ []

live* : ∀ {n} → List (Tm n) → List (Tm n)
live* []       = []
live* (e ∷ es) = live e ++ live* es

-- Total on all processes; only meaningful (and only used) on binder-free ones.
threads : ∀ {n} → Proc n → List (Tm n)
threads ⟪ e ⟫   = live e
threads (P ∥ Q) = threads P ++ threads Q
threads (ν _)   = []
threads (φ _ _ _) = []

------------------------------------------------------------------------
-- The binder-free fragment.
------------------------------------------------------------------------

data Flat {n} : Proc n → Set where
  fthr : ∀ {e} → Flat ⟪ e ⟫
  fpar : ∀ {P Q} → Flat P → Flat Q → Flat (P ∥ Q)

flat-ν : ∀ {n} {P : Proc n} → Flat P → νcount P ≡ 0
flat-ν fthr = refl
flat-ν (fpar {P} f g) = cong₂ _+_ (flat-ν f) (flat-ν g)

flat-φ : ∀ {n} {P : Proc n} → Flat P → φcount P ≡ 0
flat-φ fthr = refl
flat-φ (fpar {P} f g) = cong₂ _+_ (flat-φ f) (flat-φ g)

-- The converse: no binders ⇒ binder-free.  This is what keeps ≋-chains inside
-- the fragment.
flat? : ∀ {n} (P : Proc n) → νcount P ≡ 0 → φcount P ≡ 0 → Flat P
flat? ⟪ e ⟫   _  _  = fthr
flat? (P ∥ Q) νe φe =
  fpar (flat? P (m+n≡0⇒m≡0 (νcount P) νe) (m+n≡0⇒m≡0 (φcount P) φe))
       (flat? Q (m+n≡0⇒n≡0 (νcount P) νe) (m+n≡0⇒n≡0 (φcount P) φe))
flat? (ν P)   () _
flat? (φ f c P) _  ()

------------------------------------------------------------------------
-- Soundness: ≋ preserves the live-thread multiset on the fragment.
------------------------------------------------------------------------

≋′-threads : ∀ {n} {P Q : Proc n} → Flat P → Flat Q → P ≋′ Q → threads P ↭ threads Q
≋′-threads (fpar {P} {Q} _ _) _ ∥-comm′ = ++-comm (threads P) (threads Q)
≋′-threads (fpar {P₁} (_) (fpar {P₂} {P₃} _ _)) _ ∥-assoc′ =
  ↭-reflexive (sym (++-assoc (threads P₁) (threads P₂) (threads P₃)))
≋′-threads _ _ ∥-unit′ = ↭-refl
≋′-threads (fpar f₁ _) (fpar {Q = Q} f₂ _) (∥-cong′ g) =
  ++⁺ʳ (threads Q) (≋′-threads f₁ f₂ g)
-- The other eight generators all put a ν or a φ on one side, so splitting on
-- `Flat P` already discharges them: Agda reports the explicit absurd clauses as
-- unreachable, i.e. the coverage checker has ruled them out on its own.

≋-threads : ∀ {n} {P Q : Proc n} → Flat P → Flat Q → P ≋ Q → threads P ↭ threads Q
≋-threads fp fq ε = ↭-refl
≋-threads fp fq (fwd g ◅ c) =
  let fm = flat? _ (sym (≋′-νcount g) ■ flat-ν fp) (sym (≋′-φcount g) ■ flat-φ fp)
  in ↭-trans (≋′-threads fp fm g) (≋-threads fm fq c)
≋-threads fp fq (bwd g ◅ c) =
  let fm = flat? _ (≋′-νcount g ■ flat-ν fp) (≋′-φcount g ■ flat-φ fp)
  in ↭-trans (↭-sym (≋′-threads fm fp g)) (≋-threads fm fq c)

------------------------------------------------------------------------
-- Flat normal forms.
------------------------------------------------------------------------

Flat-pars : ∀ {n} (xs : List (Tm n)) → Flat (pars xs)
Flat-pars []       = fthr
Flat-pars (e ∷ es) = fpar fthr (Flat-pars es)

threads-pars : ∀ {n} (xs : List (Tm n)) → threads (pars xs) ≡ live* xs
threads-pars []       = refl
threads-pars (e ∷ es) = cong (live e ++_) (threads-pars es)

-- SOUNDNESS: ≋-equal flat normal forms have permuted live-thread lists.
nf-unique-flat : ∀ {n} (xs ys : List (Tm n)) → pars xs ≋ pars ys → live* xs ↭ live* ys
nf-unique-flat xs ys c =
  ↭-trans (↭-reflexive (sym (threads-pars xs)))
    (↭-trans (≋-threads (Flat-pars xs) (Flat-pars ys) c)
             (↭-reflexive (threads-pars ys)))

------------------------------------------------------------------------
-- Completeness: permuting the live threads is a ≋.
------------------------------------------------------------------------

≋-sym : ∀ {n} {P Q : Proc n} → P ≋ Q → Q ≋ P
≋-sym = Eq*.symmetric _

pars-↭ : ∀ {n} {xs ys : List (Tm n)} → xs ↭ ys → pars xs ≋ pars ys
pars-↭ ↭refl        = ε
pars-↭ (prep x p)   = ∥-cong ε (pars-↭ p)
pars-↭ (swap x y p) = ∥-assoc ◅◅ ∥-cong ∥-comm (pars-↭ p) ◅◅ ≋-sym ∥-assoc
pars-↭ (↭tr p q)    = pars-↭ p ◅◅ pars-↭ q

-- Deciding the spent-`unit` thread, so that `live` computes.
isUnit? : ∀ {n} (e : Tm n) → (e ≡ K `unit) ⊎ (live e ≡ e ∷ [])
isUnit? (K `unit)          = inj₁ refl
isUnit? (K `fork)          = inj₂ refl
isUnit? (K `send)          = inj₂ refl
isUnit? (K `recv)          = inj₂ refl
isUnit? (K `drop)          = inj₂ refl
isUnit? (K `acq)           = inj₂ refl
isUnit? (K `discard)       = inj₂ refl
isUnit? (K (`end p))       = inj₂ refl
isUnit? (K (`new s))       = inj₂ refl
isUnit? (K (`lsplit s))    = inj₂ refl
isUnit? (K (`rsplit s))    = inj₂ refl
isUnit? (K (`select b))    = inj₂ refl
isUnit? (K `branch)        = inj₂ refl
isUnit? (` x)              = inj₂ refl
isUnit? (ƛ e)              = inj₂ refl
isUnit? (μ e)              = inj₂ refl
isUnit? (e₁ ·⟨ d ⟩ e₂)     = inj₂ refl
isUnit? (e₁ ; e₂)            = inj₂ refl
isUnit? (e₁ ⊗ e₂)          = inj₂ refl
isUnit? (`let e₁ `in e₂)   = inj₂ refl
isUnit? (`let⊗ e₁ `in e₂)  = inj₂ refl
isUnit? (`inj i e)         = inj₂ refl
isUnit? (`case e `of⟨ e₁ ; e₂ ⟩) = inj₂ refl

pars-live1 : ∀ {n} (e : Tm n) → pars (live e) ≋ ⟪ e ⟫
pars-live1 e with isUnit? e
... | inj₁ refl = ε
... | inj₂ eq   = subst (λ z → pars z ≋ ⟪ e ⟫) (sym eq) ∥-unitʳ

-- Dropping the spent `unit` threads is a ≋.
pars-live* : ∀ {n} (xs : List (Tm n)) → pars xs ≋ pars (live* xs)
pars-live* []       = ε
pars-live* (e ∷ es) =
  ∥-cong (≋-sym (pars-live1 e)) (pars-live* es)
    ◅◅ pars-++ˡ (live e) (live* es)
  where
    pars-++ˡ : ∀ {n} (as bs : List (Tm n)) → pars as ∥ pars bs ≋ pars (as ++ bs)
    pars-++ˡ []       bs = ∥-unitˡ
    pars-++ˡ (a ∷ as) bs = ≋-sym ∥-assoc ◅◅ ∥-cong ε (pars-++ˡ as bs)

-- COMPLETENESS: permuted live-thread lists give ≋-equal flat normal forms.
nf-complete-flat : ∀ {n} (xs ys : List (Tm n)) → live* xs ↭ live* ys → pars xs ≋ pars ys
nf-complete-flat xs ys p =
  pars-live* xs ◅◅ pars-↭ p ◅◅ ≋-sym (pars-live* ys)
