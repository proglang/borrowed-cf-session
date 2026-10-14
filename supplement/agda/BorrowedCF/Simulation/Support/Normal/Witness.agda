-- | Phase 4: turning a `~` derivation into DATA.
--
--   `~` was deliberately generated from concrete moves, each carrying its own
--   explicit renaming (Normal.Equiv).  That was not an accident of presentation:
--   it means a derivation can be COMPUTED WITH.  This module extracts exactly
--   what a derivation contains — a bijection between the two normal forms' inner
--   scopes, plus a permutation of their live threads.
--
--   Downstream (`Backward.agda`) the use is: given `T ≋ U[ P ] σ`, `≋-witness`
--   supplies a concrete renaming carrying `T`'s bound names to the image's, so a
--   redex located in `T` can be transported to the image.  That is why `fwd` is
--   an honest renaming `_→ᵣ_` and not merely a function on `𝔽`: only a renaming
--   composes with `_⋯_`.
--
--   The quotient on threads is `live*` (Normal.Flat), i.e. the spent `K \`unit`
--   threads are dropped — the `unit-del` generator deletes them, so no finer
--   invariant survives.  `live*` is the RIGHT quotient here because renaming
--   cannot create or destroy a spent unit: `K c ⋯ σ ≡ K c` and every other head
--   constructor is preserved (`live-⋯` below is the 23-case proof).
module BorrowedCF.Simulation.Support.Normal.Witness where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; renTel-id)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id; liftId-liftRen)
open import BorrowedCF.Simulation.Support.Normal.Shift using (liftId-·)
open import BorrowedCF.Simulation.Support.Normal.Flat using (live; live*)
open import BorrowedCF.Simulation.Support.Normal.Bubble using (map-⋯-id; aswap-21-12)
open import BorrowedCF.Simulation.Support.Normal.Nat using (map-++ᴸ; map-fuse)
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Sound using (≋⇒~)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive; prep; swap)
  renaming (refl to ↭refl; trans to ↭tr)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++-comm; ++⁺; ++⁺ˡ; map⁺)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
-- The symmetric-closure constructors clash with the record's `fwd`/`bwd`
-- fields, and the FIELD names are the interface downstream reads.
open import Relation.Binary.Construct.Closure.Symmetric using ()
  renaming (fwd to sfwd; bwd to sbwd)

open Nat.Variables

------------------------------------------------------------------------
-- `live*` is stable under renaming and under permutation.
------------------------------------------------------------------------

-- Renaming never turns a live thread into the spent unit, nor conversely: the
-- head constructor of a term is untouched.  Spelling all 23 constructors out is
-- the honest way to say that — there is no head-preservation lemma for `_⋯_`.
live-⋯ : ∀ {a b} (σ : a →ᵣ b) (e : Tm a) → live (e ⋯ σ) ≡ map (_⋯ σ) (live e)
live-⋯ σ (K `unit)          = refl
live-⋯ σ (K `fork)          = refl
live-⋯ σ (K `send)          = refl
live-⋯ σ (K `recv)          = refl
live-⋯ σ (K `drop)          = refl
live-⋯ σ (K `acq)           = refl
live-⋯ σ (K `discard)       = refl
live-⋯ σ (K (`end p))       = refl
live-⋯ σ (K (`new s))       = refl
live-⋯ σ (K (`lsplit s))    = refl
live-⋯ σ (K (`rsplit s))    = refl
live-⋯ σ (K (`select b))    = refl
live-⋯ σ (K `branch)        = refl
live-⋯ σ (` x)              = refl
live-⋯ σ (ƛ e)              = refl
live-⋯ σ (μ e)              = refl
live-⋯ σ (e₁ ·⟨ d ⟩ e₂)     = refl
live-⋯ σ (e₁ ; e₂)          = refl
live-⋯ σ (e₁ ⊗ e₂)          = refl
live-⋯ σ (`let e₁ `in e₂)   = refl
live-⋯ σ (`let⊗ e₁ `in e₂)  = refl
live-⋯ σ (`inj i e)         = refl
live-⋯ σ (`case e `of⟨ e₁ ; e₂ ⟩) = refl

live*-map : ∀ {a b} (σ : a →ᵣ b) (es : List (Tm a)) →
            live* (map (_⋯ σ) es) ≡ map (_⋯ σ) (live* es)
live*-map σ []       = refl
live*-map σ (e ∷ es) =
  cong₂ _++_ (live-⋯ σ e) (live*-map σ es) ■ sym (map-++ᴸ σ (live e) (live* es))

live*-↭ : ∀ {a} {xs ys : List (Tm a)} → xs ↭ ys → live* xs ↭ live* ys
live*-↭ ↭refl        = ↭-refl
live*-↭ (prep x p)   = ++⁺ˡ (live x) (live*-↭ p)
live*-↭ (swap {xs = xs} {ys = ys} x y p) =
  ↭-trans (↭-reflexive (sym (++-assoc (live x) (live y) (live* xs))))
    (↭-trans (++⁺ (++-comm (live x) (live y)) (live*-↭ p))
             (↭-reflexive (++-assoc (live y) (live x) (live* ys))))
live*-↭ (↭tr p q)    = ↭-trans (live*-↭ p) (live*-↭ q)

------------------------------------------------------------------------
-- The witness.
------------------------------------------------------------------------

record Witness {n} (N₁ N₂ : NF n) : Set where
  constructor mkW
  field
    fwd  : inner N₁ →ᵣ inner N₂
    bwd  : inner N₂ →ᵣ inner N₁
    inv₁ : ∀ x → bwd (fwd x) ≡ x
    inv₂ : ∀ x → fwd (bwd x) ≡ x
    thrs : live* (map (_⋯ fwd) (thr N₁)) ↭ live* (thr N₂)

open Witness public

------------------------------------------------------------------------
-- The groupoid structure.  With these, the `EqClosure` induction is trivial.
------------------------------------------------------------------------

witness-refl : ∀ {n} {N : NF n} → Witness N N
witness-refl {N = mkNF t es} = mkW idₖ idₖ (λ _ → refl) (λ _ → refl)
  (↭-reflexive (cong live* (map-⋯-id (λ _ → refl) es)))

witness-sym : ∀ {n} {N₁ N₂ : NF n} → Witness N₁ N₂ → Witness N₂ N₁
witness-sym {N₁ = mkNF t₁ es₁} {N₂ = mkNF t₂ es₂} w =
  mkW (bwd w) (fwd w) (inv₂ w) (inv₁ w) thrs′
  where
    -- Push the whole `thrs` permutation back along `bwd`: renaming a
    -- permutation is a permutation (`map⁺`), and `live*` commutes with it.
    step : live* (map (_⋯ bwd w) es₂) ↭ live* (map (_⋯ bwd w) (map (_⋯ fwd w) es₁))
    step = ↭-sym (↭-trans (↭-reflexive (live*-map (bwd w) (map (_⋯ fwd w) es₁)))
                          (↭-trans (map⁺ (_⋯ bwd w) (thrs w))
                                   (↭-reflexive (sym (live*-map (bwd w) es₂)))))

    undo : map (_⋯ bwd w) (map (_⋯ fwd w) es₁) ≡ es₁
    undo = map-fuse (fwd w) (bwd w) es₁
             ■ map-⋯-id (λ x → inv₁ w x) es₁

    thrs′ : live* (map (_⋯ bwd w) es₂) ↭ live* es₁
    thrs′ = ↭-trans step (↭-reflexive (cong live* undo))

witness-trans : ∀ {n} {N₁ N₂ N₃ : NF n} → Witness N₁ N₂ → Witness N₂ N₃ → Witness N₁ N₃
witness-trans {N₁ = mkNF t₁ es₁} {N₂ = mkNF t₂ es₂} {N₃ = mkNF t₃ es₃} w₁ w₂ =
  mkW (fwd w₁ ·ₖ fwd w₂) (bwd w₂ ·ₖ bwd w₁)
      (λ x → cong (bwd w₁) (inv₁ w₂ (fwd w₁ x)) ■ inv₁ w₁ x)
      (λ x → cong (fwd w₂) (inv₂ w₁ (bwd w₂ x)) ■ inv₂ w₂ x)
      thrs′
  where
    thrs′ : live* (map (_⋯ (fwd w₁ ·ₖ fwd w₂)) es₁) ↭ live* es₃
    thrs′ =
      ↭-trans (↭-reflexive (cong live* (sym (map-fuse (fwd w₁) (fwd w₂) es₁))))
        (↭-trans (↭-reflexive (live*-map (fwd w₂) (map (_⋯ fwd w₁) es₁)))
          (↭-trans (map⁺ (_⋯ fwd w₂) (thrs w₁))
            (↭-trans (↭-reflexive (sym (live*-map (fwd w₂) es₂)))
                     (thrs w₂))))

------------------------------------------------------------------------
-- The transpositions are involutions (or mutual inverses) on names.
------------------------------------------------------------------------

-- All four are pointwise facts about `Fin`, decided by case-splitting on the
-- first few names — exactly the idiom Normal.Bubble uses for `aswap-21-12`.

swap-11-inv : ∀ {n} (x : 𝔽 (1 + 1 + n)) → swapᵣ 1 1 (swapᵣ 1 1 x) ≡ x
swap-11-inv zero           = refl
swap-11-inv (suc zero)     = refl
swap-11-inv (suc (suc x))  = refl

aswap-22-inv : ∀ {n} (x : 𝔽 (2 + (2 + n))) → assocSwapᵣ 2 2 (assocSwapᵣ 2 2 x) ≡ x
aswap-22-inv zero                        = refl
aswap-22-inv (suc zero)                  = refl
aswap-22-inv (suc (suc zero))            = refl
aswap-22-inv (suc (suc (suc zero)))      = refl
aswap-22-inv (suc (suc (suc (suc x))))   = refl

aswap-11-inv : ∀ {n} (x : 𝔽 (1 + (1 + n))) → assocSwapᵣ 1 1 (assocSwapᵣ 1 1 x) ≡ x
aswap-11-inv zero           = refl
aswap-11-inv (suc zero)     = refl
aswap-11-inv (suc (suc x))  = refl

-- The νφ transposition is the one that is not an involution: its inverse is the
-- mirrored block swap.  `aswap-21-12` (Normal.Bubble) is the other direction.
aswap-12-21 : ∀ {n} (x : 𝔽 (1 + (2 + n))) → assocSwapᵣ 2 1 (assocSwapᵣ 1 2 x) ≡ x
aswap-12-21 zero                  = refl
aswap-12-21 (suc zero)            = refl
aswap-12-21 (suc (suc zero))      = refl
aswap-12-21 (suc (suc (suc x)))   = refl

------------------------------------------------------------------------
-- One generator, one witness.
------------------------------------------------------------------------

-- For the four transpositions the thread lists are LITERALLY `map (_⋯ fwd)` of
-- each other, so `thrs` is reflexivity; all the content is in the inverse laws,
-- and `liftId-·`/`liftId-id` lift the pointwise `Fin` facts under the telescope.
-- Linked-φ: the generators RENAME the body by `liftRen t ξ` (fwd) and change
-- the inner scope, so the witness's inverse re-bases back with `liftId t ξ⁻¹`
-- under the `renTel-id t` transport.  `liftId-liftRen` (Endo) is what reconciles
-- the two lifts; the pointwise `Fin` inverse laws do the rest.
wInv₁ : ∀ {n k} (t : Tel n k) (ξ₁ ξ₂ : n →ᵣ n) → (∀ x → ξ₂ (ξ₁ x) ≡ x) →
        ∀ x → liftId t ξ₂ (subst 𝔽 (renTel-id t) (liftRen t ξ₁ x)) ≡ x
wInv₁ t ξ₁ ξ₂ h x =
  cong (liftId t ξ₂) (liftId-liftRen t ξ₁ x) ■ liftId-· t ξ₁ ξ₂ x ■ liftId-id t h x

wInv₂ : ∀ {n k} (t : Tel n k) (ξ₁ ξ₂ : n →ᵣ n) → (∀ x → ξ₁ (ξ₂ x) ≡ x) →
        ∀ y → liftRen t ξ₁ (liftId t ξ₂ (subst 𝔽 (renTel-id t) y)) ≡ y
wInv₂ t ξ₁ ξ₂ h y =
  sym (subst-sym-subst (renTel-id t))
    ■ cong (subst 𝔽 (sym (renTel-id t))) H
    ■ subst-sym-subst (renTel-id t)
  where
    H : subst 𝔽 (renTel-id t) (liftRen t ξ₁ (liftId t ξ₂ (subst 𝔽 (renTel-id t) y)))
          ≡ subst 𝔽 (renTel-id t) y
    H = liftId-liftRen t ξ₁ (liftId t ξ₂ (subst 𝔽 (renTel-id t) y))
          ■ liftId-· t ξ₂ ξ₁ (subst 𝔽 (renTel-id t) y)
          ■ liftId-id t h (subst 𝔽 (renTel-id t) y)

~₁-witness : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → Witness N₁ N₂
~₁-witness (perm-ν1 s t es) =
  mkW (liftRen t (swapᵣ 1 1)) (λ y → liftId t (swapᵣ 1 1) (subst 𝔽 (renTel-id t) y))
      (wInv₁ t (swapᵣ 1 1) (swapᵣ 1 1) (λ x → swap-11-inv x))
      (wInv₂ t (swapᵣ 1 1) (swapᵣ 1 1) (λ x → swap-11-inv x)) ↭-refl

~₁-witness (perm-νν s t es) =
  mkW (liftRen t (assocSwapᵣ 2 2)) (λ y → liftId t (assocSwapᵣ 2 2) (subst 𝔽 (renTel-id t) y))
      (wInv₁ t (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) (λ x → aswap-22-inv x))
      (wInv₂ t (assocSwapᵣ 2 2) (assocSwapᵣ 2 2) (λ x → aswap-22-inv x)) ↭-refl

~₁-witness (perm-φφ s x y c d t es) =
  mkW (liftRen t (assocSwapᵣ 1 1)) (λ z → liftId t (assocSwapᵣ 1 1) (subst 𝔽 (renTel-id t) z))
      (wInv₁ t (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) (λ w → aswap-11-inv w))
      (wInv₂ t (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) (λ w → aswap-11-inv w)) ↭-refl

~₁-witness (perm-νφ s x c t es) =
  mkW (liftRen t (assocSwapᵣ 1 2)) (λ z → liftId t (assocSwapᵣ 2 1) (subst 𝔽 (renTel-id t) z))
      (wInv₁ t (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) (λ w → aswap-12-21 w))
      (wInv₂ t (assocSwapᵣ 1 2) (assocSwapᵣ 2 1) (λ w → aswap-21-12 w)) ↭-refl

~₁-witness (perm-thr t {es} {es′} p) =
  mkW idₖ idₖ (λ _ → refl) (λ _ → refl)
    (↭-trans (↭-reflexive (cong live* (map-⋯-id (λ _ → refl) es))) (live*-↭ p))

-- Deleting the spent unit is invisible to `live*`: `live (K \`unit) ≡ []`.
~₁-witness (unit-del t es) =
  mkW idₖ idₖ (λ _ → refl) (λ _ → refl)
    (↭-reflexive (cong live* (map-⋯-id (λ _ → refl) (K `unit ∷ es))))

------------------------------------------------------------------------
-- The payoff.
------------------------------------------------------------------------

~-witness : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → Witness N₁ N₂
~-witness ε           = witness-refl
~-witness (sfwd g ◅ c) = witness-trans (~₁-witness g)               (~-witness c)
~-witness (sbwd g ◅ c) = witness-trans (witness-sym (~₁-witness g)) (~-witness c)

≋-witness : ∀ {n} {P Q : Proc n} → P ≋ Q → Witness (nf P) (nf Q)
≋-witness c = ~-witness (≋⇒~ c)
