-- | Naturality of the structural normaliser under renaming.
--
--   `nf-nat : nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ` is what the four binder-permuting
--   ≋′ generators need: each of them renames the body, so relating the two
--   sides' normal forms means relating `nf` to `renNF`.
--
--   This is the one place the two-index `Tel n k` representation does NOT pay
--   for itself.  `plug-++ᵗ` is definitional there, but `renTel` composition is
--   not: `combine` builds `t₂ ++ᵗ renTel t₁ j₂`, and re-basing that is only
--   PROPOSITIONALLY the same shape as re-basing the parts.  The index lemmas
--   below isolate exactly that gap, and `NF-≡` is the interface that lets a
--   proof discharge it once, at the level of the packed normal form, instead of
--   threading transports through every component.
module BorrowedCF.Simulation.Support.Normal.Nat where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (νNF; φNF)

open import Data.List using (List; []; _∷_; _++_; map)

open Nat.Variables

------------------------------------------------------------------------
-- Shape arithmetic: `innerOf` sees only the SHAPE of a telescope.
------------------------------------------------------------------------

-- Re-basing does not change the shape, hence does not change `innerOf`.
innerOf-renTel : ∀ {n k} (t : Tel n k) (a b : ℕ) →
                 innerOf (renTel t a) b ≡ innerOf t b
innerOf-renTel []       a b = refl
innerOf-renTel (tν t)   a b = innerOf-renTel t (2 + a) (2 + b)
innerOf-renTel (tφ f t) a b = innerOf-renTel t (1 + a) (1 + b)

-- Concatenation of telescopes composes `innerOf`.
innerOf-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (b : ℕ) →
              innerOf (t ++ᵗ s) b ≡ innerOf s (innerOf t b)
innerOf-++ᵗ []       s b = refl
innerOf-++ᵗ (tν t)   s b = innerOf-++ᵗ t s (2 + b)
innerOf-++ᵗ (tφ f t) s b = innerOf-++ᵗ t s (1 + b)

-- A telescope re-based at its own outer scope keeps its inner scope.
innerOf-id : ∀ {n k} (t : Tel n k) → innerOf t n ≡ k
innerOf-id = renTel-id

------------------------------------------------------------------------
-- Equality of packed normal forms.
------------------------------------------------------------------------

-- `NF n` packs the inner scope existentially, so two normal forms are equal as
-- soon as the inner scopes agree and the transported components do.  This is
-- the interface that keeps the transports out of the naturality proof proper.
NF-≡ : ∀ {n k k′} (eq : k ≡ k′)
       {t : Tel n k} {t′ : Tel n k′}
       {es : List (Tm k)} {es′ : List (Tm k′)} →
       subst (Tel n) eq t ≡ t′ →
       subst (λ j → List (Tm j)) eq es ≡ es′ →
       mkNF t es ≡ mkNF t′ es′
NF-≡ refl refl refl = refl

------------------------------------------------------------------------
-- Pushing a scope transport under a head binder (by J).
------------------------------------------------------------------------

subst-tν : ∀ {n k k′} (eq : k ≡ k′) (X : Tel (2 + n) k) →
           subst (Tel n) eq (tν X) ≡ tν (subst (Tel (2 + n)) eq X)
subst-tν refl X = refl

subst-tφ : ∀ {n k k′} (eq : k ≡ k′) (f : Flag) (X : Tel (1 + n) k) →
           subst (Tel n) eq (tφ f X) ≡ tφ f (subst (Tel (1 + n)) eq X)
subst-tφ refl f X = refl

------------------------------------------------------------------------
-- A.  Re-basing is idempotent: only the SHAPE of a telescope survives it.
------------------------------------------------------------------------

renTel-renTel : ∀ {n k} (t : Tel n k) (a b : ℕ) →
                subst (Tel b) (innerOf-renTel t a b) (renTel (renTel t a) b) ≡ renTel t b
renTel-renTel []       a b = refl
renTel-renTel (tν t)   a b =
  subst-tν (innerOf-renTel t (2 + a) (2 + b)) _
    ■ cong tν (renTel-renTel t (2 + a) (2 + b))
renTel-renTel (tφ f t) a b =
  subst-tφ (innerOf-renTel t (1 + a) (1 + b)) f _
    ■ cong (tφ f) (renTel-renTel t (1 + a) (1 + b))

------------------------------------------------------------------------
-- B.  Re-basing distributes over concatenation.
------------------------------------------------------------------------

renTel-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (b : ℕ) →
             subst (Tel b) (innerOf-++ᵗ t s b) (renTel (t ++ᵗ s) b)
               ≡ renTel t b ++ᵗ renTel s (innerOf t b)
renTel-++ᵗ []       s b = refl
renTel-++ᵗ (tν t)   s b =
  subst-tν (innerOf-++ᵗ t s (2 + b)) _ ■ cong tν (renTel-++ᵗ t s (2 + b))
renTel-++ᵗ (tφ f t) s b =
  subst-tφ (innerOf-++ᵗ t s (1 + b)) f _ ■ cong (tφ f) (renTel-++ᵗ t s (1 + b))

------------------------------------------------------------------------
-- C.  The matching facts for the lifted renamings, pointwise on variables.
------------------------------------------------------------------------

liftRen-cong : ∀ {n k n′} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ n′} →
               ρ₁ ≗ ρ₂ → liftRen t ρ₁ ≗ liftRen t ρ₂
liftRen-cong []       eq = eq
liftRen-cong (tν t)   eq = liftRen-cong t (eq ~↑* 2)
liftRen-cong (tφ f t) eq = liftRen-cong t (eq ~↑)

-- Lifting along a concatenation is lifting twice.
liftRen-++ᵗ : ∀ {n k j n′} (t : Tel n k) (s : Tel k j) (ρ : n →ᵣ n′) (x : 𝔽 j) →
              subst 𝔽 (innerOf-++ᵗ t s n′) (liftRen (t ++ᵗ s) ρ x)
                ≡ liftRen s (liftRen t ρ) x
liftRen-++ᵗ []       s ρ x = refl
liftRen-++ᵗ (tν t)   s ρ x = liftRen-++ᵗ t s (ρ ↑* 2) x
liftRen-++ᵗ (tφ f t) s ρ x = liftRen-++ᵗ t s (ρ ↑)   x

-- Lifting composes: re-basing the telescope is exactly what lets the two lifts
-- meet.
liftRen-· : ∀ {n k n′ a} (t : Tel n k) (ρ : n →ᵣ n′) (σ : n′ →ᵣ a) (x : 𝔽 k) →
            subst 𝔽 (innerOf-renTel t n′ a) (liftRen (renTel t n′) σ (liftRen t ρ x))
              ≡ liftRen t (ρ ·ₖ σ) x
liftRen-· []       ρ σ x = refl
liftRen-· (tν t)   ρ σ x =
  liftRen-· t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftRen-· (tφ f t) ρ σ x =
  liftRen-· t (ρ ↑) (σ ↑) x
    ■ liftRen-cong t (λ y → sym (dist-↑-· ρ σ y)) x

------------------------------------------------------------------------
-- Naturality, modulo ONE lemma about `combine`.
------------------------------------------------------------------------

-- The leaf, ν and φ cases of naturality are DEFINITIONAL: `renNF` pushes
-- `renTel`/`liftRen` under a head binder exactly the way `nf` does, so they are
-- `refl` and two `cong`s.  Everything that is left is the ∥ case, i.e. that
-- `combine` commutes with re-basing.  Isolating it as a hypothesis (rather than
-- a hole) records that the reduction is COMPLETE: naturality is `Combine-nat`
-- and nothing else.
Combine-nat : Set
Combine-nat = ∀ {n n′} (N₁ N₂ : NF n) (ρ : n →ᵣ n′) →
              combine (renNF N₁ n′ ρ) (renNF N₂ n′ ρ) ≡ renNF (combine N₁ N₂) n′ ρ

module _ (combine-nat : Combine-nat) where

  nf-nat : ∀ {n n′} (P : Proc n) (ρ : n →ᵣ n′) → nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ
  nf-nat ⟪ e ⟫   ρ = refl
  nf-nat (ν P)   ρ = cong νNF     (nf-nat P (ρ ↑* 2))
  nf-nat (φ f P) ρ = cong (φNF f) (nf-nat P (ρ ↑))
  nf-nat (P ∥ Q) ρ =
    cong₂ combine (nf-nat P ρ) (nf-nat Q ρ) ■ combine-nat (nf P) (nf Q) ρ

------------------------------------------------------------------------
-- Status of `Combine-nat`.
------------------------------------------------------------------------
--
--   Writing N₁ = mkNF t₁ es₁ (t₁ : Tel n j₁) and N₂ = mkNF t₂ es₂ (t₂ : Tel n j₂),
--   the two sides carry inner scopes
--
--       LHS : innerOf (renTel t₁ n′) (innerOf t₂ n′)
--       RHS : innerOf (t₂ ++ᵗ renTel t₁ j₂) n′
--
--   both equal to `innerOf t₁ (innerOf t₂ n′)` by `innerOf-renTel` /
--   `innerOf-++ᵗ`, but only PROPOSITIONALLY.  Every ingredient needed to bridge
--   that gap is now proved above:
--
--     telescope half : renTel-renTel (A) and renTel-++ᵗ (B), both by induction
--                      with the subst-pushing helpers subst-tν / subst-tφ;
--     renaming half  : liftRen-++ᵗ and liftRen-· (C), pointwise on variables,
--                      with liftRen-cong and the Kits laws dist-↑*-· / dist-↑-·;
--     packaging      : NF-≡, which discharges the index transport once on the
--                      packed normal form.
--
--   What remains is the ASSEMBLY: instantiate NF-≡ with the composite index
--   equality and feed it the telescope equation from A+B and the thread equation
--   from C, the latter also needing `subst` pushed through `_++_` / `map` and a
--   `⋯`-fusion step to turn (e ⋯ ρ₁) ⋯ ρ₂ into e ⋯ (ρ₁ ·ₖ ρ₂).
--
--   Representation note, now settled: keep the two-index `Tel n k`.  Indexing by
--   a scope-free `Shape` would make re-basing the identity and kill A and B, but
--   it moves the transport into `combine`'s DEFINITION — its threads would have
--   to cross `inner (s₂ ++ˢ s₁) n ≡ inner s₁ (inner s₂ n)` — which is strictly
--   worse than carrying it in this proof only.
