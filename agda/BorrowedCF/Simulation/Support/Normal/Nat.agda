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
-- D.  `wkTel` is natural: re-basing a telescope re-bases its weakening.
------------------------------------------------------------------------

-- The only genuinely NEW fact the ∥ case needs, and the only one with no
-- transport in it: the two ways of getting from the outer scope into the inner
-- one — weaken through `t`, then rename — agree.
wkTel-nat : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) (x : 𝔽 n) →
            wkTel (renTel t n′) (ρ x) ≡ liftRen t ρ (wkTel t x)
wkTel-nat []       ρ x = refl
wkTel-nat (tν t)   ρ x =
  cong (wkTel (renTel t _)) (↑*-wk ρ 2 x) ■ wkTel-nat t (ρ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-nat (tφ f t) ρ x =
  cong (wkTel (renTel t _)) (↑*-wk ρ 1 x) ■ wkTel-nat t (ρ ↑)   (weaken* ⦃ Kᵣ ⦄ 1 x)

------------------------------------------------------------------------
-- Transport plumbing.
------------------------------------------------------------------------

subst-■ : ∀ (A : ℕ → Set) {a b c} (p : a ≡ b) (q : b ≡ c) (x : A a) →
          subst A (p ■ q) x ≡ subst A q (subst A p x)
subst-■ A refl q x = refl

-- Two transports landing in a COMMON scope determine an equation between the
-- endpoints.  This is what lets the naturality proof route both sides through a
-- single mid-point instead of chaining substs end to end.
joinSubst : ∀ (A : ℕ → Set) {a b m} (p : a ≡ m) (q : b ≡ m) (x : A a) (y : A b) →
            subst A p x ≡ subst A q y → subst A (p ■ sym q) x ≡ y
joinSubst A refl refl x y h = h

subst-++ᵗ : ∀ {n k j j′} (t : Tel n k) (eq : j ≡ j′) (s : Tel k j) →
            subst (Tel n) eq (t ++ᵗ s) ≡ t ++ᵗ subst (Tel k) eq s
subst-++ᵗ t refl s = refl

subst-wkTel : ∀ {n k k′} (eq : k ≡ k′) (t : Tel n k) (x : 𝔽 n) →
              subst 𝔽 eq (wkTel t x) ≡ wkTel (subst (Tel n) eq t) x
subst-wkTel refl t x = refl

-- A + D packaged: re-basing twice weakens like re-basing once.
wkTel-renTel : ∀ {n k} (t : Tel n k) (a b : ℕ) (x : 𝔽 b) →
               subst 𝔽 (innerOf-renTel t a b) (wkTel (renTel (renTel t a) b) x)
                 ≡ wkTel (renTel t b) x
wkTel-renTel t a b x =
  subst-wkTel (innerOf-renTel t a b) (renTel (renTel t a) b) x
    ■ cong (λ T → wkTel T x) (renTel-renTel t a b)

subst-++ : ∀ {k k′} (eq : k ≡ k′) (xs ys : List (Tm k)) →
           subst (λ j → List (Tm j)) eq (xs ++ ys)
             ≡ subst (λ j → List (Tm j)) eq xs ++ subst (λ j → List (Tm j)) eq ys
subst-++ refl xs ys = refl

map-++ᴸ : ∀ {a b} (σ : a →ᵣ b) (xs ys : List (Tm a)) →
          map (_⋯ σ) (xs ++ ys) ≡ map (_⋯ σ) xs ++ map (_⋯ σ) ys
map-++ᴸ σ []       ys = refl
map-++ᴸ σ (x ∷ xs) ys = cong (_ ∷_) (map-++ᴸ σ xs ys)

map-fuse : ∀ {a b c} (σ : a →ᵣ b) (τ : b →ᵣ c) (es : List (Tm a)) →
           map (_⋯ τ) (map (_⋯ σ) es) ≡ map (_⋯ (σ ·ₖ τ)) es
map-fuse σ τ []       = refl
map-fuse σ τ (e ∷ es) = cong₂ _∷_ (fusion e σ τ) (map-fuse σ τ es)

-- Transporting a renamed thread list is renaming by the transported renaming.
map-⋯-subst : ∀ {a k k′} (eq : k ≡ k′) {σ : a →ᵣ k} {σ′ : a →ᵣ k′} →
              (∀ x → subst 𝔽 eq (σ x) ≡ σ′ x) → (es : List (Tm a)) →
              subst (λ j → List (Tm j)) eq (map (_⋯ σ) es) ≡ map (_⋯ σ′) es
map-⋯-subst refl h []       = refl
map-⋯-subst refl h (e ∷ es) = cong₂ _∷_ (⋯-cong e h) (map-⋯-subst refl h es)

------------------------------------------------------------------------
-- Naturality.
------------------------------------------------------------------------

-- The leaf, ν and φ cases of naturality are DEFINITIONAL: `renNF` pushes
-- `renTel`/`liftRen` under a head binder exactly the way `nf` does, so they are
-- `refl` and two `cong`s.  Everything that is left is the ∥ case, i.e. that
-- `combine` commutes with re-basing.
Combine-nat : Set
Combine-nat = ∀ {n n′} (N₁ N₂ : NF n) (ρ : n →ᵣ n′) →
              combine (renNF N₁ n′ ρ) (renNF N₂ n′ ρ) ≡ renNF (combine N₁ N₂) n′ ρ

-- Both sides are a normal form over `renTel t₂ n′ ++ᵗ renTel t₁ (innerOf t₂ n′)`
-- once their inner scopes are identified; the proof routes each side to that
-- common mid-point (`joinSubst`) rather than transporting one into the other.
combine-nat : Combine-nat
combine-nat {n} {n′} (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) ρ =
  NF-≡ (p ■ sym q)
       (joinSubst (Tel n′) p q
          (renTel t₂ n′ ++ᵗ renTel (renTel t₁ n′) j₂′)
          (renTel (t₂ ++ᵗ renTel t₁ j₂) n′)
          (telL ■ sym telR))
       (joinSubst (λ j → List (Tm j)) p q
          ( map (_⋯ liftRen (renTel t₁ n′) (wkTel (renTel t₂ n′)))
                (map (_⋯ liftRen t₁ ρ) es₁)
         ++ map (_⋯ wkTel (renTel (renTel t₁ n′) j₂′))
                (map (_⋯ liftRen t₂ ρ) es₂) )
          ( map (_⋯ liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ)
                ( map (_⋯ liftRen t₁ (wkTel t₂)) es₁
               ++ map (_⋯ wkTel (renTel t₁ j₂)) es₂ ) )
          (thrL ■ sym thrR))
  where
    j₂′ : ℕ
    j₂′ = innerOf t₂ n′

    p : innerOf (renTel t₁ n′) j₂′ ≡ innerOf t₁ j₂′
    p = innerOf-renTel t₁ n′ j₂′

    q₁ : innerOf (t₂ ++ᵗ renTel t₁ j₂) n′ ≡ innerOf (renTel t₁ j₂) j₂′
    q₁ = innerOf-++ᵗ t₂ (renTel t₁ j₂) n′

    q₂ : innerOf (renTel t₁ j₂) j₂′ ≡ innerOf t₁ j₂′
    q₂ = innerOf-renTel t₁ j₂ j₂′

    q : innerOf (t₂ ++ᵗ renTel t₁ j₂) n′ ≡ innerOf t₁ j₂′
    q = q₁ ■ q₂

    μ₁ : j₁ →ᵣ innerOf t₁ j₂′
    μ₁ = liftRen t₁ (ρ ·ₖ wkTel (renTel t₂ n′))

    μ₂ : j₂ →ᵣ innerOf t₁ j₂′
    μ₂ = liftRen t₂ ρ ·ₖ wkTel (renTel t₁ j₂′)

    telL : subst (Tel n′) p (renTel t₂ n′ ++ᵗ renTel (renTel t₁ n′) j₂′)
             ≡ renTel t₂ n′ ++ᵗ renTel t₁ j₂′
    telL = subst-++ᵗ (renTel t₂ n′) p (renTel (renTel t₁ n′) j₂′)
             ■ cong (renTel t₂ n′ ++ᵗ_) (renTel-renTel t₁ n′ j₂′)

    telR : subst (Tel n′) q (renTel (t₂ ++ᵗ renTel t₁ j₂) n′)
             ≡ renTel t₂ n′ ++ᵗ renTel t₁ j₂′
    telR = subst-■ (Tel n′) q₁ q₂ _
             ■ cong (subst (Tel n′) q₂) (renTel-++ᵗ t₂ (renTel t₁ j₂) n′)
             ■ subst-++ᵗ (renTel t₂ n′) q₂ (renTel (renTel t₁ j₂) j₂′)
             ■ cong (renTel t₂ n′ ++ᵗ_) (renTel-renTel t₁ j₂ j₂′)

    h₁ : ∀ x → subst 𝔽 p
                 ((liftRen t₁ ρ ·ₖ liftRen (renTel t₁ n′) (wkTel (renTel t₂ n′))) x)
                 ≡ μ₁ x
    h₁ = liftRen-· t₁ ρ (wkTel (renTel t₂ n′))

    h₂ : ∀ x → subst 𝔽 p
                 ((liftRen t₂ ρ ·ₖ wkTel (renTel (renTel t₁ n′) j₂′)) x)
                 ≡ μ₂ x
    h₂ x = wkTel-renTel t₁ n′ j₂′ (liftRen t₂ ρ x)

    thrL : subst (λ j → List (Tm j)) p
             ( map (_⋯ liftRen (renTel t₁ n′) (wkTel (renTel t₂ n′)))
                   (map (_⋯ liftRen t₁ ρ) es₁)
            ++ map (_⋯ wkTel (renTel (renTel t₁ n′) j₂′))
                   (map (_⋯ liftRen t₂ ρ) es₂) )
             ≡ map (_⋯ μ₁) es₁ ++ map (_⋯ μ₂) es₂
    thrL = cong (subst (λ j → List (Tm j)) p)
                (cong₂ _++_ (map-fuse (liftRen t₁ ρ) _ es₁)
                            (map-fuse (liftRen t₂ ρ) _ es₂))
             ■ subst-++ p _ _
             ■ cong₂ _++_ (map-⋯-subst p h₁ es₁) (map-⋯-subst p h₂ es₂)

    g₁ : ∀ x → subst 𝔽 q
                 ((liftRen t₁ (wkTel t₂) ·ₖ liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ) x)
                 ≡ μ₁ x
    g₁ x = subst-■ 𝔽 q₁ q₂ _
             ■ cong (subst 𝔽 q₂)
                 (liftRen-++ᵗ t₂ (renTel t₁ j₂) ρ (liftRen t₁ (wkTel t₂) x))
             ■ liftRen-· t₁ (wkTel t₂) (liftRen t₂ ρ) x
             ■ liftRen-cong t₁ (λ y → sym (wkTel-nat t₂ ρ y)) x

    g₂ : ∀ x → subst 𝔽 q
                 ((wkTel (renTel t₁ j₂) ·ₖ liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ) x)
                 ≡ μ₂ x
    g₂ x = subst-■ 𝔽 q₁ q₂ _
             ■ cong (subst 𝔽 q₂)
                 ( liftRen-++ᵗ t₂ (renTel t₁ j₂) ρ (wkTel (renTel t₁ j₂) x)
                 ■ sym (wkTel-nat (renTel t₁ j₂) (liftRen t₂ ρ) x) )
             ■ wkTel-renTel t₁ j₂ j₂′ (liftRen t₂ ρ x)

    thrR : subst (λ j → List (Tm j)) q
             ( map (_⋯ liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ)
                   ( map (_⋯ liftRen t₁ (wkTel t₂)) es₁
                  ++ map (_⋯ wkTel (renTel t₁ j₂)) es₂ ) )
             ≡ map (_⋯ μ₁) es₁ ++ map (_⋯ μ₂) es₂
    thrR = cong (subst (λ j → List (Tm j)) q)
                ( map-++ᴸ (liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ)
                    (map (_⋯ liftRen t₁ (wkTel t₂)) es₁)
                    (map (_⋯ wkTel (renTel t₁ j₂)) es₂)
                ■ cong₂ _++_
                    (map-fuse (liftRen t₁ (wkTel t₂))
                              (liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ) es₁)
                    (map-fuse (wkTel (renTel t₁ j₂))
                              (liftRen (t₂ ++ᵗ renTel t₁ j₂) ρ) es₂) )
             ■ subst-++ q _ _
             ■ cong₂ _++_ (map-⋯-subst q g₁ es₁) (map-⋯-subst q g₂ es₂)

nf-nat : ∀ {n n′} (P : Proc n) (ρ : n →ᵣ n′) → nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ
nf-nat ⟪ e ⟫   ρ = refl
nf-nat (ν P)   ρ = cong νNF     (nf-nat P (ρ ↑* 2))
nf-nat (φ f P) ρ = cong (φNF f) (nf-nat P (ρ ↑))
nf-nat (P ∥ Q) ρ =
  cong₂ combine (nf-nat P ρ) (nf-nat Q ρ) ■ combine-nat (nf P) (nf Q) ρ

------------------------------------------------------------------------
-- How `combine-nat` goes through.
------------------------------------------------------------------------
--
--   Writing N₁ = mkNF t₁ es₁ (t₁ : Tel n j₁) and N₂ = mkNF t₂ es₂ (t₂ : Tel n j₂),
--   the two sides carry inner scopes
--
--       LHS : innerOf (renTel t₁ n′) (innerOf t₂ n′)
--       RHS : innerOf (t₂ ++ᵗ renTel t₁ j₂) n′
--
--   both equal to `innerOf t₁ (innerOf t₂ n′)` by `innerOf-renTel` /
--   `innerOf-++ᵗ`, but only PROPOSITIONALLY.  Rather than transport one side
--   into the other, the proof sends BOTH to that common mid-point and glues with
--   `joinSubst`; that keeps every sub-lemma stated in its own natural direction:
--
--     telescope half : renTel-renTel (A) and renTel-++ᵗ (B), both by induction
--                      with the subst-pushing helpers subst-tν / subst-tφ;
--     renaming half  : liftRen-++ᵗ and liftRen-· (C), pointwise on variables,
--                      with liftRen-cong and the Kits laws dist-↑*-· / dist-↑-·;
--     the new fact   : wkTel-nat (D), that re-basing a telescope re-bases its
--                      weakening — the one ingredient with no transport in it,
--                      and the one that makes the two mid-point renamings meet;
--     packaging      : NF-≡, which discharges the index transport once on the
--                      packed normal form.
--
--   Representation note, settled: keep the two-index `Tel n k`.  Indexing by a
--   scope-free `Shape` would make re-basing the identity and kill A and B, but
--   it moves the transport into `combine`'s DEFINITION — its threads would have
--   to cross `inner (s₂ ++ˢ s₁) n ≡ inner s₁ (inner s₂ n)` — which is strictly
--   worse than carrying it in this proof only.
