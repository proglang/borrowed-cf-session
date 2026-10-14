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
innerOf-renTel : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) (b : ℕ) →
                 innerOf (renTel t ρ) b ≡ innerOf t b
innerOf-renTel []         ρ b = refl
innerOf-renTel (tν t)     ρ b = innerOf-renTel t (ρ ↑* 2) (2 + b)
innerOf-renTel (tφ f c t) ρ b = innerOf-renTel t (ρ ↑)   (1 + b)

-- Concatenation of telescopes composes `innerOf`.
innerOf-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (b : ℕ) →
              innerOf (t ++ᵗ s) b ≡ innerOf s (innerOf t b)
innerOf-++ᵗ []         s b = refl
innerOf-++ᵗ (tν t)     s b = innerOf-++ᵗ t s (2 + b)
innerOf-++ᵗ (tφ f c t) s b = innerOf-++ᵗ t s (1 + b)

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

subst-tφ : ∀ {n k k′} (eq : k ≡ k′) (f : Flag) (c : Tm n) (X : Tel (1 + n) k) →
           subst (Tel n) eq (tφ f c X) ≡ tφ f c (subst (Tel (1 + n)) eq X)
subst-tφ refl f c X = refl

------------------------------------------------------------------------
-- A.  Re-basing is idempotent: only the SHAPE of a telescope survives it.
------------------------------------------------------------------------

-- Re-basing respects pointwise-equal renamings (needed because a tφ now carries
-- a channel term that renaming acts on).
renTel-cong : ∀ {n k n′} (t : Tel n k) {ρ σ : n →ᵣ n′} → ρ ≗ σ → renTel t ρ ≡ renTel t σ
renTel-cong []         eq = refl
renTel-cong (tν t)     eq = cong tν (renTel-cong t (eq ~↑* 2))
renTel-cong (tφ f c t) eq = cong₂ (tφ f) (⋯-cong c eq) (renTel-cong t (eq ~↑))

renTel-renTel : ∀ {n k n′ n″} (t : Tel n k) (ρ : n →ᵣ n′) (σ : n′ →ᵣ n″) →
                subst (Tel n″) (innerOf-renTel t ρ n″) (renTel (renTel t ρ) σ) ≡ renTel t (ρ ·ₖ σ)
renTel-renTel []         ρ σ = refl
renTel-renTel (tν t)     ρ σ =
  subst-tν (innerOf-renTel t (ρ ↑* 2) _) _
    ■ cong tν (renTel-renTel t (ρ ↑* 2) (σ ↑* 2)
                 ■ renTel-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)))
renTel-renTel (tφ f c t) ρ σ =
  subst-tφ (innerOf-renTel t (ρ ↑) _) f (c ⋯ ρ ⋯ σ) _
    ■ cong₂ (tφ f) (fusion c ρ σ)
                   (renTel-renTel t (ρ ↑) (σ ↑)
                      ■ renTel-cong t (λ y → sym (dist-↑-· ρ σ y)))

------------------------------------------------------------------------
-- B.  Re-basing distributes over concatenation.
------------------------------------------------------------------------

renTel-++ᵗ : ∀ {n k j n′} (t : Tel n k) (s : Tel k j) (ρ : n →ᵣ n′) →
             subst (Tel n′) (innerOf-++ᵗ t s n′) (renTel (t ++ᵗ s) ρ)
               ≡ renTel t ρ ++ᵗ renTel s (liftRen t ρ)
renTel-++ᵗ []         s ρ = refl
renTel-++ᵗ (tν t)     s ρ =
  subst-tν (innerOf-++ᵗ t s _) _ ■ cong tν (renTel-++ᵗ t s (ρ ↑* 2))
renTel-++ᵗ (tφ f c t) s ρ =
  subst-tφ (innerOf-++ᵗ t s _) f (c ⋯ ρ) _ ■ cong (tφ f (c ⋯ ρ)) (renTel-++ᵗ t s (ρ ↑))

------------------------------------------------------------------------
-- C.  The matching facts for the lifted renamings, pointwise on variables.
------------------------------------------------------------------------

liftRen-cong : ∀ {n k n′} (t : Tel n k) {ρ₁ ρ₂ : n →ᵣ n′} →
               ρ₁ ≗ ρ₂ → liftRen t ρ₁ ≗ liftRen t ρ₂
liftRen-cong []         eq = eq
liftRen-cong (tν t)     eq = liftRen-cong t (eq ~↑* 2)
liftRen-cong (tφ f c t) eq = liftRen-cong t (eq ~↑)

-- Lifting along a concatenation is lifting twice.
liftRen-++ᵗ : ∀ {n k j n′} (t : Tel n k) (s : Tel k j) (ρ : n →ᵣ n′) (x : 𝔽 j) →
              subst 𝔽 (innerOf-++ᵗ t s n′) (liftRen (t ++ᵗ s) ρ x)
                ≡ liftRen s (liftRen t ρ) x
liftRen-++ᵗ []         s ρ x = refl
liftRen-++ᵗ (tν t)     s ρ x = liftRen-++ᵗ t s (ρ ↑* 2) x
liftRen-++ᵗ (tφ f c t) s ρ x = liftRen-++ᵗ t s (ρ ↑)   x

-- Lifting composes: re-basing the telescope is exactly what lets the two lifts
-- meet.
liftRen-· : ∀ {n k n′ a} (t : Tel n k) (ρ : n →ᵣ n′) (σ : n′ →ᵣ a) (x : 𝔽 k) →
            subst 𝔽 (innerOf-renTel t ρ a) (liftRen (renTel t ρ) σ (liftRen t ρ x))
              ≡ liftRen t (ρ ·ₖ σ) x
liftRen-· []         ρ σ x = refl
liftRen-· (tν t)     ρ σ x =
  liftRen-· t (ρ ↑* 2) (σ ↑* 2) x
    ■ liftRen-cong t (λ y → sym (dist-↑*-· 2 ρ σ y)) x
liftRen-· (tφ f c t) ρ σ x =
  liftRen-· t (ρ ↑) (σ ↑) x
    ■ liftRen-cong t (λ y → sym (dist-↑-· ρ σ y)) x

------------------------------------------------------------------------
-- D.  `wkTel` is natural: re-basing a telescope re-bases its weakening.
------------------------------------------------------------------------

-- The only genuinely NEW fact the ∥ case needs, and the only one with no
-- transport in it: the two ways of getting from the outer scope into the inner
-- one — weaken through `t`, then rename — agree.
wkTel-nat : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) (x : 𝔽 n) →
            wkTel (renTel t ρ) (ρ x) ≡ liftRen t ρ (wkTel t x)
wkTel-nat []         ρ x = refl
wkTel-nat (tν t)     ρ x =
  cong (wkTel (renTel t (ρ ↑* 2))) (↑*-wk ρ 2 x) ■ wkTel-nat t (ρ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-nat (tφ f c t) ρ x =
  cong (wkTel (renTel t (ρ ↑)))   (↑*-wk ρ 1 x) ■ wkTel-nat t (ρ ↑)   (weaken* ⦃ Kᵣ ⦄ 1 x)

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
wkTel-renTel : ∀ {n k n′ n″} (t : Tel n k) (ρ : n →ᵣ n′) (σ : n′ →ᵣ n″) (x : 𝔽 n″) →
               subst 𝔽 (innerOf-renTel t ρ n″) (wkTel (renTel (renTel t ρ) σ) x)
                 ≡ wkTel (renTel t (ρ ·ₖ σ)) x
wkTel-renTel t ρ σ x =
  subst-wkTel (innerOf-renTel t ρ _) (renTel (renTel t ρ) σ) x
    ■ cong (λ T → wkTel T x) (renTel-renTel t ρ σ)

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
  NF-≡ (pL ■ sym pR)
       (joinSubst (Tel n′) pL pR
          (renTel t₂ ρ ++ᵗ renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))
          (renTel (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ)
          (telL ■ sym telR))
       (joinSubst (λ j → List (Tm j)) pL pR
          ( map (_⋯ liftRen (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))
                (map (_⋯ liftRen t₁ ρ) es₁)
         ++ map (_⋯ wkTel (renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ))))
                (map (_⋯ liftRen t₂ ρ) es₂) )
          ( map (_⋯ liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ)
                ( map (_⋯ liftRen t₁ (wkTel t₂)) es₁
               ++ map (_⋯ wkTel (renTel t₁ (wkTel t₂))) es₂ ) )
          (thrL ■ sym thrR))
  where
    J₂ : ℕ
    J₂ = innerOf t₂ n′

    pL : innerOf (renTel t₁ ρ) J₂ ≡ innerOf t₁ J₂
    pL = innerOf-renTel t₁ ρ J₂

    q₁ : innerOf (t₂ ++ᵗ renTel t₁ (wkTel t₂)) n′ ≡ innerOf (renTel t₁ (wkTel t₂)) J₂
    q₁ = innerOf-++ᵗ t₂ (renTel t₁ (wkTel t₂)) n′

    q₂ : innerOf (renTel t₁ (wkTel t₂)) J₂ ≡ innerOf t₁ J₂
    q₂ = innerOf-renTel t₁ (wkTel t₂) J₂

    pR : innerOf (t₂ ++ᵗ renTel t₁ (wkTel t₂)) n′ ≡ innerOf t₁ J₂
    pR = q₁ ■ q₂

    -- the mid-point renamings
    ν₀ : n →ᵣ J₂
    ν₀ = wkTel t₂ ·ₖ liftRen t₂ ρ

    μ₁ : j₁ →ᵣ innerOf t₁ J₂
    μ₁ = liftRen t₁ ν₀

    μ₂ : j₂ →ᵣ innerOf t₁ J₂
    μ₂ = liftRen t₂ ρ ·ₖ wkTel (renTel t₁ ν₀)

    telL : subst (Tel n′) pL (renTel t₂ ρ ++ᵗ renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))
             ≡ renTel t₂ ρ ++ᵗ renTel t₁ ν₀
    telL = subst-++ᵗ (renTel t₂ ρ) pL (renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))
             ■ cong (renTel t₂ ρ ++ᵗ_)
                    (renTel-renTel t₁ ρ (wkTel (renTel t₂ ρ))
                       ■ renTel-cong t₁ (wkTel-nat t₂ ρ))

    telR : subst (Tel n′) pR (renTel (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ)
             ≡ renTel t₂ ρ ++ᵗ renTel t₁ ν₀
    telR = subst-■ (Tel n′) q₁ q₂ _
             ■ cong (subst (Tel n′) q₂) (renTel-++ᵗ t₂ (renTel t₁ (wkTel t₂)) ρ)
             ■ subst-++ᵗ (renTel t₂ ρ) q₂ (renTel (renTel t₁ (wkTel t₂)) (liftRen t₂ ρ))
             ■ cong (renTel t₂ ρ ++ᵗ_) (renTel-renTel t₁ (wkTel t₂) (liftRen t₂ ρ))

    h₁ : ∀ x → subst 𝔽 pL
                 ((liftRen t₁ ρ ·ₖ liftRen (renTel t₁ ρ) (wkTel (renTel t₂ ρ))) x)
                 ≡ μ₁ x
    h₁ x = liftRen-· t₁ ρ (wkTel (renTel t₂ ρ)) x
             ■ liftRen-cong t₁ (wkTel-nat t₂ ρ) x

    h₂ : ∀ x → subst 𝔽 pL
                 ((liftRen t₂ ρ ·ₖ wkTel (renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))) x)
                 ≡ μ₂ x
    h₂ x = wkTel-renTel t₁ ρ (wkTel (renTel t₂ ρ)) (liftRen t₂ ρ x)
             ■ cong (λ T → wkTel T (liftRen t₂ ρ x)) (renTel-cong t₁ (wkTel-nat t₂ ρ))

    thrL : subst (λ j → List (Tm j)) pL
             ( map (_⋯ liftRen (renTel t₁ ρ) (wkTel (renTel t₂ ρ)))
                   (map (_⋯ liftRen t₁ ρ) es₁)
            ++ map (_⋯ wkTel (renTel (renTel t₁ ρ) (wkTel (renTel t₂ ρ))))
                   (map (_⋯ liftRen t₂ ρ) es₂) )
             ≡ map (_⋯ μ₁) es₁ ++ map (_⋯ μ₂) es₂
    thrL = cong (subst (λ j → List (Tm j)) pL)
                (cong₂ _++_ (map-fuse (liftRen t₁ ρ) _ es₁)
                            (map-fuse (liftRen t₂ ρ) _ es₂))
             ■ subst-++ pL _ _
             ■ cong₂ _++_ (map-⋯-subst pL h₁ es₁) (map-⋯-subst pL h₂ es₂)

    g₁ : ∀ x → subst 𝔽 pR
                 ((liftRen t₁ (wkTel t₂) ·ₖ liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ) x)
                 ≡ μ₁ x
    g₁ x = subst-■ 𝔽 q₁ q₂ _
             ■ cong (subst 𝔽 q₂)
                 (liftRen-++ᵗ t₂ (renTel t₁ (wkTel t₂)) ρ (liftRen t₁ (wkTel t₂) x))
             ■ liftRen-· t₁ (wkTel t₂) (liftRen t₂ ρ) x

    g₂ : ∀ x → subst 𝔽 pR
                 ((wkTel (renTel t₁ (wkTel t₂)) ·ₖ liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ) x)
                 ≡ μ₂ x
    g₂ x = subst-■ 𝔽 q₁ q₂ _
             ■ cong (subst 𝔽 q₂)
                 ( liftRen-++ᵗ t₂ (renTel t₁ (wkTel t₂)) ρ (wkTel (renTel t₁ (wkTel t₂)) x)
                 ■ sym (wkTel-nat (renTel t₁ (wkTel t₂)) (liftRen t₂ ρ) x) )
             ■ wkTel-renTel t₁ (wkTel t₂) (liftRen t₂ ρ) (liftRen t₂ ρ x)

    thrR : subst (λ j → List (Tm j)) pR
             ( map (_⋯ liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ)
                   ( map (_⋯ liftRen t₁ (wkTel t₂)) es₁
                  ++ map (_⋯ wkTel (renTel t₁ (wkTel t₂))) es₂ ) )
             ≡ map (_⋯ μ₁) es₁ ++ map (_⋯ μ₂) es₂
    thrR = cong (subst (λ j → List (Tm j)) pR)
                ( map-++ᴸ (liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ)
                    (map (_⋯ liftRen t₁ (wkTel t₂)) es₁)
                    (map (_⋯ wkTel (renTel t₁ (wkTel t₂))) es₂)
                ■ cong₂ _++_
                    (map-fuse (liftRen t₁ (wkTel t₂))
                              (liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ) es₁)
                    (map-fuse (wkTel (renTel t₁ (wkTel t₂)))
                              (liftRen (t₂ ++ᵗ renTel t₁ (wkTel t₂)) ρ) es₂) )
             ■ subst-++ pR _ _
             ■ cong₂ _++_ (map-⋯-subst pR g₁ es₁) (map-⋯-subst pR g₂ es₂)

nf-nat : ∀ {n n′} (P : Proc n) (ρ : n →ᵣ n′) → nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ
nf-nat ⟪ e ⟫   ρ = refl
nf-nat (ν P)   ρ = cong νNF     (nf-nat P (ρ ↑* 2))
nf-nat (φ f c P) ρ = cong (φNF f (c ⋯ ρ)) (nf-nat P (ρ ↑))
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
