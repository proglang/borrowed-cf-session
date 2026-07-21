-- | `combine` is a congruence in its FIRST argument.
--
--   `combine N₁ N₂` (Normal.Norm) puts N₂'s telescope OUTERMOST and re-bases
--   N₁'s underneath it, so a generator that fires inside N₁ ends up inside the
--   re-based tail — at prefix `t₂ ++ᵗ renTel s j₂` instead of `s`.  Two things
--   have to be checked for it to fire there:
--
--     * the transposition commutes with the re-basing renaming that `combine`
--       puts on N₁'s threads (`liftId-liftRen-nat`), and
--     * it FIXES everything `combine` weakened in from N₂'s side
--       (`swap11-wk` / `aswap-wk`, i.e. the `wkˡ` laws of FinKits).
--
--   Design note.  All four transpositions leave the inner scope alone
--   (`1 + (2 + j)` and `2 + (1 + j)` are definitionally equal), so the ONLY
--   transport in this module is the one `combine-split` discharges: peeling the
--   prefix `s` out of `renTel (s ++ᵗ w) j₂`.  After that everything is a plain
--   equation, which is why `transp-core` can take the image generator as a
--   hypothesis and handle all four cases uniformly.
module BorrowedCF.Simulation.Support.Normal.CongL where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo using (++ᵗ-assoc; wkTel-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Shift using (liftId-wkTel)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; innerOf-++ᵗ; renTel-++ᵗ; liftRen-++ᵗ; subst-++ᵗ; subst-++;
         subst-wkTel; map-fuse; map-++ᴸ; map-⋯-subst)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; ++⁺ʳ)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- Walking the equivalence closure.
------------------------------------------------------------------------

≡→~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ N₂
≡→~ refl = ~-refl

-- A single generator turns into SEVERAL steps on the image — the two `combine`
-- calculations that bracket it are equalities, not generators — so `Eq*.gmap`
-- does not apply and the `Star` has to be walked by hand.
~-lift : ∀ {n} (f : NF n → NF n) → (∀ {A B : NF n} → A ~₁ B → f A ~ f B) →
         ∀ {A B : NF n} → A ~ B → f A ~ f B
~-lift f g ε           = ~-refl
~-lift f g (fwd r ◅ c) = ~-trans (g r)         (~-lift f g c)
~-lift f g (bwd r ◅ c) = ~-trans (~-sym (g r)) (~-lift f g c)

map-⋯-cong : ∀ {a b} {ρ₁ ρ₂ : a →ᵣ b} → ρ₁ ≗ ρ₂ → (es : List (Tm a)) →
             map (_⋯ ρ₁) es ≡ map (_⋯ ρ₂) es
map-⋯-cong h []       = refl
map-⋯-cong h (e ∷ es) = cong₂ _∷_ (⋯-cong e h) (map-⋯-cong h es)

------------------------------------------------------------------------
-- Peeling a generator's prefix out of `combine`.
------------------------------------------------------------------------

-- The only transport in the module: `renTel` does not distribute over `++ᵗ`
-- definitionally, so exposing the prefix `s` of the generator inside
-- `renTel (s ++ᵗ w) j₂` costs one `innerOf-++ᵗ`.  Everything downstream then
-- works with the SPLIT form, where the re-based block `renTel w _` sits at the
-- head and the generator can fire.
combine-split : ∀ {n j₂ j k} (t₂ : Tel n j₂) (es₂ : List (Tm j₂))
                  (s : Tel n j) (w : Tel j k) (es : List (Tm k)) →
  combine (mkNF (s ++ᵗ w) es) (mkNF t₂ es₂)
    ≡ mkNF ((t₂ ++ᵗ renTel s j₂) ++ᵗ renTel w (innerOf s j₂))
           ( map (_⋯ liftRen w (liftRen s (wkTel t₂))) es
          ++ map (_⋯ (wkTel (renTel s j₂) ·ₖ wkTel (renTel w (innerOf s j₂)))) es₂ )
combine-split {n} {j₂} t₂ es₂ s w es = NF-≡ e telEq thrEq
  where
    e : innerOf (s ++ᵗ w) j₂ ≡ innerOf w (innerOf s j₂)
    e = innerOf-++ᵗ s w j₂

    telEq : subst (Tel n) e (t₂ ++ᵗ renTel (s ++ᵗ w) j₂)
              ≡ (t₂ ++ᵗ renTel s j₂) ++ᵗ renTel w (innerOf s j₂)
    telEq = subst-++ᵗ t₂ e (renTel (s ++ᵗ w) j₂)
              ■ cong (t₂ ++ᵗ_) (renTel-++ᵗ s w j₂)
              ■ sym (++ᵗ-assoc t₂ (renTel s j₂) (renTel w (innerOf s j₂)))

    h₁ : ∀ x → subst 𝔽 e (liftRen (s ++ᵗ w) (wkTel t₂) x)
                 ≡ liftRen w (liftRen s (wkTel t₂)) x
    h₁ = liftRen-++ᵗ s w (wkTel t₂)

    h₂ : ∀ y → subst 𝔽 e (wkTel (renTel (s ++ᵗ w) j₂) y)
                 ≡ (wkTel (renTel s j₂) ·ₖ wkTel (renTel w (innerOf s j₂))) y
    h₂ y = subst-wkTel e (renTel (s ++ᵗ w) j₂) y
             ■ cong (λ T → wkTel T y) (renTel-++ᵗ s w j₂)
             ■ wkTel-++ᵗ (renTel s j₂) (renTel w (innerOf s j₂)) y

    thrEq : subst (λ i → List (Tm i)) e
              ( map (_⋯ liftRen (s ++ᵗ w) (wkTel t₂)) es
             ++ map (_⋯ wkTel (renTel (s ++ᵗ w) j₂)) es₂ )
              ≡ map (_⋯ liftRen w (liftRen s (wkTel t₂))) es
             ++ map (_⋯ (wkTel (renTel s j₂) ·ₖ wkTel (renTel w (innerOf s j₂)))) es₂
    thrEq = subst-++ e _ _ ■ cong₂ _++_ (map-⋯-subst e h₁ es) (map-⋯-subst e h₂ es₂)

------------------------------------------------------------------------
-- A transposition survives re-basing.
------------------------------------------------------------------------

-- `liftId` keeps the inner scope fixed and `liftRen` re-bases it; pushing a
-- transposition through a re-basing is therefore a statement about the two
-- meeting, and it reduces to the SAME statement one binder in.
liftId-liftRen-nat : ∀ {n k n′} (t : Tel n k) (ρ ρ′ : n →ᵣ n′)
                       (ξ : n →ᵣ n) (ξ′ : n′ →ᵣ n′) → ρ ·ₖ ξ′ ≗ ξ ·ₖ ρ′ →
                     ∀ x → liftId (renTel t n′) ξ′ (liftRen t ρ x)
                             ≡ liftRen t ρ′ (liftId t ξ x)
liftId-liftRen-nat []       ρ ρ′ ξ ξ′ h x = h x
liftId-liftRen-nat (tν t)   ρ ρ′ ξ ξ′ h x =
  liftId-liftRen-nat t (ρ ↑* 2) (ρ′ ↑* 2) (ξ ↑* 2) (ξ′ ↑* 2)
    (λ y → sym (dist-↑*-· 2 ρ ξ′ y) ■ (h ~↑* 2) y ■ dist-↑*-· 2 ξ ρ′ y) x
liftId-liftRen-nat (tφ f t) ρ ρ′ ξ ξ′ h x =
  liftId-liftRen-nat t (ρ ↑) (ρ′ ↑) (ξ ↑) (ξ′ ↑)
    (λ y → sym (dist-↑-· ρ ξ′ y) ■ (h ~↑) y ■ dist-↑-· ξ ρ′ y) x

------------------------------------------------------------------------
-- A transposition fixes what was weakened in past it.
------------------------------------------------------------------------

swap11-wk : ∀ {m} (z : 𝔽 m) →
            swapᵣ 1 1 (weaken* ⦃ Kᵣ ⦄ 2 z) ≡ weaken* ⦃ Kᵣ ⦄ 2 z
swap11-wk z =
  cong (swapᵣ 1 1) (weaken*~wkˡ ⦃ Kᵣ ⦄ 2 z)
    ■ wk-swap 1 1 z
    ■ sym (weaken*~wkˡ ⦃ Kᵣ ⦄ 2 z)

aswap-wk : ∀ a b {m} (z : 𝔽 m) →
           assocSwapᵣ a b (weaken* ⦃ Kᵣ ⦄ a (weaken* ⦃ Kᵣ ⦄ b z))
             ≡ weaken* ⦃ Kᵣ ⦄ b (weaken* ⦃ Kᵣ ⦄ a z)
aswap-wk a b z =
  cong (assocSwapᵣ a b)
       (cong (weaken* ⦃ Kᵣ ⦄ a) (weaken*~wkˡ ⦃ Kᵣ ⦄ b z)
          ■ weaken*~wkˡ ⦃ Kᵣ ⦄ a (wkˡ ⦃ Kᵣ ⦄ b z))
    ■ wkˡ-assocSwap a b z
    ■ sym (cong (weaken* ⦃ Kᵣ ⦄ b) (weaken*~wkˡ ⦃ Kᵣ ⦄ a z)
             ■ weaken*~wkˡ ⦃ Kᵣ ⦄ b (wkˡ ⦃ Kᵣ ⦄ a z))

------------------------------------------------------------------------
-- The uniform transposition step.
------------------------------------------------------------------------

-- Everything the four transposition cases have in common, with the image
-- generator taken as a hypothesis: all that is left of the generator here is
-- that it rewrites the whole thread list by `ζ`, and the two facts above say
-- what `ζ` does to `combine`'s two thread blocks.
transp-core : ∀ {n i j k j₂} (Tₛ : Tel n i) (W W′ : Tel i k)
                (ζ : k →ᵣ k) (σ σ′ : j →ᵣ k) (ξ : j →ᵣ j)
                (es : List (Tm j)) (κ : j₂ →ᵣ i) (es₂ : List (Tm j₂)) →
              (∀ (L : List (Tm k)) →
                 mkNF (Tₛ ++ᵗ W) L ~₁ mkNF (Tₛ ++ᵗ W′) (map (_⋯ ζ) L)) →
              σ ·ₖ ζ ≗ ξ ·ₖ σ′ →
              (∀ y → ζ (wkTel W y) ≡ wkTel W′ y) →
              mkNF (Tₛ ++ᵗ W)  (map (_⋯ σ)  es                  ++ map (_⋯ (κ ·ₖ wkTel W))  es₂)
                ~ mkNF (Tₛ ++ᵗ W′) (map (_⋯ σ′) (map (_⋯ ξ) es) ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂)
transp-core Tₛ W W′ ζ σ σ′ ξ es κ es₂ gen natσ fix =
  ~-trans (Eq*.return (gen _)) (≡→~ (cong (mkNF (Tₛ ++ᵗ W′)) eq))
  where
    eq : map (_⋯ ζ) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel W)) es₂)
           ≡ map (_⋯ σ′) (map (_⋯ ξ) es) ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂
    eq = map-++ᴸ ζ (map (_⋯ σ) es) (map (_⋯ (κ ·ₖ wkTel W)) es₂)
           ■ cong₂ _++_
               (map-fuse σ ζ es ■ map-⋯-cong natσ es ■ sym (map-fuse ξ σ′ es))
               (map-fuse (κ ·ₖ wkTel W) ζ es₂ ■ map-⋯-cong (λ y → fix (κ y)) es₂)

------------------------------------------------------------------------
-- One generator.
------------------------------------------------------------------------

combine-cong₁ : ∀ {n} {N₁ N₁′ : NF n} (N₂ : NF n) →
                N₁ ~₁ N₁′ → combine N₁ N₂ ~ combine N₁′ N₂

combine-cong₁ (mkNF t₂ es₂) (perm-thr t p) =
  Eq*.return (perm-thr _ (++⁺ʳ _ (map⁺ _ p)))

combine-cong₁ (mkNF t₂ es₂) (unit-del t es) = Eq*.return (unit-del _ _)

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-ν1 {j} {k} s t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tν t) es))
    (~-trans (transp-core Tₛ (tν u) (tν u) (liftId u (swapᵣ 1 1)) σ σ ξ
                es (wkTel (renTel s j₂)) es₂ (perm-ν1 Tₛ u) natσ fix)
      (≡→~ (sym (combine-split t₂ es₂ s (tν t) (map (_⋯ ξ) es)))))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s j₂

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    u : Tel (2 + i) (innerOf t (2 + i))
    u = renTel t (2 + i)

    σ : k →ᵣ innerOf t (2 + i)
    σ = liftRen t (τ ↑* 2)

    ξ : k →ᵣ k
    ξ = liftId t (swapᵣ 1 1)

    natσ : σ ·ₖ liftId u (swapᵣ 1 1) ≗ ξ ·ₖ σ
    natσ = liftId-liftRen-nat t (τ ↑* 2) (τ ↑* 2) (swapᵣ 1 1) (swapᵣ 1 1)
             (λ y → sym (dist-↑*-swap 1 1 τ y))

    fix : ∀ y → liftId u (swapᵣ 1 1) (wkTel (tν u) y) ≡ wkTel (tν u) y
    fix y = liftId-wkTel u (swapᵣ 1 1) (weaken* ⦃ Kᵣ ⦄ 2 y)
              ■ cong (wkTel u) (swap11-wk y)

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-νν {j} {k} s t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tν (tν t)) es))
    (~-trans (transp-core Tₛ (tν (tν u)) (tν (tν u)) (liftId u (assocSwapᵣ 2 2)) σ σ ξ
                es (wkTel (renTel s j₂)) es₂ (perm-νν Tₛ u) natσ fix)
      (≡→~ (sym (combine-split t₂ es₂ s (tν (tν t)) (map (_⋯ ξ) es)))))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s j₂

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    u : Tel (2 + (2 + i)) (innerOf t (2 + (2 + i)))
    u = renTel t (2 + (2 + i))

    σ : k →ᵣ innerOf t (2 + (2 + i))
    σ = liftRen t (τ ↑* 2 ↑* 2)

    ξ : k →ᵣ k
    ξ = liftId t (assocSwapᵣ 2 2)

    natσ : σ ·ₖ liftId u (assocSwapᵣ 2 2) ≗ ξ ·ₖ σ
    natσ = liftId-liftRen-nat t (τ ↑* 2 ↑* 2) (τ ↑* 2 ↑* 2)
             (assocSwapᵣ 2 2) (assocSwapᵣ 2 2)
             (λ y → sym (dist-↑*-assocSwap 2 2 τ y))

    fix : ∀ y → liftId u (assocSwapᵣ 2 2) (wkTel (tν (tν u)) y) ≡ wkTel (tν (tν u)) y
    fix y = liftId-wkTel u (assocSwapᵣ 2 2)
              (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 y))
              ■ cong (wkTel u) (aswap-wk 2 2 y)

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-φφ {j} {k} s x y t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tφ x (tφ y t)) es))
    (~-trans (transp-core Tₛ (tφ x (tφ y u)) (tφ y (tφ x u))
                (liftId u (assocSwapᵣ 1 1)) σ σ ξ
                es (wkTel (renTel s j₂)) es₂ (perm-φφ Tₛ x y u) natσ fix)
      (≡→~ (sym (combine-split t₂ es₂ s (tφ y (tφ x t)) (map (_⋯ ξ) es)))))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s j₂

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    u : Tel (1 + (1 + i)) (innerOf t (1 + (1 + i)))
    u = renTel t (1 + (1 + i))

    σ : k →ᵣ innerOf t (1 + (1 + i))
    σ = liftRen t (τ ↑ ↑)

    ξ : k →ᵣ k
    ξ = liftId t (assocSwapᵣ 1 1)

    natσ : σ ·ₖ liftId u (assocSwapᵣ 1 1) ≗ ξ ·ₖ σ
    natσ = liftId-liftRen-nat t (τ ↑ ↑) (τ ↑ ↑)
             (assocSwapᵣ 1 1) (assocSwapᵣ 1 1)
             (λ z → sym (dist-↑*-assocSwap 1 1 τ z))

    fix : ∀ z → liftId u (assocSwapᵣ 1 1) (wkTel (tφ x (tφ y u)) z)
                  ≡ wkTel (tφ y (tφ x u)) z
    fix z = liftId-wkTel u (assocSwapᵣ 1 1)
              (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 z))
              ■ cong (wkTel u) (aswap-wk 1 1 z)

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-νφ {j} {k} s x t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tν (tφ x t)) es))
    (~-trans (transp-core Tₛ (tν (tφ x u)) (tφ x (tν u))
                (liftId u (assocSwapᵣ 1 2)) σ σ′ ξ
                es (wkTel (renTel s j₂)) es₂ (perm-νφ Tₛ x u) natσ fix)
      (≡→~ (sym (combine-split t₂ es₂ s (tφ x (tν t)) (map (_⋯ ξ) es)))))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s j₂

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    u : Tel (1 + (2 + i)) (innerOf t (1 + (2 + i)))
    u = renTel t (1 + (2 + i))

    σ : k →ᵣ innerOf t (1 + (2 + i))
    σ = liftRen t (τ ↑* 2 ↑)

    σ′ : k →ᵣ innerOf t (1 + (2 + i))
    σ′ = liftRen t (τ ↑ ↑* 2)

    ξ : k →ᵣ k
    ξ = liftId t (assocSwapᵣ 1 2)

    natσ : σ ·ₖ liftId u (assocSwapᵣ 1 2) ≗ ξ ·ₖ σ′
    natσ = liftId-liftRen-nat t (τ ↑* 2 ↑) (τ ↑ ↑* 2)
             (assocSwapᵣ 1 2) (assocSwapᵣ 1 2)
             (λ z → sym (dist-↑*-assocSwap 1 2 τ z))

    fix : ∀ z → liftId u (assocSwapᵣ 1 2) (wkTel (tν (tφ x u)) z)
                  ≡ wkTel (tφ x (tν u)) z
    fix z = liftId-wkTel u (assocSwapᵣ 1 2)
              (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 2 z))
              ■ cong (wkTel u) (aswap-wk 1 2 z)

------------------------------------------------------------------------
-- The congruence.
------------------------------------------------------------------------

combine-congˡ : ∀ {n} {N₁ N₁′ : NF n} (N₂ : NF n) →
                N₁ ~ N₁′ → combine N₁ N₂ ~ combine N₁′ N₂
combine-congˡ N₂ = ~-lift (λ N → combine N N₂) (combine-cong₁ N₂)
