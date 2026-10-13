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
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; innerOf-++ᵗ; renTel-++ᵗ; liftRen-++ᵗ; subst-++ᵗ; subst-++;
         subst-wkTel; map-fuse; map-++ᴸ; map-⋯-subst;
         innerOf-renTel; renTel-renTel; renTel-cong; liftRen-·; liftRen-cong;
         wkTel-renTel; wkTel-nat; subst-tν; subst-tφ; joinSubst)

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
    ≡ mkNF ((t₂ ++ᵗ renTel s (wkTel t₂)) ++ᵗ renTel w (liftRen s (wkTel t₂)))
           ( map (_⋯ liftRen w (liftRen s (wkTel t₂))) es
          ++ map (_⋯ (wkTel (renTel s (wkTel t₂)) ·ₖ wkTel (renTel w (liftRen s (wkTel t₂))))) es₂ )
combine-split {n} {j₂} t₂ es₂ s w es = NF-≡ e telEq thrEq
  where
    e : innerOf (s ++ᵗ w) j₂ ≡ innerOf w (innerOf s j₂)
    e = innerOf-++ᵗ s w j₂

    telEq : subst (Tel n) e (t₂ ++ᵗ renTel (s ++ᵗ w) (wkTel t₂))
              ≡ (t₂ ++ᵗ renTel s (wkTel t₂)) ++ᵗ renTel w (liftRen s (wkTel t₂))
    telEq = subst-++ᵗ t₂ e (renTel (s ++ᵗ w) (wkTel t₂))
              ■ cong (t₂ ++ᵗ_) (renTel-++ᵗ s w (wkTel t₂))
              ■ sym (++ᵗ-assoc t₂ (renTel s (wkTel t₂)) (renTel w (liftRen s (wkTel t₂))))

    h₁ : ∀ x → subst 𝔽 e (liftRen (s ++ᵗ w) (wkTel t₂) x)
                 ≡ liftRen w (liftRen s (wkTel t₂)) x
    h₁ = liftRen-++ᵗ s w (wkTel t₂)

    h₂ : ∀ y → subst 𝔽 e (wkTel (renTel (s ++ᵗ w) (wkTel t₂)) y)
                 ≡ (wkTel (renTel s (wkTel t₂)) ·ₖ wkTel (renTel w (liftRen s (wkTel t₂)))) y
    h₂ y = subst-wkTel e (renTel (s ++ᵗ w) (wkTel t₂)) y
             ■ cong (λ T → wkTel T y) (renTel-++ᵗ s w (wkTel t₂))
             ■ wkTel-++ᵗ (renTel s (wkTel t₂)) (renTel w (liftRen s (wkTel t₂))) y

    thrEq : subst (λ i → List (Tm i)) e
              ( map (_⋯ liftRen (s ++ᵗ w) (wkTel t₂)) es
             ++ map (_⋯ wkTel (renTel (s ++ᵗ w) (wkTel t₂))) es₂ )
              ≡ map (_⋯ liftRen w (liftRen s (wkTel t₂))) es
             ++ map (_⋯ (wkTel (renTel s (wkTel t₂)) ·ₖ wkTel (renTel w (liftRen s (wkTel t₂))))) es₂
    thrEq = subst-++ e _ _ ■ cong₂ _++_ (map-⋯-subst e h₁ es) (map-⋯-subst e h₂ es₂)

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
-- that it rewrites the whole thread list by `ζ`.  Under linked-φ `ζ` re-bases
-- the inner scope (`W` and `W′` sit at propositionally-equal but distinct
-- scopes `k`/`k′`), which is why `ζ : k →ᵣ k′`; the two `combine`-thread blocks
-- come out as `map (_⋯ (σ ·ₖ ζ))` / `map (_⋯ (κ ·ₖ wkTel W′))`, and each case
-- reconciles those against `combine`'s image with a `NF-≡` transport.
transp-core : ∀ {n i j k k′ j₂} (Tₛ : Tel n i) (W : Tel i k) (W′ : Tel i k′)
                (ζ : k →ᵣ k′) (σ : j →ᵣ k) (κ : j₂ →ᵣ i)
                (es : List (Tm j)) (es₂ : List (Tm j₂)) →
              (∀ (L : List (Tm k)) →
                 mkNF (Tₛ ++ᵗ W) L ~₁ mkNF (Tₛ ++ᵗ W′) (map (_⋯ ζ) L)) →
              (∀ y → ζ (wkTel W y) ≡ wkTel W′ y) →
              mkNF (Tₛ ++ᵗ W)  (map (_⋯ σ)       es ++ map (_⋯ (κ ·ₖ wkTel W))  es₂)
                ~ mkNF (Tₛ ++ᵗ W′) (map (_⋯ (σ ·ₖ ζ)) es ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂)
transp-core Tₛ W W′ ζ σ κ es es₂ gen fix =
  ~-trans (Eq*.return (gen _)) (≡→~ (cong (mkNF (Tₛ ++ᵗ W′)) eq))
  where
    eq : map (_⋯ ζ) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel W)) es₂)
           ≡ map (_⋯ (σ ·ₖ ζ)) es ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂
    eq = map-++ᴸ ζ (map (_⋯ σ) es) (map (_⋯ (κ ·ₖ wkTel W)) es₂)
           ■ cong₂ _++_
               (map-fuse σ ζ es)
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
    (~-trans (transp-core Tₛ (tν u) (tν (renTel u sw)) (liftRen u sw) σ κ es es₂
                (perm-ν1 Tₛ u) fix)
      (≡→~ finalEq))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s (wkTel t₂)

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    κ : j₂ →ᵣ i
    κ = wkTel (renTel s (wkTel t₂))

    sw : (2 + i) →ᵣ (2 + i)
    sw = swapᵣ 1 1

    sw′ : (2 + j) →ᵣ (2 + j)
    sw′ = swapᵣ 1 1

    u : Tel (2 + i) (innerOf t (2 + i))
    u = renTel t (τ ↑* 2)

    σ : k →ᵣ innerOf t (2 + i)
    σ = liftRen t (τ ↑* 2)

    v : Tel (2 + i) (innerOf (renTel t sw′) (2 + i))
    v = renTel (renTel t sw′) (τ ↑* 2)

    fix : ∀ y → liftRen u sw (wkTel (tν u) y) ≡ wkTel (tν (renTel u sw)) y
    fix y = sym (wkTel-nat u sw (weaken* ⦃ Kᵣ ⦄ 2 y))
              ■ cong (wkTel (renTel u sw)) (swap11-wk y)

    -- the two inner scopes `combine`'s image and the fired generator produce
    p : innerOf (renTel t (τ ↑* 2)) (2 + i) ≡ innerOf t (2 + i)
    p = innerOf-renTel t (τ ↑* 2) (2 + i)

    q : innerOf (renTel t sw′) (2 + i) ≡ innerOf t (2 + i)
    q = innerOf-renTel t sw′ (2 + i)

    e : innerOf (renTel t (τ ↑* 2)) (2 + i) ≡ innerOf (renTel t sw′) (2 + i)
    e = p ■ sym q

    comm : (τ ↑* 2) ·ₖ sw ≗ sw′ ·ₖ (τ ↑* 2)
    comm z = sym (dist-↑*-swap 1 1 τ z)

    telEq : subst (Tel (2 + i)) e (renTel u sw) ≡ v
    telEq = joinSubst (Tel (2 + i)) p q (renTel u sw) v
              (renTel-renTel t (τ ↑* 2) sw
                 ■ renTel-cong t comm
                 ■ sym (renTel-renTel t sw′ (τ ↑* 2)))

    thr₁ : ∀ z → subst 𝔽 e ((σ ·ₖ liftRen u sw) z)
                   ≡ (liftRen t sw′ ·ₖ liftRen (renTel t sw′) (τ ↑* 2)) z
    thr₁ z = joinSubst 𝔽 p q _ _
               (liftRen-· t (τ ↑* 2) sw z
                  ■ liftRen-cong t comm z
                  ■ sym (liftRen-· t sw′ (τ ↑* 2) z))

    thr₂ : ∀ y → subst 𝔽 e ((κ ·ₖ wkTel (tν (renTel u sw))) y)
                   ≡ (κ ·ₖ wkTel (tν v)) y
    thr₂ y = joinSubst 𝔽 p q _ _
               (wkTel-renTel t (τ ↑* 2) sw (weaken* ⦃ Kᵣ ⦄ 2 (κ y))
                  ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 2 (κ y))) (renTel-cong t comm)
                  ■ sym (wkTel-renTel t sw′ (τ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 (κ y))))

    finalEq :
      mkNF (Tₛ ++ᵗ tν (renTel u sw))
           (map (_⋯ (σ ·ₖ liftRen u sw)) es ++ map (_⋯ (κ ·ₖ wkTel (tν (renTel u sw)))) es₂)
        ≡ combine (mkNF (s ++ᵗ tν (renTel t sw′)) (map (_⋯ liftRen t sw′) es)) (mkNF t₂ es₂)
    finalEq =
      NF-≡ e
        (subst-++ᵗ Tₛ e (tν (renTel u sw))
           ■ cong (Tₛ ++ᵗ_) (subst-tν e (renTel u sw) ■ cong tν telEq))
        (subst-++ e _ _
           ■ cong₂ _++_
               (map-⋯-subst e thr₁ es
                  ■ sym (map-fuse (liftRen t sw′) (liftRen (renTel t sw′) (τ ↑* 2)) es))
               (map-⋯-subst e thr₂ es₂))
      ■ sym (combine-split t₂ es₂ s (tν (renTel t sw′)) (map (_⋯ liftRen t sw′) es))

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-νν {j} {k} s t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tν (tν t)) es))
    (~-trans (transp-core Tₛ (tν (tν u)) (tν (tν (renTel u sw))) (liftRen u sw) σ κ es es₂
                (perm-νν Tₛ u) fix)
      (≡→~ finalEq))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s (wkTel t₂)

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    κ : j₂ →ᵣ i
    κ = wkTel (renTel s (wkTel t₂))

    sw : (2 + (2 + i)) →ᵣ (2 + (2 + i))
    sw = assocSwapᵣ 2 2

    sw′ : (2 + (2 + j)) →ᵣ (2 + (2 + j))
    sw′ = assocSwapᵣ 2 2

    u : Tel (2 + (2 + i)) (innerOf t (2 + (2 + i)))
    u = renTel t (τ ↑* 2 ↑* 2)

    σ : k →ᵣ innerOf t (2 + (2 + i))
    σ = liftRen t (τ ↑* 2 ↑* 2)

    v : Tel (2 + (2 + i)) (innerOf (renTel t sw′) (2 + (2 + i)))
    v = renTel (renTel t sw′) (τ ↑* 2 ↑* 2)

    fix : ∀ y → liftRen u sw (wkTel (tν (tν u)) y) ≡ wkTel (tν (tν (renTel u sw))) y
    fix y = sym (wkTel-nat u sw (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 y)))
              ■ cong (wkTel (renTel u sw)) (aswap-wk 2 2 y)

    p : innerOf (renTel t (τ ↑* 2 ↑* 2)) (2 + (2 + i)) ≡ innerOf t (2 + (2 + i))
    p = innerOf-renTel t (τ ↑* 2 ↑* 2) (2 + (2 + i))

    q : innerOf (renTel t sw′) (2 + (2 + i)) ≡ innerOf t (2 + (2 + i))
    q = innerOf-renTel t sw′ (2 + (2 + i))

    e : innerOf (renTel t (τ ↑* 2 ↑* 2)) (2 + (2 + i)) ≡ innerOf (renTel t sw′) (2 + (2 + i))
    e = p ■ sym q

    comm : (τ ↑* 2 ↑* 2) ·ₖ sw ≗ sw′ ·ₖ (τ ↑* 2 ↑* 2)
    comm z = sym (dist-↑*-assocSwap 2 2 τ z)

    telEq : subst (Tel (2 + (2 + i))) e (renTel u sw) ≡ v
    telEq = joinSubst (Tel (2 + (2 + i))) p q (renTel u sw) v
              (renTel-renTel t (τ ↑* 2 ↑* 2) sw
                 ■ renTel-cong t comm
                 ■ sym (renTel-renTel t sw′ (τ ↑* 2 ↑* 2)))

    thr₁ : ∀ z → subst 𝔽 e ((σ ·ₖ liftRen u sw) z)
                   ≡ (liftRen t sw′ ·ₖ liftRen (renTel t sw′) (τ ↑* 2 ↑* 2)) z
    thr₁ z = joinSubst 𝔽 p q _ _
               (liftRen-· t (τ ↑* 2 ↑* 2) sw z
                  ■ liftRen-cong t comm z
                  ■ sym (liftRen-· t sw′ (τ ↑* 2 ↑* 2) z))

    thr₂ : ∀ y → subst 𝔽 e ((κ ·ₖ wkTel (tν (tν (renTel u sw)))) y)
                   ≡ (κ ·ₖ wkTel (tν (tν v))) y
    thr₂ y = joinSubst 𝔽 p q _ _
               (wkTel-renTel t (τ ↑* 2 ↑* 2) sw (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 (κ y)))
                  ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 (κ y)))) (renTel-cong t comm)
                  ■ sym (wkTel-renTel t sw′ (τ ↑* 2 ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 (κ y)))))

    finalEq :
      mkNF (Tₛ ++ᵗ tν (tν (renTel u sw)))
           (map (_⋯ (σ ·ₖ liftRen u sw)) es ++ map (_⋯ (κ ·ₖ wkTel (tν (tν (renTel u sw))))) es₂)
        ≡ combine (mkNF (s ++ᵗ tν (tν (renTel t sw′))) (map (_⋯ liftRen t sw′) es)) (mkNF t₂ es₂)
    finalEq =
      NF-≡ e
        (subst-++ᵗ Tₛ e (tν (tν (renTel u sw)))
           ■ cong (Tₛ ++ᵗ_)
               (subst-tν e (tν (renTel u sw))
                  ■ cong tν (subst-tν e (renTel u sw) ■ cong tν telEq)))
        (subst-++ e _ _
           ■ cong₂ _++_
               (map-⋯-subst e thr₁ es
                  ■ sym (map-fuse (liftRen t sw′) (liftRen (renTel t sw′) (τ ↑* 2 ↑* 2)) es))
               (map-⋯-subst e thr₂ es₂))
      ■ sym (combine-split t₂ es₂ s (tν (tν (renTel t sw′))) (map (_⋯ liftRen t sw′) es))

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-φφ {j} {k} s x y c d t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t)) es ■ wRw))
    (~-trans (transp-core Tₛ Wg W′ (liftRen U sw) σ κ es es₂
                (perm-φφ Tₛ x y (c ⋯ τ) (d ⋯ τ) U) fix)
      (≡→~ finalEq))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s (wkTel t₂)

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    κ : j₂ →ᵣ i
    κ = wkTel (renTel s (wkTel t₂))

    sw : (1 + (1 + i)) →ᵣ (1 + (1 + i))
    sw = assocSwapᵣ 1 1

    sw′ : (1 + (1 + j)) →ᵣ (1 + (1 + j))
    sw′ = assocSwapᵣ 1 1

    U : Tel (1 + (1 + i)) (innerOf t (1 + (1 + i)))
    U = renTel t (τ ↑ ↑)

    σ : k →ᵣ innerOf t (1 + (1 + i))
    σ = liftRen t (τ ↑ ↑)

    -- the channel-weakening naturality that lets the fired cell re-form
    chanNat : ∀ (e : Tm j) →
              e ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ (τ ↑) ≡ e ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 1
    chanNat e = fusion e (weaken* ⦃ Kᵣ ⦄ 1) (τ ↑)
                  ■ ⋯-cong e (λ z → sym (↑*-wk τ 1 z))
                  ■ sym (fusion e τ (weaken* ⦃ Kᵣ ⦄ 1))

    Wg : Tel i (innerOf t (1 + (1 + i)))
    Wg = tφ x (c ⋯ τ) (tφ y (d ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 1) U)

    W′ : Tel i (innerOf (renTel t (τ ↑ ↑)) (1 + (1 + i)))
    W′ = tφ y (d ⋯ τ) (tφ x (c ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel U sw))

    wRw : mkNF (Tₛ ++ᵗ tφ x (c ⋯ τ) (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ (τ ↑)) U))
               (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel (tφ x (c ⋯ τ) (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ (τ ↑)) U)))) es₂)
        ≡ mkNF (Tₛ ++ᵗ Wg) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel Wg)) es₂)
    wRw = cong (λ W → mkNF (Tₛ ++ᵗ W) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel W)) es₂))
               (cong (λ ch → tφ x (c ⋯ τ) (tφ y ch U)) (chanNat d))

    fix : ∀ z → liftRen U sw (wkTel Wg z) ≡ wkTel W′ z
    fix z = sym (wkTel-nat U sw (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 z)))
              ■ cong (wkTel (renTel U sw)) (aswap-wk 1 1 z)

    p : innerOf (renTel t (τ ↑ ↑)) (1 + (1 + i)) ≡ innerOf t (1 + (1 + i))
    p = innerOf-renTel t (τ ↑ ↑) (1 + (1 + i))

    q : innerOf (renTel t sw′) (1 + (1 + i)) ≡ innerOf t (1 + (1 + i))
    q = innerOf-renTel t sw′ (1 + (1 + i))

    e : innerOf (renTel t (τ ↑ ↑)) (1 + (1 + i)) ≡ innerOf (renTel t sw′) (1 + (1 + i))
    e = p ■ sym q

    comm : (τ ↑ ↑) ·ₖ sw ≗ sw′ ·ₖ (τ ↑ ↑)
    comm z = sym (dist-↑*-assocSwap 1 1 τ z)

    v : Tel (1 + (1 + i)) (innerOf (renTel t sw′) (1 + (1 + i)))
    v = renTel (renTel t sw′) (τ ↑ ↑)

    telEq : subst (Tel (1 + (1 + i))) e (renTel U sw) ≡ v
    telEq = joinSubst (Tel (1 + (1 + i))) p q (renTel U sw) v
              (renTel-renTel t (τ ↑ ↑) sw
                 ■ renTel-cong t comm
                 ■ sym (renTel-renTel t sw′ (τ ↑ ↑)))

    thr₁ : ∀ z → subst 𝔽 e ((σ ·ₖ liftRen U sw) z)
                   ≡ (liftRen t sw′ ·ₖ liftRen (renTel t sw′) (τ ↑ ↑)) z
    thr₁ z = joinSubst 𝔽 p q _ _
               (liftRen-· t (τ ↑ ↑) sw z
                  ■ liftRen-cong t comm z
                  ■ sym (liftRen-· t sw′ (τ ↑ ↑) z))

    thr₂ : ∀ z → subst 𝔽 e ((κ ·ₖ wkTel W′) z)
                   ≡ (κ ·ₖ wkTel (tφ y (d ⋯ τ) (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ (τ ↑)) v))) z
    thr₂ z = joinSubst 𝔽 p q _ _
               (wkTel-renTel t (τ ↑ ↑) sw (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))
                  ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))) (renTel-cong t comm)
                  ■ sym (wkTel-renTel t sw′ (τ ↑ ↑) (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))))

    finalEq :
      mkNF (Tₛ ++ᵗ W′)
           (map (_⋯ (σ ·ₖ liftRen U sw)) es ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂)
        ≡ combine (mkNF (s ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t sw′)))
                        (map (_⋯ liftRen t sw′) es))
                  (mkNF t₂ es₂)
    finalEq =
      NF-≡ e
        (subst-++ᵗ Tₛ e W′
           ■ cong (Tₛ ++ᵗ_)
               (subst-tφ e y (d ⋯ τ) (tφ x (c ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel U sw))
                  ■ cong (tφ y (d ⋯ τ))
                      (subst-tφ e x (c ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel U sw)
                         ■ cong₂ (tφ x) (sym (chanNat c)) telEq)))
        (subst-++ e _ _
           ■ cong₂ _++_
               (map-⋯-subst e thr₁ es
                  ■ sym (map-fuse (liftRen t sw′) (liftRen (renTel t sw′) (τ ↑ ↑)) es))
               (map-⋯-subst e thr₂ es₂))
      ■ sym (combine-split t₂ es₂ s (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t sw′)))
               (map (_⋯ liftRen t sw′) es))

combine-cong₁ {n} (mkNF {j₂} t₂ es₂) (perm-νφ {j} {k} s x c t es) =
  ~-trans (≡→~ (combine-split t₂ es₂ s (tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t)) es ■ wRw))
    (~-trans (transp-core Tₛ Wg W′ (liftRen U sw) σ κ es es₂
                (perm-νφ Tₛ x (c ⋯ τ) U) fix)
      (≡→~ finalEq))
  where
    i : ℕ
    i = innerOf s j₂

    Tₛ : Tel n i
    Tₛ = t₂ ++ᵗ renTel s (wkTel t₂)

    τ : j →ᵣ i
    τ = liftRen s (wkTel t₂)

    κ : j₂ →ᵣ i
    κ = wkTel (renTel s (wkTel t₂))

    sw : (1 + (2 + i)) →ᵣ (2 + (1 + i))
    sw = assocSwapᵣ 1 2

    sw′ : (1 + (2 + j)) →ᵣ (2 + (1 + j))
    sw′ = assocSwapᵣ 1 2

    U : Tel (1 + (2 + i)) (innerOf t (1 + (2 + i)))
    U = renTel t (τ ↑* 2 ↑)

    σ : k →ᵣ innerOf t (1 + (2 + i))
    σ = liftRen t (τ ↑* 2 ↑)

    chanNat2 : ∀ (e : Tm j) →
               e ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ (τ ↑* 2) ≡ e ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 2
    chanNat2 e = fusion e (weaken* ⦃ Kᵣ ⦄ 2) (τ ↑* 2)
                   ■ ⋯-cong e (λ z → sym (↑*-wk τ 2 z))
                   ■ sym (fusion e τ (weaken* ⦃ Kᵣ ⦄ 2))

    Wg : Tel i (innerOf t (1 + (2 + i)))
    Wg = tν (tφ x (c ⋯ τ ⋯ weaken* ⦃ Kᵣ ⦄ 2) U)

    W′ : Tel i (innerOf (renTel t (τ ↑* 2 ↑)) (2 + (1 + i)))
    W′ = tφ x (c ⋯ τ) (tν (renTel U sw))

    wRw : mkNF (Tₛ ++ᵗ tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ (τ ↑* 2)) U))
               (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel (tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ (τ ↑* 2)) U)))) es₂)
        ≡ mkNF (Tₛ ++ᵗ Wg) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel Wg)) es₂)
    wRw = cong (λ W → mkNF (Tₛ ++ᵗ W) (map (_⋯ σ) es ++ map (_⋯ (κ ·ₖ wkTel W)) es₂))
               (cong (λ ch → tν (tφ x ch U)) (chanNat2 c))

    fix : ∀ z → liftRen U sw (wkTel Wg z) ≡ wkTel W′ z
    fix z = sym (wkTel-nat U sw (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 2 z)))
              ■ cong (wkTel (renTel U sw)) (aswap-wk 1 2 z)

    p : innerOf (renTel t (τ ↑* 2 ↑)) (2 + (1 + i)) ≡ innerOf t (2 + (1 + i))
    p = innerOf-renTel t (τ ↑* 2 ↑) (2 + (1 + i))

    q : innerOf (renTel t sw′) (2 + (1 + i)) ≡ innerOf t (2 + (1 + i))
    q = innerOf-renTel t sw′ (2 + (1 + i))

    e : innerOf (renTel t (τ ↑* 2 ↑)) (2 + (1 + i)) ≡ innerOf (renTel t sw′) (2 + (1 + i))
    e = p ■ sym q

    comm : (τ ↑* 2 ↑) ·ₖ sw ≗ sw′ ·ₖ (τ ↑ ↑* 2)
    comm z = sym (dist-↑*-assocSwap 1 2 τ z)

    v : Tel (2 + (1 + i)) (innerOf (renTel t sw′) (2 + (1 + i)))
    v = renTel (renTel t sw′) (τ ↑ ↑* 2)

    telEq : subst (Tel (2 + (1 + i))) e (renTel U sw) ≡ v
    telEq = joinSubst (Tel (2 + (1 + i))) p q (renTel U sw) v
              (renTel-renTel t (τ ↑* 2 ↑) sw
                 ■ renTel-cong t comm
                 ■ sym (renTel-renTel t sw′ (τ ↑ ↑* 2)))

    thr₁ : ∀ z → subst 𝔽 e ((σ ·ₖ liftRen U sw) z)
                   ≡ (liftRen t sw′ ·ₖ liftRen (renTel t sw′) (τ ↑ ↑* 2)) z
    thr₁ z = joinSubst 𝔽 p q _ _
               (liftRen-· t (τ ↑* 2 ↑) sw z
                  ■ liftRen-cong t comm z
                  ■ sym (liftRen-· t sw′ (τ ↑ ↑* 2) z))

    thr₂ : ∀ z → subst 𝔽 e ((κ ·ₖ wkTel W′) z)
                   ≡ (κ ·ₖ wkTel (tφ x (c ⋯ τ) (tν v))) z
    thr₂ z = joinSubst 𝔽 p q _ _
               (wkTel-renTel t (τ ↑* 2 ↑) sw (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))
                  ■ cong (λ T → wkTel T (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))) (renTel-cong t comm)
                  ■ sym (wkTel-renTel t sw′ (τ ↑ ↑* 2) (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 1 (κ z)))))

    finalEq :
      mkNF (Tₛ ++ᵗ W′)
           (map (_⋯ (σ ·ₖ liftRen U sw)) es ++ map (_⋯ (κ ·ₖ wkTel W′)) es₂)
        ≡ combine (mkNF (s ++ᵗ tφ x c (tν (renTel t sw′)))
                        (map (_⋯ liftRen t sw′) es))
                  (mkNF t₂ es₂)
    finalEq =
      NF-≡ e
        (subst-++ᵗ Tₛ e W′
           ■ cong (Tₛ ++ᵗ_)
               (subst-tφ e x (c ⋯ τ) (tν (renTel U sw))
                  ■ cong (tφ x (c ⋯ τ)) (subst-tν e (renTel U sw) ■ cong tν telEq)))
        (subst-++ e _ _
           ■ cong₂ _++_
               (map-⋯-subst e thr₁ es
                  ■ sym (map-fuse (liftRen t sw′) (liftRen (renTel t sw′) (τ ↑ ↑* 2)) es))
               (map-⋯-subst e thr₂ es₂))
      ■ sym (combine-split t₂ es₂ s (tφ x c (tν (renTel t sw′))) (map (_⋯ liftRen t sw′) es))

------------------------------------------------------------------------
-- The congruence.
------------------------------------------------------------------------

combine-congˡ : ∀ {n} {N₁ N₁′ : NF n} (N₂ : NF n) →
                N₁ ~ N₁′ → combine N₁ N₂ ~ combine N₁′ N₂
combine-congˡ N₂ = ~-lift (λ N → combine N N₂) (combine-cong₁ N₂)
