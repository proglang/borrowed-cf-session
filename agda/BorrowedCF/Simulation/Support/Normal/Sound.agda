-- | Soundness of the normal form: `≋` becomes `~`.
--
--   The twelve ≋′ generators split into three kinds.
--
--     * The four binder transpositions are EXACTLY Normal.Equiv's generators,
--       once `nf-nat` (Normal.Nat) has turned the generator's body renaming into
--       `renNF` and `nf-endo` (Normal.Endo) has re-based it back — they fire at
--       the head, so the prefix telescope is `[]`.
--     * ∥-unit′ is the `unit-del` generator; ∥-assoc′, ν-ext′ and φ-ext′ are
--       outright EQUALITIES of normal forms — `combine` already associates and
--       already extrudes binders, which is what makes `nf` a normaliser at all.
--     * ∥-comm′ is the only one with real content: `combine` puts its second
--       argument's telescope outermost, so commuting the two sides has to move
--       a whole telescope past another one.
module BorrowedCF.Simulation.Support.Normal.Sound where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo
open import BorrowedCF.Simulation.Support.Normal.CongL using (combine-congˡ)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; nf-nat; innerOf-renTel; innerOf-++ᵗ; renTel-renTel; renTel-++ᵗ;
         wkTel-renTel; wkTel-nat; liftRen-·; liftRen-++ᵗ; liftRen-cong;
         subst-tν; subst-tφ; subst-++ᵗ; subst-++; subst-■; subst-wkTel;
         map-fuse; map-⋯-subst; map-++ᴸ)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Equalities are equivalences.
------------------------------------------------------------------------

≡→~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ N₂
≡→~ refl = ~-refl

------------------------------------------------------------------------
-- The spent unit thread.
------------------------------------------------------------------------

unit-combine : ∀ {n} (N : NF n) →
               combine (mkNF [] (K `unit ∷ [])) N ≡ mkNF (tel N) (K `unit ∷ thr N)
unit-combine (mkNF t es) =
  NF-≡ refl (++ᵗ-idʳ t) (cong (K `unit ∷_) (map-id es))
  where
    map-id : ∀ {k} (xs : List (Tm k)) → map (_⋯ idₖ ⦃ Kᵣ ⦄) xs ≡ xs
    map-id []       = refl
    map-id (x ∷ xs) = cong₂ _∷_ (⋯-id x (λ _ → refl)) (map-id xs)

------------------------------------------------------------------------
-- Binder extrusion: `combine` already does it.
------------------------------------------------------------------------

-- Both sides are `t₂` over `t₁` re-based underneath it; the only difference is
-- WHERE `t₁` gets re-based — at `2 + n` before the merge, or at `j₂` during it —
-- and `renTel-renTel` says that does not matter.
combine-ν : ∀ {n} (N₁ : NF n) (N₂ : NF (2 + n)) →
            νNF (combine (renNF N₁ (2 + n) (weaken* ⦃ Kᵣ ⦄ 2)) N₂) ≡ combine N₁ (νNF N₂)
combine-ν {n} (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  NF-≡ e
    ( subst-tν e (t₂ ++ᵗ renTel (renTel t₁ (2 + n)) j₂)
    ■ cong tν ( subst-++ᵗ t₂ e (renTel (renTel t₁ (2 + n)) j₂)
              ■ cong (t₂ ++ᵗ_) (renTel-renTel t₁ (2 + n) j₂) ) )
    ( cong (subst (λ j → List (Tm j)) e)
           (cong₂ _++_ (map-fuse (liftRen t₁ (weaken* ⦃ Kᵣ ⦄ 2))
                                 (liftRen (renTel t₁ (2 + n)) (wkTel t₂)) es₁)
                       refl)
    ■ subst-++ e _ _
    ■ cong₂ _++_ (map-⋯-subst e (liftRen-· t₁ (weaken* ⦃ Kᵣ ⦄ 2) (wkTel t₂)) es₁)
                 (map-⋯-subst e (wkTel-renTel t₁ (2 + n) j₂) es₂) )
  where
    e : innerOf (renTel t₁ (2 + n)) j₂ ≡ innerOf t₁ j₂
    e = innerOf-renTel t₁ (2 + n) j₂

combine-φ : ∀ {n} (f : Flag) (N₁ : NF n) (N₂ : NF (1 + n)) →
            φNF f (combine (renNF N₁ (1 + n) (weaken* ⦃ Kᵣ ⦄ 1)) N₂) ≡ combine N₁ (φNF f N₂)
combine-φ {n} f (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  NF-≡ e
    ( subst-tφ e f (t₂ ++ᵗ renTel (renTel t₁ (1 + n)) j₂)
    ■ cong (tφ f) ( subst-++ᵗ t₂ e (renTel (renTel t₁ (1 + n)) j₂)
                  ■ cong (t₂ ++ᵗ_) (renTel-renTel t₁ (1 + n) j₂) ) )
    ( cong (subst (λ j → List (Tm j)) e)
           (cong₂ _++_ (map-fuse (liftRen t₁ (weaken* ⦃ Kᵣ ⦄ 1))
                                 (liftRen (renTel t₁ (1 + n)) (wkTel t₂)) es₁)
                       refl)
    ■ subst-++ e _ _
    ■ cong₂ _++_ (map-⋯-subst e (liftRen-· t₁ (weaken* ⦃ Kᵣ ⦄ 1) (wkTel t₂)) es₁)
                 (map-⋯-subst e (wkTel-renTel t₁ (1 + n) j₂) es₂) )
  where
    e : innerOf (renTel t₁ (1 + n)) j₂ ≡ innerOf t₁ j₂
    e = innerOf-renTel t₁ (1 + n) j₂

------------------------------------------------------------------------
-- `combine` associates.
------------------------------------------------------------------------

-- Nesting three telescopes is associative, and so are the three renamings the
-- threads pick up; `wkTel-nat` is what makes the two middle ones meet.
combine-assoc : ∀ {n} (N₁ N₂ N₃ : NF n) →
                combine (combine N₁ N₂) N₃ ≡ combine N₁ (combine N₂ N₃)
combine-assoc (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) (mkNF {j₃} t₃ es₃) =
  NF-≡ e telEq thrEq
  where
    j₂₃ : ℕ
    j₂₃ = innerOf t₂ j₃

    T₁₂ : Tel _ (innerOf t₁ j₂)
    T₁₂ = t₂ ++ᵗ renTel t₁ j₂

    T₂₃ : Tel _ j₂₃
    T₂₃ = t₃ ++ᵗ renTel t₂ j₃

    e₁ : innerOf T₁₂ j₃ ≡ innerOf (renTel t₁ j₂) j₂₃
    e₁ = innerOf-++ᵗ t₂ (renTel t₁ j₂) j₃

    e₂ : innerOf (renTel t₁ j₂) j₂₃ ≡ innerOf t₁ j₂₃
    e₂ = innerOf-renTel t₁ j₂ j₂₃

    e : innerOf T₁₂ j₃ ≡ innerOf t₁ j₂₃
    e = e₁ ■ e₂

    telEq : subst (Tel _) e (t₃ ++ᵗ renTel T₁₂ j₃)
              ≡ T₂₃ ++ᵗ renTel t₁ j₂₃
    telEq = subst-++ᵗ t₃ e (renTel T₁₂ j₃)
              ■ cong (t₃ ++ᵗ_)
                  ( subst-■ (Tel j₃) e₁ e₂ (renTel T₁₂ j₃)
                  ■ cong (subst (Tel j₃) e₂) (renTel-++ᵗ t₂ (renTel t₁ j₂) j₃)
                  ■ subst-++ᵗ (renTel t₂ j₃) e₂ (renTel (renTel t₁ j₂) j₂₃)
                  ■ cong (renTel t₂ j₃ ++ᵗ_) (renTel-renTel t₁ j₂ j₂₃) )
              ■ sym (++ᵗ-assoc t₃ (renTel t₂ j₃) (renTel t₁ j₂₃))

    -- es₁ : both routes weaken through t₂ and then through t₃.
    r₁ : ∀ x → subst 𝔽 e
                 ((liftRen t₁ (wkTel t₂) ·ₖ liftRen T₁₂ (wkTel t₃)) x)
                 ≡ liftRen t₁ (wkTel T₂₃) x
    r₁ x = subst-■ 𝔽 e₁ e₂ _
             ■ cong (subst 𝔽 e₂)
                 (liftRen-++ᵗ t₂ (renTel t₁ j₂) (wkTel t₃) (liftRen t₁ (wkTel t₂) x))
             ■ liftRen-· t₁ (wkTel t₂) (liftRen t₂ (wkTel t₃)) x
             ■ liftRen-cong t₁
                 (λ y → sym (wkTel-++ᵗ t₃ (renTel t₂ j₃) y ■ wkTel-nat t₂ (wkTel t₃) y)) x

    -- es₂ : the middle argument crosses t₁'s re-basing.
    r₂ : ∀ x → subst 𝔽 e
                 ((wkTel (renTel t₁ j₂) ·ₖ liftRen T₁₂ (wkTel t₃)) x)
                 ≡ (liftRen t₂ (wkTel t₃) ·ₖ wkTel (renTel t₁ j₂₃)) x
    r₂ x = subst-■ 𝔽 e₁ e₂ _
             ■ cong (subst 𝔽 e₂)
                 ( liftRen-++ᵗ t₂ (renTel t₁ j₂) (wkTel t₃) (wkTel (renTel t₁ j₂) x)
                 ■ sym (wkTel-nat (renTel t₁ j₂) (liftRen t₂ (wkTel t₃)) x) )
             ■ wkTel-renTel t₁ j₂ j₂₃ (liftRen t₂ (wkTel t₃) x)

    -- es₃ : pure weakening on both routes.
    r₃ : ∀ x → subst 𝔽 e (wkTel (renTel T₁₂ j₃) x)
                 ≡ (wkTel (renTel t₂ j₃) ·ₖ wkTel (renTel t₁ j₂₃)) x
    r₃ x = subst-■ 𝔽 e₁ e₂ _
             ■ cong (subst 𝔽 e₂)
                 ( subst-wkTel e₁ (renTel T₁₂ j₃) x
                 ■ cong (λ T → wkTel T x) (renTel-++ᵗ t₂ (renTel t₁ j₂) j₃)
                 ■ wkTel-++ᵗ (renTel t₂ j₃) (renTel (renTel t₁ j₂) j₂₃) x )
             ■ wkTel-renTel t₁ j₂ j₂₃ (wkTel (renTel t₂ j₃) x)

    thrEq : subst (λ j → List (Tm j)) e
              ( map (_⋯ liftRen T₁₂ (wkTel t₃))
                    ( map (_⋯ liftRen t₁ (wkTel t₂)) es₁
                   ++ map (_⋯ wkTel (renTel t₁ j₂)) es₂ )
             ++ map (_⋯ wkTel (renTel T₁₂ j₃)) es₃ )
              ≡ map (_⋯ liftRen t₁ (wkTel T₂₃)) es₁
             ++ map (_⋯ wkTel (renTel t₁ j₂₃))
                    ( map (_⋯ liftRen t₂ (wkTel t₃)) es₂
                   ++ map (_⋯ wkTel (renTel t₂ j₃)) es₃ )
    thrEq =
      cong (subst (λ j → List (Tm j)) e)
        (cong (_++ map (_⋯ wkTel (renTel T₁₂ j₃)) es₃)
          ( map-++ᴸ (liftRen T₁₂ (wkTel t₃))
              (map (_⋯ liftRen t₁ (wkTel t₂)) es₁)
              (map (_⋯ wkTel (renTel t₁ j₂)) es₂)
          ■ cong₂ _++_ (map-fuse (liftRen t₁ (wkTel t₂)) (liftRen T₁₂ (wkTel t₃)) es₁)
                       (map-fuse (wkTel (renTel t₁ j₂)) (liftRen T₁₂ (wkTel t₃)) es₂) ))
        ■ cong (subst (λ j → List (Tm j)) e)
            (++-assoc (map (_⋯ (liftRen t₁ (wkTel t₂) ·ₖ liftRen T₁₂ (wkTel t₃))) es₁)
                      (map (_⋯ (wkTel (renTel t₁ j₂) ·ₖ liftRen T₁₂ (wkTel t₃))) es₂)
                      (map (_⋯ wkTel (renTel T₁₂ j₃)) es₃))
        ■ subst-++ e _ _
        ■ cong₂ _++_ (map-⋯-subst e r₁ es₁)
                     ( subst-++ e _ _
                     ■ cong₂ _++_ (map-⋯-subst e r₂ es₂) (map-⋯-subst e r₃ es₃)
                     ■ sym ( map-++ᴸ (wkTel (renTel t₁ j₂₃))
                               (map (_⋯ liftRen t₂ (wkTel t₃)) es₂)
                               (map (_⋯ wkTel (renTel t₂ j₃)) es₃)
                           ■ cong₂ _++_
                               (map-fuse (liftRen t₂ (wkTel t₃))
                                         (wkTel (renTel t₁ j₂₃)) es₂)
                               (map-fuse (wkTel (renTel t₂ j₃))
                                         (wkTel (renTel t₁ j₂₃)) es₃) ) )

------------------------------------------------------------------------
-- Soundness.
------------------------------------------------------------------------

≋′⇒~ : ∀ {n} {P Q : Proc n} → P ≋′ Q → nf P ~ nf Q

≋′⇒~ (∥-unit′ {P = P}) =
  ~-trans (≡→~ (unit-combine (nf P))) (Eq*.return (unit-del (tel (nf P)) (thr (nf P))))

≋′⇒~ (ν-swap′ {P = P}) =
  ~-trans (Eq*.return (perm-ν1 [] (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong νNF (nf-endo P (swapᵣ 1 1)))))

≋′⇒~ (ν-comm′ {P = P}) =
  ~-trans (Eq*.return (perm-νν [] (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → νNF (νNF N)) (nf-endo P (assocSwapᵣ 2 2)))))

≋′⇒~ (φ-comm′ {P = P} {x} {y}) =
  ~-trans (Eq*.return (perm-φφ [] x y (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → φNF y (φNF x N)) (nf-endo P (assocSwapᵣ 1 1)))))

≋′⇒~ (νφ-comm′ {P = P} {x}) =
  ~-trans (Eq*.return (perm-νφ [] x (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → φNF x (νNF N)) (nf-endo P (assocSwapᵣ 1 2)))))

≋′⇒~ (ν-cong′ c) = ~-νNF (≋′⇒~ c)
≋′⇒~ (φ-cong′ c) = ~-φNF (≋′⇒~ c)

≋′⇒~ ∥-comm′  = {!   !}
≋′⇒~ (∥-assoc′ {P₁ = P₁} {P₂} {P₃}) =
  ≡→~ (sym (combine-assoc (nf P₁) (nf P₂) (nf P₃)))
≋′⇒~ (ν-ext′ {P = P} {Q = Q}) =
  ≡→~ ( sym (combine-ν (nf P) (nf Q))
      ■ cong (λ N → νNF (combine N (nf Q))) (sym (nf-nat P (weaken* ⦃ Kᵣ ⦄ 2))) )

≋′⇒~ (φ-ext′ {P = P} {Q = Q} {x}) =
  ≡→~ ( sym (combine-φ x (nf P) (nf Q))
      ■ cong (λ N → φNF x (combine N (nf Q))) (sym (nf-nat P (weaken* ⦃ Kᵣ ⦄ 1))) )
≋′⇒~ (∥-cong′ {Q = Q} c) = combine-congˡ (nf Q) (≋′⇒~ c)

-- The equivalence closure, one link at a time.  `Eq*.gmap` does not apply: a
-- single ≋′ generator can take several ~ steps (∥-unit′ takes one equality and
-- one generator), so the image is `~`, not `~₁`.
≋⇒~ : ∀ {n} {P Q : Proc n} → P ≋ Q → nf P ~ nf Q
≋⇒~ ε           = ~-refl
≋⇒~ (fwd g ◅ c) = ~-trans (≋′⇒~ g)         (≋⇒~ c)
≋⇒~ (bwd g ◅ c) = ~-trans (~-sym (≋′⇒~ g)) (≋⇒~ c)
