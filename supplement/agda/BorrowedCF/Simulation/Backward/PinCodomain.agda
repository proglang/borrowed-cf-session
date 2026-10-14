-- | Backward simulation, RU-LSplit — Stage D toolkit: the POINTED
--   THREAD-REPLACEMENT congruence of `~`.
--
--   A `~` derivation (Normal.Equiv) survives replacing ONE tracked live
--   thread on both of its ends: every generator acts on the thread list by
--   `map (_⋯ ρ)` (with `ρ` a concrete invertible renaming), by a `↭`, or by
--   deleting a spent `K \`unit` head — and all three commute with a pointed
--   replacement (`setAt`).  A live tracked thread is never the deleted unit,
--   so the replacement survives `unit-del` too.
--
--       ~-replace : N₁ ~ N₂ → (i : u ∈ thr N₁) → live u → (v : Tm _) →
--         Σ ρ  Σ (i′ : (u ⋯ ρ) ∈ thr N₂)
--           (mkNF (tel N₁) (setAt i v) ~ mkNF (tel N₂) (setAt i′ (v ⋯ ρ)))
--
--   This is the nf-level conjugation piece of PinLSplit's remaining Stage-D
--   hole (`C[reduct] ≈ U[ P′ ] σ`): conjugate the input ≋ through `≋⇒~`,
--   replace the pinned redex thread by its reduct on both ends, then close
--   with `~⇒≋` / `≋⇒≈`.  The remaining assembly (the pointed presentation of
--   `nf (C [ ν (⟪ T ⟫ ∥ P₁) ]ᴷ)` and the identification of the replaced
--   image list with `nf (U[ P′ ] σ)` via the reduct handle equations) is
--   OPEN — see the hole in PinLSplit.
--
--   STATUS: CLOSED (no holes).
module BorrowedCF.Simulation.Backward.PinCodomain where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Processes.Translation using (U[_])
open import BorrowedCF.Simulation.Support.StepDecomp
  using (Ctx*; ∘ᴷ; _∥ᴷ_; _ᴷ∥_; νᴷ; φᴷ; _[_]ᴷ)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen)
open import BorrowedCF.Simulation.Support.Normal.Flat using (live)
open import BorrowedCF.Simulation.Support.Normal.Sound using (≡→~; ≋⇒~)
open import BorrowedCF.Simulation.Support.Normal.Witness using (~₁-witness)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BScope; BTel; Bσ; image-block-~)
open import BorrowedCF.Simulation.Support.TypedPrenex using (prenexᵗ; tel; thr)
import BorrowedCF.Simulation.Support.Normal.Witness as W
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Simulation.Backward.PinBase using (live-ren; unit-dead)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; prep; swap)
  renaming (refl to ↭refl; trans to ↭tr)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using ()
  renaming (fwd to sfwd; bwd to sbwd)

open Nat.Variables

------------------------------------------------------------------------
-- Pointed replacement in a list, and its interaction with map / ↭.
------------------------------------------------------------------------

setAt : ∀ {A : Set} {u : A} {es : List A} → u ∈ es → A → List A
setAt {es = _ ∷ es} (here _)  v = v ∷ es
setAt {es = e ∷ es} (there i) v = e ∷ setAt i v

∈-mapᴾ : ∀ {A B : Set} (f : A → B) {x : A} {xs : List A} →
         x ∈ xs → f x ∈ map f xs
∈-mapᴾ f (here refl) = here refl
∈-mapᴾ f (there i)   = there (∈-mapᴾ f i)

map-setAt : ∀ {A B : Set} (f : A → B) {x : A} {xs : List A}
            (i : x ∈ xs) (v : A) →
            map f (setAt i v) ≡ setAt (∈-mapᴾ f i) (f v)
map-setAt f (here refl) v = refl
map-setAt f {xs = x ∷ xs} (there i) v = cong (f x ∷_) (map-setAt f i v)

setAt-subst : ∀ {A : Set} {x y : A} {es : List A} (eq : x ≡ y)
              (i : x ∈ es) (v : A) →
              setAt (subst (_∈ es) eq i) v ≡ setAt i v
setAt-subst refl i v = refl

-- Positional inversion of a map-membership: the preimage sits at the SAME
-- position, so replacement commutes on the nose.
map-∈ᴾ⁻ : ∀ {A B : Set} (f : A → B) (es : List A) {y : B}
          (i : y ∈ map f es) →
          Σ[ x ∈ A ] Σ[ j ∈ (x ∈ es) ]
            ((y ≡ f x) × (∀ (w : A) → setAt i (f w) ≡ map f (setAt j w)))
map-∈ᴾ⁻ f (x ∷ es) (here px) = x , here refl , px , λ _ → refl
map-∈ᴾ⁻ f (x ∷ es) (there i)
  with x′ , j , yeq , se ← map-∈ᴾ⁻ f es i
  = x′ , there j , yeq , λ w → cong (f x ∷_) (se w)

-- Pointed permutation: a membership survives a ↭ together with replacement.
↭-setAt : ∀ {A : Set} {es es′ : List A} (p : es ↭ es′) {u : A}
          (i : u ∈ es) (v : A) →
          Σ[ i′ ∈ (u ∈ es′) ] (setAt i v ↭ setAt i′ v)
↭-setAt ↭refl i v = i , ↭-refl
↭-setAt (prep x p) (here px) v = here px , prep v p
↭-setAt (prep x p) (there i) v
  with i′ , rel ← ↭-setAt p i v = there i′ , prep x rel
↭-setAt (swap x y p) (here px) v = there (here px) , swap v y p
↭-setAt (swap x y p) (there (here py)) v = here py , swap x v p
↭-setAt (swap x y p) (there (there i)) v
  with i′ , rel ← ↭-setAt p i v = there (there i′) , swap x y rel
↭-setAt (↭tr p q) i v
  with i′  , rel₁ ← ↭-setAt p i  v
  with i′′ , rel₂ ← ↭-setAt q i′ v
  = i′′ , ↭tr rel₁ rel₂

------------------------------------------------------------------------
-- One generator, forward.
------------------------------------------------------------------------

Replaced : ∀ {n} (N₁ N₂ : NF n) (u : Tm (inner N₁)) (i : u ∈ thr N₁)
           (v : Tm (inner N₁)) → Set
Replaced N₁ N₂ u i v =
  Σ[ ρ ∈ (inner N₁ →ᵣ inner N₂) ] Σ[ i′ ∈ ((u ⋯ ρ) ∈ thr N₂) ]
    (mkNF (tel N₁) (setAt i v) ~ mkNF (tel N₂) (setAt i′ (v ⋯ ρ)))

~₁-replace : ∀ {n} {N₁ N₂ : NF n} (g : N₁ ~₁ N₂)
             {u : Tm (inner N₁)} (i : u ∈ thr N₁) → live u ≡ u ∷ [] →
             (v : Tm (inner N₁)) → Replaced N₁ N₂ u i v
~₁-replace (perm-ν1 s t es) i lu v =
  liftId t (swapᵣ 1 1) , ∈-mapᴾ (_⋯ liftId t (swapᵣ 1 1)) i ,
  ~-trans (sfwd (perm-ν1 s t (setAt i v)) ◅ ε)
    (≡→~ (cong (mkNF (s ++ᵗ tν t)) (map-setAt (_⋯ liftId t (swapᵣ 1 1)) i v)))
~₁-replace (perm-νν s t es) i lu v =
  liftId t (assocSwapᵣ 2 2) , ∈-mapᴾ (_⋯ liftId t (assocSwapᵣ 2 2)) i ,
  ~-trans (sfwd (perm-νν s t (setAt i v)) ◅ ε)
    (≡→~ (cong (mkNF (s ++ᵗ tν (tν t))) (map-setAt (_⋯ liftId t (assocSwapᵣ 2 2)) i v)))
~₁-replace (perm-φφ s x y t es) i lu v =
  liftId t (assocSwapᵣ 1 1) , ∈-mapᴾ (_⋯ liftId t (assocSwapᵣ 1 1)) i ,
  ~-trans (sfwd (perm-φφ s x y t (setAt i v)) ◅ ε)
    (≡→~ (cong (mkNF (s ++ᵗ tφ y (tφ x t))) (map-setAt (_⋯ liftId t (assocSwapᵣ 1 1)) i v)))
~₁-replace (perm-νφ s x t es) i lu v =
  liftId t (assocSwapᵣ 1 2) , ∈-mapᴾ (_⋯ liftId t (assocSwapᵣ 1 2)) i ,
  ~-trans (sfwd (perm-νφ s x t (setAt i v)) ◅ ε)
    (≡→~ (cong (mkNF (s ++ᵗ tφ x (tν t))) (map-setAt (_⋯ liftId t (assocSwapᵣ 1 2)) i v)))
~₁-replace (perm-thr t p) {u} i lu v
  with i₀ , rel ← ↭-setAt p i v
  = idₖ , subst (_∈ _) (sym (⋯-id u (λ _ → refl))) i₀ ,
    ~-trans (sfwd (perm-thr t rel) ◅ ε)
      (≡→~ (cong (mkNF t)
        (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) i₀ (v ⋯ idₖ)
             ■ cong (setAt i₀) (⋯-id v (λ _ → refl)) ))))
~₁-replace (unit-del t es) (here q)  lu v = ⊥-elim (unit-dead q lu)
~₁-replace (unit-del t es) {u} (there j) lu v =
  idₖ , subst (_∈ _) (sym (⋯-id u (λ _ → refl))) j ,
  ~-trans (sfwd (unit-del t (setAt j v)) ◅ ε)
    (≡→~ (cong (mkNF t)
      (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) j (v ⋯ idₖ)
           ■ cong (setAt j) (⋯-id v (λ _ → refl)) ))))

------------------------------------------------------------------------
-- One generator, backward.
------------------------------------------------------------------------

-- The four transpositions share one skeleton: invert the map-membership
-- positionally (`map-∈ᴾ⁻`), undo the renaming with the generator's witness
-- inverse (`~₁-witness`), and replay the SAME generator instance on the
-- replaced list, backwards.  All four are scope ENDOs, so no transport
-- appears.

~₁-replace⁻ : ∀ {n} {N₂ N₁ : NF n} (g : N₂ ~₁ N₁)
              {u : Tm (inner N₁)} (i : u ∈ thr N₁) → live u ≡ u ∷ [] →
              (v : Tm (inner N₁)) → Replaced N₁ N₂ u i v
~₁-replace⁻ g@(perm-ν1 s t es) {u} i lu v
  with x , j , yeq , se ← map-∈ᴾ⁻ (_⋯ W.fwd (~₁-witness g)) es i
  = back where
  w = ~₁-witness g
  xeq : x ≡ u ⋯ W.bwd w
  xeq = sym (cong (_⋯ W.bwd w) yeq ■ fusion x (W.fwd w) (W.bwd w) ■ ⋯-id x (W.inv₁ w))
  back : Replaced _ _ u i v
  back = W.bwd w , subst (_∈ es) xeq j ,
    ~-trans (≡→~ (cong (mkNF (s ++ᵗ tν t))
              (sym (sym (se (v ⋯ W.bwd w))
                    ■ cong (setAt i) (fusion v (W.bwd w) (W.fwd w) ■ ⋯-id v (W.inv₂ w))))))
    (~-trans (sbwd (perm-ν1 s t (setAt j (v ⋯ W.bwd w))) ◅ ε)
      (≡→~ (cong (mkNF (s ++ᵗ tν t)) (sym (setAt-subst xeq j (v ⋯ W.bwd w))))))
~₁-replace⁻ g@(perm-νν s t es) {u} i lu v
  with x , j , yeq , se ← map-∈ᴾ⁻ (_⋯ W.fwd (~₁-witness g)) es i
  = back where
  w = ~₁-witness g
  xeq : x ≡ u ⋯ W.bwd w
  xeq = sym (cong (_⋯ W.bwd w) yeq ■ fusion x (W.fwd w) (W.bwd w) ■ ⋯-id x (W.inv₁ w))
  back : Replaced _ _ u i v
  back = W.bwd w , subst (_∈ es) xeq j ,
    ~-trans (≡→~ (cong (mkNF (s ++ᵗ tν (tν t)))
              (sym (sym (se (v ⋯ W.bwd w))
                    ■ cong (setAt i) (fusion v (W.bwd w) (W.fwd w) ■ ⋯-id v (W.inv₂ w))))))
    (~-trans (sbwd (perm-νν s t (setAt j (v ⋯ W.bwd w))) ◅ ε)
      (≡→~ (cong (mkNF (s ++ᵗ tν (tν t))) (sym (setAt-subst xeq j (v ⋯ W.bwd w))))))
~₁-replace⁻ g@(perm-φφ s x′ y′ t es) {u} i lu v
  with x , j , yeq , se ← map-∈ᴾ⁻ (_⋯ W.fwd (~₁-witness g)) es i
  = back where
  w = ~₁-witness g
  xeq : x ≡ u ⋯ W.bwd w
  xeq = sym (cong (_⋯ W.bwd w) yeq ■ fusion x (W.fwd w) (W.bwd w) ■ ⋯-id x (W.inv₁ w))
  back : Replaced _ _ u i v
  back = W.bwd w , subst (_∈ es) xeq j ,
    ~-trans (≡→~ (cong (mkNF (s ++ᵗ tφ y′ (tφ x′ t)))
              (sym (sym (se (v ⋯ W.bwd w))
                    ■ cong (setAt i) (fusion v (W.bwd w) (W.fwd w) ■ ⋯-id v (W.inv₂ w))))))
    (~-trans (sbwd (perm-φφ s x′ y′ t (setAt j (v ⋯ W.bwd w))) ◅ ε)
      (≡→~ (cong (mkNF (s ++ᵗ tφ x′ (tφ y′ t))) (sym (setAt-subst xeq j (v ⋯ W.bwd w))))))
~₁-replace⁻ g@(perm-νφ s x′ t es) {u} i lu v
  with x , j , yeq , se ← map-∈ᴾ⁻ (_⋯ W.fwd (~₁-witness g)) es i
  = back where
  w = ~₁-witness g
  xeq : x ≡ u ⋯ W.bwd w
  xeq = sym (cong (_⋯ W.bwd w) yeq ■ fusion x (W.fwd w) (W.bwd w) ■ ⋯-id x (W.inv₁ w))
  back : Replaced _ _ u i v
  back = W.bwd w , subst (_∈ es) xeq j ,
    ~-trans (≡→~ (cong (mkNF (s ++ᵗ tφ x′ (tν t)))
              (sym (sym (se (v ⋯ W.bwd w))
                    ■ cong (setAt i) (fusion v (W.bwd w) (W.fwd w) ■ ⋯-id v (W.inv₂ w))))))
    (~-trans (sbwd (perm-νφ s x′ t (setAt j (v ⋯ W.bwd w))) ◅ ε)
      (≡→~ (cong (mkNF (s ++ᵗ tν (tφ x′ t))) (sym (setAt-subst xeq j (v ⋯ W.bwd w))))))
~₁-replace⁻ (perm-thr t p) {u} i lu v
  with i₀ , rel ← ↭-setAt (↭-sym p) i v
  = idₖ , subst (_∈ _) (sym (⋯-id u (λ _ → refl))) i₀ ,
    ~-trans (sfwd (perm-thr t rel) ◅ ε)
      (≡→~ (cong (mkNF t)
        (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) i₀ (v ⋯ idₖ)
             ■ cong (setAt i₀) (⋯-id v (λ _ → refl)) ))))
~₁-replace⁻ (unit-del t es) {u} i lu v =
  idₖ , there (subst (_∈ _) (sym (⋯-id u (λ _ → refl))) i) ,
  ~-trans (sbwd (unit-del t (setAt i v)) ◅ ε)
    (≡→~ (cong (mkNF t)
      (cong (K `unit ∷_)
        (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) i (v ⋯ idₖ)
             ■ cong (setAt i) (⋯-id v (λ _ → refl)) )))))

------------------------------------------------------------------------
-- The star: a whole ~ derivation survives pointed replacement.
------------------------------------------------------------------------

~-replace : ∀ {n} {N₁ N₂ : NF n} (d : N₁ ~ N₂)
            {u : Tm (inner N₁)} (i : u ∈ thr N₁) → live u ≡ u ∷ [] →
            (v : Tm (inner N₁)) → Replaced N₁ N₂ u i v
~-replace {N₁ = N₁} ε {u} i lu v =
  idₖ , subst (_∈ _) (sym (⋯-id u (λ _ → refl))) i ,
  ≡→~ (cong (mkNF (tel N₁))
    (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) i (v ⋯ idₖ)
         ■ cong (setAt i) (⋯-id v (λ _ → refl)) )))
~-replace (sfwd g ◅ d) {u} i lu v
  with ρ₁ , i₁ , rel₁ ← ~₁-replace g i lu v
  with ρ₂ , i₂ , rel₂ ← ~-replace d i₁ (live-ren ρ₁ lu) (v ⋯ ρ₁)
  = (ρ₁ ·ₖ ρ₂) , subst (_∈ _) (fusion u ρ₁ ρ₂) i₂ ,
    ~-trans rel₁ (~-trans rel₂
      (≡→~ (cong (mkNF _)
        (sym ( setAt-subst (fusion u ρ₁ ρ₂) i₂ (v ⋯ (ρ₁ ·ₖ ρ₂))
             ■ cong (setAt i₂) (sym (fusion v ρ₁ ρ₂)) )))))
~-replace (sbwd g ◅ d) {u} i lu v
  with ρ₁ , i₁ , rel₁ ← ~₁-replace⁻ g i lu v
  with ρ₂ , i₂ , rel₂ ← ~-replace d i₁ (live-ren ρ₁ lu) (v ⋯ ρ₁)
  = (ρ₁ ·ₖ ρ₂) , subst (_∈ _) (fusion u ρ₁ ρ₂) i₂ ,
    ~-trans rel₁ (~-trans rel₂
      (≡→~ (cong (mkNF _)
        (sym ( setAt-subst (fusion u ρ₁ ρ₂) i₂ (v ⋯ (ρ₁ ·ₖ ρ₂))
             ■ cong (setAt i₂) (sym (fusion v ρ₁ ρ₂)) )))))

-- Process-level corollary: an ≋ survives replacing a tracked live thread of
-- the two normal forms.
≋-replace : ∀ {n} {P Q : Proc n} (c : P ≋ Q)
            {u : Tm (inner (nf P))} (i : u ∈ thr (nf P)) → live u ≡ u ∷ [] →
            (v : Tm (inner (nf P))) → Replaced (nf P) (nf Q) u i v
≋-replace c = ~-replace (≋⇒~ c)

------------------------------------------------------------------------
-- Pointed replacement through a one-hole context: `nf (C [ X ]ᴷ)` depends
-- on the redex thread only through ONE entry of its thread list.
------------------------------------------------------------------------

∈-++ˡᴾ : ∀ {A : Set} {u : A} {xs ys : List A} → u ∈ xs → u ∈ xs ++ ys
∈-++ˡᴾ (here px) = here px
∈-++ˡᴾ (there i) = there (∈-++ˡᴾ i)

∈-++ʳᴾ : ∀ {A : Set} {u : A} (xs : List A) {ys : List A} → u ∈ ys → u ∈ xs ++ ys
∈-++ʳᴾ []       i = i
∈-++ʳᴾ (x ∷ xs) i = there (∈-++ʳᴾ xs i)

setAt-++ˡ : ∀ {A : Set} {u : A} {xs : List A} (ys : List A) (i : u ∈ xs) (v : A) →
            setAt (∈-++ˡᴾ {ys = ys} i) v ≡ setAt i v ++ ys
setAt-++ˡ ys (here px) v = refl
setAt-++ˡ {xs = x ∷ xs} ys (there i) v = cong (x ∷_) (setAt-++ˡ ys i v)

setAt-++ʳ : ∀ {A : Set} {u : A} (xs : List A) {ys : List A} (i : u ∈ ys) (v : A) →
            setAt (∈-++ʳᴾ xs i) v ≡ xs ++ setAt i v
setAt-++ʳ []       i v = refl
setAt-++ʳ (x ∷ xs) i v = cong (x ∷_) (setAt-++ʳ xs i v)

ctx-replace :
  ∀ {n k} (C : Ctx* n k) {X X′ : Proc k}
    {u : Tm (inner (nf X))} (i : u ∈ thr (nf X)) (w : Tm (inner (nf X)))
  → nf X′ ≡ mkNF (tel (nf X)) (setAt i w)
  → Σ[ ρ ∈ (inner (nf X) →ᵣ inner (nf (C [ X ]ᴷ))) ]
    Σ[ i′ ∈ ((u ⋯ ρ) ∈ thr (nf (C [ X ]ᴷ))) ]
      (nf (C [ X′ ]ᴷ) ≡ mkNF (tel (nf (C [ X ]ᴷ))) (setAt i′ (w ⋯ ρ)))
ctx-replace ∘ᴷ {X} {u = u} i w eq =
  idₖ , subst (_∈ thr (nf X)) (sym (⋯-id u (λ _ → refl))) i ,
  ( eq ■ cong (mkNF (tel (nf X)))
          (sym ( setAt-subst (sym (⋯-id u (λ _ → refl))) i (w ⋯ idₖ)
               ■ cong (setAt i) (⋯-id w (λ _ → refl)) )) )
ctx-replace (C ∥ᴷ Q) {X} {X′} {u} i w eq
  with ρ₀ , i₀ , eq₀ ← ctx-replace C {X} {X′} i w eq =
  let t₁   = tel (nf (C [ X ]ᴷ))
      lft  = liftRen t₁ (wkTel (tel (nf Q)))
      mapQ = map (_⋯ wkTel (renTel t₁ (inner (nf Q)))) (thr (nf Q))
      j    = ∈-++ˡᴾ {ys = mapQ} (∈-mapᴾ (_⋯ lft) i₀)
  in
    (ρ₀ ·ₖ lft)
  , subst (_∈ _) (fusion u ρ₀ lft) j
  , ( cong (λ N → combine N (nf Q)) eq₀
    ■ cong (mkNF (tel (nf ((C [ X ]ᴷ) ∥ Q))))
        ( cong (_++ mapQ) (map-setAt (_⋯ lft) i₀ (w ⋯ ρ₀))
        ■ sym (setAt-++ˡ mapQ (∈-mapᴾ (_⋯ lft) i₀) ((w ⋯ ρ₀) ⋯ lft))
        ■ sym ( setAt-subst (fusion u ρ₀ lft) j (w ⋯ (ρ₀ ·ₖ lft))
              ■ cong (setAt j) (sym (fusion w ρ₀ lft)) ) ) )
ctx-replace (P ᴷ∥ C) {X} {X′} {u} i w eq
  with ρ₀ , i₀ , eq₀ ← ctx-replace C {X} {X′} i w eq =
  let tC   = tel (nf (C [ X ]ᴷ))
      ρʳ   = wkTel (renTel (tel (nf P)) (inner (nf (C [ X ]ᴷ))))
      mapP = map (_⋯ liftRen (tel (nf P)) (wkTel tC)) (thr (nf P))
      j    = ∈-++ʳᴾ mapP (∈-mapᴾ (_⋯ ρʳ) i₀)
  in
    (ρ₀ ·ₖ ρʳ)
  , subst (_∈ _) (fusion u ρ₀ ρʳ) j
  , ( cong (λ N → combine (nf P) N) eq₀
    ■ cong (mkNF (tel (nf (P ∥ (C [ X ]ᴷ)))))
        ( cong (mapP ++_) (map-setAt (_⋯ ρʳ) i₀ (w ⋯ ρ₀))
        ■ sym (setAt-++ʳ mapP (∈-mapᴾ (_⋯ ρʳ) i₀) ((w ⋯ ρ₀) ⋯ ρʳ))
        ■ sym ( setAt-subst (fusion u ρ₀ ρʳ) j (w ⋯ (ρ₀ ·ₖ ρʳ))
              ■ cong (setAt j) (sym (fusion w ρ₀ ρʳ)) ) ) )
ctx-replace (νᴷ C) {X} {X′} i w eq
  with ρ₀ , i₀ , eq₀ ← ctx-replace C {X} {X′} i w eq
  = ρ₀ , i₀ , cong (λ N → mkNF (tν (tel N)) (thr N)) eq₀
ctx-replace (φᴷ f C) {X} {X′} i w eq
  with ρ₀ , i₀ , eq₀ ← ctx-replace C {X} {X′} i w eq
  = ρ₀ , i₀ , cong (λ N → mkNF (tφ f (tel N)) (thr N)) eq₀

------------------------------------------------------------------------
-- The Stage-D headline available TODAY: the normal form of the REDUCT in
-- context is `~` to the image's block normal form with exactly ONE entry
-- replaced by the reduct thread.  The residual gap to PinLSplit's hole is
-- the identification of that replaced list with `nf (U[ P′ ] σ)` (the
-- reduct handle equations, SplitsLQ-scale) — see the module header.
------------------------------------------------------------------------

-- Replacing the ν-body's redex thread is invisible to the normal form
-- except at the head entry of its thread list.
redex-replace :
  ∀ {k} (T T′ : Tm (2 + k)) (P₁ : Proc (2 + k)) →
  nf (ν (⟪ T′ ⟫ ∥ P₁))
    ≡ mkNF (tel (nf (ν (⟪ T ⟫ ∥ P₁))))
           (setAt {es = thr (nf (ν (⟪ T ⟫ ∥ P₁)))} (here refl)
                  (T′ ⋯ wkTel (tel (nf P₁))))
redex-replace T T′ P₁ = refl

reduct-image-~ :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n)
    {k} (C : Ctx* n k) {T T′ : Tm (2 + k)} {P₁ : Proc (2 + k)} →
  live T ≡ T ∷ [] →
  C [ ν (⟪ T ⟫ ∥ P₁) ]ᴷ ≋ U[ P ] σ →
  Σ[ ρ ∈ ((2 + k) →ᵣ BScope (tel (prenexᵗ P)) n) ]
  Σ[ i′ ∈ ((T ⋯ ρ) ∈ (map (_⋯ Bσ (tel (prenexᵗ P)) σ) (thr (prenexᵗ P)) ++ K `unit ∷ [])) ]
    (nf (C [ ν (⟪ T′ ⟫ ∥ P₁) ]ᴷ)
       ~ mkNF (BTel (tel (prenexᵗ P)) n) (setAt i′ (T′ ⋯ ρ)))
reduct-image-~ P σ C {T} {T′} {P₁} lt c
  with ρC , iC , eqC ← ctx-replace C {X = ν (⟪ T ⟫ ∥ P₁)} {X′ = ν (⟪ T′ ⟫ ∥ P₁)}
         (here refl) (T′ ⋯ wkTel (tel (nf P₁))) (redex-replace T T′ P₁)
  with ρd , i′ , rel ← ~-replace
         (~-trans (≋⇒~ c) (image-block-~ P σ))
         iC (live-ren ρC (live-ren (wkTel (tel (nf P₁))) lt))
         ((T′ ⋯ wkTel (tel (nf P₁))) ⋯ ρC)
  = let
      ρF   = (wkTel (tel (nf P₁)) ·ₖ ρC) ·ₖ ρd
      fixT = cong (_⋯ ρd) (fusion T (wkTel (tel (nf P₁))) ρC)
           ■ fusion T (wkTel (tel (nf P₁)) ·ₖ ρC) ρd
    in
      ρF
    , subst (_∈ _) fixT i′
    , ~-trans (≡→~ eqC)
        (~-trans rel
          (≡→~ (cong (mkNF (BTel (tel (prenexᵗ P)) _))
            ( cong (setAt i′)
                (cong (_⋯ ρd) (fusion T′ (wkTel (tel (nf P₁))) ρC)
                 ■ fusion T′ (wkTel (tel (nf P₁)) ·ₖ ρC) ρd)
            ■ sym (setAt-subst fixT i′ (T′ ⋯ ρF)) ))))
