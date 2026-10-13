-- | Front-peeling a `msg` atom, tracking the payload type up to `_≃_`.
--
--   `Types.AtomCons` proves `≃-cons` / `atom-;-cons` only for atoms that are
--   NOT `msg p T`, because the equivalence rule `≃𝕊-msg` rewrites the payload
--   and so the atom itself is not preserved along `_≃_`.  The communication
--   rules need precisely the `msg` case, so this module redoes `≃-cons` with
--   the payload carried as an extra existential.  Nothing else changes: every
--   other case of the transport is the one from `Types.AtomCons`.
module BorrowedCF.Safety.Preservation.Support.ConsMsg where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomSnoc using (ClosedAtom; end; msg; ret; acq)
open import BorrowedCF.Types.AtomCons

open Nat.Variables

private variable
  w w₁ w₂ z z₁ z₂ z′ : 𝕊 n

-- | `w ≃ msg p T′ ; z′` for SOME payload `T′` equivalent to `T`, with the
--   suffix determined up to `_≃_`.
ConsMR : 𝕊 n → Pol → 𝕋 → 𝕊 n → Set
ConsMR w p T z = ∃[ T′ ] ∃[ z′ ] T ≃ T′ × Cons (msg p T′) w z′ × z ≃ z′

private
  step : SymClosure _≃𝕊_ w₁ w₂ → Cons (msg p T) w₁ z → ConsMR w₂ p T z
  step (fwd (≃𝕊-msg x)) here = _ , _ , x , here , ≃-refl
  step (bwd (≃𝕊-msg x)) here = _ , _ , ≃-sym x , here , ≃-refl
  step (fwd ≃𝕊-μ) c = _ , _ , ≃-refl , cons-unfold msg c , ≃-refl
  step (bwd ≃𝕊-μ) c =
    let z₂ , c₂ = cons-unfold⁻¹ msg c in
    _ , _ , ≃-refl , c₂ , cons-suffix-unique msg c (cons-unfold msg c₂)
  step (fwd (≃𝕊-;₁ x)) (hd c) =
    let _ , _ , e , c₂ , ez = step (fwd x) c in _ , _ , e , hd c₂ , ≃-; ez ≃-refl
  step (fwd (≃𝕊-;₁ x)) (tl Sk c) = _ , _ , ≃-refl , tl (≃-skips (Eq*.return x) Sk) c , ≃-refl
  step (bwd (≃𝕊-;₁ x)) (hd c) =
    let _ , _ , e , c₂ , ez = step (bwd x) c in _ , _ , e , hd c₂ , ≃-; ez ≃-refl
  step (bwd (≃𝕊-;₁ x)) (tl Sk c) = _ , _ , ≃-refl , tl (≃-skips (≃-sym (Eq*.return x)) Sk) c , ≃-refl
  step (fwd (≃𝕊-;₂ x)) (hd c) = _ , _ , ≃-refl , hd c , ≃-; ≃-refl (Eq*.return x)
  step (fwd (≃𝕊-;₂ x)) (tl Sk c) =
    let _ , _ , e , c₂ , ez = step (fwd x) c in _ , _ , e , tl Sk c₂ , ez
  step (bwd (≃𝕊-;₂ x)) (hd c) = _ , _ , ≃-refl , hd c , ≃-; ≃-refl (≃-sym (Eq*.return x))
  step (bwd (≃𝕊-;₂ x)) (tl Sk c) =
    let _ , _ , e , c₂ , ez = step (bwd x) c in _ , _ , e , tl Sk c₂ , ez
  step (fwd ≃𝕊-skipˡ) (hd c) = ⊥-elim (skips⊥cons msg skip c)
  step (fwd ≃𝕊-skipˡ) (tl _ c) = _ , _ , ≃-refl , c , ≃-refl
  step (bwd ≃𝕊-skipˡ) c = _ , _ , ≃-refl , tl skip c , ≃-refl
  step (fwd ≃𝕊-skipʳ) (hd c) = _ , _ , ≃-refl , c , ≃-skipʳ
  step (fwd ≃𝕊-skipʳ) (tl _ c) = ⊥-elim (skips⊥cons msg skip c)
  step (bwd ≃𝕊-skipʳ) c = _ , _ , ≃-refl , hd c , ≃-sym ≃-skipʳ
  step (fwd ≃𝕊-assoc) (hd (hd c)) = _ , _ , ≃-refl , hd c , ≃-assoc-;
  step (fwd ≃𝕊-assoc) (hd (tl Sk c)) = _ , _ , ≃-refl , tl Sk (hd c) , ≃-refl
  step (fwd ≃𝕊-assoc) (tl (Sk₁ ; Sk₂) c) = _ , _ , ≃-refl , tl Sk₁ (tl Sk₂ c) , ≃-refl
  step (bwd ≃𝕊-assoc) (hd c) = _ , _ , ≃-refl , hd (hd c) , ≃-sym ≃-assoc-;
  step (bwd ≃𝕊-assoc) (tl Sk (hd c)) = _ , _ , ≃-refl , hd (tl Sk c) , ≃-refl
  step (bwd ≃𝕊-assoc) (tl Sk₁ (tl Sk₂ c)) = _ , _ , ≃-refl , tl (Sk₁ ; Sk₂) c , ≃-refl
  step (fwd ≃𝕊-distr) (hd c) = ⊥-elim (¬cons-brn msg c)
  step (fwd ≃𝕊-distr) (tl () _)
  step (fwd (≃𝕊-brn₁ x)) c = ⊥-elim (¬cons-brn msg c)
  step (fwd (≃𝕊-brn₂ x)) c = ⊥-elim (¬cons-brn msg c)
  step (bwd ≃𝕊-distr) c = ⊥-elim (¬cons-brn msg c)
  step (bwd (≃𝕊-brn₁ x)) c = ⊥-elim (¬cons-brn msg c)
  step (bwd (≃𝕊-brn₂ x)) c = ⊥-elim (¬cons-brn msg c)

-- | `_≃_` transports a `msg`-headed decomposition, changing the payload only
--   up to `_≃_`.
≃-consM : w₁ ≃ w₂ → Cons (msg p T) w₁ z → ConsMR w₂ p T z
≃-consM refl c = _ , _ , ≃-refl , c , ≃-refl
≃-consM (x ◅ xs) c =
  let _ , _ , e , c₂ , ez = step x c in
  let _ , _ , e′ , c₃ , ez′ = ≃-consM xs c₂ in
  _ , _ , ≃-trans e e′ , c₃ , ≃-trans ez ez′

-- | An atom in front of an atom is that atom, and nothing is left over.
cons-atom-skip : {a b : 𝕊 n} → Atom b → Cons a b z → b ≡ a × z ≡ skip
cons-atom-skip B here = refl , refl
cons-atom-skip B (hd _) = case B of λ ()
cons-atom-skip B (tl _ _) = case B of λ ()
cons-atom-skip B (mu _) = case B of λ ()

-- | An atom equivalent to a `msg`-headed session IS a `msg`.
msg-;-atom : {b t : 𝕊 n} → Atom b → b ≃ msg p T ; t → ∃[ T′ ] b ≡ msg p T′
msg-;-atom B eq = let _ , _ , _ , c , _ = ≃-consM (≃-sym eq) (hd here) in _ , cons-atom⁻ B c

-- | THE PAYOFF: the `msg` front split, the `msg` companion of
--   `Types.AtomCons.atom-;-cons`.
msg-;-cons : {x y t : 𝕊 n} → x ; y ≃ msg p T ; t →
  (Skips x × ∃[ T′ ] (T ≃ T′) × (y ≃ msg p T′ ; t))
  ⊎ (∃[ T′ ] ∃[ h ] (T ≃ T′) × (x ≃ msg p T′ ; h) × (h ; y ≃ t))
msg-;-cons {T = T} {x = x} {y} {t} eq
  with _ , _ , T≃ , c , skt≃z₂ ← ≃-consM (≃-sym eq) (hd here)
  with c
... | hd c₁ = inj₂ (_ , _ , T≃ , cons-sound c₁ , ≃-trans (≃-sym skt≃z₂) ≃-skipˡ)
... | tl Sk c₂ =
  inj₁ (Sk , _ , T≃
       , ≃-trans (cons-sound c₂)
           (≃-; ≃-refl (≃-sym (≃-trans (≃-sym ≃-skipˡ) skt≃z₂))))

-- | Two `msg`-headed sessions with the same polarity agree on payload and tail.
msg-cancel : msg {n} p T₁ ; s₁ ≃ msg p T₂ ; s₂ → T₁ ≃ T₂ × s₁ ≃ s₂
msg-cancel {s₁ = s₁} {s₂ = s₂} eq
  with _ , _ , T≃ , c , sks₁≃ ← ≃-consM eq (hd here)
  with c
... | tl Sk _ = ⊥-elim (¬skips-atom msg Sk)
... | hd c₁
  with refl , refl ← cons-atom-skip msg c₁ =
  T≃ , ≃-trans (≃-sym ≃-skipˡ) (≃-trans sks₁≃ ≃-skipˡ)
