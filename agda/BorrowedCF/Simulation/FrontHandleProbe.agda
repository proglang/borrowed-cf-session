module BorrowedCF.Simulation.FrontHandleProbe where

open import Data.Vec.Functional as F using ()
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Terms
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed

import Relation.Binary.Construct.Closure.ReflexiveTransitive as St
import Relation.Binary.Construct.Closure.Symmetric as Sy

open Fin.Patterns

-- Two width-2 blocks.  Position 0F is a USED borrow in both.
-- gA position 1F = < acq . end ? >  (supports the PURE op `acq).
-- g2 position 1F = < end ? >         (supports only the IMPURE op `end, as bc2).
gA : Ctx 2
gA = ⟨ msg ‼ `⊤ ⟩ F.∷ (⟨ acq ; end ⁇ ⟩ F.∷ (λ ()))

g2 : Ctx 2
g2 = ⟨ msg ‼ `⊤ ⟩ F.∷ (⟨ end ⁇ ⟩ F.∷ (λ ()))

------------------------------------------------------------------------
-- POSITIVE (A): a PURE channel op (acq) operates the borrow at 1F while
-- the used borrow at 0F sits as the left (value) component, typed at the
-- honest block order (` 0F);(` 1F).  So the consumed handle is NOT forced
-- to the block front for a pure op  ==>  strict reverse bisim FALSE.
------------------------------------------------------------------------

posA : gA ; ((` 0F) ; (` 1F)) ⊢ (` 0F) ⊗ (K `acq ·¹ (` 1F))
         ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩ ∣ ℙ
posA = T-Weaken (≼-refl (;-cong ≈-refl ∥-unit₁))
         (T-Pair seq seq (T-Var 0F refl)
           (T-AppUnr refl ℙ≤ϵ (T-Const `acq) (T-Var 1F refl)))

------------------------------------------------------------------------
-- POSITIVE (impure, reversed): the IMPURE close op (end ⁇) on borrow 1F
-- types only with 1F pushed to the FRONT of the sequence: (` 1F);(` 0F).
------------------------------------------------------------------------

posImpRev : g2 ; ((` 1F) ; (` 0F)) ⊢ (K (`end ⁇) ·¹ (` 1F)) ⊗ (` 0F)
              ∶ `⊤ ⊗ᴸ ⟨ msg ‼ `⊤ ⟩ ∣ 𝕀
posImpRev = T-Weaken (≼-refl (;-cong ∥-unit₁ ≈-refl))
              (T-Pair seq seq
                (T-AppUnr refl 𝕀≤𝕀
                  (T-Conv {U = ⟨ end ⁇ ⟩ →*M `⊤ ∣ 𝕀} ≃-refl ℙ≤ϵ (T-Const `end))
                  (T-Conv {U = ⟨ end ⁇ ⟩} ≃-refl ℙ≤ϵ (T-Var 1F refl)))
                (T-Var 0F refl))

------------------------------------------------------------------------
-- NEGATIVE (B) machinery: a precedence invariant that the sub-context
-- order (;)= and (||)= must respect.  prec x y g  =  "x is sequenced
-- strictly before y somewhere in g".  We prove it is REFLECTED by ;<=
-- (a tighter context has at least the precedences of a looser one), for
-- x,y that are non-Unr in the ambient context.  Since the honest block
-- (` 0F);(` 1F) has 0F before 1F, any context ;<= it must too; the impure
-- redex's forced contexts (` 1F);(` 0F) and (` 1F)||(` 0F) do NOT.
------------------------------------------------------------------------

infix 4 _∈s_
_∈s_ : {n : ℕ} → 𝔽 n → Struct n → Set
x ∈s (` y)   = x ≡ y
x ∈s []      = ⊥
x ∈s (α ∥ β) = (x ∈s α) ⊎ (x ∈s β)
x ∈s (α ; β) = (x ∈s α) ⊎ (x ∈s β)

prec : {n : ℕ} → 𝔽 n → 𝔽 n → Struct n → Set
prec x y (` z)   = ⊥
prec x y []      = ⊥
prec x y (α ∥ β) = prec x y α ⊎ prec x y β
prec x y (α ; β) = prec x y α ⊎ prec x y β ⊎ (x ∈s α × y ∈s β)

∈s-Unr : {n : ℕ} {Γ : Ctx n} {x : 𝔽 n} {γ : Struct n} → UnrCx Γ γ → x ∈s γ → Unr (Γ x)
∈s-Unr {γ = ` z}   (` u)    refl     = u
∈s-Unr {γ = []}    []       ()
∈s-Unr {γ = α ∥ β} (uα ∥ uβ) (inj₁ i) = ∈s-Unr uα i
∈s-Unr {γ = α ∥ β} (uα ∥ uβ) (inj₂ i) = ∈s-Unr uβ i
∈s-Unr {γ = α ; β} (uα ; uβ) (inj₁ i) = ∈s-Unr uα i
∈s-Unr {γ = α ; β} (uα ; uβ) (inj₂ i) = ∈s-Unr uβ i

prec⇒∈ˡ : {n : ℕ} {x y : 𝔽 n} {γ : Struct n} → prec x y γ → x ∈s γ
prec⇒∈ˡ {γ = α ∥ β} (inj₁ p) = inj₁ (prec⇒∈ˡ p)
prec⇒∈ˡ {γ = α ∥ β} (inj₂ p) = inj₂ (prec⇒∈ˡ p)
prec⇒∈ˡ {γ = α ; β} (inj₁ p) = inj₁ (prec⇒∈ˡ p)
prec⇒∈ˡ {γ = α ; β} (inj₂ (inj₁ p)) = inj₂ (prec⇒∈ˡ p)
prec⇒∈ˡ {γ = α ; β} (inj₂ (inj₂ (xa , yb))) = inj₁ xa

-- occurrence is invariant under context equivalence (no Unr needed)
∈s-go : {n : ℕ} {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n} → Γ ∶ α ≈′ β → x ∈s α → x ∈s β
∈s-go ;′-assoc (inj₁ (inj₁ i)) = inj₁ i
∈s-go ;′-assoc (inj₁ (inj₂ i)) = inj₂ (inj₁ i)
∈s-go ;′-assoc (inj₂ i) = inj₂ (inj₂ i)
∈s-go (;′-cong₁ g) (inj₁ i) = inj₁ (∈s-go g i)
∈s-go (;′-cong₁ g) (inj₂ i) = inj₂ i
∈s-go (;′-cong₂ g) (inj₁ i) = inj₁ i
∈s-go (;′-cong₂ g) (inj₂ i) = inj₂ (∈s-go g i)
∈s-go ∥′-unit (inj₁ i) = i
∈s-go ∥′-unit (inj₂ ())
∈s-go ∥′-assoc (inj₁ (inj₁ i)) = inj₁ i
∈s-go ∥′-assoc (inj₁ (inj₂ i)) = inj₂ (inj₁ i)
∈s-go ∥′-assoc (inj₂ i) = inj₂ (inj₂ i)
∈s-go ∥′-comm (inj₁ i) = inj₂ i
∈s-go ∥′-comm (inj₂ i) = inj₁ i
∈s-go (∥′-cong₁ g) (inj₁ i) = inj₁ (∈s-go g i)
∈s-go (∥′-cong₁ g) (inj₂ i) = inj₂ i
∈s-go (∥′-dup U) i = inj₁ i
∈s-go (∥′-tm-; U) i = i

∈s-go-bwd : {n : ℕ} {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n} → Γ ∶ α ≈′ β → x ∈s β → x ∈s α
∈s-go-bwd ;′-assoc (inj₁ i) = inj₁ (inj₁ i)
∈s-go-bwd ;′-assoc (inj₂ (inj₁ i)) = inj₁ (inj₂ i)
∈s-go-bwd ;′-assoc (inj₂ (inj₂ i)) = inj₂ i
∈s-go-bwd (;′-cong₁ g) (inj₁ i) = inj₁ (∈s-go-bwd g i)
∈s-go-bwd (;′-cong₁ g) (inj₂ i) = inj₂ i
∈s-go-bwd (;′-cong₂ g) (inj₁ i) = inj₁ i
∈s-go-bwd (;′-cong₂ g) (inj₂ i) = inj₂ (∈s-go-bwd g i)
∈s-go-bwd ∥′-unit i = inj₁ i
∈s-go-bwd ∥′-assoc (inj₁ i) = inj₁ (inj₁ i)
∈s-go-bwd ∥′-assoc (inj₂ (inj₁ i)) = inj₁ (inj₂ i)
∈s-go-bwd ∥′-assoc (inj₂ (inj₂ i)) = inj₂ i
∈s-go-bwd ∥′-comm (inj₁ i) = inj₂ i
∈s-go-bwd ∥′-comm (inj₂ i) = inj₁ i
∈s-go-bwd (∥′-cong₁ g) (inj₁ i) = inj₁ (∈s-go-bwd g i)
∈s-go-bwd (∥′-cong₁ g) (inj₂ i) = inj₂ i
∈s-go-bwd (∥′-dup U) (inj₁ i) = i
∈s-go-bwd (∥′-dup U) (inj₂ i) = i
∈s-go-bwd (∥′-tm-; U) i = i

∈s-≈ : {n : ℕ} {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n} → Γ ∶ α ≈ β → x ∈s α → x ∈s β
∈s-≈ St.ε i = i
∈s-≈ (Sy.fwd g St.◅ r) i = ∈s-≈ r (∈s-go g i)
∈s-≈ (Sy.bwd g St.◅ r) i = ∈s-≈ r (∈s-go-bwd g i)

-- occurrence of a non-Unr variable is reflected by ;<=
∈s-refl : {n : ℕ} {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n} →
  Γ ∶ α ≼ β → ¬ Unr (Γ x) → x ∈s β → x ∈s α
∈s-refl (≼-refl e) xu i = ∈s-≈ (≈-sym e) i
∈s-refl (≼-∅ U) xu i = ⊥-elim (xu (∈s-Unr U i))
∈s-refl ≼-wk xu (inj₁ (inj₁ i)) = inj₁ (inj₁ i)
∈s-refl ≼-wk xu (inj₁ (inj₂ i)) = inj₂ (inj₁ i)
∈s-refl ≼-wk xu (inj₂ (inj₁ i)) = inj₁ (inj₂ i)
∈s-refl ≼-wk xu (inj₂ (inj₂ i)) = inj₂ (inj₂ i)
∈s-refl (≼-trans le₁ le₂) xu i = ∈s-refl le₁ xu (∈s-refl le₂ xu i)
∈s-refl (≼-cong-; le₁ le₂) xu (inj₁ i) = inj₁ (∈s-refl le₁ xu i)
∈s-refl (≼-cong-; le₁ le₂) xu (inj₂ i) = inj₂ (∈s-refl le₂ xu i)
∈s-refl (≼-cong-∥ le₁ le₂) xu (inj₁ i) = inj₁ (∈s-refl le₁ xu i)
∈s-refl (≼-cong-∥ le₁ le₂) xu (inj₂ i) = inj₂ (∈s-refl le₂ xu i)

-- precedence is invariant under context equivalence (Unr kills the transmute cross term)
prec-go : {n : ℕ} {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n} →
  Γ ∶ α ≈′ β → ¬ Unr (Γ x) → ¬ Unr (Γ y) → prec x y α → prec x y β
prec-go ;′-assoc xu yu (inj₁ (inj₁ pa)) = inj₁ pa
prec-go ;′-assoc xu yu (inj₁ (inj₂ (inj₁ pb))) = inj₂ (inj₁ (inj₁ pb))
prec-go ;′-assoc xu yu (inj₁ (inj₂ (inj₂ (xa , yb)))) = inj₂ (inj₂ (xa , inj₁ yb))
prec-go ;′-assoc xu yu (inj₂ (inj₁ pc)) = inj₂ (inj₁ (inj₂ (inj₁ pc)))
prec-go ;′-assoc xu yu (inj₂ (inj₂ (inj₁ xa , yc))) = inj₂ (inj₂ (xa , inj₂ yc))
prec-go ;′-assoc xu yu (inj₂ (inj₂ (inj₂ xb , yc))) = inj₂ (inj₁ (inj₂ (inj₂ (xb , yc))))
prec-go (;′-cong₁ g) xu yu (inj₁ pa) = inj₁ (prec-go g xu yu pa)
prec-go (;′-cong₁ g) xu yu (inj₂ (inj₁ pb)) = inj₂ (inj₁ pb)
prec-go (;′-cong₁ g) xu yu (inj₂ (inj₂ (xa , yb))) = inj₂ (inj₂ (∈s-go g xa , yb))
prec-go (;′-cong₂ g) xu yu (inj₁ pa) = inj₁ pa
prec-go (;′-cong₂ g) xu yu (inj₂ (inj₁ pb)) = inj₂ (inj₁ (prec-go g xu yu pb))
prec-go (;′-cong₂ g) xu yu (inj₂ (inj₂ (xa , yb))) = inj₂ (inj₂ (xa , ∈s-go g yb))
prec-go ∥′-unit xu yu (inj₁ pa) = pa
prec-go ∥′-unit xu yu (inj₂ ())
prec-go ∥′-assoc xu yu (inj₁ (inj₁ pa)) = inj₁ pa
prec-go ∥′-assoc xu yu (inj₁ (inj₂ pb)) = inj₂ (inj₁ pb)
prec-go ∥′-assoc xu yu (inj₂ pc) = inj₂ (inj₂ pc)
prec-go ∥′-comm xu yu (inj₁ pa) = inj₂ pa
prec-go ∥′-comm xu yu (inj₂ pb) = inj₁ pb
prec-go (∥′-cong₁ g) xu yu (inj₁ pa) = inj₁ (prec-go g xu yu pa)
prec-go (∥′-cong₁ g) xu yu (inj₂ pb) = inj₂ pb
prec-go (∥′-dup U) xu yu p = inj₁ p
prec-go (∥′-tm-; U) xu yu (inj₁ pa) = inj₁ pa
prec-go (∥′-tm-; U) xu yu (inj₂ pb) = inj₂ (inj₁ pb)

prec-go-bwd : {n : ℕ} {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n} →
  Γ ∶ α ≈′ β → ¬ Unr (Γ x) → ¬ Unr (Γ y) → prec x y β → prec x y α
prec-go-bwd ;′-assoc xu yu (inj₁ pa) = inj₁ (inj₁ pa)
prec-go-bwd ;′-assoc xu yu (inj₂ (inj₁ (inj₁ pb))) = inj₁ (inj₂ (inj₁ pb))
prec-go-bwd ;′-assoc xu yu (inj₂ (inj₁ (inj₂ (inj₁ pc)))) = inj₂ (inj₁ pc)
prec-go-bwd ;′-assoc xu yu (inj₂ (inj₁ (inj₂ (inj₂ (xb , yc))))) = inj₂ (inj₂ (inj₂ xb , yc))
prec-go-bwd ;′-assoc xu yu (inj₂ (inj₂ (xa , inj₁ yb))) = inj₁ (inj₂ (inj₂ (xa , yb)))
prec-go-bwd ;′-assoc xu yu (inj₂ (inj₂ (xa , inj₂ yc))) = inj₂ (inj₂ (inj₁ xa , yc))
prec-go-bwd (;′-cong₁ g) xu yu (inj₁ pa) = inj₁ (prec-go-bwd g xu yu pa)
prec-go-bwd (;′-cong₁ g) xu yu (inj₂ (inj₁ pb)) = inj₂ (inj₁ pb)
prec-go-bwd (;′-cong₁ g) xu yu (inj₂ (inj₂ (xa , yb))) = inj₂ (inj₂ (∈s-go-bwd g xa , yb))
prec-go-bwd (;′-cong₂ g) xu yu (inj₁ pa) = inj₁ pa
prec-go-bwd (;′-cong₂ g) xu yu (inj₂ (inj₁ pb)) = inj₂ (inj₁ (prec-go-bwd g xu yu pb))
prec-go-bwd (;′-cong₂ g) xu yu (inj₂ (inj₂ (xa , yb))) = inj₂ (inj₂ (xa , ∈s-go-bwd g yb))
prec-go-bwd ∥′-unit xu yu p = inj₁ p
prec-go-bwd ∥′-assoc xu yu (inj₁ pa) = inj₁ (inj₁ pa)
prec-go-bwd ∥′-assoc xu yu (inj₂ (inj₁ pb)) = inj₁ (inj₂ pb)
prec-go-bwd ∥′-assoc xu yu (inj₂ (inj₂ pc)) = inj₂ pc
prec-go-bwd ∥′-comm xu yu (inj₁ pb) = inj₂ pb
prec-go-bwd ∥′-comm xu yu (inj₂ pa) = inj₁ pa
prec-go-bwd (∥′-cong₁ g) xu yu (inj₁ pa) = inj₁ (prec-go-bwd g xu yu pa)
prec-go-bwd (∥′-cong₁ g) xu yu (inj₂ pb) = inj₂ pb
prec-go-bwd (∥′-dup U) xu yu (inj₁ p) = p
prec-go-bwd (∥′-dup U) xu yu (inj₂ p) = p
prec-go-bwd (∥′-tm-; U) xu yu (inj₁ pa) = inj₁ pa
prec-go-bwd (∥′-tm-; U) xu yu (inj₂ (inj₁ pb)) = inj₂ pb
prec-go-bwd (∥′-tm-; (inj₁ Ua)) xu yu (inj₂ (inj₂ (xa , yb))) = ⊥-elim (xu (∈s-Unr Ua xa))
prec-go-bwd (∥′-tm-; (inj₂ Ub)) xu yu (inj₂ (inj₂ (xa , yb))) = ⊥-elim (yu (∈s-Unr Ub yb))

prec-≈ : {n : ℕ} {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n} →
  Γ ∶ α ≈ β → ¬ Unr (Γ x) → ¬ Unr (Γ y) → prec x y α → prec x y β
prec-≈ St.ε xu yu p = p
prec-≈ (Sy.fwd g St.◅ r) xu yu p = prec-≈ r xu yu (prec-go g xu yu p)
prec-≈ (Sy.bwd g St.◅ r) xu yu p = prec-≈ r xu yu (prec-go-bwd g xu yu p)

-- MAIN reflection: ;<= reflects the precedence of two non-Unr variables.
prec-refl : {n : ℕ} {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n} →
  Γ ∶ α ≼ β → ¬ Unr (Γ x) → ¬ Unr (Γ y) → prec x y β → prec x y α
prec-refl (≼-refl e) xu yu p = prec-≈ (≈-sym e) xu yu p
prec-refl (≼-∅ U) xu yu p = xu (∈s-Unr U (prec⇒∈ˡ p))
prec-refl ≼-wk xu yu (inj₁ (inj₁ pa)) = inj₁ (inj₁ pa)
prec-refl ≼-wk xu yu (inj₁ (inj₂ (inj₁ pc))) = inj₂ (inj₁ (inj₁ pc))
prec-refl ≼-wk xu yu (inj₁ (inj₂ (inj₂ (xa , yc)))) = inj₂ (inj₂ (inj₁ xa , inj₁ yc))
prec-refl ≼-wk xu yu (inj₂ (inj₁ pb)) = inj₁ (inj₂ pb)
prec-refl ≼-wk xu yu (inj₂ (inj₂ (inj₁ pd))) = inj₂ (inj₁ (inj₂ pd))
prec-refl ≼-wk xu yu (inj₂ (inj₂ (inj₂ (xb , yd)))) = inj₂ (inj₂ (inj₂ xb , inj₂ yd))
prec-refl (≼-trans le₁ le₂) xu yu p = prec-refl le₁ xu yu (prec-refl le₂ xu yu p)
prec-refl (≼-cong-; le₁ le₂) xu yu (inj₁ pa) = inj₁ (prec-refl le₁ xu yu pa)
prec-refl (≼-cong-; le₁ le₂) xu yu (inj₂ (inj₁ pb)) = inj₂ (inj₁ (prec-refl le₂ xu yu pb))
prec-refl (≼-cong-; le₁ le₂) xu yu (inj₂ (inj₂ (xa , yb))) =
  inj₂ (inj₂ (∈s-refl le₁ xu xa , ∈s-refl le₂ yu yb))
prec-refl (≼-cong-∥ le₁ le₂) xu yu (inj₁ pa) = inj₁ (prec-refl le₁ xu yu pa)
prec-refl (≼-cong-∥ le₁ le₂) xu yu (inj₂ pb) = inj₂ (prec-refl le₂ xu yu pb)

-- Both channel positions of g2 are non-Unr (a session-embed is never Unr).
¬unr⟨⟩ : {s : 𝕊 0} → ¬ Unr ⟨ s ⟩
¬unr⟨⟩ ⟨ () ⟩

prec-0F1F : prec {n = 2} 0F 1F ((` 0F) ; (` 1F))
prec-0F1F = inj₂ (inj₂ (refl , refl))

------------------------------------------------------------------------
-- The impure close op's forced contexts cannot be reconciled with the
-- honest block (` 0F);(` 1F).  Hence, over the bc2 block, the close op's
-- consumed handle IS forced to the front (position 0F).
------------------------------------------------------------------------

front-forced-seq : ¬ (g2 ∶ ((` 1F) ; (` 0F)) ≼ ((` 0F) ; (` 1F)))
front-forced-seq le = ¬p (prec-refl le ¬unr⟨⟩ ¬unr⟨⟩ prec-0F1F)
  where
    ¬p : ¬ prec {n = 2} 0F 1F ((` 1F) ; (` 0F))
    ¬p (inj₁ ())
    ¬p (inj₂ (inj₁ ()))
    ¬p (inj₂ (inj₂ (() , _)))

front-forced-par : ¬ (g2 ∶ ((` 1F) ∥ (` 0F)) ≼ ((` 0F) ; (` 1F)))
front-forced-par le = ¬p (prec-refl le ¬unr⟨⟩ ¬unr⟨⟩ prec-0F1F)
  where
    ¬p : ¬ prec {n = 2} 0F 1F ((` 1F) ∥ (` 0F))
    ¬p (inj₁ ())
    ¬p (inj₂ ())


------------------------------------------------------------------------
-- GENUINE PROCESS witness for (A): a real thread (typed at ⊤ | 𝕀 via
-- TP-Expr) whose active redex is the PURE op (acq) on borrow 1F, with a
-- frame that USES borrow 0F, typed at the honest block (` 0F);(` 1F).
-- The frame is  `let⊗ ((` 0F) ⊗ □) `in body , so (` 0F) sits USED to the
-- left of the active redex (acq ·¹ (` 1F)).
------------------------------------------------------------------------

threadA : gA ; ((` 0F) ; (` 1F)) ⊢ₚ
  ⟪ `let⊗ ((` 0F) ⊗ (K `acq ·¹ (` 1F)))
     `in ((K `send ·¹ (K `unit ⊗ (` 0F))) ; (K (`end ⁇) ·¹ (` 1F))) ⟫
threadA = TP-Expr
  (T-Weaken (≼-refl (≈-trans ;-unit₂ (;-cong ≈-refl ∥-unit₁)))
    (T-LetPair seq scrutD bodyD))
  where
    scrutD : gA ; ((` 0F) ; ([] ∥ (` 1F))) ⊢ (` 0F) ⊗ (K `acq ·¹ (` 1F))
               ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩ ∣ 𝕀
    scrutD = T-Conv ≃-refl ℙ≤ϵ
               (T-Pair seq seq (T-Var 0F refl)
                 (T-AppUnr refl ℙ≤ϵ (T-Const `acq) (T-Var 1F refl)))

    sendD : ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ end ⁇ ⟩ ⸴ gA ; (` 0F)
              ⊢ K `send ·¹ (K `unit ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
    sendD = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁))
              (T-AppUnr refl 𝕀≤𝕀
                (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
                (T-Conv ≃-refl ℙ≤ϵ
                  (T-Pair par par (T-Const `unit) (T-Var 0F refl))))

    closeD : ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ end ⁇ ⟩ ⸴ gA ; (` 1F)
               ⊢ K (`end ⁇) ·¹ (` 1F) ∶ `⊤ ∣ 𝕀
    closeD = T-Weaken (≼-refl ∥-unit₁)
               (T-AppUnr refl 𝕀≤𝕀
                 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end))
                 (T-Conv ≃-refl ℙ≤ϵ (T-Var 1F refl)))

    bodyD : ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ end ⁇ ⟩ ⸴ gA ; (((` 0F) ; (` 1F)) ; [])
              ⊢ (K `send ·¹ (K `unit ⊗ (` 0F))) ; (K (`end ⁇) ·¹ (` 1F)) ∶ `⊤ ∣ 𝕀
    bodyD = T-Weaken (≼-refl (≈-sym ;-unit₂)) (T-Seq `⊤ sendD closeD)
