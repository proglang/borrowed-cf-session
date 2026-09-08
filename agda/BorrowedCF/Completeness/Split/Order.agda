-- | Completeness toolkit, part 4: `before-mob-≼`, the mobility-carrying version
--   of `before-mono-≼` (Simulation/BackwardSoup/GroupOrder.agda §3).
--
--   `before-mono-≼` says: if neither u nor v is Mobile, `≼` cannot create a
--   `;`-order.  That is useless for completeness, because `Mobile` is not
--   decidable and we may not assume immobility.  The version proved here
--   replaces the hypothesis by a CONCLUSION: either the order was already
--   present on the left, or one of the two variables IS mobile — and it hands
--   out the mobility witness, which is exactly what rebuilding the split needs.
--   Only `¬ Unr` is assumed, and `Unr` is decidable.
module BorrowedCF.Completeness.Split.Order where

open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Completeness.Split.Base using (allCx-mem)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using ( _∈ₘ_; before; before⇒mem
        ; mem-parInv; mem-seqInv; mem-parL; mem-parR; mem-seqL; mem-seqR
        ; mem-eq1; mem-eq1ᵇ; mem-≼ᵇ; mem-not-unrCx )

open Nat.Variables
open Variables

private
  variable
    u v : 𝔽 n

-- The escape hatch: one of the two variables is mobile.  A record, so that
-- Γ, u and v stay inferable (they only occur under `lookup` inside).
record Esc (Γ : Ctx n) (u v : 𝔽 n) : Set where
  constructor mkEsc
  field getEsc : Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
open Esc public

private
  esc-map : ∀ {Γ : Ctx n} {P Q : Set} → (P → Q) → P ⊎ Esc Γ u v → Q ⊎ Esc Γ u v
  esc-map f = Sum.map₁ f

------------------------------------------------------------------------
-- 1.  One equivalence step, forwards.  No mobility is ever needed here:
--     `∥′-tm-;` only turns a `∥` into a `;`, which can only ADD order.

before-fwd : {Γ : Ctx n} {α β : Struct n} → ¬ Unr (Γ ﹫ u) → ¬ Unr (Γ ﹫ v) →
  Γ ∶ α ≈′ β → before u v α → before u v β
before-fwd ¬u ¬v (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (u∈ab , v∈c))
  with mem-seqInv {α = a} {b} u∈ab
... | inj₁ u∈a = inj₁ (u∈a , mem-seqR {α = b} {c} v∈c)
... | inj₂ u∈b = inj₂ (inj₂ (inj₁ (u∈b , v∈c)))
before-fwd ¬u ¬v (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₁ (u∈a , v∈b)))) =
  inj₁ (u∈a , mem-seqL {α = b} {c} v∈b)
before-fwd ¬u ¬v (;′-assoc) (inj₂ (inj₁ (inj₂ (inj₁ ba)))) = inj₂ (inj₁ ba)
before-fwd ¬u ¬v (;′-assoc) (inj₂ (inj₁ (inj₂ (inj₂ bb)))) = inj₂ (inj₂ (inj₂ (inj₁ bb)))
before-fwd ¬u ¬v (;′-assoc) (inj₂ (inj₂ bc)) = inj₂ (inj₂ (inj₂ (inj₂ bc)))
before-fwd ¬u ¬v (;′-cong₁ st) (inj₁ (u∈a , v∈b)) = inj₁ (mem-eq1 ¬u st u∈a , v∈b)
before-fwd ¬u ¬v (;′-cong₁ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ (before-fwd ¬u ¬v st ba))
before-fwd ¬u ¬v (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ bb)
before-fwd ¬u ¬v (;′-cong₂ st) (inj₁ (u∈a , v∈b)) = inj₁ (u∈a , mem-eq1 ¬v st v∈b)
before-fwd ¬u ¬v (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ ba)
before-fwd ¬u ¬v (;′-cong₂ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ (before-fwd ¬u ¬v st bb))
before-fwd ¬u ¬v ∥′-unit (inj₁ ba) = ba
before-fwd ¬u ¬v ∥′-unit (inj₂ ())
before-fwd ¬u ¬v ∥′-assoc (inj₁ (inj₁ ba)) = inj₁ ba
before-fwd ¬u ¬v ∥′-assoc (inj₁ (inj₂ bb)) = inj₂ (inj₁ bb)
before-fwd ¬u ¬v ∥′-assoc (inj₂ bc) = inj₂ (inj₂ bc)
before-fwd ¬u ¬v ∥′-comm (inj₁ ba) = inj₂ ba
before-fwd ¬u ¬v ∥′-comm (inj₂ bb) = inj₁ bb
before-fwd ¬u ¬v (∥′-cong₁ st) (inj₁ ba) = inj₁ (before-fwd ¬u ¬v st ba)
before-fwd ¬u ¬v (∥′-cong₁ st) (inj₂ bb) = inj₂ bb
before-fwd ¬u ¬v (∥′-dup {α = a} U) b =
  ⊥-elim (mem-not-unrCx ¬u U (proj₁ (before⇒mem a b)))
before-fwd ¬u ¬v (∥′-tm-; U) (inj₁ ba) = inj₂ (inj₁ ba)
before-fwd ¬u ¬v (∥′-tm-; U) (inj₂ bb) = inj₂ (inj₂ bb)

------------------------------------------------------------------------
-- 2.  One equivalence step, backwards.  `∥′-tm-;` is the only rule that can
--     destroy order, and it comes with the mobility witness we hand out.

before-bwd : {Γ : Ctx n} {α β : Struct n} → ¬ Unr (Γ ﹫ u) → ¬ Unr (Γ ﹫ v) →
  Γ ∶ α ≈′ β → before u v β → before u v α ⊎ Esc Γ u v
before-bwd ¬u ¬v (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (u∈a , v∈bc))
  with mem-seqInv {α = b} {c} v∈bc
... | inj₁ v∈b = inj₁ (inj₂ (inj₁ (inj₁ (u∈a , v∈b))))
... | inj₂ v∈c = inj₁ (inj₁ (mem-seqL {α = a} {b} u∈a , v∈c))
before-bwd ¬u ¬v ;′-assoc (inj₂ (inj₁ ba)) = inj₁ (inj₂ (inj₁ (inj₂ (inj₁ ba))))
before-bwd ¬u ¬v (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₁ (u∈b , v∈c)))) =
  inj₁ (inj₁ (mem-seqR {α = a} {b} u∈b , v∈c))
before-bwd ¬u ¬v ;′-assoc (inj₂ (inj₂ (inj₂ (inj₁ bb)))) = inj₁ (inj₂ (inj₁ (inj₂ (inj₂ bb))))
before-bwd ¬u ¬v ;′-assoc (inj₂ (inj₂ (inj₂ (inj₂ bc)))) = inj₁ (inj₂ (inj₂ bc))
before-bwd ¬u ¬v (;′-cong₁ st) (inj₁ (u∈a′ , v∈b)) = inj₁ (inj₁ (mem-eq1ᵇ ¬u st u∈a′ , v∈b))
before-bwd ¬u ¬v (;′-cong₁ st) (inj₂ (inj₁ ba′)) =
  esc-map (λ z → inj₂ (inj₁ z)) (before-bwd ¬u ¬v st ba′)
before-bwd ¬u ¬v (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₁ (inj₂ (inj₂ bb))
before-bwd ¬u ¬v (;′-cong₂ st) (inj₁ (u∈a , v∈b′)) = inj₁ (inj₁ (u∈a , mem-eq1ᵇ ¬v st v∈b′))
before-bwd ¬u ¬v (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₁ (inj₂ (inj₁ ba))
before-bwd ¬u ¬v (;′-cong₂ st) (inj₂ (inj₂ bb′)) =
  esc-map (λ z → inj₂ (inj₂ z)) (before-bwd ¬u ¬v st bb′)
before-bwd ¬u ¬v ∥′-unit ba = inj₁ (inj₁ ba)
before-bwd ¬u ¬v ∥′-assoc (inj₁ ba) = inj₁ (inj₁ (inj₁ ba))
before-bwd ¬u ¬v ∥′-assoc (inj₂ (inj₁ bb)) = inj₁ (inj₁ (inj₂ bb))
before-bwd ¬u ¬v ∥′-assoc (inj₂ (inj₂ bc)) = inj₁ (inj₂ bc)
before-bwd ¬u ¬v ∥′-comm (inj₁ bb) = inj₁ (inj₂ bb)
before-bwd ¬u ¬v ∥′-comm (inj₂ ba) = inj₁ (inj₁ ba)
before-bwd ¬u ¬v (∥′-cong₁ st) (inj₁ ba′) = esc-map inj₁ (before-bwd ¬u ¬v st ba′)
before-bwd ¬u ¬v (∥′-cong₁ st) (inj₂ bb) = inj₁ (inj₂ bb)
before-bwd ¬u ¬v (∥′-dup {α = a} U) b =
  ⊥-elim (mem-not-unrCx ¬u U
    ([ (λ z → z) , (λ z → z) ]′ (mem-parInv {α = a} {a} (proj₁ (before⇒mem (a ∥ a) b)))))
before-bwd ¬u ¬v (∥′-tm-; {α = a} {β = b} U) (inj₁ (u∈a , v∈b)) =
  inj₂ (mkEsc ([ (λ Ma → inj₁ (allCx-mem Ma u∈a)) , (λ Mb → inj₂ (allCx-mem Mb v∈b)) ]′ U))
before-bwd ¬u ¬v (∥′-tm-; U) (inj₂ (inj₁ ba)) = inj₁ (inj₁ ba)
before-bwd ¬u ¬v (∥′-tm-; U) (inj₂ (inj₂ bb)) = inj₁ (inj₂ bb)

------------------------------------------------------------------------
-- 3.  Along `≈` and along `≼`.

before-≈ᵇ : {Γ : Ctx n} {α β : Struct n} → ¬ Unr (Γ ﹫ u) → ¬ Unr (Γ ﹫ v) →
  Γ ∶ α ≈ β → before u v β → before u v α ⊎ Esc Γ u v
before-≈ᵇ ¬u ¬v ε b = inj₁ b
before-≈ᵇ ¬u ¬v (fwd st ◅ rest) b with before-≈ᵇ ¬u ¬v rest b
... | inj₂ e  = inj₂ e
... | inj₁ b′ = before-bwd ¬u ¬v st b′
before-≈ᵇ ¬u ¬v (bwd st ◅ rest) b with before-≈ᵇ ¬u ¬v rest b
... | inj₂ e  = inj₂ e
... | inj₁ b′ = inj₁ (before-fwd ¬u ¬v st b′)

-- THE LEVER.  `≼` either preserves the `;`-order downwards, or one of the
-- two variables is mobile (and we get the witness).
before-mob-≼ : {Γ : Ctx n} {α β : Struct n} → ¬ Unr (Γ ﹫ u) → ¬ Unr (Γ ﹫ v) →
  Γ ∶ α ≼ β → before u v β → before u v α ⊎ Esc Γ u v
before-mob-≼ ¬u ¬v (≼-refl eq) b = before-≈ᵇ ¬u ¬v eq b
before-mob-≼ ¬u ¬v (≼-∅ {α = β} U) b =
  ⊥-elim (mem-not-unrCx ¬u U (proj₁ (before⇒mem β b)))
before-mob-≼ ¬u ¬v (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₁ (u∈a1 , v∈b1))) =
  inj₁ (inj₁ (mem-parL {α = a1} {a2} u∈a1 , mem-parL {α = b1} {b2} v∈b1))
before-mob-≼ ¬u ¬v ≼-wk (inj₁ (inj₂ (inj₁ ba1))) = inj₁ (inj₂ (inj₁ (inj₁ ba1)))
before-mob-≼ ¬u ¬v ≼-wk (inj₁ (inj₂ (inj₂ bb1))) = inj₁ (inj₂ (inj₂ (inj₁ bb1)))
before-mob-≼ ¬u ¬v (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₁ (u∈a2 , v∈b2))) =
  inj₁ (inj₁ (mem-parR {α = a1} {a2} u∈a2 , mem-parR {α = b1} {b2} v∈b2))
before-mob-≼ ¬u ¬v ≼-wk (inj₂ (inj₂ (inj₁ ba2))) = inj₁ (inj₂ (inj₁ (inj₂ ba2)))
before-mob-≼ ¬u ¬v ≼-wk (inj₂ (inj₂ (inj₂ bb2))) = inj₁ (inj₂ (inj₂ (inj₂ bb2)))
before-mob-≼ ¬u ¬v (≼-trans p q) b with before-mob-≼ ¬u ¬v q b
... | inj₂ e  = inj₂ e
... | inj₁ b′ = before-mob-≼ ¬u ¬v p b′
before-mob-≼ ¬u ¬v (≼-cong-; p q) (inj₁ (u∈a′ , v∈b′)) =
  inj₁ (inj₁ (mem-≼ᵇ ¬u p u∈a′ , mem-≼ᵇ ¬v q v∈b′))
before-mob-≼ ¬u ¬v (≼-cong-; p q) (inj₂ (inj₁ ba′)) =
  esc-map (λ z → inj₂ (inj₁ z)) (before-mob-≼ ¬u ¬v p ba′)
before-mob-≼ ¬u ¬v (≼-cong-; p q) (inj₂ (inj₂ bb′)) =
  esc-map (λ z → inj₂ (inj₂ z)) (before-mob-≼ ¬u ¬v q bb′)
before-mob-≼ ¬u ¬v (≼-cong-∥ p q) (inj₁ ba′) = esc-map inj₁ (before-mob-≼ ¬u ¬v p ba′)
before-mob-≼ ¬u ¬v (≼-cong-∥ p q) (inj₂ bb′) = esc-map inj₂ (before-mob-≼ ¬u ¬v q bb′)
