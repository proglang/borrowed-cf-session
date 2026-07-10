module BorrowedCF.Simulation.Support.BeforeOrder where

-- ;-ORDER separation, the ; analogue of RsplitTypingRefute.sep (whose module is
-- not importable — its probe dependency RsplitOwnershipProbe is stale — so the
-- small count-based membership helpers are inlined here).
--   before x y γ  =  x occurs ;-strictly-before y somewhere in γ.
-- `before` is monotone DOWNWARD under ≼ (bigger ⟹ smaller): ≼-wk RELAXES ; to ∥,
-- which can only DESTROY a ;-order relationship, never create one.  This pins the
-- impure send/select head redex to handle 0F: the binder ;-chain has before 0F xS,
-- so (downward) the send thread has before 0F xS, contradicting the head redex
-- being ;-minimal — unless xS ≡ 0F.

open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Data.Nat using (_+_; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (AllCx; MobCx)
open import BorrowedCF.Simulation.Support.Confine using (count; unrCx⇒count0; count-≈; count-≈′; count-self; count-wk-suc)
open import BorrowedCF.Simulation.Support.StructDom using (count-structNSeq-lt)
open import BorrowedCF.Processes.Typed using (structNSeq)
open import Data.Fin.Properties using (toℕ<n)
import BorrowedCF.Context.Substitution as 𝐂

open Fin.Patterns
open Nat.Variables

private variable
  x y : 𝔽 n
  α β : Struct n

-- ── membership via count (inlined from RsplitTypingRefute). ──
_∈ₘ_ : 𝔽 n → Struct n → Set
x ∈ₘ γ = count x γ ≢ 0

mem-resp : {α β : Struct n} → count x α ≡ count x β → x ∈ₘ α → x ∈ₘ β
mem-resp eq x∈ x≡0 = x∈ (eq ■ x≡0)

∨-of-≢0 : ∀ a b → a + b ≢ 0 → (a ≢ 0) ⊎ (b ≢ 0)
∨-of-≢0 zero    b ne = inj₂ ne
∨-of-≢0 (suc a) b ne = inj₁ (λ ())

mem-parInv : {α β : Struct n} → x ∈ₘ (α ∥ β) → (x ∈ₘ α) ⊎ (x ∈ₘ β)
mem-parInv {x = x} {α} {β} = ∨-of-≢0 (count x α) (count x β)

mem-seqInv : {α β : Struct n} → x ∈ₘ (α ; β) → (x ∈ₘ α) ⊎ (x ∈ₘ β)
mem-seqInv {x = x} {α} {β} = ∨-of-≢0 (count x α) (count x β)

mem-parL : {α β : Struct n} → x ∈ₘ α → x ∈ₘ (α ∥ β)
mem-parL {x = x} {α} x∈ eq = x∈ (m0 (count x α) eq)
  where m0 : ∀ a {b} → a + b ≡ 0 → a ≡ 0
        m0 zero _ = refl
        m0 (suc a) ()

mem-parR : {α β : Struct n} → x ∈ₘ β → x ∈ₘ (α ∥ β)
mem-parR {x = x} {α} x∈ eq = x∈ (n0 (count x α) eq)
  where n0 : ∀ a {b} → a + b ≡ 0 → b ≡ 0
        n0 zero eq = eq
        n0 (suc a) ()

mem-seqL : {α β : Struct n} → x ∈ₘ α → x ∈ₘ (α ; β)
mem-seqL {x = x} {α} {β} = mem-parL {x = x} {α} {β}

mem-seqR : {α β : Struct n} → x ∈ₘ β → x ∈ₘ (α ; β)
mem-seqR {x = x} {α} {β} = mem-parR {x = x} {α} {β}

mem-not-unrCx : ¬ Unr (Γ x) → AllCx Unr Γ α → x ∈ₘ α → ⊥
mem-not-unrCx ¬u U x∈ = x∈ (unrCx⇒count0 ¬u U)

mobCx⇒count0 : ¬ Mobile (Γ x) → MobCx Γ α → count x α ≡ 0
mobCx⇒count0 ¬m []        = refl
mobCx⇒count0 ¬m (C₁ ∥ C₂) = cong₂ _+_ (mobCx⇒count0 ¬m C₁) (mobCx⇒count0 ¬m C₂)
mobCx⇒count0 ¬m (C₁ ; C₂) = cong₂ _+_ (mobCx⇒count0 ¬m C₁) (mobCx⇒count0 ¬m C₂)
mobCx⇒count0 {x = x} ¬m (`_ {y} py) with x Fin.≟ y
... | yes refl = ⊥-elim (¬m py)
... | no  _    = refl

mem-not-mobCx : ¬ Mobile (Γ x) → MobCx Γ α → x ∈ₘ α → ⊥
mem-not-mobCx ¬m U x∈ = x∈ (mobCx⇒count0 ¬m U)

mem-eq1 : ¬ Unr (Γ x) → Γ ∶ α ≈′ β → x ∈ₘ α → x ∈ₘ β
mem-eq1 {x = x} {α} {β} ¬u st = mem-resp {x = x} {α} {β} (count-≈′ ¬u st)

mem-eq1ᵇ : ¬ Unr (Γ x) → Γ ∶ α ≈′ β → x ∈ₘ β → x ∈ₘ α
mem-eq1ᵇ {x = x} {α} {β} ¬u st = mem-resp {x = x} {β} {α} (sym (count-≈′ ¬u st))

-- ── the ;-order-before predicate. ──
before : 𝔽 n → 𝔽 n → Struct n → Set
before x y (` z)   = ⊥
before x y []      = ⊥
before x y (α ∥ β) = before x y α ⊎ before x y β
before x y (α ; β) = ((x ∈ₘ α) × (y ∈ₘ β)) ⊎ before x y α ⊎ before x y β

before⇒mem : (γ : Struct n) → before x y γ → (x ∈ₘ γ) × (y ∈ₘ γ)
before⇒mem (` z) ()
before⇒mem [] ()
before⇒mem (α ∥ β) (inj₁ bα) = let p = before⇒mem α bα in mem-parL {α = α} {β} (fst p) , mem-parL {α = α} {β} (snd p)
before⇒mem (α ∥ β) (inj₂ bβ) = let p = before⇒mem β bβ in mem-parR {α = α} {β} (fst p) , mem-parR {α = α} {β} (snd p)
before⇒mem (α ; β) (inj₁ (x∈ , y∈)) = mem-seqL {α = α} {β} x∈ , mem-seqR {α = α} {β} y∈
before⇒mem (α ; β) (inj₂ (inj₁ bα)) = let p = before⇒mem α bα in mem-seqL {α = α} {β} (fst p) , mem-seqL {α = α} {β} (snd p)
before⇒mem (α ; β) (inj₂ (inj₂ bβ)) = let p = before⇒mem β bβ in mem-seqR {α = α} {β} (fst p) , mem-seqR {α = α} {β} (snd p)

swap-mid : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
swap-mid a b c d =
  +-assoc a b (c + d)
  ■ cong (a +_) (sym (+-assoc b c d) ■ cong (_+ d) (+-comm b c) ■ +-assoc c b d)
  ■ sym (+-assoc a c (b + d))

count-≼-eq : ¬ Unr (Γ x) → Γ ∶ α ≼ β → count x α ≡ count x β
count-≼-eq ¬u (≼-refl eq) = count-≈ ¬u eq
count-≼-eq ¬u (≼-∅ U) = sym (unrCx⇒count0 ¬u U)
count-≼-eq {x = x} ¬u (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) =
  swap-mid (count x a1) (count x a2) (count x b1) (count x b2)
count-≼-eq ¬u (≼-trans p q) = count-≼-eq ¬u p ■ count-≼-eq ¬u q
count-≼-eq ¬u (≼-cong-; p q) = cong₂ _+_ (count-≼-eq ¬u p) (count-≼-eq ¬u q)
count-≼-eq ¬u (≼-cong-∥ p q) = cong₂ _+_ (count-≼-eq ¬u p) (count-≼-eq ¬u q)

mem-≼ᵇ : ¬ Unr (Γ x) → Γ ∶ α ≼ β → x ∈ₘ β → x ∈ₘ α
mem-≼ᵇ {x = x} {α = α} {β = β} ¬u le = mem-resp {x = x} {β} {α} (sym (count-≼-eq ¬u le))


-- ── before is preserved by a single ≈′ step (forward), both leaves non-Unr. ──
before-resp-eq1 : ¬ Mobile (Γ x) → ¬ Mobile (Γ y)
                → Γ ∶ α ≈′ β → before x y α → before x y β
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (x∈ab , y∈c)) with mem-seqInv {α = a} {b} x∈ab
... | inj₁ x∈a = inj₁ (x∈a , mem-seqR {α = b} {c} y∈c)
... | inj₂ x∈b = inj₂ (inj₂ (inj₁ (x∈b , y∈c)))
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₁ (x∈a , y∈b)))) = inj₁ (x∈a , mem-seqL {α = b} {c} y∈b)
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₂ (inj₁ ba)))) = inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₂ (inj₂ bb)))) = inj₂ (inj₂ (inj₂ (inj₁ bb)))
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ bc)) = inj₂ (inj₂ (inj₂ (inj₂ bc)))
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₁ (x∈a , y∈b)) = inj₁ (mem-eq1 (¬ux ∘ unr⇒mobile) st x∈a , y∈b)
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ (before-resp-eq1 ¬ux ¬uy st ba))
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ bb)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₁ (x∈a , y∈b)) = inj₁ (x∈a , mem-eq1 (¬uy ∘ unr⇒mobile) st y∈b)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ (before-resp-eq1 ¬ux ¬uy st bb))
before-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₁ ba) = ba
before-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₂ ())
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₁ ba)) = inj₁ ba
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₂ bb)) = inj₂ (inj₁ bb)
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ bc) = inj₂ (inj₂ bc)
before-resp-eq1 ¬ux ¬uy ∥′-comm (inj₁ ba) = inj₂ ba
before-resp-eq1 ¬ux ¬uy ∥′-comm (inj₂ bb) = inj₁ bb
before-resp-eq1 ¬ux ¬uy (∥′-cong₁ st) (inj₁ ba) = inj₁ (before-resp-eq1 ¬ux ¬uy st ba)
before-resp-eq1 ¬ux ¬uy (∥′-cong₁ st) (inj₂ bb) = inj₂ bb
before-resp-eq1 ¬ux ¬uy (∥′-dup {α = a} U) b = ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U (fst (before⇒mem a b)))
before-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ ba) = inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ bb) = inj₂ (inj₂ bb)

-- ── before is preserved by a single ≈′ step (backward). ──
before-resp-eq1ᵇ : ¬ Mobile (Γ x) → ¬ Mobile (Γ y)
                 → Γ ∶ α ≈′ β → before x y β → before x y α
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (x∈a , y∈bc)) with mem-seqInv {α = b} {c} y∈bc
... | inj₁ y∈b = inj₂ (inj₁ (inj₁ (x∈a , y∈b)))
... | inj₂ y∈c = inj₁ (mem-seqL {α = a} {b} x∈a , y∈c)
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ ba)) = inj₂ (inj₁ (inj₂ (inj₁ ba)))
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₁ (x∈b , y∈c)))) = inj₁ (mem-seqR {α = a} {b} x∈b , y∈c)
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₂ (inj₁ bb)))) = inj₂ (inj₁ (inj₂ (inj₂ bb)))
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₂ (inj₂ bc)))) = inj₂ (inj₂ bc)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₁ (x∈a′ , y∈b)) = inj₁ (mem-eq1ᵇ (¬ux ∘ unr⇒mobile) st x∈a′ , y∈b)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₁ ba′)) = inj₂ (inj₁ (before-resp-eq1ᵇ ¬ux ¬uy st ba′))
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ bb)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₁ (x∈a , y∈b′)) = inj₁ (x∈a , mem-eq1ᵇ (¬uy ∘ unr⇒mobile) st y∈b′)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ ba)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₂ bb′)) = inj₂ (inj₂ (before-resp-eq1ᵇ ¬ux ¬uy st bb′))
before-resp-eq1ᵇ ¬ux ¬uy (∥′-unit {α = a}) ba = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ ba) = inj₁ (inj₁ ba)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ bb)) = inj₁ (inj₂ bb)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ bc)) = inj₂ bc
before-resp-eq1ᵇ ¬ux ¬uy ∥′-comm (inj₁ bb) = inj₂ bb
before-resp-eq1ᵇ ¬ux ¬uy ∥′-comm (inj₂ ba) = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ st) (inj₁ ba′) = inj₁ (before-resp-eq1ᵇ ¬ux ¬uy st ba′)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ st) (inj₂ bb) = inj₂ bb
before-resp-eq1ᵇ ¬ux ¬uy (∥′-dup {α = a} U) b =
  ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U ([ (λ z → z) , (λ z → z) ]′ (mem-parInv {α = a} {a} (fst (before⇒mem (a ∥ a) b)))))
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ (x∈a , y∈b)) =
  [ (λ Ua → ⊥-elim (mem-not-mobCx ¬ux Ua x∈a)) , (λ Ub → ⊥-elim (mem-not-mobCx ¬uy Ub y∈b)) ]′ U
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₁ ba)) = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₂ bb)) = inj₂ bb

before-resp-≈ : ¬ Mobile (Γ x) → ¬ Mobile (Γ y)
              → Γ ∶ α ≈ β → before x y α → before x y β
before-resp-≈ ¬ux ¬uy ε b = b
before-resp-≈ ¬ux ¬uy (fwd st ◅ rest) b = before-resp-≈ ¬ux ¬uy rest (before-resp-eq1 ¬ux ¬uy st b)
before-resp-≈ ¬ux ¬uy (bwd st ◅ rest) b = before-resp-≈ ¬ux ¬uy rest (before-resp-eq1ᵇ ¬ux ¬uy st b)

-- ── before is monotone DOWNWARD under ≼ (bigger ⟹ smaller), for non-Unr x,y. ──
before-mono-≼ : ¬ Mobile (Γ x) → ¬ Mobile (Γ y)
              → Γ ∶ α ≼ β → before x y β → before x y α
before-mono-≼ ¬ux ¬uy (≼-refl eq) b = before-resp-≈ ¬ux ¬uy (≈-sym eq) b
before-mono-≼ ¬ux ¬uy (≼-∅ {α = β} U) b = ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U (fst (before⇒mem β b)))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₁ (x∈a1 , y∈b1))) =
  inj₁ (mem-parL {α = a1} {a2} x∈a1 , mem-parL {α = b1} {b2} y∈b1)
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₂ (inj₁ ba1))) = inj₂ (inj₁ (inj₁ ba1))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₂ (inj₂ bb1))) = inj₂ (inj₂ (inj₁ bb1))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₁ (x∈a2 , y∈b2))) =
  inj₁ (mem-parR {α = a1} {a2} x∈a2 , mem-parR {α = b1} {b2} y∈b2)
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₂ (inj₁ ba2))) = inj₂ (inj₁ (inj₂ ba2))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₂ (inj₂ bb2))) = inj₂ (inj₂ (inj₂ bb2))
before-mono-≼ ¬ux ¬uy (≼-trans p q) b = before-mono-≼ ¬ux ¬uy p (before-mono-≼ ¬ux ¬uy q b)
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₁ (x∈a′ , y∈b′)) = inj₁ (mem-≼ᵇ (¬ux ∘ unr⇒mobile) p x∈a′ , mem-≼ᵇ (¬uy ∘ unr⇒mobile) q y∈b′)
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₂ (inj₁ ba′)) = inj₂ (inj₁ (before-mono-≼ ¬ux ¬uy p ba′))
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₂ (inj₂ bb′)) = inj₂ (inj₂ (before-mono-≼ ¬ux ¬uy q bb′))
before-mono-≼ ¬ux ¬uy (≼-cong-∥ p q) (inj₁ ba′) = inj₁ (before-mono-≼ ¬ux ¬uy p ba′)
before-mono-≼ ¬ux ¬uy (≼-cong-∥ p q) (inj₂ bb′) = inj₂ (before-mono-≼ ¬ux ¬uy q bb′)


-- ── a ;-chain structNSeq (suc m) has  before 0F (suc z')  for every later leaf. ──
before-structNSeq : ∀ m (z′ : 𝔽 m) → before 0F (Fin.suc z′) (structNSeq (suc m))
before-structNSeq m z′ = inj₁ (0∈ , z∈)
  where
    0∈ : 0F ∈ₘ (` (Fin.zero {m}))
    0∈ eq = case (sym (count-self (Fin.zero {m})) ■ eq) of λ ()
    ceq : count (Fin.suc z′) (𝐂.wk (structNSeq m)) ≡ 1
    ceq = count-wk-suc (structNSeq m) z′ ■ count-structNSeq-lt m z′ (toℕ<n z′)
    z∈ : (Fin.suc z′) ∈ₘ 𝐂.wk (structNSeq m)
    z∈ eq = case (sym ceq ■ eq) of λ ()


-- ── step 2(b): before/count transported forward along an injective renaming. ──
count-⋯ᵣ-inj : ∀ {m k} (ϕ : m 𝐂.→ᵣ k) → 𝐂.Inj ϕ → (γ : Struct m) (w : 𝔽 m)
             → count (ϕ w) (γ 𝐂.⋯ᵣ ϕ) ≡ count w γ
count-⋯ᵣ-inj ϕ inj []      w = refl
count-⋯ᵣ-inj ϕ inj (` v)   w with ϕ w Fin.≟ ϕ v | w Fin.≟ v
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes p | no ¬q = ⊥-elim (¬q (inj p))
... | no ¬p | yes q = ⊥-elim (¬p (cong ϕ q))
count-⋯ᵣ-inj ϕ inj (α ∥ β) w = cong₂ _+_ (count-⋯ᵣ-inj ϕ inj α w) (count-⋯ᵣ-inj ϕ inj β w)
count-⋯ᵣ-inj ϕ inj (α ; β) w = cong₂ _+_ (count-⋯ᵣ-inj ϕ inj α w) (count-⋯ᵣ-inj ϕ inj β w)

mem-⋯ᵣ-inj : ∀ {m k} (ϕ : m 𝐂.→ᵣ k) → 𝐂.Inj ϕ → (γ : Struct m) {w : 𝔽 m}
           → w ∈ₘ γ → (ϕ w) ∈ₘ (γ 𝐂.⋯ᵣ ϕ)
mem-⋯ᵣ-inj ϕ inj γ {w} w∈ eq = w∈ (sym (count-⋯ᵣ-inj ϕ inj γ w) ■ eq)

before-⋯ᵣ-inj : ∀ {m k} (ϕ : m 𝐂.→ᵣ k) → 𝐂.Inj ϕ → (γ : Struct m) {x y : 𝔽 m}
              → before x y γ → before (ϕ x) (ϕ y) (γ 𝐂.⋯ᵣ ϕ)
before-⋯ᵣ-inj ϕ inj (` z) ()
before-⋯ᵣ-inj ϕ inj [] ()
before-⋯ᵣ-inj ϕ inj (α ∥ β) (inj₁ bα) = inj₁ (before-⋯ᵣ-inj ϕ inj α bα)
before-⋯ᵣ-inj ϕ inj (α ∥ β) (inj₂ bβ) = inj₂ (before-⋯ᵣ-inj ϕ inj β bβ)
before-⋯ᵣ-inj ϕ inj (α ; β) (inj₁ (x∈α , y∈β)) =
  inj₁ (mem-⋯ᵣ-inj ϕ inj α x∈α , mem-⋯ᵣ-inj ϕ inj β y∈β)
before-⋯ᵣ-inj ϕ inj (α ; β) (inj₂ (inj₁ bα)) = inj₂ (inj₁ (before-⋯ᵣ-inj ϕ inj α bα))
before-⋯ᵣ-inj ϕ inj (α ; β) (inj₂ (inj₂ bβ)) = inj₂ (inj₂ (before-⋯ᵣ-inj ϕ inj β bβ))
