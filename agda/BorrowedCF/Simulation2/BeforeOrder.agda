module BorrowedCF.Simulation2.BeforeOrder where

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
open import BorrowedCF.Context.Base using (AllCx)
open import BorrowedCF.Simulation2.Confine using (count; unrCx⇒count0; count-≈; count-≈′)

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
