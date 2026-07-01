module BorrowedCF.Simulation2.RsplitTypingRefute where

open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (AllCx)
open import BorrowedCF.Processes.Typed using (Proc; _∥_; _;_⊢ₚ_; inv-∥)

open Fin.Patterns
open Nat.Variables

import BorrowedCF.Simulation2.RsplitOwnershipProbe as P
open import BorrowedCF.Simulation2.Confine using (count; unrCx⇒count0; count-≈′; ≼⇒count≤)
open import Data.Nat using (z≤n; _≤_)

variable
  α β : Struct n

-- ============================================================================
-- VACUITY OF THE U-rsplit "BAD CASE".
--
-- bodyStruct (the TP-Res body context of the minimal R-RSplit redex
--   ν (2 ∷ []) [] (⟪ E[rsplit·inj 0F] ⟫ ∥ P)) normalizes to
--       ((` 0F) ; ((` 1F) ; [])) ∥ [] ∥ [] ∥ []
-- i.e. the HANDLE borrow 0F and the OFF-HANDLE borrow 1F of the SAME front
-- chain are SEQUENTIALLY (;) joined — never put in parallel (∥).
--
-- The "bad case" needs the TP-Par split  bodyStruct ⪰ γE ∥ γP  with 0F in the
-- rsplit thread's γE and 1F in the sibling's γP — i.e. 0F and 1F land in
-- DIFFERENT ∥-components.  We prove that the ordered context discipline forbids
-- this: ∥-separation of two non-unrestricted (linear) channel slots is
-- MONOTONE UPWARD under ≼, but bodyStruct does NOT ∥-separate 0F and 1F, while
-- any (γE ∥ γP) that places them on opposite sides DOES — contradiction.
-- ============================================================================

-- ── Multiplicity / membership of a leaf in a Struct (via Confine.count). ──
_∈ₘ_ : 𝔽 n → Struct n → Set
x ∈ₘ γ = count x γ ≢ 0

-- ── ∥-separation: x and y occur in OPPOSITE arms of some ∥ inside γ. ──
sep : 𝔽 n → 𝔽 n → Struct n → Set
sep x y (` z)   = ⊥
sep x y []      = ⊥
sep x y (α ∥ β) = ((x ∈ₘ α) × (y ∈ₘ β)) ⊎ ((x ∈ₘ β) × (y ∈ₘ α)) ⊎ sep x y α ⊎ sep x y β
sep x y (α ; β) = sep x y α ⊎ sep x y β

-- ============================================================================
-- (A)  sep is preserved UPWARD by ≼  (smaller ⟹ bigger), provided the two
--      slots are non-unrestricted (so the duplicating/transmuting ≈ rules,
--      which act only on UnrCx, cannot involve them).
-- ============================================================================

-- A non-unrestricted leaf has count 0 in any unrestricted context.
mem-not-unrCx : ∀ {Γ : Ctx n} {x : 𝔽 n} {α} → ¬ Unr (Γ x) → AllCx Unr Γ α → x ∈ₘ α → ⊥
mem-not-unrCx ¬u U x∈ = x∈ (unrCx⇒count0 ¬u U)

-- membership transports along count equalities
mem-resp : ∀ {x : 𝔽 n} {α β} → count x α ≡ count x β → x ∈ₘ α → x ∈ₘ β
mem-resp eq x∈ x≡0 = x∈ (eq ■ x≡0)

-- helper: if a + b ≢ 0 then a ≢ 0 ⊎ b ≢ 0
∨-of-≢0 : ∀ a b → a + b ≢ 0 → (a ≢ 0) ⊎ (b ≢ 0)
∨-of-≢0 zero    b ne = inj₂ ne
∨-of-≢0 (suc a) b ne = inj₁ (λ ())

mem-parInv : ∀ {x : 𝔽 n} {α β} → x ∈ₘ (α ∥ β) → (x ∈ₘ α) ⊎ (x ∈ₘ β)
mem-parInv {x = x} {α} {β} = ∨-of-≢0 (count x α) (count x β)

mem-seqInv : ∀ {x : 𝔽 n} {α β} → x ∈ₘ (α ; β) → (x ∈ₘ α) ⊎ (x ∈ₘ β)
mem-seqInv {x = x} {α} {β} = ∨-of-≢0 (count x α) (count x β)

-- ── membership unions: x∈(α∥β) from x∈α (and from x∈β); same for ; ──
mem-parL : {x : 𝔽 n} {α β : Struct n} → x ∈ₘ α → x ∈ₘ (α ∥ β)
mem-parL {x = x} {α} {β} x∈ eq = x∈ (m+n≡0⇒m≡0 (count x α) eq)
  where m+n≡0⇒m≡0 : ∀ a {b} → a + b ≡ 0 → a ≡ 0
        m+n≡0⇒m≡0 zero    _  = refl
        m+n≡0⇒m≡0 (suc a) ()

mem-parR : {x : 𝔽 n} {α β : Struct n} → x ∈ₘ β → x ∈ₘ (α ∥ β)
mem-parR {x = x} {α} {β} x∈ eq = x∈ (m+n≡0⇒n≡0 (count x α) eq)
  where m+n≡0⇒n≡0 : ∀ a {b} → a + b ≡ 0 → b ≡ 0
        m+n≡0⇒n≡0 zero    eq = eq
        m+n≡0⇒n≡0 (suc a) ()

mem-seqL : {x : 𝔽 n} {α β : Struct n} → x ∈ₘ α → x ∈ₘ (α ; β)
mem-seqL {α = α} {β} = mem-parL {α = α} {β}

mem-seqR : {x : 𝔽 n} {α β : Struct n} → x ∈ₘ β → x ∈ₘ (α ; β)
mem-seqR {α = α} {β} = mem-parR {α = α} {β}

-- ── separation implies both leaves are present. ──
sep⇒mem : {x y : 𝔽 n} (γ : Struct n) → sep x y γ → (x ∈ₘ γ) × (y ∈ₘ γ)
sep⇒mem (` z) ()
sep⇒mem [] ()
sep⇒mem (α ∥ β) (inj₁ (xα , yβ)) = mem-parL {α = α} {β} xα , mem-parR {α = α} {β} yβ
sep⇒mem (α ∥ β) (inj₂ (inj₁ (xβ , yα))) = mem-parR {α = α} {β} xβ , mem-parL {α = α} {β} yα
sep⇒mem (α ∥ β) (inj₂ (inj₂ (inj₁ sα))) =
  let xα , yα = sep⇒mem α sα in mem-parL {α = α} {β} xα , mem-parL {α = α} {β} yα
sep⇒mem (α ∥ β) (inj₂ (inj₂ (inj₂ sβ))) =
  let xβ , yβ = sep⇒mem β sβ in mem-parR {α = α} {β} xβ , mem-parR {α = α} {β} yβ
sep⇒mem (α ; β) (inj₁ sα) =
  let xα , yα = sep⇒mem α sα in mem-seqL {α = α} {β} xα , mem-seqL {α = α} {β} yα
sep⇒mem (α ; β) (inj₂ sβ) =
  let xβ , yβ = sep⇒mem β sβ in mem-seqR {α = α} {β} xβ , mem-seqR {α = α} {β} yβ

-- ── sep is invariant under one-step context ≈′ (both leaves non-unr). ──
-- We need it in both directions because ≈ is a symmetric closure.
-- membership transports along one-step ≈′ for a non-unr leaf.
mem-eq1 : {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → Γ ∶ α ≈′ β → x ∈ₘ α → x ∈ₘ β
mem-eq1 {x = x} {α = α} {β = β} ¬ux st x∈ = mem-resp {x = x} {α} {β} (count-≈′ ¬ux st) x∈

-- ∥-reassociation of separation.
reassoc∥ : {x y : 𝔽 n} (a b c : Struct n)
         → sep x y ((a ∥ b) ∥ c) → sep x y (a ∥ (b ∥ c))
reassoc∥ a b c (inj₁ (xab , yc)) with mem-parInv {α = a} {b} xab
... | inj₁ xa = inj₁ (xa , mem-parR {α = b} {c} yc)
... | inj₂ xb = inj₂ (inj₂ (inj₂ (inj₁ (xb , yc))))
reassoc∥ a b c (inj₂ (inj₁ (xc , yab))) with mem-parInv {α = a} {b} yab
... | inj₁ ya = inj₂ (inj₁ (mem-parR {α = b} {c} xc , ya))
... | inj₂ yb = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (xc , yb)))))
reassoc∥ a b c (inj₂ (inj₂ (inj₁ sab))) with sab
... | inj₁ (xa , yb) = inj₁ (xa , mem-parL {α = b} {c} yb)
... | inj₂ (inj₁ (xb , ya)) = inj₂ (inj₁ (mem-parL {α = b} {c} xb , ya))
... | inj₂ (inj₂ (inj₁ sa)) = inj₂ (inj₂ (inj₁ sa))
... | inj₂ (inj₂ (inj₂ sb)) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ sb)))))
reassoc∥ a b c (inj₂ (inj₂ (inj₂ sc))) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ sc)))))

-- ∥-commutation of separation.
comm∥ : {x y : 𝔽 n} {a b : Struct n}
      → sep x y (a ∥ b) → sep x y (b ∥ a)
comm∥ (inj₁ (xa , yb)) = inj₂ (inj₁ (xa , yb))
comm∥ (inj₂ (inj₁ (xb , ya))) = inj₁ (xb , ya)
comm∥ (inj₂ (inj₂ (inj₁ sa))) = inj₂ (inj₂ (inj₂ sa))
comm∥ (inj₂ (inj₂ (inj₂ sb))) = inj₂ (inj₂ (inj₁ sb))

sep-resp-eq1 : {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → ¬ Unr (Γ y)
        → Γ ∶ α ≈′ β → sep x y α → sep x y β
sep-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₁ p)) = inj₁ p
sep-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₂ p)) = inj₂ (inj₁ p)
sep-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ p) = inj₂ (inj₂ p)
sep-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₁ p) = inj₁ (sep-resp-eq1 ¬ux ¬uy st p)
sep-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₂ p) = inj₂ p
sep-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₁ p) = inj₁ p
sep-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₂ p) = inj₂ (sep-resp-eq1 ¬ux ¬uy st p)
sep-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₁ (xa , y[])) = ⊥-elim (y[] refl)
sep-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₂ (inj₁ (x[] , ya))) = ⊥-elim (x[] refl)
sep-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₂ (inj₂ (inj₁ sa))) = sa
sep-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₂ (inj₂ (inj₂ ())))
sep-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) sp = reassoc∥ a b c sp
sep-resp-eq1 ¬ux ¬uy ∥′-comm sp = comm∥ sp
sep-resp-eq1 ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₁ (xa , yb)) =
  inj₁ (mem-eq1 ¬ux st xa , yb)
sep-resp-eq1 ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₁ (xb , ya))) =
  inj₂ (inj₁ (xb , mem-eq1 ¬uy st ya))
sep-resp-eq1 ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₂ (inj₁ sa))) =
  inj₂ (inj₂ (inj₁ (sep-resp-eq1 ¬ux ¬uy st sa)))
sep-resp-eq1 ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₂ (inj₂ sb))) =
  inj₂ (inj₂ (inj₂ sb))
sep-resp-eq1 ¬ux ¬uy (∥′-dup {α = a} U) sp =
  ⊥-elim (mem-not-unrCx ¬ux U (fst (sep⇒mem a sp)))
sep-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ (xa , yb)) =
  [ (λ Ua → ⊥-elim (mem-not-unrCx ¬ux Ua xa))
  , (λ Ub → ⊥-elim (mem-not-unrCx ¬uy Ub yb)) ]′ U
sep-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₁ (xb , ya))) =
  [ (λ Ua → ⊥-elim (mem-not-unrCx ¬uy Ua ya))
  , (λ Ub → ⊥-elim (mem-not-unrCx ¬ux Ub xb)) ]′ U
sep-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₂ (inj₁ sa))) = inj₁ sa
sep-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₂ (inj₂ sb))) = inj₂ sb


-- backward membership transport: x∈β → x∈α  for  α ≈′ β.
mem-eq1ᵇ : {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → Γ ∶ α ≈′ β → x ∈ₘ β → x ∈ₘ α
mem-eq1ᵇ {x = x} {α = α} {β = β} ¬ux st x∈ =
  mem-resp {x = x} {β} {α} (sym (count-≈′ ¬ux st)) x∈

-- backward ∥-reassociation:  sep (a ∥ (b ∥ c)) → sep ((a ∥ b) ∥ c).
reassoc∥ᵇ : {x y : 𝔽 n} (a b c : Struct n)
          → sep x y (a ∥ (b ∥ c)) → sep x y ((a ∥ b) ∥ c)
reassoc∥ᵇ a b c (inj₁ (xa , ybc)) with mem-parInv {α = b} {c} ybc
... | inj₁ yb = inj₂ (inj₂ (inj₁ (inj₁ (xa , yb))))
... | inj₂ yc = inj₁ (mem-parL {α = a} {b} xa , yc)
reassoc∥ᵇ a b c (inj₂ (inj₁ (xbc , ya))) with mem-parInv {α = b} {c} xbc
... | inj₁ xb = inj₂ (inj₂ (inj₁ (inj₂ (inj₁ (xb , ya)))))
... | inj₂ xc = inj₂ (inj₁ (xc , mem-parL {α = a} {b} ya))
reassoc∥ᵇ a b c (inj₂ (inj₂ (inj₁ sa))) = inj₂ (inj₂ (inj₁ (inj₂ (inj₂ (inj₁ sa)))))
reassoc∥ᵇ a b c (inj₂ (inj₂ (inj₂ sbc))) with sbc
... | inj₁ (xb , yc) = inj₁ (mem-parR {α = a} {b} xb , yc)
... | inj₂ (inj₁ (xc , yb)) = inj₂ (inj₁ (xc , mem-parR {α = a} {b} yb))
... | inj₂ (inj₂ (inj₁ sb)) = inj₂ (inj₂ (inj₁ (inj₂ (inj₂ (inj₂ sb)))))
... | inj₂ (inj₂ (inj₂ sc)) = inj₂ (inj₂ (inj₂ sc))

-- ── the backward single-step: sep x y β → sep x y α  for  α ≈′ β. ──
sep-resp-eq1ᵇ : {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → ¬ Unr (Γ y)
        → Γ ∶ α ≈′ β → sep x y β → sep x y α
sep-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ p) = inj₁ (inj₁ p)
sep-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ p)) = inj₁ (inj₂ p)
sep-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ p)) = inj₂ p
sep-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₁ p) = inj₁ (sep-resp-eq1ᵇ ¬ux ¬uy st p)
sep-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₂ p) = inj₂ p
sep-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₁ p) = inj₁ p
sep-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₂ p) = inj₂ (sep-resp-eq1ᵇ ¬ux ¬uy st p)
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-unit {α = a}) sa = inj₂ (inj₂ (inj₁ sa))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) sp = reassoc∥ᵇ a b c sp
sep-resp-eq1ᵇ ¬ux ¬uy ∥′-comm sp = comm∥ sp
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₁ (xa′ , yb)) =
  inj₁ (mem-eq1ᵇ ¬ux st xa′ , yb)
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₁ (xb , ya′))) =
  inj₂ (inj₁ (xb , mem-eq1ᵇ ¬uy st ya′))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₂ (inj₁ sa′))) =
  inj₂ (inj₂ (inj₁ (sep-resp-eq1ᵇ ¬ux ¬uy st sa′)))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ {α = a} {α′ = a′} {β = b} st) (inj₂ (inj₂ (inj₂ sb))) =
  inj₂ (inj₂ (inj₂ sb))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-dup {α = a} U) sp =
  ⊥-elim (mem-not-unrCx ¬ux U
    ([ (λ z → z) , (λ z → z) ]′ (mem-parInv {α = a} {a} (fst (sep⇒mem (a ∥ a) sp)))))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ sa) = inj₂ (inj₂ (inj₁ sa))
sep-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ sb) = inj₂ (inj₂ (inj₂ sb))

-- ============================================================================
-- (B)  Lift to full ≈, then to ≼ (the ordered sub-context order).
-- ============================================================================

sep-resp-≈ : {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → ¬ Unr (Γ y)
        → Γ ∶ α ≈ β → sep x y α → sep x y β
sep-resp-≈ ¬ux ¬uy ε sp = sp
sep-resp-≈ ¬ux ¬uy (fwd st ◅ rest) sp = sep-resp-≈ ¬ux ¬uy rest (sep-resp-eq1 ¬ux ¬uy st sp)
sep-resp-≈ ¬ux ¬uy (bwd st ◅ rest) sp = sep-resp-≈ ¬ux ¬uy rest (sep-resp-eq1ᵇ ¬ux ¬uy st sp)

-- the key ≼-wk case:  sep ((α₁∥α₂);(β₁∥β₂)) → sep ((α₁;β₁)∥(α₂;β₂)).
sepwk : {x y : 𝔽 n} (a1 a2 b1 b2 : Struct n)
      → sep x y ((a1 ∥ a2) ; (b1 ∥ b2)) → sep x y ((a1 ; b1) ∥ (a2 ; b2))
sepwk a1 a2 b1 b2 (inj₁ sa) = fromA sa
  where fromA : sep _ _ (a1 ∥ a2) → sep _ _ ((a1 ; b1) ∥ (a2 ; b2))
        fromA (inj₁ (xa1 , ya2)) =
          inj₁ (mem-seqL {α = a1} {b1} xa1 , mem-seqL {α = a2} {b2} ya2)
        fromA (inj₂ (inj₁ (xa2 , ya1))) =
          inj₂ (inj₁ (mem-seqL {α = a2} {b2} xa2 , mem-seqL {α = a1} {b1} ya1))
        fromA (inj₂ (inj₂ (inj₁ sa1))) = inj₂ (inj₂ (inj₁ (inj₁ sa1)))
        fromA (inj₂ (inj₂ (inj₂ sa2))) = inj₂ (inj₂ (inj₂ (inj₁ sa2)))
sepwk a1 a2 b1 b2 (inj₂ sb) = fromB sb
  where fromB : sep _ _ (b1 ∥ b2) → sep _ _ ((a1 ; b1) ∥ (a2 ; b2))
        fromB (inj₁ (xb1 , yb2)) =
          inj₁ (mem-seqR {α = a1} {b1} xb1 , mem-seqR {α = a2} {b2} yb2)
        fromB (inj₂ (inj₁ (xb2 , yb1))) =
          inj₂ (inj₁ (mem-seqR {α = a2} {b2} xb2 , mem-seqR {α = a1} {b1} yb1))
        fromB (inj₂ (inj₂ (inj₁ sb1))) = inj₂ (inj₂ (inj₁ (inj₂ sb1)))
        fromB (inj₂ (inj₂ (inj₂ sb2))) = inj₂ (inj₂ (inj₂ (inj₂ sb2)))

mono-mem-≼ : {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → Γ ∶ α ≼ β → x ∈ₘ α → x ∈ₘ β
mono-mem-≼ {x = x} {α = α} {β = β} ¬ux le x∈ x≡0 =
  x∈ (n≤0⇒n≡0 (subst (count x α ≤_) x≡0 (≼⇒count≤ ¬ux le)))
  where n≤0⇒n≡0 : ∀ {m} → m ≤ 0 → m ≡ 0
        n≤0⇒n≡0 z≤n = refl

sep-mono-≼ : {Γ : Ctx n} {x y : 𝔽 n} {α β : Struct n}
        → ¬ Unr (Γ x) → ¬ Unr (Γ y)
        → Γ ∶ α ≼ β → sep x y α → sep x y β
sep-mono-≼ ¬ux ¬uy (≼-refl eq) sp = sep-resp-≈ ¬ux ¬uy eq sp
sep-mono-≼ ¬ux ¬uy (≼-∅ U) ()
sep-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) sp =
  sepwk a1 a2 b1 b2 sp
sep-mono-≼ ¬ux ¬uy (≼-trans p q) sp = sep-mono-≼ ¬ux ¬uy q (sep-mono-≼ ¬ux ¬uy p sp)
sep-mono-≼ ¬ux ¬uy (≼-cong-; {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₁ sa) =
  inj₁ (sep-mono-≼ ¬ux ¬uy p sa)
sep-mono-≼ ¬ux ¬uy (≼-cong-; {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₂ sb) =
  inj₂ (sep-mono-≼ ¬ux ¬uy q sb)
sep-mono-≼ ¬ux ¬uy (≼-cong-∥ {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₁ (xa , yb)) =
  inj₁ (mono-mem-≼ ¬ux p xa , mono-mem-≼ ¬uy q yb)
sep-mono-≼ ¬ux ¬uy (≼-cong-∥ {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₂ (inj₁ (xb , ya))) =
  inj₂ (inj₁ (mono-mem-≼ ¬ux q xb , mono-mem-≼ ¬uy p ya))
sep-mono-≼ ¬ux ¬uy (≼-cong-∥ {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₂ (inj₂ (inj₁ sa))) =
  inj₂ (inj₂ (inj₁ (sep-mono-≼ ¬ux ¬uy p sa)))
sep-mono-≼ ¬ux ¬uy (≼-cong-∥ {α = a} {α′ = a′} {β = b} {β′ = b′} p q) (inj₂ (inj₂ (inj₂ sb))) =
  inj₂ (inj₂ (inj₂ (sep-mono-≼ ¬ux ¬uy q sb)))

-- ============================================================================
-- (C)  The CONCRETE minimal R-RSplit redex.
--      g2 0F = ⟨ msg ‼ `⊤ ⟩   (handle, linear)   g2 1F = ⟨ msg ⁇ `⊤ ⟩  (off-handle, linear)
--      Both are non-unrestricted, and  bodyStruct  does NOT ∥-separate them.
-- ============================================================================

¬u0 : ¬ Unr (P.g2 0F)
¬u0 (⟨ () ⟩)

¬u1 : ¬ Unr (P.g2 1F)
¬u1 (⟨ () ⟩)

-- bodyStruct's normal form (definitional; verified by refl).
bodyNF : Struct 2
bodyNF = ((` 0F) ; ((` 1F) ; [])) ∥ [] ∥ [] ∥ []

body≡NF : P.bodyStruct ≡ bodyNF
body≡NF = refl

-- Stripping empty ∥-arms preserves NON-separation.
sep-∥[]ʳ : {x y : 𝔽 n} (γ : Struct n) → sep x y (γ ∥ []) → sep x y γ
sep-∥[]ʳ γ (inj₁ (_ , 1[])) = ⊥-elim (1[] refl)
sep-∥[]ʳ γ (inj₂ (inj₁ (0[] , _))) = ⊥-elim (0[] refl)
sep-∥[]ʳ γ (inj₂ (inj₂ (inj₁ sγ))) = sγ
sep-∥[]ʳ γ (inj₂ (inj₂ (inj₂ ())))

-- A two-leaf sequence  (` a) ; ((` b) ; [])  has NO separation at all.
sep-seq2-no : {x y : 𝔽 n} (a b : 𝔽 n) → ¬ sep x y ((` a) ; ((` b) ; []))
sep-seq2-no a b (inj₁ ())
sep-seq2-no a b (inj₂ (inj₁ ()))
sep-seq2-no a b (inj₂ (inj₂ ()))

-- bodyNF = (((LEFT ∥ []) ∥ []) ∥ [])  (infixl),  LEFT = (` 0F) ; ((` 1F) ; []).
-- Peel the three empty ∥-arms; the surviving LEFT is a pure sequence ⇒ no sep.
¬sep-bodyNF : ¬ sep 0F 1F bodyNF
¬sep-bodyNF sp = sep-seq2-no {n = 2} {x = 0F} {y = 1F} 0F 1F
  (sep-∥[]ʳ {x = 0F} {y = 1F} L0
    (sep-∥[]ʳ {x = 0F} {y = 1F} (L0 ∥ [])
      (sep-∥[]ʳ {x = 0F} {y = 1F} ((L0 ∥ []) ∥ []) sp)))
  where L0 : Struct 2
        L0 = (` 0F) ; ((` 1F) ; [])

¬sep-body : ¬ sep 0F 1F P.bodyStruct
¬sep-body sp = ¬sep-bodyNF (subst (sep 0F 1F) body≡NF sp)

-- any (γE ∥ γP) with 0F in γE and 1F in γP DOES ∥-separate them.
sep-split : (γE γP : Struct 2) → 0F ∈ₘ γE → 1F ∈ₘ γP → sep 0F 1F (γE ∥ γP)
sep-split γE γP 0∈E 1∈P = inj₁ (0∈E , 1∈P)

-- ============================================================================
-- (D)  THE VACUITY LEMMA: no TP-Par split of bodyStruct can place the handle
--      0F in one component and the off-handle 1F in the other.
-- ============================================================================

no-offhandle-split : (γE γP : Struct 2)
        → P.g2 ∶ γE ∥ γP ≼ P.bodyStruct
        → 0F ∈ₘ γE → 1F ∈ₘ γP → ⊥
no-offhandle-split γE γP ≤body 0∈E 1∈P =
  ¬sep-body (sep-mono-≼ ¬u0 ¬u1 ≤body (sep-split γE γP 0∈E 1∈P))

-- ============================================================================
-- (E)  PROCESS-LEVEL COROLLARY.
--      In the TP-Res body of the minimal R-RSplit redex, the body process is
--      typed at  P.bodyStruct = (` 0F) ; (` 1F) ∥ ... .  By inv-∥, any
--      TP-Par body typing (rsplit thread QE  ∥  sibling QP) yields a split
--      g2 ∶ γE ∥ γP ≼ bodyStruct with g2;γE⊢QE and g2;γP⊢QP.  If the rsplit
--      thread owns the handle (0F ∈ γE) and the sibling owns the OFF-HANDLE
--      (1F ∈ γP), that is impossible.  Hence NO well-typed rsplit redex has a
--      sibling owning the off-handle borrow of the chain being split — the
--      U-rsplit "bad case" (Splits.agda leafRec ?1) is VACUOUS.
-- ============================================================================

no-offhandle-sibling :
    {QE QP : Proc 2}
  → P.g2 ; P.bodyStruct ⊢ₚ (QE ∥ QP)
  → (∀ {γE} → P.g2 ; γE ⊢ₚ QE → 0F ∈ₘ γE)
  → (∀ {γP} → P.g2 ; γP ⊢ₚ QP → 1F ∈ₘ γP)
  → ⊥
no-offhandle-sibling ⊢body ownsE ownsP
  with γE , γP , le , ⊢QE , ⊢QP ← inv-∥ ⊢body =
  no-offhandle-split γE γP le (ownsE ⊢QE) (ownsP ⊢QP)
