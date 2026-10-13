-- | Phase 3 support (`BackwardSoup/PLAN.md` §9, P3): the two general levers
--   that `Examples/Probes2.agda` §0 established for its concrete probes.
--
--     * §1  `NoAcq`: a session with no `acq` leaf is not `Mobile`; a `New`
--           session is `NoAcq`, `≃` preserves `NoAcq`, and every handle of a
--           `BindCtx′` block over a `NoAcq` session is therefore immobile.
--     * §2  `before x y γ`, the `;`-order of a `Struct`, and `before-mono-≼`:
--           `≼` can only RELAX a `;` into a `∥` (`≼-wk`), never create one,
--           so the order is monotone DOWNWARD.  The only `≈` rule that turns
--           a `∥` into a `;` is `∥′-tm-;`, which needs a MOBILE handle.
--
--   This module deliberately imports NO term syntax: `_⋯_` of
--   `Types/Substitution.agda` and `_⋯_` of `Terms/Base.agda` are different
--   operators and cannot be in scope together.  `Position.agda` re-exports
--   everything here.
--
--   `Probes2` is left untouched and keeps its own copies; it could be
--   simplified to import them from here.
module BorrowedCF.Simulation.BackwardSoup.GroupOrder where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.Symmetric as Sym
  using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (AllCx; MobCx; UnrCx)

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.Support.Confine
  using (count; unrCx⇒count0; count-≈′; count-≈)

open 𝐓 using (BindGroup; BindCtx; BindCtx′; last; cons-ret/acq; cons-acq; nil; cons)

open Bin using (_Respects_)
open Nat.Variables

private
  variable
    x y : 𝔽 n
    α β : Struct n

------------------------------------------------------------------------
-- 1.  `NoAcq`: a session with no `acq` leaf is not mobile.
--
-- Lifted from `Examples/Probes2.agda` §0.1 (which in turn ported it from
-- the retired `Simulation/Support/CloseVacuityProbe.agda`).  `Mobile ⟨ s ⟩`
-- unfolds to `∃ s′. Bounded s′ × s ≃ acq ; s′`, so a `NoAcq` session cannot
-- be mobile: `≃` preserves `NoAcq`.

data NoAcq {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoAcq (` x)
  end  : NoAcq (end {n} p)
  ret  : NoAcq (ret {n})
  skip : NoAcq (skip {n})
  msg  : NoAcq (msg {n} p T)
  brn  : NoAcq s₁ → NoAcq s₂ → NoAcq (brn p s₁ s₂)
  mu   : NoAcq s → NoAcq (mu s)
  _;_  : NoAcq s₁ → NoAcq s₂ → NoAcq (s₁ ; s₂)

¬noAcq-acq : ¬ NoAcq (acq {n})
¬noAcq-acq ()

noAcq-;-fst : NoAcq (s₁ ; s₂) → NoAcq s₁
noAcq-;-fst (x ; _) = x

noAcq-;-snd : NoAcq (s₁ ; s₂) → NoAcq s₂
noAcq-;-snd (_ ; y) = y

new⇒noAcq : New s → NoAcq s
new⇒noAcq New.`-        = `-
new⇒noAcq New.msg       = msg
new⇒noAcq (New.brn x y) = brn (new⇒noAcq x) (new⇒noAcq y)
new⇒noAcq (New.mu x)    = mu (new⇒noAcq x)
new⇒noAcq (x New.; y)   = new⇒noAcq x ; new⇒noAcq y
new⇒noAcq New.skip      = skip

new-end⇒noAcq : New s → NoAcq (s ; end p)
new-end⇒noAcq N = new⇒noAcq N ; end

noAcq-⋯ᵣ : NoAcq s → {ρ : m →ᵣ n} → NoAcq (s ⋯ ρ)
noAcq-⋯ᵣ `-        = `-
noAcq-⋯ᵣ end       = end
noAcq-⋯ᵣ ret       = ret
noAcq-⋯ᵣ skip      = skip
noAcq-⋯ᵣ msg       = msg
noAcq-⋯ᵣ (brn x y) = brn (noAcq-⋯ᵣ x) (noAcq-⋯ᵣ y)
noAcq-⋯ᵣ (mu x)    = mu (noAcq-⋯ᵣ x)
noAcq-⋯ᵣ (x ; y)   = noAcq-⋯ᵣ x ; noAcq-⋯ᵣ y

noAcq-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoAcq s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoAcq (`/id (ϕ x))) → NoAcq (s ⋯ ϕ)
noAcq-⋯ `- ∀ϕ = ∀ϕ _
noAcq-⋯ end ∀ϕ = end
noAcq-⋯ ret ∀ϕ = ret
noAcq-⋯ skip ∀ϕ = skip
noAcq-⋯ msg ∀ϕ = msg
noAcq-⋯ (brn x y) ∀ϕ = brn (noAcq-⋯ x ∀ϕ) (noAcq-⋯ y ∀ϕ)
noAcq-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noAcq-⋯ x λ where
  zero    → subst NoAcq (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoAcq (wk-`/id _) (noAcq-⋯ᵣ (∀ϕ z))
noAcq-⋯ (x ; y) ∀ϕ = noAcq-⋯ x ∀ϕ ; noAcq-⋯ y ∀ϕ

noAcq-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} →
            NoAcq (s ⋯ ϕ) → NoAcq s
noAcq-⋯⁻¹ {s = ` _} x = `-
noAcq-⋯⁻¹ {s = acq} x = ⊥-elim (¬noAcq-acq x)
noAcq-⋯⁻¹ {s = end p} x = end
noAcq-⋯⁻¹ {s = ret} x = ret
noAcq-⋯⁻¹ {s = skip} x = skip
noAcq-⋯⁻¹ {s = msg p t} x = msg
noAcq-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noAcq-⋯⁻¹ x) (noAcq-⋯⁻¹ y)
noAcq-⋯⁻¹ {s = mu s} (mu x) = mu (noAcq-⋯⁻¹ x)
noAcq-⋯⁻¹ {s = _ ; _} (x ; y) = noAcq-⋯⁻¹ x ; noAcq-⋯⁻¹ y

noAcq-≃ : NoAcq {n} Respects _≃_
noAcq-≃ ≋-refl na = na
noAcq-≃ (x ◅ xs) na = noAcq-≃ xs (go x na)
  where
  go : NoAcq {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noAcq-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (fwd (≃𝕊-msg eq))  msg       = msg
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noAcq-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y
  go (bwd (≃𝕊-msg eq))  msg       = msg
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)

¬mobile-noAcq : NoAcq s → ¬ Mobile ⟨ s ⟩
¬mobile-noAcq NAs ⟨ _ , _ , s≃ ⟩ = ¬noAcq-acq (noAcq-;-fst (noAcq-≃ s≃ NAs))

-- `T-Conv` cannot create mobility at a use site.
conv-cannot-make-mobile : NoAcq s → s ≃ s₁ → ¬ Mobile ⟨ s₁ ⟩
conv-cannot-make-mobile NAs eq = ¬mobile-noAcq (noAcq-≃ eq NAs)

------------------------------------------------------------------------
-- 2.  No handle of a `BindCtx′` block over a `NoAcq` session is mobile.

bindCtx′-¬mobile : ∀ {Γ : Ctx n} → NoAcq s → BindCtx′ s Γ →
  ∀ (z : 𝔽 n) → ¬ Mobile (Γ ﹫ z)
bindCtx′-¬mobile NAs (cons s₁ s₂ _ s-split C) zero =
  ¬mobile-noAcq (noAcq-;-fst (noAcq-≃ (≃-sym s-split) NAs))
bindCtx′-¬mobile NAs (cons s₁ s₂ _ s-split C) (suc z) =
  bindCtx′-¬mobile (noAcq-;-snd (noAcq-≃ (≃-sym s-split) NAs)) C z

bindCtx-single : ∀ {b} {Γ} → BindCtx s L.[ b ] Γ → BindCtx′ s Γ
bindCtx-single (last C) = C
bindCtx-single (cons-ret/acq _ _ _ _ C _) = ⊥-elim (𝐓.bindCtx-B≢[] C)
bindCtx-single (cons-acq C _) = ⊥-elim (𝐓.bindCtx-B≢[] C)

-- A one-group side over a `NoAcq` session has no mobile handle at all
-- (`Probes2.f1-first-group-¬mobile` in general form).
bindCtx-single-¬mobile : ∀ {b} {Γ : Ctx (sum L.[ b ])} →
  NoAcq s → BindCtx s L.[ b ] Γ →
  ∀ (z : 𝔽 (sum L.[ b ])) → ¬ Mobile (Γ ﹫ z)
bindCtx-single-¬mobile NAs C = bindCtx′-¬mobile NAs (bindCtx-single C)

-- The FRONT BLOCK of a multi-group side sits over a `NoAcq` session too: the
-- `cons-ret/acq` split `s₁ ; s₂ ≃ s` cuts `s` into `≃`-factors, and the block's
-- own session is `s₁ ; ret`.  Combined with `bindCtx′-¬mobile` this says that
-- no handle of the FIRST group of a `New`-derived side is mobile.
noAcq-front : NoAcq s → s₁ ; s₂ ≃ s → NoAcq (s₁ ; ret)
noAcq-front NAs s≃ = noAcq-;-fst (noAcq-≃ (≃-sym s≃) NAs) ; ret

------------------------------------------------------------------------
-- 3.  The `;`-order of a `Struct`, and its monotonicity under `≼`.
--
-- Lifted from `Examples/Probes2.agda` §0.3 (ported there from the retired
-- `Simulation/Support/BeforeOrder.agda`).  `before x y γ` says that `x`
-- occurs `;`-strictly before `y` somewhere in `γ`.  `≼` can only RELAX a `;`
-- into a `∥` (`≼-wk`), never create one, so `before` is monotone DOWNWARD.

infix 4 _∈ₘ_

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

mem-not-unrCx : ∀ {Γ : Ctx n} → ¬ Unr (Γ ﹫ x) → AllCx Unr Γ α → x ∈ₘ α → ⊥
mem-not-unrCx ¬u U x∈ = x∈ (unrCx⇒count0 ¬u U)

mobCx⇒count0 : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → MobCx Γ α → count x α ≡ 0
mobCx⇒count0 ¬m []        = refl
mobCx⇒count0 ¬m (C₁ ∥ C₂) = cong₂ _+_ (mobCx⇒count0 ¬m C₁) (mobCx⇒count0 ¬m C₂)
mobCx⇒count0 ¬m (C₁ ; C₂) = cong₂ _+_ (mobCx⇒count0 ¬m C₁) (mobCx⇒count0 ¬m C₂)
mobCx⇒count0 {x = x} ¬m (`_ {y} py) with x Fin.≟ y
... | yes refl = ⊥-elim (¬m py)
... | no  _    = refl

mem-not-mobCx : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → MobCx Γ α → x ∈ₘ α → ⊥
mem-not-mobCx ¬m U x∈ = x∈ (mobCx⇒count0 ¬m U)

mem-eq1 : ∀ {Γ : Ctx n} → ¬ Unr (Γ ﹫ x) → Γ ∶ α ≈′ β → x ∈ₘ α → x ∈ₘ β
mem-eq1 {x = x} {α} {β} ¬u st = mem-resp {x = x} {α} {β} (count-≈′ ¬u st)

mem-eq1ᵇ : ∀ {Γ : Ctx n} → ¬ Unr (Γ ﹫ x) → Γ ∶ α ≈′ β → x ∈ₘ β → x ∈ₘ α
mem-eq1ᵇ {x = x} {α} {β} ¬u st = mem-resp {x = x} {β} {α} (sym (count-≈′ ¬u st))

before : 𝔽 n → 𝔽 n → Struct n → Set
before x y (` z)   = ⊥
before x y []      = ⊥
before x y (α ∥ β) = before x y α ⊎ before x y β
before x y (α ; β) = ((x ∈ₘ α) × (y ∈ₘ β)) ⊎ before x y α ⊎ before x y β

before⇒mem : (γ : Struct n) → before x y γ → (x ∈ₘ γ) × (y ∈ₘ γ)
before⇒mem (` z) ()
before⇒mem [] ()
before⇒mem (α ∥ β) (inj₁ bα) =
  let q = before⇒mem α bα in
  mem-parL {α = α} {β} (proj₁ q) , mem-parL {α = α} {β} (proj₂ q)
before⇒mem (α ∥ β) (inj₂ bβ) =
  let q = before⇒mem β bβ in
  mem-parR {α = α} {β} (proj₁ q) , mem-parR {α = α} {β} (proj₂ q)
before⇒mem (α ; β) (inj₁ (x∈ , y∈)) =
  mem-seqL {α = α} {β} x∈ , mem-seqR {α = α} {β} y∈
before⇒mem (α ; β) (inj₂ (inj₁ bα)) =
  let q = before⇒mem α bα in
  mem-seqL {α = α} {β} (proj₁ q) , mem-seqL {α = α} {β} (proj₂ q)
before⇒mem (α ; β) (inj₂ (inj₂ bβ)) =
  let q = before⇒mem β bβ in
  mem-seqR {α = α} {β} (proj₁ q) , mem-seqR {α = α} {β} (proj₂ q)

¬before-∉ˡ : ∀ (x y : 𝔽 n) (γ : Struct n) → count x γ ≡ 0 → ¬ before x y γ
¬before-∉ˡ x y γ eq b = proj₁ (before⇒mem γ b) eq

¬before-∉ʳ : ∀ (x y : 𝔽 n) (γ : Struct n) → count y γ ≡ 0 → ¬ before x y γ
¬before-∉ʳ x y γ eq b = proj₂ (before⇒mem γ b) eq

private
  swap-mid : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  swap-mid a b c d =
    +-assoc a b (c + d)
    ■ cong (a +_)
        (sym (+-assoc b c d) ■ cong (_+ d) (Nat.+-comm b c) ■ +-assoc c b d)
    ■ sym (+-assoc a c (b + d))

count-≼-eq : ∀ {Γ : Ctx n} → ¬ Unr (Γ ﹫ x) → Γ ∶ α ≼ β → count x α ≡ count x β
count-≼-eq ¬u (≼-refl eq) = count-≈ ¬u eq
count-≼-eq ¬u (≼-∅ U) = sym (unrCx⇒count0 ¬u U)
count-≼-eq {x = x} ¬u (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) =
  swap-mid (count x a1) (count x a2) (count x b1) (count x b2)
count-≼-eq ¬u (≼-trans p q) = count-≼-eq ¬u p ■ count-≼-eq ¬u q
count-≼-eq ¬u (≼-cong-; p q) = cong₂ _+_ (count-≼-eq ¬u p) (count-≼-eq ¬u q)
count-≼-eq ¬u (≼-cong-∥ p q) = cong₂ _+_ (count-≼-eq ¬u p) (count-≼-eq ¬u q)

mem-≼ᵇ : ∀ {Γ : Ctx n} → ¬ Unr (Γ ﹫ x) → Γ ∶ α ≼ β → x ∈ₘ β → x ∈ₘ α
mem-≼ᵇ {x = x} {α = α} {β = β} ¬u le =
  mem-resp {x = x} {β} {α} (sym (count-≼-eq ¬u le))

before-resp-eq1 : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
                → Γ ∶ α ≈′ β → before x y α → before x y β
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (x∈ab , y∈c))
  with mem-seqInv {α = a} {b} x∈ab
... | inj₁ x∈a = inj₁ (x∈a , mem-seqR {α = b} {c} y∈c)
... | inj₂ x∈b = inj₂ (inj₂ (inj₁ (x∈b , y∈c)))
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₁ (x∈a , y∈b)))) =
  inj₁ (x∈a , mem-seqL {α = b} {c} y∈b)
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₂ (inj₁ ba)))) =
  inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ (inj₂ (inj₂ bb)))) =
  inj₂ (inj₂ (inj₂ (inj₁ bb)))
before-resp-eq1 ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ bc)) =
  inj₂ (inj₂ (inj₂ (inj₂ bc)))
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₁ (x∈a , y∈b)) =
  inj₁ (mem-eq1 (¬ux ∘ unr⇒mobile) st x∈a , y∈b)
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₁ ba)) =
  inj₂ (inj₁ (before-resp-eq1 ¬ux ¬uy st ba))
before-resp-eq1 ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ bb)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₁ (x∈a , y∈b)) =
  inj₁ (x∈a , mem-eq1 (¬uy ∘ unr⇒mobile) st y∈b)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₂ bb)) =
  inj₂ (inj₂ (before-resp-eq1 ¬ux ¬uy st bb))
before-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₁ ba) = ba
before-resp-eq1 ¬ux ¬uy (∥′-unit {α = a}) (inj₂ ())
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₁ ba)) = inj₁ ba
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ (inj₂ bb)) = inj₂ (inj₁ bb)
before-resp-eq1 ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ bc) = inj₂ (inj₂ bc)
before-resp-eq1 ¬ux ¬uy ∥′-comm (inj₁ ba) = inj₂ ba
before-resp-eq1 ¬ux ¬uy ∥′-comm (inj₂ bb) = inj₁ bb
before-resp-eq1 ¬ux ¬uy (∥′-cong₁ st) (inj₁ ba) = inj₁ (before-resp-eq1 ¬ux ¬uy st ba)
before-resp-eq1 ¬ux ¬uy (∥′-cong₁ st) (inj₂ bb) = inj₂ bb
before-resp-eq1 ¬ux ¬uy (∥′-dup {α = a} U) b =
  ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U (proj₁ (before⇒mem a b)))
before-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ ba) = inj₂ (inj₁ ba)
before-resp-eq1 ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ bb) = inj₂ (inj₂ bb)

before-resp-eq1ᵇ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
                 → Γ ∶ α ≈′ β → before x y β → before x y α
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₁ (x∈a , y∈bc))
  with mem-seqInv {α = b} {c} y∈bc
... | inj₁ y∈b = inj₂ (inj₁ (inj₁ (x∈a , y∈b)))
... | inj₂ y∈c = inj₁ (mem-seqL {α = a} {b} x∈a , y∈c)
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ ba)) =
  inj₂ (inj₁ (inj₂ (inj₁ ba)))
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₁ (x∈b , y∈c)))) =
  inj₁ (mem-seqR {α = a} {b} x∈b , y∈c)
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₂ (inj₁ bb)))) =
  inj₂ (inj₁ (inj₂ (inj₂ bb)))
before-resp-eq1ᵇ ¬ux ¬uy (;′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ (inj₂ (inj₂ bc)))) =
  inj₂ (inj₂ bc)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₁ (x∈a′ , y∈b)) =
  inj₁ (mem-eq1ᵇ (¬ux ∘ unr⇒mobile) st x∈a′ , y∈b)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₁ ba′)) =
  inj₂ (inj₁ (before-resp-eq1ᵇ ¬ux ¬uy st ba′))
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₁ st) (inj₂ (inj₂ bb)) = inj₂ (inj₂ bb)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₁ (x∈a , y∈b′)) =
  inj₁ (x∈a , mem-eq1ᵇ (¬uy ∘ unr⇒mobile) st y∈b′)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₁ ba)) = inj₂ (inj₁ ba)
before-resp-eq1ᵇ ¬ux ¬uy (;′-cong₂ st) (inj₂ (inj₂ bb′)) =
  inj₂ (inj₂ (before-resp-eq1ᵇ ¬ux ¬uy st bb′))
before-resp-eq1ᵇ ¬ux ¬uy (∥′-unit {α = a}) ba = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₁ ba) = inj₁ (inj₁ ba)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₁ bb)) = inj₁ (inj₂ bb)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-assoc {α = a} {β = b} {γ = c}) (inj₂ (inj₂ bc)) = inj₂ bc
before-resp-eq1ᵇ ¬ux ¬uy ∥′-comm (inj₁ bb) = inj₂ bb
before-resp-eq1ᵇ ¬ux ¬uy ∥′-comm (inj₂ ba) = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ st) (inj₁ ba′) =
  inj₁ (before-resp-eq1ᵇ ¬ux ¬uy st ba′)
before-resp-eq1ᵇ ¬ux ¬uy (∥′-cong₁ st) (inj₂ bb) = inj₂ bb
before-resp-eq1ᵇ ¬ux ¬uy (∥′-dup {α = a} U) b =
  ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U
    ([ (λ z → z) , (λ z → z) ]′
      (mem-parInv {α = a} {a} (proj₁ (before⇒mem (a ∥ a) b)))))
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₁ (x∈a , y∈b)) =
  [ (λ Ua → ⊥-elim (mem-not-mobCx ¬ux Ua x∈a))
  , (λ Ub → ⊥-elim (mem-not-mobCx ¬uy Ub y∈b)) ]′ U
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₁ ba)) = inj₁ ba
before-resp-eq1ᵇ ¬ux ¬uy (∥′-tm-; {α = a} {β = b} U) (inj₂ (inj₂ bb)) = inj₂ bb

before-resp-≈ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
              → Γ ∶ α ≈ β → before x y α → before x y β
before-resp-≈ ¬ux ¬uy ≋-refl b = b
before-resp-≈ ¬ux ¬uy (fwd st ◅ rest) b =
  before-resp-≈ ¬ux ¬uy rest (before-resp-eq1 ¬ux ¬uy st b)
before-resp-≈ ¬ux ¬uy (bwd st ◅ rest) b =
  before-resp-≈ ¬ux ¬uy rest (before-resp-eq1ᵇ ¬ux ¬uy st b)

-- THE LEVER.  `≼` never creates a `;`-order: if the target orders x before y
-- and neither is mobile, the source must order them too.
before-mono-≼ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
              → Γ ∶ α ≼ β → before x y β → before x y α
before-mono-≼ ¬ux ¬uy (≼-refl eq) b = before-resp-≈ ¬ux ¬uy (≈-sym eq) b
before-mono-≼ ¬ux ¬uy (≼-∅ {α = β} U) b =
  ⊥-elim (mem-not-unrCx (¬ux ∘ unr⇒mobile) U (proj₁ (before⇒mem β b)))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₁ (x∈a1 , y∈b1))) =
  inj₁ (mem-parL {α = a1} {a2} x∈a1 , mem-parL {α = b1} {b2} y∈b1)
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₂ (inj₁ ba1))) =
  inj₂ (inj₁ (inj₁ ba1))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₁ (inj₂ (inj₂ bb1))) =
  inj₂ (inj₂ (inj₁ bb1))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₁ (x∈a2 , y∈b2))) =
  inj₁ (mem-parR {α = a1} {a2} x∈a2 , mem-parR {α = b1} {b2} y∈b2)
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₂ (inj₁ ba2))) =
  inj₂ (inj₁ (inj₂ ba2))
before-mono-≼ ¬ux ¬uy (≼-wk {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) (inj₂ (inj₂ (inj₂ bb2))) =
  inj₂ (inj₂ (inj₂ bb2))
before-mono-≼ ¬ux ¬uy (≼-trans p q) b =
  before-mono-≼ ¬ux ¬uy p (before-mono-≼ ¬ux ¬uy q b)
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₁ (x∈a′ , y∈b′)) =
  inj₁ (mem-≼ᵇ (¬ux ∘ unr⇒mobile) p x∈a′ , mem-≼ᵇ (¬uy ∘ unr⇒mobile) q y∈b′)
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₂ (inj₁ ba′)) =
  inj₂ (inj₁ (before-mono-≼ ¬ux ¬uy p ba′))
before-mono-≼ ¬ux ¬uy (≼-cong-; p q) (inj₂ (inj₂ bb′)) =
  inj₂ (inj₂ (before-mono-≼ ¬ux ¬uy q bb′))
before-mono-≼ ¬ux ¬uy (≼-cong-∥ p q) (inj₁ ba′) = inj₁ (before-mono-≼ ¬ux ¬uy p ba′)
before-mono-≼ ¬ux ¬uy (≼-cong-∥ p q) (inj₂ bb′) = inj₂ (before-mono-≼ ¬ux ¬uy q bb′)

-- No handle is unrestricted: `count` is EXACTLY preserved by `≼`.
¬unr-handle : ∀ {s} → ¬ Unr ⟨ s ⟩
¬unr-handle ⟨ () ⟩

