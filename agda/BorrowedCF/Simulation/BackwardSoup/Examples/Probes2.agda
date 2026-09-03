-- Backward simulation, SECOND counterexample hunt (2026-09-03).
--
-- `Probes.agda` recorded the F4 counterexamples of PLAN.md §4 and the strict
-- rules of §6/§7 that killed them.  This module sweeps the remaining
-- suspects: every typed rule whose side conditions the corresponding soup
-- rule does NOT have.  For each suspect it gives the smallest state, the soup
-- step (checked), and either a typing derivation -- which would make it a
-- counterexample -- or the precise premise that blocks the typing.
--
-- The recurring blocker is stated once, as a CHECKED refutation rather than
-- an argument, in §0: the binder structure `structBinder` sequences the
-- handles of ONE group (`structNSeq`), the `≈`/`≼` theory can only turn `∥`
-- into `;` through `∥′-tm-;`, which needs a MOBILE handle, and no handle of a
-- FIRST group is mobile (its session is a factor of the `New` session `s`,
-- hence contains no `acq`).  §0 ports the two ingredients from
-- `Simulation/Support/{BeforeOrder,CloseVacuityProbe}.agda`, which do not
-- typecheck any more (they predate `Ctx = Vec`).
module BorrowedCF.Simulation.BackwardSoup.Examples.Probes2 where

open import Data.Product using (_×_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (_+_; zero; suc)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (AllCx; MobCx; UnrCx)
import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Simulation.Support.Confine
  using (count; unrCx⇒count0; count-≈′; count-≈; count-self)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Reduction.Base as 𝐓E
import BorrowedCF.Reduction.Expressions as 𝐓Ex
import BorrowedCF.Reduction.ExpressionsSoup as 𝐒Red
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open 𝐓 using (_;_⊢ₚ_)
open 𝐓Tm using (_;_⊢_∶_∣_)

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

open Bin using (_Respects_)
open Nat.Variables

private variable
  x y : 𝔽 n
  α β : Struct n

------------------------------------------------------------------------
-- §0.1  `NoAcq`: a session with no `acq` leaf is not mobile.
--
-- Ported verbatim from `Simulation/Support/CloseVacuityProbe.agda` (which no
-- longer loads).  `Mobile ⟨ s ⟩` unfolds to `∃ s′. Bounded s′ × s ≃ acq ; s′`,
-- so a `NoAcq` session cannot be mobile: `≃` preserves `NoAcq`.

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

noAcq-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoAcq (s ⋯ ϕ) → NoAcq s
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

------------------------------------------------------------------------
-- §0.2  Every handle of a SINGLE-group binder list is `NoAcq`, hence not
-- mobile.  `New s` has no `acq` and `BindCtx′` only ever cuts the session
-- into `≃`-factors.

bindCtx-single : ∀ {b} {Γ} → 𝐓.BindCtx s L.[ b ] Γ → 𝐓.BindCtx′ s Γ
bindCtx-single (𝐓.last C) = C
bindCtx-single (𝐓.cons-ret/acq _ _ _ _ C _) = ⊥-elim (𝐓.bindCtx-B≢[] C)
bindCtx-single (𝐓.cons-acq C _) = ⊥-elim (𝐓.bindCtx-B≢[] C)

bindCtx′-¬mobile : ∀ {Γ : Ctx n} → NoAcq s → 𝐓.BindCtx′ s Γ →
  ∀ (z : 𝔽 n) → ¬ Mobile (Γ ﹫ z)
bindCtx′-¬mobile NAs (𝐓.cons s₁ s₂ _ s-split C) zero =
  ¬mobile-noAcq (noAcq-;-fst (noAcq-≃ (≃-sym s-split) NAs))
bindCtx′-¬mobile NAs (𝐓.cons s₁ s₂ _ s-split C) (suc z) =
  bindCtx′-¬mobile (noAcq-;-snd (noAcq-≃ (≃-sym s-split) NAs)) C z

------------------------------------------------------------------------
-- §0.3  The `;`-order of a `Struct`, and its monotonicity under `≼`.
--
-- Ported from `Simulation/Support/BeforeOrder.agda` (which no longer loads),
-- with `Γ x` replaced by `Γ ﹫ x`.  `before x y γ` says that `x` occurs
-- `;`-strictly before `y` somewhere in `γ`.  `≼` can only RELAX a `;` into a
-- `∥` (`≼-wk`), never create one, so `before` is monotone DOWNWARD: if the
-- prescribed structure orders x before y, so must every structure below it.

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
before⇒mem (α ∥ β) (inj₁ bα) = let q = before⇒mem α bα in mem-parL {α = α} {β} (fst q) , mem-parL {α = α} {β} (snd q)
before⇒mem (α ∥ β) (inj₂ bβ) = let q = before⇒mem β bβ in mem-parR {α = α} {β} (fst q) , mem-parR {α = α} {β} (snd q)
before⇒mem (α ; β) (inj₁ (x∈ , y∈)) = mem-seqL {α = α} {β} x∈ , mem-seqR {α = α} {β} y∈
before⇒mem (α ; β) (inj₂ (inj₁ bα)) = let q = before⇒mem α bα in mem-seqL {α = α} {β} (fst q) , mem-seqL {α = α} {β} (snd q)
before⇒mem (α ; β) (inj₂ (inj₂ bβ)) = let q = before⇒mem β bβ in mem-seqR {α = α} {β} (fst q) , mem-seqR {α = α} {β} (snd q)

-- The two ways of refuting `before` on a concrete structure: the head or the
-- tail variable simply does not occur.
-- (x and y must be EXPLICIT: `before _ _ (` z)` is `⊥` whichever they are,
-- so a leaf occurrence carries no information for unification.)
¬before-∉ˡ : ∀ (x y : 𝔽 n) (γ : Struct n) → count x γ ≡ 0 → ¬ before x y γ
¬before-∉ˡ x y γ eq b = fst (before⇒mem γ b) eq

¬before-∉ʳ : ∀ (x y : 𝔽 n) (γ : Struct n) → count y γ ≡ 0 → ¬ before x y γ
¬before-∉ʳ x y γ eq b = snd (before⇒mem γ b) eq

swap-mid : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
swap-mid a b c d =
  +-assoc a b (c + d)
  ■ cong (a +_) (sym (+-assoc b c d) ■ cong (_+ d) (+-comm b c) ■ +-assoc c b d)
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
mem-≼ᵇ {x = x} {α = α} {β = β} ¬u le = mem-resp {x = x} {β} {α} (sym (count-≼-eq ¬u le))

before-resp-eq1 : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
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

before-resp-eq1ᵇ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
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

before-resp-≈ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
              → Γ ∶ α ≈ β → before x y α → before x y β
before-resp-≈ ¬ux ¬uy ≋-refl b = b
before-resp-≈ ¬ux ¬uy (fwd st ◅ rest) b = before-resp-≈ ¬ux ¬uy rest (before-resp-eq1 ¬ux ¬uy st b)
before-resp-≈ ¬ux ¬uy (bwd st ◅ rest) b = before-resp-≈ ¬ux ¬uy rest (before-resp-eq1ᵇ ¬ux ¬uy st b)

-- THE LEVER.  `≼` never creates a `;`-order: if the target orders x before y
-- and neither is mobile, the source must order them too.
before-mono-≼ : ∀ {Γ : Ctx n} → ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y)
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

------------------------------------------------------------------------
-- §1  Com (and Choice) on a NON-HEAD handle of the first group.
--
-- `RUS-Com` fires on ANY thread holding `send ·¹ (v ⊗ 𝓒[ _ × x × _ ])`; it
-- does not look at the endpoint's flags at all.  `R-Com` insists that the
-- send handle be the variable `0F`, i.e. the HEAD of the FIRST group.
--
-- The probe: a single left group of width 3
--     x₀ : ⟨ skip ⟩   x₁ : ⟨ msg ‼ `⊤ ⟩   x₂ : ⟨ end ‼ ⟩
-- (`BindCtx′` happily peels a `⟨ skip ⟩` off the FRONT of a first group --
-- `AcqHeadCtx` only constrains NON-first groups), with `⟪ discard x₀ ⟫` in
-- one thread and `send` on `x₁` in another.  A single group has no flags, so
-- all three handles translate to the SAME soup value `𝓒[ * × 0F × * ]` and
-- the soup cannot tell them apart.
--
-- VERDICT: ill typed.  `structBinder` sequences the group as `x₀ ; x₁ ; x₂`
-- and the two threads compose in PARALLEL; `before-mono-≼` turns that into a
-- checked refutation (`f1-blocked`).

f1-Γ : Ctx 5
f1-Γ = ⟨ skip ⟩ ∷ ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ end ‼ ⟩ ∷ ⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

-- The binder contexts are fine: this shape IS a legal `ν`.
f1-C1 : 𝐓.BindCtx (msg ‼ `⊤ ; end ‼) (3 ∷ [])
          (⟨ skip ⟩ ∷ ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ end ‼ ⟩ ∷ [])
f1-C1 =
  𝐓.last
    (𝐓.cons skip (msg ‼ `⊤ ; end ‼) (λ { (() ; _) }) ≃-skipˡ
      (𝐓.cons (msg ‼ `⊤) (end ‼) (λ { (() ; _) }) ≃-refl
        (𝐓.cons (end ‼) skip (λ ()) ≃-skipʳ (𝐓.nil skip))))

f1-C2 : 𝐓.BindCtx (dual (msg ‼ `⊤) ; end ⁇) (2 ∷ [])
          (⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ [])
f1-C2 =
  𝐓.last
    (𝐓.cons (msg ⁇ `⊤) (end ⁇) (λ { (() ; _) }) ≃-refl
      (𝐓.cons (end ⁇) skip (λ ()) ≃-skipʳ (𝐓.nil skip)))

-- §0.2 applied: NO handle of this group is mobile, so `∥′-tm-;` is unusable
-- anywhere inside it.
f1-first-group-¬mobile :
  ∀ (z : 𝔽 3) → ¬ Mobile ((⟨ skip ⟩ ∷ ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ end ‼ ⟩ ∷ []) ﹫ z)
f1-first-group-¬mobile =
  bindCtx′-¬mobile (new-end⇒noAcq New.msg) (bindCtx-single f1-C1)

a0 a1 a2 : 𝐓Tm.Tm 5
a0 = 𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 0F)
a1 = (𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 1F)))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 2F))
a2 = (𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 3F))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 4F))

P1 : 𝐓.Proc 0
P1 = 𝐓.ν (3 ∷ []) (2 ∷ []) ((𝐓.⟪ a0 ⟫ 𝐓.∥ 𝐓.⟪ a1 ⟫) 𝐓.∥ 𝐓.⟪ a2 ⟫)

C1 : 𝐒.Config 1 3
C1 = 𝑪 P1

-- All three left handles have the SAME soup representation.
C1≡ :
  C1 ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      ((𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])
C1≡ = refl

C1′ : 𝐒.Config 1 3
C1′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])

step-f1-com : C1 𝐑.─→ₚ C1′
step-f1-com =
  𝐑.RUS-Com 1F 2F 0F 0F 1F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷ [])
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷ [])
    (λ ()) 𝐑.left-right refl 𝐒Red.V-K refl refl

-- The three threads type individually ...
⊢a0 : f1-Γ ; ([] ∥ (` 0F)) ⊢ a0 ∶ `⊤ ∣ 𝕀
⊢a0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl))

f1-α f1-β f1-δ f1-der f1-γ : Struct 5
f1-α = [] ∥ (` 0F)
f1-β = ([] ∥ ([] ∥ (` 1F))) ; ([] ∥ (` 2F))
f1-δ = ([] ∥ (` 3F)) ; ([] ∥ (` 4F))
f1-der = (f1-α ∥ f1-β) ∥ f1-δ
-- ... and this is what `TP-Res` prescribes for the body (see `f1-γ≡`).
f1-γ =
  ((((` 0F) ; ((` 1F) ; ((` 2F) ; []))) ∥ [])
    ∥ ((((` 3F) ; ((` 4F) ; [])) ∥ [])))
  ∥ []

f1-γ≡ :
  f1-γ ≡
    ((𝐓.structBinder (3 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
      ∥ (𝐓.structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 3 𝐂.⋯ᵣ 𝐂.wkʳ 0))
    ∥ (([] {n = 0}) 𝐂.⋯ᵣ 𝐂.weaken* 5)
f1-γ≡ = refl

⊢a1 : f1-Γ ; f1-β ⊢ a1 ∶ `⊤ ∣ 𝕀
⊢a1 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`send `⊤)))
      (𝐓Tm.T-Pair par par
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`unit))
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl))))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl)))

⊢a2 : f1-Γ ; f1-δ ⊢ a2 ∶ `⊤ ∣ 𝕀
⊢a2 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`recv `⊤)))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 3F refl)))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 4F refl)))

-- ... but they cannot be glued.  The binder puts 0F `;`-before 1F ...
f1-before : before 0F 1F f1-γ
f1-before = inj₁ (inj₁ (inj₁ (inj₁ ((λ ()) , (λ ())))))

-- ... while the three threads put them in different PARALLEL components.
f1-¬before : ¬ before 0F 1F f1-der
f1-¬before (inj₁ (inj₁ b)) = ¬before-∉ʳ 0F 1F f1-α refl b
f1-¬before (inj₁ (inj₂ b)) = ¬before-∉ˡ 0F 1F f1-β refl b
f1-¬before (inj₂ b)        = ¬before-∉ˡ 0F 1F f1-δ refl b

-- THE REFUTATION.  No `TP-Weaken` bridges the two, because the only `≈` rule
-- that turns `∥` into `;` is `∥′-tm-;` and it needs a MOBILE handle.
f1-¬mob0 : ¬ Mobile (f1-Γ ﹫ 0F)
f1-¬mob0 = ¬mobile-noAcq skip

f1-¬mob1 : ¬ Mobile (f1-Γ ﹫ 1F)
f1-¬mob1 = ¬mobile-noAcq msg

f1-blocked : ¬ (f1-Γ ∶ f1-der ≼ f1-γ)
f1-blocked le =
  f1-¬before (before-mono-≼ {x = 0F} {y = 1F} f1-¬mob0 f1-¬mob1 le f1-before)

------------------------------------------------------------------------
-- §1b  The one-thread variant: `send x₁` BEFORE `discard x₀`.
--
-- Same binder, same soup step, and now a single thread holds both handles --
-- but in the WRONG order.  `;` is not symmetric, and making it so needs
-- `;-commMob`, i.e. again a mobile handle.

a1b : 𝐓Tm.Tm 5
a1b =
  ((𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 1F)))
    𝐓Tm.; (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 0F)))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 2F))

P1b : 𝐓.Proc 0
P1b = 𝐓.ν (3 ∷ []) (2 ∷ []) (𝐓.⟪ a1b ⟫ 𝐓.∥ 𝐓.⟪ a2 ⟫)

C1b : 𝐒.Config 1 2
C1b = 𝑪 P1b

C1b′ : 𝐒.Config 1 2
C1b′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( ((𝐒Tm.* 𝐒Tm.; (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])

step-f1b-com : C1b 𝐑.─→ₚ C1b′
step-f1b-com =
  𝐑.RUS-Com 0F 1F 0F 0F 1F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
     (𝐒Red.□; (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷ [])
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷ [])
    (λ ()) 𝐑.left-right refl 𝐒Red.V-K refl refl

f1b-α f1b-der : Struct 5
f1b-α = (([] ∥ ([] ∥ (` 1F))) ; ([] ∥ (` 0F))) ; ([] ∥ (` 2F))
f1b-der = f1b-α ∥ f1-δ

⊢a1b : f1-Γ ; f1b-α ⊢ a1b ∶ `⊤ ∣ 𝕀
⊢a1b =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-Seq `⊤
      (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`send `⊤)))
        (𝐓Tm.T-Pair par par
          (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`unit))
          (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl))))
      (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl))))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl)))

f1b-¬before : ¬ before 0F 1F f1b-der
f1b-¬before (inj₁ (inj₁ (_ , y∈))) = y∈ refl
f1b-¬before (inj₁ (inj₂ (inj₁ (inj₁ (x∈ , _))))) = x∈ refl
f1b-¬before (inj₁ (inj₂ (inj₁ (inj₂ (inj₁ b))))) =
  ¬before-∉ˡ {n = 5} 0F 1F ([] ∥ ([] ∥ (` 1F))) refl b
f1b-¬before (inj₁ (inj₂ (inj₁ (inj₂ (inj₂ b))))) =
  ¬before-∉ʳ {n = 5} 0F 1F ([] ∥ (` 0F)) refl b
f1b-¬before (inj₁ (inj₂ (inj₂ b))) = ¬before-∉ˡ {n = 5} 0F 1F ([] ∥ (` 2F)) refl b
f1b-¬before (inj₂ b) = ¬before-∉ˡ 0F 1F f1-δ refl b

f1b-blocked : ¬ (f1-Γ ∶ f1b-der ≼ f1-γ)
f1b-blocked le =
  f1b-¬before (before-mono-≼ {x = 0F} {y = 1F} f1-¬mob0 f1-¬mob1 le f1-before)

-- CHOICE.  `RUS-Choice`'s redex pattern `𝓒[ e₁ × x × e₂ ]` is exactly as
-- unconstrained as `RUS-Com`'s, and `R-Choice` pins the `select` handle to
-- `0F` exactly as `R-Com` does; replacing `send`/`recv` by
-- `select i`/`branch` in `a1`/`a2` changes nothing in the analysis above.
-- The Choice case therefore does NOT differ.

------------------------------------------------------------------------
-- §2  Close with a width-2 side.
--
-- `RUS-Close` needs `lookup cs i ≡ (true , [] , [])`, i.e. BOTH endpoints
-- have an empty flag list -- and `UBFrom` produces an empty flag list exactly
-- for a SINGLE-group binder list.  So the two closing handles necessarily sit
-- in a FIRST group, where §0.2 forbids mobility; a width-2 first group is
-- therefore sequential, and its `⟨ end ‼ ⟩` cannot be reached while the other
-- handle is still live.
--
--     x₀ : ⟨ skip ⟩   x₁ : ⟨ end ‼ ⟩        (left, one group of width 2)
--     x₂ : ⟨ end ⁇ ⟩                        (right, one group of width 1)
--
-- The soup closes at once; the typed calculus is NOT stuck (`R-Discard` fires
-- on `x₀`, which IS at `0F`) but it takes a DIFFERENT step, so this would be a
-- genuine counterexample -- if it were well typed.  It is not.

f2-Γ : Ctx 3
f2-Γ = ⟨ skip ⟩ ∷ ⟨ end ‼ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

f2-C1 : 𝐓.BindCtx (skip ; end ‼) (2 ∷ []) (⟨ skip ⟩ ∷ ⟨ end ‼ ⟩ ∷ [])
f2-C1 =
  𝐓.last
    (𝐓.cons skip (end ‼) (λ { (_ ; ()) }) ≃-refl
      (𝐓.cons (end ‼) skip (λ ()) ≃-skipʳ (𝐓.nil skip)))

f2-C2 : 𝐓.BindCtx (dual skip ; end ⁇) (1 ∷ []) (⟨ end ⁇ ⟩ ∷ [])
f2-C2 =
  𝐓.last
    (𝐓.cons (end ⁇) skip (λ { (_ ; ()) })
      (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (𝐓.nil skip))

d0 d1 d2 : 𝐓Tm.Tm 3
d0 = 𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 0F)
d1 = 𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 1F)
d2 = 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 2F)

P2 : 𝐓.Proc 0
P2 = 𝐓.ν (2 ∷ []) (1 ∷ []) ((𝐓.⟪ d0 ⟫ 𝐓.∥ 𝐓.⟪ d1 ⟫) 𝐓.∥ 𝐓.⟪ d2 ⟫)

C2 : 𝐒.Config 1 3
C2 = 𝑪 P2

-- A single group on each side ⇒ no flags ⇒ `RUS-Close` is enabled.
C2≡ :
  C2 ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])
C2≡ = refl

C2′ : 𝐒.Config 1 3
C2′ =
  𝐒.config
    ((false , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷ 𝐒Tm.* ∷ [])

step-f2-close : C2 𝐑.─→ₚ C2′
step-f2-close =
  𝐑.RUS-Close 1F 2F 0F 0F 1F [] [] (λ ()) 𝐑.left-right refl refl refl

⊢d0 : f2-Γ ; ([] ∥ (` 0F)) ⊢ d0 ∶ `⊤ ∣ 𝕀
⊢d0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl))

⊢d1 : f2-Γ ; ([] ∥ (` 1F)) ⊢ d1 ∶ `⊤ ∣ 𝕀
⊢d1 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl))

⊢d2 : f2-Γ ; ([] ∥ (` 2F)) ⊢ d2 ∶ `⊤ ∣ 𝕀
⊢d2 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl))

f2-der f2-γ : Struct 3
f2-der = (([] ∥ (` 0F)) ∥ ([] ∥ (` 1F))) ∥ ([] ∥ (` 2F))
f2-γ = ((((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ ((((` 2F) ; []) ∥ []))) ∥ []

f2-γ≡ :
  f2-γ ≡
    ((𝐓.structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0)
      ∥ (𝐓.structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0))
    ∥ (([] {n = 0}) 𝐂.⋯ᵣ 𝐂.weaken* 3)
f2-γ≡ = refl

f2-¬mob0 : ¬ Mobile (f2-Γ ﹫ 0F)
f2-¬mob0 = ¬mobile-noAcq skip

-- NB `⟨ end ‼ ⟩` is not mobile either: `NoAcq` has an `end` constructor.
f2-¬mob1 : ¬ Mobile (f2-Γ ﹫ 1F)
f2-¬mob1 = ¬mobile-noAcq end

f2-before : before 0F 1F f2-γ
f2-before = inj₁ (inj₁ (inj₁ (inj₁ ((λ ()) , (λ ())))))

f2-¬before : ¬ before 0F 1F f2-der
f2-¬before (inj₁ (inj₁ b)) = ¬before-∉ʳ {n = 3} 0F 1F ([] ∥ (` 0F)) refl b
f2-¬before (inj₁ (inj₂ b)) = ¬before-∉ˡ {n = 3} 0F 1F ([] ∥ (` 1F)) refl b
f2-¬before (inj₂ b)        = ¬before-∉ˡ {n = 3} 0F 1F ([] ∥ (` 2F)) refl b

f2-blocked : ¬ (f2-Γ ∶ f2-der ≼ f2-γ)
f2-blocked le =
  f2-¬before (before-mono-≼ {x = 0F} {y = 1F} f2-¬mob0 f2-¬mob1 le f2-before)

------------------------------------------------------------------------
-- §3a  Drop on the LAST handle of a width-2 FIRST group.
--
--     group 0 (width 2) : x₀ : ⟨ msg ‼ `⊤ ⟩   x₁ : ⟨ ret ⟩
--     group 1 (width 1) : x₂ : ⟨ acq ; end ‼ ⟩
--
-- This is PLAN.md §4's F4(a) moved into the FIRST group, where `cons-ret/acq`
-- has nothing to complain about (`s₂ ≡ end ‼` is not a skip and the next
-- group is acq-headed): the binder context `f3a-C1` CHECKS.  What blocks the
-- process is again §0.2/§0.3: `x₀ : ⟨ msg ‼ `⊤ ⟩` is a first-group handle,
-- hence not mobile, so it cannot be used in a thread parallel to the dropper.
--
-- (In `Pf4` the same group was NON-first, its head was the mobile
-- `⟨ acq ; end ‼ ⟩`, and the strict `¬skips₂` premise was what killed it.)

f3a-Γ : Ctx 5
f3a-Γ = ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ ret ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ ⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

f3a-C1 :
  𝐓.BindCtx (msg ‼ `⊤ ; end ‼) (2 ∷ 1 ∷ [])
    ((⟨ msg ‼ `⊤ ⟩ ∷ ⟨ ret ⟩ ∷ []) V.++ (⟨ acq ; end ‼ ⟩ ∷ []))
f3a-C1 =
  𝐓.cons-ret/acq (msg ‼ `⊤) ≃-refl (λ ())
    (𝐓.cons (msg ‼ `⊤) ret (λ { (() ; _) }) ≃-refl
      (𝐓.cons ret skip (λ ()) ≃-skipʳ (𝐓.nil skip)))
    (𝐓.last
      (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip)))
    (λ { (() ; _) })

f3a-C2 : 𝐓.BindCtx (dual (msg ‼ `⊤) ; end ⁇) (2 ∷ [])
           (⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ [])
f3a-C2 = f1-C2

g0 g1 g2 g3 : 𝐓Tm.Tm 5
g0 = 𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 0F))
g1 = 𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 1F)
g2 = 𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 2F))
g3 = (𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 3F))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 4F))

P3a : 𝐓.Proc 0
P3a =
  𝐓.ν (2 ∷ 1 ∷ []) (2 ∷ [])
    ((𝐓.⟪ g0 ⟫ 𝐓.∥ 𝐓.⟪ g1 ⟫) 𝐓.∥ (𝐓.⟪ g2 ⟫ 𝐓.∥ 𝐓.⟪ g3 ⟫))

C3a : 𝐒.Config 1 4
C3a = 𝑪 P3a

C3a≡ :
  C3a ≡
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])
C3a≡ = refl

C3a′ : 𝐒.Config 1 4
C3a′ =
  𝐒.config
    ((true , 𝐒.acq ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      𝐒Tm.* ∷
      (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])

-- The soup drops `x₁` (slot 0 of endpoint 0) and RELEASES the boundary,
-- although `x₀` of the same group is still live.
step-f3a-drop : C3a 𝐑.─→ₚ C3a′
step-f3a-drop = 𝐑.RUS-Drop 1F 0F 0F [] [] [] refl refl refl

⊢g0 : f3a-Γ ; ([] ∥ ([] ∥ (` 0F))) ⊢ g0 ∶ `⊤ ∣ 𝕀
⊢g0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`send `⊤)))
    (𝐓Tm.T-Pair par par
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`unit))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl)))

⊢g1 : f3a-Γ ; ([] ∥ (` 1F)) ⊢ g1 ∶ `⊤ ∣ 𝕀
⊢g1 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`drop))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl))

⊢g2 : f3a-Γ ; ([] ∥ ([] ∥ (` 2F))) ⊢ g2 ∶ `⊤ ∣ 𝕀
⊢g2 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-AppUnr refl ℙ≤ϵ
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl)))

⊢g3 : f3a-Γ ; (([] ∥ (` 3F)) ; ([] ∥ (` 4F))) ⊢ g3 ∶ `⊤ ∣ 𝕀
⊢g3 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`recv `⊤)))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 3F refl)))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 4F refl)))

f3a-der f3a-γ : Struct 5
f3a-der =
  (([] ∥ ([] ∥ (` 0F))) ∥ ([] ∥ (` 1F)))
  ∥ (([] ∥ ([] ∥ (` 2F))) ∥ (([] ∥ (` 3F)) ; ([] ∥ (` 4F))))
f3a-γ =
  (((((` 0F) ; ((` 1F) ; [])) ∥ ((((` 2F) ; []) ∥ []))))
    ∥ ((((` 3F) ; ((` 4F) ; [])) ∥ [])))
  ∥ []

f3a-γ≡ :
  f3a-γ ≡
    ((𝐓.structBinder (2 ∷ 1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
      ∥ (𝐓.structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 3 𝐂.⋯ᵣ 𝐂.wkʳ 0))
    ∥ (([] {n = 0}) 𝐂.⋯ᵣ 𝐂.weaken* 5)
f3a-γ≡ = refl

f3a-¬mob0 : ¬ Mobile (f3a-Γ ﹫ 0F)
f3a-¬mob0 = ¬mobile-noAcq msg

f3a-¬mob1 : ¬ Mobile (f3a-Γ ﹫ 1F)
f3a-¬mob1 = ¬mobile-noAcq ret

f3a-before : before 0F 1F f3a-γ
f3a-before = inj₁ (inj₁ (inj₁ (inj₁ ((λ ()) , (λ ())))))

f3a-¬before : ¬ before 0F 1F f3a-der
f3a-¬before (inj₁ (inj₁ b)) = ¬before-∉ʳ {n = 5} 0F 1F ([] ∥ ([] ∥ (` 0F))) refl b
f3a-¬before (inj₁ (inj₂ b)) = ¬before-∉ˡ {n = 5} 0F 1F ([] ∥ (` 1F)) refl b
f3a-¬before (inj₂ b) =
  ¬before-∉ˡ {n = 5} 0F 1F
    (([] ∥ ([] ∥ (` 2F))) ∥ (([] ∥ (` 3F)) ; ([] ∥ (` 4F)))) refl b

f3a-blocked : ¬ (f3a-Γ ∶ f3a-der ≼ f3a-γ)
f3a-blocked le =
  f3a-¬before
    (before-mono-≼ {x = 0F} {y = 1F} f3a-¬mob0 f3a-¬mob1 le f3a-before)

------------------------------------------------------------------------
-- §3c  Acquire on the head of group 1 while group 0 is non-empty.
--
-- `C3a` is exactly that state: thread 2 holds `acq ·¹ 𝓒[ phi (0F,0) × 0F × * ]`
-- and group 0 has width 2.  `UBFrom` writes `ϕ[ 2 ] ≡ drop` for the boundary,
-- and `RUS-Acquire` wants `endpointFlags … ≡ before ++ acq ∷ after`.  With the
-- one-element flag list `drop ∷ []` there is no such split -- THE SOUP IS
-- STUCK TOO, so there is nothing to match and no counterexample.
--
-- (The typed side is stuck for the mirror reason: `R-Acq` needs
-- `ν (zero ∷ suc b₁ ∷ B₁) …`, i.e. an EMPTY first group.  This is F4(c) of
-- PLAN.md §4, re-checked here on a first-group instance.)

f3c-flags : 𝐑.endpointFlags (lookup (𝐒.channels C3a) 0F) 0F ≡ 𝐒.drop ∷ []
f3c-flags = refl

f3c-no-acq-slot :
  ∀ (bef aft : L.List 𝐒.Flag) → (𝐒.drop ∷ []) ≢ bef L.++ 𝐒.acq ∷ aft
f3c-no-acq-slot [] aft ()
f3c-no-acq-slot (𝐒.drop ∷ []) aft ()
f3c-no-acq-slot (𝐒.drop ∷ (_ ∷ _)) aft ()
f3c-no-acq-slot (𝐒.acq ∷ bef) aft ()

------------------------------------------------------------------------
-- §3d  POSITIVE check: the state right after a typed `R-Acq`.
--
-- `R-Acq` turns `ν (zero ∷ suc b₁ ∷ B₁) …` into `ν (suc b₁ ∷ B₁) …` and the
-- acquired handle's type from `⟨ acq ; t ⟩` into `⟨ t ⟩`.  The new FIRST group
-- is therefore headed by a handle that does NOT carry an `acq`.  The strict
-- rules accept that: `AcqHeadCtx` is a premise of `cons-ret/acq`/`cons-acq`
-- only, i.e. it constrains the head of a NON-first group.  Checked on a
-- two-group reduct (the second group is still acq-headed, as it must be):

f3d-after :
  𝐓.BindCtx (msg ‼ `⊤ ; end ‼) (1 ∷ 1 ∷ [])
    ((⟨ msg ‼ `⊤ ; ret ⟩ ∷ []) V.++ (⟨ acq ; end ‼ ⟩ ∷ []))
f3d-after =
  𝐓.cons-ret/acq (msg ‼ `⊤) ≃-refl (λ ())
    (𝐓.cons (msg ‼ `⊤ ; ret) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip))
    (𝐓.last
      (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip)))
    (λ { (() ; _) })

-- ... and the same context is REJECTED in non-first position, which is the
-- content of `AcqHeadCtx` (cf. `Probes.f4b-acqHead-blocked`):
f3d-acqHead-first-only :
  ¬ 𝐓.AcqHeadCtx (⟨ skip ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
f3d-acqHead-first-only ah = ah skip

------------------------------------------------------------------------
-- §4 (and §3b)  A `skip` handle that is not at the head, discarded early.
--
--     group 0 (width 3) : x₀ : ⟨ msg ‼ `⊤ ⟩   x₁ : ⟨ skip ⟩   x₂ : ⟨ ret ⟩
--     group 1 (width 1) : x₃ : ⟨ acq ; end ‼ ⟩
--
-- `BindCtx′` DOES accept an interior `⟨ skip ⟩` (`sk4-C1` checks): its
-- `¬ Skips` premises constrain the REMAINING session, not the handle.  So
-- this is the shape to beat.  Two independent facts kill it:
--
--   (i)  it is unreachable: an `lsplit`/`rsplit` that peels a `⟨ skip ⟩` off
--        would have to discharge `¬ Skips skip` (`sk4-split-blocked`), which
--        is exactly the premise added on branch `codex/soup-strict-groups`;
--   (ii) it is not typable with the discard where the soup fires it: `x₀`
--        precedes `x₁` in the group's `;`-chain and is not mobile
--        (`sk4-blocked`).
--
-- This is at the same time probe §3b -- `RUS-Discard` on a handle that is not
-- the `0F` of the first group.  (The other position for an early discard, the
-- HEAD of a non-first group, is `Probes.Pf4b`, killed by `AcqHeadCtx`.)

sk4-Γ : Ctx 6
sk4-Γ =
  ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ skip ⟩ ∷ ⟨ ret ⟩ ∷ ⟨ acq ; end ‼ ⟩
  ∷ ⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

sk4-C1 :
  𝐓.BindCtx (msg ‼ `⊤ ; end ‼) (3 ∷ 1 ∷ [])
    ((⟨ msg ‼ `⊤ ⟩ ∷ ⟨ skip ⟩ ∷ ⟨ ret ⟩ ∷ []) V.++ (⟨ acq ; end ‼ ⟩ ∷ []))
sk4-C1 =
  𝐓.cons-ret/acq (msg ‼ `⊤) ≃-refl (λ ())
    (𝐓.cons (msg ‼ `⊤) ret (λ { (() ; _) }) ≃-refl
      (𝐓.cons skip ret (λ ()) ≃-skipˡ
        (𝐓.cons ret skip (λ ()) ≃-skipʳ (𝐓.nil skip))))
    (𝐓.last
      (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip)))
    (λ { (() ; _) })

-- (i) the strict split constants cannot manufacture the `⟨ skip ⟩`.
sk4-split-blocked : ¬ (¬ Skips {0} skip)
sk4-split-blocked ¬sk = ¬sk skip

h0 h1 h2 h3 : 𝐓Tm.Tm 6
h0 = 𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 0F))
h1 = (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 1F))
     𝐓Tm.; (𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 2F))
h2 = 𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 3F))
h3 = (𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 4F))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 5F))

P4 : 𝐓.Proc 0
P4 =
  𝐓.ν (3 ∷ 1 ∷ []) (2 ∷ [])
    ((𝐓.⟪ h0 ⟫ 𝐓.∥ 𝐓.⟪ h1 ⟫) 𝐓.∥ (𝐓.⟪ h2 ⟫ 𝐓.∥ 𝐓.⟪ h3 ⟫))

C4 : 𝐒.Config 1 4
C4 = 𝑪 P4

C4≡ :
  C4 ≡
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
                𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ])) ∷
      (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])
C4≡ = refl

C4′ : 𝐒.Config 1 4
C4′ =
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
                     𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ])) ∷
      (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])

-- `RUS-Discard` is the least constrained rule of all: any thread, any value.
step-f4-discard : C4 𝐑.─→ₚ C4′
step-f4-discard =
  𝐑.RUS-Discard 1F
    ((𝐒Red.□; (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
                𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ])) ∷ [])
    (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K)
    refl

⊢h0 : sk4-Γ ; ([] ∥ ([] ∥ (` 0F))) ⊢ h0 ∶ `⊤ ∣ 𝕀
⊢h0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const (𝐓Tm.`send `⊤)))
    (𝐓Tm.T-Pair par par
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`unit))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl)))

⊢h1 : sk4-Γ ; (([] ∥ (` 1F)) ; ([] ∥ (` 2F))) ⊢ h1 ∶ `⊤ ∣ 𝕀
⊢h1 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl)))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`drop))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl)))

sk4-der sk4-γ : Struct 6
sk4-der =
  (([] ∥ ([] ∥ (` 0F))) ∥ (([] ∥ (` 1F)) ; ([] ∥ (` 2F))))
  ∥ (([] ∥ ([] ∥ (` 3F))) ∥ (([] ∥ (` 4F)) ; ([] ∥ (` 5F))))
sk4-γ =
  (((((` 0F) ; ((` 1F) ; ((` 2F) ; []))) ∥ ((((` 3F) ; []) ∥ []))))
    ∥ ((((` 4F) ; ((` 5F) ; [])) ∥ [])))
  ∥ []

sk4-γ≡ :
  sk4-γ ≡
    ((𝐓.structBinder (3 ∷ 1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
      ∥ (𝐓.structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 4 𝐂.⋯ᵣ 𝐂.wkʳ 0))
    ∥ (([] {n = 0}) 𝐂.⋯ᵣ 𝐂.weaken* 6)
sk4-γ≡ = refl

sk4-¬mob0 : ¬ Mobile (sk4-Γ ﹫ 0F)
sk4-¬mob0 = ¬mobile-noAcq msg

sk4-¬mob1 : ¬ Mobile (sk4-Γ ﹫ 1F)
sk4-¬mob1 = ¬mobile-noAcq skip

sk4-before : before 0F 1F sk4-γ
sk4-before = inj₁ (inj₁ (inj₁ (inj₁ ((λ ()) , (λ ())))))

sk4-¬before : ¬ before 0F 1F sk4-der
sk4-¬before (inj₁ (inj₁ b)) = ¬before-∉ʳ {n = 6} 0F 1F ([] ∥ ([] ∥ (` 0F))) refl b
sk4-¬before (inj₁ (inj₂ b)) =
  ¬before-∉ˡ {n = 6} 0F 1F (([] ∥ (` 1F)) ; ([] ∥ (` 2F))) refl b
sk4-¬before (inj₂ b) =
  ¬before-∉ˡ {n = 6} 0F 1F
    (([] ∥ ([] ∥ (` 3F))) ∥ (([] ∥ (` 4F)) ; ([] ∥ (` 5F)))) refl b

sk4-blocked : ¬ (sk4-Γ ∶ sk4-der ≼ sk4-γ)
sk4-blocked le =
  sk4-¬before
    (before-mono-≼ {x = 0F} {y = 1F} sk4-¬mob0 sk4-¬mob1 le sk4-before)

------------------------------------------------------------------------
-- §5  Handles inside data: an expression step, then the communication step.
--
-- A handle is passed through a pair and re-bound by `let⊗`.  The TYPED
-- `E-PairElim` substitutes a VARIABLE (`` ` 0F ``) for a variable, the soup's
-- substitutes the handle triple `𝓒[ * × 0F × * ]` -- and the two agree on the
-- nose, which is exactly the compositionality that the translation-inversion
-- step (PLAN.md §8 (a)) will need.  After the expression step the `send`
-- redex sits under the frame `□; …` with the handle syntactically at
-- `𝓒[ … ]`, and `RUS-Com` / `R-Com` match.

f5-Γ : Ctx 4
f5-Γ = ⟨ msg ‼ `⊤ ⟩ ∷ ⟨ end ‼ ⟩ ∷ ⟨ msg ⁇ `⊤ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

f5-C1 : 𝐓.BindCtx (msg ‼ `⊤ ; end ‼) (2 ∷ []) (⟨ msg ‼ `⊤ ⟩ ∷ ⟨ end ‼ ⟩ ∷ [])
f5-C1 =
  𝐓.last
    (𝐓.cons (msg ‼ `⊤) (end ‼) (λ { (() ; _) }) ≃-refl
      (𝐓.cons (end ‼) skip (λ ()) ≃-skipʳ (𝐓.nil skip)))

e5a e5a′ e5b : 𝐓Tm.Tm 4
e5a =
  (𝐓Tm.`let⊗ ((𝐓Tm.` 0F) 𝐓Tm.⊗ 𝐓Tm.*)
     `in (𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 0F))))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 1F))
e5a′ =
  (𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (𝐓Tm.* 𝐓Tm.⊗ (𝐓Tm.` 0F)))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 1F))
e5b =
  (𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 2F))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F))

P5 P5′ P5″ : 𝐓.Proc 0
P5  = 𝐓.ν (2 ∷ []) (2 ∷ []) ((𝐓.⟪ e5a ⟫ 𝐓.∥ 𝐓.⟪ e5b ⟫) 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)
P5′ = 𝐓.ν (2 ∷ []) (2 ∷ []) ((𝐓.⟪ e5a′ ⟫ 𝐓.∥ 𝐓.⟪ e5b ⟫) 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)
P5″ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.* 𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F)) ⟫
      𝐓.∥ 𝐓.⟪ 𝐓Tm.* 𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F)) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

C5 : 𝐒.Config 1 3
C5 = 𝑪 P5

-- The handle sits inside the pair, as `𝓒[ … ]`; the `let⊗`-bound occurrence
-- is a plain soup VARIABLE.
C5≡ :
  C5 ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( ((𝐒Tm.`let⊗ (𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] 𝐒Tm.⊗ 𝐒Tm.*)
          `in (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ (𝐒Tm.` 0F))))
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      𝐒Tm.* ∷
      [])
C5≡ = refl

C5′ : 𝐒.Config 1 3
C5′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( ((𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ (𝐒Tm.* 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      𝐒Tm.* ∷
      [])

step-f5-exp : C5 𝐑.─→ₚ C5′
step-f5-exp =
  𝐑.RUS-Exp 0F
    (𝐒Red.E-Ctx (𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))
      (𝐒Red.E-□
        (𝐒Red.E-PairElim
          (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K) 𝐒Red.V-K)))

red-f5-exp : P5 𝐓𝐑.─→ₚ P5′
red-f5-exp =
  𝐓𝐑.R-Bind
    (𝐓𝐑.R-Par
      (𝐓𝐑.R-Par
        (𝐓𝐑.R-Exp
          (𝐓Ex.E-Ctx (𝐓E.□; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 1F)))
            (𝐓Ex.E-□ (𝐓Ex.E-PairElim 𝐓E.V-` 𝐓E.V-K))))))

-- THE POINT: substituting the handle triple in the soup gives exactly the
-- translation of the typed reduct, in which a VARIABLE was substituted.
f5-exp-exact : 𝑪 P5′ ≡ C5′
f5-exp-exact = refl

C5″ : 𝐒.Config 1 3
C5″ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      𝐒Tm.* ∷
      [])

step-f5-com : C5′ 𝐑.─→ₚ C5″
step-f5-com =
  𝐑.RUS-Com 0F 1F 0F 0F 1F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷ [])
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷ [])
    (λ ()) 𝐑.left-right refl 𝐒Red.V-K refl refl

red-f5-com : P5′ 𝐓𝐑.─→ₚ P5″
red-f5-com =
  𝐓𝐑.R-Com
    {e = 𝐓Tm.*}
    {E₁ = (𝐓E.□; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F))) ∷ []}
    {E₂ = (𝐓E.□; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F))) ∷ []}
    𝐓E.V-K

f5-com-exact : 𝑪 P5″ ≡ C5″
f5-com-exact = refl

------------------------------------------------------------------------
-- §6  Canonical position via `≋`: a redex nested away from its binder.
--
--   P6 = ν_a [2][1] ( ⟪ end⁇ z ⟫
--                     ∥ ν_b [1][1] ( ⟪ discard x₀ ; end‼ x₁ ⟫
--                                    ∥ ⟪ end‼ y₀ ; end⁇ y₁ ⟫ ) )
--
-- The `discard` is on `ν_a`'s handle `x₀` but the thread lives under `ν_b`,
-- while `R-Discard` wants the dropper as the LEFT component of a `∥` directly
-- under ITS OWN `ν`.  `R-Struct` repairs this with FOUR `≋` rules, all
-- present:
--
--   ν-ext′   (under ν-cong′)  pull `ν_b` out of the `∥`
--   ν-comm′                   swap `ν_a` inside `ν_b`
--   ∥-assoc′ / ∥-comm′        bring the dropper to the front
--
-- and `∥-assoc′` is needed in the BACKWARD direction, which `_≋_` supplies
-- because it is an `EqClosure` (`bwd`).  NOTHING IS MISSING: in particular no
-- rule that moves a `ν` INWARD is needed -- `ν-ext′` used backwards is that
-- rule, and `≋` is symmetric.

f6-thr-a f6-thr-b : 𝐓Tm.Tm 5
f6-thr-a =
  (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 2F))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 3F))
f6-thr-b =
  (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F))
  𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F))

P6 : 𝐓.Proc 0
P6 =
  𝐓.ν (2 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 2F) ⟫
     𝐓.∥ 𝐓.ν (1 ∷ []) (1 ∷ []) (𝐓.⟪ f6-thr-a ⟫ 𝐓.∥ 𝐓.⟪ f6-thr-b ⟫))

-- After `ν-ext′`, `ν-comm′` and the two `∥` rules.
P6′ : 𝐓.Proc 0
P6′ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.ν (2 ∷ []) (1 ∷ [])
      (𝐓.⟪ (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 0F))
           𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 1F)) ⟫
       𝐓.∥ (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 2F) ⟫
            𝐓.∥ 𝐓.⟪ (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 3F))
                    𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 4F)) ⟫)))

p6-≋ : P6 𝐓.≋ P6′
p6-≋ =
  𝐓.ν-cong (fwd 𝐓.ν-ext′ ◅ ≋-refl)
  ◅◅ (fwd 𝐓.ν-comm′ ◅ ≋-refl)
  ◅◅ 𝐓.ν-cong (𝐓.ν-cong 𝐓.∥-assoc)
  ◅◅ 𝐓.ν-cong (𝐓.ν-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl))
  ◅◅ 𝐓.ν-cong (𝐓.ν-cong (bwd 𝐓.∥-assoc′ ◅ ≋-refl))

P6″ : 𝐓.Proc 0
P6″ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.ν (1 ∷ []) (1 ∷ [])
      (𝐓.⟪ 𝐓Tm.* 𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F)) ⟫
       𝐓.∥ (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫
            𝐓.∥ 𝐓.⟪ (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 2F))
                    𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F)) ⟫)))

red-f6 : P6 𝐓𝐑.─→ₚ P6″
red-f6 =
  𝐓𝐑.R-Struct p6-≋
    (𝐓𝐑.R-Bind
      (𝐓𝐑.R-Discard
        {b₁ = 1} {B₁ = []} {B₂ = 1 ∷ []}
        {P = 𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫
             𝐓.∥ 𝐓.⟪ (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 2F))
                     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F)) ⟫}
        {E = (𝐓E.□; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F))) ∷ []}))
    ≋-refl

C6 : 𝐒.Config 2 3
C6 = 𝑪 P6

C6≡ :
  C6 ≡
  𝐒.config
    ((true , [] , []) ∷ (true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 2F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 3F × 𝐒Tm.* ])) ∷
      [])
C6≡ = refl

C6′ : 𝐒.Config 2 3
C6′ =
  𝐒.config
    ((true , [] , []) ∷ (true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      ((𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 2F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 3F × 𝐒Tm.* ])) ∷
      [])

step-f6-discard : C6 𝐑.─→ₚ C6′
step-f6-discard =
  𝐑.RUS-Discard 1F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷ [])
    (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K)
    refl

-- The typed reduct flattens to `C6′` UP TO the channel renumbering that
-- `ν-comm′` caused (`ν_b` is now the outer binder, so it gets channel 0) and
-- the induced thread order -- failure mode F2 of PLAN.md §2, which
-- `GlobalImage` absorbs (`logicalChannels` + the thread embedding).  No `≋`
-- is needed for the IMAGE; `≋` was needed only to expose the redex.
f6-reduct-image :
  𝑪 P6″ ≡
  𝐒.config
    ((true , [] , []) ∷ (true , [] , []) ∷ [])
    ( (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 2F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 3F × 𝐒Tm.* ]) ∷
      ((𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
        𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])) ∷
      [])
f6-reduct-image = refl

------------------------------------------------------------------------
-- §7  Things noticed on the way (the loopholes that were checked and closed).
--
-- (a) `∥′-dup` and `≼-∅` are the only rules that change a variable's
--     multiplicity, and both need `Unr`.  No handle is `Unr` (`Unr ⟨ s ⟩`
--     asks for `⊥`), so `count` is EXACTLY preserved by `≼` (`count-≼-eq`).
--     That is what makes §0.3's lever applicable and, incidentally, what
--     stops a thread from silently "also" holding a handle it does not use.

¬unr-handle : ∀ {s} → ¬ Unr ⟨ s ⟩
¬unr-handle ⟨ () ⟩

-- (b) `T-Conv` cannot create mobility at a use site: `≃` preserves `NoAcq`,
--     so no `≃`-conversion turns a first-group handle into `⟨ acq ; … ⟩`.

f7-conv-cannot-make-mobile : ∀ {s u} → NoAcq s → s ≃ u → ¬ Mobile ⟨ u ⟩
f7-conv-cannot-make-mobile NAs eq = ¬mobile-noAcq (noAcq-≃ eq NAs)

-- (c) Recursion does not open a hole either.  `Bounded (mu s)` IS derivable,
--     so `Mobile ⟨ acq ; mu s ⟩` can hold -- but a `New`-derived session still
--     has no `acq`, and `noAcq-≃` covers `≃𝕊-μ` (unfolding), which is the
--     only case of the proof that is not immediate.

f7-mu : ¬ Mobile ⟨ mu (msg ‼ `⊤ ; (` 0F)) ⟩
f7-mu = ¬mobile-noAcq (mu (msg ; `-))

-- (d) `T-Weaken` cannot reorder either: `≼` may RELAX a `;` into a `∥`
--     (`≼-wk`, `;-≼-∥`) but never the converse -- that is precisely
--     `before-mono-≼`.  The dual direction is available and harmless:

f7-seq-≼-par : ∀ {n} {Γ : Ctx n} {α β} → Γ ∶ α ; β ≼ α ∥ β
f7-seq-≼-par = ;-≼-∥

-- (e) The effect discipline explains why the hunt comes up empty.  Reading
--     off `Reduction/Base.agda`, the ONLY frames whose structure puts
--     resources `;`-BEFORE the hole are
--          `app₁ v L`     (`TF-app₁` with `Arr.IsL a`, structure `γ ; □`)
--          `v ⊗□`         (`TF-⊗□`  with `p/s ≡ seq`, structure `γ ; □`)
--     and BOTH force the hole to be PURE (`appLeft` gives `ϵ₁ ≡ ℙ`;
--     `Seq⇒Pure seq ϵ₁ ϵ₂` gives `ϵ₂ ≡ ℙ`).  Every other frame
--     (`app₂`, `□⊗`, `□;`, `let`, `let⊗`, `case`) puts the hole FIRST.
--     Consequently a redex whose constant has effect `𝕀` -- `send`, `recv`,
--     `select`, `branch`, `end p`, `drop`, `discard`, i.e. exactly the
--     constants whose typed rule pins the handle to `0F` -- can never be
--     exposed while a handle that precedes it in the binder `;`-chain is
--     still unconsumed.  The PURE constants (`fork`, `new`, `lsplit`,
--     `rsplit`, `acq`) can sit in such a delayed position, and for them the
--     typed rules impose no position: `R-LSplit`/`R-RSplit` fire at an
--     arbitrary offset `q` inside an arbitrary group, `R-New`/`R-Fork` are
--     positionless, and `R-Acq` is pinned only through `⊢ᴮ` (§3c).
--
-- (f) Summary of the sweep.  Under the strict rules of PLAN.md §6/§7 every
--     remaining suspect is ill typed, and always for one of exactly three
--     reasons:
--        * the group `;`-order (§1, §1b, §2, §3a, §4) -- `before-mono-≼`
--          plus "no first-group handle is mobile" (§0.2);
--        * `AcqHeadCtx` (`Probes.f4b-acqHead-blocked`, re-checked as
--          `f3d-acqHead-first-only`);
--        * `⊢ᴮ` / the flag discipline (§3c), where the SOUP is stuck too.
--     NO COUNTEREXAMPLE SURVIVES.
