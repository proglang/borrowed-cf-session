-- | Locating the TWO threads that synchronise, and carrying a typing
--   derivation to a hole.
--
--   `Safety/Progress/Redex/Located.agda` (agent G1) turns ONE `_∈BC_` witness
--   into a `ProcessContext` whose hole is the blocked thread.  `R-Com`,
--   `R-Choice` and `R-Close` consume TWO threads, so this module does the same
--   for a pair: `locate₂` produces the two-hole context
--   `CanonicalPair.ProcessContext₂` that `canon-pair` walks.  The two threads
--   are automatically distinct, because a thread has at most one evaluation
--   position and therefore blocks on at most one channel
--   (`Sync/Unique.∈BCe-unique`).
--
--   `swapLoc₂` exchanges the two holes; the main lemma uses it when the
--   sender sits on the SECOND endpoint, so that `canon-pair` is called with
--   `heads-rl` and the `ν`-sides are exchanged by its own `ν-swap′`.
--
--   `plug-typing⁺` is `Locate.focusTyping` with the extra clause that the
--   hole's context agrees with the ambient one along `weakenThrough` -- which
--   is what links the head handles `0F` / `head₂` of a `ν` to the types the
--   blocked threads give them.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Locate where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Relation.Unary.All.Properties using (++⁺)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Safety.Blocked
open import BorrowedCF.Safety.Progress.Redex.Located using (∈BC⇒located)
open import BorrowedCF.Safety.Progress.Sync.Unique using (∈BCe-unique)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug; compose)
open import BorrowedCF.Simulation.BackwardSoup.Position using (weakenThrough)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; par₂; par₂ˢ; left₂; right₂; bind₂
        ; plug₂; wt₁; wt₂; fill₁; fill₂; plug-fill₁; plug-fill₂)

open Nat.Variables
open Variables
open Fin.Patterns

private variable
  x y : 𝔽 n

private
  ↑ʳ-inj : (p : ℕ) {q : ℕ} {i j : 𝔽 q} → p ↑ʳ i ≡ p ↑ʳ j → i ≡ j
  ↑ʳ-inj zero eq = eq
  ↑ʳ-inj (suc p) eq = ↑ʳ-inj p (Fin.suc-injective eq)

------------------------------------------------------------------------
-- 1.  One thread.

record Loc₁ {n} (P : Proc n) (x : 𝔽 n) : Set where
  constructor loc₁
  field
    {ar}    : ℕ
    ctx₁    : ProcessContext ar n
    tm      : Tm ar
    plug-eq : plug ctx₁ ⟪ tm ⟫ ≡ P
    bc      : weakenThrough ctx₁ x ∈BCe tm

locate₁ : {P : Proc n} → x ∈BC P → Loc₁ P x
locate₁ mem
  with _ , ctx , E , c , d , w , refl , bc ← ∈BC⇒located mem =
  loc₁ ctx (E [ K c ·⟨ d ⟩ w ]*) refl (bcRedex⇒∈BCe E bc)

------------------------------------------------------------------------
-- 2.  Two threads.

record Loc₂ {n} (P : Proc n) (x y : 𝔽 n) : Set where
  constructor loc₂
  field
    {ar₁ ar₂} : ℕ
    ctx₂    : ProcessContext₂ ar₁ ar₂ n
    tm₁     : Tm ar₁
    tm₂     : Tm ar₂
    plug-eq : plug₂ ctx₂ ⟪ tm₁ ⟫ ⟪ tm₂ ⟫ ≡ P
    bc₁     : wt₁ ctx₂ x ∈BCe tm₁
    bc₂     : wt₂ ctx₂ y ∈BCe tm₂

locate₂ : {P : Proc n} → x ≢ y → x ∈BC P → y ∈BC P → Loc₂ P x y
locate₂ ne (thr p) (thr q) = ⊥-elim (ne (∈BCe-unique p q))
locate₂ ne (∥ˡ p) (∥ˡ q)
  with loc₂ c f₁ f₂ eq b₁ b₂ ← locate₂ ne p q =
  loc₂ (left₂ c _) f₁ f₂ (cong (_∥ _) eq) b₁ b₂
locate₂ ne (∥ʳ p) (∥ʳ q)
  with loc₂ c f₁ f₂ eq b₁ b₂ ← locate₂ ne p q =
  loc₂ (right₂ _ c) f₁ f₂ (cong (_ ∥_) eq) b₁ b₂
locate₂ ne (∥ˡ p) (∥ʳ q)
  with loc₁ c₁ f₁ eq₁ b₁ ← locate₁ p
  with loc₁ c₂ f₂ eq₂ b₂ ← locate₁ q =
  loc₂ (par₂ c₁ c₂) f₁ f₂ (cong₂ _∥_ eq₁ eq₂) b₁ b₂
locate₂ ne (∥ʳ p) (∥ˡ q)
  with loc₁ c₁ f₁ eq₁ b₁ ← locate₁ p
  with loc₁ c₂ f₂ eq₂ b₂ ← locate₁ q =
  loc₂ (par₂ˢ c₂ c₁) f₁ f₂ (cong₂ _∥_ eq₂ eq₁) b₁ b₂
locate₂ {P = ν B₁ B₂ P} ne (res p) (res q)
  with loc₂ c f₁ f₂ eq b₁ b₂ ← locate₂ (ne ∘ ↑ʳ-inj (sum B₁ + sum B₂)) p q =
  loc₂ (bind₂ B₁ B₂ c) f₁ f₂ (cong (ν B₁ B₂) eq) b₁ b₂

------------------------------------------------------------------------
-- 3.  Exchanging the two holes.

swap₂ : ProcessContext₂ k₁ k₂ n → ProcessContext₂ k₂ k₁ n
swap₂ (par₂ c₁ c₂) = par₂ˢ c₁ c₂
swap₂ (par₂ˢ c₂ c₁) = par₂ c₂ c₁
swap₂ (left₂ c Q) = left₂ (swap₂ c) Q
swap₂ (right₂ Q c) = right₂ Q (swap₂ c)
swap₂ (bind₂ B₁ B₂ c) = bind₂ B₁ B₂ (swap₂ c)

plug-swap₂ : (c : ProcessContext₂ k₁ k₂ n) (R₁ : Proc k₁) (R₂ : Proc k₂) →
  plug₂ (swap₂ c) R₂ R₁ ≡ plug₂ c R₁ R₂
plug-swap₂ (par₂ c₁ c₂) R₁ R₂ = refl
plug-swap₂ (par₂ˢ c₂ c₁) R₁ R₂ = refl
plug-swap₂ (left₂ c Q) R₁ R₂ = cong (_∥ Q) (plug-swap₂ c R₁ R₂)
plug-swap₂ (right₂ Q c) R₁ R₂ = cong (Q ∥_) (plug-swap₂ c R₁ R₂)
plug-swap₂ (bind₂ B₁ B₂ c) R₁ R₂ = cong (ν B₁ B₂) (plug-swap₂ c R₁ R₂)

wt₁-swap₂ : (c : ProcessContext₂ k₁ k₂ n) (z : 𝔽 n) → wt₁ (swap₂ c) z ≡ wt₂ c z
wt₁-swap₂ (par₂ c₁ c₂) z = refl
wt₁-swap₂ (par₂ˢ c₂ c₁) z = refl
wt₁-swap₂ (left₂ c Q) z = wt₁-swap₂ c z
wt₁-swap₂ (right₂ Q c) z = wt₁-swap₂ c z
wt₁-swap₂ (bind₂ B₁ B₂ c) z = wt₁-swap₂ c ((sum B₁ + sum B₂) ↑ʳ z)

wt₂-swap₂ : (c : ProcessContext₂ k₁ k₂ n) (z : 𝔽 n) → wt₂ (swap₂ c) z ≡ wt₁ c z
wt₂-swap₂ (par₂ c₁ c₂) z = refl
wt₂-swap₂ (par₂ˢ c₂ c₁) z = refl
wt₂-swap₂ (left₂ c Q) z = wt₂-swap₂ c z
wt₂-swap₂ (right₂ Q c) z = wt₂-swap₂ c z
wt₂-swap₂ (bind₂ B₁ B₂ c) z = wt₂-swap₂ c ((sum B₁ + sum B₂) ↑ʳ z)

swapLoc₂ : {P : Proc n} → Loc₂ P x y → Loc₂ P y x
swapLoc₂ {x = x} {y = y} (loc₂ c f₁ f₂ eq b₁ b₂) =
  loc₂ (swap₂ c) f₂ f₁ (plug-swap₂ c ⟪ f₁ ⟫ ⟪ f₂ ⟫ ■ eq)
    (subst (_∈BCe f₂) (sym (wt₁-swap₂ c y)) b₂)
    (subst (_∈BCe f₁) (sym (wt₂-swap₂ c x)) b₁)

------------------------------------------------------------------------
-- 4.  Carrying a typing derivation to the hole, with the context agreement.

plug-typing⁺ : (ctx : ProcessContext k n) (R₀ : Proc k) {Γ : Ctx n} {γ : Struct n} →
  ChanCx Γ → Γ ; γ ⊢ₚ plug ctx R₀ →
  Σ[ Γ′ ∈ Ctx k ] Σ[ γ′ ∈ Struct k ]
    ChanCx Γ′ × (Γ′ ; γ′ ⊢ₚ R₀) × (∀ z → Γ′ ﹫ weakenThrough ctx z ≡ Γ ﹫ z)
plug-typing⁺ hole R₀ Γ-S ⊢P = _ , _ , Γ-S , ⊢P , λ z → refl
plug-typing⁺ (par-left ctx Q) R₀ Γ-S ⊢P
  with _ , _ , _ , ⊢l , _ ← inv-∥ ⊢P = plug-typing⁺ ctx R₀ Γ-S ⊢l
plug-typing⁺ (par-right Q ctx) R₀ Γ-S ⊢P
  with _ , _ , _ , _ , ⊢r ← inv-∥ ⊢P = plug-typing⁺ ctx R₀ Γ-S ⊢r
plug-typing⁺ (bind B₁ B₂ ctx) R₀ {Γ = Γ} Γ-S ⊢P
  with Γ₁ , Γ₂ , _ , _ , _ , _ , _ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′ , γ′ , Γ′-S , ⊢R₀ , lk ←
    plug-typing⁺ ctx R₀ (++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) ⊢body =
  Γ′ , γ′ , Γ′-S , ⊢R₀ ,
  λ z → lk ((sum B₁ + sum B₂) ↑ʳ z) ■ V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ z
