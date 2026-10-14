-- | THE SYNCHRONISATION LEMMA (wave 2, agent G2).
--
--   At a node `plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q)` of a CLOSED typed
--   process, if BOTH head handles are blocking channels of `Q` -- `0F ∈BC Q`
--   and `head₂ ∈BC Q`, the premise that `Blocked`'s B-Nu rule denies -- then the
--   process reduces.  This is the case the process-progress induction cannot do
--   with the single-thread redex lemmas.
--
--   The proof:
--     1. `Sync/Locate.locate₂` splits `Q` into a two-hole context with the two
--        blocked threads in the holes.  They are distinct threads because a
--        thread blocks on at most one channel (`Sync/Unique.∈BCe-unique`) and
--        `0F ≢ head₂`.
--     2. `Sync/Heads.bc-shape` reads the head kind (`msg p` / `brn p` / `end p`)
--        of each thread's handle off the typing, and `Sync/Heads.head-kinds`
--        -- via the front-kind theory of `Sync/Front.agda` -- says the two kinds
--        are DUAL.  So the only surviving constant pairs are send/recv,
--        select/branch and end ‼/end ⁇, in either order.
--     3. `Sync/Dispatch.dispatch` fires the matching rule, with the endpoints
--        exchanged (`Sync/Binder.binderR`, `heads-rl`) when the first thread
--        sits on the second endpoint.
--
--   Exports for agent G3: `plug-typing` and `sync-redex`.
module BorrowedCF.Safety.Progress.Sync where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Vec.Relation.Unary.All.Properties using (++⁺)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_)

open import BorrowedCF.Safety.Blocked using (_∈BC_; _∈BCe_; head₂)
open import BorrowedCF.Safety.Progress.Sync.Front using (HKind; dualKind)
open import BorrowedCF.Safety.Progress.Sync.Heads using (BCShape; bc-shape; head-kinds)
open import BorrowedCF.Safety.Progress.Sync.Locate
  using (Loc₂; loc₂; locate₂; plug-typing⁺)
open import BorrowedCF.Safety.Progress.Sync.Binder using (0≢head₂)
open import BorrowedCF.Safety.Progress.Sync.Dispatch using (dispatch)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; plug; focusTyping)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; plug₂; wt₁; wt₂
        ; fill₁; fill₂; plug-fill₁; plug-fill₂; wt₁-fill₂; wt₂-fill₁)

open Nat.Variables
open Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  Typing through a process context (the plain form; `Sync/Locate.agda`
--     has the version that also relates the two contexts).

plug-typing : {k n : ℕ} (ctx : ProcessContext k n) (Q : Proc k)
  {Γ : Ctx n} {γ : Struct n} → ChanCx Γ → Γ ; γ ⊢ₚ plug ctx Q →
  Σ[ Δ ∈ Ctx k ] Σ[ σ ∈ Struct k ] ChanCx Δ × (Δ ; σ ⊢ₚ Q)
plug-typing ctx Q Γ-S ⊢P = focusTyping ctx Q Γ-S ⊢P

------------------------------------------------------------------------
-- 2.  Reading the head handles' types off the two threads.

private
  -- Rewriting a typing along a process equation MUST match the equation with
  -- `refl` while both processes are still variables; `subst` here makes Agda
  -- unfold `plug` / `plug₂` / `fill₂` and blows the heap (see Sync/Dispatch).
  transport-⊢ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {X Y : Proc n} →
    X ≡ Y → Γ ; γ ⊢ₚ X → Γ ; γ ⊢ₚ Y
  transport-⊢ refl d = d

  lookup-fst : ∀ {a b n} (Γ₁ : Ctx (suc a)) (Γ₂ : Ctx b) (Δ : Ctx n) →
    Γ₁ ﹫ 0F ≡ ((Γ₁ ⸴* Γ₂) ⸴* Δ) ﹫ 0F
  lookup-fst Γ₁ Γ₂ Δ =
    sym (V.lookup-++ˡ Γ₁ Γ₂ 0F) ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Δ 0F)

  lookup-snd : ∀ {a b n} (Γ₁ : Ctx a) (Γ₂ : Ctx (suc b)) (Δ : Ctx n) →
    Γ₂ ﹫ 0F ≡ ((Γ₁ ⸴* Γ₂) ⸴* Δ) ﹫ ((a ↑ʳ 0F) ↑ˡ n)
  lookup-snd {a = a} Γ₁ Γ₂ Δ =
    sym (V.lookup-++ʳ Γ₁ Γ₂ 0F) ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Δ (a ↑ʳ 0F))

  sync-go : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k))
    (f₁ : Tm k₁) (f₂ : Tm k₂) →
    wt₁ c₀ 0F ∈BCe f₁ →
    wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂) ∈BCe f₂ →
    [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) →
    Σ[ P′ ∈ Proc 0 ]
      plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) ─→ₚ P′
  sync-go ctx b₁ b₂ B₁ B₂ c₀ f₁ f₂ bce₁ bce₂ ⊢P =
    let _ , _ , Δ-S , ⊢ν , _ =
          plug-typing⁺ ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) []ᴬ ⊢P
        Γ₁ , Γ₂ , s , p , N , _ , _ , C , C′ , ⊢Q = inv-ν ⊢ν
        Γbody = ++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Δ-S
        Γa , _ , Γa-S , ⊢th₁ , lka =
          plug-typing⁺ (fill₂ c₀ ⟪ f₂ ⟫) ⟪ f₁ ⟫ Γbody
            (transport-⊢ (sym (plug-fill₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) ⊢Q)
        Γb , _ , Γb-S , ⊢th₂ , lkb =
          plug-typing⁺ (fill₁ c₀ ⟪ f₁ ⟫) ⟪ f₂ ⟫ Γbody
            (transport-⊢ (sym (plug-fill₁ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) ⊢Q)
        _ , _ , sh₁ , lk₁ , ck₁ = bc-shape Γa-S (inv-⟪⟫ ⊢th₁) bce₁
        _ , _ , sh₂ , lk₂ , ck₂ = bc-shape Γb-S (inv-⟪⟫ ⊢th₂) bce₂
        dual-eq =
          head-kinds C C′
            (lookup-fst Γ₁ Γ₂ _ ■ sym (lka 0F)
              ■ cong (Γa ﹫_) (wt₁-fill₂ c₀ ⟪ f₂ ⟫ 0F) ■ lk₁)
            (lookup-snd Γ₁ Γ₂ _ ■ sym (lkb (head₂ (suc b₁ ∷ B₁) b₂ B₂))
              ■ cong (Γb ﹫_) (wt₂-fill₁ c₀ ⟪ f₁ ⟫ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ■ lk₂)
            ck₁ ck₂
    in dispatch ctx b₁ b₂ B₁ B₂ c₀ sh₁ (subst (λ z → BCShape _ z f₂) dual-eq sh₂) ⊢P

------------------------------------------------------------------------
-- 3.  THE SYNCHRONISATION LEMMA.

sync-redex : {k : ℕ} (ctx : ProcessContext k 0) {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  {Q : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)} →
  [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) →
  0F ∈BC Q →
  head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC Q →
  Σ[ P′ ∈ Proc 0 ] plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) ─→ₚ P′
sync-redex ctx {b₁} {b₂} {B₁} {B₂} ⊢P m₁ m₂
  with locate₂ (0≢head₂ b₁ b₂ B₁ B₂) m₁ m₂
... | loc₂ c₀ f₁ f₂ refl bce₁ bce₂ =
  sync-go ctx b₁ b₂ B₁ B₂ c₀ f₁ f₂ bce₁ bce₂ ⊢P
