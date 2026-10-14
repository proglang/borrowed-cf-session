-- | front-block-nonzero: a com/close/choice redex bind group `BL` whose front
--   channel is `msg`-typed has a NONZERO first block, i.e. no leading `cons-acq`
--   (pending-acq / dropped-not-reacquired) zero-block.  This lets `R-Com`
--   (pattern `suc b1 ; B1`) fire after the confinement pins the consumed handle.
--
--   A leading zero-block is `cons-acq`, exposing `BindCtx (acq ; s) B G`; the
--   front channel's session is then `≃ acq ; _` (via `bindCtx-inv-msg`), and the
--   send gives `≃ msg p T ; _`, clashing by `AtomHead.msg;≄acq;` (leading
--   atom-kind rigidity for the DEFINITE first action).
module BorrowedCF.Simulation.Backward.FrontBlock where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open TP using ( BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil
              ; bindCtx-inv-msg; bindCtx⇒chanCtx; bindCtx-B≢[] )
open import BorrowedCF.Types.Syntax using (𝕊; msg; acq; end; _;_; Pol; 𝕋)
open import BorrowedCF.Types.Equivalence using (_≃_; ≃-⟨⟩⁻¹)
open import BorrowedCF.Types.AtomHead using (msg;≄acq;)
open import BorrowedCF.Reduction.Base using (chanCx-lookup)
open import Data.Nat.ListAction using (sum)
open import Data.List using (_++_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat.Base using (NonZero)
open import BorrowedCF.Simulation.Support.Confine using (+≡0)
open TP using (⊢ᴮ_)
open import Data.Fin.Properties using (toℕ-injective)

open Fin.Patterns

private variable
  pm : Pol
  B B′ : BindGroup

-- Acq-headed block group with explicitly nonzero first block: no msg front.
acq-front-suc-⊥ : ∀ {n s′} {G : Ctx (sum (suc n ∷ B′))}
  → BindCtx (acq ; s′) (suc n ∷ B′) G → lookup G 0F ≃ ⟨ msg pm T ⟩ → ⊥
acq-front-suc-⊥ {G = g ∷ G′} C lk
  with s₀ , g≡ ← chanCx-lookup (bindCtx⇒chanCtx C) 0F =
  msg;≄acq; (proj₁ (proj₂ (bindCtx-inv-msg s₀≃msg C′)))
  where
    s₀≃msg = ≃-⟨⟩⁻¹ (subst (_≃ ⟨ msg _ _ ⟩) g≡ lk)
    C′ = subst (\ h → BindCtx (acq ; _) _ (h ∷ G′)) g≡ C

xto0 : ∀ {N} (x : 𝔽 (suc N)) → Fin.toℕ x ≡ 0 → x ≡ 0F
xto0 x tx = toℕ-injective tx

-- The [0] case, EXPLICIT shape: front channel of the first (suc b₁) block sits
-- under a cons-acq wrapper, so it is acq-headed; clash with the msg send.
front-zero-⊥ : ∀ {b₁ B₂ˢ G} → BindCtx (s ; end p) (0 ∷ suc b₁ ∷ B₂ˢ) G
  → lookup G 0F ≃ ⟨ msg pm T ⟩ → ⊥
front-zero-⊥ (cons-acq C′) lk = acq-front-suc-⊥ C′ lk
front-zero-⊥ (cons-ret/acq s₁ s≃ (nil (_ ; ())) restC) lk

-- The consumed handle pinned to the front of `B₁ˢ ++ suc b₁ ∷ B₂ˢ` (`sum B₁ˢ ≡ 0`)
-- forces `B₁ˢ ≡ []` (no leading pending-acq zero-block): a nonzero-leading B₁ˢ is
-- ruled out by `sum`, a >=2 B₁ˢ by well-formedness, a single [0] by front-zero-⊥.
front-block-nonzero : ∀ (B₁ˢ B₂ˢ : BindGroup) (b₁ : ℕ) {G₁ : Ctx (sum (B₁ˢ ++ suc b₁ ∷ B₂ˢ))}
  → BindCtx (s ; end p) (B₁ˢ ++ suc b₁ ∷ B₂ˢ) G₁ → sum B₁ˢ ≡ 0 → ⊢ᴮ (B₁ˢ ++ suc b₁ ∷ B₂ˢ)
  → (x : 𝔽 (sum (B₁ˢ ++ suc b₁ ∷ B₂ˢ))) → Fin.toℕ x ≡ 0 → lookup G₁ x ≃ ⟨ msg pm T ⟩ → B₁ˢ ≡ []
front-block-nonzero [] B₂ˢ b₁ C sum0 wf x tx lk = refl
front-block-nonzero (suc w ∷ rest) B₂ˢ b₁ C () wf x tx lk
front-block-nonzero (0 ∷ []) B₂ˢ b₁ C sum0 wf x tx lk
  rewrite xto0 x tx = ⊥-elim (front-zero-⊥ C lk)
front-block-nonzero (0 ∷ w′ ∷ rest′) B₂ˢ b₁ C sum0 (nzw′ ∷ _) x tx lk =
  ⊥-elim (Nat.<-irrefl refl (subst (0 Nat.<_) (proj₁ (+≡0 sum0)) (Nat.>-nonZero⁻¹ w′ ⦃ nzw′ ⦄)))

------------------------------------------------------------------------
-- Pin-free version.  The front block is nonzero (no leading pending-acq
-- `cons-acq` block) purely from the msg-typed front handle (`lookup G 0F ≃
-- msg`), with NO `sum B₁ˢ ≡ 0` confinement/`before`-ordering pin.  Leading
-- zero-blocks are peeled by `cons-acq`, each accumulating an `acq ;` prefix
-- onto the session; the first nonzero block's front leaf is then acq-headed,
-- clashing with the msg send via `acq-front-suc-⊥` (StartsKind rigidity).
------------------------------------------------------------------------

-- Front leaf of an acq-headed bind-ctx (arbitrary leading-zero nesting) is
-- never msg.
front-acq-⊥ : ∀ {s′} (B : BindGroup) {G : Ctx (sum B)} (x : 𝔽 (sum B))
  → BindCtx (acq ; s′) B G → Fin.toℕ x ≡ 0 → lookup G x ≃ ⟨ msg pm T ⟩ → ⊥
front-acq-⊥ (suc n ∷ B′) x C tx lk
  rewrite xto0 x tx = acq-front-suc-⊥ C lk
front-acq-⊥ (0 ∷ B′) x (cons-acq C) tx lk = front-acq-⊥ B′ x C tx lk
front-acq-⊥ (0 ∷ B′) x (cons-ret/acq s₁ s≃ (nil (_ ; ())) restC) tx lk
front-acq-⊥ (0 ∷ []) x (last (nil (() ; _))) tx lk

-- BL's front block is nonzero: no leading `cons-acq`, proved directly from the
-- msg-typed front handle (the `New` protocol makes the block `msg`-headed),
-- with NO ordering / `before` / confinement pin.  This is exactly what
-- `front-block-nonzero` obtained from its `sum B₁ˢ ≡ 0` precondition, now
-- discharged structurally.
front-block-nonzero′ : ∀ {B G} → BindCtx (s ; end p) B G
  → (x : 𝔽 (sum B)) → Fin.toℕ x ≡ 0 → lookup G x ≃ ⟨ msg pm T ⟩
  → ∃[ b ] ∃[ B′ ] B ≡ suc b ∷ B′
front-block-nonzero′ {B = suc b ∷ B′} C x tx lk = b , B′ , refl
front-block-nonzero′ {B = 0 ∷ B′} (cons-acq C) x tx lk = ⊥-elim (front-acq-⊥ B′ x C tx lk)
front-block-nonzero′ {B = 0 ∷ B′} (cons-ret/acq s₁ s≃ (nil (_ ; ())) restC) x tx lk
front-block-nonzero′ {B = 0 ∷ []} (last (nil (_ ; ()))) x tx lk
front-block-nonzero′ {B = []} C x tx lk = ⊥-elim (bindCtx-B≢[] C)
