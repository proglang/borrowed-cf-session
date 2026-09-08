------------------------------------------------------------------------
-- Applying BindCtxLsplit / BindCtxRsplit at the position the reduction
-- rules pick out.  The hypothesis is exactly what the inversion of the
-- redex typing delivers: the entry of the first binder context at flat
-- position `sum B₁ + q` is the handle ⟨ t₁ ; t₂ ⟩ that gets split.
--
-- The `Fin.cast (sym (sum-++ …)) (sum B₁ ↑ʳ (… ↑ˡ …))` positions are the
-- `SplitRenamings.atk` / `SplitRenamings.inj` variables of the rules with
-- their two trailing `↑ˡ` (into the second binder block and the ambient
-- context) stripped off.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Redex where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Splits.Chain
open import BorrowedCF.Safety.Preservation.Splits.Group

open Nat.Variables
open Fin.Patterns
open ≡-Reasoning

private variable
  t t₁ t₂ : 𝕊 0
  q b₁ : ℕ

------------------------------------------------------------------------
-- R-LSplit

lsplit-bindCtx : ∀ (B₁ : BindGroup) {B₂ q b₁} {s₀ t t₁ t₂ : 𝕊 0}
  {Γ₁ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))} →
  ¬ Skips t₁ → ¬ Skips t₂ → t ≃ t₁ ; t₂ →
  Γ₁ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    ≡ (⟨ t ⟩) →
  BindCtx s₀ (B₁ ++ (q + suc b₁) ∷ B₂) Γ₁ →
  Σ[ Γ₁′ ∈ Ctx (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) ]
      BindCtx s₀ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) Γ₁′
    × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))
                      (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂)) ≡ ⟨ t₁ ⟩)
    × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂)))
                      (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)) ≡ ⟨ t₂ ⟩)
    × Agree (sum B₁ + q) Γ₁ Γ₁′
lsplit-bindCtx B₁ {B₂} {q} {b₁} {t₁ = t₁} {t₂} {Γ₁} ¬S₁ ¬S₂ teq eqT C
  with Γc , f ← mkSame B₁ Γ₁
  with Γg , Γr , refl ← vsplit (q + suc b₁) Γc
  with T , Γg′ , eqg , eqg₁ , eqg₂ , I , Ag ← mkIns q Γg ⟨ t₁ ⟩ ⟨ t₂ ⟩
  with Γ₁′ , Sm ← f {(q + suc (suc b₁)) ∷ B₂} (Γg′ ⸴* Γr)
  with refl ← sym eqg
             ■ sym (V.lookup-++ˡ Γg Γr (q ↑ʳ 0F))
             ■ sym (same-lookupˡ B₁ Sm ((q ↑ʳ 0F) ↑ˡ sum B₂))
             ■ eqT
  = Γ₁′
  , bindCtx-lsplit B₁ ¬S₁ ¬S₂ teq I C Sm
  , (same-lookupʳ B₁ Sm ((q ↑ʳ 0F) ↑ˡ sum B₂) ■ V.lookup-++ˡ Γg′ Γr (q ↑ʳ 0F) ■ eqg₁)
  , (same-lookupʳ B₁ Sm ((q ↑ʳ 1F) ↑ˡ sum B₂) ■ V.lookup-++ˡ Γg′ Γr (q ↑ʳ 1F) ■ eqg₂)
  , same-agree B₁ Sm (Ag Γr)

------------------------------------------------------------------------
-- R-RSplit

rsplit-bindCtx : ∀ (B₁ : BindGroup) {B₂ q b₁} {s₀ t t₁ t₂ : 𝕊 0}
  {Γ₁ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))} →
  ¬ Skips t₁ → ¬ Skips t₂ → t ≃ t₁ ; t₂ →
  Γ₁ ﹫ Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
                (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    ≡ (⟨ t ⟩) →
  BindCtx s₀ (B₁ ++ (q + suc b₁) ∷ B₂) Γ₁ →
  Σ[ Γ₁′ ∈ Ctx (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) ]
      BindCtx s₀ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) Γ₁′
    × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                      (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ≡ ⟨ t₁ ; ret ⟩)
    × (Γ₁′ ﹫ Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂)))
                      (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F)) ≡ ⟨ acq ; t₂ ⟩)
    × Agree (sum B₁ + q) Γ₁ Γ₁′
rsplit-bindCtx B₁ {B₂} {q} {b₁} {t₁ = t₁} {t₂} {Γ₁} ¬S₁ ¬S₂ teq eqT C
  with Γc , f ← mkSame B₁ Γ₁
  with Γg , Γr , refl ← vsplit (q + suc b₁) Γc
  with T , Γg₁ , Γg₂ , eqg , eqg₁ , eqg₂ , I , Ag ← mkInsR q Γg ⟨ t₁ ; ret ⟩ ⟨ acq ; t₂ ⟩
  with Γ₁′ , Sm ← f {(q + 1) ∷ suc b₁ ∷ B₂} (Γg₁ ⸴* (Γg₂ ⸴* Γr))
  with refl ← sym eqg
             ■ sym (V.lookup-++ˡ Γg Γr (q ↑ʳ 0F))
             ■ sym (same-lookupˡ B₁ Sm ((q ↑ʳ 0F) ↑ˡ sum B₂))
             ■ eqT
  = Γ₁′
  , bindCtx-rsplit B₁ ¬S₁ ¬S₂ teq I C Sm
  , (same-lookupʳ B₁ Sm ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))
      ■ V.lookup-++ˡ Γg₁ (Γg₂ ⸴* Γr) (q ↑ʳ 0F) ■ eqg₁)
  , (same-lookupʳ B₁ Sm ((q + 1) ↑ʳ 0F)
      ■ V.lookup-++ʳ Γg₁ (Γg₂ ⸴* Γr) 0F
      ■ V.lookup-++ˡ Γg₂ Γr 0F ■ eqg₂)
  , same-agree B₁ Sm (Ag Γr)
