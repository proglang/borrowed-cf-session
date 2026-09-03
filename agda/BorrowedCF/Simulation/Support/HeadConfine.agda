-- | Confinement for the HEAD-of-the-first-group redexes: `R-Discard` and
--   `R-Drop`.  The consumed handle is variable `0F` of a binder
--   `ν (suc bh ∷ D₁) D₂`, so -- by linearity -- the frame `E` and the
--   parallel residual `P` both factor through the renaming that skips it.
--
--   Structure copied from `SplitConfine.acq-confine` (the `zero ∷ suc b₁ ∷ B₁`
--   case), with the counting lemma adapted to the group list `suc bh ∷ D₁`
--   and with `discard` / `drop`'s own non-`Unr` inversion.
module BorrowedCF.Simulation.Support.HeadConfine where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Context using (Ctx; Struct)
open 𝐓 using (_;_⊢ₚ_; inv-∥; inv-ν; inv-⟪⟫; BindGroup; structBinder)
open import BorrowedCF.Context.Base using (_∥_)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Simulation.Support.Confine
  using (count; count-self; count0⇒∉dom; ≼⇒count≤)
open import BorrowedCF.Simulation.Support.InvFrame
  using (strengthen-frame; inv-app; inv-var-count; arg-type)
open import BorrowedCF.Simulation.Support.Strengthen
  using (strengthen-Proc-gen; Inverter; mk-thin)
open import BorrowedCF.Simulation.Support.FrameRename using (⋯ᶠ*-cong)
open import BorrowedCF.Simulation.Support.StructDom
  using (count-structBinder-lt; count-weaken*-lo; count-⋯ᵣwkʳ-↑ˡ)
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Properties using (toℕ-↑ˡ)
open import Data.List using (_∷_)
open Nat using (_≤_; _<_; ≤-trans; m≤m+n; m≤n+m; +-monoˡ-≤; n≤0⇒n≡0; s≤s⁻¹; s≤s; z≤n)

------------------------------------------------------------------------
-- 1.  No handle is unrestricted, and `discard` / `drop` consume one.

¬unr-handle : ∀ {s} → ¬ Unr ⟨ s ⟩
¬unr-handle ⟨ () ⟩

fn-discard-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {T U a ϵ}
  → Γ ; β ⊢ K `discard ∶ T ⟨ a ⟩→ U ∣ ϵ → ⟨ skip ⟩ ≃ T
fn-discard-dom (T-Const `discard) = ≃-refl
fn-discard-dom (T-Conv (dom≃ `→ cod≃) _ d) = ≃-trans (fn-discard-dom d) dom≃
fn-discard-dom (T-Weaken _ d) = fn-discard-dom d

fn-drop-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {T U a ϵ}
  → Γ ; β ⊢ K `drop ∶ T ⟨ a ⟩→ U ∣ ϵ → ⟨ ret ⟩ ≃ T
fn-drop-dom (T-Const `drop) = ≃-refl
fn-drop-dom (T-Conv (dom≃ `→ cod≃) _ d) = ≃-trans (fn-drop-dom d) dom≃
fn-drop-dom (T-Weaken _ d) = fn-drop-dom d

discard-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {dir} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K `discard ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ → ¬ Unr (lookup Γ x)
discard-app-nonUnr (T-AppUnr _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))) u)
discard-app-nonUnr (T-AppLin _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))) u)
discard-app-nonUnr (T-AppLeft _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))) u)
discard-app-nonUnr (T-AppRight _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))) u)
discard-app-nonUnr (T-Conv _ _ d) u = discard-app-nonUnr d u
discard-app-nonUnr (T-Weaken _ d) u = discard-app-nonUnr d u

drop-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {dir} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K `drop ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ → ¬ Unr (lookup Γ x)
drop-app-nonUnr (T-AppUnr _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u)
drop-app-nonUnr (T-AppLin _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u)
drop-app-nonUnr (T-AppLeft _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u)
drop-app-nonUnr (T-AppRight _ _ ⊢fn ⊢arg) u =
  ¬unr-handle (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u)
drop-app-nonUnr (T-Conv _ _ d) u = drop-app-nonUnr d u
drop-app-nonUnr (T-Weaken _ d) u = drop-app-nonUnr d u

------------------------------------------------------------------------
-- 2.  The handle 0F occurs exactly once in the `TP-Res` body structure.

count-handle-head : ∀ (bh : ℕ) (D₁ D₂ : BindGroup) {m} (γ : Struct m) →
  let C₁ = suc bh ∷ D₁ in
  count 0F
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum D₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder D₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum D₂)) ) ≡ 1
count-handle-head bh D₁ D₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = suc bh ∷ D₁
    0<C₁ : 0 < sum C₁
    0<C₁ = s≤s z≤n
    partA : count 0F (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum D₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum D₂)) (0F ↑ˡ sum D₂)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum D₂) (structBinder C₁) 0F
          ■ count-structBinder-lt C₁ 0F 0<C₁
    partB : count 0F (structBinder D₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder D₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (0F ↑ˡ sum D₂)
          ■ cong (count (0F ↑ˡ sum D₂)) (wkˡ≡weaken* (sum C₁) (structBinder D₂))
          ■ count-weaken*-lo (sum C₁) (structBinder D₂) (0F ↑ˡ sum D₂) 0↑<C₁
      where
        0↑<C₁ : Fin.toℕ (Fin.zero {bh + sum D₁} ↑ˡ sum D₂) < sum C₁
        0↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ (Fin.zero {bh + sum D₁}) (sum D₂))) 0<C₁
        wkˡ≡weaken* : ∀ b {j} (δ : Struct j) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count 0F (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum D₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum D₂) γ (Fin.zero {bh + sum D₁ + sum D₂ + m}) (s≤s z≤n)

headN-eq : ∀ (bh : ℕ) (D₁ D₂ : BindGroup) {m} →
  0 + suc ((bh + sum D₁) + sum D₂ + m) ≡ sum (suc bh ∷ D₁) + sum D₂ + m
headN-eq bh D₁ D₂ = refl

mp≡handle-head : ∀ (bh : ℕ) (D₁ D₂ : BindGroup) {m} →
  Fin.cast (headN-eq bh D₁ D₂ {m}) (0 ↑ʳ 0F) ≡ 0F
mp≡handle-head bh D₁ D₂ = refl

------------------------------------------------------------------------
-- 3.  The two confinement lemmas.

-- Exactly the left-hand-side shape of `R-Discard` / `R-Drop`: the frame and
-- the residual are weakenings of ones that do not mention the handle.
HeadConfined : ∀ {m} (bh : ℕ) (D₁ D₂ : BindGroup)
  (E : Frame* (sum (suc bh ∷ D₁) + sum D₂ + m))
  (P : 𝐓.Proc (sum (suc bh ∷ D₁) + sum D₂ + m)) → Set
HeadConfined {m} bh D₁ D₂ E P =
  Σ (Frame* (sum (bh ∷ D₁) + sum D₂ + m)) λ E₀ → (E ≡ E₀ ⋯ᶠ* weakenᵣ)
    × Σ (𝐓.Proc (sum (bh ∷ D₁) + sum D₂ + m)) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ weakenᵣ

private
  head-confine-gen : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
    {bh : ℕ} {D₁ D₂ : BindGroup} {c : Const}
    {E : Frame* (sum (suc bh ∷ D₁) + sum D₂ + m)}
    {P : 𝐓.Proc (sum (suc bh ∷ D₁) + sum D₂ + m)} →
    (∀ {N} {Γ′ : Ctx N} {β : Struct N} {dir} {x : 𝔽 N} {T ϵ}
       → Γ′ ; β ⊢ K c ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ → ¬ Unr (lookup Γ′ x)) →
    Γ ; γ ⊢ₚ 𝐓.ν (suc bh ∷ D₁) D₂
              (𝐓.⟪ E [ K c ·¹ (` 0F) ]* ⟫ 𝐓.∥ P) →
    HeadConfined bh D₁ D₂ E P
  head-confine-gen {m = m} Γ-S {γ = γ} {bh = bh} {D₁ = D₁} {D₂ = D₂}
                   {E = E} {P = P} nonUnr ⊢P =
    let
      handle : 𝔽 (sum (suc bh ∷ D₁) + sum D₂ + m)
      handle = 0F
      Γ₁ , Γ₂ , s' , _p , _N , _⊢B₁ , _⊢B₂ , C , C' , ⊢body = inv-ν ⊢P
      α , β , αβ≼ , ⊢thread , ⊢Ppar = inv-∥ ⊢body
      ⊢term = inv-⟪⟫ ⊢thread
      βplug , (_ , _ , ⊢plug) , support , factor = strengthen-frame E ⊢term
      ¬u = nonUnr ⊢plug
      αfn , αarg , (_ , _ , ⊢fn) , (_ , _ , ⊢arg) , cle-plug = inv-app ⊢plug
      c-αβ≤1 = subst (count handle α + count handle β ≤_)
                     (count-handle-head bh D₁ D₂ γ)
                     (≼⇒count≤ {x = handle} ¬u αβ≼)
      1≤αarg = subst (_≤ count handle αarg) (count-self handle)
                     (inv-var-count ⊢arg handle ¬u)
      1≤βplug = ≤-trans 1≤αarg
                  (≤-trans (m≤n+m (count handle αarg) (count handle αfn))
                           (cle-plug handle ¬u))
      1≤α = ≤-trans 1≤βplug (support handle ¬u)
      α≤βplug = ≤-trans (≤-trans (m≤m+n (count handle α) (count handle β))
                                 c-αβ≤1) 1≤βplug
      cβ0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count handle β) 1≤α) c-αβ≤1))
      ρ⁻ , inv-mp , skip-mp = mk-thin 0 ((bh + sum D₁) + sum D₂ + m)
                                (headN-eq bh D₁ D₂)
      inv-h = subst (Inverter ρ⁻) (mp≡handle-head bh D₁ D₂) inv-mp
      E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
      P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
      wkeq : ∀ y → ρ⁻ y ≡ weakenᵣ y
      wkeq y = Fin.cast-is-id (headN-eq bh D₁ D₂) (weakenᵣ y)
    in E₀ , (Eeq ■ ⋯ᶠ*-cong E₀ wkeq)
     , P₀ , (Peq ■ 𝐓.⋯ₚ-cong P₀ wkeq)

discard-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {bh : ℕ} {D₁ D₂ : BindGroup}
  {E : Frame* (sum (suc bh ∷ D₁) + sum D₂ + m)}
  {P : 𝐓.Proc (sum (suc bh ∷ D₁) + sum D₂ + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (suc bh ∷ D₁) D₂
            (𝐓.⟪ E [ K `discard ·¹ (` 0F) ]* ⟫ 𝐓.∥ P) →
  HeadConfined bh D₁ D₂ E P
discard-confine Γ-S ⊢P = head-confine-gen Γ-S discard-app-nonUnr ⊢P

drop-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {bh : ℕ} {D₁ D₂ : BindGroup}
  {E : Frame* (sum (suc bh ∷ D₁) + sum D₂ + m)}
  {P : 𝐓.Proc (sum (suc bh ∷ D₁) + sum D₂ + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (suc bh ∷ D₁) D₂
            (𝐓.⟪ E [ K `drop ·¹ (` 0F) ]* ⟫ 𝐓.∥ P) →
  HeadConfined bh D₁ D₂ E P
drop-confine Γ-S ⊢P = head-confine-gen Γ-S drop-app-nonUnr ⊢P
