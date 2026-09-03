-- | Typed-side shape lemmas for the two administrative ν-leaves `R-Drop`
--   and `R-Discard` (`ForwardSoup/PLAN.md`, §4, Phase 3, items 5 and 6).
--
--   Both rules fire on the *head* binder of the first group,
--
--     ν (suc b₁ ∷ B₁) B₂
--       (⟪ E ⋯ᶠ* weakenᵣ [ K c ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
--
--   and the constant `c` pins the session of that binder down: `discard`
--   forces it `≃ ⟨ skip ⟩`, `drop` forces it `≃ ⟨ ret ⟩`.  Since the head
--   binder is the *first borrow* of the `BindCtx` supplied by `TP-Res`, that
--   rules out most shapes of the head bind group:
--
--     * `discard` at head group `1 ∷ c₀ ∷ B′` is untypeable — the first
--       borrow of a `cons-ret/acq` block cannot skip (`discard-b0-vacuous`);
--     * `drop` forces the head group to be `1 ∷ c₀ ∷ B′` — a `last` block
--       sits over a `New`-derived (hence `NoRet`) session, and a second
--       borrow after the `ret` would have to skip (`drop-shape`).
--
--   These are the vector-context re-establishments of the lemmas that used
--   to live in `Simulation/Forward/Discard.agda` (`fn-discard-dom`,
--   `discard-handle-≃skip`, `disc-b0-vac`) and in
--   `Simulation/Support/Theorems/Drop.agda` (`fn-drop-dom`,
--   `drop-handle-≃ret`, the two impossible branches of `U-drop`); neither of
--   those modules loads any more.  No soup imports.
module BorrowedCF.Simulation.Support.Theorems.DropShape where

open import BorrowedCF.Simulation.Support.Base

import BorrowedCF.Processes.Typed as T

open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Context.Base using (_⸴*_)
open import BorrowedCF.Simulation.Support.InvFrame using (strengthen-frame; arg-type)
open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; noRet-;-fst; ¬noRet-ret
        ; RetTip; noRet-front-cons; retTip-Sc-skips; retTip-≃
        )

open T using (BindGroup)
open T using (inv-ν; inv-∥; inv-⟪⟫)
open T using (last; cons-ret/acq; cons-acq; nil; cons)
open T using (_;_⊢ₚ_)

------------------------------------------------------------------------
-- Peeling a channel type.

private
  ⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃ ⟨ eq ⟩ = eq

------------------------------------------------------------------------
-- `discard` consumes a skipping handle.

fn-discard-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ} →
  Γ ; β ⊢ K `discard ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ →
  ⟨ skip ⟩ ≃ Tᵈ
fn-discard-dom (T-Const `discard) = ≃-refl
fn-discard-dom (T-Conv (dom≃ `→ _) _ d) = ≃-trans (fn-discard-dom d) dom≃
fn-discard-dom (T-Weaken _ d) = fn-discard-dom d

discard-handle-≃skip : ∀ {N} {Δ : Ctx N} {β : Struct N} {x : 𝔽 N} {U ϵ} →
  Δ ; β ⊢ K `discard ·¹ (` x) ∶ U ∣ ϵ →
  lookup Δ x ≃ ⟨ skip ⟩
discard-handle-≃skip (T-AppUnr _ _ ⊢fn ⊢arg) =
  ≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))
discard-handle-≃skip (T-AppLin _ _ ⊢fn ⊢arg) =
  ≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))
discard-handle-≃skip (T-Conv _ _ d) = discard-handle-≃skip d
discard-handle-≃skip (T-Weaken _ d) = discard-handle-≃skip d

------------------------------------------------------------------------
-- `drop` consumes a returning handle.

fn-drop-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ} →
  Γ ; β ⊢ K `drop ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ →
  ⟨ ret ⟩ ≃ Tᵈ
fn-drop-dom (T-Const `drop) = ≃-refl
fn-drop-dom (T-Conv (dom≃ `→ _) _ d) = ≃-trans (fn-drop-dom d) dom≃
fn-drop-dom (T-Weaken _ d) = fn-drop-dom d

drop-handle-≃ret : ∀ {N} {Δ : Ctx N} {β : Struct N} {x : 𝔽 N} {U ϵ} →
  Δ ; β ⊢ K `drop ·¹ (` x) ∶ U ∣ ϵ →
  lookup Δ x ≃ ⟨ ret ⟩
drop-handle-≃ret (T-AppUnr _ _ ⊢fn ⊢arg) =
  ≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))
drop-handle-≃ret (T-AppLin _ _ ⊢fn ⊢arg) =
  ≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))
drop-handle-≃ret (T-Conv _ _ d) = drop-handle-≃ret d
drop-handle-≃ret (T-Weaken _ d) = drop-handle-≃ret d

------------------------------------------------------------------------
-- `R-Discard` at head group `1 ∷ c₀ ∷ B′` is vacuous.
--
--   A head group with a non-empty tail is a `cons-ret/acq` block, whose
--   front `BindCtx′ (sh ; ret) Γ₁` carries `¬ Skips (sh ; ret)`.  With
--   `b₁ = 0` the front block holds exactly one borrow, so the discarded
--   handle *is* that borrow: `s₁ ≃ skip`, and the rest of the block skips —
--   whence `Skips (sh ; ret)`, a contradiction.

discard-b0-vacuous :
  ∀ {m : ℕ} {Γ : Ctx m} {γ : Struct m} {c₀ : ℕ} {B′ B₂ : BindGroup}
    {E : Frame* (sum (zero ∷ c₀ ∷ B′) + sum B₂ + m)}
    {P : T.Proc (sum (zero ∷ c₀ ∷ B′) + sum B₂ + m)} →
  Γ ; γ ⊢ₚ T.ν (suc zero ∷ c₀ ∷ B′) B₂
    (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫
     T.∥ (P T.⋯ₚ weakenᵣ)) →
  ⊥
discard-b0-vacuous {E = E} ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , _ , _ , _
    , cons-ret/acq _ _ _ (cons s₁ʰ s₂ʰ ¬sk₁ s≃₁ (nil skTail)) _ _
    , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢discardThread , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢discardThread)
... | _ , (_ , _ , ⊢plug) , _ , _ =
  ¬sk₁ (≃-skips s≃₁ (Skips._;_ headSkips skTail))
  where
  head≃skip : s₁ʰ ≃ skip
  head≃skip = ⟨⟩≃ (discard-handle-≃skip ⊢plug)

  headSkips : Skips s₁ʰ
  headSkips = ≃-skips (≃-sym head≃skip) Skips.skip

------------------------------------------------------------------------
-- `R-Drop` forces the head group to be `1 ∷ c₀ ∷ B′`.
--
--   `B₁ ≡ []` — the head group is a `last` block over `s ; end p` with
--   `New s`, hence `NoRet`; its first borrow is `NoRet` too and cannot be
--   `≃ ret`.
--
--   `b₁ ≡ suc _` with `B₁` non-empty — the front block `sh ; ret` is
--   `RetTip` (`sh` is `NoRet`), so once the first borrow is `≃ ret` the
--   remainder skips; but a second borrow demands `¬ Skips` of it.

drop-b₁-zero :
  ∀ {m : ℕ} {Γ : Ctx m} {γ : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
    {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
    {P : T.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)} →
  Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) B₂
    (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫
     T.∥ (P T.⋯ₚ weakenᵣ)) →
  b₁ ≡ 0
drop-b₁-zero {b₁ = zero} ⊢P = refl
drop-b₁-zero {b₁ = suc b} {B₁ = []} {E = E} ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , N , _ , _
    , last (cons s₁ s₂ ¬sk s≃ _) , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropThread , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropThread)
... | _ , (_ , _ , ⊢plug) , _ , _ =
  ⊥-elim
    (¬noRet-ret
      (noRet-≃ (⟨⟩≃ (drop-handle-≃ret ⊢plug))
        (noRet-;-fst (noRet-≃ (≃-sym s≃) (NoRet._;_ (new⇒noRet N) NoRet.end)))))
drop-b₁-zero {b₁ = suc b} {B₁ = c₀ ∷ B′} {E = E} ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , N , _ , _
    , cons-ret/acq sh frontSplit _
        (cons s₁ʰ s₂ʰ ¬sk₁ s≃₁ (cons _ _ ¬skTail _ _)) _ _
    , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropThread , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropThread)
... | _ , (_ , _ , ⊢plug) , _ , _ =
  ⊥-elim (¬skTail (retTip-Sc-skips retTipBorrow head≃ret))
  where
  head≃ret : s₁ʰ ≃ ret
  head≃ret = ⟨⟩≃ (drop-handle-≃ret ⊢plug)

  noRet-sh : NoRet sh
  noRet-sh =
    noRet-;-fst
      (noRet-≃ (≃-sym frontSplit) (NoRet._;_ (new⇒noRet N) NoRet.end))

  retTipBorrow : RetTip (s₁ʰ ; s₂ʰ)
  retTipBorrow = retTip-≃ (≃-sym s≃₁) (noRet-front-cons noRet-sh)

drop-B₁-cons :
  ∀ {m : ℕ} {Γ : Ctx m} {γ : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
    {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
    {P : T.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)} →
  Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) B₂
    (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫
     T.∥ (P T.⋯ₚ weakenᵣ)) →
  Σ[ c₀ ∈ ℕ ] Σ[ B′ ∈ BindGroup ] B₁ ≡ c₀ ∷ B′
drop-B₁-cons {B₁ = c₀ ∷ B′} ⊢P = c₀ , B′ , refl
drop-B₁-cons {B₁ = []} {E = E} ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , N , _ , _
    , last (cons s₁ s₂ ¬sk s≃ _) , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropThread , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropThread)
... | _ , (_ , _ , ⊢plug) , _ , _ =
  ⊥-elim
    (¬noRet-ret
      (noRet-≃ (⟨⟩≃ (drop-handle-≃ret ⊢plug))
        (noRet-;-fst (noRet-≃ (≃-sym s≃) (NoRet._;_ (new⇒noRet N) NoRet.end)))))

drop-shape :
  ∀ {m : ℕ} {Γ : Ctx m} {γ : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
    {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
    {P : T.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)} →
  Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) B₂
    (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫
     T.∥ (P T.⋯ₚ weakenᵣ)) →
  b₁ ≡ 0 × Σ[ c₀ ∈ ℕ ] Σ[ B′ ∈ BindGroup ] B₁ ≡ c₀ ∷ B′
drop-shape {E = E} {P = P} ⊢P =
  drop-b₁-zero {E = E} {P = P} ⊢P , drop-B₁-cons {E = E} {P = P} ⊢P
