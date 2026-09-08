-- The "erasing" structure substitution `er k`, which sends the first `k`
-- variables to the empty structure `[]` and shifts the rest down.  It is the
-- structure-level left inverse of `weaken* k`, and it is what turns the
-- linear-handle occurrence of a consumed handle into a droppable `[]`.
module BorrowedCF.Safety.Preservation.Handles.Erase where

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open Fin.Patterns

er : ∀ k {n} → (k + n) 𝐂.→ₛ n
er zero    x       = ` x
er (suc k) 0F      = []
er (suc k) (suc x) = er k x

-- `er k` undoes `weaken* k` on variables …
er-wk-var : ∀ k {n} (y : 𝔽 n) → er k (𝐂.weaken* ⦃ 𝐂.Kᵣ ⦄ k y) ≡ ` y
er-wk-var zero    y = refl
er-wk-var (suc k) y = er-wk-var k y

-- … hence on whole structures.
er-wk : ∀ k {n} (γ : Struct n) → (γ 𝐂.⋯ᵣ 𝐂.weaken* k) 𝐂.⋯ er k ≡ γ
er-wk k γ =
  𝐂.fusion γ (𝐂.weaken* k) (er k)
    ■ 𝐂.⋯-cong γ (er-wk-var k)
    ■ 𝐂.⋯-id γ (λ _ → refl)

-- `er k` is a legal structure substitution out of any context that starts
-- with `k` extra entries: the erased variables go to `[]`, which satisfies
-- every context predicate vacuously.
er-⇒ : ∀ {k n} (Δ : Ctx k) {Γ : Ctx n} → 𝐂._∶_⇒_ (er k) (Δ ⸴* Γ) Γ
er-⇒ []      x       = (λ u → ` u) , (λ m → ` m)
er-⇒ (T ⸴ Δ) 0F      = (λ _ → []) , (λ _ → [])
er-⇒ (T ⸴ Δ) (suc x) = er-⇒ Δ x

-- The crux.  A handle that a constant consumes contributes exactly one
-- variable occurrence to the structure of the application, and every other
-- part of that structure is droppable.  Erasing the handle therefore makes
-- the whole structure droppable.
app-var-[]≼ : ∀ {m n} {Γ : Ctx m} {Γ′ : Ctx n} {σ : m 𝐂.→ₛ n} {γ : Struct m}
  {c : Const} {x : 𝔽 m} {T ϵ} →
  𝐂._∶_⇒_ σ Γ Γ′ →
  σ x ≡ [] →
  Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ →
  Γ′ ∶ [] ≼ γ 𝐂.⋯ σ
app-var-[]≼ {σ = σ} {x = x} ⇒σ σx≡ (T-AppUnr _ _ ⊢f ⊢a) =
  ≼-trans (≼-refl (≈-sym 𝐂.∥-unit₁))
    (≼-cong-∥ (𝐂.≼-⋯ ⇒σ (inv-K ⊢f .proj₂ .proj₂ .proj₁))
              (≼-trans (≼-refl (≈-reflexive (sym σx≡))) (𝐂.≼-⋯ ⇒σ (inv-` ⊢a .proj₂))))
app-var-[]≼ {σ = σ} {x = x} ⇒σ σx≡ (T-AppLin _ _ ⊢f ⊢a) =
  ≼-trans (≼-refl (≈-sym 𝐂.∥-unit₁))
    (≼-cong-∥ (𝐂.≼-⋯ ⇒σ (inv-K ⊢f .proj₂ .proj₂ .proj₁))
              (≼-trans (≼-refl (≈-reflexive (sym σx≡))) (𝐂.≼-⋯ ⇒σ (inv-` ⊢a .proj₂))))
app-var-[]≼ ⇒σ σx≡ (T-Conv _ _ ⊢e) = app-var-[]≼ ⇒σ σx≡ ⊢e
app-var-[]≼ ⇒σ σx≡ (T-Weaken γ≤ ⊢e) =
  ≼-trans (app-var-[]≼ ⇒σ σx≡ ⊢e) (𝐂.≼-⋯ ⇒σ γ≤)

er-↑ʳ : ∀ k {n} (y : 𝔽 n) → er k (k ↑ʳ y) ≡ ` y
er-↑ʳ zero    y = refl
er-↑ʳ (suc k) y = er-↑ʳ k y

-- The same for the substitution kit, which is what the typed weakening
-- lemmas (`⊢weaken`, `⊢weaken*`) hand back.
er-wkₛ : ∀ k {n} (γ : Struct n) → (γ 𝐂.⋯ 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k) 𝐂.⋯ er k ≡ γ
er-wkₛ k γ =
  𝐂.fusion γ (𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k) (er k)
    ■ 𝐂.⋯-id γ (λ y → cong (𝐂._⋯ er k) (𝐂.weaken*~wkˡ ⦃ 𝐂.Kₛ ⦄ k y) ■ er-↑ʳ k y)

er-wk𝓅 : ∀ k {n} (𝒫 : CxPat n) → (𝒫 ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k) ⋯𝓅 er k ≡ 𝒫
er-wk𝓅 k [] = refl
er-wk𝓅 k ((d , γ) ∷ 𝒫) = cong₂ _∷_ (cong (d ,_) (er-wkₛ k γ)) (er-wk𝓅 k 𝒫)

-- One consumed-handle thread.  `𝒫₀` is the frame pattern pulled back through
-- the weakening, `𝒫 [ γ′ ]𝓅 ≼ α` the typing of the redex thread; the result
-- bounds the plugged-with-unit thread by the erased α.
plug-≼ : ∀ k {n} {Δ : Ctx k} {Γ : Ctx n} {𝒫 : CxPat (k + n)} {𝒫₀ : CxPat n}
  {γ′ α : Struct (k + n)} {c : Const} {x : 𝔽 (k + n)} {T ϵ} →
  ((Δ ⸴* Γ) ∶ (𝒫₀ ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k) ≼𝓅 𝒫) →
  ((Δ ⸴* Γ) ∶ 𝒫 [ γ′ ]𝓅 ≼ α) →
  er k x ≡ [] →
  (Δ ⸴* Γ) ; γ′ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ →
  Γ ∶ 𝒫₀ [ [] ]𝓅 ≼ α 𝐂.⋯ er k
plug-≼ k {Δ = Δ} {𝒫 = 𝒫} {𝒫₀ = 𝒫₀} {γ′ = γ″} ≤𝒫 ≤α erx ⊢app =
  let ⇒er = er-⇒ Δ in
  ≼-trans (≼-refl (≈-reflexive (sym (cong (_[ [] ]𝓅) (er-wk𝓅 k 𝒫₀)))))
  $ ≼-trans (≼-refl (≈-reflexive (sym ([-]-dist-⋯ (𝒫₀ ⋯𝓅 𝐂.weaken* ⦃ 𝐂.Kₛ ⦄ k) [] (er k)))))
  $ ≼-trans (𝐂.≼-⋯ ⇒er (≤𝒫 (≼-refl refl)))
  $ ≼-trans (≼-refl (≈-reflexive ([-]-dist-⋯ 𝒫 [] (er k))))
  $ ≼-trans ([-]𝓅-≼ (𝒫 ⋯𝓅 er k) (app-var-[]≼ ⇒er erx ⊢app))
  $ ≼-trans (≼-refl (≈-reflexive (sym ([-]-dist-⋯ 𝒫 γ″ (er k)))))
  $ 𝐂.≼-⋯ ⇒er ≤α
