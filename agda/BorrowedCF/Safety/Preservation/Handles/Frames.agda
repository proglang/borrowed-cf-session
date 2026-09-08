-- How the `TP-Res` body structure of `ν (suc b₁ ∷ B₁) B₂` erases, under
-- `er 1`, to the body structure of `ν (b₁ ∷ B₁) B₂`.  This is the structural
-- half of R-Drop and R-Discard: the head binder disappears from the first
-- group and its `structNSeq` contribution collapses to `[]`.
module BorrowedCF.Safety.Preservation.Handles.Frames where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Handles.Erase

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open Fin.Patterns

-- Cancelling one `suc` in a renaming against `er 1`.
er1-fuse : ∀ {m k} (X : Struct m) {ϕ : m 𝐂.→ᵣ suc k} {ψ : m 𝐂.→ᵣ k} →
  (∀ x → ϕ x ≡ suc (ψ x)) →
  (X 𝐂.⋯ᵣ ϕ) 𝐂.⋯ er 1 ≡ X 𝐂.⋯ᵣ ψ
er1-fuse X {ϕ} eq = 𝐂.fusion X ϕ (er 1) ■ 𝐂.⋯-congᶜ X (λ x → cong (er 1) (eq x))

fuse2 : ∀ {m a b} (X : Struct m) (ρ₁ : m 𝐂.→ᵣ a) (ρ₂ : a 𝐂.→ᵣ b) →
  X 𝐂.⋯ᵣ ρ₁ 𝐂.⋯ᵣ ρ₂ ≡ X 𝐂.⋯ᵣ (ρ₁ 𝐂.·ₖ ρ₂)
fuse2 X ρ₁ ρ₂ = 𝐂.fusion X ρ₁ ρ₂

fuse3 : ∀ {m a b c} (X : Struct m) (ρ₁ : m 𝐂.→ᵣ a) (ρ₂ : a 𝐂.→ᵣ b) (ρ₃ : b 𝐂.→ᵣ c) →
  X 𝐂.⋯ᵣ ρ₁ 𝐂.⋯ᵣ ρ₂ 𝐂.⋯ᵣ ρ₃ ≡ X 𝐂.⋯ᵣ ((ρ₁ 𝐂.·ₖ ρ₂) 𝐂.·ₖ ρ₃)
fuse3 X ρ₁ ρ₂ ρ₃ = cong (𝐂._⋯ᵣ ρ₃) (fuse2 X ρ₁ ρ₂) ■ fuse2 X (ρ₁ 𝐂.·ₖ ρ₂) ρ₃

fuse4 : ∀ {m a b c d} (X : Struct m) (ρ₁ : m 𝐂.→ᵣ a) (ρ₂ : a 𝐂.→ᵣ b) (ρ₃ : b 𝐂.→ᵣ c) (ρ₄ : c 𝐂.→ᵣ d) →
  X 𝐂.⋯ᵣ ρ₁ 𝐂.⋯ᵣ ρ₂ 𝐂.⋯ᵣ ρ₃ 𝐂.⋯ᵣ ρ₄ ≡ X 𝐂.⋯ᵣ (((ρ₁ 𝐂.·ₖ ρ₂) 𝐂.·ₖ ρ₃) 𝐂.·ₖ ρ₄)
fuse4 X ρ₁ ρ₂ ρ₃ ρ₄ = cong (𝐂._⋯ᵣ ρ₄) (fuse3 X ρ₁ ρ₂ ρ₃) ■ fuse2 X ((ρ₁ 𝐂.·ₖ ρ₂) 𝐂.·ₖ ρ₃) ρ₄

module _ (b₁ : ℕ) (B₁ B₂ : BindGroup) {n : ℕ} where

  -- second component of the first binder group's structure
  tail-er :
    (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ (suc b₁) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n) 𝐂.⋯ er 1
    ≡ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ b₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
  tail-er =
    cong (𝐂._⋯ er 1) (fuse3 (structBinder B₁) (𝐂.wkˡ (suc b₁)) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))
      ■ er1-fuse (structBinder B₁) (λ x → refl)
      ■ sym (fuse3 (structBinder B₁) (𝐂.wkˡ b₁) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))

  -- the `structNSeq` head of the first binder group
  nseq-er :
    (𝐂.wk (structNSeq b₁) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n) 𝐂.⋯ er 1
    ≡ (structNSeq b₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
  nseq-er =
    cong (𝐂._⋯ er 1)
      (fuse4 (structNSeq b₁) 𝐂.weakenᵣ (𝐂.wkʳ (sum B₁)) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))
      ■ er1-fuse (structNSeq b₁) (λ x → refl)
      ■ sym (fuse3 (structNSeq b₁) (𝐂.wkʳ (sum B₁)) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))

  -- the second binder group's structure
  grp₂-er :
    (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum (suc b₁ ∷ B₁)) 𝐂.⋯ᵣ 𝐂.wkʳ n) 𝐂.⋯ er 1
    ≡ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum (b₁ ∷ B₁)) 𝐂.⋯ᵣ 𝐂.wkʳ n)
  grp₂-er =
    cong (𝐂._⋯ er 1) (fuse2 (structBinder B₂) (𝐂.wkˡ (sum (suc b₁ ∷ B₁))) (𝐂.wkʳ n))
      ■ er1-fuse (structBinder B₂) (λ x → refl)
      ■ sym (fuse2 (structBinder B₂) (𝐂.wkˡ (sum (b₁ ∷ B₁))) (𝐂.wkʳ n))

  -- the ambient structure
  amb-er : (γ : Struct n) →
    (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum (suc b₁ ∷ B₁) + sum B₂)) 𝐂.⋯ er 1
    ≡ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum (b₁ ∷ B₁) + sum B₂))
  amb-er γ = er1-fuse γ (λ x → refl)
