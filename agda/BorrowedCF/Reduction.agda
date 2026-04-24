module BorrowedCF.Reduction where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)

import Data.Vec.Functional as F

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context renaming (module Substitution to 𝐂)

open Nat.Variables

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : 𝕋

data Value {n} : Tm n → Set where
  V-` : ∀ {x} → Value (` x)
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (λ[ d ] e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ,⟨ d ⟩ e₂)

infix 4 _–→_

data _–→_ {n} : Tm n → Tm n → Set where
  E-App : (V : Value e₂) → (λ[ d ] e₁) · e₂ –→ e₁ ⋯ ⦅ e₂ ⦆
  E-Seq : K `unit ; e –→ e
  E-Let : Value e₁ → `let e₁ `in e₂ –→ e₂ ⋯ ⦅ e₁ ⦆
  E-PairElim : (V₁ : Value e₁) (V₂ : Value e₂) → `let⊗ (e₁ ,⟨ d ⟩ e₂) `in e –→ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆
  E-Cx-·₁ : e₁ –→ e₂ → e₁ · e –→ e₂ · e
  E-Cx-·₂ : (V : Value e) → e₁ –→ e₂ → e · e₁ –→ e · e₂
  E-Cx-;  : e₁ –→ e₂ → e₁ ; e –→ e₂ ; e
  E-Cx-⊗₁ : e₁ –→ e₂ → e₁ ,⟨ d ⟩ e –→ e₂ ,⟨ d ⟩ e
  E-Cx-⊗₂ : (V : Value e) → e₁ –→ e₂ → e ,⟨ d ⟩ e₁ –→ e ,⟨ d ⟩ e₂
  E-Cx-let : e₁ –→ e₂ → `let e₁ `in e –→ `let e₂ `in e
  E-Cx-let⊗ : e₁ –→ e₂ → `let⊗ e₁ `in e –→ `let⊗ e₂ `in e

ChanCx : Ctx n → Set
ChanCx Γ = ∀ x → ∃ λ s → Γ x ≡ ⟨ s ⟩

module ≈ {n} = IsEquivalence (≈-isEquivalence n)

⊢unit⇒γ≼[] : Γ ; γ ⊢ K `unit ∶ unit ∣ ϵ → [] ≼ γ
⊢unit⇒γ≼[] (T-Const x) = refl refl
⊢unit⇒γ≼[] (T-Weaken ϵ≤ γ≤ x) = ≼-trans (⊢unit⇒γ≼[] x) γ≤

value⇒pure : Value e → (x : Γ ; γ ⊢ e ∶ T ∣ ϵ) → Γ ; γ ⊢ e ∶ T ∣ ℙ
value⇒pure V (T-Var x T-eq) = T-Var x T-eq
value⇒pure V (T-Const x) = T-Const x
value⇒pure V (T-Abs 𝓂→C x) = T-Abs 𝓂→C x
value⇒pure (V-⊗ V₁ V₂) (T-Pair p/s x₁ x₂ seq⇒p) = T-Pair p/s (value⇒pure V₁ x₁) (value⇒pure V₂ x₂) seq⇒pure-ℙℙ
value⇒pure V (T-Weaken ϵ≤ γ≤ x) = T-Weaken ≤ϵ-refl γ≤ (value⇒pure V x)

inv-⊢abs : Γ ; γ ⊢ λ[ d ] e ∶ arr 𝓂 d ϵ T U ∣ ℙ → ∃[ γ′ ] γ′ ≼ join d (` zero) (𝐂.wk γ) × T F.∷ Γ ; γ′ ⊢ e ∶ U ∣ ϵ
inv-⊢abs (T-Abs 𝓂→C x) = _ , refl refl , x
inv-⊢abs {d = d} (T-Weaken ℙ≤ϵ γ≤ x) =
  let _ , γ≤′ , x′ = inv-⊢abs x in
  _ , ≼-trans γ≤′ (≼-join d (refl refl) (subst₂ _≼_ (𝐂.weaken/wk _) (𝐂.weaken/wk _) (≼-⋯ {σ = 𝐂.weaken} γ≤))) , x′

inv-⊢pair : Γ ; γ ⊢ e₁ ,⟨ d ⟩ e₂ ∶ pair d T U ∣ ℙ → ∃[ γ₁ ] ∃[ γ₂ ] join d γ₁ γ₂ ≼ γ × Γ ; γ₁ ⊢ e₁ ∶ T ∣ ℙ × Γ ; γ₂ ⊢ e₂ ∶ U ∣ ℙ
inv-⊢pair (T-Pair p/s x₁ x₂ par⇒seq)
  rewrite seq⇒pure-ℙϵ⁻¹ par⇒seq
  = _ , _ , refl refl , x₁ , x₂
inv-⊢pair (T-Weaken ℙ≤ϵ γ≤ x) =
  let _ , _ , γ≤′ , x₁ , x₂ = inv-⊢pair x in
  _ , _ , ≼-trans γ≤′ γ≤ , x₁ , x₂

⊢pair-dir-uniq : Γ ; γ ⊢ e₁ ,⟨ d₁ ⟩ e₂ ∶ pair d₂ T U ∣ ϵ → d₁ ≡ d₂
⊢pair-dir-uniq (T-Pair p/s x x₁ x₂) = refl
⊢pair-dir-uniq (T-Weaken ϵ≤ γ≤ x) = ⊢pair-dir-uniq x

⊢abs-dir-uniq : Γ ; γ ⊢ λ[ d₁ ] e ∶ arr 𝓂 d₂ ϵ′ T U ∣ ϵ → d₁ ≡ d₂
⊢abs-dir-uniq (T-Abs 𝓂→C x) = refl
⊢abs-dir-uniq (T-Weaken ϵ≤ γ≤ x) = ⊢abs-dir-uniq x

progress : ChanCx Γ → Γ ; γ ⊢ e ∶ t ∣ ϵ → Value e ⊎ ∃[ e′ ] e –→ e′
progress Γ-S (T-Const c) = inj₁ V-K
progress Γ-S (T-Var x T-eq) = inj₁ V-`
progress Γ-S (T-Abs 𝓂→C e) = inj₁ V-λ
progress Γ-S (T-App e₁ e₂) with progress Γ-S e₁
... | inj₂ (_ , x₁) = inj₂ (_ , E-Cx-·₁ x₁)
... | inj₁ V₁ with progress Γ-S e₂
... | inj₂ (_ , x₂) = inj₂ (_ , E-Cx-·₂ V₁ x₂)
... | inj₁ V₂ = {!!}
progress Γ-S (T-Pair p/s e₁ e₂ seq⇒p) = {!!}
progress Γ-S (T-Let p/s e₁ e₂) = {!!}
progress Γ-S (T-LetUnit p/s e₁ e₂) = {!!}
progress Γ-S (T-LetPair p/s e₁ e₂) = {!!}
progress Γ-S (T-Weaken ϵ≤ γ≤ e) = progress Γ-S e

preservation : ChanCx Γ → Γ ; γ ⊢ e ∶ t ∣ ϵ → e –→ e′ → Γ ; γ ⊢ e′ ∶ t ∣ ϵ
preservation Γ-S (T-App {d = d} {γ₁} {γ₂} f e) (E-App V) with refl ← ⊢abs-dir-uniq f =
  let open ≼-Reasoning in
  let γ′ , γ≤ , f′ = inv-⊢abs (value⇒pure V-λ f) in
  let γ≤′ = begin
              γ′ 𝐂.⋯ 𝐂.⦅ γ₂ ⦆
            ≲⟨ ≼-⋯ γ≤ ⟩
              join d (` zero) (𝐂.wk γ₁) 𝐂.⋯ 𝐂.⦅ γ₂ ⦆
            ≡⟨ join-⋯ d _ _ ⟩
              join d γ₂ (𝐂.wk γ₁ 𝐂.⋯ 𝐂.⦅ γ₂ ⦆)
            ≡⟨ cong (join d γ₂) (γ₁ 𝐂.⋯-wk-cancels-⦅ γ₂ ⦆) ⟩
              join d γ₂ γ₁
            ∎
  in
  T-Weaken ≤ϵ-refl γ≤′ (f′ ⊢⋯ₛ ⊢⦅ value⇒pure V e ⦆ₛ)
preservation Γ-S (T-App e₁ e₂) (E-Cx-·₁ x₁) =
  T-App (preservation Γ-S e₁ x₁) e₂
preservation Γ-S (T-App e₁ e₂) (E-Cx-·₂ V₁ x₂) =
  T-App e₁ (preservation Γ-S e₂ x₂)
preservation Γ-S (T-Pair p/s e₁ e₂ par⇒seq) (E-Cx-⊗₁ x₁) =
  T-Pair p/s (preservation Γ-S e₁ x₁) e₂ par⇒seq
preservation Γ-S (T-Pair p/s e₁ e₂ par⇒seq) (E-Cx-⊗₂ V₁ x₂) =
  T-Pair p/s e₁ (preservation Γ-S e₂ x₂) par⇒seq
preservation Γ-S (T-Let p/s {γ₁} {γ₂} e₁ e₂) (E-Let V-e₁) =
  let eq = join-⋯ {σ = 𝐂.⦅ γ₁ ⦆} p/s (` zero) (𝐂.wk γ₂)
             ■ cong (join p/s γ₁) (γ₂ 𝐂.⋯-wk-cancels-⦅ γ₁ ⦆)
  in
  subst-γ eq (e₂ ⊢⋯ ⊢⦅ value⇒pure V-e₁ e₁ ⦆ₛ)
preservation Γ-S (T-Let p/s e₁ e₂) (E-Cx-let x) =
  T-Let p/s (preservation Γ-S e₁ x) e₂
preservation Γ-S (T-LetUnit p/s e₁ e₂) E-Seq =
  let γ≼ = ≼-trans (refl (≈-sym (join-[]₁ p/s)))
                   (≼-join p/s (⊢unit⇒γ≼[] e₁) (refl refl))
  in
  T-Weaken ≤ϵ-refl γ≼ e₂
preservation Γ-S (T-LetUnit p/s e₁ e₂) (E-Cx-; x) =
  T-LetUnit p/s (preservation Γ-S e₁ x) e₂
preservation Γ-S (T-LetPair {d = d} {T₂ = T₂} p/s {γ₁} {γ₂} e e′) (E-PairElim V₁ V₂) with refl ← ⊢pair-dir-uniq e =
  let open Fin.Patterns in
  let open ≼-Reasoning in
  let α , β , γ≤ , e₁ , e₂ = inv-⊢pair (value⇒pure (V-⊗ V₁ V₂) e) in
  let γ≤′ = begin
              join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ₂))
                𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆ 𝐂.⋯ 𝐂.⦅ β ⦆
            ≡⟨ cong (𝐂._⋯ 𝐂.⦅ β ⦆) (join-⋯ p/s _ _) ⟩
              join p/s (join d (` 0F) (` 1F) 𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆) (𝐂.wk (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆) 𝐂.⋯ 𝐂.⦅ β ⦆
            ≡⟨ cong₂ (λ x y → join p/s x y 𝐂.⋯ 𝐂.⦅ β ⦆)
                     (join-⋯ d _ _)
                     (𝐂.wk γ₂ 𝐂.⋯-wk-cancels-⦅ _ ⦆) ⟩
              join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F)) (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ β ⦆
            ≡⟨ join-⋯ p/s _ _ ⟩
              join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F) 𝐂.⋯ 𝐂.⦅ β ⦆) (𝐂.wk γ₂ 𝐂.⋯ 𝐂.⦅ β ⦆)
            ≡⟨ cong₂ (join p/s) (join-⋯ d _ _) (γ₂ 𝐂.⋯-wk-cancels-⦅ _ ⦆) ⟩
              join p/s (join d (α 𝐂.⋯ 𝐂.weaken 𝐂.⋯ 𝐂.⦅ β ⦆) β) γ₂
            ≡⟨ cong (λ x → join p/s (join d x β) γ₂) (α 𝐂.⋯-weaken-cancels-⦅ β ⦆) ⟩
              join p/s (join d α β) γ₂
            ≲⟨ ≼-join p/s γ≤ (refl refl) ⟩
              join p/s γ₁ γ₂
            ∎
  in
  T-Weaken ≤ϵ-refl γ≤′ (e′ ⊢⋯ₛ ⊢⦅ e₁ ⊢⋯ ⊢weakenᵣ {T = T₂} _ ⦆ₛ ⊢⋯ₛ ⊢⦅ e₂ ⦆ₛ)
preservation Γ-S (T-LetPair p/s e₁ e₂) (E-Cx-let⊗ x) =
  T-LetPair p/s (preservation Γ-S e₁ x) e₂
preservation Γ-S (T-Weaken ϵ≤ γ≤ e) x =
  T-Weaken ϵ≤ γ≤ (preservation Γ-S e x)
