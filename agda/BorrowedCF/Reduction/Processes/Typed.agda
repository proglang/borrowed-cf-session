module BorrowedCF.Reduction.Processes.Typed where

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Vec.Functional as F using ()
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)

open +-*-Solver using (solve; _:=_; _:+_; con)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Processes.Typed hiding (wkₚ)
open import BorrowedCF.Types
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns

private variable
  b b₁ b₂ q : ℕ

wkₚ : ∀ a c → a + c + n →ᵣ suc a + suc c + n
wkₚ {n} a c =
  Fin.cast (sym (+-assoc (suc a) (suc c) n))
    ∘ (weakenᵣ ↑* suc a)
    ∘ Fin.cast (cong suc (+-assoc a c n))
    ∘ weakenᵣ

ins : ∀ p {k} → p + k →ᵣ p + suc k
ins p = weakenᵣ ↑* p

private
  reassoc-l₁ : ∀ s b B C n → s + (suc b + B) + C + n ≡ s + 1 + (b + B + C + n)
  reassoc-l₁ = solve 5 (λ s b B C n →
    s :+ (con 1 :+ b :+ B) :+ C :+ n := s :+ con 1 :+ (b :+ B :+ C :+ n)) refl
  reassoc-l₂ : ∀ s b B C n → s + 1 + suc (b + B + C + n) ≡ s + (suc (suc b) + B) + C + n
  reassoc-l₂ = solve 5 (λ s b B C n →
    s :+ con 1 :+ (con 1 :+ (b :+ B :+ C :+ n)) := s :+ (con 1 :+ (con 1 :+ b) :+ B) :+ C :+ n) refl
  reassoc-r₁ : ∀ s b B C n → s + (suc b + B) + C + n ≡ s + (suc b + B + C + n)
  reassoc-r₁ = solve 5 (λ s b B C n →
    s :+ (con 1 :+ b :+ B) :+ C :+ n := s :+ (con 1 :+ b :+ B :+ C :+ n)) refl
  reassoc-r₂ : ∀ s b B C n → s + suc (suc b + B + C + n) ≡ s + (suc (suc b) + B) + C + n
  reassoc-r₂ = solve 5 (λ s b B C n →
    s :+ (con 1 :+ (con 1 :+ b :+ B :+ C :+ n)) := s :+ (con 1 :+ (con 1 :+ b) :+ B) :+ C :+ n) refl

  -- k-generalized (interior split at block-position k): sum B₁ + k plays the
  -- role of sum B₁ in the front-only versions above.
  reassoc-lk₁ : ∀ s k b B C n → s + (k + suc b + B) + C + n ≡ s + k + 1 + (b + B + C + n)
  reassoc-lk₁ = solve 6 (λ s k b B C n →
    s :+ (k :+ (con 1 :+ b) :+ B) :+ C :+ n := s :+ k :+ con 1 :+ (b :+ B :+ C :+ n)) refl
  reassoc-lk₂ : ∀ s k b B C n → s + k + 1 + suc (b + B + C + n) ≡ s + (k + suc (suc b) + B) + C + n
  reassoc-lk₂ = solve 6 (λ s k b B C n →
    s :+ k :+ con 1 :+ (con 1 :+ (b :+ B :+ C :+ n)) := s :+ (k :+ (con 1 :+ (con 1 :+ b)) :+ B) :+ C :+ n) refl
  reassoc-rk₁ : ∀ s k b B C n → s + (k + suc b + B) + C + n ≡ s + k + (suc b + B + C + n)
  reassoc-rk₁ = solve 6 (λ s k b B C n →
    s :+ (k :+ (con 1 :+ b) :+ B) :+ C :+ n := s :+ k :+ (con 1 :+ b :+ B :+ C :+ n)) refl
  reassoc-rk₂ : ∀ s k b B C n → s + k + suc (suc b + B + C + n) ≡ s + (k + suc (suc b) + B) + C + n
  reassoc-rk₂ = solve 6 (λ s k b B C n →
    s :+ k :+ (con 1 :+ (con 1 :+ b :+ B :+ C :+ n)) := s :+ (k :+ (con 1 :+ (con 1 :+ b)) :+ B) :+ C :+ n) refl
  -- rsplit at interior position k: the input block k + suc b splits into the two
  -- blocks (k + 1) ∷ suc b (a fresh sync boundary lands between them).
  reassoc-rwk₂ : ∀ s k b B C n → s + k + suc (suc b + B + C + n) ≡ s + ((k + 1) + (suc b + B)) + C + n
  reassoc-rwk₂ = solve 6 (λ s k b B C n →
    s :+ k :+ (con 1 :+ (con 1 :+ b :+ B :+ C :+ n)) := s :+ ((k :+ con 1) :+ (con 1 :+ b :+ B)) :+ C :+ n) refl

module SplitRenamings (B₁ B₂ B′ : BindGroup) where
  inj : 𝔽 (sum (B ++ B₂)) → 𝔽 (sum (B₁ ++ B ++ B₂) + sum B′ + n)
  inj {B} {n} z = Fin.cast (sym (sum-++ B₁ (B ++ B₂))) (sum B₁ ↑ʳ z) ↑ˡ sum B′ ↑ˡ n

  -- position j of a single middle block of width w, as a full-scope variable.
  atk : ∀ {w n} → 𝔽 w → 𝔽 (sum (B₁ ++ w ∷ B₂) + sum B′ + n)
  atk {w} {n} j = inj {B = w ∷ []} {n} (j ↑ˡ sum B₂)

  lwk : sum (B₁ ++ (q + suc b) ∷ B₂) + sum B′ + n →ᵣ sum (B₁ ++ (q + suc (suc b)) ∷ B₂) + sum B′ + n
  lwk {q} {b} {n} = Fin.cast eq₂ ∘ ins (sum B₁ + q + 1) {b + sum B₂ + sum B′ + n} ∘ Fin.cast eq₁
    where
      eq₁ : sum (B₁ ++ (q + suc b) ∷ B₂) + sum B′ + n ≡ sum B₁ + q + 1 + (b + sum B₂ + sum B′ + n)
      eq₁ rewrite sum-++ B₁ ((q + suc b) ∷ B₂) = reassoc-lk₁ (sum B₁) q b (sum B₂) (sum B′) n
      eq₂ : sum B₁ + q + 1 + suc (b + sum B₂ + sum B′ + n) ≡ sum (B₁ ++ (q + suc (suc b)) ∷ B₂) + sum B′ + n
      eq₂ rewrite sum-++ B₁ ((q + suc (suc b)) ∷ B₂) = reassoc-lk₂ (sum B₁) q b (sum B₂) (sum B′) n

  rwk : sum (B₁ ++ (q + suc b) ∷ B₂) + sum B′ + n →ᵣ sum (B₁ ++ (q + 1) ∷ suc b ∷ B₂) + sum B′ + n
  rwk {q} {b} {n} = Fin.cast eq₂ ∘ ins (sum B₁ + q) {suc b + sum B₂ + sum B′ + n} ∘ Fin.cast eq₁
    where
      eq₁ : sum (B₁ ++ (q + suc b) ∷ B₂) + sum B′ + n ≡ sum B₁ + q + (suc b + sum B₂ + sum B′ + n)
      eq₁ rewrite sum-++ B₁ ((q + suc b) ∷ B₂) = reassoc-rk₁ (sum B₁) q b (sum B₂) (sum B′) n
      eq₂ : sum B₁ + q + suc (suc b + sum B₂ + sum B′ + n) ≡ sum (B₁ ++ (q + 1) ∷ suc b ∷ B₂) + sum B′ + n
      eq₂ rewrite sum-++ B₁ ((q + 1) ∷ suc b ∷ B₂) = reassoc-rwk₂ (sum B₁) q b (sum B₂) (sum B′) n

infix 4 _─→ₚ_

data _─→ₚ_ {n} : Proc n → Proc n → Set where
  R-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

  R-New : (E : Frame* n) →
    ⟪ E [ K (`new s) ·¹ * ]* ⟫
      ─→ₚ
    ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      ⟪ E ⋯ᶠ* weaken* _ [ (` 1F) ⊗ (` 0F) ]* ⟫

  R-Fork : (E : Frame* n) (V : Value e) →
    ⟪ E [ K `fork ·¹ e ]* ⟫
      ─→ₚ
    ⟪ E [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫

  R-Com : ∀ {E₁ E₂} → Value e →
    let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
        ∥ ⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ n (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        ∥ (P ⋯ₚ wkρ))
      ─→ₚ
    ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ e ]* ⟫) ∥ P)

  R-Choice : ∀ {E₁ E₂ i} →
    let x = 0F in
    let y = wkʳ n (wkˡ (suc b₁ + sum B₁) 0F) in
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ [ K (`select i) ·¹ (` x) ]* ⟫
        ∥ ⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫)
        ∥ P)
      ─→ₚ
    ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ E₁ [ ` 0F ]* ⟫
        ∥ ⟪ E₂ [ `inj i (` y) ]* ⟫)
        ∥ P)

  R-LSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ B in
    ν (B₁ ++ (q + suc b₁) ∷ B₂) B (⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ ∥ (P ⋯ₚ 𝐒.lwk))

  R-RSplit : ∀ {E} →
    let module 𝐒 = SplitRenamings B₁ B₂ B in
    ν (B₁ ++ (q + suc b₁) ∷ B₂) B (⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ ∥ P)
      ─→ₚ
    ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ⊗ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)) ]* ⟫ ∥ (P ⋯ₚ 𝐒.rwk))

  R-Drop : ∀ {E} →
    ν (suc b₁ ∷ B₁) B₂
      (⟪ E ⋯ᶠ* weakenᵣ [ K `drop ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (b₁ ∷ B₁) B₂
      (⟪ E [ * ]* ⟫ ∥ P)

  R-Acq : ∀ {E} →
    ν (zero ∷ suc b₁ ∷ B₁) B₂
      (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P)
      ─→ₚ
    ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ]* ⟫ ∥ P)

  R-Close : ∀ {E₁ E₂} →
    ν L.[ 1 ] L.[ 1 ]
      ( ⟪ E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
      ∥ ⟪ E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫
      )
      ─→ₚ
    ⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ * ]* ⟫

  R-Discard : ∀ {E} →
    ν (suc b₁ ∷ B₁) B₂
      (⟪ E ⋯ᶠ* weakenᵣ [ K `discard ·¹ (` 0F) ]* ⟫ ∥ (P ⋯ₚ weakenᵣ))
      ─→ₚ
    ν (b₁ ∷ B₁) B₂
      (⟪ E [ * ]* ⟫ ∥ P)

  R-Par :
    P ─→ₚ P′ →
    P ∥ Q ─→ₚ P′ ∥ Q

  R-Bind :
    P ─→ₚ Q →
    ν B₁ B₂ P ─→ₚ ν B₁ B₂ Q

  R-Struct :
    P ≋ P′ →
    P′ ─→ₚ Q′ →
    Q′ ≋ Q →
    P ─→ₚ Q

open ≼-Reasoning

preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q
preservationₚ {Γ = Γ} {γ} Γ-S p (R-New {s = s} E)
  with e ← inv-⟪⟫ p
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , eq , ϵ≤ , ⊢E , ⊢new·* ← ⊢[]*⁻¹ E _ e
  with inv-·-unr ⊢new·* (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-new , γ-* , _ , ≤γ′ , ≤ₐ , refl , x , y
  with _ , eq₁ `→ eq₂ , []≤γ-new , `new N ← inv-K x
  with _ , _ , []≤γ-* , _ ← inv-K y
  = TP-Res N ⁇ (_ ∷ []) (_ ∷ [])
      {const ⟨ acq ; (s      ; end ⁇) ⟩}
      {const ⟨ acq ; (dual s ; end ‼) ⟩}
      (cons-acq (last (cons (λ{ (() ; _) }) ≃-skipʳ (λ{ 0F → refl }) (nil {Γ = λ()} skip))))
      (cons-acq (last (cons (λ{ (() ; _) }) ≃-skipʳ (λ{ 0F → refl }) (nil {Γ = λ()} skip))))
      (TP-Expr $ T-Conv eq ϵ≤ $ T-Weaken
        (begin  (𝒫 ⋯𝓅 𝐂.weaken* 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≡⟨ {!!} ⟩ -- mediate between Kₛ (top) and Kᵣ (bottom)
                (𝒫 ⋯𝓅 𝐂.weaken* 2) [ (` 0F) ∥ (` 1F) ]𝓅
                  ≲⟨ pullOut-≼ (𝒫 ⋯𝓅 𝐂.weaken* 2) (` 0F ∥ ` 1F) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 ⋯𝓅 𝐂.weaken* 2) [ [] ]𝓅
                  ≡⟨ cong (_ ∥_) ([-]-dist-⋯ 𝒫 [] (𝐂.weaken* 2)) ⟨
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ [] ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥
                        (≼-refl refl)
                        (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _)
                               (𝐂.wk*-preserves {m = 2} _)
                               ([-]𝓅-≼ 𝒫 (≼-trans (≼-∅ ([] ∥ [])) (≼-cong-∥ []≤γ-* []≤γ-new))))
                   ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ-* ∥ γ-new ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _) (𝐂.wk*-preserves {m = 2} _) ([-]𝓅-≼ 𝒫 ≤γ′)) ⟩
                (` 0F) ∥ (` 1F) ∥ (𝒫 [ γ′ ]𝓅 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves {m = 2} _) (𝐂.wk*-preserves {m = 2} _) ≤γ) ⟩
                (` 0F) ∥ (` 1F) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                   ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.;-unit₂ 𝐂.;-unit₂) refl ⟨
                (` 0F) ; [] ∥ ((` 1F) ; []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₂ 𝐂.∥-unit₂) refl ⟨
                (` 0F) ; [] ∥ [] ∥ ((` 1F) ; [] ∥ []) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2)
                  ≈⟨ 𝐂.∥-cong (𝐂.∥-cong 𝐂.∥-unit₁ 𝐂.∥-unit₁) refl ⟨
                [] ∥ ((` 0F) ; [] ∥ []) ∥ ([] ∥ ((` 1F) ; [] ∥ [])) ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* 2) ∎)
        ⊢⟨ ⊢E ⊢⋯ᶠ* ⊢weaken* _ Γ [ T-Conv eq₂ ≤ₐ (T-Pair par par (T-Var 0F refl) (T-Var 1F refl)) ]*⟩)
preservationₚ {γ = γ} Γ-S p (R-Fork {e = e} E V)
  with ⟪e⟫ ← inv-⟪⟫ p
  with 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , eq , ϵ≤ , ⊢E , ⊢fork·e ← ⊢[]*⁻¹ E _ ⟪e⟫
  with inv-·-unr ⊢fork·e (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-fork , γ-e , _ , ≤γ′ , ≤ₐ , refl , ⊢fork , ⊢e
  with _ , eq₁ `→ eq₂ , []≤γ-fork , `fork ← inv-K ⊢fork
  = TP-Weaken
      (begin  𝒫 [ [] ]𝓅 ∥ (γ-e ∥ [])  ≈⟨ 𝐂.∥-comm ⟩
              (γ-e ∥ []) ∥ 𝒫 [ [] ]𝓅  ≈⟨ pullOutMobile 𝒫 (inv-mob V (arr refl) (T-Conv (≃-sym eq₁) ≤ϵ-refl ⊢e) ∥ []) ⟨
              𝒫 [ γ-e ∥ [] ]𝓅         ≲⟨ [-]𝓅-≼ 𝒫 (≼-cong-∥ (≼-refl refl) []≤γ-fork) ⟩
              𝒫 [ γ-e ∥ γ-fork ]𝓅     ≲⟨ [-]𝓅-≼ 𝒫 ≤γ′ ⟩
              𝒫 [ γ′ ]𝓅               ≲⟨ ≤γ ⟩
              γ ∎)
      (TP-Par (TP-Expr (T-Conv eq ϵ≤ ⊢⟨ ⊢E [ T-Conv eq₂ ≤ₐ (T-Const `unit) ]*⟩))
              (TP-Expr (T-AppLin (refl , refl) 𝕀≤𝕀 (T-Conv (≃-sym eq₁) (𝕀-maximum _) ⊢e) (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)))))
preservationₚ Γ-S ⊢p (R-Com x) = {!!}
preservationₚ Γ-S ⊢p R-Choice = {!!}
preservationₚ Γ-S ⊢p R-LSplit = {!⊢p!}
preservationₚ Γ-S ⊢p R-RSplit = {!!}
preservationₚ Γ-S p (R-Drop {E = E})
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  with α , β , ≤γ , ⟪Edrop⟫ , q ← inv-∥ p′
  with ⊢Edrop ← inv-⟪⟫ ⟪Edrop⟫
  with 𝒫 , γ′ , _ , _ , _ , _ , 𝒫[γ′]≤ , eq , ϵ≤ , ⊢E , ⊢drop·c ← ⊢[]*⁻¹ (E ⋯ᶠ* weakenᵣ) _ ⊢Edrop
  with inv-·-unr ⊢drop·c (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
... | a , γ-drop , γ-c , _ , γ-drop∥γ-c≤ , ↔ₐ , refl , ⊢drop , ⊢c
  with _ , eq₁ `→ eq₂ , []≤γ-drop , `drop ← inv-K ⊢drop
  with eq₃ , `c≤γ-c ← inv-` ⊢c
  with refl , B₁⁺ , C₁′ ← bindCtx-drop N {!!} C₁
  = let γ″ , γ″≤ , q′ = q ⊢≗ₚ sym ∘ ⸴-cons  ⊢⋯ₚ⁻¹ ⊢weaken _ in
    TP-Res N pl B₁ B₂ C₁′ C₂ $
      TP-Par
        (TP-Expr (T-Weaken {!!} (T-Conv {!!} {!!} ⊢⟨ {!⊢E!} [ {!!} ]*⟩)))
        {!TP-Weaken ? q′ ⊢≗ ?!}
preservationₚ Γ-S ⊢p R-Acq = {!!}
preservationₚ Γ-S ⊢p R-Close = {!!}
preservationₚ Γ-S p₀ (R-Par x)
  with α , β , ≤γ , p , q ← inv-∥ p₀
  = TP-Weaken ≤γ (TP-Par (preservationₚ Γ-S p x) q)
preservationₚ Γ-S ⊢p (R-Bind x) = {!!}
preservationₚ Γ-S p (R-Exp x)
  with e ← inv-⟪⟫ p
  = TP-Expr (preservation Γ-S e x)
preservationₚ Γ-S ⊢p (R-Struct eq₁ x eq₂) = {!!}
preservationₚ Γ-S p R-Discard
  with Γ₁ , Γ₂ , _ , pl , N , B₁ , B₂ , C₁ , C₂ , p′ ← inv-ν p
  = TP-Res N pl B₁ B₂ {!C₁!} C₂ {!p′!}
