module BorrowedCF.Simulation.BackwardSoup.Unique where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.Base using (Const)
open import BorrowedCF.Types using (Dir; L; R; 𝟙)

import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Reduction.ExpressionsSoup as SoupRed
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction

open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (plug-app-not-value)

open Nat.Variables

private
  app-injective :
    {n : ℕ} {d : Dir}
    {e₁ e₂ e₁′ e₂′ : SoupTerm.Tm n} →
    e₁ SoupTerm.·⟨ d ⟩ e₂ ≡ e₁′ SoupTerm.·⟨ d ⟩ e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  app-injective refl = refl , refl

  pair-injective :
    {n : ℕ} {e₁ e₂ e₁′ e₂′ : SoupTerm.Tm n} →
    e₁ SoupTerm.⊗ e₂ ≡ e₁′ SoupTerm.⊗ e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  pair-injective refl = refl , refl

  seq-injective :
    {n : ℕ} {e₁ e₂ e₁′ e₂′ : SoupTerm.Tm n} →
    e₁ SoupTerm.; e₂ ≡ e₁′ SoupTerm.; e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  seq-injective refl = refl , refl

  let-injective :
    {n : ℕ} {e₁ e₁′ : SoupTerm.Tm n} {e₂ e₂′ : SoupTerm.Tm (1 + n)} →
    SoupTerm.`let e₁ `in e₂ ≡ SoupTerm.`let e₁′ `in e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  let-injective refl = refl , refl

  letpair-injective :
    {n : ℕ} {e₁ e₁′ : SoupTerm.Tm n} {e₂ e₂′ : SoupTerm.Tm (2 + n)} →
    SoupTerm.`let⊗ e₁ `in e₂ ≡ SoupTerm.`let⊗ e₁′ `in e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  letpair-injective refl = refl , refl

  inj-injective :
    {n : ℕ} {i : SoupTerm.Side} {e e′ : SoupTerm.Tm n} →
    SoupTerm.`inj i e ≡ SoupTerm.`inj i e′ →
    e ≡ e′
  inj-injective refl = refl

  case-injective :
    {n : ℕ} {e e′ : SoupTerm.Tm n}
    {l l′ r r′ : SoupTerm.Tm (1 + n)} →
    SoupTerm.`case e `of⟨ l ; r ⟩ ≡ SoupTerm.`case e′ `of⟨ l′ ; r′ ⟩ →
    (e ≡ e′) × (l ≡ l′) × (r ≡ r′)
  case-injective refl = refl , refl , refl

  cons-injective :
    {A : Set} {x y : A} {xs ys : List A} →
    L._∷_ x xs ≡ L._∷_ y ys →
    (x ≡ y) × (xs ≡ ys)
  cons-injective refl = refl , refl

  redex-not-value :
    {n : ℕ} (F : SoupRed.Frame* n) {c : Const} {v : SoupTerm.Tm n} →
    ¬ SoupRed.Value (F SoupRed.[ SoupTerm.K c SoupTerm.·¹ v ]*)
  redex-not-value F = plug-app-not-value F

redex-unique :
  {n : ℕ} {F F′ : SoupRed.Frame* n} {c c′ : Const}
  {v v′ : SoupTerm.Tm n} →
  SoupRed.Value v → SoupRed.Value v′ →
  F SoupRed.[ SoupTerm.K c SoupTerm.·¹ v ]* ≡
  F′ SoupRed.[ SoupTerm.K c′ SoupTerm.·¹ v′ ]* →
  (c ≡ c′) × (v ≡ v′) ×
  ((t : SoupTerm.Tm n) → F SoupRed.[ t ]* ≡ F′ SoupRed.[ t ]*) ×
  ((x : 𝔽 n) (k : ℕ) (t : SoupTerm.Tm n) →
    SoupReduction.insertPhi-frames x k F SoupRed.[ t ]* ≡
    SoupReduction.insertPhi-frames x k F′ SoupRed.[ t ]*)
redex-unique {F = []} {F′ = []} V V′ refl =
  refl , refl , (λ t → refl) , (λ x k t → refl)
redex-unique {F = []} {F′ = SoupRed.app₁ e L V? ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.app₁ e R V? ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.app₁ e 𝟙 V? ∷ F′} V V′ eq
  with app-injective eq
... | k≡ , _ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value k≡ SoupRed.V-K))
redex-unique {F = []} {F′ = SoupRed.app₂ e L V? ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.app₂ e R V? ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.app₂ e 𝟙 V? ∷ F′} V V′ eq
  with app-injective eq
... | _ , v≡ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value v≡ V))
redex-unique {F = []} {F′ = SoupRed.□⊗ e ∷ F′} V V′ ()
redex-unique {F = []} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.□; e ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.`let-`in e ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.`let⊗-`in e ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = []} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = []} V V′ eq
  with app-injective eq
... | k≡ , _ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym k≡) SoupRed.V-K))
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = []} V V′ eq
  with app-injective eq
... | _ , v≡ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym v≡) V′))
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = []} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = []} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = []} V V′ ()

redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ eq
  with app-injective eq
... | _ , e≡ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value e≡ (V? refl)))
redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ eq
  with app-injective eq
... | inner≡ , _ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym inner≡) (V?′ (inj₁ refl))))
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ eq
  with app-injective eq
... | inner≡ , _ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym inner≡) (V?′ (inj₂ refl))))
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ eq
  with app-injective eq
... | _ , inner≡ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym inner≡) (V?′ refl)))
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ eq
  with app-injective eq
... | e≡ , _ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value e≡ (V? (inj₁ refl))))
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ eq
  with app-injective eq
... | e≡ , _ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value e≡ (V? (inj₂ refl))))
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ ()

redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ eq
  with pair-injective eq
... | inner≡ , _ =
  ⊥-elim (redex-not-value F (subst SoupRed.Value (sym inner≡) V₀))
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.□⊗ e ∷ F′} V V′ eq
  with pair-injective eq
... | v≡ , _ =
  ⊥-elim (redex-not-value F′ (subst SoupRed.Value v≡ V₀))

redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ eq
  with app-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...     | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ L ⟩ b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ L ⟩ b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi x k) e≡)
redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e L V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ eq
  with app-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...     | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ 𝟙 ⟩ b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ 𝟙 ⟩ b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi x k) e≡)
redex-unique {F = SoupRed.app₁ e 𝟙 V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₁ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₁ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e R V? ∷ F} {F′ = SoupRed.app₁ e′ R V?′ ∷ F′} V V′ eq
  with app-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ R ⟩ b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ R ⟩ b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi x k) e≡)
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₁ e d V? ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ eq
  with app-injective eq
... | e≡ , inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ L ⟩ b) e≡ (plug≡ t))
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ L ⟩ b)
      (cong (SoupReduction.insertPhi x k) e≡) (insert≡ x k t)
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e L V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ eq
  with app-injective eq
... | e≡ , inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ 𝟙 ⟩ b) e≡ (plug≡ t))
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ 𝟙 ⟩ b)
      (cong (SoupReduction.insertPhi x k) e≡) (insert≡ x k t)
redex-unique {F = SoupRed.app₂ e 𝟙 V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₂ e′ L V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₂ e′ 𝟙 V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e R V? ∷ F} {F′ = SoupRed.app₂ e′ R V?′ ∷ F′} V V′ eq
  with app-injective eq
... | e≡ , inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.·⟨ R ⟩ b) e≡ (plug≡ t))
  , λ x k t → cong₂ (λ a b → a SoupTerm.·⟨ R ⟩ b)
      (cong (SoupReduction.insertPhi x k) e≡) (insert≡ x k t)
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.app₂ e d V? ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ eq
  with pair-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.⊗ b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → a SoupTerm.⊗ b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi x k) e≡)
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.□⊗ e ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = V₁ SoupRed.⊗□ ∷ F′} V V′ eq
  with pair-injective eq
... | v≡ , inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡′ , plug≡ , insert≡ =
  c≡ , v≡′
  , (λ t → cong₂ (λ a b → a SoupTerm.⊗ b) v≡ (plug≡ t))
  , λ x k t → cong₂ (λ a b → a SoupTerm.⊗ b)
      (cong (SoupReduction.insertPhi x k) v≡) (insert≡ x k t)
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = V₀ SoupRed.⊗□ ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ eq
  with seq-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → a SoupTerm.; b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → a SoupTerm.; b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi x k) e≡)
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.□; e ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ eq
  with let-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → SoupTerm.`let a `in b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → SoupTerm.`let a `in b)
      (insert≡ x k t) (cong (SoupReduction.insertPhi (suc x) k) e≡)
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let-`in e ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ eq
  with letpair-injective eq
... | inner≡ , e≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong₂ (λ a b → SoupTerm.`let⊗ a `in b) (plug≡ t) e≡)
  , λ x k t → cong₂ (λ a b → SoupTerm.`let⊗ a `in b)
      (insert≡ x k t)
      (cong (SoupReduction.insertPhi (suc (suc x)) k) e≡)
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.`let⊗-`in e ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ true ∷ F} {F′ = SoupRed.`inj□ true ∷ F′} V V′ eq
  with inj-injective eq
... | inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong (SoupTerm.`inj true) (plug≡ t))
  , λ x k t → cong (SoupTerm.`inj true) (insert≡ x k t)
redex-unique {F = SoupRed.`inj□ true ∷ F} {F′ = SoupRed.`inj□ false ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ false ∷ F} {F′ = SoupRed.`inj□ true ∷ F′} V V′ ()
redex-unique {F = SoupRed.`inj□ false ∷ F} {F′ = SoupRed.`inj□ false ∷ F′} V V′ eq
  with inj-injective eq
... | inner≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t → cong (SoupTerm.`inj false) (plug≡ t))
  , λ x k t → cong (SoupTerm.`inj false) (insert≡ x k t)
redex-unique {F = SoupRed.`inj□ i ∷ F} {F′ = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.app₁ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.app₂ e′ d V?′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.□⊗ e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = V₀ SoupRed.⊗□ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.□; e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.`let-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.`let⊗-`in e′ ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.`inj□ i ∷ F′} V V′ ()
redex-unique {F = SoupRed.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F} {F′ = SoupRed.`case□`of⟨ e₁′ ; e₂′ ⟩ ∷ F′} V V′ eq
  with case-injective eq
... | inner≡ , e₁≡ , e₂≡
  with redex-unique {F = F} {F′ = F′} V V′ inner≡
...   | c≡ , v≡ , plug≡ , insert≡ =
  c≡ , v≡
  , (λ t →
      cong (λ z → SoupTerm.`case z `of⟨ e₁ ; e₂ ⟩) (plug≡ t)
      ■ cong₂
          (λ a b → SoupTerm.`case (F′ SoupRed.[ t ]*) `of⟨ a ; b ⟩)
          e₁≡ e₂≡)
  , λ x k t →
      cong
        (λ z →
          SoupTerm.`case z
            `of⟨ SoupReduction.insertPhi (suc x) k e₁
               ; SoupReduction.insertPhi (suc x) k e₂ ⟩)
        (insert≡ x k t)
      ■ cong₂
          (λ a b →
            SoupTerm.`case
              (SoupReduction.insertPhi-frames x k F′ SoupRed.[ t ]*)
              `of⟨ a ; b ⟩)
          (cong (SoupReduction.insertPhi (suc x) k) e₁≡)
          (cong (SoupReduction.insertPhi (suc x) k) e₂≡)

split-around-unique :
  {A : Set} {a : A} {xs xs′ ys ys′ : List A} →
  xs ++ a ∷ ys ≡ xs′ ++ a ∷ ys′ →
  L.length xs ≡ L.length xs′ →
  xs ≡ xs′ × ys ≡ ys′
split-around-unique {xs = []} {xs′ = []} refl refl =
  refl , refl
split-around-unique {xs = []} {xs′ = x′ ∷ xs′} eq ()
split-around-unique {xs = x ∷ xs} {xs′ = []} eq ()
split-around-unique {xs = x ∷ xs} {xs′ = x′ ∷ xs′} eq len≡
  with cons-injective eq
... | x≡ , eq′
  with split-around-unique {xs = xs} {xs′ = xs′} eq′ (suc⁻¹ len≡)
...   | xs≡ , ys≡ = cong₂ L._∷_ x≡ xs≡ , ys≡
