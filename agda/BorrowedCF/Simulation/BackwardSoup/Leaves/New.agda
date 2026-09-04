-- | Backward simulation for the soup new leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.New where

import Data.Vec.Relation.Unary.All as AllV
open import Data.Maybe using (just)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.Local.New
  using (new-step; newThread; newSlotEq; newFrame; newSelectedNew
        ; newIndex; newConfigStep)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( LocalImage; OrientedChannel; OptionalThreadImage
        ; present; omitted; live-thread; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using ( T-const-inv; plug-app-not-value; plug-inversion-K
        ; pair-not-const)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusChannels; threadInContext; closedPairEnv
        ; plug)

open Typed using (_;_⊢ₚ_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  app-injective :
    {n : ℕ} {dir : Types.Dir}
    {e₁ e₂ e₁′ e₂′ : SoupTerm.Tm n} →
    e₁ SoupTerm.·⟨ dir ⟩ e₂ ≡ e₁′ SoupTerm.·⟨ dir ⟩ e₂′ →
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
    {n : ℕ} {e₁ e₁′ : SoupTerm.Tm n}
    {e₂ e₂′ : SoupTerm.Tm (1 + n)} →
    SoupTerm.`let e₁ `in e₂ ≡ SoupTerm.`let e₁′ `in e₂′ →
    (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
  let-injective refl = refl , refl

  letpair-injective :
    {n : ℕ} {e₁ e₁′ : SoupTerm.Tm n}
    {e₂ e₂′ : SoupTerm.Tm (2 + n)} →
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
    SoupTerm.`case e `of⟨ l ; r ⟩ ≡
    SoupTerm.`case e′ `of⟨ l′ ; r′ ⟩ →
    (e ≡ e′) × (l ≡ l′) × (r ≡ r′)
  case-injective refl = refl , refl , refl

  redex-not-value :
    {n : ℕ} (F : SoupExpression.Frame* n)
    {c : Source.Const} {v : SoupTerm.Tm n} →
    ¬ SoupExpression.Value
      (F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]*)
  redex-not-value F = plug-app-not-value F

  new-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n} {s : Types.𝕊 0}
    {t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K (Source.`new s) SoupTerm.·¹ SoupTerm.*
        ]* →
    t ≢ SoupTerm.*
  new-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  renamed-redex-unique :
    {n n′ : ℕ} {F F′ : SoupExpression.Frame* n}
    {c c′ : Source.Const} {v v′ : SoupTerm.Tm n} →
    SoupExpression.Value v → SoupExpression.Value v′ →
    F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]* ≡
    F′ SoupExpression.[ SoupTerm.K c′ SoupTerm.·¹ v′ ]* →
    (ρ : 𝔽 n → 𝔽 n′) (t : SoupTerm.Tm n′) →
    SoupExpression.frames-rename F ρ SoupExpression.[ t ]* ≡
    SoupExpression.frames-rename F′ ρ SoupExpression.[ t ]*
  renamed-redex-unique {F = []} {F′ = []} V V′ refl ρ t = refl
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₁ e Types.L V? ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₁ e Types.R V? ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₁ e Types.𝟙 V? ∷ F′} V V′ eq
    with app-injective eq
  ... | k≡ , _ =
    ⊥-elim (redex-not-value F′ (subst SoupExpression.Value k≡ SoupExpression.V-K))
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₂ e Types.L V? ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₂ e Types.R V? ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.app₂ e Types.𝟙 V? ∷ F′} V V′ eq
    with app-injective eq
  ... | _ , v≡ =
    ⊥-elim (redex-not-value F′ (subst SoupExpression.Value v≡ V))
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.□⊗ e ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.□; e ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.`let-`in e ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.`let⊗-`in e ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = []}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = []} V V′ eq
    with app-injective eq
  ... | k≡ , _ =
    ⊥-elim (redex-not-value F (subst SoupExpression.Value (sym k≡) SoupExpression.V-K))
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = []} V V′ eq
    with app-injective eq
  ... | _ , v≡ =
    ⊥-elim (redex-not-value F (subst SoupExpression.Value (sym v≡) V′))
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = []} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = []} V V′ ()

  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | _ , e≡ =
    ⊥-elim (redex-not-value F′ (subst SoupExpression.Value e≡ (V? refl)))
  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | inner≡ , _ =
    ⊥-elim (redex-not-value F
      (subst SoupExpression.Value (sym inner≡) (V?′ (inj₁ refl))))
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | inner≡ , _ =
    ⊥-elim (redex-not-value F
      (subst SoupExpression.Value (sym inner≡) (V?′ (inj₂ refl))))
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | _ , inner≡ =
    ⊥-elim (redex-not-value F
      (subst SoupExpression.Value (sym inner≡) (V?′ refl)))
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | e≡ , _ =
    ⊥-elim (redex-not-value F′
      (subst SoupExpression.Value e≡ (V? (inj₁ refl))))
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ eq
    with app-injective eq
  ... | e≡ , _ =
    ⊥-elim (redex-not-value F′
      (subst SoupExpression.Value e≡ (V? (inj₂ refl))))
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ eq
    with pair-injective eq
  ... | inner≡ , _ =
    ⊥-elim (redex-not-value F
      (subst SoupExpression.Value (sym inner≡) V₀))
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.□⊗ e ∷ F′} V V′ eq
    with pair-injective eq
  ... | v≡ , _ =
    ⊥-elim (redex-not-value F′
      (subst SoupExpression.Value v≡ V₀))

  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | inner≡ , e≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.L ⟩ b)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | inner≡ , e≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.𝟙 ⟩ b)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
  renamed-redex-unique {F = SoupExpression.app₁ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₁ e′ Types.R V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | inner≡ , e≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.R ⟩ b)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₁ e d V? ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | e≡ , inner≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.L ⟩ b)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.L V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | e≡ , inner≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.𝟙 ⟩ b)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = SoupExpression.app₂ e Types.𝟙 V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.L V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.𝟙 V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e Types.R V? ∷ F}
    {F′ = SoupExpression.app₂ e′ Types.R V?′ ∷ F′} V V′ eq ρ t
    with app-injective eq
  ... | e≡ , inner≡ =
    cong₂ (λ a b → a SoupTerm.·⟨ Types.R ⟩ b)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.app₂ e d V? ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ eq ρ t
    with pair-injective eq
  ... | inner≡ , e≡ =
    cong₂ SoupTerm._⊗_
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□⊗ e ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = V₁ SoupExpression.⊗□ ∷ F′} V V′ eq ρ t
    with pair-injective eq
  ... | v≡ , inner≡ =
    cong₂ SoupTerm._⊗_
      (cong (SoupTerm._⋯ᵣ ρ) v≡)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = V₀ SoupExpression.⊗□ ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ eq ρ t
    with seq-injective eq
  ... | inner≡ , e≡ =
    cong₂ SoupTerm._;_
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ ρ) e≡)
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.□; e ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ eq ρ t
    with let-injective eq
  ... | inner≡ , e≡ =
    cong₂ SoupTerm.`let_`in_
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ SoupTerm.liftRen ρ) e≡)
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let-`in e ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ eq ρ t
    with letpair-injective eq
  ... | inner≡ , e≡ =
    cong₂ SoupTerm.`let⊗_`in_
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
      (cong (SoupTerm._⋯ᵣ (SoupTerm.liftRen (SoupTerm.liftRen ρ))) e≡)
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`let⊗-`in e ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ true ∷ F}
    {F′ = SoupExpression.`inj□ true ∷ F′} V V′ eq ρ t
    with inj-injective eq
  ... | inner≡ =
    cong (SoupTerm.`inj true)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = SoupExpression.`inj□ true ∷ F}
    {F′ = SoupExpression.`inj□ false ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ false ∷ F}
    {F′ = SoupExpression.`inj□ true ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`inj□ false ∷ F}
    {F′ = SoupExpression.`inj□ false ∷ F′} V V′ eq ρ t
    with inj-injective eq
  ... | inner≡ =
    cong (SoupTerm.`inj false)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
  renamed-redex-unique {F = SoupExpression.`inj□ i ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F′} V V′ ()

  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.app₁ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.app₂ e′ d V?′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.□⊗ e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = V₀ SoupExpression.⊗□ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.□; e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.`let-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.`let⊗-`in e′ ∷ F′} V V′ ()
  renamed-redex-unique {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.`inj□ i ∷ F′} V V′ ()
  renamed-redex-unique
    {F = SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩ ∷ F}
    {F′ = SoupExpression.`case□`of⟨ e₁′ ; e₂′ ⟩ ∷ F′}
    V V′ eq ρ t
    with case-injective eq
  ... | inner≡ , e₁≡ , e₂≡ =
    cong (λ z → SoupTerm.`case z
      `of⟨ e₁ SoupTerm.⋯ᵣ SoupTerm.liftRen ρ
           ; e₂ SoupTerm.⋯ᵣ SoupTerm.liftRen ρ ⟩)
      (renamed-redex-unique {F = F} {F′ = F′} V V′ inner≡ ρ t)
    ■ cong₂
        (λ a b →
          SoupTerm.`case
            (SoupExpression.frames-rename F′ ρ SoupExpression.[ t ]*)
            `of⟨ a ; b ⟩)
        (cong (SoupTerm._⋯ᵣ SoupTerm.liftRen ρ) e₁≡)
        (cong (SoupTerm._⋯ᵣ SoupTerm.liftRen ρ) e₂≡)

  newPayload :
    {n : ℕ} → 𝔽 (suc n) → SoupTerm.Tm (2 *ℕ suc n)
  newPayload i =
    let l = Soup.leftEnd i
        r = Soup.rightEnd i
        c₀ = (SoupTerm.`phi (l , 0) SoupTerm.⊗ (SoupTerm.` l)) SoupTerm.⊗ SoupTerm.*
        c₁ = (SoupTerm.`phi (r , 0) SoupTerm.⊗ (SoupTerm.` r)) SoupTerm.⊗ SoupTerm.*
    in c₀ SoupTerm.⊗ c₁

  newResult-cong :
    {n : ℕ} {F F′ : SoupExpression.Frame* (2 *ℕ n)}
    {c c′ : Source.Const} {v v′ : SoupTerm.Tm (2 *ℕ n)} →
    SoupExpression.Value v → SoupExpression.Value v′ →
    F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]* ≡
    F′ SoupExpression.[ SoupTerm.K c′ SoupTerm.·¹ v′ ]* →
    (i : 𝔽 (suc n)) →
    SoupReduction.newResult i F ≡ SoupReduction.newResult i F′
  newResult-cong {F = F} {F′ = F′} {c = c} {c′ = c′} {v = v} {v′ = v′}
    V V′ redexEq i =
    renamed-redex-unique {F = F} {F′ = F′} {c = c} {c′ = c′}
      {v = v} {v′ = v′} V V′ redexEq
      (SoupReduction.insertEndpoint i) (newPayload i)

  new-index-eq :
    {k n m : ℕ}
    {E : SourceReduction.Frame* k} {s : Types.𝕊 0}
    {logicalChannels : Vec (OrientedChannel n) 0}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    (i : 𝔽 (suc n)) →
    (Vsigma : ValueEnv sigma) →
    (image : LocalImage
      (Typed.⟪ SourceReduction._[_]* E
                 (Source._·¹_ (Source.K (Source.`new s)) Source.*) ⟫)
      logicalChannels sigma ambientChannel ambientThread C) →
    newIndex
      (new-step {E = E} {s = s} {logicalChannels = logicalChannels}
        {sigma = sigma} {ambientChannel = ambientChannel}
        {ambientThread = ambientThread} {C = C} i Vsigma image) ≡ i
  new-index-eq {E = E} {s = s} {logicalChannels = []} {sigma = sigma}
    i Vsigma image
    with live-thread image 0F
  ... | omitted slotEq expectedEq =
    ⊥-elim
      (ForwardStep.plug-not-K (Tᶠ*[ E ] {σ = sigma} Vsigma)
        (sym (T[_]-plugᶠ* E
                {e = Source._·¹_ (Source.K (Source.`new s)) Source.*}
                Vsigma)
         ■ expectedEq))
  ... | present _ _ _ = refl

------------------------------------------------------------------------
-- The selected soup allocation is reflected by source `R-New` at the
-- located expression.  The caller's physical insertion slot is preserved.

new-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  {s : Types.𝕊 0}
  (j : 𝔽 m) (i : 𝔽 (suc n))
  (F : SoupExpression.Frame* (2 *ℕ n)) →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K (Source.`new s) SoupTerm.·¹ SoupTerm.*
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config
        (V.insertAt cs i
          (true , Soup.acq ∷ [] , Soup.acq ∷ []))
        (SoupReduction.replaceAt
          (V.map (SoupReduction.insertThreadEndpoints i) ts)
          j
          (SoupReduction.newResult i F)))
new-reflect {P = P} {cs = cs} {ts = ts} {s = s} j i F selected
  ⊢P image
  with image-thread-term image j
         (new-redex-not-unit {F = F} selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F (Source.`new s) Types.𝟙 SoupTerm.*
         (sym content ■ selected)
... | E , arg , refl , frameEq , argEq
  with T-const-inv arg
         (focusEnv ctx Typed.⟪
           SourceReduction._[_]* E
             (Source.K (Source.`new s) Source.·¹ arg)
          ⟫ (logicalChannels image) (λ ()))
         argEq
... | inj₁ refl =
  plug ctx localTarget
  , plug-red ctx (TypedReduction.R-New E)
  , closeConfigStep exactStep
  where
  sigma =
    focusEnv ctx Typed.⟪
      SourceReduction._[_]* E
        (Source.K (Source.`new s) Source.·¹ Source.*)
    ⟫ (logicalChannels image) (λ ())

  Vsigma =
    focusValueEnv ctx Typed.⟪
      SourceReduction._[_]* E
        (Source.K (Source.`new s) Source.·¹ Source.*)
    ⟫ (logicalChannels image) (λ ())

  localTarget : Typed.Proc _
  localTarget =
    Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      (Typed.⟪ SourceReduction._[_]*
        (SourceReduction._⋯ᶠ*_ E
          (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
        (Source._⊗_ (Source.` 0F) (Source.` 1F)) ⟫)

  focused = focusImage ctx Typed.⟪
      SourceReduction._[_]* E
        (Source.K (Source.`new s) Source.·¹ Source.*)
    ⟫ (localImage image)

  redexImage :
    LocalImage
      (Typed.⟪ SourceReduction._[_]* E
        (Source.K (Source.`new s) Source.·¹ Source.*) ⟫)
      (focusChannels ctx Typed.⟪
        SourceReduction._[_]* E
          (Source.K (Source.`new s) Source.·¹ Source.*)
       ⟫ (logicalChannels image))
      sigma
      (focusedAmbientChannel focused)
      (focusedAmbientThread focused)
      (Soup.config cs ts)
  redexImage = focused-image focused

  leaf =
    new-step {E = E} {s = s}
      {logicalChannels =
        focusChannels ctx Typed.⟪
          SourceReduction._[_]* E
            (Source.K (Source.`new s) Source.·¹ Source.*)
        ⟫ (logicalChannels image)}
      {sigma = sigma} {C = Soup.config cs ts}
      i Vsigma redexImage

  focusedSlot :
    threadEmbedding (focused-image focused) zero ≡
    threadEmbedding (localImage image)
      (threadInContext ctx Typed.⟪
        SourceReduction._[_]* E
          (Source.K (Source.`new s) Source.·¹ Source.*)
       ⟫ zero)
  focusedSlot =
    focusImage-thread ctx Typed.⟪
      SourceReduction._[_]* E
        (Source.K (Source.`new s) Source.·¹ Source.*)
    ⟫ (localImage image) zero

  sameSlot : newThread leaf ≡ j
  sameSlot =
    just-injective
      (sym (newSlotEq leaf) ■ focusedSlot ■
       cong (threadEmbedding (localImage image)) position ■ embedded)

  redexEq :
    newFrame leaf SoupExpression.[
      SoupTerm.K (Source.`new s) SoupTerm.·¹ SoupTerm.*
    ]* ≡
    F SoupExpression.[
      SoupTerm.K (Source.`new s) SoupTerm.·¹ SoupTerm.*
    ]*
  redexEq =
    sym (newSelectedNew leaf) ■
    cong (lookup ts) sameSlot ■
    selected

  resultEq :
    SoupReduction.newResult i (newFrame leaf) ≡
    SoupReduction.newResult i F
  resultEq =
    newResult-cong {F = newFrame leaf} {F′ = F}
      {c = Source.`new s} {c′ = Source.`new s}
      {v = SoupTerm.*} {v′ = SoupTerm.*}
      SoupExpression.V-K SoupExpression.V-K redexEq i

  sameIndex : newIndex leaf ≡ i
  sameIndex = new-index-eq i Vsigma redexImage

  indexThreadsEq :
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints (newIndex leaf)) ts)
      (newThread leaf)
      (SoupReduction.newResult (newIndex leaf) (newFrame leaf)) ≡
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints i) ts)
      (newThread leaf)
      (SoupReduction.newResult i (newFrame leaf))
  indexThreadsEq =
    cong
      (λ h →
        SoupReduction.replaceAt
          (V.map (SoupReduction.insertThreadEndpoints h) ts)
          (newThread leaf)
          (SoupReduction.newResult h (newFrame leaf)))
      sameIndex

  targetThreadsEq :
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints (newIndex leaf)) ts)
      (newThread leaf)
      (SoupReduction.newResult (newIndex leaf) (newFrame leaf)) ≡
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints i) ts)
      j
      (SoupReduction.newResult i F)
  targetThreadsEq =
    indexThreadsEq ■
    cong₂
      (SoupReduction.replaceAt
        (V.map (SoupReduction.insertThreadEndpoints i) ts))
      sameSlot resultEq

  targetChannelsEq :
    V.insertAt cs (newIndex leaf)
      (true , Soup.acq ∷ [] , Soup.acq ∷ []) ≡
    V.insertAt cs i
      (true , Soup.acq ∷ [] , Soup.acq ∷ [])
  targetChannelsEq =
    cong (λ h → V.insertAt cs h
      (true , Soup.acq ∷ [] , Soup.acq ∷ []))
      sameIndex

  targetEq :
    Soup.config
      (V.insertAt cs (newIndex leaf)
        (true , Soup.acq ∷ [] , Soup.acq ∷ []))
      (SoupReduction.replaceAt
        (V.map (SoupReduction.insertThreadEndpoints (newIndex leaf)) ts)
        (newThread leaf)
        (SoupReduction.newResult (newIndex leaf) (newFrame leaf))) ≡
    Soup.config
      (V.insertAt cs i (true , Soup.acq ∷ [] , Soup.acq ∷ []))
      (SoupReduction.replaceAt
        (V.map (SoupReduction.insertThreadEndpoints i) ts)
        j
        (SoupReduction.newResult i F))
  targetEq =
    cong₂ Soup.config targetChannelsEq targetThreadsEq

  lifted = ascend focused (newConfigStep leaf)

  exactStep =
    subst
      (λ C′ →
        ForwardStep.ConfigStep
          (plug ctx localTarget) (λ ()) (λ _ → ⊥) (λ _ → ⊥)
          (Soup.config cs ts) C′)
      targetEq lifted
... | inj₂ (x , _ , varEq) =
  ⊥-elim (pair-not-const Psigma x varEq)
  where
  Psigma =
    focusPairEnv ctx Typed.⟪ source ⟫
      (logicalChannels image) closedPairEnv
