-- Raw regression tests for the tightened synchronization rules.
--
-- The strict soup rules now insist that the distinguished endpoint handle
-- starts with `*`.  These examples pin down that change directly:
-- replacing that leading `*` by another value blocks the step, while the
-- canonical `*`-leading configuration still reduces by the intended soup
-- constructor.
module BorrowedCF.Simulation.BackwardSoup.Examples.StrictSync where

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (‼; ⁇; L; R; 𝟙)

import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.ExpressionsSoup as 𝐄
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base
open import BorrowedCF.Simulation.BackwardSoup.Inversion using (plug-app-not-value)

open Fin.Patterns

private
  openChannel : 𝐒.Channel
  openChannel = true , [] , []

  closedChannel : 𝐒.Channel
  closedChannel = false , [] , []

badLead : 𝐒Tm.Tm 2
badLead = 𝐒Tm.` 0F

payload : 𝐒Tm.Tm 2
payload = 𝐒Tm.ƛ 𝐒Tm.*

badLead-value : 𝐄.Value badLead
badLead-value = 𝐄.V-`

payload-value : 𝐄.Value payload
payload-value = 𝐄.V-λ

handle-bad₀ : 𝐒Tm.Tm 2
handle-bad₀ = 𝓒[ badLead × 0F × 𝐒Tm.* ]

handle-bad₁ : 𝐒Tm.Tm 2
handle-bad₁ = 𝓒[ badLead × 1F × 𝐒Tm.* ]

handle-good₀ : 𝐒Tm.Tm 2
handle-good₀ = 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]

handle-good₁ : 𝐒Tm.Tm 2
handle-good₁ = 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]

handle-bad₀-value : 𝐄.Value handle-bad₀
handle-bad₀-value = 𝐄.V-⊗ (𝐄.V-⊗ badLead-value 𝐄.V-`) 𝐄.V-K

handle-bad₁-value : 𝐄.Value handle-bad₁
handle-bad₁-value = 𝐄.V-⊗ (𝐄.V-⊗ badLead-value 𝐄.V-`) 𝐄.V-K

handle-good₀-value : 𝐄.Value handle-good₀
handle-good₀-value = 𝐄.V-⊗ (𝐄.V-⊗ 𝐄.V-K 𝐄.V-`) 𝐄.V-K

handle-good₁-value : 𝐄.Value handle-good₁
handle-good₁-value = 𝐄.V-⊗ (𝐄.V-⊗ 𝐄.V-K 𝐄.V-`) 𝐄.V-K

pair-send-bad : 𝐒Tm.Tm 2
pair-send-bad = payload 𝐒Tm.⊗ handle-bad₀

pair-send-good : 𝐒Tm.Tm 2
pair-send-good = payload 𝐒Tm.⊗ handle-good₀

pair-send-bad-value : 𝐄.Value pair-send-bad
pair-send-bad-value = 𝐄.V-⊗ payload-value handle-bad₀-value

pair-send-good-value : 𝐄.Value pair-send-good
pair-send-good-value = 𝐄.V-⊗ payload-value handle-good₀-value

app-injective :
  ∀ {n} {d} {e₁ e₂ e₁′ e₂′ : 𝐒Tm.Tm n} →
  e₁ 𝐒Tm.·⟨ d ⟩ e₂ ≡ e₁′ 𝐒Tm.·⟨ d ⟩ e₂′ →
  (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
app-injective refl = refl , refl

pair-injective :
  ∀ {n} {e₁ e₂ e₁′ e₂′ : 𝐒Tm.Tm n} →
  e₁ 𝐒Tm.⊗ e₂ ≡ e₁′ 𝐒Tm.⊗ e₂′ →
  (e₁ ≡ e₁′) × (e₂ ≡ e₂′)
pair-injective refl = refl , refl

badLead-not-unit : badLead ≢ 𝐒Tm.*
badLead-not-unit ()

handle-bad₀-not-canonical :
  ∀ {e₂} → handle-bad₀ ≢ 𝓒[ 𝐒Tm.* × 0F × e₂ ]
handle-bad₀-not-canonical eq
  with pair-injective eq
... | inner≡ , _ with pair-injective inner≡
...   | bad≡ , _ = badLead-not-unit bad≡

value-no-head :
  ∀ {n} {t : 𝐒Tm.Tm n} {e₂ : 𝐒Tm.Tm n} →
  𝐄.Value t →
  ¬ (t 𝐄.─→ e₂)
value-no-head 𝐄.V-` ()
value-no-head 𝐄.V-phi ()
value-no-head 𝐄.V-K ()
value-no-head 𝐄.V-λ ()
value-no-head (𝐄.V-⊗ V₁ V₂) ()
value-no-head (𝐄.V-⊕ V) ()

value-step :
  ∀ {n} {t : 𝐒Tm.Tm n} {e₂ : 𝐒Tm.Tm n} →
  𝐄.Value t →
  ¬ (t 𝐄.⋯→ e₂)
value-step V (𝐄.E-□ hred) = value-no-head V hred
value-step V (𝐄.E-Ctx (𝐄.app₁ _ _ _) red) with V
... | ()
value-step V (𝐄.E-Ctx (𝐄.app₂ _ _ _) red) with V
... | ()
value-step V (𝐄.E-Ctx (𝐄.□⊗ _) red) with V
... | 𝐄.V-⊗ V₁ V₂ = value-step V₁ red
value-step V (𝐄.E-Ctx (_ 𝐄.⊗□) red) with V
... | 𝐄.V-⊗ V₁ V₂ = value-step V₂ red
value-step V (𝐄.E-Ctx (𝐄.□; _) red) with V
... | ()
value-step V (𝐄.E-Ctx (𝐄.`let-`in _) red) with V
... | ()
value-step V (𝐄.E-Ctx (𝐄.`let⊗-`in _) red) with V
... | ()
value-step V (𝐄.E-Ctx (𝐄.`inj□ _) red) with V
... | 𝐄.V-⊕ V′ = value-step V′ red
value-step V (𝐄.E-Ctx 𝐄.`case□`of⟨ _ ; _ ⟩ red) with V
... | ()

⋯→-app :
  ∀ {n} {e₁ e₂ e′ : 𝐒Tm.Tm n} {d} →
  (e₁ 𝐒Tm.·⟨ d ⟩ e₂) 𝐄.⋯→ e′ →
    (Σ[ b ∈ 𝐒Tm.Tm (suc n) ] (e₁ ≡ 𝐒Tm.ƛ b) × 𝐄.Value e₂ × (e′ ≡ 𝐄.subst₀ e₂ b))
  ⊎ (Σ[ e₁′ ∈ 𝐒Tm.Tm n ] (e₁ 𝐄.⋯→ e₁′) × (e′ ≡ e₁′ 𝐒Tm.·⟨ d ⟩ e₂) × (d ≡ L → 𝐄.Value e₂))
  ⊎ ((d ≡ 𝟙 ⊎ d ≡ R → 𝐄.Value e₁) × Σ[ e₂′ ∈ 𝐒Tm.Tm n ] (e₂ 𝐄.⋯→ e₂′) × (e′ ≡ e₁ 𝐒Tm.·⟨ d ⟩ e₂′))
⋯→-app {e₁ = e₁} {e₂ = e₂} {e′ = e′} {d = d} step = go _ step refl
  where
  go :
    (t : 𝐒Tm.Tm _) →
    t 𝐄.⋯→ e′ →
    t ≡ e₁ 𝐒Tm.·⟨ d ⟩ e₂ →
      (Σ[ b ∈ 𝐒Tm.Tm (suc _) ] (e₁ ≡ 𝐒Tm.ƛ b) × 𝐄.Value e₂ × (e′ ≡ 𝐄.subst₀ e₂ b))
    ⊎ (Σ[ e₁′ ∈ 𝐒Tm.Tm _ ] (e₁ 𝐄.⋯→ e₁′) × (e′ ≡ e₁′ 𝐒Tm.·⟨ d ⟩ e₂) × (d ≡ L → 𝐄.Value e₂))
    ⊎ ((d ≡ 𝟙 ⊎ d ≡ R → 𝐄.Value e₁) × Σ[ e₂′ ∈ 𝐒Tm.Tm _ ] (e₂ 𝐄.⋯→ e₂′) × (e′ ≡ e₁ 𝐒Tm.·⟨ d ⟩ e₂′))
  go _ (𝐄.E-□ (𝐄.E-App V)) refl = inj₁ (_ , refl , V , refl)
  go _ (𝐄.E-Ctx (𝐄.app₁ _ _ V?) inner) refl = inj₂ (inj₁ (_ , inner , refl , V?))
  go _ (𝐄.E-Ctx (𝐄.app₂ _ _ V?) inner) refl = inj₂ (inj₂ (V? , _ , inner , refl))

const-app-value-no-step :
  ∀ {n} {c} {arg e′ : 𝐒Tm.Tm n} →
  𝐄.Value arg →
  (𝐒Tm.K c 𝐒Tm.·¹ arg) 𝐄.⋯→ e′ →
  ⊥
const-app-value-no-step Varg step with ⋯→-app step
... | inj₁ (_ , () , _ , _)
... | inj₂ (inj₁ (_ , red , _ , _)) = value-step 𝐄.V-K red
... | inj₂ (inj₂ (_ , _ , red , _)) = value-step Varg red

------------------------------------------------------------------------
-- RUS-Com

com-bad : 𝐒.Config 1 2
com-bad =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ pair-send-bad) ∷
      (𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ handle-good₁) ∷
      [])

com-good : 𝐒.Config 1 2
com-good =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ pair-send-good) ∷
      (𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ handle-good₁) ∷
      [])

com-good′ : 𝐒.Config 1 2
com-good′ =
  𝐒.config
    (openChannel ∷ [])
    (𝐒Tm.* ∷ payload ∷ [])

strict-com-canonical-step : com-good 𝐑.─→ₚ com-good′
strict-com-canonical-step =
  𝐑.RUS-Com 0F 1F 0F 0F 1F [] []
    (λ ()) 𝐑.left-right refl payload-value refl refl

-- The first sender-handle component is rigidly `badLead`, so the strict
-- `*`-headed communication premise cannot be instantiated.
strict-com-nonunit-blocks :
  ∀ (F : 𝐄.Frame* 2) {e e₁′} →
  (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹ pair-send-bad) ≢
  𝐄._[_]* F (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹
    (e 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × e₁′ ]))
strict-com-nonunit-blocks [] eq
  with app-injective eq
... | refl , arg≡ with pair-injective arg≡
...   | _ , handle≡ = handle-bad₀-not-canonical handle≡
strict-com-nonunit-blocks (𝐄.app₁ _ L _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.app₁ _ R _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.app₁ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | inner≡ , _ =
  plug-app-not-value F (subst 𝐄.Value inner≡ 𝐄.V-K)
strict-com-nonunit-blocks (𝐄.app₂ _ L _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.app₂ _ R _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.app₂ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | _ , inner≡ =
  plug-app-not-value F (subst 𝐄.Value inner≡ pair-send-bad-value)
strict-com-nonunit-blocks (𝐄.□⊗ _ ∷ F) ()
strict-com-nonunit-blocks (_ 𝐄.⊗□ ∷ F) ()
strict-com-nonunit-blocks (𝐄.□; _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.`let-`in _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.`let⊗-`in _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.`inj□ _ ∷ F) ()
strict-com-nonunit-blocks (𝐄.`case□`of⟨ _ ; _ ⟩ ∷ F) ()

------------------------------------------------------------------------
-- RUS-Choice

choice-bad : 𝐒.Config 1 2
choice-bad =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`select 𝐓Tm.L) 𝐒Tm.·¹ handle-bad₀) ∷
      (𝐒Tm.K 𝐒Tm.`branch 𝐒Tm.·¹ handle-good₁) ∷
      [])

choice-good : 𝐒.Config 1 2
choice-good =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`select 𝐓Tm.L) 𝐒Tm.·¹ handle-good₀) ∷
      (𝐒Tm.K 𝐒Tm.`branch 𝐒Tm.·¹ handle-good₁) ∷
      [])

choice-good′ : 𝐒.Config 1 2
choice-good′ =
  𝐒.config
    (openChannel ∷ [])
    (handle-good₀ ∷ 𝐒Tm.`inj 𝐓Tm.L handle-good₁ ∷ [])

strict-choice-canonical-step : choice-good 𝐑.─→ₚ choice-good′
strict-choice-canonical-step =
  𝐑.RUS-Choice 0F 1F 0F 0F 1F [] [] 𝐓Tm.L
    (λ ()) 𝐑.left-right refl refl refl

-- Likewise for selection: the strict handle shape insists on `*` in front.
strict-choice-nonunit-blocks :
  ∀ (F : 𝐄.Frame* 2) {choice e₁′} →
  (𝐒Tm.K (𝐒Tm.`select 𝐓Tm.L) 𝐒Tm.·¹ handle-bad₀) ≢
  𝐄._[_]* F (𝐒Tm.K (𝐒Tm.`select choice) 𝐒Tm.·¹
    𝓒[ 𝐒Tm.* × 0F × e₁′ ])
strict-choice-nonunit-blocks [] eq
  with app-injective eq
... | refl , handle≡ = handle-bad₀-not-canonical handle≡
strict-choice-nonunit-blocks (𝐄.app₁ _ L _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.app₁ _ R _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.app₁ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | inner≡ , _ =
  plug-app-not-value F (subst 𝐄.Value inner≡ 𝐄.V-K)
strict-choice-nonunit-blocks (𝐄.app₂ _ L _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.app₂ _ R _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.app₂ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | _ , inner≡ =
  plug-app-not-value F (subst 𝐄.Value inner≡ handle-bad₀-value)
strict-choice-nonunit-blocks (𝐄.□⊗ _ ∷ F) ()
strict-choice-nonunit-blocks (_ 𝐄.⊗□ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.□; _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.`let-`in _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.`let⊗-`in _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.`inj□ _ ∷ F) ()
strict-choice-nonunit-blocks (𝐄.`case□`of⟨ _ ; _ ⟩ ∷ F) ()

------------------------------------------------------------------------
-- RUS-Close

close-bad : 𝐒.Config 1 2
close-bad =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ handle-bad₀) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ handle-good₁) ∷
      [])

close-good : 𝐒.Config 1 2
close-good =
  𝐒.config
    (openChannel ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ handle-good₀) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ handle-good₁) ∷
      [])

close-good′ : 𝐒.Config 1 2
close-good′ =
  𝐒.config
    (closedChannel ∷ [])
    (𝐒Tm.* ∷ 𝐒Tm.* ∷ [])

strict-close-canonical-step : close-good 𝐑.─→ₚ close-good′
strict-close-canonical-step =
  𝐑.RUS-Close 0F 1F 0F 0F 1F [] []
    (λ ()) 𝐑.left-right refl refl refl

-- Close now has the same strict requirement on the distinguished handle.
strict-close-nonunit-blocks :
  ∀ (F : 𝐄.Frame* 2) →
  (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ handle-bad₀) ≢
  𝐄._[_]* F (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
    𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
strict-close-nonunit-blocks [] eq
  with app-injective eq
... | refl , handle≡ = handle-bad₀-not-canonical handle≡
strict-close-nonunit-blocks (𝐄.app₁ _ L _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.app₁ _ R _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.app₁ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | inner≡ , _ =
  plug-app-not-value F (subst 𝐄.Value inner≡ 𝐄.V-K)
strict-close-nonunit-blocks (𝐄.app₂ _ L _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.app₂ _ R _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.app₂ e 𝟙 V? ∷ F) eq
  with app-injective eq
... | _ , inner≡ =
  plug-app-not-value F (subst 𝐄.Value inner≡ handle-bad₀-value)
strict-close-nonunit-blocks (𝐄.□⊗ _ ∷ F) ()
strict-close-nonunit-blocks (_ 𝐄.⊗□ ∷ F) ()
strict-close-nonunit-blocks (𝐄.□; _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.`let-`in _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.`let⊗-`in _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.`inj□ _ ∷ F) ()
strict-close-nonunit-blocks (𝐄.`case□`of⟨ _ ; _ ⟩ ∷ F) ()
