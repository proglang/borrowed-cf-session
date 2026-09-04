-- | Backward simulation for the soup drop leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Drop where

open import Data.Nat.ListAction using (sum)
import Data.Vec.Relation.Unary.All as AllV
open import Data.Maybe using (just)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

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

open import BorrowedCF.Simulation.ForwardSoup.Local.Drop
  using ( DropStep; drop-step; dropThread; dropSlotEq; dropFrame; dropArgument
        ; dropArgumentValue; dropEndpoint; dropEndpointShape; dropArgumentShape
        ; dropTailFlags; dropSourceFlags; dropSelected
        ; dropConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( LocalImage; OrientedChannel; threadEmbedding
        ; physicalChannel; orientSide)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-value-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( FocusedImage; focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusTyping; focusChannels; threadInContext
        ; closedPairEnv; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using ( handle-value-var; resolve; ImpureHandleConst; HeadOfFirstGroup
        )
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head′)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using ( CanonRedex; canon-drop)
import BorrowedCF.Simulation.BackwardSoup.Canonical as Canonical
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique; split-around-unique)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (endpoint-injective)
open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (fn-drop-dom)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Types using (ret; ⟨_⟩; ≃-sym; ≤ϵ-refl)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  cons-head-tail :
    {A : Set} {q : ℕ} (xs : Vec A (suc q)) →
    V.head xs ∷ V.tail xs ≡ xs
  cons-head-tail (x ∷ xs) = refl

  threadEmbedding-subst :
    {k n m : ℕ} {P : Typed.Proc k}
    {channels channels′ :
      Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set}
    {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    (eq : channels ≡ channels′) →
    (image :
      LocalImage P channels sigma ambientChannel ambientThread C) →
    (j : 𝔽 (Translation.processCount P)) →
    threadEmbedding
      (subst
        (λ channels″ →
          LocalImage P channels″ sigma ambientChannel ambientThread C)
        eq image)
      j ≡
    threadEmbedding image j
  threadEmbedding-subst refl image j = refl

  drop-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {γ : Context.Struct N}
      {arg : Source.Tm N} {U ϵ} →
    Γ ; γ ⊢ Source.K Source.`drop Source.·¹ arg ∶ U ∣ ϵ →
    Σ[ β ∈ Context.Struct N ] Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      (Types.⟨ Types.ret ⟩ Types.≃ R) ×
      (Γ ; β ⊢ arg ∶ R ∣ ϵ′)
  drop-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    _ , _ , _ , fn-drop-dom ⊢fn , ⊢arg
  drop-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    _ , _ , _ , fn-drop-dom ⊢fn , ⊢arg
  drop-arg-decomp (Source.T-Conv _ _ d) = drop-arg-decomp d
  drop-arg-decomp (Source.T-Weaken _ d) = drop-arg-decomp d

  drop-argument-var :
    {N : ℕ} {Γ : Context.Ctx N} {γ : Context.Struct N}
    {E : SourceReduction.Frame* N} {w : Source.Tm N}
    {T : Types.𝕋} {ϵ : Types.Eff} →
    Γ ; γ ⊢ E SourceReduction.[
      Source.K Source.`drop Source.·¹ w
    ]* ∶ T ∣ ϵ →
    SourceReduction.Value w →
    Σ[ x ∈ 𝔽 N ] w ≡ Source.` x
  drop-argument-var {E = E} {w = w} ⊢plug Vw
    with SourceReduction.⊢[]*⁻¹ E
           (Source.K Source.`drop Source.·¹ w) ⊢plug
  ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢app
    with drop-arg-decomp ⊢app
  ... | β , R , ϵ′ , ret≃ , ⊢arg =
    handle-value-var
      (Source.T-Conv (Types.≃-sym ret≃) Types.≤ϵ-refl ⊢arg)
      Vw

  drop-handle-value :
    {n : ℕ} {i : 𝔽 n} {side : 𝔽 2} {k : ℕ} →
    SoupExpression.Value
      (Translation.chanTriple
        (SoupTerm.* , Soup.endpoint i side ,
         SoupTerm.`phi (Soup.endpoint i side , k)))
  drop-handle-value =
    SoupExpression.V-⊗
      (SoupExpression.V-⊗ SoupExpression.V-K SoupExpression.V-`)
      SoupExpression.V-phi

  drop-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n} {v t : SoupTerm.Tm n} →
    SoupExpression.Value v →
    t ≡ F SoupExpression.[ SoupTerm.K SoupTerm.`drop SoupTerm.·¹ v ]* →
    t ≢ SoupTerm.*
  drop-redex-not-unit {F = F} V selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  drop-handle-injective :
    {n : ℕ} {endpoint endpoint′ : 𝔽 (2 *ℕ n)} {k : ℕ} →
    Translation.chanTriple
      (SoupTerm.* , endpoint , SoupTerm.`phi (endpoint , 0)) ≡
    Translation.chanTriple
      (SoupTerm.* , endpoint′ , SoupTerm.`phi (endpoint′ , k)) →
    (endpoint ≡ endpoint′) × (0 ≡ k)
  drop-handle-injective refl = refl , refl

  redex-frame-unique :
    {n : ℕ} {F F′ : SoupExpression.Frame* n}
    {c c′ : Source.Const} {v v′ : SoupTerm.Tm n} →
    SoupExpression.Value v → SoupExpression.Value v′ →
    F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]* ≡
    F′ SoupExpression.[ SoupTerm.K c′ SoupTerm.·¹ v′ ]* →
    (t : SoupTerm.Tm n) →
    F SoupExpression.[ t ]* ≡ F′ SoupExpression.[ t ]*
  redex-frame-unique {F = F} {F′ = F′} {c = c} {c′ = c′}
    V V′ equal =
    proj₂ (proj₂
      (redex-unique {F = F} {F′ = F′} {c = c} {c′ = c′}
        V V′ equal))

  canon-redex-local :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P c src) → Typed.Proc (CanonRedex.midʳ cn)
  canon-redex-local {c = c} cn =
    Typed.ν (suc (CanonRedex.bh cn) ∷ CanonRedex.D₁ cn)
      (CanonRedex.D₂ cn)
      (Typed.⟪
        SourceReduction._[_]*
          (SourceReduction._⋯ᶠ*_ (CanonRedex.E₀ cn) Source.weakenᵣ)
          (Source.K c Source.·¹ (Source.` 0F))
       ⟫ Typed.∥
       (CanonRedex.Q₀ cn Typed.⋯ₚ Source.weakenᵣ))

  canon-redex-process :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)} →
    CanonRedex P c src → Typed.Proc 0
  canon-redex-process cn =
    plug (CanonRedex.above′ cn) (canon-redex-local cn)

  canon-redex-image :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    GlobalImage P C →
    GlobalImage (canon-redex-process cn) C
  canon-redex-image cn =
    transportGlobalImage (CanonRedex.≋-redex cn)

  canon-redex-slot :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} {j : 𝔽 m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage P C) →
    threadEmbedding (localImage image) src ≡ just j →
    threadEmbedding (localImage (canon-redex-image cn image))
      (threadInContext (CanonRedex.above′ cn)
        (canon-redex-local cn) 0F) ≡ just j
  canon-redex-slot cn image slot =
    transportGlobalSlot
      (CanonRedex.≋-redex cn) image (CanonRedex.tracks cn) slot

  canon-redex-focus :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    FocusedImage
      (CanonRedex.above′ cn) (canon-redex-local cn)
      (logicalChannels image) (λ ())
      (λ _ → ⊥) (λ _ → ⊥) C
  canon-redex-focus cn image =
    focusImage (CanonRedex.above′ cn)
      (canon-redex-local cn) (localImage image)

  canon-redex-focus-thread :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    threadEmbedding (focused-image (canon-redex-focus cn image)) 0F ≡
    threadEmbedding (localImage image)
      (threadInContext (CanonRedex.above′ cn)
        (canon-redex-local cn) 0F)
  canon-redex-focus-thread cn image =
    focusImage-thread (CanonRedex.above′ cn)
      (canon-redex-local cn) (localImage image) 0F

  canon-redex-channels :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    Vec (OrientedChannel n)
      (Translation.channelCount (canon-redex-local cn))
  canon-redex-channels cn image =
    focusChannels (CanonRedex.above′ cn)
      (canon-redex-local cn) (logicalChannels image)

  canon-redex-head-channel :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    OrientedChannel n
  canon-redex-head-channel cn image =
    V.head (canon-redex-channels cn image)

  canon-redex-body-channels :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    Vec (OrientedChannel n)
      (Translation.channelCount
        (Typed._⋯ₚ_ (CanonRedex.Q₀ cn) Source.weakenᵣ))
  canon-redex-body-channels cn image =
    V.tail (canon-redex-channels cn image)

  canon-redex-channels-split :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P c src) →
    (image : GlobalImage (canon-redex-process cn) C) →
    canon-redex-channels cn image ≡
      canon-redex-head-channel cn image ∷
      canon-redex-body-channels cn image
  canon-redex-channels-split cn image =
    sym (cons-head-tail (canon-redex-channels cn image))

  canon-redex-local-target :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P c src) → Typed.Proc (CanonRedex.midʳ cn)
  canon-redex-local-target cn =
    Typed.ν (CanonRedex.bh cn ∷ CanonRedex.D₁ cn)
      (CanonRedex.D₂ cn)
      (Typed.⟪ SourceReduction._[_]* (CanonRedex.E₀ cn) Source.* ⟫
       Typed.∥ CanonRedex.Q₀ cn)

  canon-redex-target :
    {P : Typed.Proc 0} {c : Source.Const}
    {src : 𝔽 (Translation.processCount P)} →
    CanonRedex P c src → Typed.Proc 0
  canon-redex-target cn =
    plug (CanonRedex.above′ cn) (canon-redex-local-target cn)

  canon-drop-reduction :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)} →
    (cn : CanonRedex P Source.`drop src) →
    P TypedReduction.─→ₚ canon-redex-target cn
  canon-drop-reduction cn =
    TypedReduction.R-Struct
      (CanonRedex.≋-redex cn)
      (plug-red (CanonRedex.above′ cn)
        (TypedReduction.R-Drop {E = CanonRedex.E₀ cn}))
      ≋-refl

  CanonDropStep :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`drop src) →
    GlobalImage (canon-redex-process cn) C → Set
  CanonDropStep {C = C} cn image =
    DropStep
      {b₁ = CanonRedex.bh cn}
      {B₁ = CanonRedex.D₁ cn}
      {B₂ = CanonRedex.D₂ cn}
      {E = CanonRedex.E₀ cn}
      {P = CanonRedex.Q₀ cn}
      {channel = canon-redex-head-channel cn image}
      {bodyChannels = canon-redex-body-channels cn image}
      (canon-redex-local-target cn)
      (focusEnv (CanonRedex.above′ cn)
        (canon-redex-local cn) (logicalChannels image) (λ ()))
      (focusedAmbientChannel (canon-redex-focus cn image))
      (focusedAmbientThread (canon-redex-focus cn image))
      C
      (subst
        (λ channels →
          LocalImage (canon-redex-local cn) channels
            (focusEnv (CanonRedex.above′ cn)
              (canon-redex-local cn) (logicalChannels image) (λ ()))
            (focusedAmbientChannel (canon-redex-focus cn image))
            (focusedAmbientThread (canon-redex-focus cn image))
            C)
        (canon-redex-channels-split cn image)
        (focused-image (canon-redex-focus cn image)))

  canon-drop-leaf :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} →
    (cn : CanonRedex P Source.`drop src) →
    [] ; Context.[] ⊢ₚ P →
    (image : GlobalImage (canon-redex-process cn) C) →
    CanonDropStep cn image
  canon-drop-leaf {C = C} cn ⊢P image
    with focusTyping (CanonRedex.above′ cn)
      (canon-redex-local cn) AllV.[]
      (AllV.[] / ⊢P ⊢-≋ CanonRedex.≋-redex cn)
  ... | Γᶜ , γᶜ , Γᶜ-S , ⊢local =
    drop-step
      {b₁ = CanonRedex.bh cn}
      {B₁ = CanonRedex.D₁ cn}
      {B₂ = CanonRedex.D₂ cn}
      {E = CanonRedex.E₀ cn}
      {P = CanonRedex.Q₀ cn}
      {channel = canon-redex-head-channel cn image}
      {bodyChannels = canon-redex-body-channels cn image}
      Γᶜ-S ⊢local
      (focusValueEnv (CanonRedex.above′ cn)
        (canon-redex-local cn) (logicalChannels image) (λ ()))
      (subst
        (λ channels →
          LocalImage (canon-redex-local cn) channels
            (focusEnv (CanonRedex.above′ cn)
              (canon-redex-local cn) (logicalChannels image) (λ ()))
            (focusedAmbientChannel (canon-redex-focus cn image))
            (focusedAmbientThread (canon-redex-focus cn image))
            C)
        (canon-redex-channels-split cn image)
        (focused-image (canon-redex-focus cn image)))

  canon-drop-same-slot :
    {P : Typed.Proc 0}
    {src : 𝔽 (Translation.processCount P)}
    {n m : ℕ} {C : Soup.Config n m} {j : 𝔽 m} →
    (cn : CanonRedex P Source.`drop src) →
    (image : GlobalImage P C) →
    (leaf : CanonDropStep cn (canon-redex-image cn image)) →
    threadEmbedding (localImage image) src ≡ just j →
    dropThread leaf ≡ j
  canon-drop-same-slot cn image leaf sourceSlot =
    just-injective
      (sym (dropSlotEq leaf) ■
       threadEmbedding-subst
         (canon-redex-channels-split cn canonicalImage)
         (focused-image (canon-redex-focus cn canonicalImage)) 0F ■
       canon-redex-focus-thread cn canonicalImage ■
       canon-redex-slot cn image sourceSlot)
    where
    canonicalImage = canon-redex-image cn image

------------------------------------------------------------------------
-- A strict soup drop step is the image of a source `R-Drop` at the same
-- physical thread and endpoint.

drop-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n)) (before after : List Soup.Flag) →
  SoupReduction.is-open cs i →
  SoupReduction.endpointFlags (lookup cs i) side ≡
    before ++ Soup.drop ∷ after →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`drop SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side ,
           SoupTerm.`phi (Soup.endpoint i side , L.length before))
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config
        (V.updateAt cs i
          (SoupReduction.setEndpointFlags side (before ++ Soup.acq ∷ after)))
        (SoupReduction.replaceAt ts j (F SoupExpression.[ SoupTerm.* ]*)))
drop-reflect {P = P} {n = n} {m = m} {cs = cs} {ts = ts}
  j i side F before after openEq flagsEq selected ⊢P image
  with image-thread-term image j
         (drop-redex-not-unit
           {n = 2 *ℕ n} {F = F}
           {v = Translation.chanTriple
             (SoupTerm.* , Soup.endpoint i side ,
              SoupTerm.`phi (Soup.endpoint i side , L.length before))}
           (drop-handle-value
             {n = n} {i = i} {side = side} {k = L.length before})
           selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F SoupTerm.`drop Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side ,
           SoupTerm.`phi (Soup.endpoint i side , L.length before)))
         (sym content ■ selected)
... | E , arg , refl , frameEq , argEq
  with drop-argument-var {E = E} {w = arg} ⊢source
         (T-value-inv arg
           (focusEnv ctx Typed.⟪
             SourceReduction._[_]* E
               (Source.K Source.`drop Source.·¹ arg)
           ⟫ (logicalChannels image) (λ ()))
           (focusValueEnv ctx Typed.⟪
             SourceReduction._[_]* E
               (Source.K Source.`drop Source.·¹ arg)
           ⟫ (logicalChannels image) (λ ()))
         (subst SoupExpression.Value (sym argEq)
           (drop-handle-value
             {n = n} {i = i} {side = side} {k = L.length before}))
         )
... | x , refl =
  canon-redex-target cn
  , canon-drop-reduction cn
  , closeConfigStep exactStep
  where
  bnd = resolve ctx x

  ⊢redex :
    [] ; Context.[] ⊢ₚ
      plug ctx Typed.⟪
        SourceReduction._[_]* E
          (Source.K Source.`drop Source.·¹ (Source.` x))
      ⟫
  ⊢redex =
    ⊢P

  head =
    impure-redex-head′
      {E = E} {c = Source.`drop} {x = x}
      bnd ⊢redex ImpureHandleConst.`drop

  cn =
    canon-drop E bnd (Canonical.headOfFirstGroup⇒shape bnd head) ⊢redex

  localTarget : Typed.Proc (CanonRedex.midʳ cn)
  localTarget =
    Typed.ν (CanonRedex.bh cn ∷ CanonRedex.D₁ cn)
      (CanonRedex.D₂ cn)
      (Typed.⟪ SourceReduction._[_]* (CanonRedex.E₀ cn) Source.* ⟫
       Typed.∥ CanonRedex.Q₀ cn)

  target : Typed.Proc 0
  target = plug (CanonRedex.above′ cn) localTarget

  leaf =
    canon-drop-leaf cn ⊢P (canon-redex-image cn image)

  sameSlot =
    canon-drop-same-slot cn image leaf
      (cong (threadEmbedding (localImage image)) position ■ embedded)

  redexEq :
    dropFrame leaf SoupExpression.[
      SoupTerm.K SoupTerm.`drop SoupTerm.·¹ dropArgument leaf
    ]* ≡
    F SoupExpression.[
      SoupTerm.K SoupTerm.`drop SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side ,
           SoupTerm.`phi (Soup.endpoint i side , L.length before))
    ]*
  redexEq =
    sym (dropSelected leaf) ■
    cong (lookup ts) sameSlot ■
    selected

  handleEq :
    dropArgument leaf ≡
    Translation.chanTriple
      (SoupTerm.* , Soup.endpoint i side ,
       SoupTerm.`phi (Soup.endpoint i side , L.length before))
  handleEq =
    proj₁ (proj₂ (redex-unique
      {F = dropFrame leaf} {F′ = F}
      {c = SoupTerm.`drop} {c′ = SoupTerm.`drop}
      (dropArgumentValue leaf)
      (drop-handle-value
        {n = n} {i = i} {side = side} {k = L.length before})
      redexEq))

  endpointEq :
    dropEndpoint leaf ≡ Soup.endpoint i side
  endpointEq =
    proj₁ (drop-handle-injective {n = n}
      (sym (dropArgumentShape leaf) ■ handleEq))

  physicalEndpointEq = sym (dropEndpointShape leaf) ■ endpointEq

  channelEq =
    proj₁ (endpoint-injective {n = n} physicalEndpointEq)

  endpointSideEq =
    proj₂ (endpoint-injective {n = n} physicalEndpointEq)

  prefixLengthEq : 0 ≡ L.length before
  prefixLengthEq =
    proj₂ (drop-handle-injective {n = n}
      (sym (dropArgumentShape leaf) ■ handleEq))

  canonicalFlagsEq :
    SoupReduction.endpointFlags (lookup cs i) side ≡
    [] ++ Soup.drop ∷ dropTailFlags leaf
  canonicalFlagsEq =
    subst₂
      (λ i′ side′ →
        SoupReduction.endpointFlags (lookup cs i′) side′ ≡
        [] ++ Soup.drop ∷ dropTailFlags leaf)
      (proj₁ (endpoint-injective {n = n} physicalEndpointEq))
      (proj₂ (endpoint-injective {n = n} physicalEndpointEq))
      (dropSourceFlags leaf)

  flagSplit : before ≡ [] × after ≡ dropTailFlags leaf
  flagSplit =
    split-around-unique
      (sym flagsEq ■ canonicalFlagsEq)
      (sym prefixLengthEq)

  targetFlagsEq :
    Soup.acq ∷ dropTailFlags leaf ≡ before ++ Soup.acq ∷ after
  targetFlagsEq =
    sym
      (cong₂
        (λ before′ after′ → before′ ++ Soup.acq ∷ after′)
        (proj₁ flagSplit)
        (proj₂ flagSplit))

  frameUnitEq :
    dropFrame leaf SoupExpression.[ SoupTerm.* ]* ≡
    F SoupExpression.[ SoupTerm.* ]*
  frameUnitEq =
    redex-frame-unique {n = 2 *ℕ n}
      {F = dropFrame leaf} {F′ = F}
      {c = SoupTerm.`drop} {c′ = SoupTerm.`drop}
      (dropArgumentValue leaf)
      (drop-handle-value
        {n = n} {i = i} {side = side} {k = L.length before})
      redexEq SoupTerm.*

  exactStep :
    ForwardStep.ConfigStep target (λ ()) (λ _ → ⊥) (λ _ → ⊥)
      (Soup.config cs ts)
      (Soup.config
        (V.updateAt cs i
          (SoupReduction.setEndpointFlags side
            (before ++ Soup.acq ∷ after)))
        (SoupReduction.replaceAt ts j
          (F SoupExpression.[ SoupTerm.* ]*)))
  exactStep =
    ascend
      (canon-redex-focus cn (canon-redex-image cn image))
      (dropConfigStepAt leaf
        channelEq endpointSideEq sameSlot
        (proj₁ flagSplit) (proj₂ flagSplit) frameUnitEq)
