-- | Backward simulation for the soup choice leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Choice where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.ListAction using (sum)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Vec.Relation.Unary.All as AllV
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅◅_) renaming (ε to ≋-refl)

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

open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( OrientedChannel; LocalImage; OptionalThreadImage; present; omitted
        ; threadEmbedding; channelEmbedding-injective; live-thread)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Choice
  using ( choice-step; choiceSelector; choiceBrancher
        ; choiceSelectorSlot; choiceBrancherSlot
        ; choiceSelectFrame; choiceBranchFrame; choiceLabel
        ; choiceSelectTail; choiceBranchTail
        ; choiceSelectHandleValue; choiceBranchHandleValue
        ; choiceSelectedSelect; choiceSelectedBranch; choiceConfigStepAt)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-pair-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( closedPairEnv; plug; focusEnv; focusValueEnv; focusTyping
        ; focusChannels; ≡→≋; ≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.LocatePair
  using (located-pair; image-thread-pair; focusPairExprTyping)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( plug₂; thread₁; thread₂; fill₁; fill₂; plug-fill₁; plug-fill₂
        ; Binder₂; binder₂⇒₁; binder₂⇒₂; CanonPair; canonPair; canon-pair
        ; HeadShape₂; headShapes⇒₂)
import BorrowedCF.Simulation.BackwardSoup.CanonicalPair as CanonicalPair
import BorrowedCF.Simulation.BackwardSoup.Canonical as Canonical
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (tracks-≡→≋ℕ)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using (Tracks; tracks-◅◅; tracks-≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread
        ; focusedAmbientChannel; focusedAmbientThread
        ; ascend; plug-red; closeConfigStep)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (ImpureHandleConst)
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head′)
open import BorrowedCF.Simulation.BackwardSoup.PairPosition
  using ( pairFocusEnv₁; pairFocusEnv₂
        ; pairFocusValueEnv₁; pairFocusValueEnv₂
        ; pairFocusPairEnv₁; pairFocusPairEnv₂
        ; pairThread₁-content; pairThread₂-content
        ; same-physical-channel⇒binder₂-data)
open import BorrowedCF.Simulation.Support.Frames
  using (frame-plug₁)
open import BorrowedCF.Simulation.Support.PairConfine
  using (comHandle)
open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  just-not-nothing : {A : Set} {x : A} → just x ≢ nothing
  just-not-nothing ()

  cons-head-tail :
    {A : Set} {q : ℕ} (xs : Vec A (suc q)) →
    V.head xs ∷ V.tail xs ≡ xs
  cons-head-tail (x ∷ xs) = refl

  transportLocalChannels :
    {k n m : ℕ} {P : Typed.Proc k}
    {channels channels′ :
      Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set}
    {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    channels ≡ channels′ →
    LocalImage P channels sigma ambientChannel ambientThread C →
    LocalImage P channels′ sigma ambientChannel ambientThread C
  transportLocalChannels refl image = image

  threadEmbedding-transportLocalChannels :
    {k n m : ℕ} {P : Typed.Proc k}
    {channels channels′ :
      Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set}
    {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    (equal : channels ≡ channels′) →
    (image :
      LocalImage P channels sigma ambientChannel ambientThread C) →
    (j : 𝔽 (Translation.processCount P)) →
    threadEmbedding (transportLocalChannels equal image) j ≡
    threadEmbedding image j
  threadEmbedding-transportLocalChannels refl image j = refl

  present-lookup :
    {n m : ℕ} {threads : Vec (Soup.Thread n) m}
    {slot : Maybe (𝔽 m)} {expected : Soup.Thread n} {j : 𝔽 m} →
    OptionalThreadImage {n = n} {m = m} threads slot expected →
    slot ≡ just j →
    lookup threads j ≡ expected
  present-lookup {threads = threads} {expected = expected}
    (present l slotEq content) same =
    subst (λ z → lookup threads z ≡ expected)
      (sym (just-injective (sym same ■ slotEq))) content
  present-lookup (omitted slotEq unitEq) same =
    ⊥-elim (just-not-nothing (sym same ■ slotEq))

  plug*-⋯ᵣ :
    {m n : ℕ} (E : SourceReduction.Frame* m) (t : Source.Tm m)
    (ρ : 𝔽 m → 𝔽 n) →
    Source._⋯_ (SourceReduction._[_]* E t) ρ ≡
    SourceReduction._[_]* (SourceReduction._⋯ᶠ*_ E ρ) (Source._⋯_ t ρ)
  plug*-⋯ᵣ [] t ρ = refl
  plug*-⋯ᵣ (F ∷ Es) t ρ =
    frame-plug₁ F ρ (λ _ → SourceReduction.V-`)
    ■ cong (SourceReduction._[_] (SourceReduction._⋯ᶠ_ F ρ))
        (plug*-⋯ᵣ Es t ρ)

  choice-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {c : Source.Const} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[ SoupTerm.K c SoupTerm.·¹ v ]* →
    t ≢ SoupTerm.*
  choice-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq)) SoupExpression.V-K)

  pair-not-channel :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {a b : Source.Tm k} {R ϵ s} →
    Γ ; γ ⊢ a Source.⊗ b ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    ⊥
  pair-not-channel typed eq
    with Source.inv-⊗ typed
  ... | _ , _ , _ , _ , _ , _ , _ , _ , pairEq , _ =
    mismatch (Types.≃-trans eq (Types.≃-sym pairEq))
    where
    mismatch : ∀ {s T U d} → ¬ (Types.⟨ s ⟩ Types.≃ (T Types.⊗⟨ d ⟩ U))
    mismatch ()

  select-fn-dom :
    ∀ {N} {Γ : Context.Ctx N} {α : Context.Struct N}
      {T U a ϵ} {choice} →
    Γ ; α ⊢ Source.K (Source.`select choice) ∶
      T Types.⟨ a ⟩→ U ∣ ϵ →
    Σ[ s₁ ∈ Types.𝕊 0 ] Σ[ s₂ ∈ Types.𝕊 0 ]
      (Types.⟨ Types.brn Types.‼ s₁ s₂ ⟩ Types.≃ T)
  select-fn-dom (Source.T-Const Source.`select) = _ , _ , Types.≃-refl
  select-fn-dom (Source.T-Conv (dom≃ Types.`→ _) _ d) =
    let s₁ , s₂ , eq = select-fn-dom d in
    s₁ , s₂ , Types.≃-trans eq dom≃
  select-fn-dom (Source.T-Weaken _ d) = select-fn-dom d

  select-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {γ : Context.Struct N}
      {arg : Source.Tm N} {U ϵ} {choice} →
    Γ ; γ ⊢ Source.K (Source.`select choice) Source.·¹ arg ∶ U ∣ ϵ →
    Σ[ s₁ ∈ Types.𝕊 0 ] Σ[ s₂ ∈ Types.𝕊 0 ]
    Σ[ β ∈ Context.Struct N ] Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      (Types.⟨ Types.brn Types.‼ s₁ s₂ ⟩ Types.≃ R) ×
      (Γ ; β ⊢ arg ∶ R ∣ ϵ′)
  select-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    let s₁ , s₂ , eq = select-fn-dom ⊢fn in
    s₁ , s₂ , _ , _ , _ , eq , ⊢arg
  select-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    let s₁ , s₂ , eq = select-fn-dom ⊢fn in
    s₁ , s₂ , _ , _ , _ , eq , ⊢arg
  select-arg-decomp (Source.T-Conv _ _ d) = select-arg-decomp d
  select-arg-decomp (Source.T-Weaken _ d) = select-arg-decomp d

  branch-fn-dom :
    ∀ {N} {Γ : Context.Ctx N} {α : Context.Struct N}
      {T U a ϵ} →
    Γ ; α ⊢ Source.K Source.`branch ∶ T Types.⟨ a ⟩→ U ∣ ϵ →
    Σ[ s₁ ∈ Types.𝕊 0 ] Σ[ s₂ ∈ Types.𝕊 0 ]
      (Types.⟨ Types.brn Types.⁇ s₁ s₂ ⟩ Types.≃ T)
  branch-fn-dom (Source.T-Const Source.`branch) = _ , _ , Types.≃-refl
  branch-fn-dom (Source.T-Conv (dom≃ Types.`→ _) _ d) =
    let s₁ , s₂ , eq = branch-fn-dom d in
    s₁ , s₂ , Types.≃-trans eq dom≃
  branch-fn-dom (Source.T-Weaken _ d) = branch-fn-dom d

  branch-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {γ : Context.Struct N}
      {arg : Source.Tm N} {U ϵ} →
    Γ ; γ ⊢ Source.K Source.`branch Source.·¹ arg ∶ U ∣ ϵ →
    Σ[ s₁ ∈ Types.𝕊 0 ] Σ[ s₂ ∈ Types.𝕊 0 ]
    Σ[ β ∈ Context.Struct N ] Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      (Types.⟨ Types.brn Types.⁇ s₁ s₂ ⟩ Types.≃ R) ×
      (Γ ; β ⊢ arg ∶ R ∣ ϵ′)
  branch-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    let s₁ , s₂ , eq = branch-fn-dom ⊢fn in
    s₁ , s₂ , _ , _ , _ , eq , ⊢arg
  branch-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    let s₁ , s₂ , eq = branch-fn-dom ⊢fn in
    s₁ , s₂ , _ , _ , _ , eq , ⊢arg
  branch-arg-decomp (Source.T-Conv _ _ d) = branch-arg-decomp d
  branch-arg-decomp (Source.T-Weaken _ d) = branch-arg-decomp d

  argument-var :
    ∀ {k n} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {sigma : Translation.Env k n}
      {arg : Source.Tm k} {s : Types.𝕊 0}
      {R : Types.𝕋} {ϵ : Types.Eff}
      {e₁ e₂ : SoupTerm.Tm n} {x : 𝔽 n} →
    Γ ; γ ⊢ arg ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    Translation.T[ arg ] sigma ≡ Translation.chanTriple (e₁ , x , e₂) →
    Σ[ y ∈ 𝔽 k ] arg ≡ Source.` y
  argument-var ⊢arg ch argEq
    with T-pair-inv _ _ argEq
  ... | inj₂ (y , varEq , _) = y , varEq
  ... | inj₁ (a , b , pairEq , _ , _) =
    ⊥-elim
      (pair-not-channel
        (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) pairEq ⊢arg) ch)

  opposite-apart :
    ∀ {side₁ side₂} → SoupReduction.Opposite side₁ side₂ → side₁ ≢ side₂
  opposite-apart SoupReduction.left-right ()
  opposite-apart SoupReduction.right-left ()

  select-injective :
    ∀ {left right} → Source.`select left ≡ Source.`select right → left ≡ right
  select-injective refl = refl

------------------------------------------------------------------------
-- A strict soup choice reflects to a typed choice.

choice-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)) (choice : Source.Side)
  {e₁′ e₂′ : Soup.Thread n} →
  j ≢ k →
  SoupReduction.Opposite side₁ side₂ →
  SoupReduction.is-open cs i →
  lookup ts j ≡
    F₁ SoupExpression.[
      SoupTerm.K (SoupTerm.`select choice) SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₁ , e₁′) ]* →
  lookup ts k ≡
    F₂ SoupExpression.[
      SoupTerm.K SoupTerm.`branch SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₂ , e₂′) ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs
        (SoupReduction.replaceTwo ts
          j (F₁ SoupExpression.[
            Translation.chanTriple
              (SoupTerm.* , Soup.endpoint i side₁ , e₁′) ]*)
          k (F₂ SoupExpression.[
            SoupTerm.`inj choice
              (Translation.chanTriple
                (SoupTerm.* , Soup.endpoint i side₂ , e₂′)) ]*)))
choice-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j k i side₁ side₂ F₁ F₂ choice {e₁′ = e₁′} {e₂′ = e₂′}
  slotsApart opposite openChannel
  selected₁ selected₂ ⊢P image
  with image-thread-pair image j k slotsApart
         (choice-redex-not-unit {F = F₁} selected₁)
         (choice-redex-not-unit {F = F₂} selected₂)
... | sourceThread₁ , sourceThread₂
    , (embedded₁ , content₁) , (embedded₂ , content₂)
    , located-pair ctx source₁ source₂
  with focusPairExprTyping ctx source₁ source₂ AllV.[] ⊢P
... | (Γ₁ , γ₁ , Γ₁-S , ⊢source₁)
    , (Γ₂ , γ₂ , Γ₂-S , ⊢source₂)
  with plug-inversion-K source₁
         (pairFocusEnv₁ ctx source₁ source₂ (logicalChannels image) (λ ()))
         (pairFocusValueEnv₁ ctx source₁ source₂
           (logicalChannels image) (λ ()))
         (pairFocusPairEnv₁ ctx source₁ source₂
           (logicalChannels image) closedPairEnv)
         F₁ (Source.`select choice) Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side₁ , e₁′))
         (sym (pairThread₁-content ctx source₁ source₂
                 (logicalChannels image) (λ ()))
          ■ sym content₁ ■ selected₁)
... | E₁ , arg₁ , sourceEq₁ , frameEq₁ , argEq₁
  with plug-inversion-K source₂
         (pairFocusEnv₂ ctx source₁ source₂ (logicalChannels image) (λ ()))
         (pairFocusValueEnv₂ ctx source₁ source₂
           (logicalChannels image) (λ ()))
         (pairFocusPairEnv₂ ctx source₁ source₂
           (logicalChannels image) closedPairEnv)
         F₂ Source.`branch Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side₂ , e₂′))
         (sym (pairThread₂-content ctx source₁ source₂
                 (logicalChannels image) (λ ()))
          ■ sym content₂ ■ selected₂)
... | E₂ , arg₂ , sourceEq₂ , frameEq₂ , argEq₂
  with SourceReduction.⊢[]*⁻¹ E₁
         (Source.K (Source.`select choice) Source.·¹ arg₁)
         (subst (λ z → Γ₁ ; γ₁ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₁ ⊢source₁)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₁ , ⊢app₁
  with select-arg-decomp ⊢app₁
... | s₁₁ , s₁₂ , β₁ , R₁ , ϵ₁ , argType₁ , ⊢arg₁
  with argument-var ⊢arg₁ argType₁ argEq₁
... | x₁ , refl
  with SourceReduction.⊢[]*⁻¹ E₂
         (Source.K Source.`branch Source.·¹ arg₂)
         (subst (λ z → Γ₂ ; γ₂ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₂ ⊢source₂)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₂ , ⊢app₂
  with branch-arg-decomp ⊢app₂
... | s₂₁ , s₂₂ , β₂ , R₂ , ϵ₂ , argType₂ , ⊢arg₂
  with argument-var ⊢arg₂ argType₂ argEq₂
... | x₂ , refl
  with same-physical-channel⇒binder₂-data
         ctx source₁ source₂ (logicalChannels image)
         (channelEmbedding-injective (localImage image)) x₁ x₂
         (opposite-apart opposite) argEq₁ argEq₂
... | bnd , localsApart , logical , physicalEq , binderContent = finish
  where
  redex₁ : Source.Tm _
  redex₁ =
    E₁ SourceReduction.[
      Source.K (Source.`select choice) Source.·¹ (Source.` x₁) ]*

  redex₂ : Source.Tm _
  redex₂ =
    E₂ SourceReduction.[
      Source.K Source.`branch Source.·¹ (Source.` x₂) ]*

  redexProc : Typed.Proc 0
  redexProc = plug₂ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫

  redexProcEq : P ≡ redexProc
  redexProcEq =
    cong₂ (λ z₁ z₂ → plug₂ ctx Typed.⟪ z₁ ⟫ Typed.⟪ z₂ ⟫)
      sourceEq₁ sourceEq₂

  ⊢redex : [] ; Context.[] ⊢ₚ redexProc
  ⊢redex = subst ([] ; Context.[] ⊢ₚ_) redexProcEq ⊢P

  bnd₁ = binder₂⇒₁ bnd Typed.⟪ redex₂ ⟫
  bnd₂ = binder₂⇒₂ bnd Typed.⟪ redex₁ ⟫

  ⊢redex₁ :
    [] ; Context.[] ⊢ₚ
      plug (fill₂ ctx Typed.⟪ redex₂ ⟫) Typed.⟪ redex₁ ⟫
  ⊢redex₁ =
    subst ([] ; Context.[] ⊢ₚ_)
      (sym (plug-fill₂ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫)) ⊢redex

  ⊢redex₂ :
    [] ; Context.[] ⊢ₚ
      plug (fill₁ ctx Typed.⟪ redex₁ ⟫) Typed.⟪ redex₂ ⟫
  ⊢redex₂ =
    subst ([] ; Context.[] ⊢ₚ_)
      (sym (plug-fill₁ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫)) ⊢redex

  head₁ =
    impure-redex-head′
      {E = E₁} {c = Source.`select choice} {x = x₁}
      bnd₁ ⊢redex₁ ImpureHandleConst.`select

  head₂ =
    impure-redex-head′
      {E = E₂} {c = Source.`branch} {x = x₂}
      bnd₂ ⊢redex₂ ImpureHandleConst.`branch

  shape₁ = Canonical.headOfFirstGroup⇒shape bnd₁ head₁
  shape₂ = Canonical.headOfFirstGroup⇒shape bnd₂ head₂

  headShape :
    HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
      (Binder₂.local₁ bnd) (Binder₂.local₂ bnd)
  headShape = headShapes⇒₂ shape₁ shape₂ localsApart

  canon :
    CanonPair redexProc redex₁ redex₂ x₁ x₂
      (thread₁ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫ 0F)
      (thread₂ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫ 0F)
  canon = canon-pair redex₁ redex₂ bnd headShape

  finish :
    Σ[ P′ ∈ Typed.Proc 0 ]
      (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
        TypedReduction.─→ₚ P′) ×
      GlobalImage P′
        (Soup.config cs
          (SoupReduction.replaceTwo ts
            j (F₁ SoupExpression.[
              Translation.chanTriple
                (SoupTerm.* , Soup.endpoint i side₁ , e₁′) ]*)
            k (F₂ SoupExpression.[
              SoupTerm.`inj choice
                (Translation.chanTriple
                  (SoupTerm.* , Soup.endpoint i side₂ , e₂′)) ]*)))
  finish with canon
  ... | canonPair b₁′ b₂′ B₁′ B₂′ above′ ρ₁ ρ₂ resid
          ≋canon x₁eq x₂eq tracks₁ tracks₂ =
    targetProc
    , TypedReduction.R-Struct allCong (plug-red above′ localStep) ≋-refl
    , closeConfigStep exactStep
    where
    handle₂ = comHandle b₁′ b₂′ B₁′ B₂′

    ownerFrame₁ = E₁ SourceReduction.⋯ᶠ* ρ₁
    ownerFrame₂ = E₂ SourceReduction.⋯ᶠ* ρ₂

    ownerApp₁ =
      Source.K (Source.`select choice) Source.·¹ (Source.` 0F)

    ownerApp₂ =
      Source.K Source.`branch Source.·¹ (Source.` handle₂)

    renamedTermEq₁ :
      redex₁ Source.⋯ ρ₁ ≡
      ownerFrame₁ SourceReduction.[ ownerApp₁ ]*
    renamedTermEq₁ =
      plug*-⋯ᵣ E₁
        (Source.K (Source.`select choice) Source.·¹ (Source.` x₁)) ρ₁
      ■ cong
          (λ z → ownerFrame₁ SourceReduction.[
            Source.K (Source.`select choice) Source.·¹ (Source.` z) ]*)
          x₁eq

    renamedTermEq₂ :
      redex₂ Source.⋯ ρ₂ ≡
      ownerFrame₂ SourceReduction.[ ownerApp₂ ]*
    renamedTermEq₂ =
      plug*-⋯ᵣ E₂
        (Source.K Source.`branch Source.·¹ (Source.` x₂)) ρ₂
      ■ cong
          (λ z → ownerFrame₂ SourceReduction.[
            Source.K Source.`branch Source.·¹ (Source.` z) ]*)
          x₂eq

    localRedex : Typed.Proc _
    localRedex =
      Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        ((Typed.⟪ redex₁ Source.⋯ ρ₁ ⟫ Typed.∥
          Typed.⟪ redex₂ Source.⋯ ρ₂ ⟫)
         Typed.∥ resid)

    normalizedLocal : Typed.Proc _
    normalizedLocal =
      Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        ((Typed.⟪ ownerFrame₁ SourceReduction.[ ownerApp₁ ]* ⟫ Typed.∥
          Typed.⟪ ownerFrame₂ SourceReduction.[ ownerApp₂ ]* ⟫)
         Typed.∥ resid)

    localEq : localRedex ≡ normalizedLocal
    localEq =
      cong₂
        (λ z₁ z₂ →
          Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
            ((Typed.⟪ z₁ ⟫ Typed.∥ Typed.⟪ z₂ ⟫) Typed.∥ resid))
        renamedTermEq₁ renamedTermEq₂

    canonicalRedex : Typed.Proc 0
    canonicalRedex = plug above′ localRedex

    sourceToRedex = ≡→≋ redexProcEq

    redex≋ : P Typed.≋ canonicalRedex
    redex≋ = sourceToRedex ◅◅ ≋canon

    localCong = ≡→≋ localEq

    allCong : P Typed.≋ plug above′ normalizedLocal
    allCong = redex≋ ◅◅ ≋-plug above′ localCong

    sourceToRedexTracks₁ :
      Tracks sourceToRedex
        (thread₁ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫ 0F)
        (thread₁ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫ 0F)
    sourceToRedexTracks₁ =
      tracks-≡→≋ℕ redexProcEq
        (thread₁ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫ 0F)
        (sym (cong₂
          (λ z₁ z₂ → Fin.toℕ
            (thread₁ ctx Typed.⟪ z₁ ⟫ Typed.⟪ z₂ ⟫ 0F))
          sourceEq₁ sourceEq₂))

    sourceToRedexTracks₂ :
      Tracks sourceToRedex
        (thread₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫ 0F)
        (thread₂ ctx Typed.⟪ redex₁ ⟫ Typed.⟪ redex₂ ⟫ 0F)
    sourceToRedexTracks₂ =
      tracks-≡→≋ℕ redexProcEq
        (thread₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫ 0F)
        (sym (cong₂
          (λ z₁ z₂ → Fin.toℕ
            (thread₂ ctx Typed.⟪ z₁ ⟫ Typed.⟪ z₂ ⟫ 0F))
          sourceEq₁ sourceEq₂))

    redexTracks₁ = tracks-◅◅ sourceToRedexTracks₁ tracks₁
    redexTracks₂ = tracks-◅◅ sourceToRedexTracks₂ tracks₂

    localTrack₁ = tracks-≡→≋ℕ localEq 0F refl
    localTrack₂ = tracks-≡→≋ℕ localEq 1F refl

    allTrack₁ =
      tracks-◅◅ redexTracks₁ (tracks-≋-plug above′ localTrack₁)
    allTrack₂ =
      tracks-◅◅ redexTracks₂ (tracks-≋-plug above′ localTrack₂)

    normalizedGlobal = transportGlobalImage allCong image
    normalizedImage = localImage normalizedGlobal

    normalizedChannels :
      Vec (OrientedChannel n) (Translation.channelCount normalizedLocal)
    normalizedChannels =
      focusChannels above′ normalizedLocal (logicalChannels normalizedGlobal)

    normalizedChannel = V.head normalizedChannels
    normalizedBodyChannels = V.tail normalizedChannels

    normalizedChannelsSplit :
      normalizedChannels ≡ normalizedChannel ∷ normalizedBodyChannels
    normalizedChannelsSplit = sym (cons-head-tail normalizedChannels)

    focused = focusImage above′ normalizedLocal normalizedImage

    adjustedImage :
      LocalImage normalizedLocal
        (normalizedChannel ∷ normalizedBodyChannels)
        (focusEnv above′ normalizedLocal
          (logicalChannels normalizedGlobal) (λ ()))
        (focusedAmbientChannel focused) (focusedAmbientThread focused)
        (Soup.config cs ts)
    adjustedImage =
      transportLocalChannels normalizedChannelsSplit (focused-image focused)

    bodyImage = res-split-image adjustedImage
    ownersImage = par-split-left bodyImage

    normalizedSlot₁ =
      transportGlobalSlot allCong image allTrack₁ embedded₁
    normalizedSlot₂ =
      transportGlobalSlot allCong image allTrack₂ embedded₂

    focusedSlot₁ = focusImage-thread above′ normalizedLocal normalizedImage 0F
    focusedSlot₂ = focusImage-thread above′ normalizedLocal normalizedImage 1F

    adjustedSlot₁ =
      threadEmbedding-transportLocalChannels normalizedChannelsSplit
        (focused-image focused) 0F
    adjustedSlot₂ =
      threadEmbedding-transportLocalChannels normalizedChannelsSplit
        (focused-image focused) 1F

    ownersSlot₁ : threadEmbedding ownersImage 0F ≡ just j
    ownersSlot₁ = adjustedSlot₁ ■ focusedSlot₁ ■ normalizedSlot₁

    ownersSlot₂ : threadEmbedding ownersImage 1F ≡ just k
    ownersSlot₂ = adjustedSlot₂ ■ focusedSlot₂ ■ normalizedSlot₂

    ambientSigma =
      focusEnv above′ normalizedLocal (logicalChannels normalizedGlobal) (λ ())

    localValueEnv =
      focusValueEnv above′ normalizedLocal
        (logicalChannels normalizedGlobal) (λ ())

    leaf =
      choice-step
        {b₁ = b₁′} {b₂ = b₂′} {B₁ = B₁′} {B₂ = B₂′}
        {E₁ = ownerFrame₁} {E₂ = ownerFrame₂} {choice = choice}
        {P = resid} {channel = normalizedChannel}
        {bodyChannels = normalizedBodyChannels}
        adjustedImage localValueEnv

    sameSelector : choiceSelector leaf ≡ j
    sameSelector =
      just-injective (sym (choiceSelectorSlot leaf) ■ ownersSlot₁)

    sameBrancher : choiceBrancher leaf ≡ k
    sameBrancher =
      just-injective (sym (choiceBrancherSlot leaf) ■ ownersSlot₂)

    concreteHandle₁ =
      Translation.chanTriple
        (SoupTerm.* , Soup.endpoint i side₁ , e₁′)

    concreteHandle₂ =
      Translation.chanTriple
        (SoupTerm.* , Soup.endpoint i side₂ , e₂′)

    concreteHandleValue₁ : SoupExpression.Value concreteHandle₁
    concreteHandleValue₁ =
      subst SoupExpression.Value argEq₁
        (pairFocusValueEnv₁ ctx source₁ source₂
          (logicalChannels image) (λ ()) x₁)

    concreteHandleValue₂ : SoupExpression.Value concreteHandle₂
    concreteHandleValue₂ =
      subst SoupExpression.Value argEq₂
        (pairFocusValueEnv₂ ctx source₁ source₂
          (logicalChannels image) (λ ()) x₂)

    leafRedexEq₁ =
      sym (choiceSelectedSelect leaf) ■
      cong (lookup ts) sameSelector ■ selected₁

    leafRedexEq₂ =
      sym (choiceSelectedBranch leaf) ■
      cong (lookup ts) sameBrancher ■ selected₂

    unique₁ =
      redex-unique
        {F = choiceSelectFrame leaf} {F′ = F₁}
        {c = SoupTerm.`select (choiceLabel leaf)}
        {c′ = SoupTerm.`select choice}
        (choiceSelectHandleValue leaf) concreteHandleValue₁ leafRedexEq₁

    unique₂ =
      redex-unique
        {F = choiceBranchFrame leaf} {F′ = F₂}
        {c = SoupTerm.`branch} {c′ = SoupTerm.`branch}
        (choiceBranchHandleValue leaf) concreteHandleValue₂ leafRedexEq₂

    sameLabel : choiceLabel leaf ≡ choice
    sameLabel = select-injective (proj₁ unique₁)

    sameHandle₁ = proj₁ (proj₂ unique₁)
    sameHandle₂ = proj₁ (proj₂ unique₂)

    sameLeftTarget :
      choiceSelectFrame leaf SoupExpression.[
        Translation.chanTriple
          ( SoupTerm.*
          , Soup.endpoint (BorrowedCF.Simulation.ForwardSoup.Local.Choice.choiceChannel leaf)
              (BorrowedCF.Simulation.ForwardSoup.Local.Choice.choiceSide₁ leaf)
          , choiceSelectTail leaf ) ]* ≡
      F₁ SoupExpression.[ concreteHandle₁ ]*
    sameLeftTarget =
      cong (SoupExpression._[_]* (choiceSelectFrame leaf)) sameHandle₁
      ■ proj₁ (proj₂ (proj₂ unique₁)) concreteHandle₁

    sameRightTarget :
      choiceBranchFrame leaf SoupExpression.[
        SoupTerm.`inj (choiceLabel leaf)
          (Translation.chanTriple
            ( SoupTerm.*
            , Soup.endpoint (BorrowedCF.Simulation.ForwardSoup.Local.Choice.choiceChannel leaf)
                (BorrowedCF.Simulation.ForwardSoup.Local.Choice.choiceSide₂ leaf)
            , choiceBranchTail leaf )) ]* ≡
      F₂ SoupExpression.[ SoupTerm.`inj choice concreteHandle₂ ]*
    sameRightTarget =
      cong (SoupExpression._[_]* (choiceBranchFrame leaf))
        (cong₂ SoupTerm.`inj sameLabel sameHandle₂)
      ■ proj₁ (proj₂ (proj₂ unique₂))
          (SoupTerm.`inj choice concreteHandle₂)

    exactStep =
      ascend focused
        (choiceConfigStepAt leaf
          sameSelector sameBrancher sameLeftTarget sameRightTarget)

    localTarget : Typed.Proc _
    localTarget =
      Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        ((Typed.⟪ ownerFrame₁ SourceReduction.[ Source.` 0F ]* ⟫ Typed.∥
          Typed.⟪ ownerFrame₂ SourceReduction.[
            Source.`inj choice (Source.` handle₂) ]* ⟫)
         Typed.∥ resid)

    localStep : normalizedLocal TypedReduction.─→ₚ localTarget
    localStep =
      TypedReduction.R-Choice ownerFrame₁ ownerFrame₂ choice

    targetProc : Typed.Proc 0
    targetProc = plug above′ localTarget
