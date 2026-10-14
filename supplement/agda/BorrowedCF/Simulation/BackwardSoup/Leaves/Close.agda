-- | Backward simulation for the soup close leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Close where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.ListAction using (sum)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Vec.Relation.Unary.All as AllV
open import Relation.Binary.Construct.Closure.Symmetric using (fwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

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

open import BorrowedCF.Processes.TranslationSoup.Properties
  using (UB-flags-length)

open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( Orientation; forward; reverse; OrientedChannel; LocalImage
        ; OptionalThreadImage; present; omitted; threadEmbedding
        ; physicalChannel; physicalEndpoint
        ; channelEmbedding-injective; live-channel; live-thread)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Local.Close
  using ( close-step
        ; closeLeft; closeRight; closeLeftSlot; closeRightSlot
        ; closeChannel; closeSide₁; closeSide₂
        ; closeSelectedLeft; closeSelectedRight
        ; closeLeftFrame; closeRightFrame; closeConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; processCount-rename)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-pair-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( closedPairEnv; plug; focusEnv; focusValueEnv; focusTyping
        ; focusChannels; threadInContext; ≡→≋; ≋-sym; ≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.LocatePair
  using (LocatedPair; located-pair; image-thread-pair; focusPairExprTyping)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; plug₂; thread₁; thread₂; fill₁; fill₂
        ; plug-fill₁; plug-fill₂; Binder₂; binder₂⇒₁; binder₂⇒₂
        ; CanonPair; canonPair; canon-pair; HeadShape₂; heads-lr; heads-rl
        ; headShapes⇒₂)
import BorrowedCF.Simulation.BackwardSoup.CanonicalPair as CanonicalPair
import BorrowedCF.Simulation.BackwardSoup.Canonical as Canonical
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using ( tracks-≡→≋ℕ; threadInContext-ℕ
        ; ∥-commℕ-l; ν-ext′ℕ)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using ( Tracks; tracks-◅◅; tracks-sym; tracks-gmap-ν
        ; tracks-≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread
        ; focusedAmbientChannel; focusedAmbientThread
        ; ascend; plug-red; closeConfigStep)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective; endpoint-injective)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Simulation.Support.Frames
  using (frame-plug₁)
open import BorrowedCF.Simulation.Support.FrameRename
  using (⋯ᶠ*-cong)
open import BorrowedCF.Simulation.Support.PairConfine
  using (comHandle; close-handle-end; close-group-width; close-pair-confine)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (ImpureHandleConst; GroupOf; head-group)
open import BorrowedCF.Simulation.BackwardSoup.AcqShape
  using (UB-entry-shape)
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head′)
open import BorrowedCF.Simulation.BackwardSoup.PairPosition
  using ( pairFocusEnv₁; pairFocusEnv₂
        ; pairFocusValueEnv₁; pairFocusValueEnv₂
        ; pairFocusPairEnv₁; pairFocusPairEnv₂
        ; pairThread₁-content; pairThread₂-content
        ; same-physical-channel⇒binder₂-data
        )
open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open Fin.Patterns

private
  cong₃ :
    {A B C D : Set} (f : A → B → C → D)
    {a a′ : A} {b b′ : B} {c c′ : C} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

  wkₚ-zero : ∀ {n} →
    Source.wkₚ {n} 0 0 ≗ Source.weaken* ⦃ Source.Kᵣ ⦄ 2
  wkₚ-zero x =
    cong suc (cong suc
      (Fin.cast-is-id _ (Fin.cast _ x) ■ Fin.cast-is-id _ x))

  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  just-not-nothing : {A : Set} {x : A} → just x ≢ nothing
  just-not-nothing ()

  cons-head-tail :
    {A : Set} {q : ℕ} (xs : Vec A (suc q)) →
    V.head xs ∷ V.tail xs ≡ xs
  cons-head-tail (x ∷ xs) = refl

  singleton-eta :
    {A : Set} (xs : Vec A 1) → xs ≡ V.head xs ∷ []
  singleton-eta (x ∷ []) = refl

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

  plug-hole-typing :
    ∀ {n} {Γ : Context.Ctx n} {γ : Context.Struct n}
      {E : SourceReduction.Frame* n} {e : Source.Tm n} {T ϵ} →
    Γ ; γ ⊢ E SourceReduction.[ e ]* ∶ T ∣ ϵ →
    Σ[ γ′ ∈ Context.Struct n ] Σ[ U ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      Γ ; γ′ ⊢ e ∶ U ∣ ϵ′
  plug-hole-typing {E = E} {e = e} typed
    with SourceReduction.⊢[]*⁻¹ E e typed
  ... | _ , γ′ , _ , U , _ , ϵ′ , _ , _ , _ , _ , ⊢e =
    γ′ , U , ϵ′ , ⊢e

  opposite-apart :
    ∀ {side₁ side₂} → SoupReduction.Opposite side₁ side₂ → side₁ ≢ side₂
  opposite-apart SoupReduction.left-right ()
  opposite-apart SoupReduction.right-left ()

  syncs-head-zero :
    (b : ℕ) (B : Typed.BindGroup) →
    Translation.syncs (suc b ∷ B) ≡ 0 → B ≡ []
  syncs-head-zero b [] equal = refl
  syncs-head-zero b (_ ∷ _ ∷ _) ()

  bindChannel-syncs-zero :
    {n : ℕ} {B₁ B₂ : Typed.BindGroup}
    (channel : BorrowedCF.Simulation.ForwardSoup.LocalImage.OrientedChannel n) →
    bindChannel B₁ B₂ channel ≡ (true , [] , []) →
    Translation.syncs B₁ ≡ 0 × Translation.syncs B₂ ≡ 0
  bindChannel-syncs-zero {B₁ = B₁} {B₂ = B₂} (i , forward) equal =
    let
      leftLength = cong (L.length ∘ proj₁ ∘ proj₂) equal
      rightLength = cong (L.length ∘ proj₂ ∘ proj₂) equal
      leftEnd = Soup.endpoint i 0F
      rightEnd = Soup.endpoint i 1F
    in
    ( (sym (UB-flags-length B₁ leftEnd
        (SoupTerm.* , leftEnd , SoupTerm.*)) ■ leftLength)
    , (sym (UB-flags-length B₂ rightEnd
        (SoupTerm.* , rightEnd , SoupTerm.*)) ■ rightLength)
    )
  bindChannel-syncs-zero {B₁ = B₁} {B₂ = B₂} (i , reverse) equal =
    let
      leftLength = cong (L.length ∘ proj₂ ∘ proj₂) equal
      rightLength = cong (L.length ∘ proj₁ ∘ proj₂) equal
      leftEnd = Soup.endpoint i 1F
      rightEnd = Soup.endpoint i 0F
    in
    ( (sym (UB-flags-length B₁ leftEnd
        (SoupTerm.* , leftEnd , SoupTerm.*)) ■ leftLength)
    , (sym (UB-flags-length B₂ rightEnd
        (SoupTerm.* , rightEnd , SoupTerm.*)) ■ rightLength)
    )

  bindEnv-head-shape :
    {n k : ℕ} (b : ℕ) (B₁ B₂ : Typed.BindGroup)
    (channel : OrientedChannel n) (sigma : Translation.Env k (2 *ℕ n)) →
    Σ[ left ∈ SoupTerm.Tm (2 *ℕ n) ]
    Σ[ right ∈ SoupTerm.Tm (2 *ℕ n) ]
      bindEnv (suc b ∷ B₁) B₂ channel sigma 0F ≡
      Translation.chanTriple
        (left , physicalEndpoint channel 0F , right)
  bindEnv-head-shape {k = k} b B₁ B₂ channel sigma
    with UB-entry-shape (suc b ∷ B₁)
           (physicalEndpoint channel 0F) (physicalEndpoint channel 0F)
           SoupTerm.* SoupTerm.* 0F (head-group B₁ 0F)
  ... | left , right , entryEq =
    left , right ,
    (++ₛ-lookupˡ
      (proj₁ (Translation.UB[ suc b ∷ B₁ ]
          (physicalEndpoint channel 0F)
          (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ]
          (physicalEndpoint channel 1F)
          (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma (0F ↑ˡ sum B₂)
    ■ ++ₛ-lookupˡ
        (proj₁ (Translation.UB[ suc b ∷ B₁ ]
          (physicalEndpoint channel 0F)
          (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)))
        (proj₁ (Translation.UB[ B₂ ]
          (physicalEndpoint channel 1F)
          (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))) 0F
    ■ entryEq)

  close-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {p : Types.Pol} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K (SoupTerm.`end p) SoupTerm.·¹ v
        ]* →
    t ≢ SoupTerm.*
  close-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  ⟨⟩≭⊗ :
    ∀ {s T U d} → ¬ (Types.⟨ s ⟩ Types.≃ (T Types.⊗⟨ d ⟩ U))
  ⟨⟩≭⊗ ()

  pair-not-channel :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {a b : Source.Tm k} {R ϵ s} →
    Γ ; γ ⊢ a Source.⊗ b ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    ⊥
  pair-not-channel typed eq
    with Source.inv-⊗ typed
  ... | _ , _ , _ , _ , _ , _ , _ , _ , pairEq , _ =
    ⟨⟩≭⊗ (Types.≃-trans eq (Types.≃-sym pairEq))

  fn-end-dom :
    ∀ {N} {Γ : Context.Ctx N} {β : Context.Struct N} {p T U a ϵ} →
    Γ ; β ⊢ Source.K (Source.`end p) ∶ T Types.⟨ a ⟩→ U ∣ ϵ →
    Types.⟨ Types.end p ⟩ Types.≃ T
  fn-end-dom (Source.T-Const Source.`end) = Types.≃-refl
  fn-end-dom (Source.T-Conv (dom≃ Types.`→ cod≃) _ d) =
    Types.≃-trans (fn-end-dom d) dom≃
  fn-end-dom (Source.T-Weaken _ d) = fn-end-dom d

  end-arg-chan :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {p : Types.Pol} {arg : Source.Tm k} {T ϵ} →
    Γ ; γ ⊢ Source.K (Source.`end p) Source.·¹ arg ∶ T ∣ ϵ →
    Σ[ β ∈ Context.Struct k ] Σ[ R ∈ Types.𝕋 ] Σ[ ϵ₂ ∈ Types.Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) ×
      (Types.⟨ Types.end p ⟩ Types.≃ R)
  end-arg-chan (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    _ , _ , _ , ⊢arg , fn-end-dom ⊢fn
  end-arg-chan (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    _ , _ , _ , ⊢arg , fn-end-dom ⊢fn
  end-arg-chan (Source.T-Conv _ _ d) = end-arg-chan d
  end-arg-chan (Source.T-Weaken _ d) = end-arg-chan d

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
        (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) pairEq ⊢arg)
        ch)

------------------------------------------------------------------------
-- A strict soup close reflects to a typed close.

close-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : SoupExpression.Frame* (2 *ℕ n)) →
  j ≢ k →
  SoupReduction.Opposite side₁ side₂ →
  lookup cs i ≡ (true , [] , []) →
  lookup ts j ≡
    F₁ SoupExpression.[
      SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*)
    ]* →
  lookup ts k ≡
    F₂ SoupExpression.[
      SoupTerm.K (SoupTerm.`end Types.⁇) SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₂ , SoupTerm.*)
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config
        (SoupReduction.replaceAt cs i (false , [] , []))
        (SoupReduction.replaceTwo ts
          j (F₁ SoupExpression.[ SoupTerm.* ]*)
          k (F₂ SoupExpression.[ SoupTerm.* ]*)))
close-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j k i side₁ side₂ F₁ F₂ slotsApart opposite channelEq
  selected₁ selected₂ ⊢P image
  with image-thread-pair image j k slotsApart
         (close-redex-not-unit {F = F₁} selected₁)
         (close-redex-not-unit {F = F₂} selected₂)
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
         F₁ (Source.`end Types.‼) Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*))
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
         F₂ (Source.`end Types.⁇) Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side₂ , SoupTerm.*))
         (sym (pairThread₂-content ctx source₁ source₂
                 (logicalChannels image) (λ ()))
          ■ sym content₂ ■ selected₂)
... | E₂ , arg₂ , sourceEq₂ , frameEq₂ , argEq₂
  with SourceReduction.⊢[]*⁻¹ E₁
         (Source.K (Source.`end Types.‼) Source.·¹ arg₁)
         (subst (λ z → Γ₁ ; γ₁ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₁ ⊢source₁)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₁ , ⊢app₁
  with end-arg-chan ⊢app₁
... | β₁ , R₁ , ϵ₁ , ⊢arg₁ , argType₁
  with argument-var ⊢arg₁ argType₁ argEq₁
... | x₁ , refl
  with SourceReduction.⊢[]*⁻¹ E₂
         (Source.K (Source.`end Types.⁇) Source.·¹ arg₂)
         (subst (λ z → Γ₂ ; γ₂ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₂ ⊢source₂)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₂ , ⊢app₂
  with end-arg-chan ⊢app₂
... | β₂ , R₂ , ϵ₂ , ⊢arg₂ , argType₂
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
      Source.K (Source.`end Types.‼) Source.·¹ (Source.` x₁) ]*

  redex₂ : Source.Tm _
  redex₂ =
    E₂ SourceReduction.[
      Source.K (Source.`end Types.⁇) Source.·¹ (Source.` x₂) ]*

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
      {E = E₁} {c = Source.`end Types.‼} {x = x₁}
      bnd₁ ⊢redex₁ ImpureHandleConst.`end

  head₂ =
    impure-redex-head′
      {E = E₂} {c = Source.`end Types.⁇} {x = x₂}
      bnd₂ ⊢redex₂ ImpureHandleConst.`end

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
  canon =
    canon-pair redex₁ redex₂ bnd headShape

  finish :
    Σ[ P′ ∈ Typed.Proc 0 ]
      (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
        TypedReduction.─→ₚ P′) ×
      GlobalImage P′
        (Soup.config
          (SoupReduction.replaceAt cs i (false , [] , []))
          (SoupReduction.replaceTwo ts
            j (F₁ SoupExpression.[ SoupTerm.* ]*)
            k (F₂ SoupExpression.[ SoupTerm.* ]*)))
  finish with canon
  ... | canonPair b₁′ b₂′ B₁′ B₂′ above′ ρ₁ ρ₂ resid
          ≋canon x₁eq x₂eq tracks₁ tracks₂ = result
    where
    localRedex : Typed.Proc _
    localRedex =
      Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        ((Typed.⟪ redex₁ Source.⋯ ρ₁ ⟫ Typed.∥
          Typed.⟪ redex₂ Source.⋯ ρ₂ ⟫)
         Typed.∥ resid)

    canonicalRedex : Typed.Proc 0
    canonicalRedex = plug above′ localRedex

    sourceToRedex = ≡→≋ redexProcEq

    redex≋ : P Typed.≋ canonicalRedex
    redex≋ = sourceToRedex ◅◅ ≋canon

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

    canonicalGlobal = transportGlobalImage redex≋ image
    canonicalImage = localImage canonicalGlobal

    canonicalChannels :
      Vec (OrientedChannel n) (Translation.channelCount localRedex)
    canonicalChannels =
      focusChannels above′ localRedex (logicalChannels canonicalGlobal)

    canonicalChannel : OrientedChannel n
    canonicalChannel = V.head canonicalChannels

    canonicalBodyChannels = V.tail canonicalChannels

    canonicalChannelsSplit :
      canonicalChannels ≡ canonicalChannel ∷ canonicalBodyChannels
    canonicalChannelsSplit = sym (cons-head-tail canonicalChannels)

    focused = focusImage above′ localRedex canonicalImage

    adjustedImage :
      LocalImage localRedex (canonicalChannel ∷ canonicalBodyChannels)
        (focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ()))
        (focusedAmbientChannel focused) (focusedAmbientThread focused)
        (Soup.config cs ts)
    adjustedImage =
      transportLocalChannels canonicalChannelsSplit (focused-image focused)

    bodyImage = res-split-image adjustedImage

    canonicalSlot₁ =
      transportGlobalSlot redex≋ image redexTracks₁ embedded₁

    canonicalSlot₂ =
      transportGlobalSlot redex≋ image redexTracks₂ embedded₂

    focusedSlot₁ = focusImage-thread above′ localRedex canonicalImage 0F
    focusedSlot₂ = focusImage-thread above′ localRedex canonicalImage 1F

    adjustedSlot₁ =
      threadEmbedding-transportLocalChannels canonicalChannelsSplit
        (focused-image focused) 0F
    adjustedSlot₂ =
      threadEmbedding-transportLocalChannels canonicalChannelsSplit
        (focused-image focused) 1F

    bodySlot₁ : threadEmbedding bodyImage 0F ≡ just j
    bodySlot₁ = adjustedSlot₁ ■ focusedSlot₁ ■ canonicalSlot₁

    bodySlot₂ : threadEmbedding bodyImage 1F ≡ just k
    bodySlot₂ = adjustedSlot₂ ■ focusedSlot₂ ■ canonicalSlot₂

    bodyContent₁ = present-lookup (live-thread bodyImage 0F) bodySlot₁
    bodyContent₂ = present-lookup (live-thread bodyImage 1F) bodySlot₂

    ambientSigma =
      focusEnv above′ localRedex (logicalChannels canonicalGlobal) (λ ())

    bodySigma =
      bindEnv (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        canonicalChannel ambientSigma

    localValueEnv =
      focusValueEnv above′ localRedex
        (logicalChannels canonicalGlobal) (λ ())

    bodyValueEnv : ValueEnv bodySigma
    bodyValueEnv =
      bindEnv-Value
        {B₁ = suc b₁′ ∷ B₁′} {B₂ = suc b₂′ ∷ B₂′}
        {channel = canonicalChannel} localValueEnv

    ownerFrame₁ = E₁ SourceReduction.⋯ᶠ* ρ₁

    ownerApp₁ =
      Source.K (Source.`end Types.‼) Source.·¹ (Source.` 0F)

    renamedTermEq₁ :
      redex₁ Source.⋯ ρ₁ ≡
      ownerFrame₁ SourceReduction.[ ownerApp₁ ]*
    renamedTermEq₁ =
      plug*-⋯ᵣ E₁
        (Source.K (Source.`end Types.‼) Source.·¹ (Source.` x₁)) ρ₁
      ■ cong
          (λ z → ownerFrame₁ SourceReduction.[
            Source.K (Source.`end Types.‼) Source.·¹ (Source.` z) ]*)
          x₁eq

    soupFrame₁ = Tᶠ*[ ownerFrame₁ ] { σ = bodySigma } bodyValueEnv

    canonicalSelected₁ :
      lookup ts j ≡
      soupFrame₁ SoupExpression.[
        SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹ bodySigma 0F ]*
    canonicalSelected₁ =
      bodyContent₁
      ■ cong (λ z → Translation.T[ z ] bodySigma) renamedTermEq₁
      ■ T[_]-plugᶠ* ownerFrame₁ {e = ownerApp₁} bodyValueEnv

    concreteHandleValue :
      SoupExpression.Value
        (Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*))
    concreteHandleValue =
      subst SoupExpression.Value argEq₁
        (pairFocusValueEnv₁ ctx source₁ source₂
          (logicalChannels image) (λ ()) x₁)

    redexEq₁ :
      soupFrame₁ SoupExpression.[
        SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹ bodySigma 0F ]* ≡
      F₁ SoupExpression.[
        SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹
          Translation.chanTriple
            (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*) ]*
    redexEq₁ = sym canonicalSelected₁ ■ selected₁

    handleEq₁ :
      bodySigma 0F ≡
      Translation.chanTriple
        (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*)
    handleEq₁ =
      proj₁ (proj₂ (redex-unique
        {F = soupFrame₁} {F′ = F₁}
        {c = SoupTerm.`end Types.‼} {c′ = SoupTerm.`end Types.‼}
        (bodyValueEnv 0F) concreteHandleValue redexEq₁))

    headShape₁ =
      bindEnv-head-shape b₁′ B₁′ (suc b₂′ ∷ B₂′)
        canonicalChannel ambientSigma

    headLeft₁ = proj₁ headShape₁
    headRight₁ = proj₁ (proj₂ headShape₁)
    headEntryEq₁ = proj₂ (proj₂ headShape₁)

    endpointEq₁ :
      physicalEndpoint canonicalChannel 0F ≡ Soup.endpoint i side₁
    endpointEq₁ =
      proj₁ (proj₂ (chanTriple-injective
        (sym headEntryEq₁ ■ handleEq₁)))

    canonicalPhysicalEq : physicalChannel canonicalChannel ≡ i
    canonicalPhysicalEq = proj₁ (endpoint-injective endpointEq₁)

    canonicalBinderEmpty :
      bindChannel (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
        canonicalChannel ≡ (true , [] , [])
    canonicalBinderEmpty =
      sym (res-split-channel adjustedImage)
      ■ cong (lookup cs) canonicalPhysicalEq
      ■ channelEq

    canonicalSyncs =
      bindChannel-syncs-zero
        {B₁ = suc b₁′ ∷ B₁′} {B₂ = suc b₂′ ∷ B₂′}
        canonicalChannel canonicalBinderEmpty

    B₁′≡[] = syncs-head-zero b₁′ B₁′ (proj₁ canonicalSyncs)
    B₂′≡[] = syncs-head-zero b₂′ B₂′ (proj₂ canonicalSyncs)

    canonicalTyping : [] ; Context.[] ⊢ₚ canonicalRedex
    canonicalTyping = AllV.[] / ⊢P ⊢-≋ redex≋

    focusedTyping =
      focusTyping above′ localRedex AllV.[] canonicalTyping

    localGamma = proj₁ focusedTyping
    localStruct = proj₁ (proj₂ focusedTyping)
    localChanCx = proj₁ (proj₂ (proj₂ focusedTyping))
    localTyping = proj₂ (proj₂ (proj₂ focusedTyping))

    result :
      Σ[ P′ ∈ Typed.Proc 0 ]
        (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
          TypedReduction.─→ₚ P′) ×
        GlobalImage P′
          (Soup.config
            (SoupReduction.replaceAt cs i (false , [] , []))
            (SoupReduction.replaceTwo ts
              j (F₁ SoupExpression.[ SoupTerm.* ]*)
              k (F₂ SoupExpression.[ SoupTerm.* ]*)))
    result with B₁′≡[] | B₂′≡[]
    ... | refl | refl = build normalizedTyping
      where
      ownerFrame₂ = E₂ SourceReduction.⋯ᶠ* ρ₂

      ownerApp₂ =
        Source.K (Source.`end Types.⁇) Source.·¹
          (Source.` (comHandle b₁′ b₂′ [] []))

      renamedTermEq₂ :
        redex₂ Source.⋯ ρ₂ ≡
        ownerFrame₂ SourceReduction.[ ownerApp₂ ]*
      renamedTermEq₂ =
        plug*-⋯ᵣ E₂
          (Source.K (Source.`end Types.⁇) Source.·¹ (Source.` x₂)) ρ₂
        ■ cong
            (λ z → ownerFrame₂ SourceReduction.[
              Source.K (Source.`end Types.⁇) Source.·¹ (Source.` z) ]*)
            x₂eq

      normalizedLocal : Typed.Proc _
      normalizedLocal =
        Typed.ν (suc b₁′ ∷ []) (suc b₂′ ∷ [])
          ((Typed.⟪ ownerFrame₁ SourceReduction.[ ownerApp₁ ]* ⟫ Typed.∥
            Typed.⟪ ownerFrame₂ SourceReduction.[ ownerApp₂ ]* ⟫)
           Typed.∥ resid)

      localEq : localRedex ≡ normalizedLocal
      localEq =
        cong₂
          (λ z₁ z₂ →
            Typed.ν (suc b₁′ ∷ []) (suc b₂′ ∷ [])
              ((Typed.⟪ z₁ ⟫ Typed.∥ Typed.⟪ z₂ ⟫) Typed.∥ resid))
          renamedTermEq₁ renamedTermEq₂

      normalizedTyping :
        localGamma ; localStruct ⊢ₚ normalizedLocal
      normalizedTyping =
        subst (λ Z → localGamma ; localStruct ⊢ₚ Z) localEq localTyping

      build :
        localGamma ; localStruct ⊢ₚ normalizedLocal →
        Σ[ P′ ∈ Typed.Proc 0 ]
          (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
            TypedReduction.─→ₚ P′) ×
          GlobalImage P′
            (Soup.config
              (SoupReduction.replaceAt cs i (false , [] , []))
              (SoupReduction.replaceTwo ts
                j (F₁ SoupExpression.[ SoupTerm.* ]*)
                k (F₂ SoupExpression.[ SoupTerm.* ]*)))
      build ⊢normalized with Typed.inv-ν ⊢normalized
      ... | Γleft , Γright , sess , pol , newSess
          , ⊢leftGroup , ⊢rightGroup
          , bindLeft , bindRight , ⊢body =
        finishWidths b₁′≡0 b₂′≡0
        where
        bodySplit = Typed.inv-∥ ⊢body
        ⊢owners = proj₁ (proj₂ (proj₂ (proj₂ bodySplit)))

        ownersSplit = Typed.inv-∥ ⊢owners
        ⊢owner₁ = proj₁ (proj₂ (proj₂ (proj₂ ownersSplit)))
        ⊢owner₂ = proj₂ (proj₂ (proj₂ (proj₂ ownersSplit)))

        holeTyping₁ =
          plug-hole-typing {E = ownerFrame₁} {e = ownerApp₁}
            (Typed.inv-⟪⟫ ⊢owner₁)
        holeTyping₂ =
          plug-hole-typing {E = ownerFrame₂} {e = ownerApp₂}
            (Typed.inv-⟪⟫ ⊢owner₂)
        ⊢ownerApp₁ = proj₂ (proj₂ (proj₂ holeTyping₁))
        ⊢ownerApp₂ = proj₂ (proj₂ (proj₂ holeTyping₂))

        leftChanCx = Typed.bindCtx⇒chanCtx bindLeft
        leftSession = proj₁ (SourceReduction.chanCx-lookup leftChanCx 0F)
        leftLookup = proj₂ (SourceReduction.chanCx-lookup leftChanCx 0F)

        bodyLeftLookup :
          lookup ((Γleft Context.⸴* Γright) Context.⸴* localGamma) 0F ≡
          Types.⟨ leftSession ⟩
        bodyLeftLookup =
          V.lookup-++ˡ (Γleft Context.⸴* Γright) localGamma
            (0F ↑ˡ V.length Γright)
          ■ V.lookup-++ˡ Γleft Γright 0F
          ■ leftLookup

        leftTip = close-handle-end ⊢ownerApp₁ bodyLeftLookup

        b₁′≡0 : b₁′ ≡ 0
        b₁′≡0 =
          close-group-width newSess bindLeft leftLookup leftTip

        rightChanCx = Typed.bindCtx⇒chanCtx bindRight
        rightSession = proj₁ (SourceReduction.chanCx-lookup rightChanCx 0F)
        rightLookup = proj₂ (SourceReduction.chanCx-lookup rightChanCx 0F)

        bodyRightLookup :
          lookup ((Γleft Context.⸴* Γright) Context.⸴* localGamma)
            (comHandle b₁′ b₂′ [] []) ≡
          Types.⟨ rightSession ⟩
        bodyRightLookup =
          V.lookup-++ˡ (Γleft Context.⸴* Γright) localGamma
            ((V.length Γleft) ↑ʳ 0F)
          ■ V.lookup-++ʳ Γleft Γright 0F
          ■ rightLookup

        rightTip = close-handle-end ⊢ownerApp₂ bodyRightLookup

        b₂′≡0 : b₂′ ≡ 0
        b₂′≡0 =
          close-group-width (Types.new-dual newSess)
            bindRight rightLookup rightTip

        finishWidths :
          b₁′ ≡ 0 → b₂′ ≡ 0 →
          Σ[ P′ ∈ Typed.Proc 0 ]
            (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
              TypedReduction.─→ₚ P′) ×
            GlobalImage P′
              (Soup.config
                (SoupReduction.replaceAt cs i (false , [] , []))
                (SoupReduction.replaceTwo ts
                  j (F₁ SoupExpression.[ SoupTerm.* ]*)
                  k (F₂ SoupExpression.[ SoupTerm.* ]*)))
        finishWidths refl refl
          with close-pair-confine
            localChanCx
            {E₁ = ownerFrame₁} {E₂ = ownerFrame₂} {P = resid}
            ⊢normalized
        ... | E₁₀ , E₁eq , E₂₀ , E₂eq , residual , residualEq =
          targetProc
          , TypedReduction.R-Struct redex≋
              (plug-red above′ localStep) ≋-refl
          , closeConfigStep exactStep
          where
          closeRedex : Typed.Proc _
          closeRedex =
            Typed.ν (1 ∷ []) (1 ∷ [])
              (Typed.⟪ E₁₀ SourceReduction.⋯ᶠ*
                    Source.weaken* ⦃ Source.Kᵣ ⦄ 2
                  SourceReduction.[ ownerApp₁ ]* ⟫
               Typed.∥
               Typed.⟪ E₂₀ SourceReduction.⋯ᶠ*
                    Source.weaken* ⦃ Source.Kᵣ ⦄ 2
                  SourceReduction.[ ownerApp₂ ]* ⟫)

          closeTarget : Typed.Proc _
          closeTarget =
            Typed.⟪ E₁₀ SourceReduction.[ Source.* ]* ⟫ Typed.∥
            Typed.⟪ E₂₀ SourceReduction.[ Source.* ]* ⟫

          isolatedLocal : Typed.Proc _
          isolatedLocal = residual Typed.∥ closeRedex

          isolatedTarget : Typed.Proc _
          isolatedTarget = residual Typed.∥ closeTarget

          factoredLocal : Typed.Proc _
          factoredLocal =
            Typed.ν (1 ∷ []) (1 ∷ [])
              ((Typed.⟪ E₁₀ SourceReduction.⋯ᶠ*
                    Source.weaken* ⦃ Source.Kᵣ ⦄ 2
                  SourceReduction.[ ownerApp₁ ]* ⟫
                Typed.∥
                Typed.⟪ E₂₀ SourceReduction.⋯ᶠ*
                    Source.weaken* ⦃ Source.Kᵣ ⦄ 2
                  SourceReduction.[ ownerApp₂ ]* ⟫)
               Typed.∥
               (residual Typed.⋯ₚ
                 Source.weaken* ⦃ Source.Kᵣ ⦄ 2))

          factorEq : normalizedLocal ≡ factoredLocal
          factorEq =
            cong₃
              (λ X Y Q →
                Typed.ν (1 ∷ []) (1 ∷ [])
                  ((Typed.⟪ X SourceReduction.[ ownerApp₁ ]* ⟫ Typed.∥
                    Typed.⟪ Y SourceReduction.[ ownerApp₂ ]* ⟫)
                   Typed.∥ Q))
              (E₁eq ■ ⋯ᶠ*-cong E₁₀ wkₚ-zero)
              (E₂eq ■ ⋯ᶠ*-cong E₂₀ wkₚ-zero)
              (residualEq ■ Typed.⋯ₚ-cong residual wkₚ-zero)

          isolate≋ : factoredLocal Typed.≋ isolatedLocal
          isolate≋ =
            Typed.ν-cong Typed.∥-comm
            ◅◅ ≋-sym (fwd Typed.ν-ext′ ◅ ≋-refl)

          localCong : localRedex Typed.≋ isolatedLocal
          localCong =
            ≡→≋ localEq ◅◅ ≡→≋ factorEq ◅◅ isolate≋

          closeCtx =
            BorrowedCF.Simulation.BackwardSoup.Locate.par-right
              residual BorrowedCF.Simulation.BackwardSoup.Locate.hole

          localTrack :
            (q : 𝔽 2) →
            Tracks localCong
              (q ↑ˡ Translation.processCount resid)
              (threadInContext closeCtx closeRedex q)
          localTrack q =
            tracks-◅◅
              (tracks-≡→≋ℕ localEq
                (q ↑ˡ Translation.processCount resid) refl)
              (tracks-◅◅
                (tracks-≡→≋ℕ factorEq
                  (q ↑ˡ Translation.processCount resid)
                  {b = q ↑ˡ Translation.processCount
                    (residual Typed.⋯ₚ
                      Source.weaken* ⦃ Source.Kᵣ ⦄ 2)}
                  (Fin.toℕ-↑ˡ q
                    (Translation.processCount
                      (residual Typed.⋯ₚ
                        Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                   ■ sym (Fin.toℕ-↑ˡ q
                     (Translation.processCount resid))))
                (tracks-◅◅
                  (tracks-gmap-ν
                    (∥-commℕ-l q
                      (Fin.toℕ-↑ˡ q
                        (Translation.processCount
                          (residual Typed.⋯ₚ
                            Source.weaken* ⦃ Source.Kᵣ ⦄ 2)))
                      (Fin.toℕ-↑ʳ
                        (Translation.processCount
                          (residual Typed.⋯ₚ
                            Source.weaken* ⦃ Source.Kᵣ ⦄ 2)) q)))
                  (tracks-sym
                    (ν-ext′ℕ
                      (Translation.processCount residual ↑ʳ q)
                      (Fin.toℕ-↑ʳ
                        (Translation.processCount
                          (residual Typed.⋯ₚ
                            Source.weaken* ⦃ Source.Kᵣ ⦄ 2)) q
                       ■ cong (_+ Fin.toℕ q)
                           (processCount-rename residual
                             (Source.weaken* ⦃ Source.Kᵣ ⦄ 2))
                       ■ sym (Fin.toℕ-↑ʳ
                           (Translation.processCount residual) q))))))

          allCong :
            P Typed.≋ plug above′ isolatedLocal
          allCong = redex≋ ◅◅ ≋-plug above′ localCong

          allTrack₁ =
            tracks-◅◅ redexTracks₁
              (tracks-≋-plug above′ (localTrack 0F))

          allTrack₂ =
            tracks-◅◅ redexTracks₂
              (tracks-≋-plug above′ (localTrack 1F))

          isolatedGlobal = transportGlobalImage allCong image
          isolatedImage = localImage isolatedGlobal

          outerChannels =
            focusChannels above′ isolatedLocal
              (logicalChannels isolatedGlobal)

          outerFocused = focusImage above′ isolatedLocal isolatedImage
          closeFocused =
            focusImage closeCtx closeRedex (focused-image outerFocused)

          closeChannels =
            focusChannels closeCtx closeRedex outerChannels

          closeChannel′ = V.head closeChannels

          closeChannelsSingleton :
            closeChannels ≡ closeChannel′ ∷ []
          closeChannelsSingleton = singleton-eta closeChannels

          adjustedCloseImage =
            transportLocalChannels closeChannelsSingleton
              (focused-image closeFocused)

          outerValueEnv =
            focusValueEnv above′ isolatedLocal
              (logicalChannels isolatedGlobal) (λ ())

          closeValueEnv =
            focusValueEnv closeCtx closeRedex outerChannels outerValueEnv

          leaf =
            close-step
              {E₁ = E₁₀} {E₂ = E₂₀}
              {channel = closeChannel′}
              adjustedCloseImage closeValueEnv

          isolatedSlot₁ =
            transportGlobalSlot allCong image allTrack₁ embedded₁

          isolatedSlot₂ =
            transportGlobalSlot allCong image allTrack₂ embedded₂

          isolatedOuterSlot₁ =
            focusImage-thread above′ isolatedLocal isolatedImage
              (threadInContext closeCtx closeRedex 0F)

          isolatedOuterSlot₂ =
            focusImage-thread above′ isolatedLocal isolatedImage
              (threadInContext closeCtx closeRedex 1F)

          isolatedCloseSlot₁ =
            focusImage-thread closeCtx closeRedex
              (focused-image outerFocused) 0F

          isolatedCloseSlot₂ =
            focusImage-thread closeCtx closeRedex
              (focused-image outerFocused) 1F

          isolatedAdjustedSlot₁ =
            threadEmbedding-transportLocalChannels
              closeChannelsSingleton (focused-image closeFocused) 0F

          isolatedAdjustedSlot₂ =
            threadEmbedding-transportLocalChannels
              closeChannelsSingleton (focused-image closeFocused) 1F

          isolatedBodySlot₁ :
            threadEmbedding (res-split-image adjustedCloseImage) 0F ≡ just j
          isolatedBodySlot₁ =
            isolatedAdjustedSlot₁ ■ isolatedCloseSlot₁ ■
            isolatedOuterSlot₁ ■ isolatedSlot₁

          isolatedBodySlot₂ :
            threadEmbedding (res-split-image adjustedCloseImage) 1F ≡ just k
          isolatedBodySlot₂ =
            isolatedAdjustedSlot₂ ■ isolatedCloseSlot₂ ■
            isolatedOuterSlot₂ ■ isolatedSlot₂

          sameLeft : closeLeft leaf ≡ j
          sameLeft =
            just-injective (sym (closeLeftSlot leaf) ■ isolatedBodySlot₁)

          sameRight : closeRight leaf ≡ k
          sameRight =
            just-injective (sym (closeRightSlot leaf) ■ isolatedBodySlot₂)

          leafHandleValue₁ :
            SoupExpression.Value
              (Translation.chanTriple
                ( SoupTerm.*
                , Soup.endpoint (closeChannel leaf) (closeSide₁ leaf)
                , SoupTerm.* ))
          leafHandleValue₁ =
            SoupExpression.V-⊗
              (SoupExpression.V-⊗ SoupExpression.V-K SoupExpression.V-`)
              SoupExpression.V-K

          leafHandleValue₂ :
            SoupExpression.Value
              (Translation.chanTriple
                ( SoupTerm.*
                , Soup.endpoint (closeChannel leaf) (closeSide₂ leaf)
                , SoupTerm.* ))
          leafHandleValue₂ =
            SoupExpression.V-⊗
              (SoupExpression.V-⊗ SoupExpression.V-K SoupExpression.V-`)
              SoupExpression.V-K

          concreteHandleValue₂ :
            SoupExpression.Value
              (Translation.chanTriple
                (SoupTerm.* , Soup.endpoint i side₂ , SoupTerm.*))
          concreteHandleValue₂ =
            subst SoupExpression.Value argEq₂
              (pairFocusValueEnv₂ ctx source₁ source₂
                (logicalChannels image) (λ ()) x₂)

          isolatedRedexEq₁ :
            closeLeftFrame leaf SoupExpression.[
              SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹
                Translation.chanTriple
                  ( SoupTerm.*
                  , Soup.endpoint (closeChannel leaf) (closeSide₁ leaf)
                  , SoupTerm.* ) ]* ≡
            F₁ SoupExpression.[
              SoupTerm.K (SoupTerm.`end Types.‼) SoupTerm.·¹
                Translation.chanTriple
                  (SoupTerm.* , Soup.endpoint i side₁ , SoupTerm.*) ]*
          isolatedRedexEq₁ =
            sym (closeSelectedLeft leaf) ■ cong (lookup ts) sameLeft ■ selected₁

          isolatedRedexEq₂ :
            closeRightFrame leaf SoupExpression.[
              SoupTerm.K (SoupTerm.`end Types.⁇) SoupTerm.·¹
                Translation.chanTriple
                  ( SoupTerm.*
                  , Soup.endpoint (closeChannel leaf) (closeSide₂ leaf)
                  , SoupTerm.* ) ]* ≡
            F₂ SoupExpression.[
              SoupTerm.K (SoupTerm.`end Types.⁇) SoupTerm.·¹
                Translation.chanTriple
                  (SoupTerm.* , Soup.endpoint i side₂ , SoupTerm.*) ]*
          isolatedRedexEq₂ =
            sym (closeSelectedRight leaf) ■ cong (lookup ts) sameRight ■ selected₂

          isolatedHandleEq₁ =
            proj₁ (proj₂ (redex-unique
              {F = closeLeftFrame leaf} {F′ = F₁}
              {c = SoupTerm.`end Types.‼} {c′ = SoupTerm.`end Types.‼}
              leafHandleValue₁ concreteHandleValue isolatedRedexEq₁))

          isolatedHandleEq₂ =
            proj₁ (proj₂ (redex-unique
              {F = closeRightFrame leaf} {F′ = F₂}
              {c = SoupTerm.`end Types.⁇} {c′ = SoupTerm.`end Types.⁇}
              leafHandleValue₂ concreteHandleValue₂ isolatedRedexEq₂))

          isolatedEndpointEq₁ =
            proj₁ (proj₂ (chanTriple-injective isolatedHandleEq₁))

          closeChannelEq : closeChannel leaf ≡ i
          closeChannelEq =
            proj₁ (endpoint-injective isolatedEndpointEq₁)

          closeFrameEq₁ =
            proj₁ (proj₂ (proj₂ (redex-unique
              {F = closeLeftFrame leaf} {F′ = F₁}
              {c = SoupTerm.`end Types.‼} {c′ = SoupTerm.`end Types.‼}
              leafHandleValue₁ concreteHandleValue isolatedRedexEq₁)))
              SoupTerm.*

          closeFrameEq₂ =
            proj₁ (proj₂ (proj₂ (redex-unique
              {F = closeRightFrame leaf} {F′ = F₂}
              {c = SoupTerm.`end Types.⁇} {c′ = SoupTerm.`end Types.⁇}
              leafHandleValue₂ concreteHandleValue₂ isolatedRedexEq₂)))
              SoupTerm.*

          exactStep =
            ascend outerFocused
              (ascend closeFocused
                (closeConfigStepAt leaf
                  closeChannelEq sameLeft sameRight
                  closeFrameEq₁ closeFrameEq₂))

          localStep : localRedex TypedReduction.─→ₚ isolatedTarget
          localStep =
            TypedReduction.R-Struct localCong
              (plug-red
                (BorrowedCF.Simulation.BackwardSoup.Locate.par-right
                  residual
                  BorrowedCF.Simulation.BackwardSoup.Locate.hole)
                (TypedReduction.R-Close {E₁ = E₁₀} {E₂ = E₂₀}))
              ≋-refl

          targetProc : Typed.Proc 0
          targetProc = plug above′ isolatedTarget
