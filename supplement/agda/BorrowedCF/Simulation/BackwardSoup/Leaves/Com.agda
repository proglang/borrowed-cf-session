-- | Backward simulation for the soup communication leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.Com where

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

import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 as ComHelpers

open import BorrowedCF.Context.Join
  using (biasedDir)
open import BorrowedCF.Processes.Congruence
  using (_/_⊢-≋_)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using ( OrientedChannel; LocalImage; OptionalThreadImage; present; omitted
        ; threadEmbedding; channelEmbedding-injective; live-thread)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ*[_]; T[_]-plugᶠ*)
open import BorrowedCF.Simulation.ForwardSoup.Local.Com
  using ( com-step
        ; comSender; comReceiver; comSenderSlot; comReceiverSlot
        ; comSendFrame; comRecvFrame; comMessage
        ; comSendTail; comRecvTail
        ; comMessageValue; comSendHandleValue; comRecvHandleValue
        ; comSelectedSend; comSelectedRecv; comConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (processCount-rename)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using ( T-value-inv; T-pair-inv; pair-arg-inversion
        ; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( closedPairEnv; plug; focusEnv; focusValueEnv; focusTyping
        ; focusChannels; ≡→≋; ≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.LocatePair
  using (located-pair; image-thread-pair; focusPairExprTyping)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( plug₂; thread₁; thread₂; fill₁; fill₂; plug-fill₁; plug-fill₂
        ; Binder₂; binder₂⇒₁; binder₂⇒₂; CanonPair; canonPair; canon-pair
        ; HeadShape₂; headShapes⇒₂)
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
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (ImpureHandleConst; pair-arg-not-var)
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (impure-redex-head′; pair-arg-redex-head′)
open import BorrowedCF.Simulation.BackwardSoup.PairPosition
  using ( pairFocusEnv₁; pairFocusEnv₂
        ; pairFocusValueEnv₁; pairFocusValueEnv₂
        ; pairFocusPairEnv₁; pairFocusPairEnv₂
        ; pairThread₁-content; pairThread₂-content
        ; same-physical-channel⇒binder₂-data)
open import BorrowedCF.Simulation.Support.Frames
  using (frame-plug₁)
open import BorrowedCF.Simulation.Support.FrameRename
  using (⋯ᶠ*-cong)
open import BorrowedCF.Simulation.Support.InvFrame
  using (value-reflect)
open import BorrowedCF.Simulation.Support.PairConfine
  using (PairConfined; comHandle; com-confine)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Fin.Patterns

private
  cong₄ :
    {A B C D E : Set} (f : A → B → C → D → E)
    {a a′ : A} {b b′ : B} {c c′ : C} {d d′ : D} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
    f a b c d ≡ f a′ b′ c′ d′
  cong₄ f refl refl refl refl = refl

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

  send-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {msg handle t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K SoupTerm.`send SoupTerm.·¹
            (msg SoupTerm.⊗ handle)
        ]* →
    t ≢ SoupTerm.*
  send-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  recv-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {handle t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K SoupTerm.`recv SoupTerm.·¹ handle
        ]* →
    t ≢ SoupTerm.*
  recv-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  pair-injective :
    {n : ℕ} {a b c d : SoupTerm.Tm n} →
    a SoupTerm.⊗ b ≡ c SoupTerm.⊗ d →
    (a ≡ c) × (b ≡ d)
  pair-injective refl = refl , refl

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

  pair-decomp :
    ∀ {N} {Γ : Context.Ctx N} {β : Context.Struct N}
      {e₁ e₂ : Source.Tm N} {T ϵ} →
    Γ ; β ⊢ e₁ Source.⊗ e₂ ∶ T ∣ ϵ →
    Σ[ Te ∈ Types.𝕋 ] Σ[ d ∈ Types.Dir ]
    Σ[ Tx ∈ Types.𝕋 ] Σ[ α₂ ∈ Context.Struct N ]
    Σ[ ϵ₂ ∈ Types.Eff ]
      (T Types.≃ (Te Types.⊗⟨ d ⟩ Tx)) ×
      (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂)
  pair-decomp (Source.T-Pair p/s {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
    _ , biasedDir p/s , _ , γ₂ , _ , Types.≃-refl , ⊢e₂
  pair-decomp (Source.T-Conv T≃ _ d) =
    let Te , dd , Tx , α₂ , ϵ₂ , Teq , ⊢e₂ = pair-decomp d in
    Te , dd , Tx , α₂ , ϵ₂ ,
    Types.≃-trans (Types.≃-sym T≃) Teq , ⊢e₂
  pair-decomp (Source.T-Weaken _ d) = pair-decomp d

  fn-send-dom :
    ∀ {N} {Γ : Context.Ctx N} {β : Context.Struct N}
      {Tᵈ U a ϵ} →
    Γ ; β ⊢ Source.K Source.`send ∶ Tᵈ Types.⟨ a ⟩→ U ∣ ϵ →
    Σ[ T ∈ Types.𝕋 ]
      ((T Types.⊗¹ Types.⟨ Types.msg Types.‼ T ⟩)
        Types.≃ Tᵈ)
  fn-send-dom (Source.T-Const (Source.`send {T = T} _)) =
    T , Types.≃-refl
  fn-send-dom (Source.T-Conv (dom≃ Types.`→ _) _ d) =
    let T , eq = fn-send-dom d in T , Types.≃-trans eq dom≃
  fn-send-dom (Source.T-Weaken _ d) = fn-send-dom d

  fn-recv-dom :
    ∀ {N} {Γ : Context.Ctx N} {β : Context.Struct N}
      {Tᵈ U a ϵ} →
    Γ ; β ⊢ Source.K Source.`recv ∶ Tᵈ Types.⟨ a ⟩→ U ∣ ϵ →
    Σ[ T ∈ Types.𝕋 ]
      (Types.⟨ Types.msg Types.⁇ T ⟩ Types.≃ Tᵈ)
  fn-recv-dom (Source.T-Const (Source.`recv {T = T} _)) =
    T , Types.≃-refl
  fn-recv-dom (Source.T-Conv (dom≃ Types.`→ _) _ d) =
    let T , eq = fn-recv-dom d in T , Types.≃-trans eq dom≃
  fn-recv-dom (Source.T-Weaken _ d) = fn-recv-dom d

  send-arg-core :
    ∀ {N} {Γ : Context.Ctx N} {α β : Context.Struct N}
      {e₁ e₂ : Source.Tm N} {Targ a U ϵ₁ ϵ₂} →
    Γ ; α ⊢ Source.K Source.`send ∶ Targ Types.⟨ a ⟩→ U ∣ ϵ₁ →
    Γ ; β ⊢ e₁ Source.⊗ e₂ ∶ Targ ∣ ϵ₂ →
    Σ[ Tᵐ ∈ Types.𝕋 ] Σ[ α₂ ∈ Context.Struct N ]
    Σ[ Tx ∈ Types.𝕋 ] Σ[ ϵ₂′ ∈ Types.Eff ]
      (Types.⟨ Types.msg Types.‼ Tᵐ ⟩ Types.≃ Tx) ×
      (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂′)
  send-arg-core ⊢fn ⊢arg
    with fn-send-dom ⊢fn | pair-decomp ⊢arg
  ... | Tᵐ , domeq | Te , d , Tx , α₂ , ϵ₂ , T≃ , ⊢e₂
    with Types.≃-trans domeq T≃
  ... | (_ Types.⊗ eq) = Tᵐ , α₂ , Tx , ϵ₂ , eq , ⊢e₂

  send-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {β : Context.Struct N}
      {e₁ e₂ : Source.Tm N} {U ϵ} →
    Γ ; β ⊢
      Source.K Source.`send Source.·¹ (e₁ Source.⊗ e₂) ∶ U ∣ ϵ →
    Σ[ Tᵐ ∈ Types.𝕋 ] Σ[ α₂ ∈ Context.Struct N ]
    Σ[ Tx ∈ Types.𝕋 ] Σ[ ϵ₂′ ∈ Types.Eff ]
      (Types.⟨ Types.msg Types.‼ Tᵐ ⟩ Types.≃ Tx) ×
      (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂′)
  send-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    send-arg-core ⊢fn ⊢arg
  send-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    send-arg-core ⊢fn ⊢arg
  send-arg-decomp (Source.T-Conv _ _ d) = send-arg-decomp d
  send-arg-decomp (Source.T-Weaken _ d) = send-arg-decomp d

  recv-arg-core :
    ∀ {N} {Γ : Context.Ctx N} {α β : Context.Struct N}
      {arg : Source.Tm N} {Targ U ϵ₁ ϵ₂ a} →
    Γ ; α ⊢ Source.K Source.`recv ∶ Targ Types.⟨ a ⟩→ U ∣ ϵ₁ →
    Γ ; β ⊢ arg ∶ Targ ∣ ϵ₂ →
    Σ[ Tᵐ ∈ Types.𝕋 ] Σ[ β′ ∈ Context.Struct N ]
    Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      (Types.⟨ Types.msg Types.⁇ Tᵐ ⟩ Types.≃ R) ×
      (Γ ; β′ ⊢ arg ∶ R ∣ ϵ′)
  recv-arg-core {β = β} ⊢fn ⊢arg
    with fn-recv-dom ⊢fn
  ... | Tᵐ , domeq = Tᵐ , β , _ , _ , domeq , ⊢arg

  recv-arg-decomp :
    ∀ {N} {Γ : Context.Ctx N} {γ : Context.Struct N}
      {arg : Source.Tm N} {U ϵ} →
    Γ ; γ ⊢ Source.K Source.`recv Source.·¹ arg ∶ U ∣ ϵ →
    Σ[ Tᵐ ∈ Types.𝕋 ] Σ[ β′ ∈ Context.Struct N ]
    Σ[ R ∈ Types.𝕋 ] Σ[ ϵ′ ∈ Types.Eff ]
      (Types.⟨ Types.msg Types.⁇ Tᵐ ⟩ Types.≃ R) ×
      (Γ ; β′ ⊢ arg ∶ R ∣ ϵ′)
  recv-arg-decomp (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    recv-arg-core ⊢fn ⊢arg
  recv-arg-decomp (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    recv-arg-core ⊢fn ⊢arg
  recv-arg-decomp (Source.T-Conv _ _ d) = recv-arg-decomp d
  recv-arg-decomp (Source.T-Weaken _ d) = recv-arg-decomp d

  opposite-apart :
    ∀ {side₁ side₂} → SoupReduction.Opposite side₁ side₂ → side₁ ≢ side₂
  opposite-apart SoupReduction.left-right ()
  opposite-apart SoupReduction.right-left ()

------------------------------------------------------------------------
-- A strict soup communication reflects to a typed communication.

com-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : SoupExpression.Frame* (2 *ℕ n))
  {e e₁′ e₂′ : Soup.Thread n} →
  j ≢ k →
  SoupReduction.Opposite side₁ side₂ →
  SoupReduction.is-open cs i →
  SoupExpression.Value e →
  lookup ts j ≡
    F₁ SoupExpression.[
      SoupTerm.K SoupTerm.`send SoupTerm.·¹
        (e SoupTerm.⊗
          Translation.chanTriple
            (SoupTerm.* , Soup.endpoint i side₁ , e₁′)) ]* →
  lookup ts k ≡
    F₂ SoupExpression.[
      SoupTerm.K SoupTerm.`recv SoupTerm.·¹
        Translation.chanTriple
          (SoupTerm.* , Soup.endpoint i side₂ , e₂′) ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs
        (SoupReduction.replaceTwo ts
          j (F₁ SoupExpression.[ SoupTerm.* ]*)
          k (F₂ SoupExpression.[ e ]*)))
com-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j k i side₁ side₂ F₁ F₂ {e = e} {e₁′ = e₁′} {e₂′ = e₂′}
  slotsApart opposite openChannel messageValue
  selected₁ selected₂ ⊢P image
  with image-thread-pair image j k slotsApart
         (send-redex-not-unit {F = F₁} selected₁)
         (recv-redex-not-unit {F = F₂} selected₂)
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
         F₁ Source.`send Types.𝟙
         (e SoupTerm.⊗
          Translation.chanTriple
            (SoupTerm.* , Soup.endpoint i side₁ , e₁′))
         (sym (pairThread₁-content ctx source₁ source₂
                 (logicalChannels image) (λ ()))
          ■ sym content₁ ■ selected₁)
... | E₁ , arg₁ , sourceEq₁ , frameEq₁ , argEq₁
  with SourceReduction.⊢[]*⁻¹ E₁
         (Source.K Source.`send Source.·¹ arg₁)
         (subst (λ z → Γ₁ ; γ₁ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₁ ⊢source₁)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₁ , ⊢app₁
  with pair-arg-inversion arg₁
         (pairFocusEnv₁ ctx source₁ source₂ (logicalChannels image) (λ ()))
         (pair-arg-not-var Γ₁-S ⊢app₁)
         argEq₁
... | messageSource , handleArg , refl , sourceMessageEq , handleEq₁
  with send-arg-decomp ⊢app₁
... | Tᵐ₁ , β₁ , R₁ , ϵ₁ , handleType₁ , ⊢handle₁
  with argument-var ⊢handle₁ handleType₁ handleEq₁
... | x₁ , refl
  with plug-inversion-K source₂
         (pairFocusEnv₂ ctx source₁ source₂ (logicalChannels image) (λ ()))
         (pairFocusValueEnv₂ ctx source₁ source₂
           (logicalChannels image) (λ ()))
         (pairFocusPairEnv₂ ctx source₁ source₂
           (logicalChannels image) closedPairEnv)
         F₂ Source.`recv Types.𝟙
         (Translation.chanTriple
           (SoupTerm.* , Soup.endpoint i side₂ , e₂′))
         (sym (pairThread₂-content ctx source₁ source₂
                 (logicalChannels image) (λ ()))
          ■ sym content₂ ■ selected₂)
... | E₂ , arg₂ , sourceEq₂ , frameEq₂ , argEq₂
  with SourceReduction.⊢[]*⁻¹ E₂
         (Source.K Source.`recv Source.·¹ arg₂)
         (subst (λ z → Γ₂ ; γ₂ ⊢ z ∶ Types.`⊤ ∣ Types.𝕀)
           sourceEq₂ ⊢source₂)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E₂ , ⊢app₂
  with recv-arg-decomp ⊢app₂
... | Tᵐ₂ , β₂ , R₂ , ϵ₂ , handleType₂ , ⊢arg₂
  with argument-var ⊢arg₂ handleType₂ argEq₂
... | x₂ , refl
  with same-physical-channel⇒binder₂-data
         ctx source₁ source₂ (logicalChannels image)
         (channelEmbedding-injective (localImage image)) x₁ x₂
         (opposite-apart opposite) handleEq₁ argEq₂
... | bnd , localsApart , logical , physicalEq , binderContent = finish
  where
  redex₁ : Source.Tm _
  redex₁ =
    E₁ SourceReduction.[
      Source.K Source.`send Source.·¹
        (messageSource Source.⊗ (Source.` x₁)) ]*

  redex₂ : Source.Tm _
  redex₂ =
    E₂ SourceReduction.[
      Source.K Source.`recv Source.·¹ (Source.` x₂) ]*

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
    pair-arg-redex-head′
      {E = E₁} {c = Source.`send} {w = messageSource} {x = x₁}
      bnd₁ ⊢redex₁ ImpureHandleConst.`send

  head₂ =
    impure-redex-head′
      {E = E₂} {c = Source.`recv} {x = x₂}
      bnd₂ ⊢redex₂ ImpureHandleConst.`recv

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

  sourceMessageValue : SourceReduction.Value messageSource
  sourceMessageValue =
    T-value-inv messageSource
      (pairFocusEnv₁ ctx source₁ source₂ (logicalChannels image) (λ ()))
      (pairFocusValueEnv₁ ctx source₁ source₂
        (logicalChannels image) (λ ()))
      (subst SoupExpression.Value (sym sourceMessageEq) messageValue)

  finish :
    Σ[ P′ ∈ Typed.Proc 0 ]
      (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
        TypedReduction.─→ₚ P′) ×
      GlobalImage P′
        (Soup.config cs
          (SoupReduction.replaceTwo ts
            j (F₁ SoupExpression.[ SoupTerm.* ]*)
            k (F₂ SoupExpression.[ e ]*)))
  finish with canon
  ... | canonPair b₁′ b₂′ B₁′ B₂′ above′ ρ₁ ρ₂ resid
          ≋canon x₁eq x₂eq tracks₁ tracks₂ = result
    where
    handle₂ = comHandle b₁′ b₂′ B₁′ B₂′
    wkρ = Source.wkₚ (b₁′ + sum B₁′) (b₂′ + sum B₂′)

    ownerFrame₁ = E₁ SourceReduction.⋯ᶠ* ρ₁
    ownerFrame₂ = E₂ SourceReduction.⋯ᶠ* ρ₂

    sentRenamed : Source.Tm _
    sentRenamed = messageSource Source.⋯ ρ₁

    sentRenamedValue : SourceReduction.Value sentRenamed
    sentRenamedValue = sourceMessageValue SourceReduction.⋯ᵛ ρ₁

    ownerApp₁ =
      Source.K Source.`send Source.·¹
        (sentRenamed Source.⊗ (Source.` 0F))

    ownerApp₂ =
      Source.K Source.`recv Source.·¹ (Source.` handle₂)

    renamedTermEq₁ :
      redex₁ Source.⋯ ρ₁ ≡
      ownerFrame₁ SourceReduction.[ ownerApp₁ ]*
    renamedTermEq₁ =
      plug*-⋯ᵣ E₁
        (Source.K Source.`send Source.·¹
          (messageSource Source.⊗ (Source.` x₁))) ρ₁
      ■ cong
          (λ z → ownerFrame₁ SourceReduction.[
            Source.K Source.`send Source.·¹
              (sentRenamed Source.⊗ (Source.` z)) ]*)
          x₁eq

    renamedTermEq₂ :
      redex₂ Source.⋯ ρ₂ ≡
      ownerFrame₂ SourceReduction.[ ownerApp₂ ]*
    renamedTermEq₂ =
      plug*-⋯ᵣ E₂
        (Source.K Source.`recv Source.·¹ (Source.` x₂)) ρ₂
      ■ cong
          (λ z → ownerFrame₂ SourceReduction.[
            Source.K Source.`recv Source.·¹ (Source.` z) ]*)
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

    canonicalTyping : [] ; Context.[] ⊢ₚ canonicalRedex
    canonicalTyping = AllV.[] / ⊢P ⊢-≋ redex≋

    focusedTyping =
      focusTyping above′ localRedex AllV.[] canonicalTyping

    localGamma = proj₁ focusedTyping
    localStruct = proj₁ (proj₂ focusedTyping)
    localChanCx = proj₁ (proj₂ (proj₂ focusedTyping))
    localTyping = proj₂ (proj₂ (proj₂ focusedTyping))

    abstract
      normalizedTyping :
        localGamma ; localStruct ⊢ₚ normalizedLocal
      normalizedTyping =
        subst (λ Z → localGamma ; localStruct ⊢ₚ Z) localEq localTyping

      confined :
        PairConfined b₁′ b₂′ B₁′ B₂′
          ownerFrame₁ ownerFrame₂ sentRenamed resid
      confined =
        com-confine localChanCx
          {E₁ = ownerFrame₁} {E₂ = ownerFrame₂}
          {v = sentRenamed} {P = resid}
          normalizedTyping

    result :
      Σ[ P′ ∈ Typed.Proc 0 ]
        (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
          TypedReduction.─→ₚ P′) ×
        GlobalImage P′
          (Soup.config cs
            (SoupReduction.replaceTwo ts
              j (F₁ SoupExpression.[ SoupTerm.* ]*)
              k (F₂ SoupExpression.[ e ]*)))
    result
      with confined
    ... | E₁₀ , E₁eq , E₂₀ , E₂eq
        , v₀ , veq , residual , residualEq =
      finishConfined Vv₀
      where
      Vv₀ : SourceReduction.Value v₀
      Vv₀ =
        value-reflect wkρ v₀
          (subst SourceReduction.Value veq sentRenamedValue)

      comRedex : Typed.Proc _
      comRedex =
        Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
          ((Typed.⟪
              E₁₀ SourceReduction.⋯ᶠ* wkρ
                SourceReduction.[
                  Source.K Source.`send Source.·¹
                    ((v₀ Source.⋯ wkρ) Source.⊗ (Source.` 0F)) ]*
            ⟫ Typed.∥
            Typed.⟪
              E₂₀ SourceReduction.⋯ᶠ* wkρ
                SourceReduction.[
                  Source.K Source.`recv Source.·¹
                    (Source.` handle₂) ]*
            ⟫)
           Typed.∥ (residual Typed.⋯ₚ wkρ))

      factorEq : normalizedLocal ≡ comRedex
      factorEq =
        cong₄
          (λ X Y Z Q →
            Typed.ν (suc b₁′ ∷ B₁′) (suc b₂′ ∷ B₂′)
              ((Typed.⟪ X SourceReduction.[
                  Source.K Source.`send Source.·¹
                    (Z Source.⊗ (Source.` 0F)) ]* ⟫ Typed.∥
                Typed.⟪ Y SourceReduction.[
                  Source.K Source.`recv Source.·¹
                    (Source.` handle₂) ]* ⟫)
               Typed.∥ Q))
          E₁eq E₂eq veq residualEq

      comTyping :
        localGamma ; localStruct ⊢ₚ comRedex
      comTyping =
        subst (λ Z → localGamma ; localStruct ⊢ₚ Z) factorEq
          normalizedTyping

      abstract
        com-widths :
          SourceReduction.Value v₀ →
          localGamma ; localStruct ⊢ₚ comRedex →
          Σ[ bh₁ ∈ ℕ ] Σ[ bh₂ ∈ ℕ ]
            (b₁′ ≡ suc bh₁) × (b₂′ ≡ suc bh₂)
        com-widths Vv typing
          with ComHelpers.com-head≥1
                 {Γ = localGamma} {γ = localStruct}
                 {b₁ = b₁′} {b₂ = b₂′} {B₁ = B₁′} {B₂ = B₂′}
                 {e = v₀} {E₁ = E₁₀} {E₂ = E₂₀} {P = residual}
                 Vv typing
             | ComHelpers.com-head≥2
                 {Γ = localGamma} {γ = localStruct}
                 {b₁ = b₁′} {b₂ = b₂′} {B₁ = B₁′} {B₂ = B₂′}
                 {e = v₀} {E₁ = E₁₀} {E₂ = E₂₀} {P = residual}
                 Vv typing
        ... | bh₁ , eq₁ | bh₂ , eq₂ = bh₁ , bh₂ , eq₁ , eq₂

      finishConfined :
        SourceReduction.Value v₀ →
        Σ[ P′ ∈ Typed.Proc 0 ]
          (plug₂ ctx Typed.⟪ source₁ ⟫ Typed.⟪ source₂ ⟫
            TypedReduction.─→ₚ P′) ×
          GlobalImage P′
            (Soup.config cs
              (SoupReduction.replaceTwo ts
                j (F₁ SoupExpression.[ SoupTerm.* ]*)
                k (F₂ SoupExpression.[ e ]*)))
      finishConfined Vv₀′ with com-widths Vv₀′ comTyping
      ... | bh₁ , bh₂ , refl , refl =
        targetProc
        , TypedReduction.R-Struct redex≋
            (plug-red above′ localStep) ≋-refl
        , closeConfigStep exactStep
        where
        localCong : localRedex Typed.≋ comRedex
        localCong = ≡→≋ localEq ◅◅ ≡→≋ factorEq

        allCong : P Typed.≋ plug above′ comRedex
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

        localTrack₁ =
          tracks-◅◅
            (tracks-≡→≋ℕ localEq 0F refl)
            (tracks-≡→≋ℕ factorEq 0F refl)
        localTrack₂ =
          tracks-◅◅
            (tracks-≡→≋ℕ localEq 1F refl)
            (tracks-≡→≋ℕ factorEq 1F refl)

        allTrack₁ =
          tracks-◅◅ redexTracks₁ (tracks-≋-plug above′ localTrack₁)
        allTrack₂ =
          tracks-◅◅ redexTracks₂ (tracks-≋-plug above′ localTrack₂)

        comGlobal = transportGlobalImage allCong image
        comImage = localImage comGlobal

        comChannels :
          Vec (OrientedChannel n) (Translation.channelCount comRedex)
        comChannels =
          focusChannels above′ comRedex (logicalChannels comGlobal)

        comChannel = V.head comChannels
        comBodyChannels = V.tail comChannels

        comChannelsSplit :
          comChannels ≡ comChannel ∷ comBodyChannels
        comChannelsSplit = sym (cons-head-tail comChannels)

        focused = focusImage above′ comRedex comImage

        adjustedImage :
          LocalImage comRedex
            (comChannel ∷ comBodyChannels)
            (focusEnv above′ comRedex (logicalChannels comGlobal) (λ ()))
            (focusedAmbientChannel focused) (focusedAmbientThread focused)
            (Soup.config cs ts)
        adjustedImage =
          transportLocalChannels comChannelsSplit (focused-image focused)

        bodyImage = res-split-image adjustedImage
        ownersImage = par-split-left bodyImage

        comSlot₁ =
          transportGlobalSlot allCong image allTrack₁ embedded₁
        comSlot₂ =
          transportGlobalSlot allCong image allTrack₂ embedded₂

        focusedSlot₁ =
          focusImage-thread above′ comRedex comImage 0F
        focusedSlot₂ =
          focusImage-thread above′ comRedex comImage 1F

        adjustedSlot₁ =
          threadEmbedding-transportLocalChannels comChannelsSplit
            (focused-image focused) 0F
        adjustedSlot₂ =
          threadEmbedding-transportLocalChannels comChannelsSplit
            (focused-image focused) 1F

        ownersSlot₁ : threadEmbedding ownersImage 0F ≡ just j
        ownersSlot₁ = adjustedSlot₁ ■ focusedSlot₁ ■ comSlot₁

        ownersSlot₂ : threadEmbedding ownersImage 1F ≡ just k
        ownersSlot₂ = adjustedSlot₂ ■ focusedSlot₂ ■ comSlot₂

        localValueEnv =
          focusValueEnv above′ comRedex
            (logicalChannels comGlobal) (λ ())

        leaf =
          com-step
            {b₁ = bh₁} {b₂ = bh₂} {B₁ = B₁′} {B₂ = B₂′}
            {P = residual} {E₁ = E₁₀} {E₂ = E₂₀} {e = v₀}
            {channel = comChannel} {bodyChannels = comBodyChannels}
            adjustedImage localValueEnv Vv₀′

        sameSender : comSender leaf ≡ j
        sameSender =
          just-injective (sym (comSenderSlot leaf) ■ ownersSlot₁)

        sameReceiver : comReceiver leaf ≡ k
        sameReceiver =
          just-injective (sym (comReceiverSlot leaf) ■ ownersSlot₂)

        concreteHandle₁ =
          Translation.chanTriple
            (SoupTerm.* , Soup.endpoint i side₁ , e₁′)

        concreteHandle₂ =
          Translation.chanTriple
            (SoupTerm.* , Soup.endpoint i side₂ , e₂′)

        concreteHandleValue₁ : SoupExpression.Value concreteHandle₁
        concreteHandleValue₁ =
          subst SoupExpression.Value handleEq₁
            (pairFocusValueEnv₁ ctx source₁ source₂
              (logicalChannels image) (λ ()) x₁)

        concreteHandleValue₂ : SoupExpression.Value concreteHandle₂
        concreteHandleValue₂ =
          subst SoupExpression.Value argEq₂
            (pairFocusValueEnv₂ ctx source₁ source₂
              (logicalChannels image) (λ ()) x₂)

        leafSendArgValue :
          SoupExpression.Value
            (comMessage leaf SoupTerm.⊗
              Translation.chanTriple
                ( SoupTerm.*
                , Soup.endpoint
                    (BorrowedCF.Simulation.ForwardSoup.Local.Com.comChannel leaf)
                    (BorrowedCF.Simulation.ForwardSoup.Local.Com.comSide₁ leaf)
                , comSendTail leaf ))
        leafSendArgValue =
          SoupExpression.V-⊗ (comMessageValue leaf) (comSendHandleValue leaf)

        concreteSendArgValue :
          SoupExpression.Value (e SoupTerm.⊗ concreteHandle₁)
        concreteSendArgValue =
          SoupExpression.V-⊗ messageValue concreteHandleValue₁

        leafRedexEq₁ =
          sym (comSelectedSend leaf) ■
          cong (lookup ts) sameSender ■ selected₁

        unique₁ =
          redex-unique
            {F = comSendFrame leaf} {F′ = F₁}
            {c = SoupTerm.`send} {c′ = SoupTerm.`send}
            leafSendArgValue concreteSendArgValue leafRedexEq₁

        sendArgEq = proj₁ (proj₂ unique₁)

        sameMessage : comMessage leaf ≡ e
        sameMessage = proj₁ (pair-injective sendArgEq)

        sendFrameUnitEq :
          comSendFrame leaf SoupExpression.[ SoupTerm.* ]* ≡
          F₁ SoupExpression.[ SoupTerm.* ]*
        sendFrameUnitEq =
          proj₁ (proj₂ (proj₂ unique₁)) SoupTerm.*

        leafRedexEq₂ =
          sym (comSelectedRecv leaf) ■
          cong (lookup ts) sameReceiver ■ selected₂

        unique₂ =
          redex-unique
            {F = comRecvFrame leaf} {F′ = F₂}
            {c = SoupTerm.`recv} {c′ = SoupTerm.`recv}
            (comRecvHandleValue leaf) concreteHandleValue₂ leafRedexEq₂

        recvFrameMessageEq :
          comRecvFrame leaf SoupExpression.[ comMessage leaf ]* ≡
          F₂ SoupExpression.[ e ]*
        recvFrameMessageEq =
          cong (SoupExpression._[_]* (comRecvFrame leaf)) sameMessage
          ■ proj₁ (proj₂ (proj₂ unique₂)) e

        exactStep =
          ascend focused
            (comConfigStepAt leaf
              sameSender sameReceiver sendFrameUnitEq recvFrameMessageEq)

        localTarget : Typed.Proc _
        localTarget =
          Typed.ν (suc bh₁ ∷ B₁′) (suc bh₂ ∷ B₂′)
            ((Typed.⟪ E₁₀ SourceReduction.[ Source.* ]* ⟫ Typed.∥
              Typed.⟪ E₂₀ SourceReduction.[ v₀ ]* ⟫)
             Typed.∥ residual)

        localStep : localRedex TypedReduction.─→ₚ localTarget
        localStep =
          TypedReduction.R-Struct localCong
            (TypedReduction.R-Com
              {b₁ = suc bh₁} {b₂ = suc bh₂}
              {B₂ = B₂′} {P = residual} {E₁ = E₁₀} {E₂ = E₂₀}
              Vv₀′)
            ≋-refl

        targetProc : Typed.Proc 0
        targetProc = plug above′ localTarget
