-- | Backward simulation for the soup left-split leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.LSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)
import Data.Nat.Properties as NatP
import Data.Vec.Relation.Unary.All as AllV
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Context.Substitution as ContextSub
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

open import BorrowedCF.Simulation.ForwardSoup.Local.LSplit
  using ( lsplit-step; lsplitThread; lsplitSlotEq; lsplitChannel; lsplitSide
        ; lsplitOpen; lsplitFrame; lsplitHandleLeft; lsplitHandleEnd
        ; lsplitHandleRight; lsplitHandleValue; lsplitSelected; lsplitReplacement
        ; lsplitReplacement≡; lsplitConfigStepAt)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (LocalImage; OrientedChannel; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Struct
  using (≋-image)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using ( CanonSplit; SplitShape; canon-lsplit
        ; split-l; split-r; splitIx
        ; tracks-≡→≋ℕ; threadInContext-ℕ
        )
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-pair-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusTyping; focusChannels; closedPairEnv; plug
        ; threadInContext; ≡→≋)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using ( Binder; resolve; sideOf; SideOf; inl; inr
        ; GroupOf; head-group; next-group; groupOf
        ; handle-value-var)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.TracksImage
  using (≋-image-slot)
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using (Tracks; tracks-◅◅)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective; endpoint-injective)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open import BorrowedCF.Simulation.Support.InvFrame
  using (fn-lsplit-dom)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Fin.Patterns

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  chanTriple-cong :
    {n : ℕ} {e₁ e₁′ e₂ e₂′ : SoupTerm.Tm n} {c c′ : 𝔽 n} →
    e₁ ≡ e₁′ →
    c ≡ c′ →
    e₂ ≡ e₂′ →
    Translation.chanTriple (e₁ , c , e₂) ≡
    Translation.chanTriple (e₁′ , c′ , e₂′)
  chanTriple-cong refl refl refl = refl

  split-replacement-cong :
    {n : ℕ} {e₁ e₁′ e₂ e₂′ : SoupTerm.Tm n} {c c′ : 𝔽 n} →
    Translation.chanTriple (e₁ , c , e₂) ≡
      Translation.chanTriple (e₁′ , c′ , e₂′) →
    (Translation.chanTriple (e₁ , c , SoupTerm.*) SoupTerm.⊗
     Translation.chanTriple (SoupTerm.* , c , e₂)) ≡
    (Translation.chanTriple (e₁′ , c′ , SoupTerm.*) SoupTerm.⊗
     Translation.chanTriple (SoupTerm.* , c′ , e₂′))
  split-replacement-cong equal
    with chanTriple-injective equal
  ... | leftEq , endEq , rightEq =
    cong₂ SoupTerm._⊗_
      (chanTriple-cong leftEq endEq refl)
      (chanTriple-cong refl endEq rightEq)

  lsplit-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {s : Types.𝕊 0} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K (SoupTerm.`lsplit s) SoupTerm.·¹ v
        ]* →
    t ≢ SoupTerm.*
  lsplit-redex-not-unit {F = F} selected unitEq =
    plug-app-not-value F
      (subst SoupExpression.Value
        (sym (sym selected ■ unitEq))
        SoupExpression.V-K)

  ⟨⟩≄⊗ :
    ∀ {s T U d} → ¬ (Types.⟨ s ⟩ Types.≃ (T Types.⊗⟨ d ⟩ U))
  ⟨⟩≄⊗ ()

  pair-not-channel :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {a b : Source.Tm k} {R ϵ s} →
    Γ ; γ ⊢ a Source.⊗ b ∶ R ∣ ϵ →
    Types.⟨ s ⟩ Types.≃ R →
    ⊥
  pair-not-channel typed eq
    with Source.inv-⊗ typed
  ... | _ , _ , _ , _ , _ , _ , _ , _ , pairEq , _ =
    ⟨⟩≄⊗ (Types.≃-trans eq (Types.≃-sym pairEq))

  lsplit-arg-chan :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {s : Types.𝕊 0} {arg : Source.Tm k} {T ϵ} →
    Γ ; γ ⊢ Source.K (Source.`lsplit s) Source.·¹ arg ∶ T ∣ ϵ →
    Σ[ s′ ∈ Types.𝕊 0 ] Σ[ β ∈ Context.Struct k ]
    Σ[ R ∈ Types.𝕋 ] Σ[ ϵ₂ ∈ Types.Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) ×
      (Types.⟨ s Types.; s′ ⟩ Types.≃ R)
  lsplit-arg-chan (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    let s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
  lsplit-arg-chan (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    let s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
  lsplit-arg-chan (Source.T-Conv _ _ d) = lsplit-arg-chan d
  lsplit-arg-chan (Source.T-Weaken _ d) = lsplit-arg-chan d

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

  fin-split :
    (b : ℕ) (z : 𝔽 b) →
    Σ[ rest ∈ ℕ ] b ≡ Fin.toℕ z + suc rest
  fin-split b z =
    b Nat.∸ suc q
    , sym (NatP.+-suc q (b Nat.∸ suc q)
           ■ NatP.m+[n∸m]≡n (Fin.toℕ<n z))
    where
    q = Fin.toℕ z

  splitIx-toℕ :
    (G₁ G₂ : Typed.BindGroup) (q b : ℕ) →
    Fin.toℕ (splitIx G₁ G₂ q b) ≡ sum G₁ + q
  splitIx-toℕ G₁ G₂ q b =
    Fin.toℕ-cast
      (sym (sum-++ G₁ ((q + suc b) ∷ G₂)))
      (sum G₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum G₂))
    ■ Fin.toℕ-↑ʳ (sum G₁) ((q ↑ʳ 0F) ↑ˡ sum G₂)
    ■ cong (sum G₁ +_)
        (Fin.toℕ-↑ˡ (q ↑ʳ 0F) (sum G₂)
         ■ Fin.toℕ-↑ʳ q 0F
         ■ NatP.+-identityʳ q)

  splitIx-cons :
    (h : ℕ) (G₁ G₂ : Typed.BindGroup) (q b : ℕ) →
    splitIx (h ∷ G₁) G₂ q b ≡ h ↑ʳ splitIx G₁ G₂ q b
  splitIx-cons h G₁ G₂ q b =
    Fin.toℕ-injective
      ( splitIx-toℕ (h ∷ G₁) G₂ q b
      ■ NatP.+-assoc h (sum G₁) q
      ■ cong (h +_) (sym (splitIx-toℕ G₁ G₂ q b))
      ■ sym (Fin.toℕ-↑ʳ h (splitIx G₁ G₂ q b))
      )

  head-split-left-suc :
    {b : ℕ} (B C : Typed.BindGroup) (j : 𝔽 b) (rest : ℕ) →
    b ≡ Fin.toℕ j + suc rest →
    SplitShape (suc b ∷ B) C ((suc j ↑ˡ sum B) ↑ˡ sum C)
  head-split-left-suc B C j rest bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape (suc z ∷ B) C ((suc j′ ↑ˡ sum B) ↑ˡ sum C))
      (sym bEq)
      build
      j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) →
      Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape
        (suc (Fin.toℕ j + suc rest) ∷ B) C
        ((suc j′ ↑ˡ sum B) ↑ˡ sum C)
    build j′ j′Eq =
      subst
        (λ ix →
          SplitShape ((suc (Fin.toℕ j) + suc rest) ∷ B) C ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ˡ (splitIx [] B (suc (Fin.toℕ j)) rest) (sum C)
          ■ splitIx-toℕ [] B (suc (Fin.toℕ j)) rest
          ■ cong suc (sym j′Eq)
          ■ sym
              (Fin.toℕ-↑ˡ (suc j′ ↑ˡ sum B) (sum C)
               ■ Fin.toℕ-↑ˡ (suc j′) (sum B))))
        (split-l [] B (suc (Fin.toℕ j)) rest C)

  head-split-right-suc :
    {b : ℕ} (C B : Typed.BindGroup) (j : 𝔽 b) (rest : ℕ) →
    b ≡ Fin.toℕ j + suc rest →
    SplitShape C (suc b ∷ B) (sum C ↑ʳ (suc j ↑ˡ sum B))
  head-split-right-suc C B j rest bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape C (suc z ∷ B) (sum C ↑ʳ (suc j′ ↑ˡ sum B)))
      (sym bEq)
      build
      j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) →
      Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape C
        (suc (Fin.toℕ j + suc rest) ∷ B)
        (sum C ↑ʳ (suc j′ ↑ˡ sum B))
    build j′ j′Eq =
      subst
        (λ ix →
          SplitShape C ((suc (Fin.toℕ j) + suc rest) ∷ B) ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ʳ (sum C) (splitIx [] B (suc (Fin.toℕ j)) rest)
          ■ cong (sum C +_)
              (splitIx-toℕ [] B (suc (Fin.toℕ j)) rest)
          ■ cong (sum C +_) (cong suc (sym j′Eq))
          ■ sym
              (Fin.toℕ-↑ʳ (sum C) (suc j′ ↑ˡ sum B)
               ■ cong (sum C +_) (Fin.toℕ-↑ˡ (suc j′) (sum B)))))
        (split-r C [] B (suc (Fin.toℕ j)) rest)

  head-split-left :
    (b : ℕ) (B C : Typed.BindGroup) (j : 𝔽 b) →
    SplitShape (b ∷ B) C ((j ↑ˡ sum B) ↑ˡ sum C)
  head-split-left zero B C ()
  head-split-left (suc b) B C zero = split-l [] B zero b C
  head-split-left (suc b) B C (suc j)
    with fin-split b j
  ... | rest , bEq = head-split-left-suc B C j rest bEq

  head-split-right :
    (C : Typed.BindGroup) (b : ℕ) (B : Typed.BindGroup) (j : 𝔽 b) →
    SplitShape C (b ∷ B) (sum C ↑ʳ (j ↑ˡ sum B))
  head-split-right C zero B ()
  head-split-right C (suc b) B zero = split-r C [] B zero b
  head-split-right C (suc b) B (suc j)
    with fin-split b j
  ... | rest , bEq = head-split-right-suc C B j rest bEq

  transportSplitShapeˡ :
    {B B′ C : Typed.BindGroup}
    {i : 𝔽 (sum B + sum C)}
    {i′ : 𝔽 (sum B′ + sum C)} →
    B ≡ B′ →
    Fin.toℕ i′ ≡ Fin.toℕ i →
    SplitShape B C i →
    SplitShape B′ C i′
  transportSplitShapeˡ refl same sh =
    subst (λ ix → SplitShape _ _ ix)
      (Fin.toℕ-injective (sym same))
      sh

  transportSplitShapeʳ :
    {B B′ C : Typed.BindGroup}
    {i : 𝔽 (sum C + sum B)}
    {i′ : 𝔽 (sum C + sum B′)} →
    B ≡ B′ →
    Fin.toℕ i′ ≡ Fin.toℕ i →
    SplitShape C B i →
    SplitShape C B′ i′
  transportSplitShapeʳ refl same sh =
    subst (λ ix → SplitShape _ _ ix)
      (Fin.toℕ-injective (sym same))
      sh

  leftPrefixIx :
    (G₀ B C : Typed.BindGroup) →
    𝔽 (sum B) →
    𝔽 (sum (G₀ ++ B) + sum C)
  leftPrefixIx G₀ B C i =
    Fin.cast (cong (_+ sum C) (sym (sum-++ G₀ B)))
      ((sum G₀ ↑ʳ i) ↑ˡ sum C)

  leftPrefixIx-toℕ :
    (G₀ B C : Typed.BindGroup) (i : 𝔽 (sum B)) →
    Fin.toℕ (leftPrefixIx G₀ B C i) ≡ sum G₀ + Fin.toℕ i
  leftPrefixIx-toℕ G₀ B C i =
    Fin.toℕ-cast
      (cong (_+ sum C) (sym (sum-++ G₀ B)))
      ((sum G₀ ↑ʳ i) ↑ˡ sum C)
    ■ Fin.toℕ-↑ˡ (sum G₀ ↑ʳ i) (sum C)
    ■ Fin.toℕ-↑ʳ (sum G₀) i

  rightPrefixIx :
    (G₀ B C : Typed.BindGroup) →
    𝔽 (sum B) →
    𝔽 (sum C + sum (G₀ ++ B))
  rightPrefixIx G₀ B C i =
    Fin.cast (cong (sum C +_) (sym (sum-++ G₀ B)))
      (sum C ↑ʳ (sum G₀ ↑ʳ i))

  rightPrefixIx-toℕ :
    (G₀ B C : Typed.BindGroup) (i : 𝔽 (sum B)) →
    Fin.toℕ (rightPrefixIx G₀ B C i) ≡
    sum C + (sum G₀ + Fin.toℕ i)
  rightPrefixIx-toℕ G₀ B C i =
    Fin.toℕ-cast
      (cong (sum C +_) (sym (sum-++ G₀ B)))
      (sum C ↑ʳ (sum G₀ ↑ʳ i))
    ■ Fin.toℕ-↑ʳ (sum C) (sum G₀ ↑ʳ i)
    ■ cong (sum C +_) (Fin.toℕ-↑ʳ (sum G₀) i)

  head-split-left-prefix :
    (G₀ B C : Typed.BindGroup) {b : ℕ} (j : 𝔽 b) →
    SplitShape (G₀ ++ (b ∷ B)) C
      (leftPrefixIx G₀ (b ∷ B) C (j ↑ˡ sum B))
  head-split-left-prefix G₀ B C {b = b} j
    with fin-split b j
  ... | rest , bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape (G₀ ++ (z ∷ B)) C
          (leftPrefixIx G₀ (z ∷ B) C (j′ ↑ˡ sum B)))
      (sym bEq)
      build
      j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) →
      Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape (G₀ ++ ((Fin.toℕ j + suc rest) ∷ B)) C
        (leftPrefixIx G₀ ((Fin.toℕ j + suc rest) ∷ B) C
          (j′ ↑ˡ sum B))
    build j′ j′Eq =
      subst
        (λ ix →
          SplitShape (G₀ ++ ((Fin.toℕ j + suc rest) ∷ B)) C ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ˡ (splitIx G₀ B (Fin.toℕ j) rest) (sum C)
          ■ splitIx-toℕ G₀ B (Fin.toℕ j) rest
          ■ cong (sum G₀ +_) (sym j′Eq)
          ■ sym
              (leftPrefixIx-toℕ
                G₀ ((Fin.toℕ j + suc rest) ∷ B) C
                (j′ ↑ˡ sum B)
               ■ cong (sum G₀ +_) (Fin.toℕ-↑ˡ j′ (sum B)))))
        (split-l G₀ B (Fin.toℕ j) rest C)

  head-split-right-prefix :
    (G₀ B C : Typed.BindGroup) {b : ℕ} (j : 𝔽 b) →
    SplitShape C (G₀ ++ (b ∷ B))
      (rightPrefixIx G₀ (b ∷ B) C (j ↑ˡ sum B))
  head-split-right-prefix G₀ B C {b = b} j
    with fin-split b j
  ... | rest , bEq =
    subst
      (λ z →
        (j′ : 𝔽 z) → Fin.toℕ j′ ≡ Fin.toℕ j →
        SplitShape C (G₀ ++ (z ∷ B))
          (rightPrefixIx G₀ (z ∷ B) C (j′ ↑ˡ sum B)))
      (sym bEq)
      build
      j refl
    where
    build :
      (j′ : 𝔽 (Fin.toℕ j + suc rest)) →
      Fin.toℕ j′ ≡ Fin.toℕ j →
      SplitShape C (G₀ ++ ((Fin.toℕ j + suc rest) ∷ B))
        (rightPrefixIx G₀ ((Fin.toℕ j + suc rest) ∷ B) C
          (j′ ↑ˡ sum B))
    build j′ j′Eq =
      subst
        (λ ix →
          SplitShape C (G₀ ++ ((Fin.toℕ j + suc rest) ∷ B)) ix)
        (Fin.toℕ-injective
          ( Fin.toℕ-↑ʳ (sum C) (splitIx G₀ B (Fin.toℕ j) rest)
          ■ cong (sum C +_)
              (splitIx-toℕ G₀ B (Fin.toℕ j) rest)
          ■ cong (sum C +_)
              (cong (sum G₀ +_) (sym j′Eq))
          ■ sym
              (rightPrefixIx-toℕ
                G₀ ((Fin.toℕ j + suc rest) ∷ B) C
                (j′ ↑ˡ sum B)
               ■ cong (sum C +_)
                   (cong (sum G₀ +_)
                     (Fin.toℕ-↑ˡ j′ (sum B))))))
        (split-r C G₀ B (Fin.toℕ j) rest)

  group-split-left-prefix :
    (G₀ B C : Typed.BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i →
    SplitShape (G₀ ++ B) C (leftPrefixIx G₀ B C i)
  group-split-left-prefix G₀ (b ∷ B) C (head-group .B j) =
    head-split-left-prefix G₀ B C j
  group-split-left-prefix G₀ (b ∷ B) C (next-group .b {i = i} g) =
    transportSplitShapeˡ groupEq same
      (group-split-left-prefix (G₀ ++ (b ∷ [])) B C g)
    where
    groupEq : (G₀ ++ (b ∷ [])) ++ B ≡ G₀ ++ (b ∷ B)
    groupEq = L.++-assoc G₀ (b ∷ []) B

    sumPrefixEq : sum (G₀ ++ (b ∷ [])) ≡ sum G₀ + b
    sumPrefixEq =
      sum-++ G₀ (b ∷ [])
      ■ cong (sum G₀ +_) (NatP.+-identityʳ b)

    same :
      Fin.toℕ (leftPrefixIx G₀ (b ∷ B) C (b ↑ʳ i)) ≡
      Fin.toℕ (leftPrefixIx (G₀ ++ (b ∷ [])) B C i)
    same =
      leftPrefixIx-toℕ G₀ (b ∷ B) C (b ↑ʳ i)
      ■ cong (sum G₀ +_) (Fin.toℕ-↑ʳ b i)
      ■ sym (NatP.+-assoc (sum G₀) b (Fin.toℕ i))
      ■ cong (_+ Fin.toℕ i) (sym sumPrefixEq)
      ■ sym (leftPrefixIx-toℕ (G₀ ++ (b ∷ [])) B C i)

  group-split-right-prefix :
    (G₀ B C : Typed.BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i →
    SplitShape C (G₀ ++ B) (rightPrefixIx G₀ B C i)
  group-split-right-prefix G₀ (b ∷ B) C (head-group .B j) =
    head-split-right-prefix G₀ B C j
  group-split-right-prefix G₀ (b ∷ B) C (next-group .b {i = i} g) =
    transportSplitShapeʳ groupEq same
      (group-split-right-prefix (G₀ ++ (b ∷ [])) B C g)
    where
    groupEq : (G₀ ++ (b ∷ [])) ++ B ≡ G₀ ++ (b ∷ B)
    groupEq = L.++-assoc G₀ (b ∷ []) B

    sumPrefixEq : sum (G₀ ++ (b ∷ [])) ≡ sum G₀ + b
    sumPrefixEq =
      sum-++ G₀ (b ∷ [])
      ■ cong (sum G₀ +_) (NatP.+-identityʳ b)

    same :
      Fin.toℕ (rightPrefixIx G₀ (b ∷ B) C (b ↑ʳ i)) ≡
      Fin.toℕ (rightPrefixIx (G₀ ++ (b ∷ [])) B C i)
    same =
      rightPrefixIx-toℕ G₀ (b ∷ B) C (b ↑ʳ i)
      ■ cong (sum C +_)
          (cong (sum G₀ +_) (Fin.toℕ-↑ʳ b i)
           ■ sym (NatP.+-assoc (sum G₀) b (Fin.toℕ i))
           ■ cong (_+ Fin.toℕ i) (sym sumPrefixEq))
      ■ sym (rightPrefixIx-toℕ (G₀ ++ (b ∷ [])) B C i)

  group-split-left :
    (B C : Typed.BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i →
    SplitShape B C (i ↑ˡ sum C)
  group-split-left B C {i = i} g =
    transportSplitShapeˡ refl
      (Fin.toℕ-↑ˡ i (sum C) ■ sym (leftPrefixIx-toℕ [] B C i))
      (group-split-left-prefix [] B C g)

  group-split-right :
    (C B : Typed.BindGroup) {i : 𝔽 (sum B)} →
    GroupOf B i →
    SplitShape C B (sum C ↑ʳ i)
  group-split-right C B {i = i} g =
    transportSplitShapeʳ refl
      (Fin.toℕ-↑ʳ (sum C) i ■ sym (rightPrefixIx-toℕ [] B C i))
      (group-split-right-prefix [] B C g)

  canon-lsplit-sess :
    ∀ {k} {ctx : BorrowedCF.Simulation.BackwardSoup.Locate.ProcessContext k 0}
      {x : 𝔽 k}
      (s₀ : Types.𝕊 0) (E : SourceReduction.Frame* k)
      (bnd : Binder ctx x)
      (sh : SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)) →
    CanonSplit.sess (canon-lsplit s₀ E bnd sh) ≡ s₀
  canon-lsplit-sess s₀ E bnd (split-l G₁ G₂ q b C) = refl
  canon-lsplit-sess s₀ E bnd (split-r C G₁ G₂ q b) = refl

  split-shape :
    ∀ {k} {ctx : BorrowedCF.Simulation.BackwardSoup.Locate.ProcessContext k 0}
      {x : 𝔽 k} →
    (bnd : Binder ctx x) →
    SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
  split-shape bnd
    with sideOf (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)
  ... | inl i = group-split-left (Binder.B₁ bnd) (Binder.B₂ bnd) (groupOf (Binder.B₁ bnd) i)
  ... | inr i = group-split-right (Binder.B₁ bnd) (Binder.B₂ bnd) (groupOf (Binder.B₂ bnd) i)

------------------------------------------------------------------------
-- A strict soup left split reflects to the canonical typed `R-LSplit`.

lsplit-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  {s : Types.𝕊 0} {e₁ e₂ : Soup.Thread n} →
  SoupReduction.is-open cs i →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K (SoupTerm.`lsplit s) SoupTerm.·¹
        SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ]
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    GlobalImage P′
      (Soup.config cs
        (SoupReduction.replaceAt ts j
          (F SoupExpression.[
            SoupReduction.𝓒[ e₁ × Soup.endpoint i side × SoupTerm.* ]
            SoupTerm.⊗
            SoupReduction.𝓒[ SoupTerm.* × Soup.endpoint i side × e₂ ]
          ]*)))
lsplit-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j i side F {s = s} {e₁ = e₁} {e₂ = e₂} openEq selected ⊢P image
  with image-thread-term image j
         (lsplit-redex-not-unit {F = F} selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F (Source.`lsplit s) Types.𝟙
         (SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ])
         (sym content ■ selected)
... | E , arg , sourceEq , frameEq , argEq
  with SourceReduction.⊢[]*⁻¹ E (Source.K (Source.`lsplit s) Source.·¹ arg)
         (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) sourceEq ⊢source)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E , ⊢app
  with lsplit-arg-chan ⊢app
... | s′ , β , R , ϵ₂ , ⊢arg , argTy
  with argument-var ⊢arg (argTy) argEq
... | x , refl =
  targetProc
  , TypedReduction.R-Struct redex≋ typedStep ≋-refl
  , closeConfigStep exactStep
  where
  redexLocal : Typed.Proc k
  redexLocal =
    Typed.⟪ E SourceReduction.[
      Source.K (Source.`lsplit s) Source.·¹ (Source.` x) ]* ⟫

  redexProc : Typed.Proc 0
  redexProc = plug ctx redexLocal

  bnd = resolve ctx x

  canon =
    canon-lsplit s E bnd (split-shape bnd)

  open CanonSplit canon

  sessEq : sess ≡ s
  sessEq = canon-lsplit-sess s E bnd (split-shape bnd)

  localRedex : Typed.Proc _
  localRedex =
    Typed.ν (G₁ ++ (q + suc b) ∷ G₂) C
      (Typed.⟪ E₀ SourceReduction.[
         Source.K (Source.`lsplit sess) Source.·¹
           (Source.`
             (Source.SplitRenamings.atk G₁ G₂ (sum C)
               {q + suc b} {_} (q ↑ʳ 0F))) ]* ⟫
       Typed.∥ Q₀)

  localTarget : Typed.Proc _
  localTarget =
    Typed.ν (G₁ ++ (q + suc (suc b)) ∷ G₂) C
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₀
                   (Source.SplitRenamings.lwk G₁ G₂ (sum C) {q} {b} {_}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.atk G₁ G₂ (sum C)
                       {q + suc (suc b)} {_} (q ↑ʳ 0F)))
                   (Source.`
                     (Source.SplitRenamings.atk G₁ G₂ (sum C)
                       {q + suc (suc b)} {_} (q ↑ʳ 1F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ Q₀
           (Source.SplitRenamings.lwk G₁ G₂ (sum C) {q} {b} {_})))

  canonicalRedex : Typed.Proc 0
  canonicalRedex = plug above′ localRedex

  targetProc : Typed.Proc 0
  targetProc = plug above′ localTarget

  redex≋ : P Typed.≋ canonicalRedex
  redex≋ =
    ≡→≋ (cong (plug ctx ∘ Typed.⟪_⟫) sourceEq)
    ◅◅
    ≋-redex

  sourceToRedexTracks :
    Tracks (≡→≋ (cong (plug ctx ∘ Typed.⟪_⟫) sourceEq))
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext ctx redexLocal 0F)
  sourceToRedexTracks =
    tracks-≡→≋ℕ
      (cong (plug ctx ∘ Typed.⟪_⟫) sourceEq)
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext-ℕ ctx redexLocal Typed.⟪ source ⟫ 0F 0F refl)

  redexTracks :
    Tracks redex≋
      (threadInContext ctx Typed.⟪ source ⟫ 0F)
      (threadInContext above′ localRedex 0F)
  redexTracks =
    tracks-◅◅ sourceToRedexTracks tracks

  typedStep : canonicalRedex TypedReduction.─→ₚ targetProc
  typedStep = plug-red above′ localStep
    where
    localStep :
      Typed.ν (G₁ ++ (q + suc b) ∷ G₂) C
        (Typed.⟪ E₀ SourceReduction.[
          Source.K (Source.`lsplit sess) Source.·¹
            (Source.`
              (Source.SplitRenamings.atk G₁ G₂ (sum C)
                {q + suc b} {_} (q ↑ʳ 0F))) ]* ⟫
         Typed.∥ Q₀)
      TypedReduction.─→ₚ
      Typed.ν (G₁ ++ (q + suc (suc b)) ∷ G₂) C
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_ E₀
                     (Source.SplitRenamings.lwk G₁ G₂ (sum C) {q} {b} {_}))
                   (Source._⊗_
                     (Source.`
                       (Source.SplitRenamings.atk G₁ G₂ (sum C)
                         {q + suc (suc b)} {_} (q ↑ʳ 0F)))
                     (Source.`
                       (Source.SplitRenamings.atk G₁ G₂ (sum C)
                         {q + suc (suc b)} {_} (q ↑ʳ 1F)))) ⟫
         Typed.∥
           (Typed._⋯ₚ_ Q₀
             (Source.SplitRenamings.lwk G₁ G₂ (sum C) {q} {b} {_})))
    localStep =
      TypedReduction.R-LSplit
        {B₁ = G₁} {B₂ = G₂} {B = C}
        {q = q} {b₁ = b} {s = sess} {E = E₀}

  canonicalGlobalImage = transportGlobalImage redex≋ image

  canonicalImage : LocalImage canonicalRedex (logicalChannels canonicalGlobalImage)
    (λ ()) (λ _ → ⊥) (λ _ → ⊥) (Soup.config cs ts)
  canonicalImage = localImage canonicalGlobalImage

  canonicalTyping :
    [] ; Context.[] ⊢ₚ canonicalRedex
  canonicalTyping =
    AllV.[] / ⊢P ⊢-≋ redex≋

  focused = focusImage above′ localRedex canonicalImage

  focusedTyping = focusTyping above′ localRedex AllV.[] canonicalTyping

  localValueEnv =
    focusValueEnv above′ localRedex
      (logicalChannels canonicalGlobalImage) (λ ())

  leaf =
    lsplit-step
      {k = midˢ} {q = q} {b₁ = b}
      {B₁ = G₁} {B₂ = G₂} {B = C} {s = sess}
      {E = E₀} {P = Q₀}
      {logicalChannels =
        focusChannels above′ localRedex (logicalChannels canonicalGlobalImage)}
      {sigma =
        focusEnv above′ localRedex
          (logicalChannels canonicalGlobalImage) (λ ())}
      {ambientChannel = focusedAmbientChannel focused}
      {ambientThread = focusedAmbientThread focused}
      {C = Soup.config cs ts}
      (proj₁ (proj₂ (proj₂ focusedTyping)))
      (proj₂ (proj₂ (proj₂ focusedTyping)))
      localValueEnv
      (focused-image focused)

  trackedSlot :
    threadEmbedding canonicalImage
      (threadInContext above′ localRedex 0F)
    ≡ just j
  trackedSlot =
    transportGlobalSlot redex≋ image redexTracks
      (cong (threadEmbedding (localImage image)) position ■ embedded)

  focusedSlot :
    threadEmbedding (focused-image focused) 0F ≡
    threadEmbedding canonicalImage (threadInContext above′ localRedex 0F)
  focusedSlot =
    focusImage-thread above′ localRedex canonicalImage 0F

  sameSlot : lsplitThread leaf ≡ j
  sameSlot =
    just-injective
      (sym (lsplitSlotEq leaf) ■ focusedSlot ■ trackedSlot)

  concreteHandleValue :
    SoupExpression.Value
      (Translation.chanTriple (e₁ , Soup.endpoint i side , e₂))
  concreteHandleValue =
    subst SoupExpression.Value argEq
      (focusValueEnv ctx Typed.⟪ source ⟫
        (logicalChannels image) (λ ()) x)

  leafHandleValue :
    SoupExpression.Value
      (Translation.chanTriple
        ( lsplitHandleLeft leaf
        , lsplitHandleEnd leaf
        , lsplitHandleRight leaf ))
  leafHandleValue =
    lsplitHandleValue leaf

  redexEq :
    lsplitFrame leaf SoupExpression.[
      SoupTerm.K (SoupTerm.`lsplit s) SoupTerm.·¹
        Translation.chanTriple
          ( lsplitHandleLeft leaf
          , lsplitHandleEnd leaf
          , lsplitHandleRight leaf )
    ]* ≡
    F SoupExpression.[
      SoupTerm.K (SoupTerm.`lsplit s) SoupTerm.·¹
        SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ]
    ]*
  redexEq =
    sym
      (subst
        (λ z →
          lookup ts (lsplitThread leaf) ≡
          lsplitFrame leaf SoupExpression.[
            SoupTerm.K (SoupTerm.`lsplit z) SoupTerm.·¹
              Translation.chanTriple
                ( lsplitHandleLeft leaf
                , lsplitHandleEnd leaf
                , lsplitHandleRight leaf )
          ]*)
        sessEq
        (lsplitSelected leaf))
    ■ cong (lookup ts) sameSlot
    ■ selected

  handleEq :
    Translation.chanTriple
      ( lsplitHandleLeft leaf
      , lsplitHandleEnd leaf
      , lsplitHandleRight leaf )
    ≡
    Translation.chanTriple (e₁ , Soup.endpoint i side , e₂)
  handleEq =
    proj₁ (proj₂ (redex-unique
      {F = lsplitFrame leaf} {F′ = F}
      {c = SoupTerm.`lsplit s} {c′ = SoupTerm.`lsplit s}
      leafHandleValue concreteHandleValue redexEq))

  replacementHandleEq :
    SoupReduction.𝓒[
      lsplitHandleLeft leaf × lsplitHandleEnd leaf × SoupTerm.* ]
    SoupTerm.⊗
    SoupReduction.𝓒[
      SoupTerm.* × lsplitHandleEnd leaf × lsplitHandleRight leaf ]
    ≡
    SoupReduction.𝓒[ e₁ × Soup.endpoint i side × SoupTerm.* ]
    SoupTerm.⊗
    SoupReduction.𝓒[ SoupTerm.* × Soup.endpoint i side × e₂ ]
  replacementHandleEq = split-replacement-cong handleEq

  replacementEq :
    lsplitReplacement leaf ≡
    F SoupExpression.[
      SoupReduction.𝓒[ e₁ × Soup.endpoint i side × SoupTerm.* ]
      SoupTerm.⊗
      SoupReduction.𝓒[ SoupTerm.* × Soup.endpoint i side × e₂ ]
    ]*
  replacementEq =
    lsplitReplacement≡ leaf
    ■ cong (λ t → lsplitFrame leaf SoupExpression.[ t ]*)
        replacementHandleEq
    ■ framePlugEq
        (SoupReduction.𝓒[ e₁ × Soup.endpoint i side × SoupTerm.* ]
         SoupTerm.⊗
         SoupReduction.𝓒[ SoupTerm.* × Soup.endpoint i side × e₂ ])
    where
    framePlugEq :
      (t : SoupTerm.Tm (2 *ℕ n)) →
      lsplitFrame leaf SoupExpression.[ t ]* ≡
      F SoupExpression.[ t ]*
    framePlugEq =
      proj₂ (proj₂ (redex-unique
        {F = lsplitFrame leaf} {F′ = F}
        {c = SoupTerm.`lsplit s} {c′ = SoupTerm.`lsplit s}
        leafHandleValue concreteHandleValue redexEq))

  exactStep =
    ascend focused
      (lsplitConfigStepAt leaf sameSlot replacementEq)
