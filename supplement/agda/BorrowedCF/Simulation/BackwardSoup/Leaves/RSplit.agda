-- | Backward simulation for the soup right-split leaf.
module BorrowedCF.Simulation.BackwardSoup.Leaves.RSplit where

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

open import BorrowedCF.Simulation.ForwardSoup.Local.RSplit
  using ( rsplit-step; rsplitThread; rsplitSlotEq; rsplitChannel; rsplitSide
        ; rsplitOpen; rsplitFrame; rsplitHandleLeft; rsplitHandleEnd
        ; rsplitHandleRight; rsplitHandleValue; rsplitSelected; rsplitReplacement
        ; rsplitHandleEndEq; rsplitBoundary; rsplitBefore; rsplitAfter
        ; rsplitBoundaryEq; rsplitFlagsEq; rsplitTargetChannels
        ; rsplitTargetChannels≡; rsplitInsertedThreads
        ; rsplitInsertedThreads≡; rsplitReplacement≡; rsplitTargetThreads
        ; rsplitTargetThreads≡; rsplitTargetConfig; rsplitTargetConfig≡
        ; rsplitConfigStep)
open import BorrowedCF.Simulation.ForwardSoup.Local.Step as ForwardStep
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (LocalImage; OrientedChannel; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using ( CanonSplit; SplitShape; canon-rsplit
        ; split-l; split-r; splitIx
        ; tracks-≡→≋ℕ; threadInContext-ℕ
        )
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (T-pair-inv; plug-app-not-value; plug-inversion-K)
open import BorrowedCF.Simulation.BackwardSoup.Lift
  using ( focusImage; focused-image; focusImage-thread; ascend; plug-red
        ; closeConfigStep; focusedAmbientChannel; focusedAmbientThread
        ; focusSeparated)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( image-thread-term; focusEnv; focusValueEnv; focusPairEnv
        ; focusExprTyping; focusTyping; focusChannels; closedPairEnv; plug
        ; threadInContext; ≡→≋)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using ( Binder; resolve; sideOf; SideOf; inl; inr
        ; GroupOf; head-group; next-group; groupOf
        )
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage
  using (transportGlobalImage; transportGlobalSlot)
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using (Tracks; tracks-◅◅)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective; endpoint-injective)
open import BorrowedCF.Simulation.BackwardSoup.Unique
  using (redex-unique)
open import BorrowedCF.Simulation.BackwardSoup.Statement
  using (_≈ˢ_)
open import BorrowedCF.Simulation.BackwardSoup.SlotInsert
  using (rsplitBody; rsplitResult; rsplit-positions; insertDrop-prefix)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open import BorrowedCF.Simulation.Support.InvFrame
  using (fn-rsplit-dom)

open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)
open Fin.Patterns

private
  cong₃ :
    {A B C D : Set} (f : A → B → C → D)
    {a a′ : A} {b b′ : B} {c c′ : C} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  prefix-length≤ :
    (xs ys : List Soup.Flag) → L.length xs Nat.≤ L.length (xs L.++ ys)
  prefix-length≤ xs ys =
    subst (L.length xs Nat.≤_)
      (sym (L.length-++ xs))
      (NatP.m≤m+n (L.length xs) (L.length ys))

  rsplit-redex-not-unit :
    {n : ℕ} {F : SoupExpression.Frame* n}
    {s : Types.𝕊 0} {v t : SoupTerm.Tm n} →
    t ≡ F SoupExpression.[
          SoupTerm.K (SoupTerm.`rsplit s) SoupTerm.·¹ v
        ]* →
    t ≢ SoupTerm.*
  rsplit-redex-not-unit {F = F} selected unitEq =
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

  rsplit-arg-chan :
    ∀ {k} {Γ : Context.Ctx k} {γ : Context.Struct k}
      {s : Types.𝕊 0} {arg : Source.Tm k} {T ϵ} →
    Γ ; γ ⊢ Source.K (Source.`rsplit s) Source.·¹ arg ∶ T ∣ ϵ →
    Σ[ s′ ∈ Types.𝕊 0 ] Σ[ β ∈ Context.Struct k ]
    Σ[ R ∈ Types.𝕋 ] Σ[ ϵ₂ ∈ Types.Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) ×
      (Types.⟨ s Types.; s′ ⟩ Types.≃ R)
  rsplit-arg-chan (Source.T-AppUnr _ _ ⊢fn ⊢arg) =
    let s′ , eq = fn-rsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
  rsplit-arg-chan (Source.T-AppLin _ _ ⊢fn ⊢arg) =
    let s′ , eq = fn-rsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
  rsplit-arg-chan (Source.T-Conv _ _ d) = rsplit-arg-chan d
  rsplit-arg-chan (Source.T-Weaken _ d) = rsplit-arg-chan d

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

  canon-rsplit-sess :
    ∀ {k} {ctx : BorrowedCF.Simulation.BackwardSoup.Locate.ProcessContext k 0}
      {x : 𝔽 k}
      (s₀ : Types.𝕊 0) (E : SourceReduction.Frame* k)
      (bnd : Binder ctx x)
      (sh : SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)) →
    CanonSplit.sess (canon-rsplit s₀ E bnd sh) ≡ s₀
  canon-rsplit-sess s₀ E bnd (split-l G₁ G₂ q b C) = refl
  canon-rsplit-sess s₀ E bnd (split-r C G₁ G₂ q b) = refl

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
-- A strict soup right split reflects to the canonical typed `R-RSplit`.

rsplit-reflect :
  {P : Typed.Proc 0} {n m : ℕ}
  {cs : Vec Soup.Channel n} {ts : Vec (Soup.Thread n) m}
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (before after : List Soup.Flag)
  {s : Types.𝕊 0} {e₁ e₂ : Soup.Thread n} →
  SoupReduction.is-open cs i →
  SoupReduction.endpointFlags (lookup cs i) side ≡ before L.++ after →
  lookup ts j ≡
    F SoupExpression.[
      SoupTerm.K (SoupTerm.`rsplit s) SoupTerm.·¹
        SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ]
    ]* →
  [] ; Context.[] ⊢ₚ P →
  (image : GlobalImage P (Soup.config cs ts)) →
  Σ[ P′ ∈ Typed.Proc 0 ]
    (P TypedReduction.─→ₚ P′) ×
    Σ[ C₀′ ∈ Soup.Config n m ] GlobalImage P′ C₀′ ×
      C₀′ ≈ˢ
      (Soup.config
        (V.updateAt cs i
          (SoupReduction.setEndpointFlags side
            (before L.++ Soup.drop ∷ after)))
        (let endpoint = Soup.endpoint i side
             slot = L.length before
         in SoupReduction.replaceAt
              (V.map (SoupReduction.insertPhi endpoint slot) ts) j
              (SoupReduction.insertPhi-frames endpoint slot F
                SoupExpression.[ rsplitBody endpoint slot e₁ e₂ ]*)))
rsplit-reflect {P = P} {n = n} {cs = cs} {ts = ts}
  j i side F before after {s = s} {e₁ = e₁} {e₂ = e₂}
  openEq flagsEq selected ⊢P image
  with image-thread-term image j
         (rsplit-redex-not-unit {F = F} selected)
... | k , ctx , source , sourceThread , refl , position , embedded , content
  with focusExprTyping ctx source AllV.[] ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢source
  with plug-inversion-K source
         (focusEnv ctx Typed.⟪ source ⟫ (logicalChannels image) (λ ()))
         (focusValueEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) (λ ()))
         (focusPairEnv ctx Typed.⟪ source ⟫
           (logicalChannels image) closedPairEnv)
         F (Source.`rsplit s) Types.𝟙
         (SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ])
         (sym content ■ selected)
... | E , arg , sourceEq , frameEq , argEq
  with SourceReduction.⊢[]*⁻¹ E (Source.K (Source.`rsplit s) Source.·¹ arg)
         (subst (λ z → _ ; _ ⊢ z ∶ _ ∣ _) sourceEq ⊢source)
... | _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢E , ⊢app
  with rsplit-arg-chan ⊢app
... | s′ , β , R , ϵ₂ , ⊢arg , argTy
  with argument-var ⊢arg (argTy) argEq
... | x , refl =
  targetProc
  , TypedReduction.R-Struct redex≋ typedStep ≋-refl
  , rsplitTargetConfig leaf
  , closeConfigStep canonicalStep
  , equivalentTarget
  where
  redexLocal : Typed.Proc k
  redexLocal =
    Typed.⟪ E SourceReduction.[
      Source.K (Source.`rsplit s) Source.·¹ (Source.` x) ]* ⟫

  redexProc : Typed.Proc 0
  redexProc = plug ctx redexLocal

  bnd = resolve ctx x

  canon =
    canon-rsplit s E bnd (split-shape bnd)

  open CanonSplit canon

  sessEq : sess ≡ s
  sessEq = canon-rsplit-sess s E bnd (split-shape bnd)

  localRedex : Typed.Proc _
  localRedex =
    Typed.ν (G₁ ++ (q + suc b) ∷ G₂) C
      (Typed.⟪ E₀ SourceReduction.[
         Source.K (Source.`rsplit sess) Source.·¹
           (Source.`
             (Source.SplitRenamings.atk G₁ G₂ (sum C)
               {q + suc b} {_} (q ↑ʳ 0F))) ]* ⟫
       Typed.∥ Q₀)

  localTarget : Typed.Proc _
  localTarget =
    Typed.ν (G₁ ++ (q + 1) ∷ suc b ∷ G₂) C
      (Typed.⟪ SourceReduction._[_]*
                 (SourceReduction._⋯ᶠ*_ E₀
                   (Source.SplitRenamings.rwk G₁ G₂ (sum C) {q} {b} {_}))
                 (Source._⊗_
                   (Source.`
                     (Source.SplitRenamings.inj G₁ G₂ (sum C)
                       {(q + 1) ∷ suc b ∷ []} {_}
                       ((q ↑ʳ 0F) ↑ˡ (suc b + sum G₂))))
                   (Source.`
                     (Source.SplitRenamings.inj G₁ G₂ (sum C)
                       {(q + 1) ∷ suc b ∷ []} {_}
                       ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥
         (Typed._⋯ₚ_ Q₀
           (Source.SplitRenamings.rwk G₁ G₂ (sum C) {q} {b} {_})))

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
          Source.K (Source.`rsplit sess) Source.·¹
            (Source.`
              (Source.SplitRenamings.atk G₁ G₂ (sum C)
                {q + suc b} {_} (q ↑ʳ 0F))) ]* ⟫
         Typed.∥ Q₀)
      TypedReduction.─→ₚ
      Typed.ν (G₁ ++ (q + 1) ∷ suc b ∷ G₂) C
        (Typed.⟪ SourceReduction._[_]*
                   (SourceReduction._⋯ᶠ*_ E₀
                     (Source.SplitRenamings.rwk G₁ G₂ (sum C) {q} {b} {_}))
                   (Source._⊗_
                     (Source.`
                       (Source.SplitRenamings.inj G₁ G₂ (sum C)
                         {(q + 1) ∷ suc b ∷ []} {_}
                         ((q ↑ʳ 0F) ↑ˡ (suc b + sum G₂))))
                     (Source.`
                       (Source.SplitRenamings.inj G₁ G₂ (sum C)
                         {(q + 1) ∷ suc b ∷ []} {_}
                         ((q + 1) ↑ʳ 0F)))) ⟫
         Typed.∥
           (Typed._⋯ₚ_ Q₀
             (Source.SplitRenamings.rwk G₁ G₂ (sum C) {q} {b} {_})))
    localStep =
      TypedReduction.R-RSplit
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

  closedSeparated :
    Separated (λ ()) (λ _ → ⊥) (λ _ → ⊥) (Soup.config cs ts)
  closedSeparated = record
    { env-separated = λ ()
    ; thread-separated = λ _ ()
    }

  localSeparated =
    focusSeparated above′ localRedex closedSeparated canonicalImage

  localValueEnv =
    focusValueEnv above′ localRedex
      (logicalChannels canonicalGlobalImage) (λ ())

  leaf =
    rsplit-step
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
      localSeparated
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

  sameSlot : rsplitThread leaf ≡ j
  sameSlot =
    just-injective
      (sym (rsplitSlotEq leaf) ■ focusedSlot ■ trackedSlot)

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
        ( rsplitHandleLeft leaf
        , rsplitHandleEnd leaf
        , rsplitHandleRight leaf ))
  leafHandleValue =
    rsplitHandleValue leaf

  redexEq :
    rsplitFrame leaf SoupExpression.[
      SoupTerm.K (SoupTerm.`rsplit s) SoupTerm.·¹
        Translation.chanTriple
          ( rsplitHandleLeft leaf
          , rsplitHandleEnd leaf
          , rsplitHandleRight leaf )
    ]* ≡
    F SoupExpression.[
      SoupTerm.K (SoupTerm.`rsplit s) SoupTerm.·¹
        SoupReduction.𝓒[ e₁ × Soup.endpoint i side × e₂ ]
    ]*
  redexEq =
    sym
      (subst
        (λ z →
          lookup ts (rsplitThread leaf) ≡
          rsplitFrame leaf SoupExpression.[
            SoupTerm.K (SoupTerm.`rsplit z) SoupTerm.·¹
              Translation.chanTriple
                ( rsplitHandleLeft leaf
                , rsplitHandleEnd leaf
                , rsplitHandleRight leaf )
          ]*)
        sessEq
        (rsplitSelected leaf))
    ■ cong (lookup ts) sameSlot
    ■ selected

  handleEq :
    Translation.chanTriple
      ( rsplitHandleLeft leaf
      , rsplitHandleEnd leaf
      , rsplitHandleRight leaf )
    ≡
    Translation.chanTriple (e₁ , Soup.endpoint i side , e₂)
  handleEq =
    proj₁ (proj₂ (redex-unique
      {F = rsplitFrame leaf} {F′ = F}
      {c = SoupTerm.`rsplit s} {c′ = SoupTerm.`rsplit s}
      leafHandleValue concreteHandleValue redexEq))

  handleParts = chanTriple-injective handleEq

  handleLeftEq : rsplitHandleLeft leaf ≡ e₁
  handleLeftEq = proj₁ handleParts

  handleEndEq : rsplitHandleEnd leaf ≡ Soup.endpoint i side
  handleEndEq = proj₁ (proj₂ handleParts)

  handleRightEq : rsplitHandleRight leaf ≡ e₂
  handleRightEq = proj₂ (proj₂ handleParts)

  endpointEq :
    Soup.endpoint (rsplitChannel leaf) (rsplitSide leaf) ≡
    Soup.endpoint i side
  endpointEq = sym (rsplitHandleEndEq leaf) ■ handleEndEq

  endpointParts = endpoint-injective endpointEq

  channelEq : rsplitChannel leaf ≡ i
  channelEq = proj₁ endpointParts

  sideEq : rsplitSide leaf ≡ side
  sideEq = proj₂ endpointParts

  flags : List Soup.Flag
  flags = before L.++ after

  leafFlagsEq : rsplitBefore leaf L.++ rsplitAfter leaf ≡ flags
  leafFlagsEq =
    sym (rsplitFlagsEq leaf)
    ■ cong₂
        (λ ch side′ → SoupReduction.endpointFlags (lookup cs ch) side′)
        channelEq sideEq
    ■ flagsEq

  insertedFlagsEq :
    rsplitBefore leaf L.++ Soup.drop ∷ rsplitAfter leaf ≡
    BorrowedCF.Simulation.BackwardSoup.SlotInsert.insertDrop
      (rsplitBoundary leaf) flags
  insertedFlagsEq =
    sym (insertDrop-prefix (rsplitBefore leaf) (rsplitAfter leaf))
    ■ cong₂ BorrowedCF.Simulation.BackwardSoup.SlotInsert.insertDrop
        (rsplitBoundaryEq leaf) leafFlagsEq

  targetChannelsEq :
    rsplitTargetChannels leaf ≡
    V.updateAt cs i
      (SoupReduction.setEndpointFlags side
        (BorrowedCF.Simulation.BackwardSoup.SlotInsert.insertDrop
          (rsplitBoundary leaf) flags))
  targetChannelsEq =
    rsplitTargetChannels≡ leaf
    ■ cong₃
        (λ ch side′ fs →
          V.updateAt cs ch (SoupReduction.setEndpointFlags side′ fs))
        channelEq sideEq insertedFlagsEq

  insertedThreadsEq :
    rsplitInsertedThreads leaf ≡
    V.map
      (SoupReduction.insertPhi (Soup.endpoint i side) (rsplitBoundary leaf)) ts
  insertedThreadsEq =
    rsplitInsertedThreads≡ leaf
    ■ cong
        (λ endpoint →
          V.map (SoupReduction.insertPhi endpoint (rsplitBoundary leaf)) ts)
        handleEndEq

  insertedFrameEq :
    (x′ : 𝔽 (2 *ℕ n)) (slot : ℕ) (t : SoupTerm.Tm (2 *ℕ n)) →
    SoupReduction.insertPhi-frames x′ slot (rsplitFrame leaf)
      SoupExpression.[ t ]* ≡
    SoupReduction.insertPhi-frames x′ slot F SoupExpression.[ t ]*
  insertedFrameEq =
    proj₂ (proj₂ (proj₂ (redex-unique
      {F = rsplitFrame leaf} {F′ = F}
      {c = SoupTerm.`rsplit s} {c′ = SoupTerm.`rsplit s}
      leafHandleValue concreteHandleValue redexEq)))

  targetReplacementEq :
    rsplitReplacement leaf ≡
    SoupReduction.insertPhi-frames
      (Soup.endpoint i side) (rsplitBoundary leaf) F
      SoupExpression.[
        rsplitBody (Soup.endpoint i side) (rsplitBoundary leaf) e₁ e₂ ]*
  targetReplacementEq =
    rsplitReplacement≡ leaf
    ■ insertedFrameEq (rsplitHandleEnd leaf) (rsplitBoundary leaf)
        (rsplitBody (rsplitHandleEnd leaf) (rsplitBoundary leaf)
          (rsplitHandleLeft leaf) (rsplitHandleRight leaf))
    ■ cong₃
        (λ endpoint left right →
          SoupReduction.insertPhi-frames endpoint (rsplitBoundary leaf) F
            SoupExpression.[
              rsplitBody endpoint (rsplitBoundary leaf) left right ]*)
        handleEndEq handleLeftEq handleRightEq

  targetThreadsEq :
    rsplitTargetThreads leaf ≡
    SoupReduction.replaceAt
      (V.map
        (SoupReduction.insertPhi
          (Soup.endpoint i side) (rsplitBoundary leaf)) ts)
      j
      (SoupReduction.insertPhi-frames
        (Soup.endpoint i side) (rsplitBoundary leaf) F
        SoupExpression.[
          rsplitBody (Soup.endpoint i side) (rsplitBoundary leaf) e₁ e₂ ]*)
  targetThreadsEq =
    rsplitTargetThreads≡ leaf
    ■ cong₃
        (λ ts′ j′ replacement → SoupReduction.replaceAt ts′ j′ replacement)
        insertedThreadsEq sameSlot targetReplacementEq

  canonicalResultEq :
    rsplitTargetConfig leaf ≡
    rsplitResult cs ts j i side F flags (rsplitBoundary leaf) e₁ e₂
  canonicalResultEq =
    rsplitTargetConfig≡ leaf
    ■ cong₂ Soup.config targetChannelsEq targetThreadsEq

  canonicalBound : rsplitBoundary leaf Nat.≤ L.length flags
  canonicalBound =
    subst₂ Nat._≤_
      (rsplitBoundaryEq leaf)
      (cong L.length leafFlagsEq)
      (prefix-length≤ (rsplitBefore leaf) (rsplitAfter leaf))

  soupBound : L.length before Nat.≤ L.length flags
  soupBound = prefix-length≤ before after

  positionsEquivalent =
    rsplit-positions cs ts j i side F flags
      (rsplitBoundary leaf) (L.length before) e₁ e₂
      canonicalBound soupBound

  actualThreads =
    SoupReduction.replaceAt
      (V.map
        (SoupReduction.insertPhi (Soup.endpoint i side) (L.length before)) ts)
      j
      (SoupReduction.insertPhi-frames
        (Soup.endpoint i side) (L.length before) F
        SoupExpression.[
          rsplitBody (Soup.endpoint i side) (L.length before) e₁ e₂ ]*)

  actualResultEq :
    rsplitResult cs ts j i side F flags (L.length before) e₁ e₂ ≡
    Soup.config
      (V.updateAt cs i
        (SoupReduction.setEndpointFlags side
          (before L.++ Soup.drop ∷ after)))
      actualThreads
  actualResultEq =
    cong
      (λ fs →
        Soup.config
          (V.updateAt cs i (SoupReduction.setEndpointFlags side fs))
          actualThreads)
      (insertDrop-prefix before after)

  equivalentTarget =
    subst₂ _≈ˢ_ (sym canonicalResultEq) actualResultEq positionsEquivalent

  canonicalStep = ascend focused (rsplitConfigStep leaf)
