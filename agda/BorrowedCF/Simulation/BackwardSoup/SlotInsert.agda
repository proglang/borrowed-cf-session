-- | Slot-renumbering support for backward reflection of `RUS-RSplit`.
module BorrowedCF.Simulation.BackwardSoup.SlotInsert where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Nat.Properties as NatP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.BackwardSoup.Statement
  using ( _≈¹_; _≈ˢ_; swap; swapAt; swapPhi; swapFlags; swapSlot
        ; swapPhi-hit; swapPhi-miss; ≈¹⇒≈ˢ; ≈ˢ-refl; ≈ˢ-sym; ≈ˢ-trans)
open import BorrowedCF.Simulation.ForwardSoup.Local.InsertSupport
  using (insertPhi-hit)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Moving an insertion one slot to the right.

swapSlot-insertSlot :
  (k l : ℕ) →
  swapSlot k (SoupReduction.insertSlot k l) ≡
  SoupReduction.insertSlot (suc k) l
swapSlot-insertSlot zero zero = refl
swapSlot-insertSlot zero (suc l) = refl
swapSlot-insertSlot (suc k) zero = refl
swapSlot-insertSlot (suc k) (suc l) =
  cong suc (swapSlot-insertSlot k l)

swapPhi-insertPhi :
  (x : 𝔽 n) (k : ℕ) (t : SoupTerm.Tm n) →
  swapPhi x k (SoupReduction.insertPhi x k t) ≡
  SoupReduction.insertPhi x (suc k) t
swapPhi-insertPhi x k (SoupTerm.` y) = refl
swapPhi-insertPhi x k (SoupTerm.`phi (y , l))
  with x Fin.≟ y
... | no apart =
  swapPhi-miss apart k l
... | yes refl =
  swapPhi-hit x k (SoupReduction.insertSlot k l)
  ■ cong (λ z → SoupTerm.`phi (x , z)) (swapSlot-insertSlot k l)
swapPhi-insertPhi x k (SoupTerm.K c) = refl
swapPhi-insertPhi x k (SoupTerm.ƛ t) =
  cong SoupTerm.ƛ (swapPhi-insertPhi (suc x) k t)
swapPhi-insertPhi x k (SoupTerm.μ t) =
  cong SoupTerm.μ (swapPhi-insertPhi (suc x) k t)
swapPhi-insertPhi x k (t₁ SoupTerm.·⟨ d ⟩ t₂) =
  cong₂ (SoupTerm._·⟨ d ⟩_)
    (swapPhi-insertPhi x k t₁) (swapPhi-insertPhi x k t₂)
swapPhi-insertPhi x k (t₁ SoupTerm.; t₂) =
  cong₂ SoupTerm._;_
    (swapPhi-insertPhi x k t₁) (swapPhi-insertPhi x k t₂)
swapPhi-insertPhi x k (t₁ SoupTerm.⊗ t₂) =
  cong₂ SoupTerm._⊗_
    (swapPhi-insertPhi x k t₁) (swapPhi-insertPhi x k t₂)
swapPhi-insertPhi x k (SoupTerm.`let t₁ `in t₂) =
  cong₂ SoupTerm.`let_`in_
    (swapPhi-insertPhi x k t₁)
    (swapPhi-insertPhi (suc x) k t₂)
swapPhi-insertPhi x k (SoupTerm.`let⊗ t₁ `in t₂) =
  cong₂ SoupTerm.`let⊗_`in_
    (swapPhi-insertPhi x k t₁)
    (swapPhi-insertPhi (suc (suc x)) k t₂)
swapPhi-insertPhi x k (SoupTerm.`inj side t) =
  cong (SoupTerm.`inj side) (swapPhi-insertPhi x k t)
swapPhi-insertPhi x k (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₃ SoupTerm.`case_`of⟨_;_⟩
    (swapPhi-insertPhi x k t)
    (swapPhi-insertPhi (suc x) k t₁)
    (swapPhi-insertPhi (suc x) k t₂)
  where
  cong₃ :
    {A B C D : Set} (f : A → B → C → D)
    {a a′ : A} {b b′ : B} {c c′ : C} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

swapPhi-insertPhi-frame :
  (x : 𝔽 n) (k : ℕ) (F : SoupExpression.Frame n)
  (t : SoupTerm.Tm n) →
  swapPhi x k
    (SoupReduction.insertPhi-frame x k F SoupExpression.[ t ]) ≡
  SoupReduction.insertPhi-frame x (suc k) F SoupExpression.[
    swapPhi x k t ]
swapPhi-insertPhi-frame x k (SoupExpression.app₁ e d V?) t =
  cong₂ (SoupTerm._·⟨ d ⟩_)
    refl (swapPhi-insertPhi x k e)
swapPhi-insertPhi-frame x k (SoupExpression.app₂ e d V?) t =
  cong₂ (SoupTerm._·⟨ d ⟩_)
    (swapPhi-insertPhi x k e) refl
swapPhi-insertPhi-frame x k (SoupExpression.□⊗ e) t =
  cong₂ SoupTerm._⊗_ refl (swapPhi-insertPhi x k e)
swapPhi-insertPhi-frame x k (V SoupExpression.⊗□) t =
  cong₂ SoupTerm._⊗_
    (swapPhi-insertPhi x k (SoupExpression.vTm V)) refl
swapPhi-insertPhi-frame x k (SoupExpression.□; e) t =
  cong₂ SoupTerm._;_ refl (swapPhi-insertPhi x k e)
swapPhi-insertPhi-frame x k (SoupExpression.`let-`in e) t =
  cong₂ SoupTerm.`let_`in_ refl (swapPhi-insertPhi (suc x) k e)
swapPhi-insertPhi-frame x k (SoupExpression.`let⊗-`in e) t =
  cong₂ SoupTerm.`let⊗_`in_ refl
    (swapPhi-insertPhi (suc (suc x)) k e)
swapPhi-insertPhi-frame x k (SoupExpression.`inj□ side) t = refl
swapPhi-insertPhi-frame x k
  (SoupExpression.`case□`of⟨ e₁ ; e₂ ⟩) t =
  cong₂ (λ head branches →
      SoupTerm.`case head `of⟨ proj₁ branches ; proj₂ branches ⟩)
    refl
    (cong₂ _,_
      (swapPhi-insertPhi (suc x) k e₁)
      (swapPhi-insertPhi (suc x) k e₂))

swapPhi-insertPhi-frames :
  (x : 𝔽 n) (k : ℕ) (F : SoupExpression.Frame* n)
  (t : SoupTerm.Tm n) →
  swapPhi x k
    (SoupReduction.insertPhi-frames x k F SoupExpression.[ t ]*) ≡
  SoupReduction.insertPhi-frames x (suc k) F SoupExpression.[
    swapPhi x k t ]*
swapPhi-insertPhi-frames x k [] t = refl
swapPhi-insertPhi-frames x k (F ∷ Fs) t =
  swapPhi-insertPhi-frame x k F
    (SoupReduction.insertPhi-frames x k Fs SoupExpression.[ t ]*)
  ■ cong (SoupReduction.insertPhi-frame x (suc k) F SoupExpression.[_])
      (swapPhi-insertPhi-frames x k Fs t)

------------------------------------------------------------------------
-- A normal form for a right-split soup reduct at an explicit slot.

insertDrop : ℕ → List Soup.Flag → List Soup.Flag
insertDrop zero fs = Soup.drop ∷ fs
insertDrop (suc k) [] = Soup.drop ∷ []
insertDrop (suc k) (f ∷ fs) = f ∷ insertDrop k fs

insertDrop-prefix :
  (before after : List Soup.Flag) →
  insertDrop (L.length before) (before L.++ after) ≡
  before L.++ Soup.drop ∷ after
insertDrop-prefix [] after = refl
insertDrop-prefix (f ∷ before) after =
  cong (f ∷_) (insertDrop-prefix before after)

swapAt-insertDrop :
  (k : ℕ) (fs : List Soup.Flag) →
  k Nat.< L.length fs →
  swapAt k (insertDrop k fs) ≡ insertDrop (suc k) fs
swapAt-insertDrop zero [] ()
swapAt-insertDrop zero (f ∷ fs) lt = refl
swapAt-insertDrop (suc k) [] ()
swapAt-insertDrop (suc k) (f ∷ fs) (Nat.s≤s lt) =
  cong (f ∷_) (swapAt-insertDrop k fs lt)

insertDrop-longer :
  (k : ℕ) (fs : List Soup.Flag) →
  k Nat.< L.length fs →
  suc k Nat.< L.length (insertDrop k fs)
insertDrop-longer zero [] ()
insertDrop-longer zero (f ∷ fs) lt = Nat.s≤s (Nat.s≤s Nat.z≤n)
insertDrop-longer (suc k) [] ()
insertDrop-longer (suc k) (f ∷ fs) (Nat.s≤s lt) =
  Nat.s≤s (insertDrop-longer k fs lt)

rsplitBody :
  (x : 𝔽 n) → ℕ → SoupTerm.Tm n → SoupTerm.Tm n → SoupTerm.Tm n
rsplitBody x k e₁ e₂ =
  Translation.chanTriple
    ( SoupReduction.insertPhi x k e₁
    , x
    , SoupTerm.`phi (x , k) )
  SoupTerm.⊗
  Translation.chanTriple
    ( SoupTerm.`phi (x , k)
    , x
    , SoupReduction.insertPhi x k e₂ )

swapPhi-rsplitBody :
  (x : 𝔽 n) (k : ℕ) (e₁ e₂ : SoupTerm.Tm n) →
  swapPhi x k (rsplitBody x k e₁ e₂) ≡
  rsplitBody x (suc k) e₁ e₂
swapPhi-rsplitBody x k e₁ e₂
  with x Fin.≟ x
... | no apart = ⊥-elim (apart refl)
... | yes refl =
  cong₂ SoupTerm._⊗_
    (cong₂ SoupTerm._⊗_
      (cong₂ SoupTerm._⊗_
        (swapPhi-insertPhi x k e₁) refl)
      (cong SoupTerm.`phi (cong (x ,_) (swap-self k))))
    (cong₂ SoupTerm._⊗_
      (cong₂ SoupTerm._⊗_
        (cong SoupTerm.`phi (cong (x ,_) (swap-self k))) refl)
      (swapPhi-insertPhi x k e₂))
  where
  swap-self : (l : ℕ) →
    swapSlot l l ≡ suc l
  swap-self zero = refl
  swap-self (suc l) = cong suc (swap-self l)

rsplitResult :
  {n m : ℕ} →
  Vec Soup.Channel n → Vec (Soup.Thread n) m →
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2) →
  SoupExpression.Frame* (2 *ℕ n) →
  List Soup.Flag → ℕ → Soup.Thread n → Soup.Thread n →
  Soup.Config n m
rsplitResult cs ts j i side F flags k e₁ e₂ =
  Soup.config
    (V.updateAt cs i
      (SoupReduction.setEndpointFlags side (insertDrop k flags)))
    (SoupReduction.replaceAt
      (V.map (SoupReduction.insertPhi x k) ts) j
      (SoupReduction.insertPhi-frames x k F SoupExpression.[
        rsplitBody x k e₁ e₂ ]*))
  where
  x = Soup.endpoint i side

endpointFlags-setEndpointFlags :
  (side : 𝔽 2) (fs : List Soup.Flag) (ch : Soup.Channel) →
  SoupReduction.endpointFlags
    (SoupReduction.setEndpointFlags side fs ch) side ≡ fs
endpointFlags-setEndpointFlags zero fs (open? , fs₀ , fs₁) = refl
endpointFlags-setEndpointFlags (suc zero) fs (open? , fs₀ , fs₁) = refl

swapFlags-insertDrop :
  (side : 𝔽 2) (k : ℕ) (flags : List Soup.Flag) (ch : Soup.Channel) →
  k Nat.< L.length flags →
  swapFlags side k
    (SoupReduction.setEndpointFlags side (insertDrop k flags) ch) ≡
  SoupReduction.setEndpointFlags side (insertDrop (suc k) flags) ch
swapFlags-insertDrop zero k flags (open? , fs₀ , fs₁) lt =
  cong (λ fs → open? , fs , fs₁) (swapAt-insertDrop k flags lt)
swapFlags-insertDrop (suc zero) k flags (open? , fs₀ , fs₁) lt =
  cong (λ fs → open? , fs₀ , fs) (swapAt-insertDrop k flags lt)

------------------------------------------------------------------------
-- Adjacent and arbitrary valid insertion positions are slot equivalent.

rsplit-adjacent :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (flags : List Soup.Flag) (k : ℕ)
  (e₁ e₂ : Soup.Thread n) →
  k Nat.< L.length flags →
  rsplitResult cs ts j i side F flags k e₁ e₂ ≈¹
  rsplitResult cs ts j i side F flags (suc k) e₁ e₂
rsplit-adjacent cs ts j i side F flags k e₁ e₂ lt =
  subst
    (rsplitResult cs ts j i side F flags k e₁ e₂ ≈¹_)
    targetEq
    (swap resultChannels resultThreads i side k lengthBound)
  where
  x = Soup.endpoint i side

  resultChannels =
    V.updateAt cs i
      (SoupReduction.setEndpointFlags side (insertDrop k flags))

  replacement =
    SoupReduction.insertPhi-frames x k F SoupExpression.[
      rsplitBody x k e₁ e₂ ]*

  resultThreads =
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertPhi x k) ts) j replacement

  resultFlagsEq :
    SoupReduction.endpointFlags (lookup resultChannels i) side ≡
    insertDrop k flags
  resultFlagsEq =
    cong (λ ch → SoupReduction.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-setEndpointFlags side (insertDrop k flags) (lookup cs i)

  lengthBound :
    suc k Nat.<
      L.length (SoupReduction.endpointFlags (lookup resultChannels i) side)
  lengthBound =
    subst (suc k Nat.<_) (sym (cong L.length resultFlagsEq))
      (insertDrop-longer k flags lt)

  channelEq :
    V.updateAt resultChannels i (swapFlags side k) ≡
    V.updateAt cs i
      (SoupReduction.setEndpointFlags side (insertDrop (suc k) flags))
  channelEq =
    V.updateAt-updateAt-local i cs localEq
    where
    localEq :
      swapFlags side k
        (SoupReduction.setEndpointFlags side (insertDrop k flags)
          (lookup cs i)) ≡
      SoupReduction.setEndpointFlags side (insertDrop (suc k) flags)
        (lookup cs i)
    localEq = swapFlags-insertDrop side k flags (lookup cs i) lt

  mapEq :
    V.map (swapPhi x k) (V.map (SoupReduction.insertPhi x k) ts) ≡
    V.map (SoupReduction.insertPhi x (suc k)) ts
  mapEq =
    sym (V.map-∘ (swapPhi x k) (SoupReduction.insertPhi x k) ts)
    ■ V.map-cong (swapPhi-insertPhi x k) ts

  replacementEq :
    swapPhi x k replacement ≡
    SoupReduction.insertPhi-frames x (suc k) F SoupExpression.[
      rsplitBody x (suc k) e₁ e₂ ]*
  replacementEq =
    swapPhi-insertPhi-frames x k F (rsplitBody x k e₁ e₂)
    ■ cong
        (λ t →
          SoupReduction.insertPhi-frames x (suc k) F SoupExpression.[ t ]*)
        (swapPhi-rsplitBody x k e₁ e₂)

  threadEq :
    V.map (swapPhi x k) resultThreads ≡
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertPhi x (suc k)) ts) j
      (SoupReduction.insertPhi-frames x (suc k) F SoupExpression.[
        rsplitBody x (suc k) e₁ e₂ ]*)
  threadEq =
    V.map-updateAt
      (V.map (SoupReduction.insertPhi x k) ts) j replacementEq
    ■ cong₂ (λ ys z → SoupReduction.replaceAt ys j z) mapEq refl

  targetEq :
    Soup.config
      (V.updateAt resultChannels i (swapFlags side k))
      (V.map (swapPhi x k) resultThreads) ≡
    rsplitResult cs ts j i side F flags (suc k) e₁ e₂
  targetEq = cong₂ Soup.config channelEq threadEq

rsplit-advance :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (flags : List Soup.Flag) (k d : ℕ)
  (e₁ e₂ : Soup.Thread n) →
  k + d Nat.≤ L.length flags →
  rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
  rsplitResult cs ts j i side F flags (k + d) e₁ e₂
rsplit-advance cs ts j i side F flags k zero e₁ e₂ bound =
  subst
    (λ l →
      rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
      rsplitResult cs ts j i side F flags l e₁ e₂)
    (sym (NatP.+-identityʳ k))
    ≈ˢ-refl
rsplit-advance cs ts j i side F flags k (suc d) e₁ e₂ bound =
  subst
    (λ l →
      rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
      rsplitResult cs ts j i side F flags l e₁ e₂)
    (sym (NatP.+-suc k d))
    (≈ˢ-trans
      (≈¹⇒≈ˢ
        (rsplit-adjacent cs ts j i side F flags k e₁ e₂ below))
      (rsplit-advance cs ts j i side F flags (suc k) d e₁ e₂ bound′))
  where
  below : k Nat.< L.length flags
  below =
    NatP.≤-trans
      (NatP.m<m+n k {suc d} (Nat.s≤s Nat.z≤n))
      bound

  bound′ : suc k + d Nat.≤ L.length flags
  bound′ =
    subst (λ z → z Nat.≤ L.length flags) (NatP.+-suc k d) bound

rsplit-to-end :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (flags : List Soup.Flag) (k : ℕ)
  (e₁ e₂ : Soup.Thread n) →
  k Nat.≤ L.length flags →
  rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
  rsplitResult cs ts j i side F flags (L.length flags) e₁ e₂
rsplit-to-end cs ts j i side F flags k e₁ e₂ bound =
  subst
    (λ l →
      rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
      rsplitResult cs ts j i side F flags l e₁ e₂)
    endEq
    (rsplit-advance cs ts j i side F flags k
      (L.length flags Nat.∸ k) e₁ e₂ advanceBound)
  where
  endEq : k + (L.length flags Nat.∸ k) ≡ L.length flags
  endEq = NatP.m+[n∸m]≡n bound

  advanceBound : k + (L.length flags Nat.∸ k) Nat.≤ L.length flags
  advanceBound =
    subst (λ z → z Nat.≤ L.length flags) (sym endEq) NatP.≤-refl

rsplit-positions :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : SoupExpression.Frame* (2 *ℕ n))
  (flags : List Soup.Flag) (k l : ℕ)
  (e₁ e₂ : Soup.Thread n) →
  k Nat.≤ L.length flags →
  l Nat.≤ L.length flags →
  rsplitResult cs ts j i side F flags k e₁ e₂ ≈ˢ
  rsplitResult cs ts j i side F flags l e₁ e₂
rsplit-positions cs ts j i side F flags k l e₁ e₂ kBound lBound =
  ≈ˢ-trans
    (rsplit-to-end cs ts j i side F flags k e₁ e₂ kBound)
    (≈ˢ-sym (rsplit-to-end cs ts j i side F flags l e₁ e₂ lBound))
