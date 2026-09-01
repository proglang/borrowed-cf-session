module BorrowedCF.Reduction.Processes.UntypedSoup where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Terms.BaseSoup
open import BorrowedCF.Processes.UntypedSoup
open import BorrowedCF.Reduction.ExpressionsSoup

open Nat.Variables
open Fin.Patterns

private variable A : Set

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

replaceAt : Vec A n → 𝔽 n → A → Vec A n
replaceAt xs i x = V.updateAt xs i (const x)

replaceTwo : Vec A n → 𝔽 n → A → 𝔽 n → A → Vec A n
replaceTwo xs i x j y = replaceAt (replaceAt xs i x) j y

insertAfter : Vec A n → 𝔽 n → A → Vec A (suc n)
insertAfter xs i x = V.insertAt xs (suc i) x

endpointFlags : Channel → 𝔽 2 → List Flag
endpointFlags (_ , fs₀ , fs₁) zero = fs₀
endpointFlags (_ , fs₀ , fs₁) (suc zero) = fs₁

setEndpointFlags : 𝔽 2 → List Flag → Channel → Channel
setEndpointFlags zero fs (open? , _ , fs₁) = open? , fs , fs₁
setEndpointFlags (suc zero) fs (open? , fs₀ , _) = open? , fs₀ , fs

appendEndpointFlag : 𝔽 2 → Flag → Channel → Channel
appendEndpointFlag side f ch =
  setEndpointFlags side (endpointFlags ch side ++ f ∷ []) ch

shiftSlot : ℕ → ℕ → ℕ
shiftSlot zero zero = zero
shiftSlot zero (suc k) = k
shiftSlot (suc k) zero = zero
shiftSlot (suc k) (suc l) = suc (shiftSlot k l)

-- Remove one phi cell.  The matching occurrence is unreachable after the
-- acquire redex is replaced; unit keeps the operation total on raw terms.
consumePhi : 𝔽 n → ℕ → Tm n → Tm n
consumePhi x k (` y) = ` y
consumePhi x k (`phi (y , l)) with x FinP.≟ y
... | no _ = `phi (y , l)
... | yes refl with k NatP.≟ l
...   | no _ = `phi (x , shiftSlot k l)
...   | yes refl = *
consumePhi x k (K c) = K c
consumePhi x k (ƛ e) = ƛ (consumePhi (suc x) k e)
consumePhi x k (μ e) = μ (consumePhi (suc x) k e)
consumePhi x k (e₁ ·⟨ d ⟩ e₂) =
  consumePhi x k e₁ ·⟨ d ⟩ consumePhi x k e₂
consumePhi x k (e₁ ; e₂) = consumePhi x k e₁ ; consumePhi x k e₂
consumePhi x k (e₁ ⊗ e₂) = consumePhi x k e₁ ⊗ consumePhi x k e₂
consumePhi x k (`let e₁ `in e₂) =
  `let consumePhi x k e₁ `in consumePhi (suc x) k e₂
consumePhi x k (`let⊗ e₁ `in e₂) =
  `let⊗ consumePhi x k e₁ `in consumePhi (suc (suc x)) k e₂
consumePhi x k (`inj side e) = `inj side (consumePhi x k e)
consumePhi x k (`case e `of⟨ e₁ ; e₂ ⟩) =
  `case consumePhi x k e
    `of⟨ consumePhi (suc x) k e₁ ; consumePhi (suc x) k e₂ ⟩

weakenEndpoint : ∀ {n} → 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
weakenEndpoint {n} x =
  Fin.cast (sym (Nat.*-suc 2 n)) (suc (suc x))

weakenThread : Thread n → Thread (suc n)
weakenThread e = e ⋯ᵣ weakenEndpoint

newResult : ∀ {n} → Frame* (2 *ℕ n) → Thread (suc n)
newResult {n} F =
  let l = leftEnd {n = suc n} zero
      r = rightEnd {n = suc n} zero
      c₀ = 𝓒[ `phi (l , 0) × l × * ]
      c₁ = 𝓒[ `phi (r , 0) × r × * ]
  in frames-rename F weakenEndpoint [ c₀ ⊗ c₁ ]*

data Opposite : 𝔽 2 → 𝔽 2 → Set where
  left-right : Opposite zero (suc zero)
  right-left : Opposite (suc zero) zero

infix 4 _─→ₚ_

data _─→ₚ_ : ∀ {n m n′ m′} → Config n m → Config n′ m′ → Set where
  RUS-Exp :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) {e′} →
    lookup ts j ⋯→ e′ →
    config cs ts ─→ₚ config cs (replaceAt ts j e′)

  RUS-Fork :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (F : Frame* (2 *ℕ n)) {e} →
    Value e →
    lookup ts j ≡ F [ K `fork ·¹ e ]* →
    config cs ts ─→ₚ
    config cs (insertAfter (replaceAt ts j (F [ * ]*)) j (e ·¹ *))

  RUS-New :
    ∀ {n m s} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (F : Frame* (2 *ℕ n)) →
    lookup ts j ≡ F [ K (`new s) ·¹ * ]* →
    config cs ts ─→ₚ
    config ((true , acq ∷ [] , acq ∷ []) ∷ cs)
      (replaceAt (V.map weakenThread ts) j (newResult F))

  RUS-LSplit :
    ∀ {n m s} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) {e₁ e₂} →
    proj₁ (lookup cs i) ≡ true →
    lookup ts j ≡
      F [ K (`lsplit s) ·¹ 𝓒[ e₁ × endpoint i side × e₂ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceAt ts j
      (F [ 𝓒[ e₁ × endpoint i side × * ] ⊗
           𝓒[ * × endpoint i side × e₂ ] ]*))

  RUS-RSplit :
    ∀ {n m s} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) {e₁ e₂} →
    proj₁ (lookup cs i) ≡ true →
    lookup ts j ≡
      F [ K (`rsplit s) ·¹ 𝓒[ e₁ × endpoint i side × e₂ ] ]* →
    config cs ts ─→ₚ
    config (V.updateAt cs i (appendEndpointFlag side drop))
      (replaceAt ts j
        (let x = endpoint i side
             k = L.length (endpointFlags (lookup cs i) side)
         in F [ 𝓒[ e₁ × x × `phi (x , k) ] ⊗
                𝓒[ `phi (x , k) × x × e₂ ] ]*))

  RUS-Drop :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) (before after : List Flag) →
    proj₁ (lookup cs i) ≡ true →
    endpointFlags (lookup cs i) side ≡ before ++ drop ∷ after →
    lookup ts j ≡
      F [ K `drop ·¹
          𝓒[ * × endpoint i side ×
             `phi (endpoint i side , L.length before) ] ]* →
    config cs ts ─→ₚ
    config (V.updateAt cs i
      (setEndpointFlags side (before ++ acq ∷ after)))
      (replaceAt ts j (F [ * ]*))

  RUS-Discard :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (F : Frame* (2 *ℕ n)) {e} →
    Value e →
    lookup ts j ≡ F [ K `discard ·¹ e ]* →
    config cs ts ─→ₚ config cs (replaceAt ts j (F [ * ]*))

  RUS-Acquire :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) (before after : List Flag) {e} →
    proj₁ (lookup cs i) ≡ true →
    endpointFlags (lookup cs i) side ≡ before ++ acq ∷ after →
    lookup ts j ≡
      F [ K `acq ·¹
          𝓒[ `phi (endpoint i side , L.length before) ×
             endpoint i side × e ] ]* →
    config cs ts ─→ₚ
    config (V.updateAt cs i (setEndpointFlags side (before ++ after)))
      (let x = endpoint i side
           k = L.length before
           ts′ = V.map (consumePhi x k) ts
       in replaceAt ts′ j
            (consumePhi x k (F [ 𝓒[ * × x × e ] ]*)))

  RUS-Close :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
      (F₁ F₂ : Frame* (2 *ℕ n)) {e₁ e₁′ e₂ e₂′} →
    j ≢ k →
    Opposite side₁ side₂ →
    lookup cs i ≡ (true , [] , []) →
    lookup ts j ≡
      F₁ [ K (`end ‼) ·¹ 𝓒[ e₁ × endpoint i side₁ × e₁′ ] ]* →
    lookup ts k ≡
      F₂ [ K (`end ⁇) ·¹ 𝓒[ e₂ × endpoint i side₂ × e₂′ ] ]* →
    config cs ts ─→ₚ
    config (replaceAt cs i (false , [] , []))
      (replaceTwo ts j (F₁ [ * ]*) k (F₂ [ * ]*))

  RUS-Com :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
      (F₁ F₂ : Frame* (2 *ℕ n)) {e e₁ e₁′ e₂ e₂′} →
    j ≢ k →
    Opposite side₁ side₂ →
    proj₁ (lookup cs i) ≡ true →
    Value e →
    lookup ts j ≡
      F₁ [ K `send ·¹ (e ⊗ 𝓒[ e₁ × endpoint i side₁ × e₁′ ]) ]* →
    lookup ts k ≡
      F₂ [ K `recv ·¹ 𝓒[ e₂ × endpoint i side₂ × e₂′ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceTwo ts j (F₁ [ * ]*) k (F₂ [ e ]*))

  RUS-Choice :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
      (F₁ F₂ : Frame* (2 *ℕ n)) (choice : Side)
      {e₁ e₁′ e₂ e₂′} →
    j ≢ k →
    Opposite side₁ side₂ →
    proj₁ (lookup cs i) ≡ true →
    lookup ts j ≡
      F₁ [ K (`select choice) ·¹
        𝓒[ e₁ × endpoint i side₁ × e₁′ ] ]* →
    lookup ts k ≡
      F₂ [ K `branch ·¹
        𝓒[ e₂ × endpoint i side₂ × e₂′ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceTwo ts
      j (F₁ [ 𝓒[ e₁ × endpoint i side₁ × e₁′ ] ]*)
      k (F₂ [ `inj choice
           𝓒[ e₂ × endpoint i side₂ × e₂′ ] ]*))
