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

-- Insert one phi cell.  `insertSlot k l` is the dual of `shiftSlot`: slots
-- below `k` keep their number, slots at or above `k` move up by one.
insertSlot : ℕ → ℕ → ℕ
insertSlot zero l = suc l
insertSlot (suc k) zero = zero
insertSlot (suc k) (suc l) = suc (insertSlot k l)

-- Renumber the phi cells of one endpoint after a new sync boundary has been
-- inserted at position `k`.  Dual to `consumePhi`, which removes cell `k`.
insertPhi : 𝔽 n → ℕ → Tm n → Tm n
insertPhi x k (` y) = ` y
insertPhi x k (`phi (y , l)) with x FinP.≟ y
... | no _ = `phi (y , l)
... | yes refl = `phi (x , insertSlot k l)
insertPhi x k (K c) = K c
insertPhi x k (ƛ e) = ƛ (insertPhi (suc x) k e)
insertPhi x k (μ e) = μ (insertPhi (suc x) k e)
insertPhi x k (e₁ ·⟨ d ⟩ e₂) =
  insertPhi x k e₁ ·⟨ d ⟩ insertPhi x k e₂
insertPhi x k (e₁ ; e₂) = insertPhi x k e₁ ; insertPhi x k e₂
insertPhi x k (e₁ ⊗ e₂) = insertPhi x k e₁ ⊗ insertPhi x k e₂
insertPhi x k (`let e₁ `in e₂) =
  `let insertPhi x k e₁ `in insertPhi (suc x) k e₂
insertPhi x k (`let⊗ e₁ `in e₂) =
  `let⊗ insertPhi x k e₁ `in insertPhi (suc (suc x)) k e₂
insertPhi x k (`inj side e) = `inj side (insertPhi x k e)
insertPhi x k (`case e `of⟨ e₁ ; e₂ ⟩) =
  `case insertPhi x k e
    `of⟨ insertPhi (suc x) k e₁ ; insertPhi (suc x) k e₂ ⟩

insertPhi-Value :
  (x : 𝔽 n) (k : ℕ) {e : Tm n} → Value e → Value (insertPhi x k e)
insertPhi-Value x k V-` = V-`
insertPhi-Value x k (V-phi {r = y , l}) with x FinP.≟ y
... | no _ = V-phi
... | yes refl = V-phi
insertPhi-Value x k V-K = V-K
insertPhi-Value x k V-λ = V-λ
insertPhi-Value x k (V-⊗ V₁ V₂) =
  V-⊗ (insertPhi-Value x k V₁) (insertPhi-Value x k V₂)
insertPhi-Value x k (V-⊕ V) = V-⊕ (insertPhi-Value x k V)

insertPhi-frame : 𝔽 n → ℕ → Frame n → Frame n
insertPhi-frame x k (app₁ e d V?) =
  app₁ (insertPhi x k e) d λ d≡L → insertPhi-Value x k (V? d≡L)
insertPhi-frame x k (app₂ e d V?) =
  app₂ (insertPhi x k e) d λ d≡→ → insertPhi-Value x k (V? d≡→)
insertPhi-frame x k (□⊗ e) = □⊗ (insertPhi x k e)
insertPhi-frame x k (V ⊗□) = insertPhi-Value x k V ⊗□
insertPhi-frame x k (□; e) = □; (insertPhi x k e)
insertPhi-frame x k (`let-`in e) = `let-`in (insertPhi (suc x) k e)
insertPhi-frame x k (`let⊗-`in e) = `let⊗-`in (insertPhi (suc (suc x)) k e)
insertPhi-frame x k (`inj□ i) = `inj□ i
insertPhi-frame x k (`case□`of⟨ e₁ ; e₂ ⟩) =
  `case□`of⟨ insertPhi (suc x) k e₁ ; insertPhi (suc x) k e₂ ⟩

insertPhi-frames : 𝔽 n → ℕ → Frame* n → Frame* n
insertPhi-frames x k [] = []
insertPhi-frames x k (F ∷ Fs) =
  insertPhi-frame x k F ∷ insertPhi-frames x k Fs

insertPhi-plug :
  (x : 𝔽 n) (k : ℕ) (F : Frame n) (t : Tm n) →
  insertPhi x k (F [ t ]) ≡ insertPhi-frame x k F [ insertPhi x k t ]
insertPhi-plug x k (app₁ e d V?) t = refl
insertPhi-plug x k (app₂ e d V?) t = refl
insertPhi-plug x k (□⊗ e) t = refl
insertPhi-plug x k (V ⊗□) t = refl
insertPhi-plug x k (□; e) t = refl
insertPhi-plug x k (`let-`in e) t = refl
insertPhi-plug x k (`let⊗-`in e) t = refl
insertPhi-plug x k (`inj□ i) t = refl
insertPhi-plug x k (`case□`of⟨ e₁ ; e₂ ⟩) t = refl

insertPhi-plug* :
  (x : 𝔽 n) (k : ℕ) (F : Frame* n) (t : Tm n) →
  insertPhi x k (F [ t ]*) ≡ insertPhi-frames x k F [ insertPhi x k t ]*
insertPhi-plug* x k [] t = refl
insertPhi-plug* x k (F ∷ Fs) t =
  insertPhi-plug x k F (Fs [ t ]*)
  ■ cong (insertPhi-frame x k F [_]) (insertPhi-plug* x k Fs t)

insertEndpoint : ∀ {n} → 𝔽 (suc n) → 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
insertEndpoint {n} i x
  with Fin.remQuot 2 (Fin.cast (Nat.*-comm 2 n) x)
... | c , side = endpoint (Fin.punchIn i c) side

insertThreadEndpoints : ∀ {n} → 𝔽 (suc n) → Thread n → Thread (suc n)
insertThreadEndpoints i e = e ⋯ᵣ insertEndpoint i

newResult : ∀ {n} → 𝔽 (suc n) → Frame* (2 *ℕ n) → Thread (suc n)
newResult i F =
  let l = leftEnd i
      r = rightEnd i
      c₀ = 𝓒[ `phi (l , 0) × l × * ]
      c₁ = 𝓒[ `phi (r , 0) × r × * ]
  in frames-rename F (insertEndpoint i) [ c₀ ⊗ c₁ ]*

data Opposite : 𝔽 2 → 𝔽 2 → Set where
  left-right : Opposite zero (suc zero)
  right-left : Opposite (suc zero) zero

-- created an abbrev for `proj₁ (lookup cs i) ≡ true` defined as
is-open : ∀ {n} → Vec Channel n → 𝔽 n → Set
is-open cs i = proj₁ (lookup cs i) ≡ true

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
      (j : 𝔽 m) (i : 𝔽 (suc n)) (F : Frame* (2 *ℕ n)) →
    lookup ts j ≡ F [ K (`new s) ·¹ * ]* →
    -- could be simplified by just putting the new channel at the end and weakening all threads
    config cs ts ─→ₚ
    config (V.insertAt cs i (true , acq ∷ [] , acq ∷ []))
      (replaceAt (V.map (insertThreadEndpoints i) ts) j (newResult i F))

  RUS-LSplit :
    ∀ {n m s} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) {e₁ e₂} →
    is-open cs i →
    lookup ts j ≡
      F [ K (`lsplit s) ·¹ 𝓒[ e₁ × endpoint i side × e₂ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceAt ts j
      (F [ 𝓒[ e₁ × endpoint i side × * ] ⊗
           𝓒[ * × endpoint i side × e₂ ] ]*))

  -- A right split inserts a *new* sync boundary at flag position `k`, where
  -- `k` is the number of boundaries that precede it on this endpoint (in the
  -- translation: the number of binder groups before the split one).  Every
  -- phi reference of the endpoint at slot `k` or above therefore moves up by
  -- one — in every thread of the soup, which is what `insertPhi` does; it is
  -- the exact dual of the `consumePhi` sweep of `RUS-Acquire`.  The two new
  -- handles carry the new boundary `phi (x , k)`.
  RUS-RSplit :
    ∀ {n m s} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) (before after : List Flag) {e₁ e₂} →
    is-open cs i →
    endpointFlags (lookup cs i) side ≡ before ++ after →
    lookup ts j ≡
      F [ K (`rsplit s) ·¹ 𝓒[ e₁ × endpoint i side × e₂ ] ]* →
    config cs ts ─→ₚ
    config (V.updateAt cs i (setEndpointFlags side (before ++ drop ∷ after)))
      (let x = endpoint i side
           k = L.length before
       in replaceAt (V.map (insertPhi x k) ts) j
            (insertPhi-frames x k F
              [ 𝓒[ insertPhi x k e₁ × x × `phi (x , k) ] ⊗
                𝓒[ `phi (x , k) × x × insertPhi x k e₂ ] ]*))

  RUS-Drop :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
      (F : Frame* (2 *ℕ n)) (before after : List Flag) →
    is-open cs i →
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
    is-open cs i →
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
      (F₁ F₂ : Frame* (2 *ℕ n)) →
    j ≢ k →
    Opposite side₁ side₂ →
    lookup cs i ≡ (true , [] , []) →
    lookup ts j ≡
      F₁ [ K (`end ‼) ·¹ 𝓒[ * × endpoint i side₁ × * ] ]* →
    lookup ts k ≡
      F₂ [ K (`end ⁇) ·¹ 𝓒[ * × endpoint i side₂ × * ] ]* →
    config cs ts ─→ₚ
    config (replaceAt cs i (false , [] , []))
      (replaceTwo ts j (F₁ [ * ]*) k (F₂ [ * ]*))

  RUS-Com :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
      (F₁ F₂ : Frame* (2 *ℕ n)) {e e₁′ e₂′} →
    j ≢ k →
    Opposite side₁ side₂ →
    is-open cs i →
    Value e →
    lookup ts j ≡
      F₁ [ K `send ·¹ (e ⊗ 𝓒[ * × endpoint i side₁ × e₁′ ]) ]* →
    lookup ts k ≡
      F₂ [ K `recv ·¹ 𝓒[ * × endpoint i side₂ × e₂′ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceTwo ts j (F₁ [ * ]*) k (F₂ [ e ]*))

  RUS-Choice :
    ∀ {n m} {cs : Vec Channel n} {ts : Vec (Thread n) m}
      (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
      (F₁ F₂ : Frame* (2 *ℕ n)) (choice : Side)
      {e₁′ e₂′} →
    j ≢ k →
    Opposite side₁ side₂ →
    is-open cs i →
    lookup ts j ≡
      F₁ [ K (`select choice) ·¹
        𝓒[ * × endpoint i side₁ × e₁′ ] ]* →
    lookup ts k ≡
      F₂ [ K `branch ·¹
        𝓒[ * × endpoint i side₂ × e₂′ ] ]* →
    config cs ts ─→ₚ
    config cs (replaceTwo ts
      j (F₁ [ 𝓒[ * × endpoint i side₁ × e₁′ ] ]*)
      k (F₂ [ `inj choice
           𝓒[ * × endpoint i side₂ × e₂′ ] ]*))
