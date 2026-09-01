module BorrowedCF.Reduction.Processes.UntypedSoup.Properties where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Base as FinBase
import Data.Fin.Permutation as Perm
import Data.Fin.Properties as FinP
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup
open import BorrowedCF.Processes.UntypedSoup
open import BorrowedCF.Reduction.ExpressionsSoup
open import BorrowedCF.Reduction.Processes.UntypedSoup

open Nat.Variables
open Perm using (Permutation′; _⟨$⟩ʳ_; _⟨$⟩ˡ_)

private
  variable
    A B : Set

permuteVec : Permutation′ n → Vec A n → Vec A n
permuteVec pi xs = V.tabulate λ i → lookup xs (pi ⟨$⟩ʳ i)

permuteConfig : Permutation′ m → Config n m → Config n m
permuteConfig pi (config cs ts) = config cs (permuteVec pi ts)

lookup-permute :
  (pi : Permutation′ n) (xs : Vec A n) (i : 𝔽 n) →
  lookup (permuteVec pi xs) (pi ⟨$⟩ˡ i) ≡ lookup xs i
lookup-permute pi xs i =
  VecP.lookup∘tabulate (λ j → lookup xs (pi ⟨$⟩ʳ j)) (pi ⟨$⟩ˡ i) ■
  cong (lookup xs) (Perm.inverseʳ pi)

permuteVec-ext :
  {xs ys : Vec A n} →
  (∀ i → lookup xs i ≡ lookup ys i) →
  xs ≡ ys
permuteVec-ext {xs = xs} {ys = ys} p =
  sym (VecP.tabulate∘lookup xs) ■
  VecP.tabulate-cong p ■
  VecP.tabulate∘lookup ys

permute-replace :
  (pi : Permutation′ n) (xs : Vec A n) (i : 𝔽 n) (x : A) →
  replaceAt (permuteVec pi xs) (pi ⟨$⟩ˡ i) x ≡
  permuteVec pi (replaceAt xs i x)
permute-replace pi xs i x = permuteVec-ext pointwise
  where
  i′ = pi ⟨$⟩ˡ i

  pointwise : ∀ j →
    lookup (replaceAt (permuteVec pi xs) i′ x) j ≡
    lookup (permuteVec pi (replaceAt xs i x)) j
  pointwise j with FinP._≟_ j i′
  ... | yes refl =
    VecP.lookup∘updateAt i′ (permuteVec pi xs) ■
    sym
      (cong (λ k → lookup (replaceAt xs i x) k) (Perm.inverseʳ pi) ■
       VecP.lookup∘updateAt i xs) ■
    sym (VecP.lookup∘tabulate (λ k → lookup (replaceAt xs i x) (pi ⟨$⟩ʳ k)) i′)
  ... | no j≢i′ =
    VecP.lookup∘updateAt′ j i′ j≢i′ (permuteVec pi xs) ■
    VecP.lookup∘tabulate (λ k → lookup xs (pi ⟨$⟩ʳ k)) j ■
    sym (VecP.lookup∘updateAt′ (pi ⟨$⟩ʳ j) i piʳj≢i xs) ■
    sym (VecP.lookup∘tabulate (λ k → lookup (replaceAt xs i x) (pi ⟨$⟩ʳ k)) j)
    where
    piʳj≢i : pi ⟨$⟩ʳ j ≢ i
    piʳj≢i eq = j≢i′ (sym (Perm.inverseˡ pi) ■ cong (pi ⟨$⟩ˡ_) eq)

permute-replace-map :
  (f : A → B) (pi : Permutation′ n) (xs : Vec A n) (i : 𝔽 n) (x : B) →
  replaceAt (V.map f (permuteVec pi xs)) (pi ⟨$⟩ˡ i) x ≡
  permuteVec pi (replaceAt (V.map f xs) i x)
permute-replace-map f pi xs i x =
  cong (λ ys → replaceAt ys (pi ⟨$⟩ˡ i) x) (map-permute f pi xs) ■
  permute-replace pi (V.map f xs) i x
  where
  map-permute : (f : A → B) (pi : Permutation′ n) (xs : Vec A n) →
    V.map f (permuteVec pi xs) ≡ permuteVec pi (V.map f xs)
  map-permute f pi xs = permuteVec-ext λ j →
    VecP.lookup-map j f (permuteVec pi xs) ■
    cong f (VecP.lookup∘tabulate (λ k → lookup xs (pi ⟨$⟩ʳ k)) j) ■
    sym (VecP.lookup-map (pi ⟨$⟩ʳ j) f xs) ■
    sym (VecP.lookup∘tabulate (λ k → lookup (V.map f xs) (pi ⟨$⟩ʳ k)) j)

permute-replace-two :
  (pi : Permutation′ n) (xs : Vec A n)
  (i j : 𝔽 n) (x y : A) →
  i ≢ j →
  replaceTwo (permuteVec pi xs) (pi ⟨$⟩ˡ i) x (pi ⟨$⟩ˡ j) y ≡
  permuteVec pi (replaceTwo xs i x j y)
permute-replace-two pi xs i j x y i≢j =
  cong (λ ys → replaceAt ys (pi ⟨$⟩ˡ j) y)
    (permute-replace pi xs i x) ■
  permute-replace pi (replaceAt xs i x) j y

permute-neq :
  (pi : Permutation′ n) {i j : 𝔽 n} →
  i ≢ j → pi ⟨$⟩ˡ i ≢ pi ⟨$⟩ˡ j
permute-neq pi i≢j eq = i≢j (sym (Perm.inverseʳ pi) ■ cong (pi ⟨$⟩ʳ_) eq ■ Perm.inverseʳ pi)

insert-hit :
  (i j : 𝔽 (suc n)) (pi : Permutation′ n) →
  Perm.insert i j pi ⟨$⟩ʳ i ≡ j
insert-hit i j pi rewrite FinP.≟-≡-refl i = refl

permute-insertAfter-replace :
  (pi : Permutation′ n) (xs : Vec A n) (i : 𝔽 n) (x y : A) →
  let i′ = pi ⟨$⟩ˡ i
      pi′ = Perm.insert (suc i′) (suc i) pi
  in
  insertAfter (replaceAt (permuteVec pi xs) i′ x) i′ y ≡
  permuteVec pi′ (insertAfter (replaceAt xs i x) i y)
permute-insertAfter-replace pi xs i x y = permuteVec-ext pointwise
  where
  i′ = pi ⟨$⟩ˡ i
  pi′ = Perm.insert (suc i′) (suc i) pi
  lhs = insertAfter (replaceAt (permuteVec pi xs) i′ x) i′ y
  rhs = insertAfter (replaceAt xs i x) i y

  pointwise : ∀ k → lookup lhs k ≡ lookup (permuteVec pi′ rhs) k
  pointwise k with FinP._≟_ k (suc i′)
  ... | yes refl =
    VecP.insertAt-lookup (replaceAt (permuteVec pi xs) i′ x) (suc i′) y ■
    sym
      (cong (λ l → lookup rhs l) (insert-hit (suc i′) (suc i) pi) ■
       VecP.insertAt-lookup (replaceAt xs i x) (suc i) y) ■
    sym (VecP.lookup∘tabulate (λ l → lookup rhs (pi′ ⟨$⟩ʳ l)) (suc i′))
  ... | no k≢ =
    cong (lookup lhs) (sym (FinP.punchIn-punchOut pos≢k)) ■
    VecP.insertAt-punchIn (replaceAt (permuteVec pi xs) i′ x) (suc i′) y l ■
    cong (λ ys → lookup ys l) (permute-replace pi xs i x) ■
    VecP.lookup∘tabulate (λ q → lookup (replaceAt xs i x) (pi ⟨$⟩ʳ q)) l ■
    sym (VecP.insertAt-punchIn (replaceAt xs i x) (suc i) y (pi ⟨$⟩ʳ l)) ■
    sym (cong (lookup rhs) (Perm.insert-punchIn (suc i′) (suc i) pi l)) ■
    sym (VecP.lookup∘tabulate (λ q → lookup rhs (pi′ ⟨$⟩ʳ q))
      (FinBase.punchIn (suc i′) l)) ■
    cong (lookup (permuteVec pi′ rhs)) (FinP.punchIn-punchOut pos≢k)
    where
    pos≢k : suc i′ ≢ k
    pos≢k = k≢ ∘ sym

    l = FinBase.punchOut pos≢k

permute-step :
  (pi : Permutation′ m) →
  {C : Config n m} {C′ : Config n′ m′} →
  C ─→ₚ C′ →
  Σ[ pi′ ∈ Permutation′ m′ ]
    permuteConfig pi C ─→ₚ permuteConfig pi′ C′
permute-step pi (RUS-Exp {cs = cs} {ts = ts} j e→e′) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs) (permute-replace pi ts j _))
    (RUS-Exp (pi ⟨$⟩ˡ j)
      (subst (_⋯→ _) (sym (lookup-permute pi ts j)) e→e′))
permute-step pi (RUS-Fork {cs = cs} {ts = ts} j F V eq) =
  let j′ = pi ⟨$⟩ˡ j
      pi′ = Perm.insert (suc j′) (suc j) pi
  in
  pi′ ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs)
      (permute-insertAfter-replace pi ts j (F [ * ]*) (_ ·¹ *)))
    (RUS-Fork j′ F V (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-New {n = n} {cs = cs} {ts = ts} j i F eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config (V.insertAt cs i (true , acq ∷ [] , acq ∷ [])))
      (permute-replace-map (insertThreadEndpoints {n = n} i) pi ts j
        (newResult {n = n} i F)))
    (RUS-New (pi ⟨$⟩ˡ j) i F
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-LSplit {cs = cs} {ts = ts} j i side F live eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs) (permute-replace pi ts j _))
    (RUS-LSplit (pi ⟨$⟩ˡ j) i side F live
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-RSplit {cs = cs} {ts = ts} j i side F live eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config (V.updateAt cs i (appendEndpointFlag side drop)))
      (permute-replace pi ts j _))
    (RUS-RSplit (pi ⟨$⟩ˡ j) i side F live
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-Drop {cs = cs} {ts = ts} j i side F before after live fs eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config (V.updateAt cs i (setEndpointFlags side (before ++ acq ∷ after))))
      (permute-replace pi ts j _))
    (RUS-Drop (pi ⟨$⟩ˡ j) i side F before after live fs
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-Discard {cs = cs} {ts = ts} j F V eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs) (permute-replace pi ts j _))
    (RUS-Discard (pi ⟨$⟩ˡ j) F V
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-Acquire {cs = cs} {ts = ts} j i side F before after live fs eq) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config (V.updateAt cs i (setEndpointFlags side (before ++ after))))
      (permute-replace-map (consumePhi (endpoint i side) (L.length before))
        pi ts j (consumePhi (endpoint i side) (L.length before)
          (F [ 𝓒[ * × endpoint i side × _ ] ]*))))
    (RUS-Acquire (pi ⟨$⟩ˡ j) i side F before after live fs
      (lookup-permute pi ts j ■ eq))
permute-step pi (RUS-Close {cs = cs} {ts = ts} j k i side₁ side₂ F₁ F₂ j≢k opp ch eq₁ eq₂) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config (replaceAt cs i (false , [] , [])))
      (permute-replace-two pi ts j k (F₁ [ * ]*) (F₂ [ * ]*) j≢k))
    (RUS-Close (pi ⟨$⟩ˡ j) (pi ⟨$⟩ˡ k) i side₁ side₂ F₁ F₂
      (permute-neq pi j≢k) opp ch
      (lookup-permute pi ts j ■ eq₁)
      (lookup-permute pi ts k ■ eq₂))
permute-step pi (RUS-Com {cs = cs} {ts = ts} j k i side₁ side₂ F₁ F₂ j≢k opp live V eq₁ eq₂) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs)
      (permute-replace-two pi ts j k (F₁ [ * ]*) (F₂ [ _ ]*) j≢k))
    (RUS-Com (pi ⟨$⟩ˡ j) (pi ⟨$⟩ˡ k) i side₁ side₂ F₁ F₂
      (permute-neq pi j≢k) opp live V
      (lookup-permute pi ts j ■ eq₁)
      (lookup-permute pi ts k ■ eq₂))
permute-step pi (RUS-Choice {cs = cs} {ts = ts} j k i side₁ side₂ F₁ F₂ choice j≢k opp live eq₁ eq₂) =
  pi ,
  subst (config cs (permuteVec pi ts) ─→ₚ_)
    (cong (config cs)
      (permute-replace-two pi ts j k
        (F₁ [ 𝓒[ _ × endpoint i side₁ × _ ] ]*)
        (F₂ [ `inj choice 𝓒[ _ × endpoint i side₂ × _ ] ]*) j≢k))
    (RUS-Choice (pi ⟨$⟩ˡ j) (pi ⟨$⟩ˡ k) i side₁ side₂ F₁ F₂ choice
      (permute-neq pi j≢k) opp live
      (lookup-permute pi ts j ■ eq₁)
      (lookup-permute pi ts k ■ eq₂))
