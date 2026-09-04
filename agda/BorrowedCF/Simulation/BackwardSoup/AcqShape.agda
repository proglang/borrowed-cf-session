-- | Binder-group shape forced by an acquire boundary.
module BorrowedCF.Simulation.BackwardSoup.AcqShape where

open import Data.List.Relation.Unary.All as Allᴸ
  using ([]; _∷_) renaming (All to Allᴸ)
open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Local.SplitCommon
  using ( bindFlags; pick-pos; Ub-entry; UBFrom-cons-lo; UBFrom-lookupʳ
        ; UB-flags-shape)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (GroupOf; head-group; next-group)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (AcqShape; acq-l; acq-r)

open Fin.Patterns

private
  phi-slot-miss :
    {n : ℕ} {r : 𝔽 n} {slot : ℕ} →
    slot ≢ zero →
    SoupTerm.`phi (r , slot) ≢ SoupTerm.`phi (r , zero)
  phi-slot-miss slot≠0 refl = slot≠0 refl

  star-phi-miss :
    {n : ℕ} {r : 𝔽 n} {slot : ℕ} →
    SoupTerm.* ≢ SoupTerm.`phi (r , slot)
  star-phi-miss ()

  ub-left-miss :
    {n b : ℕ} {left right tail : SoupTerm.Tm n}
    {c r : 𝔽 n} →
    left ≢ SoupTerm.`phi (r , zero) →
    (i : 𝔽 b) →
    Translation.Ub[ b ] (left , c , right) i ≢
    Translation.chanTriple (SoupTerm.`phi (r , zero) , r , tail)
  ub-left-miss {b = zero} left≠ ()
  ub-left-miss {b = suc zero} left≠ zero equal =
    left≠ (proj₁ (chanTriple-injective equal))
  ub-left-miss {b = suc (suc b)} left≠ zero equal =
    left≠ (proj₁ (chanTriple-injective equal))
  ub-left-miss {b = suc (suc b)} left≠ (suc i) equal =
    ub-left-miss (λ ()) i equal

  ub-positive-index-miss :
    {n w : ℕ} {left right tail : SoupTerm.Tm n}
    {c r : 𝔽 n} →
    (i : 𝔽 w) →
    zero Nat.< Fin.toℕ i →
    Translation.Ub[ w ] (left , c , right) i ≢
    Translation.chanTriple (SoupTerm.`phi (r , zero) , r , tail)
  ub-positive-index-miss {w = w} {left = left} {right = right}
    {c = c} {r = r} i positive equal =
    star-phi-miss
      (sym (pick-pos (Fin.toℕ i) left positive)
       ■ proj₁
          (chanTriple-injective
            (sym (Ub-entry w c left right i) ■ equal)))

  ub-from-group-miss :
    {n : ℕ} (slot : ℕ) → slot ≢ zero →
    (B : Typed.BindGroup) (r c : 𝔽 n) (right tail : SoupTerm.Tm n) →
    (i : 𝔽 (sum B)) →
    GroupOf B i →
    proj₁
      (Translation.UBFrom (suc slot) B r
        (SoupTerm.`phi (r , slot) , c , right)) i ≢
    Translation.chanTriple (SoupTerm.`phi (r , zero) , r , tail)
  ub-from-group-miss slot slot≠0 [] r c right tail i ()
  ub-from-group-miss slot slot≠0 (b ∷ []) r c right tail .(j ↑ˡ 0)
    (head-group .[] j) =
    ub-left-miss (phi-slot-miss slot≠0) (j ↑ˡ 0)
  ub-from-group-miss slot slot≠0 (b ∷ b′ ∷ B′) r c right tail
    .(j ↑ˡ sum (b′ ∷ B′)) (head-group .(b′ ∷ B′) j) equal =
    ub-left-miss (phi-slot-miss slot≠0) j
      (sym
        (UBFrom-cons-lo (suc slot) b b′ B′ r c
          (SoupTerm.`phi (r , slot)) right
          (j ↑ˡ sum (b′ ∷ B′)) j
          (Fin.toℕ-↑ˡ j (sum (b′ ∷ B′))))
       ■ equal)
  ub-from-group-miss slot slot≠0 (b ∷ []) r c right tail i
    (next-group .b ()) equal
  ub-from-group-miss slot slot≠0 (b ∷ b′ ∷ B′) r c right tail
    .(b ↑ʳ i) (next-group .b {i = i} g) equal =
    ub-from-group-miss (suc slot) (λ ()) (b′ ∷ B′) r c right tail i g
      (sym
        (UBFrom-lookupʳ (suc slot) b (b′ ∷ B′) r c
          (SoupTerm.`phi (r , slot)) right i)
       ■ equal)

  all-positive-no-acq :
    {B : Typed.BindGroup} →
    Allᴸ NonZero B →
    (before after : List Soup.Flag) →
    bindFlags B ≢ before ++ Soup.acq ∷ after
  all-positive-no-acq {B = []} all [] after ()
  all-positive-no-acq {B = []} all (f ∷ before) after ()
  all-positive-no-acq {B = b ∷ []} all [] after ()
  all-positive-no-acq {B = b ∷ []} all (f ∷ before) after ()
  all-positive-no-acq {B = zero ∷ b ∷ B} (() ∷ all) before after
  all-positive-no-acq {B = suc a ∷ b ∷ B} (nz ∷ all) [] after ()
  all-positive-no-acq {B = suc a ∷ b ∷ B} (nz ∷ all)
    (f ∷ before) after equal =
    all-positive-no-acq all before after (L.∷-injectiveʳ equal)

-- In a well-formed binder group only the first group may have width zero.
-- Hence an `acq` boundary in its translated flag list is necessarily the
-- boundary from that first empty group to a nonempty second group.
acq-flag-shape :
  (B : Typed.BindGroup) →
  Typed.⊢ᴮ B →
  (before after : List Soup.Flag) →
  bindFlags B ≡ before ++ Soup.acq ∷ after →
  Σ[ b ∈ ℕ ] Σ[ B′ ∈ Typed.BindGroup ]
    (B ≡ zero ∷ suc b ∷ B′) × (before ≡ [])
acq-flag-shape [] typed [] after ()
acq-flag-shape [] typed (f ∷ before) after ()
acq-flag-shape (a ∷ []) typed [] after ()
acq-flag-shape (a ∷ []) typed (f ∷ before) after ()
acq-flag-shape (zero ∷ zero ∷ B) (() ∷ typed) before after equal
acq-flag-shape (zero ∷ suc b ∷ B) (nz ∷ typed) [] after equal =
  b , B , refl , refl
acq-flag-shape (suc a ∷ b ∷ B) typed [] after ()
acq-flag-shape (a ∷ b ∷ B) typed (f ∷ before) after equal =
  ⊥-elim
    (all-positive-no-acq typed before after (L.∷-injectiveʳ equal))

-- Once the flag shape has exposed `0 :: suc b :: B`, the entry carrying
-- the boundary token at slot zero is uniquely the head of the second group.
acq-entry-zero :
  {n : ℕ} (b : ℕ) (B : Typed.BindGroup) (r : 𝔽 n)
  (i : 𝔽 (sum (zero ∷ suc b ∷ B)))
  (g : GroupOf (zero ∷ suc b ∷ B) i) →
  {tail : SoupTerm.Tm n} →
  proj₁
    (Translation.UB[ zero ∷ suc b ∷ B ] r
      (SoupTerm.* , r , SoupTerm.*)) i ≡
  Translation.chanTriple (SoupTerm.`phi (r , zero) , r , tail) →
  i ≡ 0F
acq-entry-zero b B r i (head-group .(suc b ∷ B) ()) equal
acq-entry-zero b B r i (next-group .zero (head-group .B zero)) equal = refl
acq-entry-zero b [] r i
  (next-group .zero (head-group .[] (suc j))) equal =
  ⊥-elim
    (ub-positive-index-miss (suc j ↑ˡ 0)
      (subst (zero Nat.<_)
        (sym (Fin.toℕ-↑ˡ (suc j) 0))
        (Nat.s≤s Nat.z≤n))
      (sym
        (UBFrom-lookupʳ 0 0 (suc b ∷ []) r r SoupTerm.* SoupTerm.*
          (suc j ↑ˡ 0))
       ■ equal))
acq-entry-zero b (c ∷ C) r i
  (next-group .zero (head-group .(c ∷ C) (suc j))) equal =
  ⊥-elim
    (ub-positive-index-miss (suc j) (Nat.s≤s Nat.z≤n)
      (sym
        (UBFrom-cons-lo 1 (suc b) c C r r
          (SoupTerm.`phi (r , zero)) SoupTerm.*
          (suc j ↑ˡ sum (c ∷ C)) (suc j)
          (Fin.toℕ-↑ˡ (suc j) (sum (c ∷ C))))
       ■ sym
          (UBFrom-lookupʳ 0 0 (suc b ∷ c ∷ C) r r
            SoupTerm.* SoupTerm.*
            (suc j ↑ˡ sum (c ∷ C)))
       ■ equal))
acq-entry-zero b [] r i (next-group .zero (next-group .(suc b) ())) equal
acq-entry-zero b (c ∷ C) r i
  (next-group .zero (next-group .(suc b) {i = k} g)) {tail} equal =
  ⊥-elim
    (ub-from-group-miss 1 (λ ()) (c ∷ C) r r SoupTerm.* tail k g
      (sym
        (UBFrom-lookupʳ 1 (suc b) (c ∷ C) r r
          (SoupTerm.`phi (r , zero)) SoupTerm.* k)
       ■ sym
          (UBFrom-lookupʳ 0 0 (suc b ∷ c ∷ C) r r
            SoupTerm.* SoupTerm.* (suc b ↑ʳ k))
       ■ equal))

acq-shape-left :
  {n : ℕ} (B₁ B₂ : Typed.BindGroup) →
  Typed.⊢ᴮ B₁ →
  (r : 𝔽 n) (i : 𝔽 (sum B₁)) →
  GroupOf B₁ i →
  (before after : List Soup.Flag) →
  {tail : SoupTerm.Tm n} →
  proj₂
    (Translation.UB[ B₁ ] r (SoupTerm.* , r , SoupTerm.*)) ≡
    before ++ Soup.acq ∷ after →
  proj₁
    (Translation.UB[ B₁ ] r (SoupTerm.* , r , SoupTerm.*)) i ≡
    Translation.chanTriple
      (SoupTerm.`phi (r , L.length before) , r , tail) →
  AcqShape B₁ B₂ (i ↑ˡ sum B₂)
acq-shape-left B₁ B₂ typed r i group before after flagsEq entryEq
  with acq-flag-shape B₁ typed before after
         (sym (UB-flags-shape B₁ r r SoupTerm.* SoupTerm.*) ■ flagsEq)
... | b , B′ , refl , refl
  with acq-entry-zero b B′ r i group entryEq
... | refl = acq-l b B′ B₂

acq-shape-right :
  {n : ℕ} (B₁ B₂ : Typed.BindGroup) →
  Typed.⊢ᴮ B₂ →
  (r : 𝔽 n) (i : 𝔽 (sum B₂)) →
  GroupOf B₂ i →
  (before after : List Soup.Flag) →
  {tail : SoupTerm.Tm n} →
  proj₂
    (Translation.UB[ B₂ ] r (SoupTerm.* , r , SoupTerm.*)) ≡
    before ++ Soup.acq ∷ after →
  proj₁
    (Translation.UB[ B₂ ] r (SoupTerm.* , r , SoupTerm.*)) i ≡
    Translation.chanTriple
      (SoupTerm.`phi (r , L.length before) , r , tail) →
  AcqShape B₁ B₂ (sum B₁ ↑ʳ i)
acq-shape-right B₁ B₂ typed r i group before after flagsEq entryEq
  with acq-flag-shape B₂ typed before after
         (sym (UB-flags-shape B₂ r r SoupTerm.* SoupTerm.*) ■ flagsEq)
... | b , B′ , refl , refl
  with acq-entry-zero b B′ r i group entryEq
... | refl = acq-r B₁ b B′
