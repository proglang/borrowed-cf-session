{-# OPTIONS --rewriting #-}
module BorrowedCF.Types.Predicates where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence

open Bin using (_Respects_)
open Nat.Variables

data Skips {n} : 𝕊 n → Set where
  skip : Skips skip
  _;_  : (S₁ : Skips s₁) (S₂ : Skips s₂) → Skips (s₁ ; s₂)
  mu   : (S : Skips s) → Skips (mu s)

≃-skips : Skips {n} Respects _≃_
≃-skips refl = id
≃-skips (x ◅ xs) = ≃-skips xs ∘ go x where
  go : SymClosure _≃𝕊_ s₁ s₂ → Skips s₁ → Skips s₂
  go (fwd ≃𝕊-μ) (mu s) = {!!}
  go (fwd (≃𝕊-;₁ x)) (s₁ ; s₂) = go (fwd x) s₁ ; s₂
  go (fwd (≃𝕊-;₂ x)) (s₁ ; s₂) = s₁ ; go (fwd x) s₂
  go (fwd ≃𝕊-skipˡ) (s₁ ; s₂) = s₂
  go (fwd ≃𝕊-skipʳ) (s₁ ; s₂) = s₁
  go (fwd ≃𝕊-assoc) ((s₁ ; s₂) ; s₃) = s₁ ; (s₂ ; s₃)
  go (fwd ≃𝕊-distr) (() ; _)
  go (bwd (≃𝕊-;₁ x)) (s₁ ; s₂) = go (bwd x) s₁ ; s₂
  go (bwd (≃𝕊-;₂ x)) (s₁ ; s₂) = s₁ ; go (bwd x) s₂
  go (bwd ≃𝕊-skipˡ) s = skip ; s
  go (bwd ≃𝕊-skipʳ) s = s ; skip
  go (bwd ≃𝕊-μ) s = {!!}
  go (bwd ≃𝕊-assoc) (s₁ ; (s₂ ; s₃)) = (s₁ ; s₂) ; s₃

skips⇒skip≃ : Skips s → skip ≃ s
skips⇒skip≃ skip = refl
skips⇒skip≃ {s = s₁ ; s₂} (sk ; sk₁) =
  let open ≃-Reasoning in
  begin skip         ≈⟨ ≃-skipˡ ⟨
        skip ; skip  ≈⟨ ≃-; (skips⇒skip≃ sk) (skips⇒skip≃ sk₁) ⟩
        s₁   ; s₂    ∎
skips⇒skip≃ (mu sk) = {!!}

skip≃⇒skips : skip ≃ s → Skips s
skip≃⇒skips eq = ≃-skips eq skip

-- data Bounded {n} : 𝕊 n → Set where
--   `_ : (x : 𝔽 n) → Bounded (` x)
--   end  : Bounded (end p)
--   ret  : Bounded ret
--   _;₁_ : Bounded s₁ → Skips s₂ → Bounded (s₁ ; s₂)
--   -;₂_ : Bounded s₂ → Bounded (s₁ ; s₂)
--   mu   : Bounded s → Bounded (mu s)
--   brn  : Bounded s₁ → Bounded s₂ → Bounded (brn p s₁ s₂)

-- ≃-bounded : Bounded {n} Respects _≃_
-- ≃-bounded refl = id
-- ≃-bounded (x ◅ xs) = ≃-bounded xs ∘ go x where
--   go : SymClosure _≃𝕊_ s₁ s₂ → Bounded s₁ → Bounded s₂
--   go (fwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (fwd x) b ;₁ x₁
--   go (fwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
--   go (fwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Eq*.return x) x₁
--   go (fwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (fwd x) b
--   go (fwd ≃𝕊-skipˡ) (-;₂ b) = b
--   go (fwd ≃𝕊-skipʳ) (b ;₁ x) = b
--   go (fwd ≃𝕊-assoc) ((b ;₁ x₁) ;₁ x) = b ;₁ (x₁ ; x)
--   go (fwd ≃𝕊-assoc) ((-;₂ b) ;₁ x) = -;₂ (b ;₁ x)
--   go (fwd ≃𝕊-assoc) (-;₂ b) = -;₂ (-;₂ b)
--   go (fwd ≃𝕊-distr) (brn b b₁ ;₁ x) = brn (b ;₁ x) (b₁ ;₁ x)
--   go (fwd ≃𝕊-distr) (-;₂ b) = brn (-;₂ b) (-;₂ b)
--   go (bwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (bwd x) b ;₁ x₁
--   go (bwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
--   go (bwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Star.return (bwd x)) x₁
--   go (bwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (bwd x) b
--   go (bwd ≃𝕊-skipˡ) b = -;₂ b
--   go (bwd ≃𝕊-skipʳ) b = b ;₁ skip
--   go (bwd ≃𝕊-assoc) (b ;₁ (x ; x₁)) = (b ;₁ x) ;₁ x₁
--   go (bwd ≃𝕊-assoc) (-;₂ (b ;₁ x)) = (-;₂ b) ;₁ x
--   go (bwd ≃𝕊-assoc) (-;₂ (-;₂ b)) = -;₂ b
--   go (bwd ≃𝕊-distr) (brn (b ;₁ x) (b₁ ;₁ x₁)) = brn b b₁ ;₁ x₁
--   go (bwd ≃𝕊-distr) (brn (b ;₁ x) (-;₂ b₁)) = -;₂ b₁
--   go (bwd ≃𝕊-distr) (brn (-;₂ b) b₁) = -;₂ b

-- data Mobile : 𝕋 → Set where
--   `⊤  : Mobile `⊤
--   arr : Arr.Mobile a → Mobile (T ⟨ a ⟩→ U)
--   acq : Bounded s → Mobile ⟨ acq ; s ⟩
--   skip : Skips s → Mobile ⟨ s ⟩
--   _⊗_ : Mobile T → Mobile U → Mobile (T ⊗⟨ d ⟩ U)

-- ≃-mobile : Mobile Respects _≃_
-- ≃-mobile `⊤ `⊤ = `⊤
-- ≃-mobile (eq ⊗ eq₁) (m ⊗ m₁) = (≃-mobile eq m) ⊗ (≃-mobile eq₁ m₁)
-- ≃-mobile (eq `→ eq₁) (arr x) = arr x
-- ≃-mobile ⟨ x ⟩ (acq x₁) = {!!}
-- ≃-mobile ⟨ x ⟩ (skip x₁) = {!!}

-- data Unr : 𝕋 → Set where
--   `⊤   : Unr `⊤
--   _⊗_  : Unr T → Unr U → Unr (T ⊗⟨ d ⟩ U)
--   arr  : Arr.Unr a → Unr (T ⟨ a ⟩→ U)
--   ⟨_⟩  : Skips s → Unr ⟨ s ⟩

-- Unr⇒Mobile : Unr T → Mobile T
-- Unr⇒Mobile `⊤ = `⊤
-- Unr⇒Mobile (T ⊗ U) = Unr⇒Mobile T ⊗ Unr⇒Mobile U
-- Unr⇒Mobile (arr {a} U) = arr (Arr.ω⇒M a U)
-- Unr⇒Mobile ⟨ s ⟩   = skip s

-- skips? : Un.Decidable (Skips {n})
-- skips? (` x) = no λ()
-- skips? (end p) = no λ()
-- skips? (msg p t) = no λ()
-- skips? (brn p s₁ s₂) = no λ()
-- skips? (mu s) = map′ mu (λ{ (mu x) → x }) (skips? s)
-- skips? (s₁ ; s₂) = map′ (uncurry _;_) (λ{ (x ; y) → (x , y) }) (skips? s₁ ×-dec skips? s₂)
-- skips? skip = yes skip
-- skips? ret = no λ()
-- skips? acq = no λ()
-- skips? (`` x) = no λ()

-- unr? : Un.Decidable Unr
-- unr? ⟨ s ⟩ = map′ ⟨_⟩ (λ{ ⟨ x ⟩ → x }) (skips? s)
-- unr? `⊤ = yes `⊤
-- unr? (t ⟨ a ⟩→ u) with Arr.lin a in eq
-- ... | 𝟙   = no λ{ (arr eq′) → case sym eq ■ eq′ of λ() }
-- ... | unr = yes (arr eq)
-- unr? (t ⊗⟨ d ⟩ u) = map′ (uncurry _⊗_) (λ{ (unrT ⊗ unrU) → unrT , unrU }) (unr? t ×-dec unr? u)
