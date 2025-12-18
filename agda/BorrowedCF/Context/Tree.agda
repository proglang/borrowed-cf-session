module BorrowedCF.Context.Tree where

open import BorrowedCF.Prelude

open import Data.Unit using (⊤)
open import Data.Tree.Binary
open import Data.Tree.Binary.Properties

private variable
  n l p q : Level
  N N₁ N₂ N₃ : Set n
  L L₁ L₂ L₃ : Set l

Shape : Set
Shape = Tree ⊤ ⊤

shape : Tree N L → Shape
shape = map (const _) (const _)

shape-Shape : (S : Shape) → shape S ≡ S
shape-Shape = map-id

shape-idemp : (T : Tree N L) → shape (shape T) ≡ shape T
shape-idemp = shape-Shape ∘ shape

ext1 : Shape → Shape
ext1 S = node S _ (leaf _)

ext2 : Shape → Shape
ext2 S = node S _ (node (leaf _) _ (leaf _))

data Any {N : Set n} {L : Set l} (P : Pred N p) (Q : Pred L q) : Tree N L → Set (n ⊔ℓ l ⊔ℓ p ⊔ℓ q) where
  leaf  : ∀ {x}     → Q x → Any P Q (leaf x)
  node  : ∀ {l x r} → P x → Any P Q (node l x r)
  left  : ∀ {l x r} → Any P Q l → Any P Q (node l x r)
  right : ∀ {l x r} → Any P Q r → Any P Q (node l x r)

Leaf : Pred (Tree N L) _
Leaf = Any (const ⊥) (const ⊤)
