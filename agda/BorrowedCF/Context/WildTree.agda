module BorrowedCF.Context.WildTree where

open import BorrowedCF.Prelude

open L using (length)
open Nat using (_>_)
open Un using (_∩_)

open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as IfJust using (just; nothing) renaming (All to IfJust)
open import Data.List.Relation.Unary.All as All* using ([]; _∷_) renaming (All to All*)
open import Data.List.Relation.Unary.All.Properties as All* using ()
open import Data.List.Relation.Unary.Any as Any* using (here; there) renaming (Any to Any*)
open import Data.List.Relation.Unary.Any.Properties as Any* using ()

private variable
  n n₁ n₂ l l₁ l₂ p q ℓ : Level
  N N₁ N₂ N′ : Set n
  L L₁ L₂ L′ : Set l
  P : Pred L p
  Q : Pred L q

data WideTree (N : Set n) (L : Set l) : Set (n ⊔ℓ l) where
  leaf : L → WideTree N L
  node : N → (ts : List (WideTree N L)) → .(length ts > 1) → WideTree N L

label : WideTree N L → Maybe N
label (leaf _) = nothing
label (node n _ _) = just n

map  : (N → N′) → (L → L′) → WideTree N L → WideTree N′ L′

map* : (N → N′) → (L → L′) → (xs : List (WideTree N L)) → Σ[ ys ∈ List (WideTree N′ L′) ] length xs ≡ length ys
map* f g [] = [] , refl
map* f g (t ∷ ts) = let ts′ , p = map* f g ts in map f g t ∷ ts′ , cong suc p

map f g (leaf x) = leaf (g x)
map f g (node n ts pₙ) = let ts′ , p = map* f g ts in node (f n) ts′ (subst (_> 1) p pₙ)

map*-map : {f : N → N′} {g : L → L′} → proj₁ ∘ map* f g ≗ L.map (map f g)
map*-map [] = refl
map*-map (x ∷ xs) = cong (_ ∷_) (map*-map xs)

mapᴸ : (L → L′) → WideTree N L → WideTree N L′
mapᴸ = map (λ x → x)

leaves : WideTree N L → List L
catLeaves : List (WideTree N L) → List L

leaves (leaf x) = L.[ x ]
leaves (node _ ts _) = catLeaves ts

catLeaves [] = []
catLeaves (t ∷ ts) = leaves t L.++ catLeaves ts

catLeaves-≡ : catLeaves {N = N} {L = L} ≗ L.concatMap leaves
catLeaves-≡ [] = refl
catLeaves-≡ (t ∷ ts) = cong (leaves t ++_) (catLeaves-≡ ts)

IsLeaf : Pred (WideTree N L) _
IsLeaf t = ∃ λ x → t ≡ leaf x

data Any {N : Set n} {L : Set l} (P : Pred L p) : Pred (WideTree N L) (n ⊔ℓ l ⊔ℓ p) where
  leaf : ∀ {x} → P x → Any P (leaf x)
  node : ∀ {n ts} → Any* (Any P) ts → ∀ .p → Any P (node n ts p)

any-map⁻  : ∀ {f : N → N′} {g : L → L′} {t : WideTree N L} → Any P (map f g t) → Any (P ∘ g) t
any-map*⁻ : ∀ {f : N → N′} {g : L → L′} {ts : List (WideTree N L)} →
  Any* (Any P) (map* f g ts .proj₁) →
  Any* (Any (P ∘ g)) ts

any-map⁻ {t = leaf _}      (leaf x)   = leaf x
any-map⁻ {t = node _ ts n} (node x _) = node (any-map*⁻ x) n

any-map*⁻ {ts = _ ∷ ts} (here x)  = here (any-map⁻ x)
any-map*⁻ {ts = _ ∷ ts} (there x) = there (any-map*⁻ x)

data Layered {N : Set n} {L : Set l} (R : Rel N ℓ) : Pred (WideTree N L) (n ⊔ℓ l ⊔ℓ ℓ) where
  leaf : ∀ {x} → Layered R (leaf x)
  node : ∀ {n ts} .{p} → All* (IfJust (R n) ∘ label ∩ Layered R) ts → Layered R (node n ts p)
