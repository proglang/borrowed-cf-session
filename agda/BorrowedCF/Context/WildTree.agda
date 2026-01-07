module BorrowedCF.Context.WildTree where

open import BorrowedCF.Prelude

open L using (length)
open Nat using (_>_)
open Un using (_∩_)

open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as IfJust using (just; nothing) renaming (All to IfJust)
open import Data.Maybe.Relation.Unary.All.Properties as IfJust using ()
open import Data.List.NonEmpty as L⁺ using (List⁺; _∷_)
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

mk : N → List⁺ (WideTree N L) → WideTree N L
mk n (x ∷ []) = x
mk n (x ∷ y ∷ zs) = node n (x ∷ y ∷ zs) Nat.sz<ss

leaf-injective : {x y : L} → leaf {N = N} x ≡ leaf y → x ≡ y
leaf-injective refl = refl

node-injective : {x y : N} {ts us : List (WideTree N L)} .{p : length ts > 1} .{q : length us > 1} →
  node x ts p ≡ node y us q → x ≡ y × ts ≡ us
node-injective refl = refl , refl

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

map-injective  : {f : N → N′} {g : L → L′} →
  Injective _≡_ _≡_ f → Injective _≡_ _≡_ g → Injective _≡_ _≡_ (map f g)
map*-injective : {f : N → N′} {g : L → L′} →
  Injective _≡_ _≡_ f → Injective _≡_ _≡_ g → Injective _≡_ _≡_ (proj₁ ∘ map* f g)

cong-node : {n₁ n₂ : N} {ts₁ ts₂ : List (WideTree N L)} →
  n₁ ≡ n₂ → ts₁ ≡ ts₂ → ∀ .p₁ .p₂ → node n₁ ts₁ p₁ ≡ node n₂ ts₂ p₂
cong-node refl refl _ _ = refl

map-injective f g {leaf x}      {leaf y}      eq = cong leaf (g (leaf-injective eq))
map-injective f g {node x ts p} {node y us q} eq =
  cong-node (f (node-injective eq .proj₁)) (map*-injective f g (node-injective eq .proj₂)) p q

map*-injective f g {[]}     {[]}     eq = refl
map*-injective f g {x ∷ xs} {y ∷ ys} eq =
  cong₂ _∷_ (map-injective f g (L.∷-injective eq .proj₁))
            (map*-injective f g {xs} {ys} (L.∷-injective eq .proj₂))

label : WideTree N L → Maybe N
label (leaf _) = nothing
label (node n _ _) = just n

label-map : {f : N → N′} {g : L → L′} → label ∘ map f g ≗ May.map f ∘ label
label-map (leaf x) = refl
label-map (node n ts p) = refl

leaves : WideTree N L → List L
catLeaves : List (WideTree N L) → List L

leaves (leaf x) = L.[ x ]
leaves (node _ ts _) = catLeaves ts

catLeaves [] = []
catLeaves (t ∷ ts) = leaves t L.++ catLeaves ts

catLeaves-≡ : catLeaves {N = N} {L = L} ≗ L.concatMap leaves
catLeaves-≡ [] = refl
catLeaves-≡ (t ∷ ts) = cong (leaves t ++_) (catLeaves-≡ ts)

leaves-map  : {f : N → N′} {g : L → L′} → leaves ∘ map f g ≗ L.map g ∘ leaves
leaves-map* : {f : N → N′} {g : L → L′} → catLeaves ∘ proj₁ ∘ map* f g ≗ L.map g ∘ catLeaves

leaves-map (leaf x) = refl
leaves-map {f = f} {g} (node n ts p) = leaves-map* ts

leaves-map* [] = refl
leaves-map* (t ∷ ts) = cong₂ _++_ (leaves-map t) (leaves-map* ts) ■ sym (L.map-++ _ (leaves t) (catLeaves ts))

dcong₂-irr : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} (f : (x : A) → .(B x) → C) {x₁ x₂} →
  x₁ ≡ x₂ →
  ∀ y₁ y₂ →
  f x₁ y₁ ≡ f x₂ y₂
dcong₂-irr f refl y₁ y₂ = refl

mk-map : {f : N → N′} {g : L → L′} (n : N) → map f g ∘ mk n ≗ mk (f n) ∘ L⁺.map (map f g)
mk-map n (x ∷ []) = refl
mk-map {f = f} {g} n (x ∷ y ∷ zs) = dcong₂-irr (node (f n)) (cong (λ ts → _ ∷ _ ∷ ts) (map*-map zs)) Nat.sz<ss Nat.sz<ss

mk-leaves : (n : N) → leaves {N = N} {L = L} ∘ mk n ≗ L.concatMap leaves ∘ L⁺.toList
mk-leaves n (x ∷ []) rewrite L.++-identityʳ (leaves x) = refl
mk-leaves n (x ∷ y ∷ zs) rewrite catLeaves-≡ zs = refl

mk-label-node : (n : N) (ts : List⁺ (WideTree N L)) → .(L⁺.length ts > 1) → label (mk n ts) ≡ just n
mk-label-node n (x ∷ []) p = ⊥-elim-irr (case p of λ{ (Nat.s≤s ()) })
mk-label-node n (x ∷ y ∷ zs) p = refl

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

data Layered {N : Set n} {L : Set l} (R : Rel N ℓ) : Pred (WideTree N L) (n ⊔ℓ l ⊔ℓ ℓ)

IsLayer : (R : Rel N ℓ) → N → List (WideTree N L) → Set _
IsLayer R n = All* (IfJust (R n) ∘ label ∩ Layered R)

data Layered R where
  leaf : ∀ {x} → Layered R (leaf x)
  node : ∀ {n ts} .{p} → IsLayer R n ts → Layered R (node n ts p)

layered-map⁺  : {R : Rel N′ ℓ} {f : N → N′} {g : L → L′} {t : WideTree N L} →
  Layered (R on f) t → Layered R (map f g t)
layered-map⁺′ : {R : Rel N′ ℓ} {f : N → N′} {g : L → L′} {n : N} {ts : List (WideTree N L)} →
  IsLayer (R on f) n ts → IsLayer R (f n) (L.map (map f g) ts)

layered-map⁺ leaf = leaf
layered-map⁺ (node {ts = ts} xs) = node (subst (IsLayer _ _) (sym (map*-map ts)) (layered-map⁺′ xs))

layered-map⁺′ [] = []
layered-map⁺′ ((rn , lay) ∷ x) =
  (subst (IfJust _) (sym (label-map _)) (IfJust.map⁺ rn) , layered-map⁺ lay) ∷ (layered-map⁺′ x)

layered-map⁻  : {R : Rel N′ ℓ} {f : N → N′} {g : L → L′} {t : WideTree N L} →
  Layered R (map f g t) → Layered (R on f) t
layered-map⁻′ : {R : Rel N′ ℓ} {f : N → N′} {g : L → L′} {n : N} {ts : List (WideTree N L)} →
  IsLayer R (f n) (L.map (map f g) ts) → IsLayer (R on f) n ts

layered-map⁻ {t = leaf _} x = leaf
layered-map⁻ {t = node n ts p} (node xs) = node (layered-map⁻′ (subst (IsLayer _ _) (map*-map ts) xs))

layered-map⁻′ {ts = []} x = []
layered-map⁻′ {ts = t ∷ ts} ((rn , lay) ∷ x) =
  (IfJust.map⁻ (subst (IfJust _) (label-map _) rn) , layered-map⁻ lay) ∷ layered-map⁻′ x
