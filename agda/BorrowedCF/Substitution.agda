module BorrowedCF.Substitution where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Maybe.Properties as May using ()
open import Data.Maybe.Relation.Unary.Any as Just using (just) renaming (Any to Just)
open import Data.Maybe.Relation.Unary.All as IfJust using (just; nothing) renaming (All to IfJust)
open import Data.Maybe.Relation.Unary.All.Properties as IfJust using ()
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected; just; just-nothing; nothing-just; nothing)
open import Data.List.Membership.Propositional as ∈ using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties as ∈ using ()
open import Data.List.NonEmpty as L⁺ using (List⁺; _∷_; _⁺++⁺_)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using ()
open import Data.List.Relation.Unary.Any as Any⁰ using (here; there) renaming (Any to Any⁰)
open import Data.List.Relation.Unary.Any.Properties as Any⁰ using ()
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Unary.Unique.Propositional as Uniq using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq using ()
open import Data.These using (These; this; that; these; mergeThese)
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Vec.Functional as VF using () renaming (_∷_ to _V∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context.WildTree as WT using (WideTree; leaf; node)

open Bin using (Reflexive; Symmetric)
open Un using (_∩_)

open Nat.Variables

variable
  α α₁ α₂ α₃ α′ : 𝔽 n

data Const : Set where
  ⟨⟩ `new `fork
     `close `wait
     `send `recv
     `lsplit `rsplit
     `drop `acquire
       : Const

infix 9 `_

data Tm n : Set where
  K   : Const → Tm n
  `_  : (α : 𝔽 n) → Tm n
  `λ  : (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _⊗_ : (e₁ e₂ : Tm n) → Tm n
  let-` : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  let-⊗ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n
  `inl `inr : (e : Tm n) → Tm n
  `case_of[_⇒_,_⇒_] : (e : Tm n) (e₁ : Tm (1 + n)) (e₂ : Tm (1 + n)) → Tm n

data Dir : Set where
  ‼ ⁇ : Dir

data Mode : Set where
  owned borrowed : Mode

data Mobility : Set where
  mobile static : Mobility

data Direction : Set where
  L R 𝟙 : Direction

data Effect : Set where
  ℙ 𝕀 : Effect

infixr 6 _⊔ϵ_

_⊔ϵ_ : Effect → Effect → Effect
ℙ ⊔ϵ y = y
𝕀 ⊔ϵ y = 𝕀

data Ty : Set

data 𝕊 n : Set where
  ε : 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  end : (⁉ : Dir) (m : Mode) → 𝕊 n
  msg : (⁉ : Dir) (t : Ty) → 𝕊 n
  branch : (⁉ : Dir) (s₁ s₂ : 𝕊 n) → 𝕊 n
  `_  : (α : 𝔽 n) → 𝕊 n
  μ   : (s : 𝕊 (1 + n)) → 𝕊 n

data Ty where
  `⊤ : Ty
  arr : (m : Mobility) (d : Direction) (ℯ : Effect) (t₁ t₂ : Ty) → Ty
  _`+_ : (t₁ t₂ : Ty) → Ty
  S  : (s : 𝕊 0) → Ty

-- Ctxt : ℕ → Set
-- Ctxt n = (α : 𝔽 n) → Maybe Ty

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : Ty
  s s₁ s₂ s₃ s′ : 𝕊 n
--  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctxt n

data ParSeq : Set where
  par seq : ParSeq

psEq? : DecidableEquality ParSeq
psEq? par par = yes refl
psEq? par seq = no λ()
psEq? seq par = no λ()
psEq? seq seq = yes refl

psFlip : ParSeq → ParSeq
psFlip par = seq
psFlip seq = par

directionToParSeq : Direction → ParSeq
directionToParSeq L = seq
directionToParSeq R = seq
directionToParSeq 𝟙 = par

select[par⇒_seq⇒_] : ∀ {a} {A : Set a} → A → A → ParSeq → A
select[par⇒ x seq⇒ y ] par = x
select[par⇒ x seq⇒ y ] seq = y

select⁺ : ∀ {a p ps} {A : Set a} {P : Pred A p} {x y : A} → P x → P y → P (select[par⇒ x seq⇒ y ] ps)
select⁺ {ps = par} px py = px
select⁺ {ps = seq} px py = py

select[L⇒_R⇒_𝟙⇒_] : ∀ {a} {A : Set a} → A → A → A → Direction → A
select[L⇒ x R⇒ y 𝟙⇒ z ] L = x
select[L⇒ x R⇒ y 𝟙⇒ z ] R = y
select[L⇒ x R⇒ y 𝟙⇒ z ] 𝟙 = z

selectLR𝟙⁺ : ∀ {a p d} {A : Set a} {P : Pred A p} {x y z : A} → P x → P y → P z → P (select[L⇒ x R⇒ y 𝟙⇒ z ] d)
selectLR𝟙⁺ {d = L} x y z = x
selectLR𝟙⁺ {d = R} x y z = y
selectLR𝟙⁺ {d = 𝟙} x y z = z

selectLR𝟙⁻ : ∀ {a p d} {A : Set a} {P : Pred A p} {x y z : A} → P (select[L⇒ x R⇒ y 𝟙⇒ z ] d) → P x ⊎ P y ⊎ P z
selectLR𝟙⁻ {d = L} p = inj₁ p
selectLR𝟙⁻ {d = R} p = inj₂ (inj₁ p)
selectLR𝟙⁻ {d = 𝟙} p = inj₂ (inj₂ p)

Any⁺ : ∀ {a p} {A : Set a} → Pred A p → Pred (List⁺ A) _
Any⁺ P = Any⁰ P ∘ L⁺.toList

All⁺ : ∀ {a p} {A : Set a} → Pred A p → Pred (List⁺ A) _
All⁺ P = All P ∘ L⁺.toList

T⁺ : ℕ → Set
T⁺ n = WideTree ParSeq (𝔽 n)

Struct⁺ : T⁺ n → Set
Struct⁺ t = WT.Layered _≢_ t × Unique (WT.leaves t)

T : ℕ → Set
T n = Maybe (T⁺ n)

Struct : T n → Set
Struct = IfJust Struct⁺

Disjoint⁺ : Rel (T⁺ n) _
Disjoint⁺ = Disjoint on WT.leaves

Disjoint⁰ : Rel (T n) _
Disjoint⁰ = Connected Disjoint⁺

struct⁺-mk : (ps : ParSeq) {ts : List⁺ (T⁺ n)} →
  All⁺ (IfJust (ps ≢_) ∘ WT.label ∩ WT.Layered _≢_) ts →
  Unique (L.concatMap WT.leaves (L⁺.toList ts)) →
  Struct⁺ (WT.mk ps ts)
struct⁺-mk ps {t ∷ []} ((lab , lay) ∷ _) uniq
  rewrite L.++-identityʳ (WT.leaves t)
  = lay , uniq
struct⁺-mk ps {t₁ ∷ t₂ ∷ ts} lay uniq
  rewrite WT.catLeaves-≡ ts
  = node lay , uniq

struct-mk : (ps : ParSeq) {ts : List (T⁺ n)} →
  All (IfJust (ps ≢_) ∘ WT.label ∩ WT.Layered _≢_) ts →
  Unique (L.concatMap WT.leaves ts) →
  Struct (May.map (WT.mk ps) (L⁺.fromList ts))
struct-mk ps {[]}    xs uniq = nothing
struct-mk ps {_ ∷ _} xs uniq = just (struct⁺-mk ps xs uniq)

denode : ParSeq → T⁺ n → List⁺ (T⁺ n)
denode ps (leaf x) = L⁺.[ leaf x ]
denode ps n@(node ps′ (t ∷ ts) p) = if does (psEq? ps ps′) then t ∷ ts else L⁺.[ n ]

denode-struct : (ps : ParSeq) {t : T⁺ n} →
  Struct⁺ t → All⁺ (IfJust (ps ≢_) ∘ WT.label ∩ WT.Layered _≢_) (denode ps t)
denode-struct ps {leaf _} x = (nothing , x .proj₁) ∷ []
denode-struct ps {node ps′ (t ∷ ts) p} x with psEq? ps ps′
denode-struct ps {node ps′ (t ∷ ts) p} (node lay , _) | yes refl = lay
denode-struct ps {node ps′ (t ∷ ts) p} (lay      , _) | no  ps≢  = (just ps≢ , lay) ∷ []

denode-leaves : (ps : ParSeq) (t : T⁺ n) →
  L.concatMap WT.leaves (L⁺.toList (denode ps t)) ≡ WT.leaves t
denode-leaves ps (leaf x) = refl
denode-leaves ps (node ps′ (t ∷ ts) p) with does (psEq? ps ps′)
... | true = cong (WT.leaves t ++_) (sym (WT.catLeaves-≡ ts))
... | false = L.++-identityʳ _

cat⁺ : ParSeq → T⁺ n → T⁺ n → T⁺ n
cat⁺ ps t₁ t₂ = WT.mk ps (denode ps t₁ ⁺++⁺ denode ps t₂)

cat : ParSeq → T n → T n → T n
cat ps = May.alignWith (mergeThese (cat⁺ ps))

struct⁺-cat⁺ : (ps : ParSeq) {t₁ t₂ : T⁺ n} → Struct⁺ t₁ → Struct⁺ t₂ → Disjoint⁺ t₁ t₂ → Struct⁺ (cat⁺ ps t₁ t₂)
struct⁺-cat⁺ ps {t₁} {t₂} x y x∩y=∅ =
  struct⁺-mk ps (All.++⁺ (denode-struct ps x) (denode-struct ps y))
    $ subst Unique (sym (L.concatMap-++ WT.leaves (L⁺.toList (denode ps t₁)) (L⁺.toList (denode ps t₂))))
    $ Uniq.++⁺ (subst Unique (sym (denode-leaves ps t₁)) (proj₂ x))
               (subst Unique (sym (denode-leaves ps t₂)) (proj₂ y))
    $ subst₂ Disjoint (sym (denode-leaves ps t₁)) (sym (denode-leaves ps t₂)) x∩y=∅

struct-cat⁺ : (ps : ParSeq) {t₁ t₂ : T n} → Struct t₁ → Struct t₂ → Disjoint⁰ t₁ t₂ → Struct (cat ps t₁ t₂)
struct-cat⁺ ps nothing  nothing  x∩y=∅ = nothing
struct-cat⁺ ps (just x) nothing  x∩y=∅ = just x
struct-cat⁺ ps nothing  (just x) x∩y=∅ = just x
struct-cat⁺ ps (just x) (just y) x∩y=∅ = just (struct⁺-cat⁺ ps x y (Conn.drop-just x∩y=∅))

struct-map⁺ : ∀ {t} {f : 𝔽 m → 𝔽 n} → Injective _≡_ _≡_ f → Struct t → Struct (May.map (WT.mapᴸ f) t)
struct-map⁺ inj-f = IfJust.gmap λ where
  {t′} (lay , uniq) → WT.layered-map⁺ lay , subst Unique (sym (WT.leaves-map t′)) (Uniq.map⁺ inj-f uniq)

struct-map⁻ : ∀ {t} {f : 𝔽 m → 𝔽 n} → Struct (May.map (WT.mapᴸ f) t) → Struct t
struct-map⁻ 𝓢 =
  IfJust.map (λ where {t′} (lay , uniq) → WT.layered-map⁻ lay
                                        , Uniq.map⁻ (subst Unique (WT.leaves-map t′) uniq)
             )
             (IfJust.map⁻ 𝓢)

-- {-
-- UniqVars : T n → Set
-- UniqVars = Unique ∘ WT.leaves

-- ValidT : Struct n → Set
-- ValidT = IfJust λ{ (t , ps) → UniqVars t }

-- Var : ∀ {p} (P : Pred (𝔽 n) p) → Struct n → Set _
-- Var P = Just λ{ (t , ps) → WT.Any P t }

-- Var∈ : 𝔽 n → Struct n → Set _
-- Var∈ α = Var (α ≡_)

-- Any⁺ : ∀ {a p} {A : Set a} → Pred A p → Pred (List⁺ A) _
-- Any⁺ P = Any⁰ P ∘ L⁺.toList

-- any-⁺++⁺⁻ : ∀ {a p} {A : Set a} {P : Pred A p} (xs : List⁺ A) {ys : List⁺ A} →
--   Any⁺ P (xs ⁺++⁺ ys) → Any⁺ P xs ⊎ Any⁺ P ys
-- any-⁺++⁺⁻ xs x = Any⁰.++⁻ (L⁺.toList xs) x

-- module _ {p} {P : Pred (𝔽 n) p} where
--   any-mkStruct⁺⁻ : ∀ ps (ts : List⁺ (T n)) → WT.Any P (mkStruct⁺ ps ts .proj₁) → Any⁺ (WT.Any P) ts
--   any-mkStruct⁺⁻ ps (t ∷ []) x = here x
--   any-mkStruct⁺⁻ ps (t₁ ∷ t₂ ∷ ts) (node x _) = x

--   any-unwrapT⁻ : ∀ ps t → Any⁺ (WT.Any P) (unwrapT ps t) → WT.Any P (proj₁ t)
--   any-unwrapT⁻ ps (leaf _ , _) (here px) = px
--   any-unwrapT⁻ ps (node _ ts n , inj₂ ps′) x with does (psEq? ps ps′)
--   any-unwrapT⁻ ps (node _ (t ∷ ts) n , inj₂ ps′) x | true  = node x n
--   any-unwrapT⁻ ps (node _ (t ∷ ts) n , inj₂ ps′) x | false = Any⁰.singleton⁻ x

--   any-catT⁻ : ∀ ps (x y : T′ n) → WT.Any P (catT ps x y .proj₁) →
--     WT.Any P (proj₁ x) ⊎ WT.Any P (proj₁ y)
--   any-catT⁻ ps x y p = Sum.map (any-unwrapT⁻ ps x) (any-unwrapT⁻ ps y) $
--     any-⁺++⁺⁻ (unwrapT ps x) (any-mkStruct⁺⁻ _ (unwrapT ps x ⁺++⁺ unwrapT ps y) p)

--   var-cat⁻ : ∀ ps (𝓢₁ 𝓢₂ : Struct n) → Var P (cat ps 𝓢₁ 𝓢₂) → Var P 𝓢₁ ⊎ Var P 𝓢₂
--   var-cat⁻ ps (just x) nothing v = inj₁ v
--   var-cat⁻ ps nothing (just y) v = inj₂ v
--   var-cat⁻ ps (just x) (just y) (just v) = Sum.map just just (any-catT⁻ ps x y v)

-- -- Ctxt : Struct n → Set₁
-- -- Ctxt 𝓢 = ∀ {P : Pred _ 0ℓ} (v : Var P 𝓢) → Ty
-- -}

-- Ctxt : ℕ → Set
-- Ctxt = VF.Vector Ty

-- open import Data.List.Relation.Ternary.Appending.Propositional as App
--   using (Appending; []++_; _∷_)
-- open import Data.List.Relation.Ternary.Interleaving.Propositional as Inter
--   using (Interleaving; []; consˡ; consʳ)

-- NodeSplit : ∀ {a} {A : Set a} → ParSeq → List A → List A → List A → Set _
-- NodeSplit seq = Appending
-- NodeSplit par = Interleaving

-- {-
-- data Split′ {n} (ps : ParSeq) : Struct n → Struct n → T′ n → Set where
--   left  : ∀ {t ps′ ps″} → Split′ ps (just (t , ps′)) nothing (t , ps″)
--   right : ∀ {t ps′ ps″} → Split′ ps nothing (just (t , ps′)) (t , ps″)

--   split : ∀ {ts ls rs l r p} →
--     Appending ls rs ts →
--     mkStruct ps ls ≡ l →
--     mkStruct ps rs ≡ r →
--     Split′ ps l r (node _ ts p , inj₂ ps)

-- Split : Direction → Struct n → Struct n → Struct n → Set
-- Split d t l r = IfJust (Split′ (directionToParSeq d)
--                                (select[L⇒ l R⇒ r 𝟙⇒ l ] d)
--                                (select[L⇒ r R⇒ l 𝟙⇒ r ] d))
--                        t
-- -}

-- Ren : ℕ → ℕ → Set
-- Ren m n = 𝔽 m → 𝔽 n

-- {-
-- var-⋯⁻ : ∀ {p} {P : Pred (𝔽 n) p} (𝓢 : Struct m) {ρ : Ren m n} →
--   Injective _≡_ _≡_ ρ →
--   Var P (𝓢 𝓢⋯ᵣ ρ) →
--   Var (P ∘ ρ) 𝓢
-- var-⋯⁻ (just t) ρ (just x) = just {!!}
-- -}

-- mkConnected : ∀ {a b ℓ} {A : Set a} {B : Set b} {R : REL A B ℓ} {x : Maybe A} {y : Maybe B} →
--   (∀ {x′} {y′} → x ≡ just x′ → y ≡ just y′ → R x′ y′) → Connected R x y
-- mkConnected {x = just _}  {just _}  f = just (f refl refl)
-- mkConnected {x = just _}  {nothing} f = just-nothing
-- mkConnected {x = nothing} {just _}  f = nothing-just
-- mkConnected {x = nothing} {nothing} f = nothing

-- map-just⁻¹ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} (mx : Maybe A) {y} → .(May.map f mx ≡ just y) → ∃ λ x → mx ≡ just x
-- map-just⁻¹ (just x) eq = x , refl

-- ext𝓢 : Direction → (t : T n) → Struct t → Σ[ t′ ∈ T (1 + n) ] Struct t′
-- ext𝓢 {n} d t 𝓢 =
--   let
--     𝓢⁰ : Σ (T (1 + n)) Struct
--     𝓢⁰ = just (leaf zero) , just (leaf , [] ∷ [])
--   in
--   let
--     𝓢⁺ : Σ[ t′ ∈ T (1 + n) ] Struct t′
--     𝓢⁺ = May.map (WT.mapᴸ suc) t
--        , IfJust.gmap (λ{ {t} (lay , uniq) → WT.layered-map⁺ lay
--                                           , subst Unique (sym (WT.leaves-map t)) (Uniq.map⁺ Fin.suc-injective uniq) })
--                      𝓢
--   in
--   let
--     𝓢⁰/⁺-disjoint : Disjoint⁰ (proj₁ 𝓢⁰) (proj₁ 𝓢⁺)
--     𝓢⁰/⁺-disjoint = mkConnected λ where
--       refl eq (here refl , z∈𝓢⁺) →
--         let eq′ = cong WT.leaves (May.just-injective (sym eq ■ cong (May.map _) (map-just⁻¹ t eq .proj₂)))
--                     ■ WT.leaves-map (map-just⁻¹ t eq .proj₁)
--         in
--         case Any⁰.satisfied (Any⁰.map⁻ (subst (zero ∈_) eq′ z∈𝓢⁺)) .proj₂ of λ()
--   in
--   let xy,dis : Σ[ x ∈ ∃ (Struct {n = 1 + n}) ] Σ[ y ∈ ∃ (Struct {n = 1 + n}) ] Disjoint⁰ (proj₁ x) (proj₁ y)
--       xy,dis = select[L⇒ 𝓢⁰ , 𝓢⁺ , 𝓢⁰/⁺-disjoint
--                       R⇒ 𝓢⁺ , 𝓢⁰ , Conn.sym (λ disj {v} z → disj (Π.swap z)) 𝓢⁰/⁺-disjoint
--                       𝟙⇒ 𝓢⁰ , 𝓢⁺ , 𝓢⁰/⁺-disjoint ] d
--   in
--   cat (directionToParSeq d)
--     (xy,dis .proj₁ .proj₂)
--     (xy,dis .proj₂ .proj₁ .proj₂)
--     (xy,dis .proj₂ .proj₂)

-- fullTree : ∀ {m} → ParSeq → Σ (T m) Struct
-- fullTree {m} ps =
--   let ts = L.map leaf (L.allFin m) in
--   let
--     eq =
--       L.allFin m                      ≡⟨ L.concat-map-[ L.allFin m ] ⟨
--       L.concatMap L.[_] (L.allFin m)  ≡⟨ cong L.concat (L.map-∘ (L.allFin m)) ⟩
--       L.concatMap WT.leaves ts        ∎
--   in
--   mkStruct ps {ts} (All.tabulate isLayered) (subst Unique eq (Uniq.allFin⁺ m))
--   where
--   open ≡-Reasoning
--   isLayered : ∀ {x} → x ∈ L.map leaf (L.allFin m) → IfJust (_≢_ ps) (WT.label x) × WT.Layered _≢_ x
--   isLayered x∈ rewrite Any⁰.lookup-result (Any⁰.map⁻ x∈) = nothing , leaf

-- -- wkTree : ∀ m → ParSeq → Σ (T (suc m + n)) Struct
-- -- wkTree zero    ps = just (leaf zero) , just (leaf , [] ∷ [])
-- -- wkTree (suc m) ps =
-- --   just (node ps (L.map (λ x → leaf (x ↑ˡ _)) (L.allFin (suc (suc m)))) {!!})
-- --     , just ({!!} , {!!})

-- -- ext𝓢′ : Direction → ∀ m → (t : T n) → Struct t → Σ (T (suc m + n)) Struct
-- -- ext𝓢′ {n} d m t str =
-- --   let T′ = T (suc m + n) in
-- --   let
-- --     structNew : Σ T′ Struct
-- --     structNew = just (node {!!} {!!} {!!}) , just {!!}
-- --   in
-- --   let
-- --     structWk : Σ T′ Struct
-- --     structWk = May.map (WT.mapᴸ (suc m ↑ʳ_)) t , IfJust.gmap
-- --       (λ{ {t′} (lay , uniq) → WT.layered-map⁺ lay ,
-- --                               subst Unique (sym (WT.leaves-map t′)) (Uniq.map⁺ (↑ʳ-injective (suc m) _ _) uniq)
-- --       })
-- --       str
-- --   in
-- --   let
-- --     structDisj : Disjoint⁰ (proj₁ structNew) (proj₁ structWk)
-- --     structDisj = {!!}
-- --   in
-- --   let
-- --     xy,disj : Σ[ x ∈ Σ T′ Struct ] Σ[ y ∈ Σ T′ Struct ] Disjoint⁰ (proj₁ x) (proj₁ y)
-- --     xy,disj = {!!}
-- --   in
-- --   {!!}

-- -- {-
-- -- extΓ : {𝓢 : Struct n} {d : Direction} → Ty → Ctxt 𝓢 → Ctxt (ext𝓢 d 𝓢)
-- -- extΓ {d = d} ty Γ v =
-- --   let zz = [ {!!} , {!!} ]′ (var-cat⁻ (directionToParSeq d) _ _ v) in
-- --   [ Γ ∘ var-⋯⁻ _ Fin.suc-injective , const ty ] {!!}
-- -- -}

-- -- infix 4 ⊢ᶜ_∶_

-- -- data ⊢ᶜ_∶_ : Const → Ty → Set where
-- --   -- TODO --

-- -- infix 4 _︔_⊢_∶_∣_

-- -- data _︔_⊢_∶_∣_ (Γ : Ctxt n) : {t : T n} (𝓢 : Struct t) → Tm n → Ty → Effect → Set₁ where
-- --   ⊢` :
-- --     let 𝓢 = just (leaf {x = α} , [] ∷ []) in
-- --     Γ α ≡ t →
-- --    -----------------------------------
-- --     Γ ︔ 𝓢 ⊢ ` α ∶ t ∣ ℙ

-- --   ⊢K : ∀ {c} →
-- --     let 𝓢 = nothing in
-- --     ⊢ᶜ c ∶ t →
-- --    -------------------------
-- --     Γ ︔ 𝓢 ⊢ K c ∶ t ∣ ℙ

-- --   ⊢λ : ∀ {T 𝓢 m d ϵ} →
-- --     t₁ VF.∷ Γ ︔ ext𝓢 d T 𝓢 .proj₂ ⊢ e ∶ t₂ ∣ ϵ →
-- --     Γ ︔ 𝓢 ⊢ (`λ e) ∶ arr m d ϵ t₁ t₂ ∣ ℙ

-- --   -- ⊢· : ∀ {𝓢 𝓢₁ 𝓢₂ m d ϵ ϵ₁ ϵ₂ ϵ₃} →
-- --   --   Split d 𝓢 𝓢₁ 𝓢₂ →
-- --   --   ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ ϵ₃ ≡ ϵ →
-- --   --   Γ ︔ 𝓢₁ ⊢ e₁ ∶ arr m d ϵ₃ t₁ t₂ ∣ ϵ₁ →
-- --   --   Γ ︔ 𝓢₂ ⊢ e₂ ∶ t₁ ∣ ϵ₂ →
-- --   --  ---------------------------------------
-- --   --   Γ ︔ 𝓢 ⊢ e₁ · e₂ ∶ t₂ ∣ ϵ
