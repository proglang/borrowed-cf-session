module BorrowedCF.Substitution where

open import Data.These using (These; this; that; these; mergeThese)
open import Data.List.Membership.Propositional
open import Data.Maybe as May using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.Any as Just using (just) renaming (Any to Just)
open import Data.Maybe.Relation.Unary.All as IfJust using (just; nothing) renaming (All to IfJust)
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected; just; just-nothing; nothing-just; nothing)
open import Data.Tree.Binary as T using (Tree; leaf; node)
open import Data.List.NonEmpty as L⁺ using (List⁺; _∷_; _⁺++⁺_)
open import Data.List.Relation.Unary.Any as Any⁰ using (here; there) renaming (Any to Any⁰)
open import Data.List.Relation.Unary.Any as Any⁰ using (here; there) renaming (Any to Any⁰)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using ()
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Unary.Unique.Propositional as Uniq using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq using ()
open import Data.Bool using (Bool; true; false; if_then_else_)
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

mkStruct⁺ : (ps : ParSeq) {ts : List⁺ (T⁺ n)} →
  All⁺ (IfJust (ps ≢_) ∘ WT.label ∩ WT.Layered _≢_) ts →
  Unique (L.concatMap WT.leaves (L⁺.toList ts)) →
  Σ (T⁺ n) Struct⁺
mkStruct⁺ ps {t ∷ []} ((lab , lay) ∷ _) uniq
  rewrite L.++-identityʳ (WT.leaves t) =
  t , lay , uniq
mkStruct⁺ ps {t₁ ∷ t₂ ∷ ts} lay uniq
  rewrite sym (WT.catLeaves-≡ ts) =
  node ps (t₁ ∷ t₂ ∷ ts) Nat.sz<ss
    , node lay
    , uniq

unwrapT : (ps : ParSeq) → ∀ {t} → Struct⁺ t →
  Σ[ ts ∈ List⁺ (T⁺ n) ]
    All⁺ (IfJust (ps ≢_) ∘ WT.label ∩ WT.Layered _≢_) ts
      × WT.leaves t ≡ L.concatMap WT.leaves (L⁺.toList ts)
unwrapT ps {leaf x} 𝓢 = L⁺.[ leaf x ] , (nothing , leaf) ∷ [] , refl
unwrapT ps {node ps′ ts n} 𝓢 with psEq? ps ps′
unwrapT ps {n@(node _ _ _)} 𝓢 | no ps≢ =
  L⁺.[ n ]
    , (just ps≢ , 𝓢 .proj₁) ∷ []
    , sym (L.++-identityʳ _)
unwrapT ps {node ps′ (t ∷ ts) n} (node lay , uniq) | yes refl = t ∷ ts
  , lay
  , cong (WT.leaves t ++_) (WT.catLeaves-≡ ts)

cat⁺ : ParSeq → {t₁ t₂ : T⁺ n} → Struct⁺ t₁ → Struct⁺ t₂ → Disjoint (WT.leaves t₁) (WT.leaves t₂) → Σ (T⁺ n) Struct⁺
cat⁺ ps x y x∩y=∅ =
  let xs , pˣ , eqˣ = unwrapT ps x in
  let ys , pʸ , eqʸ = unwrapT ps y in
  mkStruct⁺ ps {xs L⁺.⁺++⁺ ys} (All.++⁺ pˣ pʸ)
    $ subst Unique (sym (L.concatMap-++ WT.leaves (L⁺.toList xs) (L⁺.toList ys)))
    $ Uniq.++⁺ (subst Unique eqˣ (proj₂ x)) (subst Unique eqʸ (proj₂ y))
    $ subst₂ Disjoint eqˣ eqʸ x∩y=∅

-- cat : ParSeq → {t₁ t₂ : T n} → Struct t₁ → Struct t₂ → Σ (T n) Struct
-- cat ps {t₁} {t₂} s₁ s₂ = {!!} -- May.alignWith (mergeThese (cat⁺ ps)) t₁ t₂ , {!!}

-- {-
-- T′ : ℕ → Set
-- T′ n = Σ[ t ∈ T n ] (WT.IsLeaf t ⊎ ParSeq)

-- Forest : ℕ → Set
-- Forest n = List (T n)

-- Struct : ℕ → Set
-- Struct n = Maybe (T′ n)

-- mkStruct⁺ : ParSeq → List⁺ (T n) → T′ n
-- mkStruct⁺ ps (t ∷ []) = (t , inj₂ (psFlip ps))
-- mkStruct⁺ ps (t₁ ∷ t₂ ∷ ts) = (node _ (t₁ ∷ t₂ ∷ ts) Nat.sz<ss , inj₂ ps)

-- mkStruct : ParSeq → List (T n) → Struct n
-- mkStruct ps [] = nothing
-- mkStruct ps (t ∷ ts) = just (mkStruct⁺ ps (t ∷ ts))

-- unwrapT : ParSeq → T′ n → List⁺ (T n)
-- unwrapT ps (leaf x , _) = L⁺.[ leaf x ]
-- unwrapT ps (node _ ts p , inj₂ ps′) with does (psEq? ps ps′)
-- unwrapT ps (node _ (t ∷ ts) p , inj₂ ps′) | true  = t ∷ ts
-- unwrapT ps (node _ ts p       , inj₂ ps′) | false = L⁺.[ node _ ts p ]

-- catT : ParSeq → T′ n → T′ n → T′ n
-- catT ps x y = mkStruct⁺ ps (unwrapT ps x L⁺.⁺++⁺ unwrapT ps y)

-- cat : ParSeq → Struct n → Struct n → Struct n
-- cat = May.alignWith ∘ mergeThese ∘ catT

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

-- -- ext𝓢 : Direction → Struct n → Struct (1 + n)
-- -- ext𝓢 {n} d 𝓢 =
-- --   let 𝓢⁺ = 𝓢 𝓢⋯ᵣ suc in
-- --   let 𝓢⁰ = just (leaf zero , inj₁ (_ , refl)) in
-- --   ?
-- -- --  cat (directionToParSeq d) (select[L⇒ 𝓢⁰ R⇒ 𝓢⁺ 𝟙⇒ 𝓢⁺ ] d)
-- -- --                            (select[L⇒ 𝓢⁺ R⇒ 𝓢⁰ 𝟙⇒ 𝓢⁰ ] d)

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

-- -- data _︔_⊢_∶_∣_ (Γ : Ctxt n) : (𝓢 : Struct n) → Tm n → Ty → Effect → Set₁ where
-- --   ⊢` : ∀ {ps} →
-- --     let 𝓢 = just (leaf α , ps) in
-- --     Γ α ≡ t →
-- --    -----------------------------------
-- --     Γ ︔ 𝓢 ⊢ ` α ∶ t ∣ ℙ

-- --   ⊢K : ∀ {c} →
-- --     let 𝓢 = nothing in
-- --     ⊢ᶜ c ∶ t →
-- --    -------------------------
-- --     Γ ︔ 𝓢 ⊢ K c ∶ t ∣ ℙ

-- --   ⊢λ : ∀ {𝓢 m d ϵ} →
-- --     t₁ VF.∷ Γ ︔ ext𝓢 d 𝓢 ⊢ e ∶ t₂ ∣ ϵ →
-- --     Γ ︔ 𝓢 ⊢ (`λ e) ∶ arr m d ϵ t₁ t₂ ∣ ℙ

-- --   -- ⊢· : ∀ {𝓢 𝓢₁ 𝓢₂ m d ϵ ϵ₁ ϵ₂ ϵ₃} →
-- --   --   Split d 𝓢 𝓢₁ 𝓢₂ →
-- --   --   ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ ϵ₃ ≡ ϵ →
-- --   --   Γ ︔ 𝓢₁ ⊢ e₁ ∶ arr m d ϵ₃ t₁ t₂ ∣ ϵ₁ →
-- --   --   Γ ︔ 𝓢₂ ⊢ e₂ ∶ t₁ ∣ ϵ₂ →
-- --   --  ---------------------------------------
-- --   --   Γ ︔ 𝓢 ⊢ e₁ · e₂ ∶ t₂ ∣ ϵ
