-- | Completeness toolkit, part 3 (helper of C1): the CONSTRUCTION half of the
--   canonical split.  Given
--     * `disj` — every variable shared by X and Y is unrestricted,
--     * `out`  — every variable of γ outside X ∪ Y is unrestricted,
--     * `sep`  — no forbidden `;`-order between an X- and a Y-variable
--                (unless one of the two is mobile),
--   the two restrictions `γ ↓ X` and `γ ↓ Y` recombine into a subcontext of γ.
--
--   Everything is proved by induction on γ; the only non-structural step is the
--   `;`-node, where the two mobility disjunctions extracted by `mob-dist` drive
--   the interchange law `(A₁ ; B₁) ⊗ (A₂ ; B₂) ≈ (A₁ ⊗ A₂) ; (B₁ ⊗ B₂)`.
module BorrowedCF.Completeness.Split.Construct where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; _∪_; ∁)
open import Data.Fin.Subset.Properties using (_∈?_; x∈p∪q⁺; x∈p∪q⁻; x∉p⇒x∈∁p; x∈∁p⇒x∉p)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Completeness.Split.Base

open Nat.Variables
open Variables

------------------------------------------------------------------------
-- 1.  Structure algebra: the two shuffles.  Both are context-free, i.e. they
--     mention Γ only through the mobility witnesses they consume.

-- Interchange for a pure `;`-square.  Swapping `Q₁` past `P₂` is the only
-- move, so a single mobility witness is enough.
;-interchange : ∀ {Γ : Ctx n} (P₁ Q₁ P₂ Q₂ : Struct n) →
  MobCx Γ P₂ ⊎ MobCx Γ Q₁ →
  Γ ∶ (P₁ ; Q₁) ; (P₂ ; Q₂) ≈ (P₁ ; P₂) ; (Q₁ ; Q₂)
;-interchange P₁ Q₁ P₂ Q₂ mob = let open ≈-Reasoning in
  begin
    (P₁ ; Q₁) ; (P₂ ; Q₂)    ≈⟨ ;-assoc ⟩
    P₁ ; (Q₁ ; (P₂ ; Q₂))    ≈⟨ ;-cong ≈-refl ;-assoc ⟨
    P₁ ; ((Q₁ ; P₂) ; Q₂)    ≈⟨ ;-cong ≈-refl (;-cong (;-commMob (Sum.swap mob)) ≈-refl) ⟩
    P₁ ; ((P₂ ; Q₁) ; Q₂)    ≈⟨ ;-cong ≈-refl ;-assoc ⟩
    P₁ ; (P₂ ; (Q₁ ; Q₂))    ≈⟨ ;-assoc ⟨
    (P₁ ; P₂) ; (Q₁ ; Q₂)    ∎

-- Interchange for a `∥` of two `;`s.  Four cases, two proof chains: either both
-- halves of one COLUMN are mobile (then transmute the rows apart and use
-- `∥-comm₄`), or both halves of one ROW are mobile (then transmute the top `∥`
-- into a `;` and reuse `;-interchange`).
;-shuffle : ∀ {Γ : Ctx n} (A₁ B₁ A₂ B₂ : Struct n) →
  MobCx Γ A₁ ⊎ MobCx Γ B₂ → MobCx Γ A₂ ⊎ MobCx Γ B₁ →
  Γ ∶ (A₁ ; B₁) ∥ (A₂ ; B₂) ≈ (A₁ ∥ A₂) ; (B₁ ∥ B₂)
;-shuffle A₁ B₁ A₂ B₂ (inj₁ mA₁) (inj₁ mA₂) = let open ≈-Reasoning in
  begin
    (A₁ ; B₁) ∥ (A₂ ; B₂)  ≈⟨ ∥-cong (∥/;-transmute (inj₁ mA₁)) (∥/;-transmute (inj₁ mA₂)) ⟨
    (A₁ ∥ B₁) ∥ (A₂ ∥ B₂)  ≈⟨ ∥-comm₄ ⟩
    (A₁ ∥ A₂) ∥ (B₁ ∥ B₂)  ≈⟨ ∥/;-transmute (inj₁ (mA₁ ∥ mA₂)) ⟩
    (A₁ ∥ A₂) ; (B₁ ∥ B₂)  ∎
;-shuffle A₁ B₁ A₂ B₂ (inj₂ mB₂) (inj₂ mB₁) = let open ≈-Reasoning in
  begin
    (A₁ ; B₁) ∥ (A₂ ; B₂)  ≈⟨ ∥-cong (∥/;-transmute (inj₂ mB₁)) (∥/;-transmute (inj₂ mB₂)) ⟨
    (A₁ ∥ B₁) ∥ (A₂ ∥ B₂)  ≈⟨ ∥-comm₄ ⟩
    (A₁ ∥ A₂) ∥ (B₁ ∥ B₂)  ≈⟨ ∥/;-transmute (inj₂ (mB₁ ∥ mB₂)) ⟩
    (A₁ ∥ A₂) ; (B₁ ∥ B₂)  ∎
;-shuffle A₁ B₁ A₂ B₂ (inj₁ mA₁) (inj₂ mB₁) = let open ≈-Reasoning in
  begin
    (A₁ ; B₁) ∥ (A₂ ; B₂)  ≈⟨ ∥/;-transmute (inj₁ (mA₁ ; mB₁)) ⟩
    (A₁ ; B₁) ; (A₂ ; B₂)  ≈⟨ ;-interchange A₁ B₁ A₂ B₂ (inj₂ mB₁) ⟩
    (A₁ ; A₂) ; (B₁ ; B₂)  ≈⟨ ;-cong (∥/;-transmute (inj₁ mA₁)) (∥/;-transmute (inj₁ mB₁)) ⟨
    (A₁ ∥ A₂) ; (B₁ ∥ B₂)  ∎
;-shuffle A₁ B₁ A₂ B₂ (inj₂ mB₂) (inj₁ mA₂) = let open ≈-Reasoning in
  begin
    (A₁ ; B₁) ∥ (A₂ ; B₂)  ≈⟨ ∥/;-transmute (inj₂ (mA₂ ; mB₂)) ⟩
    (A₁ ; B₁) ; (A₂ ; B₂)  ≈⟨ ;-interchange A₁ B₁ A₂ B₂ (inj₁ mA₂) ⟩
    (A₁ ; A₂) ; (B₁ ; B₂)  ≈⟨ ;-cong (∥/;-transmute (inj₂ mA₂)) (∥/;-transmute (inj₂ mB₂)) ⟨
    (A₁ ∥ A₂) ; (B₁ ∥ B₂)  ∎

-- An unrestricted structure absorbs a `join` with itself, in every direction.
join-dup : ∀ (d : Dir) {Γ : Ctx n} {α : Struct n} → UnrCx Γ α → Γ ∶ join d α α ≈ α
join-dup 𝟙 U = ≈-sym (∥-dup U)
join-dup L U = ≈-trans (≈-sym (∥/;-transmute (inj₁ (UnrCx⇒MobCx U)))) (≈-sym (∥-dup U))
join-dup R U = ≈-trans (≈-sym (∥/;-transmute (inj₁ (UnrCx⇒MobCx U)))) (≈-sym (∥-dup U))

------------------------------------------------------------------------
-- 2.  Turning `Sep` at a `;`-node into the two mobility disjunctions.
--     Every u of `γ₁ ↓ X` and every v of `γ₂ ↓ Y` satisfy `before u v (γ₁ ; γ₂)`
--     by the left injection, so `getXY` applies pointwise and `mob-dist`
--     collapses the pointwise witnesses to one side.

mob-XY : ∀ {Γ : Ctx n} {X Y : Subset n} (γ₁ γ₂ : Struct n) →
  SepXY Γ X Y (γ₁ ; γ₂) → MobCx Γ (γ₁ ↓ X) ⊎ MobCx Γ (γ₂ ↓ Y)
mob-XY {X = X} {Y} γ₁ γ₂ s = mob-dist (γ₁ ↓ X) (γ₂ ↓ Y) λ u v u∈ v∈ →
  getXY s u v (mem-↓⁻ γ₁ u∈ .proj₁) (mem-↓⁻ γ₂ v∈ .proj₁)
        (inj₁ (mem-↓⁻ γ₁ u∈ .proj₂ , mem-↓⁻ γ₂ v∈ .proj₂))

mob-YX : ∀ {Γ : Ctx n} {X Y : Subset n} (γ₁ γ₂ : Struct n) →
  SepYX Γ X Y (γ₁ ; γ₂) → MobCx Γ (γ₁ ↓ Y) ⊎ MobCx Γ (γ₂ ↓ X)
mob-YX {X = X} {Y} γ₁ γ₂ s = mob-dist (γ₁ ↓ Y) (γ₂ ↓ X) λ u v u∈ v∈ →
  getYX s u v (mem-↓⁻ γ₁ u∈ .proj₁) (mem-↓⁻ γ₂ v∈ .proj₁)
        (inj₁ (mem-↓⁻ γ₁ u∈ .proj₂ , mem-↓⁻ γ₂ v∈ .proj₂))

------------------------------------------------------------------------
-- 3.  The construction.

canon-core : ∀ (d : Dir) {Γ : Ctx n} {X Y : Subset n} (γ : Struct n) →
  (disj : ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)) →
  (out  : AllCx Unr Γ (γ ↓ ∁ (X ∪ Y))) →
  (sep  : Sep d Γ X Y γ) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ

canon-core d [] disj out sep = ≼-refl (join-[]₁ d)

canon-core d {Γ} {X} {Y} (` z) disj out sep with z ∈? X | z ∈? Y
... | yes z∈X | yes z∈Y = ≼-refl (join-dup d (` (disj z z∈X z∈Y)))
... | yes _   | no  _   = ≼-refl (join-[]₂ d)
... | no  _   | yes _   = ≼-refl (join-[]₁ d)
... | no  z∉X | no  z∉Y =
  ≼-trans (≼-refl (join-[]₁ d))
          (≼-∅ (` allCx-mem out
                    (mem-↓⁺ (` z) (x∉p⇒x∈∁p (λ z∈ → [ z∉X , z∉Y ]′ (x∈p∪q⁻ X Y z∈)))
                            (mem-self z))))

canon-core d {Γ} {X} {Y} (γ₁ ∥ γ₂) disj (o₁ ∥ o₂) sep =
  ≼-trans (join-distr-∥ d (γ₁ ↓ X) (γ₁ ↓ Y) (γ₂ ↓ X) (γ₂ ↓ Y))
          (≼-cong-∥ (canon-core d γ₁ disj o₁ (sep-∥ˡ d sep))
                    (canon-core d γ₂ disj o₂ (sep-∥ʳ d sep)))

canon-core 𝟙 {Γ} {X} {Y} (γ₁ ; γ₂) disj (o₁ ; o₂) (sXY , sYX) =
  ≼-trans (≼-refl (;-shuffle (γ₁ ↓ X) (γ₂ ↓ X) (γ₁ ↓ Y) (γ₂ ↓ Y)
                             (mob-XY γ₁ γ₂ sXY) (mob-YX γ₁ γ₂ sYX)))
          (≼-cong-; (canon-core 𝟙 γ₁ disj o₁ (sepXY-;ˡ sXY , sepYX-;ˡ sYX))
                    (canon-core 𝟙 γ₂ disj o₂ (sepXY-;ʳ sXY , sepYX-;ʳ sYX)))

canon-core L {Γ} {X} {Y} (γ₁ ; γ₂) disj (o₁ ; o₂) sep =
  ≼-trans (≼-refl (;-interchange (γ₁ ↓ X) (γ₂ ↓ X) (γ₁ ↓ Y) (γ₂ ↓ Y)
                                 (mob-YX γ₁ γ₂ sep)))
          (≼-cong-; (canon-core L γ₁ disj o₁ (sepYX-;ˡ sep))
                    (canon-core L γ₂ disj o₂ (sepYX-;ʳ sep)))

canon-core R {Γ} {X} {Y} (γ₁ ; γ₂) disj (o₁ ; o₂) sep =
  ≼-trans (≼-refl (;-interchange (γ₁ ↓ Y) (γ₂ ↓ Y) (γ₁ ↓ X) (γ₂ ↓ X)
                                 (mob-XY γ₁ γ₂ sep)))
          (≼-cong-; (canon-core R γ₁ disj o₁ (sepXY-;ˡ sep))
                    (canon-core R γ₂ disj o₂ (sepXY-;ʳ sep)))
