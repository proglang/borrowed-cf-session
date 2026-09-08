-- | Preamble for the completeness induction (agent C4).
--
--   Everything here depends only on the core modules (plus `Simulation/Support/Confine`
--   for `count`), never on the files of C1/C2/C3/C5, so it type-checks on its own.
--
--   Owner: agent C4.
module BorrowedCF.Completeness.Main.Base where

open import Data.Bool.Properties using (if-float)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; ⁅_⁆; ∁)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁺; x∈p∪q⁻; _∈?_; ∉⊥)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.All.Properties as All

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base

open import BorrowedCF.Simulation.Support.Confine
  using (count; ≼⇒count≤; count0⇒∉dom; count-join-Dir)

import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Types.Substitution as 𝐓

open Nat.Variables
open Fin.Patterns

private variable
  e e′ e₁ e₂ : Tm n
  α β : Struct n
  Γ̂ : Ctx n

------------------------------------------------------------------------
-- Transferring structural judgments along a change of context.
--
-- `≼` and `≈` mention the context only through `Unr` and `Mobile` of the types of
-- the variables that occur, so a context whose types satisfy at least as many of
-- those predicates admits the same structural judgments.

allCx-ctx : ∀ {ℓ} {P : Pred 𝕋 ℓ} {Γ₁ Γ₂ : Ctx n} →
  (∀ x → P (Γ₁ ﹫ x) → P (Γ₂ ﹫ x)) → AllCx P Γ₁ α → AllCx P Γ₂ α
allCx-ctx f [] = []
allCx-ctx f (x ∥ y) = allCx-ctx f x ∥ allCx-ctx f y
allCx-ctx f (x ; y) = allCx-ctx f x ; allCx-ctx f y
allCx-ctx f (`_ {x} px) = ` f x px

module _ {Γ₁ Γ₂ : Ctx n}
  (uf : ∀ x → Unr (Γ₁ ﹫ x) → Unr (Γ₂ ﹫ x))
  (mf : ∀ x → Mobile (Γ₁ ﹫ x) → Mobile (Γ₂ ﹫ x))
  where

  ≈′-ctx : Γ₁ ∶ α ≈′ β → Γ₂ ∶ α ≈′ β
  ≈′-ctx ;′-assoc = ;′-assoc
  ≈′-ctx (;′-cong₁ x) = ;′-cong₁ (≈′-ctx x)
  ≈′-ctx (;′-cong₂ x) = ;′-cong₂ (≈′-ctx x)
  ≈′-ctx ∥′-unit = ∥′-unit
  ≈′-ctx ∥′-assoc = ∥′-assoc
  ≈′-ctx ∥′-comm = ∥′-comm
  ≈′-ctx (∥′-cong₁ x) = ∥′-cong₁ (≈′-ctx x)
  ≈′-ctx (∥′-dup U) = ∥′-dup (allCx-ctx uf U)
  ≈′-ctx (∥′-tm-; U) = ∥′-tm-; (Sum.map (allCx-ctx mf) (allCx-ctx mf) U)

  ≈-ctx : Γ₁ ∶ α ≈ β → Γ₂ ∶ α ≈ β
  ≈-ctx = Eq*.gmap id ≈′-ctx

  ≼-ctx : Γ₁ ∶ α ≼ β → Γ₂ ∶ α ≼ β
  ≼-ctx (≼-refl x) = ≼-refl (≈-ctx x)
  ≼-ctx (≼-∅ U) = ≼-∅ (allCx-ctx uf U)
  ≼-ctx ≼-wk = ≼-wk
  ≼-ctx (≼-trans x y) = ≼-trans (≼-ctx x) (≼-ctx y)
  ≼-ctx (≼-cong-; x y) = ≼-cong-; (≼-ctx x) (≼-ctx y)
  ≼-ctx (≼-cong-∥ x y) = ≼-cong-∥ (≼-ctx x) (≼-ctx y)

------------------------------------------------------------------------
-- `Unr` is reflected by instantiation (no session type is unrestricted, and all
-- other type constructors are preserved by `subTy`).  `Mobile` is NOT — see
-- Main-STATUS.md, FINDING 1.

subTy-unr⁻¹ : {T : 𝕋} → Unr (subTy T σ) → Unr T
subTy-unr⁻¹ {T = `⊤} `⊤ = `⊤
subTy-unr⁻¹ {T = T ⟨ a ⟩→ U} (arr x) = arr x
subTy-unr⁻¹ {T = T ⊗⟨ d ⟩ U} (u₁ ⊗ u₂) = subTy-unr⁻¹ u₁ ⊗ subTy-unr⁻¹ u₂
subTy-unr⁻¹ {T = T ⊕ U} (u₁ ⊕ u₂) = subTy-unr⁻¹ u₁ ⊕ subTy-unr⁻¹ u₂
subTy-unr⁻¹ {T = ⟨ s ⟩} ⟨ () ⟩

-- `T̂` approximates `T` when instantiating it with σ gives `T` up to ≃.
unr-approx : {T̂ T : 𝕋} → subTy T̂ σ ≃ T → Unr T → Unr T̂
unr-approx eq u = subTy-unr⁻¹ (unr-≃ (≃-sym eq) u)

unr-approx⁻¹ : {T̂ T : 𝕋} → subTy T̂ σ ≃ T → Unr T̂ → Unr T
unr-approx⁻¹ eq u = unr-≃ eq (subTy-unr u)

mob-approx⁻¹ : {T̂ T : 𝕋} → subTy T̂ σ ≃ T → Mobile T̂ → Mobile T
mob-approx⁻¹ eq m = mobile-≃ eq (subTy-mobile m)

------------------------------------------------------------------------
-- Small facts about `join`, `dom` and `↓`.

module _ {A : Set} ⦃ J : Join A ⦄ (a : A) {Γ : Ctx n} where

  absorbʳ : UnrCx Γ β → Γ ∶ α ≼ join a α β
  absorbʳ U = ≼-trans (≼-refl (≈-sym (join-[]₂ a))) (≼-join a (≼-refl ≈-refl) (≼-∅ U))

  absorbˡ : UnrCx Γ α → Γ ∶ β ≼ join a α β
  absorbˡ U = ≼-trans (≼-refl (≈-sym (join-[]₁ a))) (≼-join a (≼-∅ U) (≼-refl ≈-refl))

allCx-of-dom : ∀ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} (γ : Struct n) →
  (∀ x → x ∈ dom γ → P (Γ ﹫ x)) → AllCx P Γ γ
allCx-of-dom [] f = []
allCx-of-dom (` x) f = ` f x (x∈⁅x⁆ x)
allCx-of-dom (α ∥ β) f =
  allCx-of-dom α (λ x x∈ → f x (x∈p∪q⁺ (inj₁ x∈))) ∥
  allCx-of-dom β (λ x x∈ → f x (x∈p∪q⁺ (inj₂ x∈)))
allCx-of-dom (α ; β) f =
  allCx-of-dom α (λ x x∈ → f x (x∈p∪q⁺ (inj₁ x∈))) ;
  allCx-of-dom β (λ x x∈ → f x (x∈p∪q⁺ (inj₂ x∈)))

dom-↓⁺ : (γ : Struct n) {X : Subset n} {x : 𝔽 n} → x ∈ dom γ → x ∈ X → x ∈ dom (γ ↓ X)
dom-↓⁺ [] x∈ x∈X = ⊥-elim (∉⊥ x∈)
dom-↓⁺ (` y) {X} {x} x∈ x∈X with x∈⁅y⁆⇒x≡y y x∈
... | refl with y ∈? X
... | yes _ = x∈⁅x⁆ y
... | no y∉ = ⊥-elim (y∉ x∈X)
dom-↓⁺ (α ∥ β) x∈ x∈X with x∈p∪q⁻ (dom α) (dom β) x∈
... | inj₁ y = x∈p∪q⁺ (inj₁ (dom-↓⁺ α y x∈X))
... | inj₂ y = x∈p∪q⁺ (inj₂ (dom-↓⁺ β y x∈X))
dom-↓⁺ (α ; β) x∈ x∈X with x∈p∪q⁻ (dom α) (dom β) x∈
... | inj₁ y = x∈p∪q⁺ (inj₁ (dom-↓⁺ α y x∈X))
... | inj₂ y = x∈p∪q⁺ (inj₂ (dom-↓⁺ β y x∈X))

dom⇒count : (γ : Struct n) {x : 𝔽 n} → x ∈ dom γ → 1 Nat.≤ count x γ
dom⇒count γ {x} x∈ with count x γ in eq
... | zero  = ⊥-elim (count0⇒∉dom γ eq x∈)
... | suc k = Nat.s≤s Nat.z≤n

-- The linearity lever: a variable occurring in BOTH sides of an admissible split of a
-- linear structure must be unrestricted.
shared-unr : {Γ : Ctx n} {γ : Struct n} (d : Dir) →
  LinStruct Γ γ → Γ ∶ join d α β ≼ γ →
  ∀ x → x ∈ dom α → x ∈ dom β → Unr (Γ ﹫ x)
shared-unr {α = α} {β = β} {Γ = Γ} {γ = γ} d lin ≤γ x x∈α x∈β with unr? (Γ ﹫ x)
... | yes u = u
... | no ¬u =
  ⊥-elim (bust (Nat.≤-trans two≤ (Nat.≤-trans (≼⇒count≤ ¬u ≤γ) (lin x ¬u))))
  where
    two≤ : 2 Nat.≤ count x (join d α β)
    two≤ = Nat.≤-trans (Nat.+-mono-≤ (dom⇒count α x∈α) (dom⇒count β x∈β))
                       (Nat.≤-reflexive (sym (count-join-Dir d x α β)))
    bust : 2 Nat.≤ 1 → ⊥
    bust (Nat.s≤s ())

------------------------------------------------------------------------
-- Effects.

≤ϵℙ⇒≡ℙ : ϵ ≤ϵ ℙ → ϵ ≡ ℙ
≤ϵℙ⇒≡ℙ ℙ≤ϵ = refl

⊔ϵ-lub : ϵ₁ ≤ϵ ϵ → ϵ₂ ≤ϵ ϵ → (ϵ₁ ⊔ϵ ϵ₂) ≤ϵ ϵ
⊔ϵ-lub ℙ≤ϵ q = q
⊔ϵ-lub 𝕀≤𝕀 q = 𝕀≤𝕀

------------------------------------------------------------------------
-- Inverting `≃` at a type constructor.  Note that `_`→_` and `_⊗_` of `≃𝕋` keep the
-- SAME `Arr` / `Dir` annotation on both sides, so the annotation is recovered too.

arrow-inv : {T̂ T U : 𝕋} → subTy T̂ σ ≃ (T ⟨ a ⟩→ U) →
  Σ[ T̂₁ ∈ 𝕋 ] Σ[ T̂₂ ∈ 𝕋 ] (T̂ ≡ T̂₁ ⟨ a ⟩→ T̂₂) × (subTy T̂₁ σ ≃ T) × (subTy T̂₂ σ ≃ U)
arrow-inv {T̂ = T̂₁ ⟨ a ⟩→ T̂₂} (eq₁ `→ eq₂) = T̂₁ , T̂₂ , refl , eq₁ , eq₂

pair-inv : {T̂ T U : 𝕋} → subTy T̂ σ ≃ (T ⊗⟨ d ⟩ U) →
  Σ[ T̂₁ ∈ 𝕋 ] Σ[ T̂₂ ∈ 𝕋 ] (T̂ ≡ T̂₁ ⊗⟨ d ⟩ T̂₂) × (subTy T̂₁ σ ≃ T) × (subTy T̂₂ σ ≃ U)
pair-inv {T̂ = T̂₁ ⊗⟨ d ⟩ T̂₂} (eq₁ ⊗ eq₂) = T̂₁ , T̂₂ , refl , eq₁ , eq₂

sum-inv : {T̂ T U : 𝕋} → subTy T̂ σ ≃ (T ⊕ U) →
  Σ[ T̂₁ ∈ 𝕋 ] Σ[ T̂₂ ∈ 𝕋 ] (T̂ ≡ T̂₁ ⊕ T̂₂) × (subTy T̂₁ σ ≃ T) × (subTy T̂₂ σ ≃ U)
sum-inv {T̂ = T̂₁ ⊕ T̂₂} (eq₁ ⊕ eq₂) = T̂₁ , T̂₂ , refl , eq₁ , eq₂

------------------------------------------------------------------------
-- The two declarative inversions missing from `Terms/Base.agda`.

inv-ƛ : {Γ : Ctx n} → Γ ; γ ⊢ ƛ e ∶ T ∣ ϵ →
  Σ[ T₁ ∈ 𝕋 ] Σ[ a ∈ Arr ] Σ[ U ∈ 𝕋 ] Σ[ γ₀ ∈ Struct n ]
    (T₁ ⟨ a ⟩→ U ≃ T)
      × (Γ ∶ γ₀ ≼ γ)
      × (Arr.Unr a → UnrCx Γ γ₀)
      × (Arr.Mobile a → MobCx Γ γ₀)
      × (T₁ ⸴ Γ ; join (Arr.dir a) (` 0F) (𝐂.wk γ₀) ⊢ e ∶ U ∣ Arr.eff a)
inv-ƛ (T-Abs Γ-unr Γ-mob d) =
  _ , _ , _ , _ , ≃-refl , ≼-refl ≈-refl , Γ-unr , Γ-mob , d
inv-ƛ (T-Conv T≃ ϵ≤ x) =
  let _ , _ , _ , _ , eq , ≤γ , u , m , d = inv-ƛ x in
  _ , _ , _ , _ , ≃-trans eq T≃ , ≤γ , u , m , d
inv-ƛ (T-Weaken γ≤ x) =
  let _ , _ , _ , _ , eq , ≤γ , u , m , d = inv-ƛ x in
  _ , _ , _ , _ , eq , ≼-trans ≤γ γ≤ , u , m , d

inv-μ : {Γ : Ctx n} {e′ : Tm (suc n)} → Γ ; γ ⊢ μ e′ ∶ T ∣ ϵ →
  Σ[ e ∈ Tm (suc (suc n)) ] Σ[ T₁ ∈ 𝕋 ] Σ[ a ∈ Arr ] Σ[ U ∈ 𝕋 ] Σ[ γ₀ ∈ Struct n ]
    (e′ ≡ ƛ e)
      × (T₁ ⟨ a ⟩→ U ≃ T)
      × (Γ ∶ γ₀ ≼ γ)
      × UnrCx Γ γ₀
      × Arr.Unr a
      × (T₁ ⸴ (T₁ ⟨ a ⟩→ U) ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ₀) ⊢ e ∶ U ∣ Arr.eff a)
inv-μ (T-AbsRec Γ-unr a-unr d) =
  _ , _ , _ , _ , _ , refl , ≃-refl , ≼-refl ≈-refl , Γ-unr , a-unr , d
inv-μ (T-Conv T≃ ϵ≤ x) with inv-μ x
... | _ , _ , _ , _ , _ , refl , eq , ≤γ , u , au , d =
  _ , _ , _ , _ , _ , refl , ≃-trans eq T≃ , ≤γ , u , au , d
inv-μ (T-Weaken γ≤ x) with inv-μ x
... | _ , _ , _ , _ , _ , refl , eq , ≤γ , u , au , d =
  _ , _ , _ , _ , _ , refl , eq , ≼-trans ≤γ γ≤ , u , au , d

------------------------------------------------------------------------
-- Solving the types of a subderivation.  `⊢-sub` instantiates every type of a
-- declarative derivation; with a `Solving` substitution the result is solved, and a
-- solved term is left untouched.

s₀ : UV.Sub
s₀ = UV.someSub

s₀-solving : Solving s₀
s₀-solving = someSub-solving

solve-ty : {Γ : Ctx n} → SolvedTm e → Γ ; γ ⊢ e ∶ T ∣ ϵ →
  subCtx Γ s₀ ; γ ⊢ e ∶ subTy T s₀ ∣ ϵ
solve-ty Se d = subst (λ t → _ ; _ ⊢ t ∶ _ ∣ _) (subTm-id Se) (⊢-sub s₀ d)

-- A context approximation survives solving the declarative context.
approx-sub : {Γ : Ctx n} → Solving σ →
  (∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x) →
  (∀ x → subTy (Γ̂ ﹫ x) σ ≃ subCtx Γ s₀ ﹫ x)
approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap x =
  ≃-trans (≃-reflexive (sym (subTy-id (subTy-solved (Γ̂ ﹫ x) Sσ))))
          (≃-trans (subTy-≃ (ap x)) (≃-reflexive (sym (V.lookup-map x _ Γ))))

lin-sub : ∀ {n} (Γ : Ctx n) (γ : Struct n) → LinStruct Γ γ → LinStruct (subCtx Γ s₀) γ
lin-sub Γ γ lin x ¬u =
  lin x (λ u → ¬u (subst Unr (sym (V.lookup-map x _ Γ)) (subTy-unr u)))

-- `subTy` at a unification variable of a CLOSED session type is just the substitution:
-- the renaming out of the empty scope is the identity.
uvar-subTy : (α : UVar) (σ : UV.Sub) → subTy {𝕤} {0} (`` α) σ ≡ UV.ap σ α
uvar-subTy α σ = 𝐓.⋯-id ⦃ 𝐓.Kᵣ ⦄ (UV.ap σ α) (λ ())

------------------------------------------------------------------------
-- Mobility constraints.

allMobile-solved : (Γ : Ctx n) (γ : Struct n) → MobCx Γ γ → SolvedΔ (allMobile Γ γ) σ
allMobile-solved Γ [] mc = All.[]
allMobile-solved Γ (` x) (` px) = subTy-mobile px All.∷ All.[]
allMobile-solved Γ (α ∥ β) (M₁ ∥ M₂) =
  All.++⁺ (allMobile-solved Γ α M₁) (allMobile-solved Γ β M₂)
allMobile-solved Γ (α ; β) (M₁ ; M₂) =
  All.++⁺ (allMobile-solved Γ α M₁) (allMobile-solved Γ β M₂)

-- The A-Abs mobility constraints, discharged from the DECLARATIVE `MobCx` through the
-- context approximation.  `Mobile` is respected by `≃`, so this needs no reflection.
allMobile-approx : ∀ {n} (Γ̂ Γ : Ctx n) (γ : Struct n) {σ : UV.Sub} →
  (∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x) → MobCx Γ γ → SolvedΔ (allMobile Γ̂ γ) σ
allMobile-approx Γ̂ Γ [] ap mc = All.[]
allMobile-approx Γ̂ Γ (` x) ap (` px) = mobile-≃ (≃-sym (ap x)) px All.∷ All.[]
allMobile-approx Γ̂ Γ (α ∥ β) ap (M₁ ∥ M₂) =
  All.++⁺ (allMobile-approx Γ̂ Γ α ap M₁) (allMobile-approx Γ̂ Γ β ap M₂)
allMobile-approx Γ̂ Γ (α ; β) ap (M₁ ; M₂) =
  All.++⁺ (allMobile-approx Γ̂ Γ α ap M₁) (allMobile-approx Γ̂ Γ β ap M₂)

------------------------------------------------------------------------
-- Projections that turn the cases missing from `SolvedTm` / `SolvedC` on as soon as
-- `Algorithmic/Solved.agda` gains the constructors (Main-STATUS.md, FINDING 3).

sTm-let : SolvedTm {n} (`let e₁ `in e₂) → SolvedTm e₁ × SolvedTm e₂
sTm-let (`let s₁ `in s₂) = s₁ , s₂
