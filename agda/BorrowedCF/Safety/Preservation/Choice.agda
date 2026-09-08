-- | Preservation of process typing for the choice rule `R-Choice`.
--
--   Unlike every other structural rule, `R-Choice` leaves the two binder
--   groups alone and only re-types their heads: the selected branch replaces
--   the choice on both endpoints.  The proof therefore has three ingredients:
--   `Choice.Session` (both endpoints resolve to dual continuations),
--   `Choice.Count` (each handle occurs exactly once, so it occurs nowhere but
--   in its own redex) and `Choice.Retype` (a derivation that does not mention
--   the two handles survives the change of context).
module BorrowedCF.Safety.Preservation.Choice where

open import Data.Nat.ListAction using (sum)
open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆)

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Domain using (dom)
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomCons using (acq-;-¬brn)

open import BorrowedCF.Simulation.Support.Confine using (count; count-self; count0⇒∉dom; ≼⇒count≤)

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Support.ComWeaken using (Fr)
open import BorrowedCF.Safety.Preservation.Choice.Count
open import BorrowedCF.Safety.Preservation.Choice.Retype
open import BorrowedCF.Safety.Preservation.Choice.Session

open Variables
open Fin.Patterns
open Nat using (_≤_; s≤s; z≤n)

private variable b₁ b₂ : ℕ

------------------------------------------------------------------------
-- Two scraps of arithmetic.
------------------------------------------------------------------------

private
  right0 : ∀ a b → 1 ≤ a → (a + b) ≤ 1 → b ≡ 0
  right0 (suc a) b _ (s≤s le) = Nat.n≤0⇒n≡0 (Nat.≤-trans (Nat.m≤n+m b a) le)

  left0 : ∀ a b → 1 ≤ b → (a + b) ≤ 1 → a ≡ 0
  left0 a b 1≤b le = right0 b a 1≤b (Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm b a)) le)

  if-⟨⟩ : ∀ (i : Bool) (t₁ t₂ : 𝕊 0) → (𝕋 ∋ (if i then ⟨ t₁ ⟩ else ⟨ t₂ ⟩)) ≡ ⟨ if i then t₁ else t₂ ⟩
  if-⟨⟩ true  _ _ = refl
  if-⟨⟩ false _ _ = refl

pres-Choice : {Γ : Ctx n} {P : Proc (suc b₁ + sum B₁ + (suc b₂ + sum B₂) + n)} →
  ChanCx Γ → ∀ (E₁ E₂ : Frame* (suc b₁ + sum B₁ + (suc b₂ + sum B₂) + n)) (i : Bool) →
  (let y = wkʳ n (wkˡ (suc b₁ + sum B₁) 0F) in
   Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
     ((⟪ E₁ [ K (`select i) ·¹ (` 0F) ]* ⟫
       ∥ ⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫)
       ∥ P)) →
  (let y = wkʳ n (wkˡ (suc b₁ + sum B₁) 0F) in
   Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
     ((⟪ E₁ [ ` 0F ]* ⟫
       ∥ ⟪ E₂ [ `inj i (` y) ]* ⟫)
       ∥ P))
pres-Choice {n = n} {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂} {γ = γ} {Γ = Γ} {P = P}
            Γ-S E₁ E₂ i p
  with (T₁ ⸴ Γ₁) , (T₂ ⸴ Γ₂) , s , pl , N , ⊢B₁ , ⊢B₂ , C₁ , C₂ , p′ ← inv-ν p
  with αβ , γP , αβγ≤ , p″ , q ← inv-∥ p′
  with α , β , αβ≤ , p₁ , p₂ ← inv-∥ p″
  with 𝒫₁ , α′ , _ , _ , _ , _ , ≤α , eqU₁ , ϵ≤₁ , ⊢E₁ , ⊢sel·x ← ⊢[]*⁻¹ E₁ _ (inv-⟪⟫ p₁)
  with 𝒫₂ , β′ , _ , _ , _ , _ , ≤β , eqU₂ , ϵ≤₂ , ⊢E₂ , ⊢br·y ← ⊢[]*⁻¹ E₂ _ (inv-⟪⟫ p₂)
  with a₁ , α-sel , α-x , _ , ≤α′ , ≤a₁ , refl , ⊢select , ⊢x
    ← inv-·-unr ⊢sel·x (λ z → constFnUnr′ (inv-K z .proj₂ .proj₁) (inv-K z .proj₂ .proj₂ .proj₂))
  with a₂ , β-br , β-y , _ , ≤β′ , ≤a₂ , refl , ⊢branch , ⊢y
    ← inv-·-unr ⊢br·y (λ z → constFnUnr′ (inv-K z .proj₂ .proj₁) (inv-K z .proj₂ .proj₂ .proj₂))
  with _ , ⟨ brn≃₁ ⟩ `→ res≃₁ , []≤α-sel , `select ← inv-K ⊢select
  with _ , ⟨ brn≃₂ ⟩ `→ ⊕≃₂ , []≤β-br , `branch ← inv-K ⊢branch
  with ⟨ eq-x ⟩ , `x≤ ← inv-` ⊢x
  with eq-y′ , `y≤ ← inv-` ⊢y
  using look-y ← V.lookup-++ˡ (Γ₁ ⸴* T₂ ⸴ Γ₂) Γ (b₁ + sum B₁ ↑ʳ 0F) ■ V.lookup-++ʳ Γ₁ (T₂ ⸴ Γ₂) 0F
  with ⟨ eq-y ⟩ ← subst (_ ≃_) look-y eq-y′
  with s* , t₁ , t₂ , N* , σ≃ , τ≃ , C₁* , C₂*
    ← choice-split i N (≃-sym (≃-trans brn≃₁ eq-x)) (≃-sym (≃-trans brn≃₂ eq-y)) C₁ C₂
  = TP-Res N* pl ⊢B₁ ⊢B₂ C₁* C₂*
      (TP-Weaken (≼-re Rt final≤)
        (TP-Par (TP-Par ⊢th₁ ⊢th₂) (P-re Rt γP∉x γP∉y q)))
  where
  xv : 𝔽 (suc b₁ + sum B₁ + (suc b₂ + sum B₂) + n)
  xv = 0F

  yv′ : 𝔽 (suc b₁ + sum B₁ + (suc b₂ + sum B₂) + n)
  yv′ = wkʳ n (wkˡ (suc b₁ + sum B₁) 0F)

  Δ Δ′ : Ctx (suc b₁ + sum B₁ + (suc b₂ + sum B₂) + n)
  Δ  = ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) ⸴* Γ
  Δ′ = ((⟨ t₁ ⟩ ⸴ Γ₁) ⸴* (⟨ t₂ ⟩ ⸴ Γ₂)) ⸴* Γ

  ¬unr-x : ¬ Unr (Δ ﹫ 0F)
  ¬unr-x ⟨ () ⟩

  ¬unr-y : ¬ Unr (Δ ﹫ yv′)
  ¬unr-y u with ⟨ () ⟩ ← subst Unr look-y u

  Rt : Retyping Δ Δ′ 0F yv′
  Rt = record
    { agree = agree-two Γ₁ Γ₂ Γ
    ; unrOK = λ z u → case z Fin.≟ 0F of λ where
        (yes refl) → ⊥-elim (¬unr-x u)
        (no ¬x) → case z Fin.≟ yv′ of λ where
          (yes refl) → ⊥-elim (¬unr-y u)
          (no ¬y) → subst Unr (agree-two Γ₁ Γ₂ Γ z ¬x ¬y) u
    ; mobOK = λ z m → case z Fin.≟ 0F of λ where
        (yes refl) → ⊥-elim (¬mob-x m)
        (no ¬x) → case z Fin.≟ yv′ of λ where
          (yes refl) → ⊥-elim (¬mob-y m)
          (no ¬y) → subst Mobile (agree-two Γ₁ Γ₂ Γ z ¬x ¬y) m
    }
    where
    ¬mob-x : ¬ Mobile (Δ ﹫ 0F)
    ¬mob-x ⟨ _ , _ , e ⟩ = acq-;-¬brn (≃-trans (≃-trans brn≃₁ eq-x) e)
    ¬mob-y : ¬ Mobile (Δ ﹫ yv′)
    ¬mob-y m with ⟨ _ , _ , e ⟩ ← subst Mobile look-y m =
      acq-;-¬brn (≃-trans (≃-trans brn≃₂ eq-y) e)

  -- the head handle is used by its own redex, hence nowhere else
  x≼α′ : Δ ∶ (` 0F) ≼ α′
  x≼α′ = ≼-trans `x≤
           (≼-trans (≼-respˡ-≈ (join-[]₂ (Arr.dir a₁)) (≼-join (Arr.dir a₁) (≼-refl ≈-refl) []≤α-sel)) ≤α′)

  y≼β′ : Δ ∶ (` yv′) ≼ β′
  y≼β′ = ≼-trans `y≤
           (≼-trans (≼-respˡ-≈ (join-[]₂ (Arr.dir a₂)) (≼-join (Arr.dir a₂) (≼-refl ≈-refl) []≤β-br)) ≤β′)

  total≤ : ∀ {z} → ¬ Unr (Δ ﹫ z) → count z (Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ) ≡ 1 →
    ((count z α + count z β) + count z γP) ≤ 1
  total≤ ¬u eq = Nat.≤-trans
    (≼⇒count≤ ¬u (≼-trans (≼-cong-∥ αβ≤ (≼-refl ≈-refl)) αβγ≤))
    (Nat.≤-reflexive eq)

  1≤cα′ : 1 ≤ count 0F α′
  1≤cα′ = Nat.≤-trans (Nat.≤-reflexive (sym (count-self xv))) (≼⇒count≤ ¬unr-x x≼α′)

  1≤cβ′ : 1 ≤ count yv′ β′
  1≤cβ′ = Nat.≤-trans (Nat.≤-reflexive (sym (count-self yv′))) (≼⇒count≤ ¬unr-y y≼β′)

  1≤cx : 1 ≤ count 0F α
  1≤cx = Nat.≤-trans 1≤cα′
    (Nat.≤-trans (Nat.m≤n+m (count 0F α′) (count 0F (𝒫₁ [ [] ]𝓅)))
    (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₁ 0F α′)))
                 (≼⇒count≤ ¬unr-x ≤α)))

  1≤cy : 1 ≤ count yv′ β
  1≤cy = Nat.≤-trans 1≤cβ′
    (Nat.≤-trans (Nat.m≤n+m (count yv′ β′) (count yv′ (𝒫₂ [ [] ]𝓅)))
    (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₂ yv′ β′)))
                 (≼⇒count≤ ¬unr-y ≤β)))

  cx-total : ((count 0F α + count 0F β) + count 0F γP) ≤ 1
  cx-total = total≤ ¬unr-x (count-Fr-x b₁ B₁ b₂ B₂ γ)

  cy-total : ((count yv′ α + count yv′ β) + count yv′ γP) ≤ 1
  cy-total = total≤ ¬unr-y (count-Fr-y b₁ B₁ b₂ B₂ γ)

  cxαβ≤1 : (count 0F α + count 0F β) ≤ 1
  cxαβ≤1 = Nat.≤-trans (Nat.m≤m+n (count 0F α + count 0F β) (count 0F γP)) cx-total

  cyαβ≤1 : (count yv′ α + count yv′ β) ≤ 1
  cyαβ≤1 = Nat.≤-trans (Nat.m≤m+n (count yv′ α + count yv′ β) (count yv′ γP)) cy-total

  cxβ0 : count 0F β ≡ 0
  cxβ0 = right0 (count 0F α) (count 0F β) 1≤cx cxαβ≤1

  cxγP0 : count 0F γP ≡ 0
  cxγP0 = right0 (count 0F α + count 0F β) (count 0F γP)
            (Nat.≤-trans 1≤cx (Nat.m≤m+n (count 0F α) (count 0F β))) cx-total

  cyα0 : count yv′ α ≡ 0
  cyα0 = left0 (count yv′ α) (count yv′ β) 1≤cy cyαβ≤1

  cyγP0 : count yv′ γP ≡ 0
  cyγP0 = right0 (count yv′ α + count yv′ β) (count yv′ γP)
            (Nat.≤-trans 1≤cy (Nat.m≤n+m (count yv′ β) (count yv′ α))) cy-total

  cxα≤1 : count 0F α ≤ 1
  cxα≤1 = Nat.≤-trans (Nat.m≤m+n (count 0F α) (count 0F β)) cxαβ≤1

  cyβ≤1 : count yv′ β ≤ 1
  cyβ≤1 = Nat.≤-trans (Nat.m≤n+m (count yv′ β) (count yv′ α)) cyαβ≤1

  cx𝒫₁0 : count 0F (𝒫₁ [ [] ]𝓅) ≡ 0
  cx𝒫₁0 = left0 (count 0F (𝒫₁ [ [] ]𝓅)) (count 0F α′) 1≤cα′
    (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₁ 0F α′)))
      (Nat.≤-trans (≼⇒count≤ ¬unr-x ≤α) cxα≤1))

  cy𝒫₂0 : count yv′ (𝒫₂ [ [] ]𝓅) ≡ 0
  cy𝒫₂0 = left0 (count yv′ (𝒫₂ [ [] ]𝓅)) (count yv′ β′) 1≤cβ′
    (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₂ yv′ β′)))
      (Nat.≤-trans (≼⇒count≤ ¬unr-y ≤β) cyβ≤1))

  cx𝒫₂0 : count 0F (𝒫₂ [ [] ]𝓅) ≡ 0
  cx𝒫₂0 = Nat.n≤0⇒n≡0
    (Nat.≤-trans (Nat.m≤m+n (count 0F (𝒫₂ [ [] ]𝓅)) (count 0F β′))
      (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₂ 0F β′)))
        (Nat.≤-trans (≼⇒count≤ ¬unr-x ≤β) (Nat.≤-reflexive cxβ0))))

  cy𝒫₁0 : count yv′ (𝒫₁ [ [] ]𝓅) ≡ 0
  cy𝒫₁0 = Nat.n≤0⇒n≡0
    (Nat.≤-trans (Nat.m≤m+n (count yv′ (𝒫₁ [ [] ]𝓅)) (count yv′ α′))
      (Nat.≤-trans (Nat.≤-reflexive (sym (count-[-]𝓅 𝒫₁ yv′ α′)))
        (Nat.≤-trans (≼⇒count≤ ¬unr-y ≤α) (Nat.≤-reflexive cyα0))))

  γP∉x : 0F ∉ dom γP
  γP∉x = count0⇒∉dom γP cxγP0
  γP∉y : yv′ ∉ dom γP
  γP∉y = count0⇒∉dom γP cyγP0

  ⊢E₁′ = F*-re Rt (count0⇒∉dom (𝒫₁ [ [] ]𝓅) cx𝒫₁0) (count0⇒∉dom (𝒫₁ [ [] ]𝓅) cy𝒫₁0) ⊢E₁
  ⊢E₂′ = F*-re Rt (count0⇒∉dom (𝒫₂ [ [] ]𝓅) cx𝒫₂0) (count0⇒∉dom (𝒫₂ [ [] ]𝓅) cy𝒫₂0) ⊢E₂

  ⊢th₁ = TP-Expr (T-Conv eqU₁ ϵ≤₁ ⊢⟨ ⊢E₁′
           [ T-Conv (≃-trans ⟨ ≃-sym σ≃ ⟩ res≃₁) ℙ≤ϵ (T-Var 0F refl) ]*⟩)

  ⊢th₂ = TP-Expr (T-Conv eqU₂ ϵ≤₂ ⊢⟨ ⊢E₂′
           [ T-Conv ⊕≃₂ ℙ≤ϵ
               (T-Inj {i = i} (T-Conv (subst (⟨ t₂ ⟩ ≃_) (sym (if-⟨⟩ i _ _)) ⟨ ≃-sym τ≃ ⟩)
                                      ℙ≤ϵ (T-Var yv′ look-y′))) ]*⟩)
    where
    look-y′ : Δ′ ﹫ yv′ ≡ ⟨ t₂ ⟩
    look-y′ = V.lookup-++ˡ (Γ₁ ⸴* ⟨ t₂ ⟩ ⸴ Γ₂) Γ (b₁ + sum B₁ ↑ʳ 0F)
            ■ V.lookup-++ʳ Γ₁ (⟨ t₂ ⟩ ⸴ Γ₂) 0F

  final≤ : Δ ∶ ((𝒫₁ [ ` 0F ]𝓅) ∥ (𝒫₂ [ ` yv′ ]𝓅)) ∥ γP ≼ Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ
  final≤ = ≼-trans
    (≼-cong-∥ (≼-cong-∥ (≼-trans ([-]𝓅-≼ 𝒫₁ x≼α′) ≤α) (≼-trans ([-]𝓅-≼ 𝒫₂ y≼β′) ≤β)) (≼-refl ≈-refl))
    (≼-trans (≼-cong-∥ αβ≤ (≼-refl ≈-refl)) αβγ≤)
