module BorrowedCF.Simulation.Theorems.Acq where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Frames
open import BorrowedCF.Simulation.TranslationProperties
open import BorrowedCF.Simulation.Flatten
open import BorrowedCF.Simulation.BlockPermutation
open import BorrowedCF.Simulation.NuExtrusion
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Simulation.Theorems.Toolkit
open import BorrowedCF.Simulation.Theorems.NuSwap
open import BorrowedCF.Simulation.Theorems.LSplit
open import BorrowedCF.Simulation.Theorems.RSplit using (φ^-split; φ^-resplit; recombine; canonₛ-head-irrel; subst-cod-app; frame*-⋯-then-ren; frame-plug*ᵣ)
open import BorrowedCF.Simulation.AcqFront using (canonₛ-acq-front; handle-a; handle-a-K; handle-c; acq-a-link; acq-x-link; acq-c-link)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

φ^-suc-out : ∀ {N} r (W : 𝐔.Proc (suc r + N)) →
             φ^ (suc r) W ≡ 𝐔.φ (φ^ r (subst 𝐔.Proc (sym (Nat.+-suc r N)) W))
φ^-suc-out {N} r W =
  sym ( φ-φ^ r (subst 𝐔.Proc (sym (Nat.+-suc r N)) W)
      ■ cong (φ^ (suc r)) (subst-subst-sym (Nat.+-suc r N)) )

φ^-acq-─→ : ∀ k {N} {P Q : 𝐔.Proc (k + N)} → P 𝐔R.─→ₚ Q → φ^ k P 𝐔R.─→ₚ φ^ k Q
φ^-acq-─→ zero    pq = pq
φ^-acq-─→ (suc k) pq = φ^-acq-─→ k (𝐔R.RU-Sync pq)

-- canonₛ-handle's middle (channel index) at the [] prefix depends only on the cc's x, not e₁/e₂.
hmid-irrel : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {N} (e₁ e₁' e₂ e₂' : Tm N) (x : 𝔽 N) →
             proj₁ (proj₂ (canonₛ-handle [] (e₁ , x , e₂) b₁ B₁))
             ≡ proj₁ (proj₂ (canonₛ-handle [] (e₁' , x , e₂') b₁ B₁))
hmid-irrel zero    []      e₁ e₁' e₂ e₂' x = refl
hmid-irrel (suc _) []      e₁ e₁' e₂ e₂' x = refl
hmid-irrel zero    (b ∷ B) e₁ e₁' e₂ e₂' x = refl
hmid-irrel (suc _) (b ∷ B) e₁ e₁' e₂ e₂' x = refl

-- canonₛ-handle's third (continuation) at the [] prefix depends only on e₂ (and x for the
-- middle of nested chains), not on e₁; with the same e₂/x it is irrelevant in e₁.
hthird-irrel : ∀ (b₁ : ℕ) (B₁ : 𝐓.BindGroup) {N} (e₁ e₁' e₂ : Tm N) (x : 𝔽 N) →
               proj₁ (proj₂ (proj₂ (canonₛ-handle [] (e₁ , x , e₂) b₁ B₁)))
               ≡ proj₁ (proj₂ (proj₂ (canonₛ-handle [] (e₁' , x , e₂) b₁ B₁)))
hthird-irrel zero    []      e₁ e₁' e₂ x = refl
hthird-irrel (suc _) []      e₁ e₁' e₂ x = refl
hthird-irrel zero    (b ∷ B) e₁ e₁' e₂ x = refl
hthird-irrel (suc _) (b ∷ B) e₁ e₁' e₂ x = refl

U-acq : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {b₁ : ℕ} {B₁ B₂ : 𝐓.BindGroup}
        {E : Frame* (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
        {P : 𝐓.Proc (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
        {k : ℕ} (ρ⁻ : k →ᵣ (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m))
        (ρ⁻-skip : ∀ y → ρ⁻ y ≢ 0F)
        {E₀ : Frame* k} (Eeq : E ≡ E₀ ⋯ᶠ* ρ⁻)
        {P₀ : 𝐓.Proc k} (Peq : P ≡ P₀ 𝐓.⋯ₚ ρ⁻)
      → U[ 𝐓.ν (zero ∷ suc b₁ ∷ B₁) B₂ (𝐓.⟪ E [ K `acq · (` 0F) ]* ⟫ 𝐓.∥ P) ] σ
          𝐔R.─→ₚ U[ 𝐓.ν (suc b₁ ∷ B₁) B₂ (𝐓.⟪ E [ ` zero ]* ⟫ 𝐓.∥ P) ] σ
U-acq {m} {n} σ Vσ {b₁} {B₁} {B₂} {E} {P} ρ⁻ ρ⁻-skip {E₀} Eeq {P₀} Peq =
  𝐔R.RU-Struct (lhsChain ◅◅ shapeStep) firing rhsRecon
  where
    C₁ : 𝐓.BindGroup
    C₁ = zero ∷ suc b₁ ∷ B₁
    C₁' : 𝐓.BindGroup
    C₁' = suc b₁ ∷ B₁
    Q : 𝐓.Proc (sum C₁ + sum B₂ + m)
    Q = 𝐓.⟪ E [ K `acq · (` 0F) ]* ⟫ 𝐓.∥ P
    sC₁ = syncs C₁
    sC₁' = syncs C₁'
    sB₂ = syncs B₂
    pre : ℕ
    pre = sB₂ + sC₁'
    -- leaf substitution for the LHS flattening (identical shape to LSplit's leafσ).
    cc1 : UChan (2 + n)
    cc1 = (K `unit , 0F , K `unit)
    cc2 : UChan (sC₁ + (2 + n))
    cc2 = (K `unit , weaken* ⦃ Kᵣ ⦄ sC₁ 1F , K `unit)
    Xleaf : (sum C₁ + sum B₂) →ₛ (sB₂ + (sC₁ + (2 + n)))
    Xleaf = (λ i → canonₛ C₁ cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ canonₛ B₂ cc2
    σpart : m →ₛ (sB₂ + (sC₁ + (2 + n)))
    σpart = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    leafσ : (sum C₁ + sum B₂ + m) →ₛ (sB₂ + (sC₁ + (2 + n)))
    leafσ = Xleaf ++ₛ σpart
    Vleafσ : VSub leafσ
    Vleafσ = ++ₛ-VSub
      (++ₛ-VSub (weaken-VSub sB₂ (VSub-canonₛ C₁ cc1 (V-K , V-K)))
                (VSub-canonₛ B₂ cc2 (V-K , V-K)))
      (weaken-VSub sB₂ (weaken-VSub sC₁ (weaken-VSub 2 Vσ)))
    BODY_L : 𝐔.Proc (sB₂ + (sC₁ + (2 + n)))
    BODY_L = (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.∥ (Flags B₂ 𝐔.∥ U[ Q ] leafσ)

    flatStep : U[ 𝐓.ν C₁ B₂ Q ] σ 𝐔.≋ 𝐔.ν (φ^ sC₁ (φ^ sB₂ BODY_L))
    flatStep = Uν-flat σ C₁ B₂ Q

    -- Restructuring: combine the inner blocks, peel the leading zero-φ, bubble it down
    -- past the pre = sB₂ + sC₁' inner φ's, then extrude that block past the ν.
    W₀ : 𝐔.Proc ((sB₂ + sC₁) + (2 + n))
    W₀ = subst 𝐔.Proc (sym (Nat.+-assoc sB₂ sC₁ (2 + n))) BODY_L
    combineStep : 𝐔.ν (φ^ sC₁ (φ^ sB₂ BODY_L)) 𝐔.≋ 𝐔.ν (φ^ (sB₂ + sC₁) W₀)
    combineStep = 𝐔.ν-cong (≡→≋ (φ^-split sB₂ sC₁ BODY_L))

    W₁ : 𝐔.Proc (suc pre + (2 + n))
    W₁ = subst (λ j → 𝐔.Proc (j + (2 + n))) (Nat.+-suc sB₂ sC₁') W₀
    castStep : 𝐔.ν (φ^ (sB₂ + sC₁) W₀) 𝐔.≋ 𝐔.ν (φ^ (suc pre) W₁)
    castStep = 𝐔.ν-cong (≡→≋ (φ^-cast (Nat.+-suc sB₂ sC₁') W₀))

    W₂ : 𝐔.Proc (pre + suc (2 + n))
    W₂ = subst 𝐔.Proc (sym (Nat.+-suc pre (2 + n))) W₁
    popStep : 𝐔.ν (φ^ (suc pre) W₁) 𝐔.≋ 𝐔.ν (𝐔.φ (φ^ pre W₂))
    popStep = 𝐔.ν-cong (≡→≋ (φ^-suc-out pre W₁))

    bubbleStep : 𝐔.ν (𝐔.φ (φ^ pre W₂)) 𝐔.≋
                 𝐔.ν (φ^ pre (𝐔.φ (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1)))
    bubbleStep = 𝐔.ν-cong (φ-past-block pre W₂)

    extrudeStep : 𝐔.ν (φ^ pre (𝐔.φ (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1))) 𝐔.≋
                  φ^ pre (𝐔.ν ((𝐔.φ (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1)) 𝐔.⋯ₚ assocSwapᵣ pre 2))
    extrudeStep = ν-φ^-comm pre (𝐔.φ (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1))

    MIDBODY : 𝐔.Proc (1 + (2 + (pre + n)))
    MIDBODY = (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1) 𝐔.⋯ₚ (assocSwapᵣ pre 2 ↑)
    restructStep : φ^ pre (𝐔.ν ((𝐔.φ (W₂ 𝐔.⋯ₚ assocSwapᵣ pre 1)) 𝐔.⋯ₚ assocSwapᵣ pre 2)) 𝐔.≋
                   φ^ pre (𝐔.ν (𝐔.φ MIDBODY))
    restructStep = ≡→≋ refl

    lhsChain : U[ 𝐓.ν C₁ B₂ Q ] σ 𝐔.≋ φ^ pre (𝐔.ν (𝐔.φ MIDBODY))
    lhsChain = flatStep ◅◅ combineStep ◅◅ castStep ◅◅ popStep ◅◅ bubbleStep ◅◅ extrudeStep ◅◅ restructStep

    -- Net scope cast of the restructuring, and W₂ as a single subst on BODY_L.
    cEq : sB₂ + (sC₁ + (2 + n)) ≡ pre + suc (2 + n)
    cEq = sym (Nat.+-assoc sB₂ sC₁ (2 + n))
        ■ cong (Nat._+ (2 + n)) (Nat.+-suc sB₂ sC₁')
        ■ sym (Nat.+-suc pre (2 + n))
    e₁eq : (sB₂ + sC₁) + (2 + n) ≡ suc pre + (2 + n)
    e₁eq = cong (Nat._+ (2 + n)) (Nat.+-suc sB₂ sC₁')
    e₀eq : sB₂ + (sC₁ + (2 + n)) ≡ (sB₂ + sC₁) + (2 + n)
    e₀eq = sym (Nat.+-assoc sB₂ sC₁ (2 + n))
    e₂eq : suc pre + (2 + n) ≡ pre + suc (2 + n)
    e₂eq = sym (Nat.+-suc pre (2 + n))
    castW₂ : W₂ ≡ subst 𝐔.Proc cEq BODY_L
    castW₂ =
        cong (subst 𝐔.Proc e₂eq) (sym (subst-cong+P {N = 2 + n} (Nat.+-suc sB₂ sC₁') W₀))
      ■ cong (subst 𝐔.Proc e₂eq) (subst-subst e₀eq)
      ■ subst-subst (e₀eq ■ e₁eq)
      ■ cong (λ p → subst 𝐔.Proc p BODY_L) (≡-irrelevant ((e₀eq ■ e₁eq) ■ e₂eq) cEq)

    -- MIDBODY as BODY_L renamed by a single composite Ψ.
    aS1 : (pre + suc (2 + n)) →ᵣ (1 + (pre + (2 + n)))
    aS1 = assocSwapᵣ pre 1
    aS2↑ : (1 + (pre + (2 + n))) →ᵣ (1 + (2 + (pre + n)))
    aS2↑ = assocSwapᵣ pre 2 ↑
    Ψ : (sB₂ + (sC₁ + (2 + n))) →ᵣ (1 + (2 + (pre + n)))
    Ψ = subst (λ z → z →ᵣ (1 + (pre + (2 + n)))) (sym cEq) aS1 ·ₖ aS2↑
    midEq : MIDBODY ≡ BODY_L 𝐔.⋯ₚ Ψ
    midEq =
        cong (𝐔._⋯ₚ aS2↑)
          ( cong (𝐔._⋯ₚ aS1) castW₂
          ■ subst-⋯ₚ′ cEq BODY_L aS1 )
      ■ 𝐔.fusionₚ BODY_L (subst (λ z → z →ᵣ (1 + (pre + (2 + n)))) (sym cEq) aS1) aS2↑

    -- toℕ action of Ψ: w<pre ↦ 3+w ; w=pre ↦ 0 ; w=pre+1 ↦ 1 ; w=pre+2 ↦ 2 ; w≥pre+3 ↦ w.
    Ψ-toℕ : ∀ (v : 𝔽 (sB₂ + (sC₁ + (2 + n)))) →
            Fin.toℕ (Ψ v) ≡ Fin.toℕ (aS2↑ (aS1 (subst 𝔽 cEq v)))
    Ψ-toℕ v = cong Fin.toℕ (cong (aS2↑) (subst-→ᵣ-app cEq aS1 v))

    -- aS1 on a position with toℕ = w, given the structural facts about pre.
    aS1ℕ-lt : ∀ (u : 𝔽 (pre + suc (2 + n))) → Fin.toℕ u Nat.< pre → Fin.toℕ (aS1 u) ≡ suc (Fin.toℕ u)
    aS1ℕ-lt u lt = toℕ-assoc-lt pre 1 u lt
    aS1ℕ-eq : ∀ (u : 𝔽 (pre + suc (2 + n))) → Fin.toℕ u ≡ pre → Fin.toℕ (aS1 u) ≡ 0
    aS1ℕ-eq u eq = toℕ-assoc-mid pre 1 u (Nat.≤-reflexive (sym eq))
                     (subst (Nat._< pre + 1) (sym eq) (Nat.m<m+n pre (Nat.s≤s Nat.z≤n)))
                 ■ cong (Nat._∸ pre) eq ■ Nat.n∸n≡0 pre
    aS1ℕ-gt : ∀ (u : 𝔽 (pre + suc (2 + n))) → pre Nat.< Fin.toℕ u → Fin.toℕ (aS1 u) ≡ Fin.toℕ u
    aS1ℕ-gt u gt = toℕ-assoc-ge pre 1 u (subst (Nat._≤ Fin.toℕ u) (Nat.+-comm 1 pre) gt)

    -- aS2↑ on a successor index.
    aS2↑ℕ-suc : ∀ (j : 𝔽 (pre + (2 + n))) → Fin.toℕ (aS2↑ (Fin.suc j)) ≡ suc (Fin.toℕ (assocSwapᵣ pre 2 j))
    aS2↑ℕ-suc j = toℕ-↑ (assocSwapᵣ pre 2) (Fin.suc j)
    aS2↑ℕ-0 : Fin.toℕ (aS2↑ 0F) ≡ 0
    aS2↑ℕ-0 = toℕ-↑ (assocSwapᵣ pre 2 {n}) 0F

    cvℕ : ∀ (v : 𝔽 (sB₂ + (sC₁ + (2 + n)))) → Fin.toℕ (subst 𝔽 cEq v) ≡ Fin.toℕ v
    cvℕ v = toℕ-subst𝔽 cEq v

    -- Ψ on the zero-flag binder (toℕ v = pre) lands at 0F.
    Ψ-zero : ∀ (v : 𝔽 (sB₂ + (sC₁ + (2 + n)))) → Fin.toℕ v ≡ pre → Ψ v ≡ 0F
    Ψ-zero v eq = Fin.toℕ-injective
      ( Ψ-toℕ v
      ■ cong Fin.toℕ (cong aS2↑ (Fin.toℕ-injective (aS1ℕ-eq (subst 𝔽 cEq v) (cvℕ v ■ eq))))
      ■ aS2↑ℕ-0 )

    -- aS1 toℕ is never 0 unless its input toℕ is pre.
    aS1ℕ-pos : ∀ (u : 𝔽 (pre + suc (2 + n))) → Fin.toℕ u ≢ pre → Fin.toℕ (aS1 u) ≢ 0
    aS1ℕ-pos u u≢ with Nat.<-cmp (Fin.toℕ u) pre
    ... | tri< lt _ _ = λ z → 0≢suc (sym (sym (aS1ℕ-lt u lt) ■ z))
      where 0≢suc : ∀ {kk} → 0 ≢ suc kk
            0≢suc ()
    ... | tri≈ _ eq _ = ⊥-elim (u≢ eq)
    ... | tri> _ _ gt = λ z → Nat.<⇒≢ (Nat.≤-trans (Nat.s≤s Nat.z≤n) gt)
                                    (sym (sym (aS1ℕ-gt u gt) ■ z))

    -- aS2↑ toℕ is 0 only at 0F.
    aS2↑-toℕ0 : ∀ (w : 𝔽 (1 + (pre + (2 + n)))) → Fin.toℕ (aS2↑ w) ≡ 0 → Fin.toℕ w ≡ 0
    aS2↑-toℕ0 0F       _  = refl
    aS2↑-toℕ0 (suc w′) z0 = ⊥-elim (0≢suc (sym (sym (aS2↑ℕ-suc w′) ■ z0)))
      where 0≢suc : ∀ {kk} → 0 ≢ suc kk
            0≢suc ()

    -- Ψ avoids 0F off the zero-flag binder.
    Ψ-avoid : ∀ (v : 𝔽 (sB₂ + (sC₁ + (2 + n)))) → Fin.toℕ v ≢ pre → Ψ v ≢ 0F
    Ψ-avoid v v≢ Ψv0 =
      aS1ℕ-pos (subst 𝔽 cEq v) (λ e → v≢ (sym (cvℕ v) ■ e))
        (aS2↑-toℕ0 (aS1 (subst 𝔽 cEq v)) (sym (Ψ-toℕ v) ■ cong Fin.toℕ Ψv0))

    -- down : strip index 0 (0F↦0F, suc j↦j); left-inverse of weakenᵣ on indices ≥1.
    down : (1 + (2 + (pre + n))) →ᵣ (2 + (pre + n))
    down 0F      = 0F
    down (suc j) = j
    down·wk-id : ∀ (i : 𝔽 (1 + (2 + (pre + n)))) → i ≢ 0F → (down ·ₖ weakenᵣ) i ≡ i
    down·wk-id 0F      i≢ = ⊥-elim (i≢ refl)
    down·wk-id (suc j) _  = refl

    -- σ₀: the strengthened leaf substitution for the post-firing scope 2+(pre+n).
    σ₀ : (sum C₁ + sum B₂ + m) →ₛ (2 + (pre + n))
    σ₀ i = leafσ i ⋯ Ψ ⋯ down
    Vσ₀ : VSub σ₀
    Vσ₀ i = value-⋯ (value-⋯ (Vleafσ i) Ψ (λ _ → V-`)) down (λ _ → V-`)

    -- The post-firing frame and the data/continuation extracted at scope 2+(pre+n).
    Fr : Frame* (2 + (pre + n))
    Fr = frame*-⋯ E σ₀ Vσ₀
    -- The leading-flag split of Flags C₁ at base 2+n: Flags(zero∷C₁') is, up to a +-suc
    -- subst, ((0F↦set)⋯wk*sC₁') ∥ Flags{suc(2+n)}C₁'.  The residual uses Flags{suc(2+n)}C₁'
    -- cast into the leaf scope sB₂+(sC₁+(2+n)) by castC₁' (the subst's renaming view), then
    -- co-located by Ψ ; down.
    castC₁' : (sC₁' + suc (2 + n)) →ᵣ (sB₂ + (sC₁ + (2 + n)))
    castC₁' i = weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) i)
    -- The residual flag groups, strengthened off the zero-flag binder via `down`.
    resFlagC₁' : 𝐔.Proc (2 + (pre + n))
    resFlagC₁' = Flags {suc (2 + n)} C₁' 𝐔.⋯ₚ castC₁' 𝐔.⋯ₚ Ψ 𝐔.⋯ₚ down
    resFlagB₂ : 𝐔.Proc (2 + (pre + n))
    resFlagB₂ = Flags B₂ 𝐔.⋯ₚ Ψ 𝐔.⋯ₚ down
    Pacq : 𝐔.Proc (2 + (pre + n))
    Pacq = resFlagC₁' 𝐔.∥ (resFlagB₂ 𝐔.∥ U[ P ] σ₀)
    -- data var of the acquired channel: σ₀ applied to handle 0F gives the triple; its
    -- middle component is (` suc X); X is the residual channel handle.
    Xv : 𝔽 (2 + (pre + n))
    Xv = down (Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ (proj₁ (proj₂ (canonₛ-acq-front b₁ B₁ {n})))))

    -- The reclaimed channel's continuation term (RU-Acquire's free `e`): the THIRD
    -- component of the acq triple, renamed to the post-firing scope.  NOT K`unit — for
    -- b₁=0 ∧ B₁≠[] it is a chain-continuation variable.
    acqCont : Tm (2 + (pre + n))
    acqCont = proj₁ (proj₂ (proj₂ (canonₛ-acq-front b₁ B₁ {n})))
                ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ⋯ down

    -- RU-Acquire LHS body in MIDBODY's scope (3+(pre+n)).
    acqLHSbody : 𝐔.Proc (1 + (2 + (pre + n)))
    acqLHSbody = (0F 𝐔.↦ 𝐔.set)
               𝐔.∥ ( 𝐔.⟪ (Fr ⋯ᶠ* weakenᵣ) [ K `acq · (((` 0F) ⊗ (` suc Xv)) ⊗ (acqCont ⋯ weakenᵣ)) ]* ⟫
                   𝐔.∥ (Pacq 𝐔.⋯ₚ weakenᵣ) )
    -- MIDBODY = (G1 ⋯ Ψ) ∥ ((G2 ⋯ Ψ) ∥ (leaf ⋯ Ψ)), distributing Ψ over BODY_L's ∥.
    G1Ψ G2Ψ leafΨ : 𝐔.Proc (1 + (2 + (pre + n)))
    G1Ψ   = (Flags C₁ 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.⋯ₚ Ψ
    G2Ψ   = Flags B₂ 𝐔.⋯ₚ Ψ
    leafΨ = U[ Q ] leafσ 𝐔.⋯ₚ Ψ
    midDistrib : MIDBODY ≡ G1Ψ 𝐔.∥ (G2Ψ 𝐔.∥ leafΨ)
    midDistrib = midEq

    -- Reconcile MIDBODY with acqLHSbody.  REMAINING WORK (the flag-merge + leaf-factoring,
    -- analogues of RSplit.flagsRenMerge and LSplit.lwk-id-off0):
    --   • pull the zero flag (G1Ψ's first ∥, var pre ↦ 0F by Ψ-zero) to the front as (0F↦set);
    --   • the acq thread (in leafΨ = ⟪(E[acq·0F])⋯leafσ⋯Ψ⟫ ∥ U[P]⋯) rewrites to
    --     ⟪(Fr⋯ᶠ*weakenᵣ)[acq·((`0F⊗`suc Xv)⊗(K`unit⋯weakenᵣ))]⟫ via canonₛ-acq-front + Ψ-zero
    --     + the down/weakenᵣ frame factoring (needs leafσ avoids var pre off handle 0F,
    --     i.e. canonₛ-head-irrel);
    --   • the residual flags (Flags C₁' from G1Ψ, G2Ψ) + U[P]leafσ⋯Ψ reassemble as Pacq⋯weakenᵣ.
    -- NOTE: this requires Pacq to bundle the residual flags (currently Pacq = U[P]σ₀ is a
    -- placeholder; the residual-flag bundle is the flagsRenMerge analogue).
    -- `down ; weakenᵣ` acts as identity on any image of Ψ that is ≠ 0F (avoids the zero binder).
    Ψdwk-avoid : ∀ (v : 𝔽 (sB₂ + (sC₁ + (2 + n)))) → Fin.toℕ v ≢ pre →
                 (Ψ ·ₖ (down ·ₖ weakenᵣ)) v ≡ Ψ v
    Ψdwk-avoid v v≢ = down·wk-id (Ψ v) (Ψ-avoid v v≢)

    -- toℕ of the leading-sB₂ flag positions: i ↑ˡ (sC₁ + (2+n)) has toℕ = toℕ i < sB₂ ≤ pre.
    sB₂-lt-pre : ∀ (i : 𝔽 sB₂) → Fin.toℕ (i ↑ˡ (sC₁ + (2 + n))) ≢ pre
    sB₂-lt-pre i eq = Nat.<-irrefl refl (subst (Nat._< pre) eq
      (Nat.<-≤-trans (subst (Nat._< sB₂) (sym (Fin.toℕ-↑ˡ i (sC₁ + (2 + n)))) (Fin.toℕ<n i))
                     (Nat.m≤m+n sB₂ sC₁')))

    -- G2 flag group: factor the post-Ψ form through down ; weakenᵣ.
    G2factor : G2Ψ ≡ resFlagB₂ 𝐔.⋯ₚ weakenᵣ
    G2factor =
        Flags-⋯-cong B₂ Ψ (Ψ ·ₖ (down ·ₖ weakenᵣ))
          (λ i → sym (Ψdwk-avoid (i ↑ˡ (sC₁ + (2 + n))) (sB₂-lt-pre i)))
      ■ sym (𝐔.fusionₚ (Flags B₂) Ψ (down ·ₖ weakenᵣ))
      ■ sym (𝐔.fusionₚ (Flags B₂ 𝐔.⋯ₚ Ψ) down weakenᵣ)

    -- G1 = Flags{2+n}(zero∷C₁') ⋯ wk*sB₂.  Composite renaming θ₁ = (subst-cast wk*sB₂) ·ₖ Ψ
    -- carries the unfolded (LF ∥ Flags C₁') into MIDBODY's scope.
    θ₁ : (sC₁' + suc (2 + n)) →ᵣ (1 + (2 + (pre + n)))
    θ₁ = subst (λ z → z →ᵣ (sB₂ + (sC₁ + (2 + n)))) (sym (Nat.+-suc sC₁' (2 + n)))
               (weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ Ψ
    -- The unfolded leading flag of Flags(zero∷C₁'): position weaken* sC₁' 0F.
    leadPos : 𝔽 (sC₁' + suc (2 + n))
    leadPos = weaken* ⦃ Kᵣ ⦄ sC₁' 0F
    -- θ₁ ≗ castC₁' ; Ψ (the subst-cast is just castC₁').
    θ₁≗castΨ : θ₁ ≗ (castC₁' ·ₖ Ψ)
    θ₁≗castΨ i = cong Ψ (subst-→ᵣ-app (Nat.+-suc sC₁' (2 + n)) (weaken* ⦃ Kᵣ ⦄ sB₂) i)
    -- θ₁ sends the leading-flag position to 0F (it co-locates onto the zero binder).
    θ₁-lead : θ₁ leadPos ≡ 0F
    θ₁-lead = θ₁≗castΨ leadPos ■ Ψ-zero (castC₁' leadPos) leadℕ
      where
        leadℕ : Fin.toℕ (castC₁' leadPos) ≡ pre
        leadℕ = toℕ-wk sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) leadPos)
              ■ cong (sB₂ +_) ( toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) leadPos
                              ■ toℕ-wk sC₁' 0F ■ Nat.+-identityʳ sC₁' )
    -- θ₁ on a Flags C₁' position (i ↑ˡ suc(2+n)) equals castC₁' there (and avoids 0F).
    θ₁-resC : ∀ (i : 𝔽 sC₁') →
              (θ₁ ·ₖ (down ·ₖ weakenᵣ)) (i ↑ˡ suc (2 + n)) ≡ θ₁ (i ↑ˡ suc (2 + n))
    θ₁-resC i = down·wk-id (θ₁ (i ↑ˡ suc (2 + n)))
                  (λ z0 → Ψ-avoid (castC₁' (i ↑ˡ suc (2 + n))) resℕ≢
                            (sym (θ₁≗castΨ (i ↑ˡ suc (2 + n))) ■ z0))
      where
        resℕ : Fin.toℕ (castC₁' (i ↑ˡ suc (2 + n))) ≡ sB₂ + Fin.toℕ i
        resℕ = toℕ-wk sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) (i ↑ˡ suc (2 + n)))
             ■ cong (sB₂ +_) ( toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) (i ↑ˡ suc (2 + n))
                             ■ Fin.toℕ-↑ˡ i (suc (2 + n)) )
        resℕ≢ : Fin.toℕ (castC₁' (i ↑ˡ suc (2 + n))) ≢ pre
        resℕ≢ eq = Nat.<-irrefl refl
          (subst (Nat._< pre) (sym resℕ ■ eq)
            (Nat.+-monoʳ-< sB₂ (Fin.toℕ<n i)))

    -- The leading-flag split + co-location for G1.
    G1factor : G1Ψ 𝐔.≋ (0F 𝐔.↦ 𝐔.set) 𝐔.∥ (resFlagC₁' 𝐔.⋯ₚ weakenᵣ)
    G1factor = ≡→≋
      ( cong (𝐔._⋯ₚ Ψ)
          ( cong (𝐔._⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) (flagsCunfold)
          ■ subst-⋯ₚ′ (Nat.+-suc sC₁' (2 + n)) (LF 𝐔.∥ Flags {suc (2 + n)} C₁') (weaken* ⦃ Kᵣ ⦄ sB₂) )
      ■ 𝐔.fusionₚ (LF 𝐔.∥ Flags {suc (2 + n)} C₁')
          (subst (λ z → z →ᵣ (sB₂ + (sC₁ + (2 + n)))) (sym (Nat.+-suc sC₁' (2 + n))) (weaken* ⦃ Kᵣ ⦄ sB₂)) Ψ
      ■ cong₂ 𝐔._∥_ leadEq resEq )
      where
        LF : 𝐔.Proc (sC₁' + suc (2 + n))
        LF = (0F 𝐔.↦ 𝐔.set) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sC₁'
        flagsCunfold : Flags {2 + n} C₁ ≡
          subst 𝐔.Proc (Nat.+-suc sC₁' (2 + n)) (LF 𝐔.∥ Flags {suc (2 + n)} C₁')
        flagsCunfold = refl
        leadEq : LF 𝐔.⋯ₚ θ₁ ≡ (0F 𝐔.↦ 𝐔.set)
        leadEq = cong (𝐔._↦ 𝐔.set) θ₁-lead
        resEq : Flags {suc (2 + n)} C₁' 𝐔.⋯ₚ θ₁ ≡ resFlagC₁' 𝐔.⋯ₚ weakenᵣ
        resEq =
            𝐔.⋯ₚ-cong (Flags {suc (2 + n)} C₁') θ₁≗castΨ
          ■ Flags-⋯-cong C₁' (castC₁' ·ₖ Ψ) ((castC₁' ·ₖ Ψ) ·ₖ (down ·ₖ weakenᵣ))
              (λ i → sym ( cong (down ·ₖ weakenᵣ) (sym (θ₁≗castΨ (i ↑ˡ suc (2 + n))))
                         ■ θ₁-resC i ■ θ₁≗castΨ (i ↑ˡ suc (2 + n)) ))
          ■ sym (𝐔.fusionₚ (Flags {suc (2 + n)} C₁') (castC₁' ·ₖ Ψ) (down ·ₖ weakenᵣ))
          ■ cong (𝐔._⋯ₚ (down ·ₖ weakenᵣ)) (sym (𝐔.fusionₚ (Flags {suc (2 + n)} C₁') castC₁' Ψ))
          ■ sym (𝐔.fusionₚ (Flags {suc (2 + n)} C₁' 𝐔.⋯ₚ castC₁' 𝐔.⋯ₚ Ψ) down weakenᵣ)

    -- ── RHS side (group C₁', no leading zero-chain): mirror of lhsChain without the pop. ──
    Q_R : 𝐓.Proc (sum C₁' + sum B₂ + m)
    Q_R = 𝐓.⟪ E [ ` zero ]* ⟫ 𝐓.∥ P
    cc2R : UChan (sC₁' + (2 + n))
    cc2R = (K `unit , weaken* ⦃ Kᵣ ⦄ sC₁' 1F , K `unit)
    XleafR : (sum C₁' + sum B₂) →ₛ (sB₂ + (sC₁' + (2 + n)))
    XleafR = (λ i → canonₛ C₁' cc1 i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ canonₛ B₂ cc2R
    σpartR : m →ₛ (sB₂ + (sC₁' + (2 + n)))
    σpartR = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC₁' ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    leafσR : (sum C₁' + sum B₂ + m) →ₛ (sB₂ + (sC₁' + (2 + n)))
    leafσR = XleafR ++ₛ σpartR
    VleafσR : VSub leafσR
    VleafσR = ++ₛ-VSub
      (++ₛ-VSub (weaken-VSub sB₂ (VSub-canonₛ C₁' cc1 (V-K , V-K)))
                (VSub-canonₛ B₂ cc2R (V-K , V-K)))
      (weaken-VSub sB₂ (weaken-VSub sC₁' (weaken-VSub 2 Vσ)))
    BODY_R : 𝐔.Proc (sB₂ + (sC₁' + (2 + n)))
    BODY_R = (Flags C₁' 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.∥ (Flags B₂ 𝐔.∥ U[ Q_R ] leafσR)

    flatStepR : U[ 𝐓.ν C₁' B₂ Q_R ] σ 𝐔.≋ 𝐔.ν (φ^ sC₁' (φ^ sB₂ BODY_R))
    flatStepR = Uν-flat σ C₁' B₂ Q_R

    -- ── canonₛ leaf relation (the O1 crux): off the consumed handle 0F, the C₁ leaf is the
    -- C₁' leaf with one sync slot inserted at index sC₁' (via weakenᵣ ↑* sC₁').  Proven by:
    -- the zero chain reduces canonₛ(zero∷C₁') to canonₛ C₁' threaded with cc-rest; head-irrel
    -- drops the cc-rest.e₁ = (`0F) (matters only at 0); canonₛ-nat rebases by weakenᵣ.
    cc-rest : UChan (suc (2 + n))
    cc-rest = ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ)
    canonC-rel : ∀ (d : 𝔽 (sum C₁')) → Fin.toℕ d ≢ 0 →
                 canonₛ C₁ cc1 d ≡ subst Tm (Nat.+-suc sC₁' (2 + n))
                                     (canonₛ C₁' cc1 d ⋯ (weakenᵣ ↑* sC₁'))
    canonC-rel d d≢ =
        subst-Π (Nat.+-suc sC₁' (2 + n)) (canonₛ C₁' cc-rest) d
      ■ cong (subst Tm (Nat.+-suc sC₁' (2 + n)))
          ( canonₛ-head-irrel C₁' (` 0F) (K `unit) (suc 0F) (K `unit ⋯ weakenᵣ) d d≢
          ■ canonₛ-nat C₁' cc1 weakenᵣ d )

    -- ins0 inserts the zero-chain sync slot at flat index pre = sB₂+sC₁' into the C₁' leaf scope.
    -- Built from (weakenᵣ ↑* sC₁') ↑* sB₂ (codomain sB₂+(sC₁'+suc(2+n))) cast to sB₂+(sC₁+(2+n)).
    ins0 : (sB₂ + (sC₁' + (2 + n))) →ᵣ (sB₂ + (sC₁ + (2 + n)))
    ins0 = subst (λ z → (sB₂ + (sC₁' + (2 + n))) →ᵣ z)
                 (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n)))
                 (((weakenᵣ {2 + n} ↑* sC₁') ↑* sB₂))
    -- ρcolR : the RHS co-location renaming (insert slot, then Ψ, then strengthen).
    ρcolR : (sB₂ + (sC₁' + (2 + n))) →ᵣ (2 + (pre + n))
    ρcolR = ins0 ·ₖ (Ψ ·ₖ down)

    -- weaken*sB₂ commutes with (ρ ↑* sC₁') ↑* sB₂ vs the cast: pointwise renaming equality.
    insComm : ((weakenᵣ ↑* sC₁') ·ₖ subst (λ z → z →ᵣ (sB₂ + (sC₁ + (2 + n)))) (sym (Nat.+-suc sC₁' (2 + n))) (weaken* ⦃ Kᵣ ⦄ sB₂))
              ≗ (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ins0)
    insComm i = Fin.toℕ-injective
      ( cong Fin.toℕ (subst-→ᵣ-app (Nat.+-suc sC₁' (2 + n)) (weaken* ⦃ Kᵣ ⦄ sB₂) ((weakenᵣ ↑* sC₁') i))
      ■ toℕ-wk sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) ((weakenᵣ ↑* sC₁') i))
      ■ cong (sB₂ +_) (toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) ((weakenᵣ ↑* sC₁') i))
      ■ sym ( cong Fin.toℕ (subst-cod-app (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) ((weakenᵣ {2 + n} ↑* sC₁') ↑* sB₂) (weaken* ⦃ Kᵣ ⦄ sB₂ i))
            ■ toℕ-subst𝔽 (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) (((weakenᵣ {2 + n} ↑* sC₁') ↑* sB₂) (weaken* ⦃ Kᵣ ⦄ sB₂ i))
            ■ ↑*-hi (weakenᵣ {2 + n} ↑* sC₁') sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ i) hge
            ■ cong (λ z → sB₂ + Fin.toℕ ((weakenᵣ {2 + n} ↑* sC₁') z)) redEq ) )
      where
        hge : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ i)
        hge = subst (sB₂ Nat.≤_) (sym (toℕ-wk sB₂ i)) (Nat.m≤m+n sB₂ (Fin.toℕ i))
        redEq : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ i) hge ≡ i
        redEq = Fin.toℕ-injective
          ( toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ i) hge
          ■ cong (Nat._∸ sB₂) (toℕ-wk sB₂ i) ■ Nat.m+n∸m≡n sB₂ (Fin.toℕ i) )

    -- Data-region leaf relation: canonₛ C₁ cc1 d ⋯ wk*sB₂ = (canonₛ C₁' cc1 d ⋯ wk*sB₂) ⋯ ins0.
    leafσ-ins-data : ∀ (d : 𝔽 (sum C₁')) → Fin.toℕ d ≢ 0 →
                     canonₛ C₁ cc1 d ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
                     ≡ (canonₛ C₁' cc1 d ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ins0
    leafσ-ins-data d d≢ =
        cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (canonC-rel d d≢)
      ■ subst-⋯ (Nat.+-suc sC₁' (2 + n)) (canonₛ C₁' cc1 d ⋯ (weakenᵣ ↑* sC₁')) (weaken* ⦃ Kᵣ ⦄ sB₂)
      ■ fusion (canonₛ C₁' cc1 d) (weakenᵣ ↑* sC₁') (subst (λ z → z →ᵣ (sB₂ + (sC₁ + (2 + n)))) (sym (Nat.+-suc sC₁' (2 + n))) (weaken* ⦃ Kᵣ ⦄ sB₂))
      ■ ⋯-cong (canonₛ C₁' cc1 d) insComm
      ■ sym (fusion (canonₛ C₁' cc1 d) (weaken* ⦃ Kᵣ ⦄ sB₂) ins0)

    -- ── B₂-flag region: canonₛ B₂ cc2 = canonₛ B₂ cc2R ⋯ ins0. ──
    -- cc2 = mapᶜ (weakenᵣ↑*sC₁'-cast) cc2R, so canonₛ-nat applies (then ↑* sB₂ = ins0).
    insSync : (sC₁' + (2 + n)) →ᵣ (sC₁ + (2 + n))
    insSync = subst (λ z → (sC₁' + (2 + n)) →ᵣ z) (Nat.+-suc sC₁' (2 + n)) (weakenᵣ {2 + n} ↑* sC₁')
    cc2-map : mapᶜ insSync cc2R ≡ cc2
    cc2-map = cong₂ _,_ refl (cong₂ _,_ ch refl)
      where
        ch : insSync (weaken* ⦃ Kᵣ ⦄ sC₁' 1F) ≡ weaken* ⦃ Kᵣ ⦄ sC₁ 1F
        ch = Fin.toℕ-injective
          ( cong Fin.toℕ (subst-cod-app (Nat.+-suc sC₁' (2 + n)) (weakenᵣ {2 + n} ↑* sC₁') (weaken* ⦃ Kᵣ ⦄ sC₁' 1F))
          ■ toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) ((weakenᵣ {2 + n} ↑* sC₁') (weaken* ⦃ Kᵣ ⦄ sC₁' 1F))
          ■ ↑*-hi (weakenᵣ {2 + n}) sC₁' (weaken* ⦃ Kᵣ ⦄ sC₁' 1F) hge
          ■ cong (sC₁' +_) wkℕ
          ■ Nat.+-suc sC₁' 1
          ■ sym (toℕ-wk sC₁ 1F) )
          where
            hge : sC₁' Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sC₁' 1F)
            hge = subst (sC₁' Nat.≤_) (sym (toℕ-wk sC₁' 1F)) (Nat.m≤m+n sC₁' 1)
            redEq : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sC₁' 1F) hge ≡ 1F
            redEq = Fin.toℕ-injective
              ( toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ sC₁' 1F) hge
              ■ cong (Nat._∸ sC₁') (toℕ-wk sC₁' 1F) ■ Nat.m+n∸m≡n sC₁' 1 )
            wkℕ : Fin.toℕ (weakenᵣ {2 + n} (Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sC₁' 1F) hge)) ≡ 2
            wkℕ = cong (λ z → Fin.toℕ (weaken* ⦃ Kᵣ ⦄ 1 z)) redEq
                ■ toℕ-wk 1 (Fin.suc (Fin.zero {n}))
    wksC : (sC₁' + (2 + n)) →ᵣ (sC₁' + suc (2 + n))
    wksC = weakenᵣ {2 + n} ↑* sC₁'
    insSyncℕq : ∀ (q : 𝔽 (sC₁' + (2 + n))) → Fin.toℕ (insSync q) ≡ Fin.toℕ (wksC q)
    insSyncℕq q =
        cong Fin.toℕ (subst-cod-app (Nat.+-suc sC₁' (2 + n)) wksC q)
      ■ toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) (wksC q)
    insSync↑sB₂ : (insSync ↑* sB₂) ≗ ins0
    insSync↑sB₂ i = Fin.toℕ-injective
      ( toℕ-↑* insSync sB₂ i
      ■ go (Fin.splitAt sB₂ i)
      ■ sym ( cong Fin.toℕ (subst-cod-app (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) (wksC ↑* sB₂) i)
            ■ toℕ-subst𝔽 (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) ((wksC ↑* sB₂) i)
            ■ toℕ-↑* wksC sB₂ i ) )
      where
        go : (s : 𝔽 sB₂ ⊎ 𝔽 (sC₁' + (2 + n))) →
             [ Fin.toℕ , (λ q → sB₂ + Fin.toℕ (insSync q)) ]′ s
             ≡ [ Fin.toℕ , (λ q → sB₂ + Fin.toℕ (wksC q)) ]′ s
        go (inj₁ _) = refl
        go (inj₂ q) = cong (sB₂ +_) (insSyncℕq q)
    leafσ-ins-B₂ : ∀ (w : 𝔽 (sum B₂)) →
                   canonₛ B₂ cc2 w ≡ canonₛ B₂ cc2R w ⋯ ins0
    leafσ-ins-B₂ w =
        cong (λ z → canonₛ B₂ z w) (sym cc2-map)
      ■ canonₛ-nat B₂ cc2R insSync w
      ■ ⋯-cong (canonₛ B₂ cc2R w) insSync↑sB₂

    -- ── base region: σpart i = σpartR i ⋯ ins0 (the deep base is shifted by the slot insert). ──
    baseRen : ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sC₁') ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ ins0
              ≗ ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sC₁) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)
    baseRen j = Fin.toℕ-injective
      ( cong Fin.toℕ (subst-cod-app (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) (wksC ↑* sB₂) base')
      ■ toℕ-subst𝔽 (cong (sB₂ +_) (Nat.+-suc sC₁' (2 + n))) ((wksC ↑* sB₂) base')
      ■ ↑*-hi wksC sB₂ base' hge
      ■ cong (sB₂ +_) ( ↑*-hi (weakenᵣ {2 + n}) sC₁' (Fin.reduce≥ base' hge) hge2
                      ■ cong (sC₁' +_) ( cong (λ z → Fin.toℕ (weaken* ⦃ Kᵣ ⦄ 1 z)) red2
                                       ■ toℕ-wk 1 (red3) ) )
      ■ baseℕ )
      where
        base' : 𝔽 (sB₂ + (sC₁' + (2 + n)))
        base' = weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC₁' (weaken* ⦃ Kᵣ ⦄ 2 j))
        rhsv : 𝔽 (sB₂ + (sC₁ + (2 + n)))
        rhsv = weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC₁ (weaken* ⦃ Kᵣ ⦄ 2 j))
        red3 : 𝔽 (2 + n)
        red3 = weaken* ⦃ Kᵣ ⦄ 2 j
        hge : sB₂ Nat.≤ Fin.toℕ base'
        hge = subst (sB₂ Nat.≤_) (sym (toℕ-wk sB₂ _)) (Nat.m≤m+n sB₂ _)
        hge2 : sC₁' Nat.≤ Fin.toℕ (Fin.reduce≥ base' hge)
        hge2 = subst (sC₁' Nat.≤_)
          (sym ( toℕ-reduce≥ base' hge ■ cong (Nat._∸ sB₂) (toℕ-wk sB₂ _) ■ Nat.m+n∸m≡n sB₂ _ ))
          (subst (sC₁' Nat.≤_) (sym (toℕ-wk sC₁' _)) (Nat.m≤m+n sC₁' _))
        red2 : Fin.reduce≥ (Fin.reduce≥ base' hge) hge2 ≡ weaken* ⦃ Kᵣ ⦄ 2 j
        red2 = Fin.toℕ-injective
          ( toℕ-reduce≥ (Fin.reduce≥ base' hge) hge2
          ■ cong (Nat._∸ sC₁') ( toℕ-reduce≥ base' hge ■ cong (Nat._∸ sB₂) (toℕ-wk sB₂ _) ■ Nat.m+n∸m≡n sB₂ _ )
          ■ cong (Nat._∸ sC₁') (toℕ-wk sC₁' (weaken* ⦃ Kᵣ ⦄ 2 j)) ■ Nat.m+n∸m≡n sC₁' _ )
        baseℕ : sB₂ + (sC₁' + suc (Fin.toℕ (weaken* ⦃ Kᵣ ⦄ 2 j))) ≡ Fin.toℕ rhsv
        baseℕ = cong (sB₂ +_) (Nat.+-suc sC₁' (Fin.toℕ (weaken* ⦃ Kᵣ ⦄ 2 j)))
              ■ sym ( toℕ-wk sB₂ _ ■ cong (sB₂ +_) (toℕ-wk sC₁ (weaken* ⦃ Kᵣ ⦄ 2 j)) )
    fuse3 : ∀ {a₀ a₁ a₂ a₃} (t : Tm a₀) (r₁ : a₀ →ᵣ a₁) (r₂ : a₁ →ᵣ a₂) (r₃ : a₂ →ᵣ a₃) →
            t ⋯ r₁ ⋯ r₂ ⋯ r₃ ≡ t ⋯ ((r₁ ·ₖ r₂) ·ₖ r₃)
    fuse3 t r₁ r₂ r₃ =
        cong (_⋯ r₃) (fusion t r₁ r₂) ■ fusion t (r₁ ·ₖ r₂) r₃
    leafσ-ins-base : ∀ (j : 𝔽 m) → σpart j ≡ σpartR j ⋯ ins0
    leafσ-ins-base j =
        fuse3 (σ j) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sC₁) (weaken* ⦃ Kᵣ ⦄ sB₂)
      ■ ⋯-cong (σ j) (λ x → sym (baseRen x))
      ■ sym ( cong (_⋯ ins0) (fuse3 (σ j) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sC₁') (weaken* ⦃ Kᵣ ⦄ sB₂))
            ■ fusion (σ j) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sC₁') ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ins0 )

    -- Combined leaf relation off the consumed handle 0F.
    leafσ-ins : ∀ (i : 𝔽 (sum C₁' + sum B₂ + m)) → Fin.toℕ i ≢ 0 → leafσ i ≡ leafσR i ⋯ ins0
    leafσ-ins i i≢ with splitAt (sum C₁' + sum B₂) i | Fin.join-splitAt (sum C₁' + sum B₂) m i
    ... | inj₂ u  | _   = leafσ-ins-base u
    ... | inj₁ db | jeq with splitAt (sum C₁') db | Fin.join-splitAt (sum C₁') (sum B₂) db
    ...   | inj₂ w | _    = leafσ-ins-B₂ w
    ...   | inj₁ d | jeq2 = leafσ-ins-data d d≢
      where
        ieq : i ≡ ((d ↑ˡ sum B₂) ↑ˡ m)
        ieq = sym jeq ■ cong (_↑ˡ m) (sym jeq2)
        d≢ : Fin.toℕ d ≢ 0
        d≢ d≡0 = i≢
          ( cong Fin.toℕ ieq
          ■ Fin.toℕ-↑ˡ (d ↑ˡ sum B₂) m ■ Fin.toℕ-↑ˡ d (sum B₂) ■ d≡0 )

    -- σ₀ in terms of the RHS leaf, off the consumed handle.
    σ₀-rel : ∀ (i : 𝔽 (sum C₁' + sum B₂ + m)) → Fin.toℕ i ≢ 0 → σ₀ i ≡ leafσR i ⋯ ρcolR
    σ₀-rel i i≢ =
        cong (λ z → z ⋯ Ψ ⋯ down) (leafσ-ins i i≢)
      ■ fusion (leafσR i ⋯ ins0) Ψ down
      ■ fusion (leafσR i) ins0 (Ψ ·ₖ down)

    ρ⁻ℕ≢0 : ∀ y → Fin.toℕ (ρ⁻ y) ≢ 0
    ρ⁻ℕ≢0 y eq = ρ⁻-skip y (Fin.toℕ-injective eq)

    -- U[P] reconcile: U[P]σ₀ = U[P]leafσR ⋯ ρcolR  (both via P₀ ; ρ⁻, off the handle).
    UP-rel : U[ P ] σ₀ ≡ U[ P ] leafσR 𝐔.⋯ₚ ρcolR
    UP-rel =
        cong (λ p → U[ p ] σ₀) Peq ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → σ₀-rel (ρ⁻ y) (ρ⁻ℕ≢0 y))
      ■ sym ( cong (λ p → U[ p ] leafσR 𝐔.⋯ₚ ρcolR) Peq
            ■ cong (𝐔._⋯ₚ ρcolR) (U-⋯ₚ P₀)
            ■ U-σ⋯ P₀ )

    -- Frame reconcile: the post-firing frame Fr equals the RHS frame renamed by ρcolR.
    σ₀ᴿ : (sum C₁' + sum B₂ + m) →ₛ (2 + (pre + n))
    σ₀ᴿ = leafσR ·ₖ ρcolR
    Vσ₀ᴿ : VSub σ₀ᴿ
    Vσ₀ᴿ i = value-⋯ (VleafσR i) ρcolR (λ _ → V-`)
    frame-rel : frame*-⋯ E leafσR VleafσR ⋯ᶠ* ρcolR ≡ Fr
    frame-rel =
        frame*-⋯-then-ren E VleafσR ρcolR Vσ₀ᴿ
      ■ frame*-fusion-gen-eq
      where
        frame*-fusion-gen-eq : frame*-⋯ E σ₀ᴿ Vσ₀ᴿ ≡ Fr
        frame*-fusion-gen-eq =
            cong (λ e → frame*-⋯ e σ₀ᴿ Vσ₀ᴿ) Eeq
          ■ frame*-fusion-gen E₀ Vσ₀ᴿ (λ y → Vσ₀ᴿ (ρ⁻ y))
          ■ frame*-cong E₀ (λ y → Vσ₀ᴿ (ρ⁻ y)) (λ y → Vσ₀ (ρ⁻ y))
              (λ y → sym (σ₀-rel (ρ⁻ y) (ρ⁻ℕ≢0 y)))
          ■ sym ( cong (λ e → frame*-⋯ e σ₀ Vσ₀) Eeq
                ■ frame*-fusion-gen E₀ Vσ₀ (λ y → Vσ₀ (ρ⁻ y)) )

    -- The C₁' head triple at 0F (= canonₛ-handle [] cc1 b₁ B₁).
    hcR = canonₛ-handle [] cc1 b₁ B₁
    aR  = proj₁ hcR
    xR  = proj₁ (proj₂ hcR)
    cR  = proj₁ (proj₂ (proj₂ hcR))
    canonₛR-0 : canonₛ C₁' cc1 0F ≡ (aR ⊗ (` xR)) ⊗ cR
    canonₛR-0 = proj₂ (proj₂ (proj₂ hcR))

    -- Xv (from canonₛ-acq-front, cc-rest.x = suc 0F) equals ρcolR applied to xR (C₁' head, cc1.x = 0F).
    xF : 𝔽 (sC₁' + suc (2 + n))
    xF = proj₁ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ) b₁ B₁))
    Xv-front : Xv ≡ down (Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) xF)))
    Xv-front = refl
    -- middle naturality: canonₛ-handle's middle scales with the cc channel index by the rename.
    midOfR : Tm (sC₁' + suc (2 + n)) → 𝔽 (sC₁' + suc (2 + n))
    midOfR ((a ⊗ (` x)) ⊗ c) = x
    midOfR t = subst 𝔽 (sym (Nat.+-suc sC₁' (2 + n))) 0F
    -- canonₛ C₁' (mapᶜ weakenᵣ cc1) 0F's middle (= xF, by head-irrel: middle depends only on cc.x)
    -- equals (weakenᵣ↑*sC₁') applied to xR.
    xF≡insxR : subst 𝔽 (Nat.+-suc sC₁' (2 + n)) xF ≡ insSync xR
    xF≡insxR =
        cong (subst 𝔽 (Nat.+-suc sC₁' (2 + n))) midNat
      ■ sym (subst-cod-app (Nat.+-suc sC₁' (2 + n)) (weakenᵣ {2 + n} ↑* sC₁') xR)
      where
        -- canonₛ C₁' (mapᶜ weakenᵣ cc1) 0F = canonₛ C₁' cc1 0F ⋯ (weakenᵣ↑*sC₁'); take middles.
        natEq : canonₛ C₁' (mapᶜ (weakenᵣ {2 + n}) cc1) 0F
                ≡ ((aR ⊗ (` xR)) ⊗ cR) ⋯ (weakenᵣ {2 + n} ↑* sC₁')
        natEq = canonₛ-nat C₁' cc1 (weakenᵣ {2 + n}) 0F
              ■ cong (_⋯ (weakenᵣ {2 + n} ↑* sC₁')) canonₛR-0
        -- the e₁/e₂-irrelevance of the middle: cc-rest = ((`0F),suc 0F,K`unit⋯wkᵣ) and
        -- mapᶜ weakenᵣ cc1 = (K`unit,suc 0F,K`unit) share x = suc 0F ⇒ same canonₛ middle.
        -- canonₛ C₁' (mapᶜ wkᵣ cc1) 0F = canonₛ-handle [] (K`unit,suc 0F,K`unit) b₁ B₁'s triple.
        hcK = canonₛ-handle [] (K `unit , suc 0F , K `unit) b₁ B₁
        handleK : canonₛ C₁' (K `unit , suc 0F , K `unit) 0F
                  ≡ (proj₁ hcK ⊗ (` proj₁ (proj₂ hcK))) ⊗ proj₁ (proj₂ (proj₂ hcK))
        handleK = proj₂ (proj₂ (proj₂ hcK))
        -- both canonₛ-handle invocations share x = suc 0F; their middle is x-only (e₁,e₂-irrel).
        midIrr : midOfR (canonₛ C₁' (mapᶜ (weakenᵣ {2 + n}) cc1) 0F) ≡ xF
        midIrr = cong midOfR handleK
               ■ hmid-irrel b₁ B₁ (K `unit) (` 0F) (K `unit) (K `unit ⋯ weakenᵣ) (suc 0F)
        midNat : xF ≡ (weakenᵣ {2 + n} ↑* sC₁') xR
        midNat = sym midIrr ■ cong midOfR natEq
    plug-mid : (` (weaken* ⦃ Kᵣ ⦄ sB₂ xR)) ⋯ ρcolR ≡ (` Xv)
    plug-mid =
        cong `_ ( cong (λ z → down (Ψ z)) insMidEq )
      ■ sym (cong `_ Xv-front)
      where
        insMidEq : ins0 (weaken* ⦃ Kᵣ ⦄ sB₂ xR) ≡ weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) xF)
        insMidEq = Fin.toℕ-injective
          ( cong Fin.toℕ (sym (insSync↑sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ xR)))
          ■ ↑*-hi insSync sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge
          ■ cong (λ z → sB₂ + Fin.toℕ (insSync z)) redEq
          ■ sym (toℕ-wk sB₂ (insSync xR))
          ■ sym (cong (Fin.toℕ ∘ weaken* ⦃ Kᵣ ⦄ sB₂) xF≡insxR) )
          where
            hge : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ xR)
            hge = subst (sB₂ Nat.≤_) (sym (toℕ-wk sB₂ xR)) (Nat.m≤m+n sB₂ _)
            redEq : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge ≡ xR
            redEq = Fin.toℕ-injective
              ( toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge
              ■ cong (Nat._∸ sB₂) (toℕ-wk sB₂ xR) ■ Nat.m+n∸m≡n sB₂ _ )

    -- ── RHS co-location chain (mirror of lhsChain for C₁', no zero pop). ──
    W₀R : 𝐔.Proc ((sB₂ + sC₁') + (2 + n))
    W₀R = subst 𝐔.Proc (sym (Nat.+-assoc sB₂ sC₁' (2 + n))) BODY_R
    combineStepR : 𝐔.ν (φ^ sC₁' (φ^ sB₂ BODY_R)) 𝐔.≋ 𝐔.ν (φ^ (sB₂ + sC₁') W₀R)
    combineStepR = 𝐔.ν-cong (≡→≋ (φ^-split sB₂ sC₁' BODY_R))
    extrudeStepR : 𝐔.ν (φ^ pre W₀R) 𝐔.≋ φ^ pre (𝐔.ν (W₀R 𝐔.⋯ₚ assocSwapᵣ pre 2))
    extrudeStepR = ν-φ^-comm pre W₀R
    colR : (sB₂ + (sC₁' + (2 + n))) →ᵣ (2 + (pre + n))
    colR = subst (λ z → z →ᵣ (2 + (pre + n))) (sym (sym (Nat.+-assoc sB₂ sC₁' (2 + n)))) (assocSwapᵣ pre 2)
    BODY_R-col : W₀R 𝐔.⋯ₚ assocSwapᵣ pre 2 ≡ BODY_R 𝐔.⋯ₚ colR
    BODY_R-col = subst-⋯ₚ′ (sym (Nat.+-assoc sB₂ sC₁' (2 + n))) BODY_R (assocSwapᵣ pre 2)

    -- ins0 inserts a slot at flat index pre, hence its image never lands ON pre.
    ins0-avoid-pre : ∀ (v : 𝔽 (sB₂ + (sC₁' + (2 + n)))) → Fin.toℕ (ins0 v) ≢ pre
    ins0-avoid-pre v = ins0ℕ≢pre
      where
        w : ℕ
        w = Fin.toℕ v
        ins0ℕ-lt : w Nat.< pre → Fin.toℕ (ins0 v) ≡ w
        ins0ℕ-lt lt with Nat.<-cmp w sB₂
        ... | tri< w<sB₂ _ _ = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-lo insSync sB₂ v w<sB₂
        ... | tri≈ _ eq _ = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v (Nat.≤-reflexive (sym eq)) ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.≤-reflexive (sym eq)
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            q<sC₁' : Fin.toℕ q Nat.< sC₁'
            q<sC₁' = subst (Nat._< sC₁') (sym qℕ) (sub-lt hge lt)
            body : sB₂ + Fin.toℕ (insSync q) ≡ w
            body = cong (sB₂ +_) (insSyncℕq q)
                 ■ cong (sB₂ +_) (↑*-lo (weakenᵣ {2 + n}) sC₁' q q<sC₁')
                 ■ cong (sB₂ +_) qℕ ■ Nat.m+[n∸m]≡n hge
        ... | tri> _ _ sB₂<w = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v (Nat.<⇒≤ sB₂<w) ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.<⇒≤ sB₂<w
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            q<sC₁' : Fin.toℕ q Nat.< sC₁'
            q<sC₁' = subst (Nat._< sC₁') (sym qℕ) (sub-lt hge lt)
            body : sB₂ + Fin.toℕ (insSync q) ≡ w
            body = cong (sB₂ +_) (insSyncℕq q)
                 ■ cong (sB₂ +_) (↑*-lo (weakenᵣ {2 + n}) sC₁' q q<sC₁')
                 ■ cong (sB₂ +_) qℕ ■ Nat.m+[n∸m]≡n hge
        ins0ℕ-ge : pre Nat.≤ w → Fin.toℕ (ins0 v) ≡ suc w
        ins0ℕ-ge ge = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v hge ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.≤-trans (Nat.m≤m+n sB₂ sC₁') ge
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            sC₁'≤q : sC₁' Nat.≤ Fin.toℕ q
            sC₁'≤q = subst (sC₁' Nat.≤_) (sym qℕ) (subst (Nat._≤ w Nat.∸ sB₂) (Nat.m+n∸m≡n sB₂ sC₁') (Nat.∸-monoˡ-≤ sB₂ ge))
            body : sB₂ + Fin.toℕ (insSync q) ≡ suc w
            body =
                cong (sB₂ +_) (insSyncℕq q)
              ■ cong (sB₂ +_) (↑*-hi (weakenᵣ {2 + n}) sC₁' q sC₁'≤q)
              ■ cong (λ z → sB₂ + (sC₁' + z)) (toℕ-wk 1 (Fin.reduce≥ q sC₁'≤q))
              ■ cong (λ z → sB₂ + (sC₁' + (1 + z))) (toℕ-reduce≥ q sC₁'≤q ■ cong (Nat._∸ sC₁') qℕ)
              ■ arith
              where
                r : ℕ
                r = (w Nat.∸ sB₂) Nat.∸ sC₁'
                rEq : r ≡ w Nat.∸ pre
                rEq = Nat.∸-+-assoc w sB₂ sC₁'
                arith : sB₂ + (sC₁' + (1 + r)) ≡ suc w
                arith =
                    shuffle
                  ■ cong (λ z → suc (pre + z)) rEq
                  ■ cong suc (Nat.m+[n∸m]≡n ge)
                  where
                    open +-*-Solver
                    shuffle : sB₂ + (sC₁' + (1 + r)) ≡ suc (pre + r)
                    shuffle = solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) := con 1 :+ ((a :+ b) :+ c)) refl sB₂ sC₁' r
        ins0ℕ≢pre : Fin.toℕ (ins0 v) ≢ pre
        ins0ℕ≢pre with Nat.<-cmp w pre
        ... | tri< lt _ _ = λ e → Nat.<-irrefl refl (subst (Nat._< pre) (sym (ins0ℕ-lt lt) ■ e) lt)
        ... | tri≈ _ eq _ = λ e → Nat.<-irrefl refl (subst (pre Nat.<_) (sym (ins0ℕ-ge (Nat.≤-reflexive (sym eq)) ■ cong suc eq) ■ e) (Nat.n<1+n pre))
        ... | tri> _ _ gt = λ e → Nat.<⇒≢ (Nat.<-trans gt (Nat.n<1+n w)) (sym (sym (ins0ℕ-ge (Nat.<⇒≤ gt)) ■ e))
    -- The two co-location renamings coincide pointwise (both realize assocSwapᵣ pre 2's toℕ
    -- action: v<pre ↦ 2+v ; pre≤v<pre+2 ↦ v-pre ; v≥pre+2 ↦ v).  REMAINING: toℕ casework
    -- composing ins0 (gap insert at pre) ; Ψ ; down vs assocSwapᵣ pre 2.
    colR≗ρcolR : colR ≗ ρcolR
    colR≗ρcolR v = Fin.toℕ-injective lhsℕ
      where
        w : ℕ
        w = Fin.toℕ v
        aEq : (sB₂ + sC₁') + (2 + n) ≡ sB₂ + (sC₁' + (2 + n))
        aEq = Nat.+-assoc sB₂ sC₁' (2 + n)
        uv : 𝔽 (pre + (2 + n))
        uv = subst 𝔽 (sym aEq) v
        uvℕ : Fin.toℕ uv ≡ w
        uvℕ = toℕ-subst𝔽 (sym aEq) v
        colRℕ : Fin.toℕ (colR v) ≡ Fin.toℕ (assocSwapᵣ pre 2 uv)
        colRℕ = cong Fin.toℕ (subst-→ᵣ-app (sym aEq) (assocSwapᵣ pre 2) v)

        -- ins0 inserts a slot at flat index pre.
        ins0ℕ-lt : w Nat.< pre → Fin.toℕ (ins0 v) ≡ w
        ins0ℕ-lt lt with Nat.<-cmp w sB₂
        ... | tri< w<sB₂ _ _ = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-lo insSync sB₂ v w<sB₂
        ... | tri≈ _ eq _ = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v (Nat.≤-reflexive (sym eq)) ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.≤-reflexive (sym eq)
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            q<sC₁' : Fin.toℕ q Nat.< sC₁'
            q<sC₁' = subst (Nat._< sC₁') (sym qℕ) (sub-lt hge lt)
            body : sB₂ + Fin.toℕ (insSync q) ≡ w
            body = cong (sB₂ +_) (insSyncℕq q)
                 ■ cong (sB₂ +_) (↑*-lo (weakenᵣ {2 + n}) sC₁' q q<sC₁')
                 ■ cong (sB₂ +_) qℕ ■ Nat.m+[n∸m]≡n hge
        ... | tri> _ _ sB₂<w = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v (Nat.<⇒≤ sB₂<w) ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.<⇒≤ sB₂<w
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            q<sC₁' : Fin.toℕ q Nat.< sC₁'
            q<sC₁' = subst (Nat._< sC₁') (sym qℕ) (sub-lt hge lt)
            body : sB₂ + Fin.toℕ (insSync q) ≡ w
            body = cong (sB₂ +_) (insSyncℕq q)
                 ■ cong (sB₂ +_) (↑*-lo (weakenᵣ {2 + n}) sC₁' q q<sC₁')
                 ■ cong (sB₂ +_) qℕ ■ Nat.m+[n∸m]≡n hge
        ins0ℕ-ge : pre Nat.≤ w → Fin.toℕ (ins0 v) ≡ suc w
        ins0ℕ-ge ge = cong Fin.toℕ (sym (insSync↑sB₂ v)) ■ ↑*-hi insSync sB₂ v hge ■ body
          where
            hge : sB₂ Nat.≤ w
            hge = Nat.≤-trans (Nat.m≤m+n sB₂ sC₁') ge
            q : 𝔽 (sC₁' + (2 + n))
            q = Fin.reduce≥ v hge
            qℕ : Fin.toℕ q ≡ w Nat.∸ sB₂
            qℕ = toℕ-reduce≥ v hge
            sC₁'≤q : sC₁' Nat.≤ Fin.toℕ q
            sC₁'≤q = subst (sC₁' Nat.≤_) (sym qℕ) (subst (Nat._≤ w Nat.∸ sB₂) (Nat.m+n∸m≡n sB₂ sC₁') (Nat.∸-monoˡ-≤ sB₂ ge))
            body : sB₂ + Fin.toℕ (insSync q) ≡ suc w
            body =
                cong (sB₂ +_) (insSyncℕq q)
              ■ cong (sB₂ +_) (↑*-hi (weakenᵣ {2 + n}) sC₁' q sC₁'≤q)
              ■ cong (λ z → sB₂ + (sC₁' + z)) (toℕ-wk 1 (Fin.reduce≥ q sC₁'≤q))
              ■ cong (λ z → sB₂ + (sC₁' + (1 + z))) (toℕ-reduce≥ q sC₁'≤q ■ cong (Nat._∸ sC₁') qℕ)
              ■ arith
              where
                r : ℕ
                r = (w Nat.∸ sB₂) Nat.∸ sC₁'
                rEq : r ≡ w Nat.∸ pre
                rEq = Nat.∸-+-assoc w sB₂ sC₁'
                arith : sB₂ + (sC₁' + (1 + r)) ≡ suc w
                arith =
                    shuffle
                  ■ cong (λ z → suc (pre + z)) rEq
                  ■ cong suc (Nat.m+[n∸m]≡n ge)
                  where
                    open +-*-Solver
                    shuffle : sB₂ + (sC₁' + (1 + r)) ≡ suc (pre + r)
                    shuffle = solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) := con 1 :+ ((a :+ b) :+ c)) refl sB₂ sC₁' r

        ins0ℕ≢pre : Fin.toℕ (ins0 v) ≢ pre
        ins0ℕ≢pre with Nat.<-cmp w pre
        ... | tri< lt _ _ = λ e → Nat.<-irrefl refl (subst (Nat._< pre) (sym (ins0ℕ-lt lt) ■ e) lt)
        ... | tri≈ _ eq _ = λ e → Nat.<-irrefl refl (subst (pre Nat.<_) (sym (ins0ℕ-ge (Nat.≤-reflexive (sym eq)) ■ cong suc eq) ■ e) (Nat.n<1+n pre))
        ... | tri> _ _ gt = λ e → Nat.<⇒≢ (Nat.<-trans gt (Nat.n<1+n w)) (sym (sym (ins0ℕ-ge (Nat.<⇒≤ gt)) ■ e))

        Ψins0≢0 : Ψ (ins0 v) ≢ 0F
        Ψins0≢0 = Ψ-avoid (ins0 v) ins0ℕ≢pre

        downℕ : ∀ (x : 𝔽 (1 + (2 + (pre + n)))) → x ≢ 0F → Fin.toℕ (down x) ≡ Fin.toℕ x Nat.∸ 1
        downℕ 0F      x≢ = ⊥-elim (x≢ refl)
        downℕ (suc j) _  = refl

        -- toℕ of Ψ on a position whose ins0-image toℕ is z, via Ψ-toℕ + aS1/aS2↑.
        ΨinsℕGen : ∀ (z : ℕ) → Fin.toℕ (ins0 v) ≡ z →
                   Fin.toℕ (Ψ (ins0 v)) ≡
                     [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ pre 2 j))) ]′
                       (Fin.splitAt 1 (aS1 (subst 𝔽 cEq (ins0 v))))
        ΨinsℕGen z zeq = Ψ-toℕ (ins0 v) ■ toℕ-↑ (assocSwapᵣ pre 2) (aS1 (subst 𝔽 cEq (ins0 v)))

        czℕ : Fin.toℕ (subst 𝔽 cEq (ins0 v)) ≡ Fin.toℕ (ins0 v)
        czℕ = cvℕ (ins0 v)

        -- RHS toℕ per case.
        rhsℕ-lt : w Nat.< pre → Fin.toℕ (ρcolR v) ≡ 2 + w
        rhsℕ-lt lt =
            downℕ (Ψ (ins0 v)) Ψins0≢0
          ■ cong (Nat._∸ 1) Ψstep
          where
            xc = subst 𝔽 cEq (ins0 v)
            xcℕ : Fin.toℕ xc ≡ w
            xcℕ = czℕ ■ ins0ℕ-lt lt
            aS1ℕ : Fin.toℕ (aS1 xc) ≡ suc w
            aS1ℕ = aS1ℕ-lt xc (subst (Nat._< pre) (sym xcℕ) lt) ■ cong suc xcℕ
            q1 : 1 Nat.≤ Fin.toℕ (aS1 xc)
            q1 = subst (1 Nat.≤_) (sym aS1ℕ) (Nat.s≤s Nat.z≤n)
            redℕ : Fin.toℕ (Fin.reduce≥ (aS1 xc) q1) ≡ w
            redℕ = toℕ-reduce≥ (aS1 xc) q1 ■ cong (Nat._∸ 1) aS1ℕ
            Ψstep : Fin.toℕ (Ψ (ins0 v)) ≡ suc (2 + w)
            Ψstep =
                ΨinsℕGen w (ins0ℕ-lt lt)
              ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ pre 2 j))) ]′ (Fin.splitAt-≥ 1 (aS1 xc) q1)
              ■ cong suc (toℕ-assoc-lt pre 2 (Fin.reduce≥ (aS1 xc) q1) (subst (Nat._< pre) (sym redℕ) lt))
              ■ cong (λ z → suc (2 + z)) redℕ
        rhsℕ-mid : pre Nat.≤ w → w Nat.< pre + 2 → Fin.toℕ (ρcolR v) ≡ w Nat.∸ pre
        rhsℕ-mid ge lt =
            downℕ (Ψ (ins0 v)) Ψins0≢0
          ■ cong (Nat._∸ 1) Ψstep
          where
            xc = subst 𝔽 cEq (ins0 v)
            xcℕ : Fin.toℕ xc ≡ suc w
            xcℕ = czℕ ■ ins0ℕ-ge ge
            sw-gt : pre Nat.< Fin.toℕ xc
            sw-gt = subst (pre Nat.<_) (sym xcℕ) (Nat.s≤s ge)
            aS1ℕ : Fin.toℕ (aS1 xc) ≡ suc w
            aS1ℕ = aS1ℕ-gt xc sw-gt ■ xcℕ
            q1 : 1 Nat.≤ Fin.toℕ (aS1 xc)
            q1 = subst (1 Nat.≤_) (sym aS1ℕ) (Nat.s≤s Nat.z≤n)
            redℕ : Fin.toℕ (Fin.reduce≥ (aS1 xc) q1) ≡ w
            redℕ = toℕ-reduce≥ (aS1 xc) q1 ■ cong (Nat._∸ 1) aS1ℕ
            r-ge : pre Nat.≤ Fin.toℕ (Fin.reduce≥ (aS1 xc) q1)
            r-ge = subst (pre Nat.≤_) (sym redℕ) ge
            r-lt : Fin.toℕ (Fin.reduce≥ (aS1 xc) q1) Nat.< pre + 2
            r-lt = subst (Nat._< pre + 2) (sym redℕ) lt
            Ψstep : Fin.toℕ (Ψ (ins0 v)) ≡ suc (w Nat.∸ pre)
            Ψstep =
                ΨinsℕGen (suc w) (ins0ℕ-ge ge)
              ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ pre 2 j))) ]′ (Fin.splitAt-≥ 1 (aS1 xc) q1)
              ■ cong suc (toℕ-assoc-mid pre 2 (Fin.reduce≥ (aS1 xc) q1) r-ge r-lt)
              ■ cong (λ z → suc (z Nat.∸ pre)) redℕ
        rhsℕ-ge : pre + 2 Nat.≤ w → Fin.toℕ (ρcolR v) ≡ w
        rhsℕ-ge ge2 =
            downℕ (Ψ (ins0 v)) Ψins0≢0
          ■ cong (Nat._∸ 1) Ψstep
          where
            ge : pre Nat.≤ w
            ge = Nat.≤-trans (Nat.m≤m+n pre 2) ge2
            xc = subst 𝔽 cEq (ins0 v)
            xcℕ : Fin.toℕ xc ≡ suc w
            xcℕ = czℕ ■ ins0ℕ-ge ge
            sw-gt : pre Nat.< Fin.toℕ xc
            sw-gt = subst (pre Nat.<_) (sym xcℕ) (Nat.s≤s ge)
            aS1ℕ : Fin.toℕ (aS1 xc) ≡ suc w
            aS1ℕ = aS1ℕ-gt xc sw-gt ■ xcℕ
            q1 : 1 Nat.≤ Fin.toℕ (aS1 xc)
            q1 = subst (1 Nat.≤_) (sym aS1ℕ) (Nat.s≤s Nat.z≤n)
            redℕ : Fin.toℕ (Fin.reduce≥ (aS1 xc) q1) ≡ w
            redℕ = toℕ-reduce≥ (aS1 xc) q1 ■ cong (Nat._∸ 1) aS1ℕ
            r-ge2 : pre + 2 Nat.≤ Fin.toℕ (Fin.reduce≥ (aS1 xc) q1)
            r-ge2 = subst (pre + 2 Nat.≤_) (sym redℕ) ge2
            Ψstep : Fin.toℕ (Ψ (ins0 v)) ≡ suc w
            Ψstep =
                ΨinsℕGen (suc w) (ins0ℕ-ge ge)
              ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ pre 2 j))) ]′ (Fin.splitAt-≥ 1 (aS1 xc) q1)
              ■ cong suc (toℕ-assoc-ge pre 2 (Fin.reduce≥ (aS1 xc) q1) r-ge2)
              ■ cong suc redℕ

        -- LHS toℕ per case.
        lhsℕ-lt : w Nat.< pre → Fin.toℕ (colR v) ≡ 2 + w
        lhsℕ-lt lt = colRℕ ■ toℕ-assoc-lt pre 2 uv (subst (Nat._< pre) (sym uvℕ) lt) ■ cong (2 +_) uvℕ
        lhsℕ-mid : pre Nat.≤ w → w Nat.< pre + 2 → Fin.toℕ (colR v) ≡ w Nat.∸ pre
        lhsℕ-mid ge lt = colRℕ ■ toℕ-assoc-mid pre 2 uv (subst (pre Nat.≤_) (sym uvℕ) ge) (subst (Nat._< pre + 2) (sym uvℕ) lt) ■ cong (Nat._∸ pre) uvℕ
        lhsℕ-ge : pre + 2 Nat.≤ w → Fin.toℕ (colR v) ≡ w
        lhsℕ-ge ge2 = colRℕ ■ toℕ-assoc-ge pre 2 uv (subst (pre + 2 Nat.≤_) (sym uvℕ) ge2) ■ uvℕ

        lhsℕ : Fin.toℕ (colR v) ≡ Fin.toℕ (ρcolR v)
        lhsℕ with Nat.<-cmp w pre
        ... | tri< lt _ _ = lhsℕ-lt lt ■ sym (rhsℕ-lt lt)
        ... | tri≈ _ eq _ with Nat.<-cmp w (pre + 2)
        ...   | tri< lt _ _ = lhsℕ-mid (Nat.≤-reflexive (sym eq)) lt ■ sym (rhsℕ-mid (Nat.≤-reflexive (sym eq)) lt)
        ...   | tri≈ _ eq2 _ = ⊥-elim (Nat.<-irrefl (sym eq) (subst (pre Nat.<_) (sym eq2) (Nat.m<m+n pre (Nat.s≤s Nat.z≤n))))
        ...   | tri> _ _ gt2 = ⊥-elim (Nat.<-irrefl (sym eq) (Nat.<-trans (Nat.m<m+n pre (Nat.s≤s Nat.z≤n)) gt2))
        lhsℕ | tri> _ _ gt with Nat.<-cmp w (pre + 2)
        ...   | tri< lt _ _ = lhsℕ-mid (Nat.<⇒≤ gt) lt ■ sym (rhsℕ-mid (Nat.<⇒≤ gt) lt)
        ...   | tri≈ _ eq2 _ = lhsℕ-ge (Nat.≤-reflexive (sym eq2)) ■ sym (rhsℕ-ge (Nat.≤-reflexive (sym eq2)))
        ...   | tri> _ _ gt2 = lhsℕ-ge (Nat.<⇒≤ gt2) ■ sym (rhsℕ-ge (Nat.<⇒≤ gt2))
    rhsChain : U[ 𝐓.ν C₁' B₂ Q_R ] σ 𝐔.≋ φ^ pre (𝐔.ν (BODY_R 𝐔.⋯ₚ colR))
    rhsChain = flatStepR ◅◅ combineStepR ◅◅ extrudeStepR ◅◅ φ^-cong pre (𝐔.ν-cong (≡→≋ BODY_R-col))

    -- BODY_R ⋯ colR distributes over ∥ and matches ⟪Fr[...]⟫ ∥ Pacq.
    G1R G2R leafRcol : 𝐔.Proc (2 + (pre + n))
    G1R = (Flags C₁' 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB₂) 𝐔.⋯ₚ colR
    G2R = Flags B₂ 𝐔.⋯ₚ colR
    leafRcol = U[ Q_R ] leafσR 𝐔.⋯ₚ colR
    bodyRdist : BODY_R 𝐔.⋯ₚ colR ≡ G1R 𝐔.∥ (G2R 𝐔.∥ leafRcol)
    bodyRdist = refl

    -- ── LHS thread/frame reconcile (mirror of frame-rel for the LHS chain). ──
    σ₀wk : (sum C₁ + sum B₂ + m) →ₛ (1 + (2 + (pre + n)))
    σ₀wk = σ₀ ·ₖ weakenᵣ
    Vσ₀wk : VSub σ₀wk
    Vσ₀wk i = value-⋯ (Vσ₀ i) weakenᵣ (λ _ → V-`)
    leafΨσ : (sum C₁ + sum B₂ + m) →ₛ (1 + (2 + (pre + n)))
    leafΨσ = leafσ ·ₖ Ψ
    VleafΨσ : VSub leafΨσ
    VleafΨσ i = value-⋯ (Vleafσ i) Ψ (λ _ → V-`)
    -- σ₀ ⋯ weakenᵣ agrees with leafσ ⋯ Ψ off the consumed handle 0F.
    σ₀wk-rel : ∀ (i : 𝔽 (sum C₁ + sum B₂ + m)) → Fin.toℕ i ≢ 0 → σ₀wk i ≡ leafΨσ i
    σ₀wk-rel i i≢ =
        fusion (leafσ i ⋯ Ψ) down weakenᵣ
      ■ cong (λ z → z ⋯ Ψ ⋯ (down ·ₖ weakenᵣ)) (leafσ-ins i i≢)
      ■ cong (_⋯ (down ·ₖ weakenᵣ)) (fusion (leafσR i) ins0 Ψ)
      ■ fusion (leafσR i) (ins0 ·ₖ Ψ) (down ·ₖ weakenᵣ)
      ■ ⋯-cong (leafσR i) (λ v → down·wk-id (Ψ (ins0 v)) (Ψ-avoid (ins0 v) (ins0-avoid-pre v)))
      ■ sym (fusion (leafσR i) ins0 Ψ)
      ■ sym (cong (_⋯ Ψ) (leafσ-ins i i≢))
    frame-relL : frame*-⋯ E leafΨσ VleafΨσ ≡ Fr ⋯ᶠ* weakenᵣ
    frame-relL =
        cong (λ e → frame*-⋯ e leafΨσ VleafΨσ) Eeq
      ■ frame*-fusion-gen E₀ VleafΨσ (λ y → VleafΨσ (ρ⁻ y))
      ■ frame*-cong E₀ (λ y → VleafΨσ (ρ⁻ y)) (λ y → Vσ₀wk (ρ⁻ y))
          (λ y → sym (σ₀wk-rel (ρ⁻ y) (ρ⁻ℕ≢0 y)))
      ■ sym ( frame*-⋯-then-ren E Vσ₀ weakenᵣ Vσ₀wk
            ■ cong (λ e → frame*-⋯ e σ₀wk Vσ₀wk) Eeq
            ■ frame*-fusion-gen E₀ Vσ₀wk (λ y → Vσ₀wk (ρ⁻ y)) )

    -- The acq thread under leafσ ⋯ Ψ rewrites to the RU-Acquire LHS thread shape.
    acqThr newThr : 𝐔.Proc (1 + (2 + (pre + n)))
    acqThr = 𝐔.⟪ (E [ K `acq · (` 0F) ]*) ⋯ leafσ ⋯ Ψ ⟫
    newThr = 𝐔.⟪ (Fr ⋯ᶠ* weakenᵣ) [ K `acq · (((` 0F) ⊗ (` suc Xv)) ⊗ (acqCont ⋯ weakenᵣ)) ]* ⟫
    Pleaf : 𝐔.Proc (1 + (2 + (pre + n)))
    Pleaf = U[ P ] leafσ 𝐔.⋯ₚ Ψ
    threadEqL : acqThr ≡ newThr
    threadEqL = cong 𝐔.⟪_⟫
      ( fusion (E [ K `acq · (` 0F) ]*) leafσ Ψ
      ■ frame-plug* E leafΨσ VleafΨσ
      ■ cong₂ (λ F t → F [ K `acq · t ]*) frame-relL acqArgEq )
      where
        acqArgEq : (` 0F) ⋯ leafΨσ ≡ ((` 0F) ⊗ (` suc Xv)) ⊗ (acqCont ⋯ weakenᵣ)
        acqArgEq =
            cong (_⋯ Ψ) leafσ-handle
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ) aft-eq
          ■ cong₂ _⊗_ (cong₂ _⊗_ slot1 (cong `_ slot2)) slot3
          where
            aft = canonₛ-acq-front b₁ B₁ {n}
            av  = proj₁ aft
            xv  = proj₁ (proj₂ aft)
            cv  = proj₁ (proj₂ (proj₂ aft))
            aft-eq : canonₛ C₁ cc1 0F ≡ (av ⊗ (` xv)) ⊗ cv
            aft-eq = proj₂ (proj₂ (proj₂ aft))
            -- leafσ 0F = canonₛ C₁ cc1 0F ⋯ wk*sB₂ (left part of the Xleaf ++ₛ, index 0F).
            leafσ-handle : leafσ 0F ≡ canonₛ C₁ cc1 0F ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
            leafσ-handle = refl
            -- slot1: av ⋯ wk*sB₂ ⋯ Ψ ≡ (`0F).  av = (`a-var), toℕ a-var = sC₁',
            -- so toℕ(wk*sB₂ a-var) = sB₂+sC₁' = pre, hence Ψ lands on 0F (Ψ-zero).
            ha = handle-a 0F (suc 0F) (K `unit ⋯ weakenᵣ) b₁ B₁
            avar : 𝔽 (sC₁ + (2 + n))
            avar = subst 𝔽 (Nat.+-suc sC₁' (2 + n)) (proj₁ ha)
            av≡ : av ≡ (` avar)
            av≡ = acq-a-link b₁ B₁
                ■ cong (subst Tm (Nat.+-suc sC₁' (2 + n))) (proj₁ (proj₂ ha))
                ■ subst-` (Nat.+-suc sC₁' (2 + n)) (proj₁ ha)
            avarℕ : Fin.toℕ avar ≡ sC₁'
            avarℕ = toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) (proj₁ ha)
                  ■ proj₂ (proj₂ ha) ■ Nat.+-identityʳ sC₁'
            slot1 : av ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ≡ (` 0F)
            slot1 = cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ) av≡
                  ■ cong `_ (Ψ-zero (weaken* ⦃ Kᵣ ⦄ sB₂ avar)
                              (toℕ-wk sB₂ avar ■ cong (sB₂ +_) avarℕ))
            -- slot2: Ψ(wk*sB₂ xv) ≡ suc Xv  (Xv = down(Ψ(wk*sB₂ xv)), and Ψ(wk*sB₂ xv) ≢ 0F).
            insMidEq2 : ins0 (weaken* ⦃ Kᵣ ⦄ sB₂ xR) ≡ weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) xF)
            insMidEq2 = Fin.toℕ-injective
              ( cong Fin.toℕ (sym (insSync↑sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ xR)))
              ■ ↑*-hi insSync sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge
              ■ cong (λ z → sB₂ + Fin.toℕ (insSync z)) redEq
              ■ sym (toℕ-wk sB₂ (insSync xR))
              ■ sym (cong (Fin.toℕ ∘ weaken* ⦃ Kᵣ ⦄ sB₂) xF≡insxR) )
              where
                hge : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ xR)
                hge = subst (sB₂ Nat.≤_) (sym (toℕ-wk sB₂ xR)) (Nat.m≤m+n sB₂ _)
                redEq : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge ≡ xR
                redEq = Fin.toℕ-injective
                  ( toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ xR) hge
                  ■ cong (Nat._∸ sB₂) (toℕ-wk sB₂ xR) ■ Nat.m+n∸m≡n sB₂ _ )
            wx≡ins : weaken* ⦃ Kᵣ ⦄ sB₂ xv ≡ ins0 (weaken* ⦃ Kᵣ ⦄ sB₂ xR)
            wx≡ins = cong (weaken* ⦃ Kᵣ ⦄ sB₂) (acq-x-link b₁ B₁) ■ sym insMidEq2
            Ψwx≢0 : Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ xv) ≢ 0F
            Ψwx≢0 = Ψ-avoid (weaken* ⦃ Kᵣ ⦄ sB₂ xv)
              (subst (λ z → Fin.toℕ z ≢ pre) (sym wx≡ins) (ins0-avoid-pre (weaken* ⦃ Kᵣ ⦄ sB₂ xR)))
            slot2 : Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ xv) ≡ suc Xv
            slot2 = sym (suc∘down (Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ xv)) Ψwx≢0)
              where
                suc∘down : ∀ (w : 𝔽 (1 + (2 + (pre + n)))) → w ≢ 0F → suc (down w) ≡ w
                suc∘down 0F      w≢ = ⊥-elim (w≢ refl)
                suc∘down (suc _) _  = refl
            -- slot3: cv ⋯ wk*sB₂ ⋯ Ψ ≡ acqCont ⋯ weakenᵣ.  acqCont = cv⋯wk*sB₂⋯Ψ⋯down,
            -- so acqCont⋯wkᵣ = cv⋯wk*sB₂⋯Ψ⋯(down·ₖwkᵣ); the down·ₖwkᵣ is identity because
            -- every var of cv⋯wk*sB₂⋯Ψ avoids 0F (cv is K`unit or a var below sC₁').
            -- (` v) ⋯ ρ₁ ⋯ ρ₂ on a single variable reduces to the renamed variable.
            var2 : ∀ {a b d} (v : 𝔽 a) (ρ₁ : a →ᵣ b) (ρ₂ : b →ᵣ d) → (` v) ⋯ ρ₁ ⋯ ρ₂ ≡ (` ρ₂ (ρ₁ v))
            var2 v ρ₁ ρ₂ = refl
            slot3 : cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ≡ acqCont ⋯ weakenᵣ
            slot3 =
                sym ( fusion (cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ) down weakenᵣ
                    ■ cvΨ-id )
              where
                cv≡ : cv ≡ subst Tm (Nat.+-suc sC₁' (2 + n)) (proj₁ (proj₂ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁))))
                cv≡ = acq-c-link b₁ B₁
                -- cv ⋯ wk*sB₂ ⋯ Ψ is a single value (K`unit or a var off pre), so the extra
                -- down ⋯ weakenᵣ is the identity.  We prove cv⋯wk*sB₂⋯Ψ is a fixed value t with
                -- t ⋯ (down·ₖweakenᵣ) ≡ t, by casing on handle-c.
                cvVal : Σ[ t ∈ Tm (1 + (2 + (pre + n))) ]
                          (cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ≡ t)
                        × (t ⋯ (down ·ₖ weakenᵣ) ≡ t)
                cvVal = elim (handle-c (` 0F) (suc 0F) (K `unit ⋯ weakenᵣ {2 + n}) refl b₁ B₁)
                  where
                    elim : _ → Σ[ t ∈ Tm (1 + (2 + (pre + n))) ]
                                 (cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ≡ t)
                               × (t ⋯ (down ·ₖ weakenᵣ) ≡ t)
                    elim (inj₁ c≡K) =
                      K `unit
                      , ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ) cvK )
                      , refl
                      where
                        cvK : cv ≡ K `unit
                        cvK = cv≡ ■ cong (subst Tm (Nat.+-suc sC₁' (2 + n))) c≡K ■ subst-Kunit (Nat.+-suc sC₁' (2 + n))
                    elim (inj₂ (vc , c≡vc , vc<sC₁')) =
                      (` Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ vcvar))
                      , ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ) cvvc ■ var2 vcvar (weaken* ⦃ Kᵣ ⦄ sB₂) Ψ )
                      , cong `_ (down·wk-id (Ψ (weaken* ⦃ Kᵣ ⦄ sB₂ vcvar))
                                  (Ψ-avoid (weaken* ⦃ Kᵣ ⦄ sB₂ vcvar) vcℕ≢pre))
                      where
                        vcvar : 𝔽 (sC₁ + (2 + n))
                        vcvar = subst 𝔽 (Nat.+-suc sC₁' (2 + n)) vc
                        vcvarℕ : Fin.toℕ vcvar ≡ Fin.toℕ vc
                        vcvarℕ = toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) vc
                        cvvc : cv ≡ (` vcvar)
                        cvvc = cv≡ ■ cong (subst Tm (Nat.+-suc sC₁' (2 + n))) c≡vc
                             ■ subst-` (Nat.+-suc sC₁' (2 + n)) vc
                        vcℕ≢pre : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ vcvar) ≢ pre
                        vcℕ≢pre eq = Nat.<-irrefl refl
                          (subst (Nat._< pre) (sym (toℕ-wk sB₂ vcvar ■ cong (sB₂ +_) vcvarℕ) ■ eq)
                            (Nat.+-monoʳ-< sB₂ vc<sC₁'))
                cvΨ-id : cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ ⋯ (down ·ₖ weakenᵣ) ≡ cv ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ Ψ
                cvΨ-id =
                    cong (_⋯ (down ·ₖ weakenᵣ)) (proj₁ (proj₂ cvVal))
                  ■ proj₂ (proj₂ cvVal)
                  ■ sym (proj₁ (proj₂ cvVal))
    PleafEqL : Pleaf ≡ U[ P ] σ₀ 𝐔.⋯ₚ weakenᵣ
    PleafEqL =
        U-σ⋯ P
      ■ cong (λ p → U[ p ] leafΨσ) Peq ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → sym (σ₀wk-rel (ρ⁻ y) (ρ⁻ℕ≢0 y)))
      ■ sym ( cong (λ p → U[ p ] σ₀ 𝐔.⋯ₚ weakenᵣ) Peq
            ■ cong (𝐔._⋯ₚ weakenᵣ) (U-⋯ₚ P₀)
            ■ U-σ⋯ P₀ )

    bodyEq : MIDBODY 𝐔.≋ acqLHSbody
    bodyEq = ≡→≋ midDistrib ◅◅ reconcile
      where
        -- leafΨ = U[Q]leafσ ⋯ Ψ distributes over ∥ into the acq thread and the rest.
        leafΨ≡ : leafΨ ≡ acqThr 𝐔.∥ Pleaf
        leafΨ≡ = refl
        -- Pacq ⋯ weakenᵣ reassembles the residual flags + U[P].
        pacqwk≡ : (resFlagC₁' 𝐔.⋯ₚ weakenᵣ) 𝐔.∥ (G2Ψ 𝐔.∥ Pleaf) ≡ Pacq 𝐔.⋯ₚ weakenᵣ
        pacqwk≡ = cong₂ 𝐔._∥_ refl (cong₂ 𝐔._∥_ G2factor PleafEqL)
        reconcile : G1Ψ 𝐔.∥ (G2Ψ 𝐔.∥ leafΨ) 𝐔.≋ acqLHSbody
        reconcile =
            𝐔.∥-cong G1factor ε
          ◅◅ Eq*.symmetric _ 𝐔.∥-assoc
          ◅◅ 𝐔.∥-cong ε (𝐔.∥-cong ε ∥-swap-mid)
          ◅◅ 𝐔.∥-cong ε ∥-swap-mid
          ◅◅ ≡→≋ (cong₂ 𝐔._∥_ refl (cong₂ 𝐔._∥_ threadEqL pacqwk≡))

    shapeStep : φ^ pre (𝐔.ν (𝐔.φ MIDBODY)) 𝐔.≋ φ^ pre (𝐔.ν (𝐔.φ acqLHSbody))
    shapeStep = φ^-cong pre (𝐔.ν-cong (𝐔.φ-cong bodyEq))

    firing : φ^ pre (𝐔.ν (𝐔.φ acqLHSbody)) 𝐔R.─→ₚ φ^ pre (𝐔.ν (𝐔.⟪ Fr [ (K `unit ⊗ (` Xv)) ⊗ acqCont ]* ⟫ 𝐔.∥ Pacq))
    firing = φ^-acq-─→ pre (𝐔R.RU-Acquire Fr {Xv})

    rhsRecon : φ^ pre (𝐔.ν (𝐔.⟪ Fr [ (K `unit ⊗ (` Xv)) ⊗ acqCont ]* ⟫ 𝐔.∥ Pacq))
               𝐔.≋ U[ 𝐓.ν C₁' B₂ (𝐓.⟪ E [ ` zero ]* ⟫ 𝐓.∥ P) ] σ
    rhsRecon = Eq*.symmetric _ (rhsChain ◅◅ φ^-cong pre (𝐔.ν-cong (≡→≋ bodyRdist ◅◅ bodyMatchR)))
      where
        threadR : 𝐔.Proc (2 + (pre + n))
        threadR = 𝐔.⟪ ((E [ ` zero ]*) ⋯ leafσR) ⋯ colR ⟫
        UPR : 𝐔.Proc (2 + (pre + n))
        UPR = U[ P ] leafσR 𝐔.⋯ₚ colR
        leafRcol≡ : leafRcol ≡ threadR 𝐔.∥ UPR
        leafRcol≡ = refl
        UPR≡ : UPR ≡ U[ P ] σ₀
        UPR≡ = 𝐔.⋯ₚ-cong (U[ P ] leafσR) colR≗ρcolR ■ sym UP-rel
        bodyMatchR : G1R 𝐔.∥ (G2R 𝐔.∥ leafRcol)
                     𝐔.≋ 𝐔.⟪ Fr [ (K `unit ⊗ (` Xv)) ⊗ acqCont ]* ⟫ 𝐔.∥ Pacq
        bodyMatchR =
            𝐔.∥-cong ε ∥-swap-mid
          ◅◅ ∥-swap-mid
          ◅◅ ≡→≋ (cong₂ 𝐔._∥_ (cong 𝐔.⟪_⟫ threadEqR)
                    (cong₂ 𝐔._∥_ G1R≡ (cong₂ 𝐔._∥_ G2R≡ UPR≡)))
          where
            redexSlotRρ : leafσR 0F ⋯ ρcolR ≡ (K `unit ⊗ (` Xv)) ⊗ acqCont
            redexSlotRρ =
                cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρcolR) canonₛR-0
              ■ cong₂ _⊗_ (cong₂ _⊗_ slot1R slot2R) slot3R
              where
                slot1R : aR ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρcolR ≡ K `unit
                slot1R = cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρcolR) (handle-a-K 0F (K `unit) b₁ B₁)
                slot2R : (` weaken* ⦃ Kᵣ ⦄ sB₂ xR) ⋯ ρcolR ≡ (` Xv)
                slot2R = plug-mid
                -- acqCont = c ⋯ wk*sB₂ ⋯ Ψ ⋯ down (c = acq-front third).  Off the handle the
                -- C₁' third cR and the C₁ third c agree up to the slot insertion ins0:
                -- cR ⋯ wk*sB₂ ⋯ ins0 ≡ c ⋯ wk*sB₂.  Then ρcolR = ins0·ₖ(Ψ·ₖdown) lines them up.
                -- The C₁' third cR co-located by (weakenᵣ↑*sC₁') equals the acq-front third c
                -- (before its +-suc subst): both come from canonₛ-handle [] with the same e₂=K`unit
                -- and x=suc 0F, so hthird-irrel + canonₛ-nat link them.
                cR-third-link : cR ⋯ (weakenᵣ {2 + n} ↑* sC₁')
                                ≡ proj₁ (proj₂ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁)))
                cR-third-link = sym thirdNat
                  where
                    thirdOfT : Tm (sC₁' + suc (2 + n)) → Tm (sC₁' + suc (2 + n))
                    thirdOfT ((_ ⊗ _) ⊗ c) = c
                    thirdOfT t = K `unit
                    natEq : canonₛ C₁' (mapᶜ (weakenᵣ {2 + n}) cc1) 0F
                            ≡ ((aR ⊗ (` xR)) ⊗ cR) ⋯ (weakenᵣ {2 + n} ↑* sC₁')
                    natEq = canonₛ-nat C₁' cc1 (weakenᵣ {2 + n}) 0F
                          ■ cong (_⋯ (weakenᵣ {2 + n} ↑* sC₁')) canonₛR-0
                    hcK = canonₛ-handle [] (K `unit , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁
                    handleK : canonₛ C₁' (K `unit , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) 0F
                              ≡ (proj₁ hcK ⊗ (` proj₁ (proj₂ hcK))) ⊗ proj₁ (proj₂ (proj₂ hcK))
                    handleK = proj₂ (proj₂ (proj₂ hcK))
                    thirdIrr : thirdOfT (canonₛ C₁' (mapᶜ (weakenᵣ {2 + n}) cc1) 0F)
                               ≡ proj₁ (proj₂ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁)))
                    thirdIrr = cong thirdOfT handleK
                             ■ hthird-irrel b₁ B₁ {suc (2 + n)} (K `unit) (` 0F) (K `unit ⋯ weakenᵣ {2 + n}) (suc 0F)
                    thirdNat : proj₁ (proj₂ (proj₂ (canonₛ-handle [] ((` 0F) , suc 0F , K `unit ⋯ weakenᵣ {2 + n}) b₁ B₁)))
                               ≡ cR ⋯ (weakenᵣ {2 + n} ↑* sC₁')
                    thirdNat = sym thirdIrr ■ cong thirdOfT natEq
                cRc-ins : cR ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ins0
                          ≡ proj₁ (proj₂ (proj₂ (canonₛ-acq-front b₁ B₁ {n}))) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
                cRc-ins =
                    sym ( cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) c-third-rel
                        ■ subst-⋯ (Nat.+-suc sC₁' (2 + n)) (cR ⋯ (weakenᵣ {2 + n} ↑* sC₁')) (weaken* ⦃ Kᵣ ⦄ sB₂)
                        ■ fusion cR (weakenᵣ {2 + n} ↑* sC₁') (subst (λ z → z →ᵣ (sB₂ + (sC₁ + (2 + n)))) (sym (Nat.+-suc sC₁' (2 + n))) (weaken* ⦃ Kᵣ ⦄ sB₂))
                        ■ ⋯-cong cR insComm
                        ■ sym (fusion cR (weaken* ⦃ Kᵣ ⦄ sB₂) ins0) )
                  where
                    c-third-rel : proj₁ (proj₂ (proj₂ (canonₛ-acq-front b₁ B₁ {n})))
                                  ≡ subst Tm (Nat.+-suc sC₁' (2 + n)) (cR ⋯ (weakenᵣ {2 + n} ↑* sC₁'))
                    c-third-rel = acq-c-link b₁ B₁ ■ cong (subst Tm (Nat.+-suc sC₁' (2 + n))) (sym cR-third-link)
                slot3R : cR ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρcolR ≡ acqCont
                slot3R =
                    sym (fusion (cR ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ins0 (Ψ ·ₖ down))
                  ■ sym (fusion (cR ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ins0) Ψ down)
                  ■ cong (λ t → t ⋯ Ψ ⋯ down) cRc-ins
            threadEqR : ((E [ ` zero ]*) ⋯ leafσR) ⋯ colR ≡ Fr [ (K `unit ⊗ (` Xv)) ⊗ acqCont ]*
            threadEqR =
                ⋯-cong ((E [ ` zero ]*) ⋯ leafσR) colR≗ρcolR
              ■ cong (_⋯ ρcolR) (frame-plug* E leafσR VleafσR)
              ■ frame-plug*ᵣ (frame*-⋯ E leafσR VleafσR) ρcolR
              ■ cong₂ _[_]* frame-rel redexSlotRρ
            G1R≡ : G1R ≡ resFlagC₁'
            G1R≡ =
                𝐔.fusionₚ (Flags {2 + n} C₁') (weaken* ⦃ Kᵣ ⦄ sB₂) colR
              ■ Flags-⋯-cong C₁' (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ colR) (castC₁' ·ₖ (Ψ ·ₖ down)) ptw
              ■ sym ( cong (𝐔._⋯ₚ down) (𝐔.fusionₚ (Flags {suc (2 + n)} C₁') castC₁' Ψ)
                    ■ 𝐔.fusionₚ (Flags {suc (2 + n)} C₁') (castC₁' ·ₖ Ψ) down
                    ■ 𝐔.⋯ₚ-cong (Flags {suc (2 + n)} C₁') (λ j → sym (assoc·ₖ j)) )
              where
                assoc·ₖ : ∀ (j : 𝔽 (sC₁' + suc (2 + n))) →
                          (castC₁' ·ₖ (Ψ ·ₖ down)) j ≡ ((castC₁' ·ₖ Ψ) ·ₖ down) j
                assoc·ₖ j = refl
                ptw : ∀ (i : 𝔽 (syncs C₁')) →
                      (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ colR) (i ↑ˡ (2 + n))
                      ≡ (castC₁' ·ₖ (Ψ ·ₖ down)) (i ↑ˡ suc (2 + n))
                ptw i = colR≗ρcolR (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))
                      ■ cong (Ψ ·ₖ down) insLo
                  where
                    wtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) ≡ sB₂ + Fin.toℕ i
                    wtoℕ = toℕ-wk sB₂ (i ↑ˡ (2 + n)) ■ cong (sB₂ +_) (Fin.toℕ-↑ˡ i (2 + n))
                    w<pre : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) Nat.< pre
                    w<pre = subst (Nat._< pre) (sym wtoℕ) (Nat.+-monoʳ-< sB₂ (Fin.toℕ<n i))
                    insLo : ins0 (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) ≡ castC₁' (i ↑ˡ suc (2 + n))
                    insLo = Fin.toℕ-injective
                      ( ins0ℕ-lt-G1
                      ■ wtoℕ
                      ■ sym castℕ )
                      where
                        bodyLo : (hge : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))) →
                                 sB₂ + Fin.toℕ (insSync (Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) hge))
                                 ≡ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))
                        bodyLo hge =
                            cong (sB₂ +_) (insSyncℕq (Fin.reduce≥ _ hge))
                          ■ cong (sB₂ +_) (↑*-lo (weakenᵣ {2 + n}) sC₁' (Fin.reduce≥ _ hge) qlt)
                          ■ cong (sB₂ +_) (toℕ-reduce≥ _ hge)
                          ■ Nat.m+[n∸m]≡n hge
                          where
                            qlt : Fin.toℕ (Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))) hge) Nat.< sC₁'
                            qlt = subst (Nat._< sC₁') (sym (toℕ-reduce≥ _ hge))
                              (subst (λ z → z Nat.∸ sB₂ Nat.< sC₁') (sym wtoℕ)
                                (subst (Nat._< sC₁') (sym (Nat.m+n∸m≡n sB₂ (Fin.toℕ i))) (Fin.toℕ<n i)))
                        castℕ : Fin.toℕ (castC₁' (i ↑ˡ suc (2 + n))) ≡ sB₂ + Fin.toℕ i
                        castℕ = toℕ-wk sB₂ (subst 𝔽 (Nat.+-suc sC₁' (2 + n)) (i ↑ˡ suc (2 + n)))
                              ■ cong (sB₂ +_) (toℕ-subst𝔽 (Nat.+-suc sC₁' (2 + n)) (i ↑ˡ suc (2 + n)) ■ Fin.toℕ-↑ˡ i (suc (2 + n)))
                        ins0ℕ-lt-G1 : Fin.toℕ (ins0 (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n))))
                                      ≡ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))
                        ins0ℕ-lt-G1 with Nat.<-cmp (Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (i ↑ˡ (2 + n)))) sB₂
                        ... | tri< lt _ _ = cong Fin.toℕ (sym (insSync↑sB₂ _)) ■ ↑*-lo insSync sB₂ _ lt
                        ... | tri≈ _ eq _ = cong Fin.toℕ (sym (insSync↑sB₂ _)) ■ ↑*-hi insSync sB₂ _ (Nat.≤-reflexive (sym eq)) ■ bodyLo (Nat.≤-reflexive (sym eq))
                        ... | tri> _ _ gt = cong Fin.toℕ (sym (insSync↑sB₂ _)) ■ ↑*-hi insSync sB₂ _ (Nat.<⇒≤ gt) ■ bodyLo (Nat.<⇒≤ gt)
            G2R≡ : G2R ≡ resFlagB₂
            G2R≡ =
                Flags-⋯-cong B₂ colR (Ψ ·ₖ down) ptw
              ■ sym (𝐔.fusionₚ (Flags {sC₁ + (2 + n)} B₂) Ψ down)
              where
                ptw : ∀ (i : 𝔽 (syncs B₂)) →
                      colR (i ↑ˡ (sC₁' + (2 + n))) ≡ (Ψ ·ₖ down) (i ↑ˡ (sC₁ + (2 + n)))
                ptw i = colR≗ρcolR (i ↑ˡ (sC₁' + (2 + n)))
                      ■ cong (Ψ ·ₖ down) insLo
                  where
                    iℕ<sB₂ : Fin.toℕ (i ↑ˡ (sC₁' + (2 + n))) Nat.< sB₂
                    iℕ<sB₂ = subst (Nat._< sB₂) (sym (Fin.toℕ-↑ˡ i (sC₁' + (2 + n)))) (Fin.toℕ<n i)
                    insLo : ins0 (i ↑ˡ (sC₁' + (2 + n))) ≡ (i ↑ˡ (sC₁ + (2 + n)))
                    insLo = Fin.toℕ-injective
                      ( cong Fin.toℕ (sym (insSync↑sB₂ (i ↑ˡ (sC₁' + (2 + n)))))
                      ■ ↑*-lo insSync sB₂ (i ↑ˡ (sC₁' + (2 + n))) iℕ<sB₂
                      ■ Fin.toℕ-↑ˡ i (sC₁' + (2 + n))
                      ■ sym (Fin.toℕ-↑ˡ i (sC₁ + (2 + n))) )
