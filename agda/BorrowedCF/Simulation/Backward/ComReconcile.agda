-- | Reconcile core for the telescoped backward R-Com / R-Choice: the general
--   (multi-block) collapse of the R-Com weakening `wkₚ` composed with the leaf
--   substitution `leafσ`.  Extracted (duplicated) VERBATIM from the forward
--   BorrowedCF.Simulation.Support.Theorems.Com `U-com-step` `wkρ-leafσ` chain,
--   generalised in both bind groups.  Append-only, zero forward-risk (like
--   Backward.SplitReconcile).
--
--   The singleton flat engine (Backward.Com.com-go, before telescoping) used
--   `com-νσ-wk` (no subst, since syncs (b ∷ []) = 0 definitionally); the general
--   case needs the `syncs`-transport `subst Tm eqAB`, exactly as the forward.
module BorrowedCF.Simulation.Backward.ComReconcile where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import BorrowedCF.Simulation.Support.BlockPerm
  using (toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-↑*-ge; toℕ-↑*-lt)
open import BorrowedCF.Simulation.Support.Theorems.PhiTel
  using (canonₛ; leafσ; Btel; Bφ; Uν-flatΦ; plugΦ-++; _++Φ_)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers1
  using (syncs-cons-irrel; canonₛ-suc-shift; leafσ-tail; leafσ-A₁; leafσ-B₁)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2
  using (plugΦ-cong; subst-Bφ-c)
open import BorrowedCF.Simulation.Support.Theorems.Com
  using (Bφ-head; subst-chan-wk1; frame-plug*ᵣ)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯; ++ₛ-VSub)
open import BorrowedCF.Simulation.Support.TranslationProperties using (U-⋯ₚ; U-cong; ≡→≋)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (VSub-canonₛ)
open import BorrowedCF.Reduction.Base using (value-⋯; V-K; V-`)
open import BorrowedCF.Processes.Translation using (syncs; UChan; ϕ[_])
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; plugΦ; wkΦ; 𝓒[_×_×_])

open Fin.Patterns

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) where

  private
    a₀ᵂ c₀ᵂ : ℕ
    a₀ᵂ = b₁ + sum B₁
    c₀ᵂ = b₂ + sum B₂

  wkρ : a₀ᵂ + c₀ᵂ + m →ᵣ sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m
  wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂)

  private
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂
    sA sB : ℕ
    sA = syncs B₁′
    sB = syncs B₂′

  τ : sum B₁′ + sum B₂′ + m →ₛ sB + (sA + (2 + n))
  τ = leafσ σ B₁′ B₂′
  τR : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n))
  τR = leafσ σ (b₁ ∷ B₁) (b₂ ∷ B₂)

  sA≡ : syncs (b₁ ∷ B₁) ≡ sA
  sA≡ = syncs-cons-irrel b₁ (suc b₁) B₁
  sB≡ : syncs (b₂ ∷ B₂) ≡ sB
  sB≡ = syncs-cons-irrel b₂ (suc b₂) B₂
  eqAB : syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (sA + (2 + n))
  eqAB = cong₂ (λ u v → u + (v + (2 + n))) sB≡ sA≡

  cc₁ : UChan (2 + n)
  cc₁ = (K `unit , 0F , K `unit)
  cc₂ : UChan (sA + (2 + n))
  cc₂ = (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit)
  Φrest : Φ* (2 + n) (sB + (sA + (2 + n)))
  Φrest = Btel B₁′ cc₁ ++Φ Btel B₂′ cc₂

  Vτ : VSub τ
  Vτ = ++ₛ-VSub
         (++ₛ-VSub
           (λ i → value-⋯ (VSub-canonₛ B₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
           (VSub-canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
         (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                   (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))

  private
    wkₚ-step : (x : 𝔽 (a₀ᵂ + c₀ᵂ + m)) →
               Fin.toℕ (wkρ x)
               ≡ Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀ᵂ) (Fin.cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))
    wkₚ-step x = Fin.toℕ-cast (sym (+-assoc (suc a₀ᵂ) (suc c₀ᵂ) m))
                   ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀ᵂ) (Fin.cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))

    toℕ-wkρ-lt : (x : 𝔽 (a₀ᵂ + c₀ᵂ + m)) → Fin.toℕ x Nat.< a₀ᵂ → Fin.toℕ (wkρ x) ≡ suc (Fin.toℕ x)
    toℕ-wkρ-lt x lt =
        wkₚ-step x
      ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀ᵂ) zc zclt
      ■ czN
      where
        zc = Fin.cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zclt : Fin.toℕ zc Nat.< suc a₀ᵂ
        zclt = subst (Nat._< suc a₀ᵂ) (sym czN) (Nat.s≤s lt)

    toℕ-wkρ-ge : (x : 𝔽 (a₀ᵂ + c₀ᵂ + m)) → a₀ᵂ Nat.≤ Fin.toℕ x → Fin.toℕ (wkρ x) ≡ 2 + Fin.toℕ x
    toℕ-wkρ-ge x ge =
        wkₚ-step x
      ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀ᵂ) zc zcge
      ■ cong (suc a₀ᵂ +_) (toℕ-weaken*ᵣ 1 (Fin.reduce≥ zc zcge) ■ cong suc redN)
      ■ arith
      where
        zc = Fin.cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ᵂ c₀ᵂ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zcge : suc a₀ᵂ Nat.≤ Fin.toℕ zc
        zcge = subst (suc a₀ᵂ Nat.≤_) (sym czN) (Nat.s≤s ge)
        redN : Fin.toℕ (Fin.reduce≥ zc zcge) ≡ Fin.toℕ x Nat.∸ a₀ᵂ
        redN = toℕ-reduce≥ zc zcge ■ cong (Nat._∸ suc a₀ᵂ) czN ■ refl
        arith : suc a₀ᵂ + suc (Fin.toℕ x Nat.∸ a₀ᵂ) ≡ 2 + Fin.toℕ x
        arith = cong suc (Nat.+-suc a₀ᵂ (Fin.toℕ x Nat.∸ a₀ᵂ))
              ■ cong (λ z → suc (suc z)) (Nat.m+[n∸m]≡n ge)

    subst-σ-app : ∀ {c d D} (eq : c ≡ d) (ρ : D →ₛ c) (x : 𝔽 D) →
                  subst (λ z → D →ₛ z) eq ρ x ≡ subst Tm eq (ρ x)
    subst-σ-app refl ρ x = refl

    wkρ-map-tail : (i : 𝔽 m) → wkρ ((a₀ᵂ + c₀ᵂ) ↑ʳ i) ≡ (suc a₀ᵂ + suc c₀ᵂ) ↑ʳ i
    wkρ-map-tail i = Fin.toℕ-injective
      ( toℕ-wkρ-ge ((a₀ᵂ + c₀ᵂ) ↑ʳ i) geq
      ■ cong (2 +_) (Fin.toℕ-↑ʳ (a₀ᵂ + c₀ᵂ) i)
      ■ sym (Fin.toℕ-↑ʳ (suc a₀ᵂ + suc c₀ᵂ) i ■ arith) )
      where
        geq : a₀ᵂ Nat.≤ Fin.toℕ ((a₀ᵂ + c₀ᵂ) ↑ʳ i)
        geq = subst (a₀ᵂ Nat.≤_) (sym (Fin.toℕ-↑ʳ (a₀ᵂ + c₀ᵂ) i)) (Nat.≤-trans (Nat.m≤m+n a₀ᵂ c₀ᵂ) (Nat.m≤m+n (a₀ᵂ + c₀ᵂ) (Fin.toℕ i)))
        arith : suc a₀ᵂ + suc c₀ᵂ + Fin.toℕ i ≡ 2 + ((a₀ᵂ + c₀ᵂ) + Fin.toℕ i)
        arith = solve 3 (λ A C I → con 1 :+ A :+ (con 1 :+ C) :+ I := con 2 :+ ((A :+ C) :+ I)) refl a₀ᵂ c₀ᵂ (Fin.toℕ i)
          where open +-*-Solver

  -- The general R-Com weakening collapse: wkₚ ·ₖ leafσ (fired bind groups) equals
  -- the leaf substitution of the contractum bind groups, up to the `syncs` transport.
  wkρ-leafσ : (wkρ ·ₖ τ) ≗ subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eqAB τR
  wkρ-leafσ x = coreEq ■ sym (subst-σ-app eqAB τR x)
    where
      coreEq : τ (wkρ x) ≡ subst Tm eqAB (τR x)
      coreEq with Fin.splitAt (a₀ᵂ + c₀ᵂ) x in eqo
      ... | inj₂ i =
            leafσ-tail σ B₁′ B₂′ (wkρ x) i splitWkρ
          ■ tailReconcile
        where
          x≡ : x ≡ (a₀ᵂ + c₀ᵂ) ↑ʳ i
          x≡ = sym (Fin.splitAt⁻¹-↑ʳ eqo)
          wkρx≡ : wkρ x ≡ (suc a₀ᵂ + suc c₀ᵂ) ↑ʳ i
          wkρx≡ = cong wkρ x≡ ■ wkρ-map-tail i
          splitWkρ : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₂ i
          splitWkρ = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                   ■ Fin.splitAt-↑ʳ (sum B₁′ + sum B₂′) m i
          tailReconcile :
            σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁′) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
            ≡ subst Tm eqAB (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
          tailReconcile = J-tail sB≡ sA≡
            where
              J-tail : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                     → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sb₁ ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                       ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                           (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
              J-tail refl refl = refl
      ... | inj₁ z with Fin.splitAt a₀ᵂ z in eqi
      ...   | inj₁ j =
                leafσ-A₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc j) splitWkρ-outer splitWkρ-inner
              ■ B₁reconcile
            where
              x≡ : x ≡ (j ↑ˡ c₀ᵂ) ↑ˡ m
              x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ˡ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
              toℕj< : Fin.toℕ j Nat.< a₀ᵂ
              toℕj< = Fin.toℕ<n j
              toℕx< : Fin.toℕ x Nat.< a₀ᵂ
              toℕx< = subst (Nat._< a₀ᵂ) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀ᵂ) m ■ Fin.toℕ-↑ˡ j c₀ᵂ)) toℕj<
              zB : 𝔽 (sum B₁′ + sum B₂′)
              zB = (Fin.suc j) ↑ˡ sum B₂′
              wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
              wkρx≡ = Fin.toℕ-injective
                ( toℕ-wkρ-lt x toℕx<
                ■ cong suc (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀ᵂ) m ■ Fin.toℕ-↑ˡ j c₀ᵂ)
                ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ˡ (Fin.suc j) (sum B₂′) ) )
              splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
              splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                             ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
              splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₁ (Fin.suc j)
              splitWkρ-inner = Fin.splitAt-↑ˡ (sum B₁′) (Fin.suc j) (sum B₂′)
              B₁reconcile :
                canonₛ B₁′ (K `unit , 0F , K `unit) (Fin.suc j) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
                ≡ subst Tm eqAB (canonₛ (b₁ ∷ B₁) (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
              B₁reconcile =
                  cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)) (canonₛ-suc-shift b₁ B₁ 0F (K `unit) j)
                ■ J-A₁ sB≡ sA≡
                where
                  ccA : UChan (2 + n)
                  ccA = (K `unit , 0F , K `unit)
                  J-A₁ : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                       → subst (λ z → Tm (z + (2 + n))) e₁ (canonₛ (b₁ ∷ B₁) ccA j) ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                         ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                             (canonₛ (b₁ ∷ B₁) ccA j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                  J-A₁ refl refl = refl
      ...   | inj₂ k =
                leafσ-B₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc k) splitWkρ-outer splitWkρ-inner
              ■ B₂reconcile
            where
              x≡ : x ≡ (a₀ᵂ ↑ʳ k) ↑ˡ m
              x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ʳ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
              toℕx≥ : a₀ᵂ Nat.≤ Fin.toℕ x
              toℕx≥ = subst (a₀ᵂ Nat.≤_) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ᵂ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ᵂ k)) (Nat.m≤m+n a₀ᵂ (Fin.toℕ k))
              zB : 𝔽 (sum B₁′ + sum B₂′)
              zB = sum B₁′ ↑ʳ (Fin.suc k)
              wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
              wkρx≡ = Fin.toℕ-injective
                ( toℕ-wkρ-ge x toℕx≥
                ■ cong (2 +_) (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ᵂ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ᵂ k)
                ■ arith
                ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ʳ (sum B₁′) (Fin.suc k) ) )
                where
                  arith : 2 + (a₀ᵂ + Fin.toℕ k) ≡ suc a₀ᵂ + suc (Fin.toℕ k)
                  arith = solve 2 (λ A K → con 2 :+ (A :+ K) := con 1 :+ A :+ (con 1 :+ K)) refl a₀ᵂ (Fin.toℕ k)
                    where open +-*-Solver
              splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
              splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                             ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
              splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₂ (Fin.suc k)
              splitWkρ-inner = Fin.splitAt-↑ʳ (sum B₁′) (sum B₂′) (Fin.suc k)
              ccB : ∀ (s : ℕ) → UChan (s + (2 + n))
              ccB s = (K `unit , weaken* ⦃ Kᵣ ⦄ s 1F , K `unit)
              B₂reconcile :
                canonₛ B₂′ (ccB (syncs B₁′)) (Fin.suc k)
                ≡ subst Tm eqAB (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
              B₂reconcile = J-B₂ sA≡
                where
                  J-B₂ : ∀ {sb₁} (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                       → canonₛ (suc b₂ ∷ B₂) (ccB sb₁) (Fin.suc k)
                         ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ e₁)
                             (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
                  J-B₂ refl =
                      canonₛ-suc-shift b₂ B₂ (weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) 1F) (K `unit) k
                    ■ cong (λ e → subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e
                                    (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k))
                        (≡-irrelevant (syncs-cons-irrel b₂ (suc b₂) B₂) sB≡)
                    ■ substReshape
                    where
                      T₀ = canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k
                      substReshape :
                        subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ T₀
                        ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ refl) T₀
                      substReshape = subst-fn-≡′ sB≡ T₀
                        where
                          subst-fn-≡′ : ∀ {a a′} (e : a ≡ a′) (t : Tm (a + (syncs (b₁ ∷ B₁) + (2 + n)))) →
                                        subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e t
                                        ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e refl) t
                          subst-fn-≡′ refl t = refl

  -- The full backward reconcile: the RU-Com RHS leaf (fired frames, at the
  -- combined φ-telescope) is ≋ to the translation of the typed contractum.
  com-back : (ϕ₁ : ϕ[ b₁ ] ≡ ϕ[ suc b₁ ]) (ϕ₂ : ϕ[ b₂ ] ≡ ϕ[ suc b₂ ])
             (E₁ E₂ : Frame* (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m))
             (e : Tm (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m))
             (P : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)) →
    U.ν (plugΦ Φrest ( U.⟪ frame*-⋯ (E₁ ⋯ᶠ* wkρ) τ Vτ [ * ]* ⟫
         U.∥ ( U.⟪ frame*-⋯ (E₂ ⋯ᶠ* wkρ) τ Vτ [ ((e ⋯ wkρ) ⋯ τ) ]* ⟫
         U.∥ U[ P T.⋯ₚ wkρ ] τ ) ))
      U.≋ U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ
  com-back ϕ₁ ϕ₂ E₁ E₂ e P = back
    where
      EE₁ EE₂ : Frame* (sum B₁′ + sum B₂′ + m)
      EE₁ = E₁ ⋯ᶠ* wkρ
      EE₂ = E₂ ⋯ᶠ* wkρ
      ee : Tm (sum B₁′ + sum B₂′ + m)
      ee = e ⋯ wkρ
      PP : T.Proc (sum B₁′ + sum B₂′ + m)
      PP = P T.⋯ₚ wkρ
      F₁ F₂ : Frame* (sB + (sA + (2 + n)))
      F₁ = frame*-⋯ EE₁ τ Vτ
      F₂ = frame*-⋯ EE₂ τ Vτ
      eM : Tm (sB + (sA + (2 + n)))
      eM = ee ⋯ τ
      RP : U.Proc (sB + (sA + (2 + n)))
      RP = U[ PP ] τ
      QR : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)
      QR = (T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P
      QL' : T.Proc (sum B₁′ + sum B₂′ + m)
      QL' = (T.⟪ EE₁ [ K `unit ]* ⟫ T.∥ T.⟪ EE₂ [ ee ]* ⟫) T.∥ PP
      WR : U.Proc (sB + (sA + (2 + n)))
      WR = U[ QL' ] τ
      cc₂' : UChan (syncs (b₁ ∷ B₁) + (2 + n))
      cc₂' = (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) 1F , K `unit)

      QL'≡ : QL' ≡ QR T.⋯ₚ wkρ
      QL'≡ = cong₂ T._∥_
               (cong₂ T._∥_ (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₁ wkρ)))
                            (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₂ wkρ))))
               refl

      U-subst-cod : ∀ {c d} (eq : c ≡ d) (Q : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m))
                    (ρ : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ c) →
                    subst U.Proc eq (U[ Q ] ρ) ≡ U[ Q ] (subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eq ρ)
      U-subst-cod refl Q ρ = refl

      WR≡XR : WR ≡ subst U.Proc eqAB (U[ QR ] τR)
      WR≡XR = cong (λ Q → U[ Q ] τ) QL'≡ ■ U-⋯ₚ QR ■ U-cong QR wkρ-leafσ ■ sym (U-subst-cod eqAB QR τR)

      leftEq : (U.⟪ F₁ [ * ]* ⟫ U.∥ U.⟪ F₂ [ eM ]* ⟫) U.∥ RP ≡ WR
      leftEq = cong₂ U._∥_
                 (cong₂ U._∥_ (cong U.⟪_⟫ (sym (frame-plug* EE₁ τ Vτ)))
                              (cong U.⟪_⟫ (sym (frame-plug* EE₂ τ Vτ))))
                 refl

      bridgeBlocks : Bφ B₁′ cc₁ (Bφ B₂′ cc₂ (subst U.Proc eqAB (U[ QR ] τR)))
                   ≡ Bφ (b₁ ∷ B₁) cc₁ (Bφ (b₂ ∷ B₂) cc₂' (U[ QR ] τR))
      bridgeBlocks =
          cong (Bφ B₁′ cc₁) innerBridge
        ■ sym (Bφ-head b₁ (suc b₁) ϕ₁ B₁ cc₁ (Bφ (b₂ ∷ B₂) cc₂' (U[ QR ] τR)))
        where
          X : U.Proc (syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)))
          X = U[ QR ] τR
          eA : syncs (b₁ ∷ B₁) + (2 + n) ≡ sA + (2 + n)
          eA = cong (_+ (2 + n)) sA≡
          leaf-final : subst U.Proc (cong (_+ (sA + (2 + n))) sB≡)
                         (subst U.Proc (cong (syncs (b₂ ∷ B₂) +_) eA) X)
                       ≡ subst U.Proc eqAB X
          leaf-final =
              subst-subst (cong (syncs (b₂ ∷ B₂) +_) eA) {cong (_+ (sA + (2 + n))) sB≡} {X}
            ■ cong (λ e → subst U.Proc e X) (≡-irrelevant _ eqAB)
          innerBridge : Bφ B₂′ cc₂ (subst U.Proc eqAB X)
                      ≡ subst U.Proc eA (Bφ (b₂ ∷ B₂) cc₂' X)
          innerBridge =
            sym ( subst-Bφ-c eA (b₂ ∷ B₂) cc₂' X
                ■ Bφ-head b₂ (suc b₂) ϕ₂ B₂ (subst UChan eA cc₂')
                    (subst U.Proc (cong (syncs (b₂ ∷ B₂) +_) eA) X)
                ■ cong₂ (Bφ B₂′) (subst-chan-wk1 sA≡ 1F) leaf-final )

      flatBridge : U.ν (plugΦ Φrest WR) ≡ U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂) QR ] σ
      flatBridge =
          cong U.ν ( plugΦ-++ (Btel B₁′ cc₁) (Btel B₂′ cc₂) WR
                   ■ cong (Bφ B₁′ cc₁) (cong (Bφ B₂′ cc₂) WR≡XR)
                   ■ bridgeBlocks )
        ■ sym (Uν-flatΦ σ (b₁ ∷ B₁) (b₂ ∷ B₂) QR)

      back : U.ν (plugΦ Φrest ( U.⟪ F₁ [ * ]* ⟫ U.∥ ( U.⟪ F₂ [ eM ]* ⟫ U.∥ RP ) ))
             U.≋ U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂) QR ] σ
      back = U.ν-cong (plugΦ-cong Φrest (U.∥-assoc ◅◅ ≡→≋ leftEq)) ◅◅ ≡→≋ flatBridge
