-- | Backward R-Com FIRE+RECONCILE engine for the ALREADY-FRONT-FORCED,
--   multi-block redex.  Direct generalisation of Backward.Com.com-go's `finish`
--   block: the singleton bind groups `suc b₁' ∷ []` / `suc b₂' ∷ []` become
--   `suc b₁ ∷ B₁` / `suc b₂ ∷ B₂`, the singleton confinement counts
--   (`count-handle-comᴸ/ᴿ`) become the general `count-handle-groupᴸ/ᴿ`, the
--   ¬Mobile facts are read straight off the redex typing (`send-¬mobile` /
--   `recv-¬mobile`), and the inline reconcile (com-νσ-wk chain) is replaced by a
--   single `CR.com-back`.  The two consumed com handles (send 0F, recv front)
--   are absent from the residual message/rest by the same linearity counting,
--   strengthened through the R-Com weakening `wkₚ`; the fired step is an R-Com
--   under a `∥-assoc` R-Struct sandwich.
module BorrowedCF.Simulation.Backward.ComFire where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import BorrowedCF.Simulation.Backward.ComReconcile as CR
open import BorrowedCF.Simulation.Backward.ComConfineGen using (send-¬mobile; recv-¬mobile)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 using (com-head≥1; com-head≥2)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋; U-⋯ₚ; U-cong)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.ReverseConfine using (strengthen-frame*)
open import BorrowedCF.Simulation.Support.Strengthen
  using (strengthen-Tm-gen*; strengthen-Proc-gen*; Inverter*; ↑*-↑ˡ; ↑*-↑ʳ)
open import BorrowedCF.Simulation.Support.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-groupᴿ)
open import BorrowedCF.Simulation.Support.RevGrindA using (barevar-arg-count; invApp-arg)
open import BorrowedCF.Simulation.Support.RevComConfine using (count-plug-add)
open import BorrowedCF.Simulation.Support.InvFrame as IF using (inv-app)
open import BorrowedCF.Simulation.Support.BeforeOrder using (count-≼-eq)
open import BorrowedCF.Simulation.Support.Confine
  using (count; ≼⇒count≤; count-self; count-join-PS; count-join-Dir; count0⇒∉dom; +≡0)
open import BorrowedCF.Simulation.Support.ReverseInv using (⊗-inj)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (leafσ)
open import BorrowedCF.Processes.Translation using (syncs; ϕ[_])
open import BorrowedCF.Types using (unr⇒mobile)
open import BorrowedCF.TypedEq using (_/_⊢-≋_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective)
import Data.Sum as Sum
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Context using (join; biasedDir; _∶_≼_; _⸴*_; _∥_)
open import BorrowedCF.Context.Pattern using (_[_]𝓅)
open import BorrowedCF.Context.Domain using (dom)
open import Data.Fin.Subset using (_∉_)

open TP using (BindGroup; structBinder; inv-⟪⟫; inv-∥; inv-ν)
open Fin.Patterns

------------------------------------------------------------------------
-- Self-contained helpers copied VERBATIM from Backward.Com (which is
-- concurrently owned/edited by another agent; copied here to decouple the
-- module dependency).  All are self-contained ℕ/Fin/Value lemmas.
------------------------------------------------------------------------

private
  cast₁ : ∀ a c k → 𝔽 (suc (a + c + k)) → 𝔽 (suc a + (c + k))
  cast₁ a c k = Fin.cast (cong suc (+-assoc a c k))
  cast₂ : ∀ a c k → 𝔽 (suc a + suc (c + k)) → 𝔽 (suc a + suc c + k)
  cast₂ a c k = Fin.cast (sym (+-assoc (suc a) (suc c) k))

wkₚ-A : ∀ a c {k} (v : 𝔽 a) →
        wkₚ {n = k} a c ((v ↑ˡ c) ↑ˡ k) ≡ ((Fin.suc v ↑ˡ suc c) ↑ˡ k)
wkₚ-A a c {k} v =
    cong (λ z → cast₂ a c k ((weakenᵣ ↑* suc a) z)) step1
  ■ cong (cast₂ a c k) step2
  ■ step3
  where
    i : 𝔽 (a + c + k)
    i = (v ↑ˡ c) ↑ˡ k
    toℕi : Fin.toℕ i ≡ Fin.toℕ v
    toℕi = toℕ-↑ˡ (v ↑ˡ c) k ■ toℕ-↑ˡ v c
    step1 : cast₁ a c k (Fin.suc i) ≡ (Fin.suc v) ↑ˡ (c + k)
    step1 = toℕ-injective
      ( toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
      ■ cong suc toℕi
      ■ sym (toℕ-↑ˡ (Fin.suc v) (c + k)) )
    step2 : (weakenᵣ ↑* suc a) ((Fin.suc v) ↑ˡ (c + k)) ≡ (Fin.suc v) ↑ˡ suc (c + k)
    step2 = ↑*-↑ˡ weakenᵣ (suc a) (Fin.suc v)
    step3 : cast₂ a c k ((Fin.suc v) ↑ˡ suc (c + k)) ≡ (Fin.suc v ↑ˡ suc c) ↑ˡ k
    step3 = toℕ-injective
      ( toℕ-cast (sym (+-assoc (suc a) (suc c) k)) ((Fin.suc v) ↑ˡ suc (c + k))
      ■ toℕ-↑ˡ (Fin.suc v) (suc (c + k))
      ■ sym (toℕ-↑ˡ (Fin.suc v ↑ˡ suc c) k ■ toℕ-↑ˡ (Fin.suc v) (suc c)) )

wkₚ-B : ∀ a c {k} (w : 𝔽 c) →
        wkₚ {n = k} a c ((a ↑ʳ w) ↑ˡ k) ≡ (((suc a) ↑ʳ Fin.suc w) ↑ˡ k)
wkₚ-B a c {k} w =
    cong (λ z → cast₂ a c k ((weakenᵣ ↑* suc a) z)) step1
  ■ cong (cast₂ a c k) step2
  ■ step3
  where
    i : 𝔽 (a + c + k)
    i = (a ↑ʳ w) ↑ˡ k
    toℕi : Fin.toℕ i ≡ a + Fin.toℕ w
    toℕi = toℕ-↑ˡ (a ↑ʳ w) k ■ toℕ-↑ʳ a w
    step1 : cast₁ a c k (Fin.suc i) ≡ (suc a) ↑ʳ (w ↑ˡ k)
    step1 = toℕ-injective
      ( toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
      ■ cong suc toℕi
      ■ sym (toℕ-↑ʳ (suc a) (w ↑ˡ k) ■ cong (suc a +_) (toℕ-↑ˡ w k)) )
    step2 : (weakenᵣ ↑* suc a) ((suc a) ↑ʳ (w ↑ˡ k)) ≡ (suc a) ↑ʳ Fin.suc (w ↑ˡ k)
    step2 = ↑*-↑ʳ weakenᵣ (suc a) (w ↑ˡ k)
    step3 : cast₂ a c k ((suc a) ↑ʳ Fin.suc (w ↑ˡ k)) ≡ ((suc a) ↑ʳ Fin.suc w) ↑ˡ k
    step3 = toℕ-injective
      ( toℕ-cast (sym (+-assoc (suc a) (suc c) k)) ((suc a) ↑ʳ Fin.suc (w ↑ˡ k))
      ■ toℕ-↑ʳ (suc a) (Fin.suc (w ↑ˡ k))
      ■ cong (λ t → suc a + suc t) (toℕ-↑ˡ w k)
      ■ sym ( toℕ-↑ˡ ((suc a) ↑ʳ Fin.suc w) k
            ■ toℕ-↑ʳ (suc a) (Fin.suc w) ) )

wkₚ-C : ∀ a c {k} (u : 𝔽 k) →
        wkₚ {n = k} a c ((a + c) ↑ʳ u) ≡ ((suc a + suc c) ↑ʳ u)
wkₚ-C a c {k} u =
    cong (λ z → cast₂ a c k ((weakenᵣ ↑* suc a) z)) step1
  ■ cong (cast₂ a c k) step2
  ■ step3
  where
    i : 𝔽 (a + c + k)
    i = (a + c) ↑ʳ u
    step1 : cast₁ a c k (Fin.suc i) ≡ (suc a) ↑ʳ (c ↑ʳ u)
    step1 = toℕ-injective
      ( toℕ-cast (cong suc (+-assoc a c k)) (Fin.suc i)
      ■ cong suc (toℕ-↑ʳ (a + c) u)
      ■ cong suc (+-assoc a c (Fin.toℕ u))
      ■ sym (toℕ-↑ʳ (suc a) (c ↑ʳ u) ■ cong (suc a +_) (toℕ-↑ʳ c u)) )
    step2 : (weakenᵣ ↑* suc a) ((suc a) ↑ʳ (c ↑ʳ u)) ≡ (suc a) ↑ʳ Fin.suc (c ↑ʳ u)
    step2 = ↑*-↑ʳ weakenᵣ (suc a) (c ↑ʳ u)
    step3 : cast₂ a c k ((suc a) ↑ʳ Fin.suc (c ↑ʳ u)) ≡ (suc a + suc c) ↑ʳ u
    step3 = toℕ-injective
      ( toℕ-cast (sym (+-assoc (suc a) (suc c) k)) ((suc a) ↑ʳ Fin.suc (c ↑ʳ u))
      ■ toℕ-↑ʳ (suc a) (Fin.suc (c ↑ʳ u))
      ■ cong (λ t → suc a + suc t) (toℕ-↑ʳ c u)
      ■ sym (+-assoc (suc a) (suc c) (Fin.toℕ u))
      ■ sym (toℕ-↑ʳ (suc a + suc c) u) )

Hcom : ∀ a c k → 𝔽 (suc a + suc c + k) → Set
Hcom a c k z = (z ≡ 0F) Sum.⊎ (z ≡ ((suc a) ↑ʳ (Fin.zero {c})) ↑ˡ k)

inv-wkₚ : ∀ a c k → Inverter* (wkₚ {n = k} a c) (Hcom a c k)
inv-wkₚ a c k y ¬H with Fin.splitAt (suc a + suc c) y in seq
... | Sum.inj₂ u = (a + c) ↑ʳ u , (wkₚ-C a c u ■ sym yeq)
  where
    yeq : y ≡ (suc a + suc c) ↑ʳ u
    yeq = sym (Fin.join-splitAt (suc a + suc c) k y)
        ■ cong (Fin.join (suc a + suc c) k) seq
... | Sum.inj₁ d with Fin.splitAt (suc a) d in seqd
...   | Sum.inj₁ 0F = ⊥-elim (¬H (Sum.inj₁ yeq))
  where
    yeq : y ≡ 0F
    yeq = sym (Fin.join-splitAt (suc a + suc c) k y)
        ■ cong (Fin.join (suc a + suc c) k) seq
        ■ cong (_↑ˡ k)
            ( sym (Fin.join-splitAt (suc a) (suc c) d)
            ■ cong (Fin.join (suc a) (suc c)) seqd )
...   | Sum.inj₁ (Fin.suc v) = (v ↑ˡ c) ↑ˡ k , (wkₚ-A a c v ■ sym yeq)
  where
    yeq : y ≡ (Fin.suc v ↑ˡ suc c) ↑ˡ k
    yeq = sym (Fin.join-splitAt (suc a + suc c) k y)
        ■ cong (Fin.join (suc a + suc c) k) seq
        ■ cong (_↑ˡ k)
            ( sym (Fin.join-splitAt (suc a) (suc c) d)
            ■ cong (Fin.join (suc a) (suc c)) seqd )
...   | Sum.inj₂ 0F = ⊥-elim (¬H (Sum.inj₂ yeq))
  where
    yeq : y ≡ ((suc a) ↑ʳ 0F) ↑ˡ k
    yeq = sym (Fin.join-splitAt (suc a + suc c) k y)
        ■ cong (Fin.join (suc a + suc c) k) seq
        ■ cong (_↑ˡ k)
            ( sym (Fin.join-splitAt (suc a) (suc c) d)
            ■ cong (Fin.join (suc a) (suc c)) seqd )
...   | Sum.inj₂ (Fin.suc w) = (a ↑ʳ w) ↑ˡ k , (wkₚ-B a c w ■ sym yeq)
  where
    yeq : y ≡ ((suc a) ↑ʳ Fin.suc w) ↑ˡ k
    yeq = sym (Fin.join-splitAt (suc a + suc c) k y)
        ■ cong (Fin.join (suc a + suc c) k) seq
        ■ cong (_↑ˡ k)
            ( sym (Fin.join-splitAt (suc a) (suc c) d)
            ■ cong (Fin.join (suc a) (suc c)) seqd )

value-⋯ᵣ⁻¹ : ∀ {k N} (ρ : k →ᵣ N) (e₀ : Tm k) → Value (e₀ ⋯ ρ) → Value e₀
value-⋯ᵣ⁻¹ ρ (` x)      V           = V-`
value-⋯ᵣ⁻¹ ρ (K c)      V           = V-K
value-⋯ᵣ⁻¹ ρ (ƛ e)      V           = V-λ
value-⋯ᵣ⁻¹ ρ (e₁ ⊗ e₂)  (V-⊗ V₁ V₂) = V-⊗ (value-⋯ᵣ⁻¹ ρ e₁ V₁) (value-⋯ᵣ⁻¹ ρ e₂ V₂)
value-⋯ᵣ⁻¹ ρ (`inj i e) (V-⊕ V)     = V-⊕ (value-⋯ᵣ⁻¹ ρ e V)

value-⋯⁻¹ᶜ : ∀ {k N} (σ : k →ₛ N) → VSub σ → (e₀ : Tm k) → Value (e₀ ⋯ σ) → Value e₀
value-⋯⁻¹ᶜ σ Vσ (` x)      V           = V-`
value-⋯⁻¹ᶜ σ Vσ (K c)      V           = V-K
value-⋯⁻¹ᶜ σ Vσ (ƛ e)      V           = V-λ
value-⋯⁻¹ᶜ σ Vσ (e₁ ⊗ e₂)  (V-⊗ V₁ V₂) = V-⊗ (value-⋯⁻¹ᶜ σ Vσ e₁ V₁) (value-⋯⁻¹ᶜ σ Vσ e₂ V₂)
value-⋯⁻¹ᶜ σ Vσ (`inj i e) (V-⊕ V)     = V-⊕ (value-⋯⁻¹ᶜ σ Vσ e V)

send-arg-count-chain : ∀ {N} {Γ : Ctx N} {γ : Struct N} {aS : Tm N} {x : 𝔽 N}
  {a} {α β : Struct N} {T ϵ}
  → ¬ Unr (lookup Γ x) → Γ ∶ join (Arr.dir a) β α ≼ γ → Γ ; β ⊢ (aS ⊗ (` x)) ∶ T ∣ ϵ → 1 Nat.≤ count x γ
send-arg-count-chain {γ = γ} {aS = aS} {x = x} {a = a} {α = α} {β = β} ¬u join≼ ⊢arg
  with p/s , α' , β' , _ , _ , _ , _ , join≼' , _ , _ , _ , _ , ⊢x ← inv-⊗ ⊢arg =
  let x≼β' = proj₂ (inv-` ⊢x)
      1≤β' = subst (Nat._≤ count x β') (count-self x) (≼⇒count≤ ¬u x≼β')
      β'≤joinβ = subst (count x β' Nat.≤_) (sym (count-join-PS p/s x α' β')) (Nat.m≤n+m (count x β') (count x α'))
      β'≤β = Nat.≤-trans β'≤joinβ (≼⇒count≤ ¬u join≼')
      β≤joinγ = subst (count x β Nat.≤_) (sym (count-join-Dir (Arr.dir a) x β α)) (Nat.m≤m+n (count x β) (count x α))
      β≤γ = Nat.≤-trans β≤joinγ (≼⇒count≤ ¬u join≼)
  in Nat.≤-trans 1≤β' (Nat.≤-trans β'≤β β≤γ)

send-arg-count : ∀ {N} {Γ : Ctx N} {γ : Struct N} {aS : Tm N} {x : 𝔽 N} {Uu ϵ}
  → ¬ Unr (lookup Γ x) → Γ ; γ ⊢ K `send ·¹ (aS ⊗ (` x)) ∶ Uu ∣ ϵ → 1 Nat.≤ count x γ
send-arg-count ¬u ⊢redex
  with aa , _ , _ , _ , join≼ , _ , _ , invapp ← inv-· ⊢redex =
  send-arg-count-chain {a = aa} ¬u join≼ (proj₂ (invApp-arg invapp))

------------------------------------------------------------------------
-- com-fire : the front-forced, multi-block reverse RU-Com engine.
------------------------------------------------------------------------

com-fire : ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    {F₀ˢ F₀ᴿ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
    {aS : Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
    {Pr : TP.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
    {F₁ F₂ : Frame* (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
    {e e₁ e₁′ e₂ e₂′ : Tm (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
    {P₁ : UP.Proc (syncs (suc b₂ ∷ B₂) + (syncs (suc b₁ ∷ B₁) + (2 + n)))}
    (V : Value e)
  → Γ ; g ⊢ₚ TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
       (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` 0F)) ]* ⟫
        TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫ TP.∥ Pr))
  → F₁ ≡ frame*-⋯ F₀ˢ (leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
  → (e ⊗ ((e₁ ⊗ (` UR.wkΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂) 0F)) ⊗ e₁′)) ≡ (aS ⊗ (` 0F)) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
  → F₂ ≡ frame*-⋯ F₀ᴿ (leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)) (CR.Vτ σ Vσ b₁ b₂ B₁ B₂)
  → ((e₂ ⊗ (` UR.wkΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂) 1F)) ⊗ e₂′) ≡ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ⋯ leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
  → P₁ ≡ U[ Pr ] (leafσ σ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂))
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` 0F)) ]* ⟫
           TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
            (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ )
com-fire {m} {n} σ Vσ {Γ} Γ-S {g} b₁ b₂ B₁ B₂ {F₀ˢ} {F₀ᴿ} {aS} {Pr} {F₁} {F₂} {e} {e₁} {e₁′} {e₂} {e₂′} {P₁}
         V ⊢P FeqS argeqS FeqR argeqR Preq
  with _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢body ← inv-ν ⊢P
  with αS , βrest , ≼₁ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with αR , βP , ≼₂ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with 𝒫ˢ , γrˢ , _ , _ , _ , _ , ≼ˢ , _ , _ , _ , ⊢redexˢ
       ← ⊢[]*⁻¹ F₀ˢ (K `send ·¹ (aS ⊗ (` 0F))) (inv-⟪⟫ ⊢PS)
  with 𝒫ᴿ , γrᴿ , _ , _ , _ , _ , ≼ᴿ , _ , _ , _ , ⊢redexᴿ
       ← ⊢[]*⁻¹ F₀ᴿ (K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F))) (inv-⟪⟫ ⊢PR)
  = result
  where
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂

    posR : 𝔽 (sum B₁′ + sum B₂′ + m)
    posR = wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)

    aW cW : ℕ
    aW = b₁ + sum B₁
    cW = b₂ + sum B₂

    wkρ : aW + cW + m →ᵣ sum B₁′ + sum B₂′ + m
    wkρ = wkₚ {n = m} aW cW

    τ : sum B₁′ + sum B₂′ + m →ₛ syncs B₂′ + (syncs B₁′ + (2 + n))
    τ = leafσ σ B₁′ B₂′
    Vτ : VSub τ
    Vτ = CR.Vτ σ Vσ b₁ b₂ B₁ B₂
    Φrest : UR.Φ* (2 + n) (syncs B₂′ + (syncs B₁′ + (2 + n)))
    Φrest = CR.Φrest σ Vσ b₁ b₂ B₁ B₂

    HH = Hcom aW cW m
    invρ = inv-wkₚ aW cW m

    ¬u0  = send-¬mobile ⊢redexˢ
    ¬uyR = recv-¬mobile ⊢redexᴿ
    ¬u0ᵁ  = ¬u0  ∘ unr⇒mobile
    ¬uyRᵁ = ¬uyR ∘ unr⇒mobile
    1≤cᴿ = barevar-arg-count ¬uyRᵁ ⊢redexᴿ

    c0γ = count-handle-groupᴸ B₁′ B₂′ g 0F
    cRγ = count-handle-groupᴿ B₁′ B₂′ g 0F

    1≤rˢ0 = send-arg-count ¬u0ᵁ ⊢redexˢ
    1≤αS0 = subst (1 Nat.≤_) (count-≼-eq ¬u0ᵁ ≼ˢ)
              (Nat.≤-trans 1≤rˢ0
                (subst (count 0F γrˢ Nat.≤_) (sym (count-plug-add 𝒫ˢ γrˢ 0F))
                  (Nat.m≤n+m (count 0F γrˢ) (count 0F (𝒫ˢ [ Struct.[] ]𝓅)))))
    tot0 = subst ((count 0F αS + count 0F βrest) Nat.≤_) c0γ (≼⇒count≤ ¬u0ᵁ ≼₁)
    cβrest0 = Nat.n≤0⇒n≡0 (Nat.s≤s⁻¹ (Nat.≤-trans (Nat.+-monoˡ-≤ (count 0F βrest) 1≤αS0) tot0))
    s2z = Nat.n≤0⇒n≡0 (subst ((count 0F αR + count 0F βP) Nat.≤_) cβrest0 (≼⇒count≤ ¬u0ᵁ ≼₂))
    cαR0 = proj₁ (+≡0 {count 0F αR} s2z)
    cβP0 = proj₂ (+≡0 {count 0F αR} s2z)
    cαS0≤1 = Nat.≤-trans (Nat.m≤m+n (count 0F αS) (count 0F βrest)) tot0
    1≤αRR = subst (1 Nat.≤_) (count-≼-eq ¬uyRᵁ ≼ᴿ)
              (Nat.≤-trans 1≤cᴿ
                (subst (count posR γrᴿ Nat.≤_) (sym (count-plug-add 𝒫ᴿ γrᴿ posR))
                  (Nat.m≤n+m (count posR γrᴿ) (count posR (𝒫ᴿ [ Struct.[] ]𝓅)))))
    subRc = ≼⇒count≤ {x = posR} ¬uyRᵁ ≼₂
    1≤βrestR = Nat.≤-trans 1≤αRR (Nat.≤-trans (Nat.m≤m+n (count posR αR) (count posR βP)) subRc)
    totR = subst ((count posR αS + count posR βrest) Nat.≤_) cRγ (≼⇒count≤ ¬uyRᵁ ≼₁)
    cαSR = Nat.n≤0⇒n≡0 (Nat.s≤s⁻¹ (subst (Nat._≤ 1) (Nat.+-comm (count posR αS) 1)
             (Nat.≤-trans (Nat.+-monoʳ-≤ (count posR αS) 1≤βrestR) totR)))
    βrestR≤1 = Nat.≤-trans (Nat.m≤n+m (count posR βrest) (count posR αS)) totR
    cβPR = Nat.n≤0⇒n≡0 (Nat.s≤s⁻¹ (Nat.≤-trans (Nat.+-monoˡ-≤ (count posR βP) 1≤αRR)
             (Nat.≤-trans subRc βrestR≤1)))
    cαRR≤1 = Nat.≤-trans (Nat.m≤m+n (count posR αR) (count posR βP)) (Nat.≤-trans subRc βrestR≤1)

    strS = strengthen-frame* F₀ˢ (inv-⟪⟫ ⊢PS) HH
    βpS = proj₁ strS
    ⊢plugS = proj₂ (proj₂ (proj₁ (proj₂ strS)))
    supS = proj₁ (proj₂ (proj₂ strS))
    facS = proj₂ (proj₂ (proj₂ strS))
    1≤βpS0 = send-arg-count ¬u0ᵁ ⊢plugS
    factS = facS (λ { h (Sum.inj₁ refl) → ¬u0ᵁ , Nat.≤-trans cαS0≤1 1≤βpS0
                    ; h (Sum.inj₂ refl) → ¬uyRᵁ , subst (Nat._≤ count posR βpS) (sym cαSR) Nat.z≤n })
                 wkρ invρ
    E₁ = proj₁ factS
    Eeq₁ = proj₂ factS

    strR = strengthen-frame* F₀ᴿ (inv-⟪⟫ ⊢PR) HH
    βpR = proj₁ strR
    ⊢plugR = proj₂ (proj₂ (proj₁ (proj₂ strR)))
    supR = proj₁ (proj₂ (proj₂ strR))
    facR = proj₂ (proj₂ (proj₂ strR))
    1≤βpRR = barevar-arg-count ¬uyRᵁ ⊢plugR
    factR = facR (λ { h (Sum.inj₁ refl) → ¬u0ᵁ , subst (Nat._≤ count 0F βpR) (sym cαR0) Nat.z≤n
                    ; h (Sum.inj₂ refl) → ¬uyRᵁ , Nat.≤-trans cαRR≤1 1≤βpRR })
                 wkρ invρ
    E₂ = proj₁ factR
    Eeq₂ = proj₂ factR

    invAppS = inv-app ⊢plugS
    αfn = proj₁ invAppS
    invAppS1 = proj₂ invAppS
    αarg = proj₁ invAppS1
    ⊢pairS = proj₂ (proj₂ (proj₁ (proj₂ (proj₂ invAppS1))))
    cleS = proj₂ (proj₂ (proj₂ invAppS1))
    invPairS = inv-⊗ ⊢pairS
    p/s = proj₁ invPairS
    d1 = proj₂ invPairS
    αaS = proj₁ d1
    d2 = proj₂ d1
    βc0 = proj₁ d2
    d7 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ d2))))
    join≼pr = proj₁ d7
    d11 = proj₂ (proj₂ (proj₂ (proj₂ d7)))
    ⊢aSty = proj₁ d11
    ⊢c0ty = proj₂ d11

    βpS0≤1 = Nat.≤-trans (supS 0F ¬u0ᵁ) cαS0≤1
    1≤βc0 : 1 Nat.≤ count 0F βc0
    1≤βc0 = subst (Nat._≤ count 0F βc0) (count-self (Fin.zero {sum B₁′ + sum B₂′ + m})) (≼⇒count≤ ¬u0ᵁ (proj₂ (inv-` ⊢c0ty)))
    pair0 = Nat.≤-trans
              (subst (Nat._≤ count 0F αarg) (count-join-PS p/s 0F αaS βc0) (≼⇒count≤ ¬u0ᵁ join≼pr))
              (Nat.≤-trans (Nat.m≤n+m (count 0F αarg) (count 0F αfn)) (cleS 0F ¬u0ᵁ))
    cαaS0 = Nat.n≤0⇒n≡0 (Nat.s≤s⁻¹ (subst (Nat._≤ 1) (Nat.+-comm (count 0F αaS) 1)
              (Nat.≤-trans (Nat.+-monoʳ-≤ (count 0F αaS) 1≤βc0)
                (Nat.≤-trans pair0 βpS0≤1))))
    cβpSR = Nat.n≤0⇒n≡0 (subst (count posR βpS Nat.≤_) cαSR (supS posR ¬uyRᵁ))
    cαaSR = Nat.n≤0⇒n≡0 (subst (count posR αaS Nat.≤_) cβpSR
              (Nat.≤-trans (Nat.m≤m+n (count posR αaS) (count posR βc0))
                (Nat.≤-trans
                  (subst (Nat._≤ count posR αarg) (count-join-PS p/s posR αaS βc0) (≼⇒count≤ ¬uyRᵁ join≼pr))
                  (Nat.≤-trans (Nat.m≤n+m (count posR αarg) (count posR αfn)) (cleS posR ¬uyRᵁ)))))
    H∉aS : (h : 𝔽 (sum B₁′ + sum B₂′ + m)) → HH h → h ∉ dom αaS
    H∉aS h (Sum.inj₁ refl) = count0⇒∉dom αaS cαaS0
    H∉aS h (Sum.inj₂ refl) = count0⇒∉dom αaS cαaSR
    strTmS = strengthen-Tm-gen* ⊢aSty wkρ HH invρ H∉aS
    eM = proj₁ strTmS
    eMeq = proj₂ strTmS

    H∉P : (h : 𝔽 (sum B₁′ + sum B₂′ + m)) → HH h → h ∉ dom βP
    H∉P h (Sum.inj₁ refl) = count0⇒∉dom βP cβP0
    H∉P h (Sum.inj₂ refl) = count0⇒∉dom βP cβPR
    strProcP = strengthen-Proc-gen* ⊢Pr wkρ HH invρ H∉P
    P'0 = proj₁ strProcP
    Peq = proj₂ strProcP

    e≡aSτ : e ≡ aS ⋯ τ
    e≡aSτ = proj₁ (⊗-inj argeqS)

    VeM : Value eM
    VeM = value-⋯ᵣ⁻¹ wkρ eM (subst Value eMeq (value-⋯⁻¹ᶜ τ Vτ aS (subst Value e≡aSτ V)))

    P′ : TP.Proc m
    P′ = TP.ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((TP.⟪ E₁ [ * ]* ⟫ TP.∥ TP.⟪ E₂ [ eM ]* ⟫) TP.∥ P'0)

    srcEq : TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` 0F)) ]* ⟫
               TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` posR) ]* ⟫ TP.∥ Pr))
          ≡ TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              (TP.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((eM ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
               TP.∥ (TP.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` posR) ]* ⟫ TP.∥ (P'0 TP.⋯ₚ wkρ)))
    srcEq = cong₂ (λ SF ST → TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (SF TP.∥ ST))
              (cong₂ (λ Xf Xm → TP.⟪ Xf [ K `send ·¹ (Xm ⊗ (` 0F)) ]* ⟫) Eeq₁ eMeq)
              (cong₂ (λ Yf YP → TP.⟪ Yf [ K `recv ·¹ (` posR) ]* ⟫ TP.∥ YP) Eeq₂ Peq)

    reshaped : Γ ; g ⊢ₚ
        TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((TP.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((eM ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
            TP.∥ TP.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` posR) ]* ⟫)
            TP.∥ (P'0 TP.⋯ₚ wkρ))
    reshaped = Γ-S / subst (λ Z → Γ ; g ⊢ₚ Z) srcEq ⊢P ⊢-≋ (TP.ν-cong TP.∥-assoc)

    b₁≥1 = com-head≥1 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = eM} {E₁ = E₁} {E₂ = E₂} {P = P'0} VeM reshaped
    b₂≥1 = com-head≥2 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = eM} {E₁ = E₁} {E₂ = E₂} {P = P'0} VeM reshaped
    ϕ₁ : ϕ[ b₁ ] ≡ ϕ[ suc b₁ ]
    ϕ₁ = subst (λ z → ϕ[ z ] ≡ ϕ[ suc z ]) (sym (proj₂ b₁≥1)) refl
    ϕ₂ : ϕ[ b₂ ] ≡ ϕ[ suc b₂ ]
    ϕ₂ = subst (λ z → ϕ[ z ] ≡ ϕ[ suc z ]) (sym (proj₂ b₂≥1)) refl

    step0 : Star TR._─→ₚ_
              (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
                (TP.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((eM ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                 TP.∥ (TP.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` posR) ]* ⟫ TP.∥ (P'0 TP.⋯ₚ wkρ)))) P′
    step0 = TR.R-Struct (TP.ν-cong TP.∥-assoc)
              (TR.R-Com {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂} {P = P'0} {E₁ = E₁} {E₂ = E₂} VeM)
              ε ◅ ε

    step : Star TR._─→ₚ_
             (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
               (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` 0F)) ]* ⟫
                TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` posR) ]* ⟫ TP.∥ Pr))) P′
    step = subst (λ Z → Star TR._─→ₚ_ Z P′) (sym srcEq) step0

    eqF₁ : F₁ ≡ frame*-⋯ (E₁ ⋯ᶠ* wkρ) τ Vτ
    eqF₁ = FeqS ■ cong (λ X → frame*-⋯ X τ Vτ) Eeq₁
    eqF₂ : F₂ ≡ frame*-⋯ (E₂ ⋯ᶠ* wkρ) τ Vτ
    eqF₂ = FeqR ■ cong (λ X → frame*-⋯ X τ Vτ) Eeq₂
    eqE : e ≡ (eM ⋯ wkρ) ⋯ τ
    eqE = e≡aSτ ■ cong (_⋯ τ) eMeq
    eqP₁ : P₁ ≡ U[ P'0 TP.⋯ₚ wkρ ] τ
    eqP₁ = Preq ■ cong (λ p → U[ p ] τ) Peq

    align : UP.ν (UR.plugΦ Φrest (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁)))
          ≡ UP.ν (UR.plugΦ Φrest
              ( UP.⟪ frame*-⋯ (E₁ ⋯ᶠ* wkρ) τ Vτ [ * ]* ⟫
                UP.∥ ( UP.⟪ frame*-⋯ (E₂ ⋯ᶠ* wkρ) τ Vτ [ ((eM ⋯ wkρ) ⋯ τ) ]* ⟫
                UP.∥ U[ P'0 TP.⋯ₚ wkρ ] τ ) ))
    align = cong (λ Z → UP.ν (UR.plugΦ Φrest Z))
              (cong₂ UP._∥_
                (cong (λ F → UP.⟪ F [ * ]* ⟫) eqF₁)
                (cong₂ UP._∥_
                  (cong₂ (λ F mm → UP.⟪ F [ mm ]* ⟫) eqF₂ eqE)
                  eqP₁))

    back = CR.com-back σ Vσ b₁ b₂ B₁ B₂ ϕ₁ ϕ₂ E₁ E₂ eM P'0

    result : Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_ (TP.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` 0F)) ]* ⟫
           TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UR.plugΦ (CR.Φrest σ Vσ b₁ b₂ B₁ B₂)
            (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁))) ≈ U[ P′ ] σ )
    result = P′ , step , ≋⇒≈ (≡→≋ align ◅◅ back)
