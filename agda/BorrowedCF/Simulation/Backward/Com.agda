-- | Backward simulation, RU-Com.  Reflects one untyped send/recv rendezvous
--   back to a typed R-Com step in the CLEAN single-step codomain.  Ported from
--   BorrowedCF.Simulation.Support.RevCom (com-go): the ⊎ cleanup slot of the old codomain
--   collapsed to a bare  Q ≈ U[ P′ ] σ; the consumed com handles are front-forced
--   (z≡0F / w≡0F) via the before-ordering/confinement theory (¬ Mobile handles
--   through ¬mobile-block-at), the residual frames/message/rest are strengthened
--   through the R-Com weakening wkₚ (from FinKits, re-exported via Base), and the
--   two consumed handle slots collapse invisibly under the leaf substitution.
--   Interface mirrors Backward.LSplit / Backward.Choice; wired at Backward.agda
--   like bwd-fork by  com-reflect σ Vσ Γ-S ⊢P V (sym eq).
module BorrowedCF.Simulation.Backward.Com where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; νσ-VSub; close-arg-var; head⊗′; ⟨⟩≄⊗;
         inv-U-ν-∥-shape; U-ν-singleton; inv-ν-chanCx; ν-inj; frameApp-reflect)
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋; U-⋯ₚ; U-cong)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2 using (F-⋯f*-fuse; frame*-cong; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.Support.Strengthen
  using (Inverter*; strengthen-Tm-gen*; strengthen-Proc-gen*; ↑*-↑ˡ; ↑*-↑ʳ)
open import BorrowedCF.Simulation.Support.ReverseConfine using (strengthen-frame*; count-handle-comᴸ)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-comᴿ; before-com-binderᴿ)
open import BorrowedCF.Simulation.Support.RevGrindA
  using (com-¬before; choice-¬before; barevar-arg-count; invApp-arg)
open import BorrowedCF.Simulation.Support.RevComConfine
  using (frames-𝕀; com-xS-min; before-com-binderᴸ; ¬mobile-block-at; count-plug-add)
open import BorrowedCF.Simulation.Support.RevComImage using (com-image-block1; recv-image-block2; pos⇒suc)
open import BorrowedCF.Simulation.Support.InvFrame as IF using (inv-app; arg-type)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before; count-≼-eq)
open import BorrowedCF.Simulation.Support.Confine
  using (count; ≼⇒count≤; count-self; count-join-Dir; count-join-PS; count0⇒∉dom; +≡0)
open import BorrowedCF.Simulation.Support.Theorems.Com using (fn-send-dom)
open import BorrowedCF.Types using (new-dual; unr⇒mobile)
open import BorrowedCF.Context using (join; biasedDir; _∶_≼_; _⸴*_)
import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Sum using ([_,_]′)
import Data.Sum as Sum
open TP using (BindGroup; structBinder)

open Fin.Patterns

------------------------------------------------------------------------
-- wkₚ image forms.  wkₚ a c : a + c + k →ᵣ suc a + suc c + k inserts the two
-- consumed com handles: slot 0 (send) and slot (suc a) (recv).  On the three
-- regions of the source scope it acts as a constructor-form shift.
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

------------------------------------------------------------------------
-- νσ collapses through the R-Com weakening: both consumed handle slots map
-- to the SAME constant chanTriple as their block-mates, so inserting them is
-- invisible to the leaf substitution.
------------------------------------------------------------------------

private
  Ub-star-const : ∀ b {N} (c : 𝔽 N) (x : 𝔽 b) →
                  Ub[ b ] (* , c , *) x ≡ ((* ⊗ (` c)) ⊗ *)
  Ub-star-const (suc zero)    c 0F      = refl
  Ub-star-const (suc (suc b)) c 0F      = refl
  Ub-star-const (suc (suc b)) c (suc x) = Ub-star-const (suc b) c x

com-νσ-wk : ∀ {m n} (b₁ b₂ : ℕ) (σ : m →ₛ n) (i : 𝔽 ((b₁ + 0) + (b₂ + 0) + m)) →
  νσ (suc b₁) (suc b₂) σ (wkₚ {n = m} (b₁ + 0) (b₂ + 0) i) ≡ νσ b₁ b₂ σ i
com-νσ-wk {m} {n} b₁ b₂ σ i with Fin.splitAt (b₁ + 0 + (b₂ + 0)) i in seq
... | Sum.inj₂ u =
    cong (νσ (suc b₁) (suc b₂) σ)
      (cong (wkₚ (b₁ + 0) (b₂ + 0)) ieq ■ wkₚ-C (b₁ + 0) (b₂ + 0) u)
  ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁ + 0 + (suc b₂ + 0)) m u)
  where
    ieq : i ≡ (b₁ + 0 + (b₂ + 0)) ↑ʳ u
    ieq = sym (Fin.join-splitAt (b₁ + 0 + (b₂ + 0)) m i)
        ■ cong (Fin.join (b₁ + 0 + (b₂ + 0)) m) seq
... | Sum.inj₁ d with Fin.splitAt (b₁ + 0) d in seqd
...   | Sum.inj₁ v =
    cong (νσ (suc b₁) (suc b₂) σ)
      (cong (wkₚ (b₁ + 0) (b₂ + 0)) ieq ■ wkₚ-A (b₁ + 0) (b₂ + 0) v)
  ■ cong [ _ , _ ]′
      (Fin.splitAt-↑ˡ (suc b₁ + 0 + (suc b₂ + 0)) (Fin.suc v ↑ˡ (suc b₂ + 0)) m)
  ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁ + 0) (Fin.suc v) (suc b₂ + 0))
  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) (Ub-star-const (suc b₁ + 0) 0F (Fin.suc v))
  ■ sym (cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) (Ub-star-const (b₁ + 0) 0F v))
  where
    ieq : i ≡ (v ↑ˡ (b₂ + 0)) ↑ˡ m
    ieq = sym (Fin.join-splitAt (b₁ + 0 + (b₂ + 0)) m i)
        ■ cong (Fin.join (b₁ + 0 + (b₂ + 0)) m) seq
        ■ cong (_↑ˡ m)
            ( sym (Fin.join-splitAt (b₁ + 0) (b₂ + 0) d)
            ■ cong (Fin.join (b₁ + 0) (b₂ + 0)) seqd )
...   | Sum.inj₂ w =
    cong (νσ (suc b₁) (suc b₂) σ)
      (cong (wkₚ (b₁ + 0) (b₂ + 0)) ieq ■ wkₚ-B (b₁ + 0) (b₂ + 0) w)
  ■ cong [ _ , _ ]′
      (Fin.splitAt-↑ˡ (suc b₁ + 0 + (suc b₂ + 0)) ((suc (b₁ + 0)) ↑ʳ Fin.suc w) m)
  ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁ + 0) (suc b₂ + 0) (Fin.suc w))
  ■ Ub-star-const (suc b₂ + 0) (weaken* ⦃ Kᵣ ⦄ 0 1F) (Fin.suc w)
  ■ sym (Ub-star-const (b₂ + 0) (weaken* ⦃ Kᵣ ⦄ 0 1F) w)
  where
    ieq : i ≡ ((b₁ + 0) ↑ʳ w) ↑ˡ m
    ieq = sym (Fin.join-splitAt (b₁ + 0 + (b₂ + 0)) m i)
        ■ cong (Fin.join (b₁ + 0 + (b₂ + 0)) m) seq
        ■ cong (_↑ˡ m)
            ( sym (Fin.join-splitAt (b₁ + 0) (b₂ + 0) d)
            ■ cong (Fin.join (b₁ + 0) (b₂ + 0)) seqd )

------------------------------------------------------------------------
-- Inverter for wkₚ, missing exactly the two consumed com handles.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Value reflection through a renaming / value substitution.
------------------------------------------------------------------------

value-⋯ᵣ⁻¹ : ∀ {k N} (ρ : k →ᵣ N) (e₀ : Tm k) → Value (e₀ ⋯ ρ) → Value e₀
value-⋯ᵣ⁻¹ ρ (` x)      V           = V-`
value-⋯ᵣ⁻¹ ρ (K c)      V           = V-K
value-⋯ᵣ⁻¹ ρ (ƛ e)    V           = V-λ
value-⋯ᵣ⁻¹ ρ (e₁ ⊗ e₂)  (V-⊗ V₁ V₂) = V-⊗ (value-⋯ᵣ⁻¹ ρ e₁ V₁) (value-⋯ᵣ⁻¹ ρ e₂ V₂)
value-⋯ᵣ⁻¹ ρ (`inj i e) (V-⊕ V)     = V-⊕ (value-⋯ᵣ⁻¹ ρ e V)

value-⋯⁻¹ᶜ : ∀ {k N} (σ : k →ₛ N) → VSub σ → (e₀ : Tm k) → Value (e₀ ⋯ σ) → Value e₀
value-⋯⁻¹ᶜ σ Vσ (` x)      V           = V-`
value-⋯⁻¹ᶜ σ Vσ (K c)      V           = V-K
value-⋯⁻¹ᶜ σ Vσ (ƛ e)    V           = V-λ
value-⋯⁻¹ᶜ σ Vσ (e₁ ⊗ e₂)  (V-⊗ V₁ V₂) = V-⊗ (value-⋯⁻¹ᶜ σ Vσ e₁ V₁) (value-⋯⁻¹ᶜ σ Vσ e₂ V₂)
value-⋯⁻¹ᶜ σ Vσ (`inj i e) (V-⊕ V)     = V-⊕ (value-⋯⁻¹ᶜ σ Vσ e V)

------------------------------------------------------------------------
-- send-side typing extractors.
------------------------------------------------------------------------

pair-decomp : ∀ {N} {Γ : Ctx N} {β : Struct N} {e₁ e₂ : Tm N} {T ϵ}
  → Γ ; β ⊢ (e₁ ⊗ e₂) ∶ T ∣ ϵ
  → Σ[ Te ∈ 𝕋 ] Σ[ d ∈ Dir ] Σ[ Tx ∈ 𝕋 ] Σ[ α₂ ∈ Struct N ] Σ[ ϵ₂ ∈ Eff ]
      (T ≃ (Te ⊗⟨ d ⟩ Tx)) × (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂)
pair-decomp (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  _ , biasedDir p/s , _ , γ₂ , _ , ≃-refl , ⊢e₂
pair-decomp (T-Conv T≃ _ d) =
  let Te , dd , Tx , α₂ , ϵ₂ , Teq , ⊢e₂ = pair-decomp d
  in Te , dd , Tx , α₂ , ϵ₂ , ≃-trans (≃-sym T≃) Teq , ⊢e₂
pair-decomp (T-Weaken _ d) = pair-decomp d

sad-core : ∀ {N} {Γ : Ctx N} {α β : Struct N} {e₁ e₂ : Tm N} {Targ a Uu ϵ₁ ϵ₂}
  → Γ ; α ⊢ K `send ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ (e₁ ⊗ e₂) ∶ Targ ∣ ϵ₂
  → Σ[ Tᵐ ∈ 𝕋 ] Σ[ α₂ ∈ Struct N ] Σ[ Tx ∈ 𝕋 ] Σ[ ϵ₂′ ∈ Eff ]
      (⟨ msg ‼ Tᵐ ⟩ ≃ Tx) × (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂′)
sad-core ⊢fn ⊢arg with fn-send-dom ⊢fn | pair-decomp ⊢arg
... | Tᵐ , domeq | Te , d , Tx , α₂ , ϵ₂ , T≃ , ⊢e₂ with ≃-trans domeq T≃
...   | (_ ⊗ eq) = Tᵐ , α₂ , Tx , ϵ₂ , eq , ⊢e₂

send-arg-decomp : ∀ {N} {Γ : Ctx N} {β : Struct N} {e₁ e₂ : Tm N} {Uu ϵ}
  → Γ ; β ⊢ K `send ·¹ (e₁ ⊗ e₂) ∶ Uu ∣ ϵ
  → Σ[ Tᵐ ∈ 𝕋 ] Σ[ α₂ ∈ Struct N ] Σ[ Tx ∈ 𝕋 ] Σ[ ϵ₂′ ∈ Eff ]
      (⟨ msg ‼ Tᵐ ⟩ ≃ Tx) × (Γ ; α₂ ⊢ e₂ ∶ Tx ∣ ϵ₂′)
send-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = sad-core ⊢fn ⊢arg
send-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = sad-core ⊢fn ⊢arg
send-arg-decomp (T-Conv _ _ d) = send-arg-decomp d
send-arg-decomp (T-Weaken _ d) = send-arg-decomp d

sv-core : ∀ {N} {Γ : Ctx N} {α β : Struct N} {x : 𝔽 N} {Targ a Uu ϵ₁ ϵ₂} {s : 𝕊 0}
  → Γ ; α ⊢ K `send ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ (` x) ∶ Targ ∣ ϵ₂ → Γ x ≡ ⟨ s ⟩ → ⊥
sv-core ⊢fn ⊢arg eq with fn-send-dom ⊢fn
... | Tᵐ , domeq =
  ⟨⟩≄⊗ (≃-trans (subst (_≃ _) eq (arg-type ⊢arg)) (≃-sym domeq))

send-var-⊥ : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {Uu ϵ} {s : 𝕊 0}
  → Γ ; β ⊢ K `send ·¹ (` x) ∶ Uu ∣ ϵ → Γ x ≡ ⟨ s ⟩ → ⊥
send-var-⊥ (T-AppUnr _ _ ⊢fn ⊢arg) eq = sv-core ⊢fn ⊢arg eq
send-var-⊥ (T-AppLin _ _ ⊢fn ⊢arg) eq = sv-core ⊢fn ⊢arg eq
send-var-⊥ (T-Conv _ _ d) eq = send-var-⊥ d eq
send-var-⊥ (T-Weaken _ d) eq = send-var-⊥ d eq

𝕀≤⇒≡ : ∀ {ϵ} → 𝕀 ≤ϵ ϵ → ϵ ≡ 𝕀
𝕀≤⇒≡ 𝕀≤𝕀 = refl

send-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu a ϵ}
  → Γ ; α ⊢ K `send ∶ T ⟨ a ⟩→ Uu ∣ ϵ → Arr.eff a ≡ 𝕀
send-fn-eff-𝕀 (T-Const (`send _)) = refl
send-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = send-fn-eff-𝕀 d
send-fn-eff-𝕀 (T-Weaken _ d) = send-fn-eff-𝕀 d

send-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `send ·¹ arg ∶ Uu ∣ ϵ → ϵ ≡ 𝕀
send-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡ (subst (_≤ϵ _) (send-fn-eff-𝕀 ⊢fn) ≤ₐ)
send-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡ (subst (_≤ϵ _) (send-fn-eff-𝕀 ⊢fn) ≤ₐ)
send-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡ (subst (_≤ϵ _) (send-app-𝕀 d) ≤)
send-app-𝕀 (T-Weaken _ d) = send-app-𝕀 d

send-arg-count-chain : ∀ {N} {Γ : Ctx N} {γ : Struct N} {aS : Tm N} {x : 𝔽 N}
  {a} {α β : Struct N} {T ϵ}
  → ¬ Unr (Γ x) → Γ ∶ join (Arr.dir a) β α ≼ γ → Γ ; β ⊢ (aS ⊗ (` x)) ∶ T ∣ ϵ → 1 Nat.≤ count x γ
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
  → ¬ Unr (Γ x) → Γ ; γ ⊢ K `send ·¹ (aS ⊗ (` x)) ∶ Uu ∣ ϵ → 1 Nat.≤ count x γ
send-arg-count ¬u ⊢redex
  with aa , _ , _ , _ , join≼ , _ , _ , invapp ← inv-· ⊢redex =
  send-arg-count-chain {a = aa} ¬u join≼ (proj₂ (invApp-arg invapp))

------------------------------------------------------------------------
-- recv-side typing extractors.
------------------------------------------------------------------------

fn-recv-dom : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu a ϵ}
  → Γ ; α ⊢ K `recv ∶ T ⟨ a ⟩→ Uu ∣ ϵ
  → Σ[ Tᵐ ∈ 𝕋 ] (⟨ msg ⁇ Tᵐ ⟩ ≃ T)
fn-recv-dom (T-Const (`recv _)) = _ , ≃-refl
fn-recv-dom (T-Conv (dom≃ `→ _) _ d) = let Tᵐ , eq = fn-recv-dom d in Tᵐ , ≃-trans eq dom≃
fn-recv-dom (T-Weaken _ d) = fn-recv-dom d

rad-core : ∀ {N} {Γ : Ctx N} {α β : Struct N} {arg : Tm N} {Targ Uu ϵ₁ ϵ₂ a}
  → Γ ; α ⊢ K `recv ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ arg ∶ Targ ∣ ϵ₂
  → Σ[ Tᵐ ∈ 𝕋 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ msg ⁇ Tᵐ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
rad-core {β = β} ⊢fn ⊢arg with fn-recv-dom ⊢fn
... | Tᵐ , domeq = Tᵐ , β , _ , _ , domeq , ⊢arg

recv-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `recv ·¹ arg ∶ Uu ∣ ϵ
  → Σ[ Tᵐ ∈ 𝕋 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ msg ⁇ Tᵐ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
recv-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = rad-core ⊢fn ⊢arg
recv-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = rad-core ⊢fn ⊢arg
recv-arg-decomp (T-Conv _ _ d) = recv-arg-decomp d
recv-arg-decomp (T-Weaken _ d) = recv-arg-decomp d

recv-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu a ϵ}
  → Γ ; α ⊢ K `recv ∶ T ⟨ a ⟩→ Uu ∣ ϵ → Arr.eff a ≡ 𝕀
recv-fn-eff-𝕀 (T-Const (`recv _)) = refl
recv-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = recv-fn-eff-𝕀 d
recv-fn-eff-𝕀 (T-Weaken _ d) = recv-fn-eff-𝕀 d

recv-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `recv ·¹ arg ∶ Uu ∣ ϵ → ϵ ≡ 𝕀
recv-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡ (subst (_≤ϵ _) (recv-fn-eff-𝕀 ⊢fn) ≤ₐ)
recv-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡ (subst (_≤ϵ _) (recv-fn-eff-𝕀 ⊢fn) ≤ₐ)
recv-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡ (subst (_≤ϵ _) (recv-app-𝕀 d) ≤)
recv-app-𝕀 (T-Weaken _ d) = recv-app-𝕀 d

------------------------------------------------------------------------
-- com-go : the reverse RU-Com engine at a strict image.
------------------------------------------------------------------------

com-go :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (b₁ b₂ : ℕ)
    {F₀ˢ F₀ᴿ : Frame* (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {argˢ argᴿ : Tm (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {Pr : TP.Proc (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)}
    {F₁ F₂ : Frame* (2 + n)} {e e₁ e₁′ e₂ e₂′ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
    (V : Value e)
  → Γ ; g ⊢ₚ TP.ν (b₁ ∷ []) (b₂ ∷ [])
       (TP.⟪ F₀ˢ [ K `send ·¹ argˢ ]* ⟫ TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ argᴿ ]* ⟫ TP.∥ Pr))
  → F₁ ≡ frame*-⋯ F₀ˢ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → (e ⊗ ((e₁ ⊗ (` 0F)) ⊗ e₁′)) ≡ argˢ ⋯ νσ b₁ b₂ σ
  → F₂ ≡ frame*-⋯ F₀ᴿ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
  → ((e₂ ⊗ (` 1F)) ⊗ e₂′) ≡ argᴿ ⋯ νσ b₁ b₂ σ
  → P₁ ≡ U[ Pr ] (νσ b₁ b₂ σ)
  → Σ[ P′ ∈ TP.Proc m ]
      ( Star TR._─→ₚ_
          (TP.ν (b₁ ∷ []) (b₂ ∷ [])
            (TP.⟪ F₀ˢ [ K `send ·¹ argˢ ]* ⟫ TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ argᴿ ]* ⟫ TP.∥ Pr))) P′ )
      × ( UP.ν (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁)) ≈ U[ P′ ] σ )
com-go {m} {n} σ Vσ {Γ} Γ-S {g} b₁ b₂ {F₀ˢ} {F₀ᴿ} {argˢ} {argᴿ} {Pr}
       {F₁} {F₂} {e} {e₁} {e₁′} {e₂} {e₂′} {P₁} V ⊢P FeqS argeqS FeqR argeqR Preq
  with Γ₁ , Γ₂ , s' , p' , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with αS , βrest , ≼₁ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with αR , βP , ≼₂ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with 𝒫ˢ , γrˢ , _ , _ , _ , _ , ≼ˢ , _ , _ , ⊢Fˢ , ⊢redexˢ
       ← ⊢[]*⁻¹ F₀ˢ (K `send ·¹ argˢ) (inv-⟪⟫ ⊢PS)
  with head⊗′ (νσ b₁ b₂ σ) argˢ (sym argeqS)
... | Sum.inj₁ (x , refl) = ⊥-elim (send-var-⊥ ⊢redexˢ (proj₂ (Γ′-S x)))
... | Sum.inj₂ (aS , cS , refl , aSeq , cSeq)
  with Tᵐ , α₂ , Tx , ϵ₂′ , msg≃Tx , ⊢cS ← send-arg-decomp ⊢redexˢ
  with xS , refl ← close-arg-var cS ⊢cS msg≃Tx (νσ b₁ b₂ σ) (sym cSeq)
  with refl ← send-app-𝕀 ⊢redexˢ
  with refl , lpˢ ← frames-𝕀 ⊢Fˢ
  with z , 1≤b₁ , refl ← com-image-block1 b₁ b₂ σ Vσ xS cSeq
  with b₁' , refl ← pos⇒suc 1≤b₁
  with 𝒫ᴿ , γrᴿ , _ , _ , _ , _ , ≼ᴿ , _ , _ , ⊢Fᴿ , ⊢redexᴿ
       ← ⊢[]*⁻¹ F₀ᴿ (K `recv ·¹ argᴿ) (inv-⟪⟫ ⊢PR)
  with Tᵐʳ , βrr , Txʳ , ϵrr , msg⁇≃ , ⊢argᴿty ← recv-arg-decomp ⊢redexᴿ
  with xR , refl ← close-arg-var argᴿ ⊢argᴿty msg⁇≃ (νσ (suc b₁') b₂ σ) (sym argeqR)
  with refl ← recv-app-𝕀 ⊢redexᴿ
  with refl , lpᴿ ← frames-𝕀 ⊢Fᴿ
  with w , 1≤b₂ , refl ← recv-image-block2 (suc b₁') b₂ σ Vσ xR argeqR
  with b₂' , refl ← pos⇒suc 1≤b₂
  = finish z≡0F w≡0F
  where
    Sb : Struct (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ []) + m)
    Sb = (structBinder (suc b₁' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (suc b₂' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (structBinder (suc b₂' ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (suc b₁' ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ [])))

    lookupL-z : ((Γ₁ ⸴* Γ₂) ⸴* Γ) ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m) ≡ Γ₁ z
    lookupL-z = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) (z ↑ˡ (suc b₂' + 0)) m)
              ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0) z (suc b₂' + 0))
    ¬u0 = ¬mobile-block-at Nnew C 0F refl

    ¬uxS = ¬mobile-block-at Nnew C z lookupL-z
    1≤c  = send-arg-count (¬uxS ∘ unr⇒mobile) ⊢redexˢ
    cnt1 = count-handle-comᴸ (suc b₁') (suc b₂') g z
    z₀   = Fin.cast (+-identityʳ (suc b₁')) z
    z₀↑0≡z : z₀ ↑ˡ 0 ≡ z
    z₀↑0≡z = toℕ-injective (toℕ-↑ˡ z₀ 0 ■ toℕ-cast (+-identityʳ (suc b₁')) z)
    contra : Fin.toℕ z₀ ≢ 0 → ⊥
    contra ne = com-xS-min ¬uxS ¬u0 lpˢ ≼ˢ ≼₁ cnt1
                  (subst (λ zz → before 0F ((zz ↑ˡ (suc b₂' + 0)) ↑ˡ m) Sb) z₀↑0≡z
                    (before-com-binderᴸ b₁' (suc b₂') g z₀ ne))
                  1≤c (com-¬before {𝒫ˢ = 𝒫ˢ} ¬uxS ¬u0 ⊢redexˢ ≼ˢ ≼₁ cnt1)
    z≡0F : z ≡ 0F
    z≡0F with Fin.toℕ z₀ Nat.≟ 0
    ... | yes e0 = toℕ-injective (sym (toℕ-cast (+-identityʳ (suc b₁')) z) ■ e0)
    ... | no  ne = ⊥-elim (contra ne)

    posR : 𝔽 (sum (suc b₁' ∷ []) + sum (suc b₂' ∷ []) + m)
    posR = ((suc b₁' + 0) ↑ʳ (Fin.zero {b₂' + 0})) ↑ˡ m
    lookupR : ((Γ₁ ⸴* Γ₂) ⸴* Γ) posR ≡ Γ₂ 0F
    lookupR = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) ((suc b₁' + 0) ↑ʳ (Fin.zero {b₂' + 0})) m)
            ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁' + 0) (suc b₂' + 0) (Fin.zero {b₂' + 0}))
    lookupL-w : ((Γ₁ ⸴* Γ₂) ⸴* Γ) (((suc b₁' + 0) ↑ʳ w) ↑ˡ m) ≡ Γ₂ w
    lookupL-w = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (suc b₁' + 0 + (suc b₂' + 0)) ((suc b₁' + 0) ↑ʳ w) m)
              ■ cong [ _ , _ ]′ (Fin.splitAt-↑ʳ (suc b₁' + 0) (suc b₂' + 0) w)
    ¬uxR = ¬mobile-block-at (new-dual Nnew) C′ w lookupL-w
    ¬uyR = ¬mobile-block-at (new-dual Nnew) C′ 0F lookupR
    1≤cᴿ = barevar-arg-count (¬uxR ∘ unr⇒mobile) ⊢redexᴿ
    cnt1ᴿ = count-handle-comᴿ (suc b₁') (suc b₂') g w
    w₀   = Fin.cast (+-identityʳ (suc b₂')) w
    w₀↑0≡w : w₀ ↑ˡ 0 ≡ w
    w₀↑0≡w = toℕ-injective (toℕ-↑ˡ w₀ 0 ■ toℕ-cast (+-identityʳ (suc b₂')) w)
    combined≼ =
      𝐂.≼-trans (𝐂.≼-refl (𝐂.≈-trans (𝐂.≈-sym 𝐂.∥-assoc) 𝐂.∥-comm))
        (𝐂.≼-trans (𝐂.≼-cong-∥ (𝐂.≼-refl 𝐂.≈-refl) ≼₂) ≼₁)
    contraᴿ : Fin.toℕ w₀ ≢ 0 → ⊥
    contraᴿ ne = com-xS-min ¬uxR ¬uyR lpᴿ ≼ᴿ combined≼ cnt1ᴿ
                   (subst (λ ww → before posR (((suc b₁' + 0) ↑ʳ ww) ↑ˡ m) Sb) w₀↑0≡w
                     (before-com-binderᴿ (suc b₁') b₂' g w₀ ne))
                   1≤cᴿ (choice-¬before ¬uxR ¬uyR ⊢redexᴿ)
    w≡0F : w ≡ 0F
    w≡0F with Fin.toℕ w₀ Nat.≟ 0
    ... | yes e0 = toℕ-injective (sym (toℕ-cast (+-identityʳ (suc b₂')) w) ■ e0)
    ... | no  ne = ⊥-elim (contraᴿ ne)

    finish : z ≡ 0F → w ≡ 0F →
      Σ[ P′ ∈ TP.Proc m ]
        ( Star TR._─→ₚ_
            (TP.ν (suc b₁' ∷ []) (suc b₂' ∷ [])
              (TP.⟪ F₀ˢ [ K `send ·¹ (aS ⊗ (` ((z ↑ˡ (suc b₂' + 0)) ↑ˡ m))) ]* ⟫
               TP.∥ (TP.⟪ F₀ᴿ [ K `recv ·¹ (` (((suc b₁' + 0) ↑ʳ w) ↑ˡ m)) ]* ⟫ TP.∥ Pr))) P′ )
        × ( UP.ν (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁)) ≈ U[ P′ ] σ )
    finish refl refl =
      let
        a = b₁' + 0
        c = b₂' + 0
        wkρ = wkₚ {n = m} a c
        HH = Hcom a c m
        invρ = inv-wkₚ a c m
        νσ0 = νσ (suc b₁') (suc b₂') σ
        Vνσ0 = νσ-VSub (suc b₁') (suc b₂') σ Vσ
        νσ1 = νσ b₁' b₂' σ
        Vνσ1 = νσ-VSub b₁' b₂' σ Vσ
        ¬u0ᵁ  = ¬u0  ∘ unr⇒mobile
        ¬uyRᵁ = ¬uyR ∘ unr⇒mobile
        c0γ = count-handle-comᴸ (suc b₁') (suc b₂') g 0F
        cRγ = count-handle-comᴿ (suc b₁') (suc b₂') g 0F
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
        βpS , (TS₀ , ϵS₀ , ⊢plugS) , supS , facS = strengthen-frame* F₀ˢ (inv-⟪⟫ ⊢PS) HH
        1≤βpS0 = send-arg-count ¬u0ᵁ ⊢plugS
        hypS = λ { h (Sum.inj₁ refl) → ¬u0ᵁ , Nat.≤-trans cαS0≤1 1≤βpS0
                 ; h (Sum.inj₂ refl) → ¬uyRᵁ , subst (Nat._≤ count posR βpS) (sym cαSR) Nat.z≤n }
        E₁ , Eeq₁ = facS hypS wkρ invρ
        βpR , (TR₀ , ϵR₀ , ⊢plugR) , supR , facR = strengthen-frame* F₀ᴿ (inv-⟪⟫ ⊢PR) HH
        1≤βpRR = barevar-arg-count ¬uyRᵁ ⊢plugR
        hypR = λ { h (Sum.inj₁ refl) → ¬u0ᵁ , subst (Nat._≤ count 0F βpR) (sym cαR0) Nat.z≤n
                 ; h (Sum.inj₂ refl) → ¬uyRᵁ , Nat.≤-trans cαRR≤1 1≤βpRR }
        E₂ , Eeq₂ = facR hypR wkρ invρ
        αfn , αarg , _fnT , (Tp , ϵp , ⊢pairS) , cleS = inv-app ⊢plugS
        p/s , αaS , βc0 , T₁ , T₂ , ϵa , ϵb , join≼pr , _ , _ , _ , ⊢aSty , ⊢c0ty = inv-⊗ ⊢pairS
        βpS0≤1 = Nat.≤-trans (supS 0F ¬u0ᵁ) cαS0≤1
        1≤βc0 : 1 Nat.≤ count 0F βc0
        1≤βc0 = subst (Nat._≤ count 0F βc0) (count-self (Fin.zero {b₁' + 0 + suc (b₂' + 0) + m})) (≼⇒count≤ ¬u0ᵁ (proj₂ (inv-` ⊢c0ty)))
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
        H∉aS = λ { h (Sum.inj₁ refl) → count0⇒∉dom αaS cαaS0 ; h (Sum.inj₂ refl) → count0⇒∉dom αaS cαaSR }
        eM , eMeq = strengthen-Tm-gen* ⊢aSty wkρ HH invρ H∉aS
        H∉P = λ { h (Sum.inj₁ refl) → count0⇒∉dom βP cβP0 ; h (Sum.inj₂ refl) → count0⇒∉dom βP cβPR }
        P'0 , Peq = strengthen-Proc-gen* ⊢Pr wkρ HH invρ H∉P
        VeM = value-⋯ᵣ⁻¹ wkρ eM (subst Value eMeq (value-⋯⁻¹ᶜ νσ0 Vνσ0 aS (subst Value aSeq V)))
        P′ = TP.ν (b₁' ∷ []) (b₂' ∷ []) (TP.⟪ E₁ [ * ]* ⟫ TP.∥ (TP.⟪ E₂ [ eM ]* ⟫ TP.∥ P'0))
        srcEq = cong₂ (λ SF ST → TP.ν (suc b₁' ∷ []) (suc b₂' ∷ []) (SF TP.∥ ST))
                  (cong₂ (λ Xf Xm → TP.⟪ Xf [ K `send ·¹ (Xm ⊗ (` 0F)) ]* ⟫) Eeq₁ eMeq)
                  (cong₂ (λ Yf YP → TP.⟪ Yf [ K `recv ·¹ (` (Fin.suc ((b₁' + 0 ↑ʳ 0F) ↑ˡ m))) ]* ⟫ TP.∥ YP) Eeq₂ Peq)
        step0 = TR.R-Struct (TP.ν-cong TP.∥-assoc)
                  (TR.R-Com {b₁ = b₁'} {B₁ = []} {b₂ = b₂'} {B₂ = []} {P = P'0} {E₁ = E₁} {E₂ = E₂} VeM)
                  (TP.ν-cong (Eq*.symmetric TP._≋′_ TP.∥-assoc)) ◅ ε
        step = subst (λ Z → Star TR._─→ₚ_ Z P′) (sym srcEq) step0
        fchain₁ = FeqS ■ cong (λ X → frame*-⋯ X νσ0 Vνσ0) Eeq₁
                ■ F-⋯f*-fuse E₁ {ρ = wkρ} {τ = νσ0} Vνσ0 (·ₖ-VSubᵣ wkρ Vνσ0)
                ■ frame*-cong E₁ (·ₖ-VSubᵣ wkρ Vνσ0) Vνσ1 (com-νσ-wk b₁' b₂' σ)
        fchain₂ = FeqR ■ cong (λ X → frame*-⋯ X νσ0 Vνσ0) Eeq₂
                ■ F-⋯f*-fuse E₂ {ρ = wkρ} {τ = νσ0} Vνσ0 (·ₖ-VSubᵣ wkρ Vνσ0)
                ■ frame*-cong E₂ (·ₖ-VSubᵣ wkρ Vνσ0) Vνσ1 (com-νσ-wk b₁' b₂' σ)
        e-eq = aSeq ■ cong (_⋯ νσ0) eMeq ■ fusion eM wkρ νσ0 ■ ⋯-cong eM (com-νσ-wk b₁' b₂' σ)
        restEq = Preq ■ cong (λ p → U[ p ] νσ0) Peq ■ U-⋯ₚ P'0 ■ U-cong P'0 (com-νσ-wk b₁' b₂' σ)
        thread₁ = cong UP.⟪_⟫ (cong (_[ * ]*) fchain₁ ■ sym (frame-plug* E₁ νσ1 Vνσ1))
        thread₂ = cong UP.⟪_⟫ (cong₂ _[_]* fchain₂ e-eq ■ sym (frame-plug* E₂ νσ1 Vνσ1))
        recon = cong UP.ν (cong₂ UP._∥_ thread₁ (cong₂ UP._∥_ thread₂ restEq))
      in P′ , step , ≋⇒≈ (≡→≋ recon)

------------------------------------------------------------------------
-- The exported reflection.  Interface mirrors Backward.LSplit /
-- Backward.Choice: the untyped redex is presented as its frames F₁/F₂ + the
-- value V of the transmitted message plus the equation  U[ P ] σ ≡ (RU-Com LHS);
-- the result is the (RU-Com RHS) ≈-bridged to U[ P′ ] σ.  Wired at Backward.agda
-- by  com-reflect σ Vσ Γ-S ⊢P V (sym eq).
------------------------------------------------------------------------

com-reflect : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
            → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
            → {e e₁ e₁′ e₂ e₂′ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
              {F₁ F₂ : Frame* (2 + n)} (V : Value e)
            → U[ P ] σ ≡ UP.ν (UP.⟪ F₁ [ K `send ·¹ (e ⊗ ((e₁ ⊗ (` 0F)) ⊗ e₁′)) ]* ⟫
                           UP.∥ (UP.⟪ F₂ [ K `recv ·¹ ((e₂ ⊗ (` 1F)) ⊗ e₂′) ]* ⟫
                           UP.∥ P₁))
            → Σ[ P′ ∈ TP.Proc m ]
                ( Star TR._─→ₚ_ P P′
                × UP.ν (UP.⟪ F₁ [ * ]* ⟫ UP.∥ (UP.⟪ F₂ [ e ]* ⟫ UP.∥ P₁))
                    ≈ U[ P′ ] σ )
com-reflect σ Vσ Γ-S {P = P} ⊢P {F₁ = F₁} {F₂ = F₂} V eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PS , Prest , refl , Seq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with PR , Pr , refl , Req , Preq ← inv-U-∥ Prest (νσ b₁ b₂ σ) (sym Resteq)
  with eS , refl , Seq′ ← inv-U-⟪⟫ PS (νσ b₁ b₂ σ) (sym Seq)
  with eR , refl , Req′ ← inv-U-⟪⟫ PR (νσ b₁ b₂ σ) (sym Req)
  with _ , _ , _ , ⊢PS , ⊢Prest ← inv-∥ ⊢body
  with _ , _ , _ , ⊢PR , ⊢Pr ← inv-∥ ⊢Prest
  with F₀ˢ , argˢ , refl , FeqS , argeqS
       ← frameApp-reflect Γ′-S eS (inv-⟪⟫ ⊢PS) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `send
           F₁ (sym Seq′)
  with F₀ᴿ , argᴿ , refl , FeqR , argeqR
       ← frameApp-reflect Γ′-S eR (inv-⟪⟫ ⊢PR) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) `recv
           F₂ (sym Req′)
  = com-go σ Vσ Γ-S b₁ b₂ V ⊢P FeqS argeqS FeqR argeqR Preq
