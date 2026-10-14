------------------------------------------------------------------------
-- Confinement of the two split redexes, with the injectivity of the
-- thinning made explicit.
--
-- This is `Simulation.Support.SplitConfine.lsplit-confine` /
-- `rsplit-confine` with one extra component: the strengthening renaming
-- ρ⁻ is injective.  `_⊢⋯ᶠ*⁻¹_/_` and `_⊢⋯ₚ⁻¹_/_` need that, and the
-- Simulation version hides ρ⁻ behind an existential, so the fact cannot
-- be recovered after the fact.  Everything else is verbatim.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Confine where
open import BorrowedCF.Terms using (module SplitRenamings)

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Context using (Ctx; Struct)
open 𝐓 using (_;_⊢ₚ_; inv-∥; inv-ν; inv-⟪⟫)
open import BorrowedCF.Simulation.Support.Confine using (count; count-self; count0⇒∉dom; ≼⇒count≤)
open import BorrowedCF.Simulation.Support.InvFrame
  using (strengthen-frame; inv-app; inv-var-count; lsplit-app-nonUnr; rsplit-app-nonUnr)
open import BorrowedCF.Simulation.Support.Strengthen
  using (strengthen-Proc-gen; Inverter; Inverter-cast; skip-cast; inv↑*; inv-weakenᵣ
        ; skip↑*; skip-weakenᵣ; cast-inj)
open import BorrowedCF.Simulation.Support.HandleCount
  using (count-handle-γinnerq; splitN-eqq; mp≡handleq)
open import Data.Nat.ListAction using (sum)
open Nat using (_≤_; ≤-trans; m≤m+n; m≤n+m; +-monoˡ-≤; n≤0⇒n≡0; s≤s⁻¹)

-- `mk-thin` of Simulation.Support.Strengthen, plus injectivity.
mk-thin′ : ∀ {N} p rest (eq : p + suc rest ≡ N)
  → Σ[ ρ⁻ ∈ ((p + rest) →ᵣ N) ]
      Inverter ρ⁻ (Fin.cast eq (p ↑ʳ zero))
    × (∀ y → ρ⁻ y ≢ Fin.cast eq (p ↑ʳ zero))
    × (∀ {x y} → ρ⁻ x ≡ ρ⁻ y → x ≡ y)
mk-thin′ p rest eq =
  (λ y → Fin.cast eq ((weakenᵣ ↑* p) y)) ,
  Inverter-cast eq (inv↑* p inv-weakenᵣ) ,
  skip-cast eq (skip↑* p skip-weakenᵣ) ,
  λ e → ↑*-inj p wk-inj (cast-inj eq e)

lsplit-confine′ : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {B₁ B₂ B : 𝐓.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : 𝐓.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
  Γ ; γ ⊢ₚ 𝐓.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
            (𝐓.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ 𝐓.∥ P) →
  Σ ℕ λ k → Σ (k →ᵣ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) λ ρ⁻ →
    (∀ y → ρ⁻ y ≢ 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F))
    × (∀ {x y} → ρ⁻ x ≡ ρ⁻ y → x ≡ y)
    × Σ (Frame* k) λ E₀ → (E ≡ E₀ ⋯ᶠ* ρ⁻)
        × Σ (𝐓.Proc k) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ ρ⁻
lsplit-confine′ {m = m} Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {E = E} {P = P} ⊢P =
  let
    handle = SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    Γ₁ , Γ₂ , s' , _p , _N , _⊢B₁ , _⊢B₂ , C , C' , ⊢body = inv-ν ⊢P
    α , β , αβ≼ , ⊢thread , ⊢Ppar = inv-∥ ⊢body
    ⊢term = inv-⟪⟫ ⊢thread
    βplug , (_ , _ , ⊢plug) , support , factor = strengthen-frame E ⊢term
    ¬u = lsplit-app-nonUnr ⊢plug
    αfn , αarg , (_ , _ , ⊢fn) , (_ , _ , ⊢arg) , cle-plug = inv-app ⊢plug
    c-αβ≤1 = subst (count handle α + count handle β ≤_) (count-handle-γinnerq B₁ B₂ B q b₁ γ)
                   (≼⇒count≤ {x = handle} ¬u αβ≼)
    1≤αarg = subst (_≤ count handle αarg) (count-self handle) (inv-var-count ⊢arg handle ¬u)
    1≤βplug = ≤-trans 1≤αarg (≤-trans (m≤n+m (count handle αarg) (count handle αfn)) (cle-plug handle ¬u))
    1≤α = ≤-trans 1≤βplug (support handle ¬u)
    α≤βplug = ≤-trans (≤-trans (m≤m+n (count handle α) (count handle β)) c-αβ≤1) 1≤βplug
    cβ0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count handle β) 1≤α) c-αβ≤1))
    ρ⁻ , inv-mp , skip-mp , inj-mp = mk-thin′ (sum B₁ + q) ((b₁ + sum B₂) + sum B + m) (splitN-eqq B₁ B₂ B q b₁)
    inv-h = subst (Inverter ρ⁻) (mp≡handleq B₁ B₂ B q b₁) inv-mp
    E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
    P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
  in _ , ρ⁻ , (λ y → subst (λ z → ρ⁻ y ≢ z) (mp≡handleq B₁ B₂ B q b₁) (skip-mp y)) , inj-mp
   , E₀ , Eeq , P₀ , Peq

rsplit-confine′ : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {B₁ B₂ B : 𝐓.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : 𝐓.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
  Γ ; γ ⊢ₚ 𝐓.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
            (𝐓.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ 𝐓.∥ P) →
  Σ ℕ λ k → Σ (k →ᵣ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) λ ρ⁻ →
    (∀ y → ρ⁻ y ≢ 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F))
    × (∀ {x y} → ρ⁻ x ≡ ρ⁻ y → x ≡ y)
    × Σ (Frame* k) λ E₀ → (E ≡ E₀ ⋯ᶠ* ρ⁻)
        × Σ (𝐓.Proc k) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ ρ⁻
rsplit-confine′ {m = m} Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {E = E} {P = P} ⊢P =
  let
    handle = SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F)
    Γ₁ , Γ₂ , s' , _p , _N , _⊢B₁ , _⊢B₂ , C , C' , ⊢body = inv-ν ⊢P
    α , β , αβ≼ , ⊢thread , ⊢Ppar = inv-∥ ⊢body
    ⊢term = inv-⟪⟫ ⊢thread
    βplug , (_ , _ , ⊢plug) , support , factor = strengthen-frame E ⊢term
    ¬u = rsplit-app-nonUnr ⊢plug
    αfn , αarg , (_ , _ , ⊢fn) , (_ , _ , ⊢arg) , cle-plug = inv-app ⊢plug
    c-αβ≤1 = subst (count handle α + count handle β ≤_) (count-handle-γinnerq B₁ B₂ B q b₁ γ)
                   (≼⇒count≤ {x = handle} ¬u αβ≼)
    1≤αarg = subst (_≤ count handle αarg) (count-self handle) (inv-var-count ⊢arg handle ¬u)
    1≤βplug = ≤-trans 1≤αarg (≤-trans (m≤n+m (count handle αarg) (count handle αfn)) (cle-plug handle ¬u))
    1≤α = ≤-trans 1≤βplug (support handle ¬u)
    α≤βplug = ≤-trans (≤-trans (m≤m+n (count handle α) (count handle β)) c-αβ≤1) 1≤βplug
    cβ0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count handle β) 1≤α) c-αβ≤1))
    ρ⁻ , inv-mp , skip-mp , inj-mp = mk-thin′ (sum B₁ + q) ((b₁ + sum B₂) + sum B + m) (splitN-eqq B₁ B₂ B q b₁)
    inv-h = subst (Inverter ρ⁻) (mp≡handleq B₁ B₂ B q b₁) inv-mp
    E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
    P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
  in _ , ρ⁻ , (λ y → subst (λ z → ρ⁻ y ≢ z) (mp≡handleq B₁ B₂ B q b₁) (skip-mp y)) , inj-mp
   , E₀ , Eeq , P₀ , Peq
