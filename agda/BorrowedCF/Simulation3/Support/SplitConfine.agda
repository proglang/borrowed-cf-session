module BorrowedCF.Simulation3.Support.SplitConfine where
open import BorrowedCF.Terms using (module SplitRenamings)

-- | The three CONFINEMENT lemmas for the channel-op simulation cases
--   (R-LSplit / R-RSplit / R-Com / R-Acq) and R-Drop.  Each extracts a
--   renaming ρ⁻ whose image avoids the consumed handle, so the frame E and
--   the parallel P both factor through it.  Ported from the (now-broken)
--   BorrowedCF.Simulation3.Support.Theorems against the reworked paper-matching typing.

open import BorrowedCF.Simulation3.Support.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
open import BorrowedCF.Context using (Ctx; Struct)
open 𝐓 using (_;_⊢ₚ_; inv-∥; inv-ν; inv-⟪⟫)
open import BorrowedCF.Simulation3.Support.Confine using (count; count-self; count0⇒∉dom; ≼⇒count≤)
open import BorrowedCF.Simulation3.Support.InvFrame using (strengthen-frame; inv-app; inv-var-count; lsplit-app-nonUnr; rsplit-app-nonUnr)
open import BorrowedCF.Simulation3.Support.Strengthen using (strengthen-Proc-gen; Inverter; mk-thin)
open import BorrowedCF.Simulation3.Support.HandleCount using (count-handle-γinner; splitN-eq; mp≡handle
  ; count-handle-γinnerq; splitN-eqq; mp≡handleq)
open import BorrowedCF.Simulation3.Support.AcqInv using (acq-app-nonUnr)
open import BorrowedCF.Simulation3.Support.AcqHandle using (count-handle-acq; acqN-eq; mp≡handle-acq)
open import Data.Nat.ListAction using (sum)
open Nat using (_≤_; ≤-trans; m≤m+n; m≤n+m; +-monoˡ-≤; n≤0⇒n≡0; s≤s⁻¹)


-- Confinement of the lsplit redex.  The consumed handle 𝐒.inj 0F is linear, so
-- the frame E and parallel P both factor through a renaming ρ⁻ whose image
-- avoids it — exactly U-lsplit's hyps.
lsplit-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {B₁ B₂ B : 𝐓.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : 𝐓.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
  Γ ; γ ⊢ₚ 𝐓.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
            (𝐓.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ 𝐓.∥ P) →
  Σ ℕ λ k → Σ (k →ᵣ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) λ ρ⁻ →
    (∀ y → ρ⁻ y ≢ 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F))
    × Σ (Frame* k) λ E₀ → (E ≡ E₀ ⋯ᶠ* ρ⁻)
        × Σ (𝐓.Proc k) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ ρ⁻
lsplit-confine {m = m} Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P =
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
    ρ⁻ , inv-mp , skip-mp = mk-thin (sum B₁ + q) ((b₁ + sum B₂) + sum B + m) (splitN-eqq B₁ B₂ B q b₁)
    inv-h = subst (Inverter ρ⁻) (mp≡handleq B₁ B₂ B q b₁) inv-mp
    E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
    P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
  in _ , ρ⁻ , (λ y → subst (λ z → ρ⁻ y ≢ z) (mp≡handleq B₁ B₂ B q b₁) (skip-mp y)) , E₀ , Eeq , P₀ , Peq

-- Confinement of the rsplit redex.
rsplit-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {B₁ B₂ B : 𝐓.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  {P : 𝐓.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)} →
  let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
  Γ ; γ ⊢ₚ 𝐓.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
            (𝐓.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F)) ]* ⟫ 𝐓.∥ P) →
  Σ ℕ λ k → Σ (k →ᵣ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) λ ρ⁻ →
    (∀ y → ρ⁻ y ≢ 𝐒.atk {q + suc b₁} {m} (q ↑ʳ 0F))
    × Σ (Frame* k) λ E₀ → (E ≡ E₀ ⋯ᶠ* ρ⁻)
        × Σ (𝐓.Proc k) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ ρ⁻
rsplit-confine {m = m} Γ-S {γ = γ} {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P =
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
    ρ⁻ , inv-mp , skip-mp = mk-thin (sum B₁ + q) ((b₁ + sum B₂) + sum B + m) (splitN-eqq B₁ B₂ B q b₁)
    inv-h = subst (Inverter ρ⁻) (mp≡handleq B₁ B₂ B q b₁) inv-mp
    E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
    P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
  in _ , ρ⁻ , (λ y → subst (λ z → ρ⁻ y ≢ z) (mp≡handleq B₁ B₂ B q b₁) (skip-mp y)) , E₀ , Eeq , P₀ , Peq

-- Confinement of the acq redex (consumed handle 0F at the front of zero ; suc b₁ ; B₁).
acq-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {b₁ : ℕ} {B₁ B₂ : 𝐓.BindGroup}
  {E : Frame* (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
  {P : 𝐓.Proc (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (zero ∷ suc b₁ ∷ B₁) B₂
            (𝐓.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ 𝐓.∥ P) →
  Σ ℕ λ k → Σ (k →ᵣ (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)) λ ρ⁻ →
    (∀ y → ρ⁻ y ≢ 0F)
    × Σ (Frame* k) λ E₀ → (E ≡ E₀ ⋯ᶠ* ρ⁻)
        × Σ (𝐓.Proc k) λ P₀ → P ≡ P₀ 𝐓.⋯ₚ ρ⁻
acq-confine {m = m} Γ-S {γ = γ} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P} ⊢P =
  let
    handle : 𝔽 (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)
    handle = 0F
    Γ₁ , Γ₂ , s' , _p , _N , _⊢B₁ , _⊢B₂ , C , C' , ⊢body = inv-ν ⊢P
    α , β , αβ≼ , ⊢thread , ⊢Ppar = inv-∥ ⊢body
    ⊢term = inv-⟪⟫ ⊢thread
    βplug , (_ , _ , ⊢plug) , support , factor = strengthen-frame E ⊢term
    ¬u = acq-app-nonUnr ⊢plug
    αfn , αarg , (_ , _ , ⊢fn) , (_ , _ , ⊢arg) , cle-plug = inv-app ⊢plug
    c-αβ≤1 = subst (count handle α + count handle β ≤_) (count-handle-acq b₁ B₁ B₂ γ)
                   (≼⇒count≤ {x = handle} ¬u αβ≼)
    1≤αarg = subst (_≤ count handle αarg) (count-self handle) (inv-var-count ⊢arg handle ¬u)
    1≤βplug = ≤-trans 1≤αarg (≤-trans (m≤n+m (count handle αarg) (count handle αfn)) (cle-plug handle ¬u))
    1≤α = ≤-trans 1≤βplug (support handle ¬u)
    α≤βplug = ≤-trans (≤-trans (m≤m+n (count handle α) (count handle β)) c-αβ≤1) 1≤βplug
    cβ0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count handle β) 1≤α) c-αβ≤1))
    ρ⁻ , inv-mp , skip-mp = mk-thin 0 ((b₁ + sum B₁) + sum B₂ + m) (acqN-eq b₁ B₁ B₂)
    inv-h = subst (Inverter ρ⁻) (mp≡handle-acq b₁ B₁ B₂) inv-mp
    E₀ , Eeq = factor handle ¬u α≤βplug ρ⁻ inv-h
    P₀ , Peq = strengthen-Proc-gen ⊢Ppar ρ⁻ handle inv-h (count0⇒∉dom β cβ0)
  in _ , ρ⁻ , (λ y → subst (λ z → ρ⁻ y ≢ z) (mp≡handle-acq b₁ B₁ B₂) (skip-mp y)) , E₀ , Eeq , P₀ , Peq
