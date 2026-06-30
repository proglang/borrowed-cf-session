-- REVERSE-CONFINE subsystem: the mirror of the forward acq-confine /
-- HandleCount machinery, for the ν-headed reverse channel cases.  Starts with
-- the CLOSE case (RU-Close inj₁): the close binder is `ν (b₁ ∷ []) (b₂ ∷ [])`
-- (singletons forced by inv-U-ν-∥-shape), NOT the SplitRenamings
-- `B₁ ++ suc b₁ ∷ B₂` shape, so the HandleCount lemmas are re-derived here as a
-- new variant.  Both consumed handles are confined: 0F (the `end ‼` endpoint,
-- block 1) and the block-2 handle at flat position sum (b₁ ∷ []) (the `end ⁇`
-- endpoint).

module BorrowedCF.Simulation2.ReverseConfine where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; cast)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder)
open import BorrowedCF.Simulation2.Confine using (count)
open import BorrowedCF.Simulation2.StructDom
  using (count-structBinder-lt; count-weaken*-lo; count-weaken*-shift; count-⋯ᵣwkʳ-↑ˡ; count-⋯ᵣwkʳ-↑ʳ)

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ)

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; s≤s; z≤n; +-identityʳ; m≤m+n; m≤n+m; <-≤-trans)
open import Data.List using (_∷_; [])

-- Extra imports for the multi-handle frame strengthening primitive.
open import BorrowedCF.Terms
open import BorrowedCF.Types using (𝕋; Eff; Unr)
open import BorrowedCF.Context.Base using (Ctx; ParSeq) renaming (`_ to `ₛ_)
open import BorrowedCF.Context.Domain using (dom)
open import Data.Fin.Subset using (_∉_)
open import BorrowedCF.Reduction.Base using (ChanCx; Frame; Frame*; _[_]*; _⋯ᶠ*_; _⋯ᵛ_; Value; value-⋯; □·_; _·□; □⊗_; _⊗□; □;_; `let-`in_; `let⊗-`in_; `inj□; `case□`of⟨_;_⟩)
open import BorrowedCF.Context.Join using (biasedDir; join)
import BorrowedCF.Simulation2.InvFrame as IF
open import BorrowedCF.Simulation2.Confine
  using (count0⇒∉dom; count-join-Dir; count-join-PS; count-wk-suc; ∉dom⇒count0)
open import BorrowedCF.Simulation2.Strengthen
  using (Inverter*; invH↑; H↑; strengthen-Tm-gen*)
import Data.List as L
open Nat using (≤-refl; ≤-reflexive; ≤-trans; +-comm)
open import BorrowedCF.Types using (Pol; ‼; ⁇; _≃_; ≃-refl; ≃-sym; ≃-trans; unr-≃; _`→_; ⟨_⟩; _⟨_⟩→_; end)
open import BorrowedCF.Simulation2.InvFrame using (arg-type)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import BorrowedCF.Processes.Typed using (_;_⊢ₚ_; inv-∥; inv-ν; inv-⟪⟫; ⟪_⟫; _∥_; ν)
open import BorrowedCF.Simulation2.Confine using (count-self; ≼⇒count≤)
open Nat using (n≤0⇒n≡0; s≤s⁻¹; +-monoˡ-≤; +-monoʳ-≤; +-mono-≤)

-- ───────────────────────────────────────────────────────────────────────────
-- close-app-nonUnr : the consumed close handle has a non-Unr type.  end's domain
-- is ⟨ end p ⟩ and Unr ⟨ end p ⟩ ≡ Skips (end p), which is uninhabited (Skips has
-- no end case).  Mirrors AcqInv.acq-app-nonUnr.
fn-end-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {p T U a ϵ}
  → Γ ; β ⊢ K (`end p) ∶ T ⟨ a ⟩→ U ∣ ϵ → ⟨ end p ⟩ ≃ T
fn-end-dom (T-Const `end) = ≃-refl
fn-end-dom (T-Conv (dom≃ `→ cod≃) _ d) = ≃-trans (fn-end-dom d) dom≃
fn-end-dom (T-Weaken _ d) = fn-end-dom d

close-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {p} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K (`end p) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
close-app-nonUnr d = go d
  where
    go : ∀ {N} {Γ : Ctx N} {β : Struct N} {p} {x : 𝔽 N} {T ϵ}
       → Γ ; β ⊢ K (`end p) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
    go (T-AppUnr _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))) u
    ... | ⟨ () ⟩
    go (T-AppLin _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))) u
    ... | ⟨ () ⟩
    go (T-AppLeft _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))) u
    ... | ⟨ () ⟩
    go (T-AppRight _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))) u
    ... | ⟨ () ⟩
    go (T-Conv _ _ d) u = go d u
    go (T-Weaken _ d) u = go d u

-- ───────────────────────────────────────────────────────────────────────────
-- count-handle-close (L) : the `end ‼` endpoint consumes 0F (block 1).  The
-- inv-ν context of `ν (b₁ ∷ []) (b₂ ∷ []) _` counts 0F exactly once.  This is
-- the AcqHandle.count-handle-acq derivation with C₁ := b₁ ∷ [], B₂ := b₂ ∷ [].
count-handle-closeᴸ : ∀ (b₁ b₂ : ℕ) {m} (γ : Struct m) →
  let C₁ = suc b₁ ∷ [] in
  count 0F
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (b₂ ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder (b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum (b₂ ∷ []))) ) ≡ 1
count-handle-closeᴸ b₁ b₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = suc b₁ ∷ []
    C₂ : BindGroup
    C₂ = b₂ ∷ []
    0<C₁ : 0 < sum C₁
    0<C₁ = s≤s z≤n
    z₁ : 𝔽 (sum C₁)
    z₁ = Fin.zero {b₁ + 0}
    partA : count 0F (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) (z₁ ↑ˡ sum C₂)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum C₂) (structBinder C₁) z₁
          ■ count-structBinder-lt C₁ z₁ 0<C₁
    partB : count 0F (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (z₁ ↑ˡ sum C₂)
          ■ cong (count (z₁ ↑ˡ sum C₂)) (wkˡ≡weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-lo (sum C₁) (structBinder C₂) (z₁ ↑ˡ sum C₂) 0↑<C₁
      where
        0↑<C₁ : Fin.toℕ (z₁ ↑ˡ sum C₂) < sum C₁
        0↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ z₁ (sum C₂))) 0<C₁
        wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count 0F (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ (Fin.zero {b₁ + 0 + sum C₂ + m}) (s≤s z≤n)

-- ───────────────────────────────────────────────────────────────────────────
-- count-handle-close (R) : the `end ⁇` endpoint consumes the block-2 handle,
-- at flat position sum (suc b₁ ∷ []) (= the first index of block 2).  Mirrors
-- HandleCount.count-handle-γinner with the consumed handle in the SECOND block.
count-handle-closeᴿ : ∀ (b₁ b₂ : ℕ) {m} (γ : Struct m) →
  let C₁ = suc b₁ ∷ []
      C₂ = suc b₂ ∷ [] in
  count ((sum C₁ ↑ʳ (Fin.zero {b₂ + 0})) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ) ≡ 1
count-handle-closeᴿ b₁ b₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = suc b₁ ∷ []
    C₂ : BindGroup
    C₂ = suc b₂ ∷ []
    z₂ : 𝔽 (sum C₂)
    z₂ = Fin.zero {b₂ + 0}
    hdl : 𝔽 (sum C₁ + sum C₂)
    hdl = sum C₁ ↑ʳ z₂
    0<C₂ : 0 < sum C₂
    0<C₂ = s≤s z≤n
    partA : count (hdl ↑ˡ m) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) hdl
          ■ count-⋯ᵣwkʳ-↑ʳ (sum C₂) (structBinder C₁) z₂
    partB : count (hdl ↑ˡ m) (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) hdl
          ■ cong (count hdl) (wkˡ≡weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-shift (sum C₁) (structBinder C₂) z₂
          ■ count-structBinder-lt C₂ z₂ 0<C₂
      where
        wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count (hdl ↑ˡ m) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ (hdl ↑ˡ m) hdl<
      where
        hdl< : Fin.toℕ (hdl ↑ˡ m) < sum C₁ + sum C₂
        hdl< = subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ hdl m))
                 (subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ʳ (sum C₁) z₂ ■ +-identityʳ (sum C₁)))
                   m<m+sucC₂)
          where
            m<m+sucC₂ : sum C₁ < sum C₁ + sum C₂
            m<m+sucC₂ = subst (suc (sum C₁) ≤_) (sym (Nat.+-suc (sum C₁) (b₂ + 0)))
                          (s≤s (m≤m+n (sum C₁) (b₂ + 0)))

-- ───────────────────────────────────────────────────────────────────────────
-- MULTI-HANDLE frame strengthening: factor a typed frame E through any renaming
-- ρ missing a whole SET H of consumed handles.  Mirrors InvFrame.strengthen-frame
-- (single handle) but uses Inverter* / strengthen-Tm-gen* so the close frame can
-- avoid BOTH bound channel handles {0F , block-2 handle} at once.  All H-handles
-- are assumed non-Unr (the consumed channels), supplied as Hnu.
strengthen-frame* : ∀ {N} {Γ : Ctx N} {α : Struct N} {t : Tm N} {T ϵ}
  (E : Frame* N) → Γ ; α ⊢ E [ t ]* ∶ T ∣ ϵ → (H : 𝔽 N → Set)
  → Σ[ β ∈ Struct N ] (∃[ T₀ ] ∃[ ϵ₀ ] Γ ; β ⊢ t ∶ T₀ ∣ ϵ₀)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h β ≤ count h α)
      × (((h : 𝔽 N) → H h → ¬ Unr (Γ h) × (count h α ≤ count h β))
         → {k : ℕ} (ρ : k →ᵣ N) → Inverter* ρ H → Σ[ E₀ ∈ Frame* k ] E ≡ E₀ ⋯ᶠ* ρ)
strengthen-frame* [] ⊢t H =
  _ , (_ , _ , ⊢t) , (λ h _ → ≤-refl) , (λ _ ρ inv → [] , refl)
strengthen-frame* (L._∷_ (□· e₂) E') ⊢E H =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = IF.inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H z → z ∉ dom α₂
            H∉ z Hz = let ¬u , cα≤β = Hαβ z Hz
                          cα₂0 = IF.+≤ˡ⇒0 (count z α₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                      in count0⇒∉dom α₂ cα₂0
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv H∉
        in (L._∷_ (□· e₂₀) E₀') , cong₂ L._∷_ (cong □·_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (_·□ {e₁ = e₁} V) E') ⊢E H =
  let α₁ , α₂ , (_ , _ , ⊢V) , (_ , _ , ⊢inner) , cle = IF.inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H z → z ∉ dom α₁
            H∉ z Hz = let ¬u , cα≤β = Hαβ z Hz
                          cα₁0 = IF.+≤ʳ⇒0 (count z α₁) (count z α₂) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                      in count0⇒∉dom α₁ cα₁0
            comp₀ , compeq = strengthen-Tm-gen* ⊢V ρ H inv H∉
            V₀ = IF.value-reflect ρ comp₀ (subst Value compeq V)
        in (L._∷_ (_·□ V₀) E₀') , cong₂ L._∷_ (IF.·□-cong compeq V (V₀ ⋯ᵛ ρ)) E'eq)
strengthen-frame* (L._∷_ (□⊗ e₂) E') ⊢E H =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = IF.inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H z → z ∉ dom α₂
            H∉ z Hz = let ¬u , cα≤β = Hαβ z Hz
                          cα₂0 = IF.+≤ˡ⇒0 (count z α₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                      in count0⇒∉dom α₂ cα₂0
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv H∉
        in (L._∷_ (□⊗ e₂₀) E₀') , cong₂ L._∷_ (cong □⊗_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (_⊗□ {e₁ = e₁} V) E') ⊢E H =
  let α₁ , α₂ , (_ , _ , ⊢V) , (_ , _ , ⊢inner) , cle = IF.inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H z → z ∉ dom α₁
            H∉ z Hz = let ¬u , cα≤β = Hαβ z Hz
                          cα₁0 = IF.+≤ʳ⇒0 (count z α₁) (count z α₂) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                      in count0⇒∉dom α₁ cα₁0
            comp₀ , compeq = strengthen-Tm-gen* ⊢V ρ H inv H∉
            V₀ = IF.value-reflect ρ comp₀ (subst Value compeq V)
        in (L._∷_ (_⊗□ V₀) E₀') , cong₂ L._∷_ (IF.⊗□-cong compeq V (V₀ ⋯ᵛ ρ)) E'eq)
strengthen-frame* (L._∷_ (□; e₂) E') ⊢E H =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = IF.inv-seq ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H z → z ∉ dom α₂
            H∉ z Hz = let ¬u , cα≤β = Hαβ z Hz
                          cα₂0 = IF.+≤ˡ⇒0 (count z α₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                      in count0⇒∉dom α₂ cα₂0
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv H∉
        in (L._∷_ (□; e₂₀) E₀') , cong₂ L._∷_ (cong □;_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`let-`in e') E') ⊢E H =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = IF.inv-let ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e₁ H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β) ρ inv
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv)
                           (λ { 0F () ; (suc z) Hz →
                                let ¬u , cα≤β = Hαβ z Hz
                                    cγ₂0 = IF.+≤ˡ⇒0 (count z γ₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                                    COUNT0 = count-join-PS p/s (suc z) (`ₛ zero) (𝐂S.wk γ₂) ■ count-wk-suc γ₂ z ■ cγ₂0
                                in count0⇒∉dom (join p/s (`ₛ zero) (𝐂S.wk γ₂)) COUNT0 })
        in (L._∷_ (`let-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let-`in_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`let⊗-`in e') E') ⊢E H =
  let γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , (_ , _ , _ , _ , ⊢e₂) , cle = IF.inv-letpair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e₁ H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β) ρ inv
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑ ↑) (H↑ (H↑ H)) (invH↑ (invH↑ inv))
                           (λ { 0F () ; (suc 0F) () ; (suc (suc z)) Hz →
                                let ¬u , cα≤β = Hαβ z Hz
                                    cγ₂0 = IF.+≤ˡ⇒0 (count z γ₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                                    COUNT0 = count-join-PS p/s (suc (suc z)) (join d (`ₛ zero) (`ₛ suc zero)) (𝐂S.wk (𝐂S.wk γ₂))
                                           ■ cong₂ _+_ (count-join-Dir d (suc (suc z)) (`ₛ zero) (`ₛ suc zero))
                                                       (count-wk-suc (𝐂S.wk γ₂) (suc z) ■ count-wk-suc γ₂ z ■ cγ₂0)
                                in count0⇒∉dom (join p/s (join d (`ₛ zero) (`ₛ suc zero)) (𝐂S.wk (𝐂S.wk γ₂))) COUNT0 })
        in (L._∷_ (`let⊗-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let⊗-`in_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`inj□ i) E') ⊢E H =
  let _ , _ , ⊢inner = IF.inv-inj ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner H
  in β , pt , support' ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' Hαβ ρ inv
        in (L._∷_ (`inj□ i) E₀') , cong₂ L._∷_ refl E'eq)
strengthen-frame* (L._∷_ (`case□`of⟨ e₁ ; e₂ ⟩) E') ⊢E H =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e) , (_ , _ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = IF.inv-case ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e H
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ Hαβ ρ inv →
        let E₀' , E'eq = factor' (λ h Hh → let ¬u , cα≤β = Hαβ h Hh
                                           in ¬u , ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β) ρ inv
            H∉ : (z : 𝔽 _) → H↑ H z → z ∉ dom (join p/s (`ₛ zero) (𝐂S.wk γ₂))
            H∉ = λ { 0F () ; (suc z) Hz →
                       let ¬u , cα≤β = Hαβ z Hz
                           cγ₂0 = IF.+≤ˡ⇒0 (count z γ₁) (≤-trans (≤-trans (cle z ¬u) cα≤β) (support' z ¬u))
                           COUNT0 = count-join-PS p/s (suc z) (`ₛ zero) (𝐂S.wk γ₂) ■ count-wk-suc γ₂ z ■ cγ₂0
                       in count0⇒∉dom (join p/s (`ₛ zero) (𝐂S.wk γ₂)) COUNT0 }
            e₁₀ , e₁eq = strengthen-Tm-gen* ⊢e₁ (ρ ↑) (H↑ H) (invH↑ inv) H∉
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv) H∉
        in (L._∷_ (`case□`of⟨ e₁₀ ; e₂₀ ⟩) E₀') ,
           cong₂ L._∷_ (cong₂ (λ a b → `case□`of⟨ a ; b ⟩) e₁eq e₂eq) E'eq)

-- ───────────────────────────────────────────────────────────────────────────
-- Inverter* for weaken* 2, missing exactly the two close handles {0F , 1F}.
H2 : ∀ {N} → 𝔽 (2 + N) → Set
H2 z = (z ≡ 0F) ⊎ (z ≡ 1F)

wk2-image : ∀ {N} (v : 𝔽 N) → 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2 v ≡ suc (suc v)
wk2-image v = 𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ 2 v

inv-wk2 : ∀ {N} → Inverter* (𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2) (H2 {N})
inv-wk2 0F             ¬H = ⊥-elim (¬H (inj₁ refl))
inv-wk2 (suc 0F)       ¬H = ⊥-elim (¬H (inj₂ refl))
inv-wk2 (suc (suc y')) ¬H = y' , sym (wk2-image y')

-- ───────────────────────────────────────────────────────────────────────────
-- close-confine (base case b₁ = b₂ = 1).  From the well-typed close redex body
-- ν [1] [1] (⟪ F₀ᴸ [ end‼ · `0F ] ⟫ ∥ ⟪ F₀ᴿ [ end⁇ · `1F ] ⟫) recover source
-- frames E₁ E₂ : Frame* m with F₀ᴸ ≡ E₁ ⋯ᶠ* weaken* 2 , F₀ᴿ ≡ E₂ ⋯ᶠ* weaken* 2 —
-- i.e. each thread's frame avoids BOTH bound channel handles {0F , 1F}.  The
-- consumed handle (0F for L, 1F for R) is confined by its own plug; the OTHER
-- handle is linear in the sibling thread, hence count 0 in this thread.
close-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {F₀ᴸ F₀ᴿ : Frame* (2 + m)} →
  Γ ; γ ⊢ₚ ν (suc 0 ∷ []) (suc 0 ∷ [])
            (⟪ F₀ᴸ [ K (`end ‼) · (` 0F) ]* ⟫ ∥ ⟪ F₀ᴿ [ K (`end ⁇) · (` 1F) ]* ⟫) →
  Σ (Frame* m) λ E₁ → (F₀ᴸ ≡ E₁ ⋯ᶠ* 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2)
    × Σ (Frame* m) λ E₂ → (F₀ᴿ ≡ E₂ ⋯ᶠ* 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2)
close-confine {m = m} Γ-S {γ = γ} {F₀ᴸ = F₀ᴸ} {F₀ᴿ = F₀ᴿ} ⊢P =
  let
    Γ₁ , Γ₂ , s′ , _N , _⊢B₁ , _⊢B₂ , C , C′ , ⊢body = inv-ν ⊢P
    α , β , αβ≼ , ⊢tL , ⊢tR = inv-∥ ⊢body
    ⊢L = inv-⟪⟫ ⊢tL
    ⊢R = inv-⟪⟫ ⊢tR
    -- count of each handle in γinner is exactly 1.
    c0γ = count-handle-closeᴸ 0 1 γ
    c1γ = count-handle-closeᴿ 0 0 γ
    -- strengthen each thread's frame against the 2-handle set.
    βpL , (_ , _ , ⊢plugL) , supportL , factorL = strengthen-frame* F₀ᴸ ⊢L H2
    βpR , (_ , _ , ⊢plugR) , supportR , factorR = strengthen-frame* F₀ᴿ ⊢R H2
    ¬u0 = close-app-nonUnr ⊢plugL
    ¬u1 = close-app-nonUnr ⊢plugR
    -- arg typings: ` 0F on the L plug, ` 1F on the R plug.
    αfnL , αargL , _ , (_ , _ , ⊢argL) , cle-plugL = IF.inv-app ⊢plugL
    αfnR , αargR , _ , (_ , _ , ⊢argR) , cle-plugR = IF.inv-app ⊢plugR
    -- the plug arg contributes ≥ 1 to its consumed handle.
    1≤βpL0 : 1 ≤ count 0F βpL
    1≤βpL0 = ≤-trans (subst (_≤ count 0F αargL) (count-self (Fin.zero {1 + m})) (IF.inv-var-count ⊢argL 0F ¬u0))
                     (≤-trans (m≤n+m (count 0F αargL) (count 0F αfnL)) (cle-plugL 0F ¬u0))
    1≤βpR1 : 1 ≤ count 1F βpR
    1≤βpR1 = ≤-trans (subst (_≤ count 1F αargR) (count-self (suc (Fin.zero {m}))) (IF.inv-var-count ⊢argR 1F ¬u1))
                     (≤-trans (m≤n+m (count 1F αargR) (count 1F αfnR)) (cle-plugR 1F ¬u1))
    -- cross-thread linearity: count h α + count h β ≤ count h γinner = 1.
    c0-αβ≤1 : count 0F α + count 0F β ≤ 1
    c0-αβ≤1 = subst (count 0F α + count 0F β ≤_) c0γ (≼⇒count≤ {x = 0F} ¬u0 αβ≼)
    c1-αβ≤1 : count 1F α + count 1F β ≤ 1
    c1-αβ≤1 = subst (count 1F α + count 1F β ≤_) c1γ (≼⇒count≤ {x = 1F} ¬u1 αβ≼)
    -- 1F is fully consumed by the R thread ⇒ absent from the L thread.
    1≤β1 : 1 ≤ count 1F β
    1≤β1 = ≤-trans 1≤βpR1 (supportR 1F ¬u1)
    cα1≡0 : count 1F α ≡ 0
    cα1≡0 = n≤0⇒n≡0 (s≤s⁻¹
              (subst (_≤ 1) (Nat.+-comm (count 1F α) 1)
                (≤-trans (Nat.+-monoʳ-≤ (count 1F α) 1≤β1) c1-αβ≤1)))
    -- 0F is fully consumed by the L thread ⇒ absent from the R thread.
    1≤α0 : 1 ≤ count 0F α
    1≤α0 = ≤-trans 1≤βpL0 (supportL 0F ¬u0)
    cβ0≡0 : count 0F β ≡ 0
    cβ0≡0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count 0F β) 1≤α0) c0-αβ≤1))
    -- L factoring: 0F count in α ≤ its plug count; 1F count in α = 0.
    α0≤βpL : count 0F α ≤ count 0F βpL
    α0≤βpL = ≤-trans (subst (_≤ 1) (cong (count 0F α +_) cβ0≡0 ■ +-identityʳ (count 0F α)) c0-αβ≤1) 1≤βpL0
    hypL = λ { h (inj₁ refl) → ¬u0 , α0≤βpL
             ; h (inj₂ refl) → ¬u1 , subst (_≤ count 1F βpL) (sym cα1≡0) z≤n }
    -- R factoring: 1F count in β ≤ its plug count; 0F count in β = 0.
    β1≤βpR : count 1F β ≤ count 1F βpR
    β1≤βpR = ≤-trans (subst (_≤ 1) (Nat.+-comm (count 1F α) (count 1F β) ■ cong (count 1F β +_) cα1≡0 ■ +-identityʳ (count 1F β)) c1-αβ≤1) 1≤βpR1
    hypR = λ { h (inj₁ refl) → ¬u0 , subst (_≤ count 0F βpR) (sym cβ0≡0) z≤n
             ; h (inj₂ refl) → ¬u1 , β1≤βpR }
    E₁ , Eeq₁ = factorL hypL (𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2) inv-wk2
    E₂ , Eeq₂ = factorR hypR (𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ 2) inv-wk2
  in E₁ , Eeq₁ , E₂ , Eeq₂
