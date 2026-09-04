-- | TWO-HANDLE confinement, for the SYNCHRONISING redexes `R-Com` and
--   `R-Close`.  Both consume a head handle on EACH endpoint of the same
--   binder, so -- by linearity -- the two frames, the sent value and the
--   parallel residual all factor through the renaming that skips BOTH.
--
--   `Support/HeadConfine.agda` does this for ONE handle (`R-Discard` /
--   `R-Drop`), reusing `Strengthen.strengthen-Tm-gen` and
--   `InvFrame.strengthen-frame`, which are indexed by a single missing
--   variable.  Here the missing variables come in pairs, so the construction
--   runs on `Strengthen`'s handle-SET machinery (`Inverter*`,
--   `strengthen-Tm-gen*`, `strengthen-Proc-gen*`); §1 supplies the one piece
--   that was still missing there, `strengthen-frame*`, the set-indexed
--   version of `InvFrame.strengthen-frame`.
--
--   §2 builds the two-variable thinnings: `wkₚ a c` (which is exactly the
--   composition of two `mk-thin`s, skipping `0F` and the head of the second
--   endpoint) and `weaken* 2` (skipping `0F` and `1F`).
--   §3 counts the two handles in the body structure that `TP-Res` prescribes.
--   §4 assembles `com-confine` and `close-confine`.
--
--   `R-Choice` needs NO confinement: its rule takes arbitrary frames and an
--   arbitrary residual.
module BorrowedCF.Simulation.Support.PairConfine where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Context using (Ctx; Struct)
open 𝐓 using (_;_⊢ₚ_; inv-∥; inv-ν; inv-⟪⟫; BindGroup; structBinder; bindCtx⇒chanCtx)
open 𝐓 using (BindCtx; BindCtx′)
open 𝐓.BindCtx
open 𝐓.BindCtx′
open import BorrowedCF.Context.Base using (_∥_; _⸴*_; `_)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Simulation.Support.Confine
  using (count; count-self; count0⇒∉dom; ≼⇒count≤)
open import BorrowedCF.Simulation.Support.InvFrame
  using ( inv-app; inv-pair; inv-seq; inv-let; inv-letpair; inv-case
        ; inv-var-count; value-reflect; app₁-cong; app₂-cong; ⊗□-cong
        ; +≤ˡ⇒0; +≤ʳ⇒0; arg-type)
  renaming (inv-inj to inv-injᶠ)
open import BorrowedCF.Simulation.Support.Strengthen
  using ( Inverter; Inverter*; H↑; invH↑; mk-thin
        ; strengthen-Tm-gen*; strengthen-Proc-gen*)
open import BorrowedCF.Simulation.Support.FrameRename using (⋯ᶠ*-cong)
open import BorrowedCF.Simulation.Support.StructDom
  using ( count-structBinder-lt; count-weaken*-lo; count-⋯ᵣwkʳ-↑ˡ
        ; count-⋯ᵣwkʳ-↑ʳ; count-weaken*-shift; ⋯ᵣwkˡ≡⋯weaken*)
open import BorrowedCF.Simulation.Support.HeadConfine
  using (¬unr-handle; count-handle-head)
open import BorrowedCF.Context.Join using (join)
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; toℕ-cast)
open import Data.List using (_∷_; [])
open import Data.Vec.Relation.Unary.All.Properties using (++⁺)
open import BorrowedCF.Simulation.Support.Confine
  using (count-join-Dir; count-join-PS; count-wk-suc)
open Nat using ( _≤_; _<_; ≤-refl; ≤-trans; m≤m+n; m≤n+m; +-monoˡ-≤; +-monoʳ-≤
               ; n≤0⇒n≡0; s≤s⁻¹; s≤s; z≤n; +-comm; +-assoc; +-identityʳ)
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe
  using (close-residual-skips)

------------------------------------------------------------------------
-- Close handles at the head of a binding group force that group to have
-- width one: no further borrow can follow an end tip.

fn-end-dom :
  ∀ {N} {Γ : Ctx N} {β : Struct N} {p T U a ϵ} →
  Γ ; β ⊢ K (`end p) ∶ T ⟨ a ⟩→ U ∣ ϵ → ⟨ end p ⟩ ≃ T
fn-end-dom (T-Const `end) = ≃-refl
fn-end-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  ≃-trans (fn-end-dom d) dom≃
fn-end-dom (T-Weaken _ d) = fn-end-dom d

close-handle-end :
  ∀ {N} {Γ : Ctx N} {β : Struct N} {p} {dir} {x : 𝔽 N} {T ϵ} {s₀} →
  Γ ; β ⊢ K (`end p) ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ →
  lookup Γ x ≡ ⟨ s₀ ⟩ → s₀ ≃ end p
close-handle-end {x = x} {s₀ = s₀} d Γx = go d
  where
  tip :
    ∀ {β₁ β₂ p T U a ϵ₁ ϵ₂} →
    _ ; β₁ ⊢ K (`end p) ∶ T ⟨ a ⟩→ U ∣ ϵ₁ →
    _ ; β₂ ⊢ ` x ∶ T ∣ ϵ₂ → s₀ ≃ end p
  tip ⊢fn ⊢arg =
    let
      T≃Γx = arg-type ⊢arg
      end≃T = fn-end-dom ⊢fn
      ⟨s₀⟩≃end : ⟨ s₀ ⟩ ≃ ⟨ end _ ⟩
      ⟨s₀⟩≃end =
        ≃-trans (≃-sym (≃-reflexive Γx))
          (≃-trans T≃Γx (≃-sym end≃T))
    in ⟨⟩≃-inv ⟨s₀⟩≃end
    where
    ⟨⟩≃-inv : ∀ {a b} → ⟨ a ⟩ ≃ ⟨ b ⟩ → a ≃ b
    ⟨⟩≃-inv ⟨ eq ⟩ = eq

  go :
    ∀ {β dir T ϵ} →
    _ ; β ⊢ K (`end _) ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ → s₀ ≃ end _
  go (T-AppUnr _ _ ⊢fn ⊢arg) = tip ⊢fn ⊢arg
  go (T-AppLin _ _ ⊢fn ⊢arg) = tip ⊢fn ⊢arg
  go (T-AppLeft _ _ ⊢fn ⊢arg) = tip ⊢fn ⊢arg
  go (T-AppRight _ _ ⊢fn ⊢arg) = tip ⊢fn ⊢arg
  go (T-Conv _ _ d) = go d
  go (T-Weaken _ d) = go d

private
  close-block-width :
    ∀ {p q} {s : 𝕊 0} {b} {Γ : Ctx (suc b)} {s₀} →
    New s → BindCtx′ (s ; end p) Γ →
    lookup Γ 0F ≡ ⟨ s₀ ⟩ → s₀ ≃ end q → b ≡ 0
  close-block-width N (cons _ _ _ _ (nil _)) Γ0 endTip = refl
  close-block-width {s₀ = s₀} N
    (cons sa sb noSkip split (cons _ _ noSkip₂ split₂ tail))
    Γ0 endTip =
    ⊥-elim (noSkip₂ (close-residual-skips N split (≃-trans sa≃s₀ endTip)))
    where
    ⟨⟩-injective : ⟨ sa ⟩ ≡ ⟨ s₀ ⟩ → sa ≡ s₀
    ⟨⟩-injective refl = refl

    sa≃s₀ : sa ≃ s₀
    sa≃s₀ with ⟨⟩-injective Γ0
    ... | refl = ≃-refl

close-group-width :
  ∀ {p q} {s : 𝕊 0} {b} {Γ : Ctx (suc b + 0)} {s₀} →
  New s → BindCtx (s ; end p) (suc b ∷ []) Γ →
  lookup Γ 0F ≡ ⟨ s₀ ⟩ → s₀ ≃ end q → b ≡ 0
close-group-width N (last block) Γ0 endTip =
  sym (+-identityʳ _) ■ close-block-width N block Γ0 endTip

------------------------------------------------------------------------
-- 1.  `strengthen-frame`, indexed by a SET of missing variables.
--
-- Line-for-line `InvFrame.strengthen-frame`, with `Inverter ρ h` replaced by
-- `Inverter* ρ H` and `strengthen-Tm-gen` by `strengthen-Tm-gen*`: the
-- "plug accounts for all of h's count" side condition is now demanded for
-- every `h` in the set.

strengthen-frame* : ∀ {N} {Γ : Ctx N} {α : Struct N} {t : Tm N} {T ϵ}
  (E : Frame* N) → Γ ; α ⊢ E [ t ]* ∶ T ∣ ϵ
  → Σ[ β ∈ Struct N ] (∃[ T₀ ] ∃[ ϵ₀ ] Γ ; β ⊢ t ∶ T₀ ∣ ϵ₀)
      × ((h : 𝔽 N) → ¬ Unr (lookup Γ h) → count h β ≤ count h α)
      × ({k : ℕ} (ρ : k →ᵣ N) (H : 𝔽 N → Set) → Inverter* ρ H
         → ((h : 𝔽 N) → H h → ¬ Unr (lookup Γ h))
         → ((h : 𝔽 N) → H h → count h α ≤ count h β)
         → Σ[ E₀ ∈ Frame* k ] E ≡ E₀ ⋯ᶠ* ρ)
strengthen-frame* L.[] ⊢t =
  _ , (_ , _ , ⊢t) , (λ h _ → ≤-refl) , (λ ρ H inv Hu Hc → L.[] , refl)
strengthen-frame* (L._∷_ (app₁ e₂ d V?) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h α₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz → count0⇒∉dom α₂ (zer z hz))
        in (L._∷_ (app₁ e₂₀ d (λ x → value-reflect ρ e₂₀ (subst Value e₂eq (V? x)))) E₀') ,
           cong₂ L._∷_ (app₁-cong e₂eq) E'eq)
strengthen-frame* (L._∷_ (app₂ e₁ d V?) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢inner) , cle = inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ʳ⇒0 (count h α₁) (count h α₂)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            comp₀ , compeq = strengthen-Tm-gen* ⊢e₁ ρ H inv (λ z hz → count0⇒∉dom α₁ (zer z hz))
        in (L._∷_ (app₂ comp₀ d (λ x → value-reflect ρ comp₀ (subst Value compeq (V? x)))) E₀') ,
           cong₂ L._∷_ (app₂-cong compeq) E'eq)
strengthen-frame* (L._∷_ (□⊗ e₂) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h α₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz → count0⇒∉dom α₂ (zer z hz))
        in (L._∷_ (□⊗ e₂₀) E₀') , cong₂ L._∷_ (cong □⊗_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (_⊗□ {e₁ = e₁} V) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢V) , (_ , _ , ⊢inner) , cle = inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ʳ⇒0 (count h α₁) (count h α₂)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            comp₀ , compeq = strengthen-Tm-gen* ⊢V ρ H inv (λ z hz → count0⇒∉dom α₁ (zer z hz))
            V₀ = value-reflect ρ comp₀ (subst Value compeq V)
        in (L._∷_ (_⊗□ V₀) E₀') , cong₂ L._∷_ (⊗□-cong compeq V (V₀ ⋯ᵛ ρ)) E'eq)
strengthen-frame* (L._∷_ (□; e₂) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-seq ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h α₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ ρ H inv (λ z hz → count0⇒∉dom α₂ (zer z hz))
        in (L._∷_ (□; e₂₀) E₀') , cong₂ L._∷_ (cong □;_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`let-`in e') E') ⊢E =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = inv-let ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e₁
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h γ₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv)
                           (λ { (suc z) hz →
                              count0⇒∉dom (join p/s (` zero) (𝐂S.wk γ₂))
                                (count-join-PS p/s (suc z) (` zero) (𝐂S.wk γ₂)
                                 ■ count-wk-suc γ₂ z ■ zer z hz) })
        in (L._∷_ (`let-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let-`in_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`let⊗-`in e') E') ⊢E =
  let γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , (_ , _ , _ , _ , ⊢e₂) , cle = inv-letpair ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e₁
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h γ₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑ ↑) (H↑ (H↑ H)) (invH↑ (invH↑ inv))
                           (λ { (suc (suc z)) hz →
                              count0⇒∉dom
                                (join p/s (join d (` zero) (` suc zero)) (𝐂S.wk (𝐂S.wk γ₂)))
                                (count-join-PS p/s (suc (suc z))
                                   (join d (` zero) (` suc zero)) (𝐂S.wk (𝐂S.wk γ₂))
                                 ■ cong₂ _+_
                                     (count-join-Dir d (suc (suc z)) (` zero) (` suc zero))
                                     (count-wk-suc (𝐂S.wk γ₂) (suc z)
                                      ■ count-wk-suc γ₂ z ■ zer z hz)) })
        in (L._∷_ (`let⊗-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let⊗-`in_ e₂eq) E'eq)
strengthen-frame* (L._∷_ (`inj□ i) E') ⊢E =
  let _ , _ , ⊢inner = inv-injᶠ ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢inner
  in β , pt , support' ,
     (λ ρ H inv Hu Hc →
        let E₀' , E'eq = factor' ρ H inv Hu Hc
        in (L._∷_ (`inj□ i) E₀') , cong₂ L._∷_ refl E'eq)
strengthen-frame* (L._∷_ (`case□`of⟨ e₁ ; e₂ ⟩) E') ⊢E =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e) , (_ , _ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = inv-case ⊢E
      β , pt , support' , factor' = strengthen-frame* E' ⊢e
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ ρ H inv Hu Hc →
        let rec = λ h hh → ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h (Hu h hh))) (Hc h hh)
            zer = λ h hh → +≤ˡ⇒0 (count h γ₁)
                    (≤-trans (≤-trans (cle h (Hu h hh)) (Hc h hh)) (support' h (Hu h hh)))
            E₀' , E'eq = factor' ρ H inv Hu rec
            ∉br = λ (z : 𝔽 _) hz →
                    count0⇒∉dom (join p/s (` zero) (𝐂S.wk γ₂))
                      (count-join-PS p/s (suc z) (` zero) (𝐂S.wk γ₂)
                       ■ count-wk-suc γ₂ z ■ zer z hz)
            e₁₀ , e₁eq = strengthen-Tm-gen* ⊢e₁ (ρ ↑) (H↑ H) (invH↑ inv)
                           (λ { (suc z) hz → ∉br z hz })
            e₂₀ , e₂eq = strengthen-Tm-gen* ⊢e₂ (ρ ↑) (H↑ H) (invH↑ inv)
                           (λ { (suc z) hz → ∉br z hz })
        in (L._∷_ (`case□`of⟨ e₁₀ ; e₂₀ ⟩) E₀') ,
           cong₂ L._∷_ (cong₂ (λ u₁ u₂ → `case□`of⟨ u₁ ; u₂ ⟩) e₁eq e₂eq) E'eq)

------------------------------------------------------------------------
-- 2.  The two-variable thinnings.

-- `Inverter*` is contravariant in the missing set.
inv*-weaken : ∀ {k N} {ρ : k →ᵣ N} {H H′ : 𝔽 N → Set} →
  (∀ y → H y → H′ y) → Inverter* ρ H → Inverter* ρ H′
inv*-weaken sub inv y ¬H′ = inv y (λ Hy → ¬H′ (sub y Hy))

-- A single-variable `Inverter` IS a set-`Inverter` for the singleton.
inv⇒inv* : ∀ {k N} {ρ : k →ᵣ N} {h : 𝔽 N} → Inverter ρ h → Inverter* ρ (λ y → y ≡ h)
inv⇒inv* inv y ¬e = inv y ¬e

-- Composing two thinnings: the outer one's gap, plus the image of the inner
-- one's gap.
inv*-∘ : ∀ {k N₁ N₂} {f : k →ᵣ N₁} {g : N₁ →ᵣ N₂}
  {H₁ : 𝔽 N₁ → Set} {H₂ : 𝔽 N₂ → Set} {H : 𝔽 N₂ → Set} →
  Inverter* f H₁ → Inverter* g H₂ →
  (∀ y → H₂ y → H y) → (∀ w → H₁ w → H (g w)) →
  Inverter* (λ z → g (f z)) H
inv*-∘ {g = g} {H = H} invf invg h2 h1 y ¬Hy =
  let w , eqw = invg y (λ H₂y → ¬Hy (h2 y H₂y))
      y₀ , eq = invf w (λ H₁w → ¬Hy (subst H eqw (h1 w H₁w)))
  in y₀ , (cong g eq ■ eqw)

module _ (a c : ℕ) {n : ℕ} where
  private
    eq₀ : 0 + suc (a + c + n) ≡ suc (a + (c + n))
    eq₀ = cong suc (+-assoc a c n)
    eq₁ : suc a + suc (c + n) ≡ suc a + suc c + n
    eq₁ = sym (+-assoc (suc a) (suc c) n)

  -- The second gap of `wkₚ a c`: the head of the SECOND endpoint.
  wkₚ-gap₂ : 𝔽 (suc a + suc c + n)
  wkₚ-gap₂ = Fin.cast eq₁ (suc a ↑ʳ (Fin.zero {c + n}))

  wkₚ-gap₂-eq :
    wkₚ-gap₂ ≡ wkʳ ⦃ Kᵣ ⦄ n (wkˡ ⦃ Kᵣ ⦄ (suc a) (Fin.zero {c}))
  wkₚ-gap₂-eq = Fin.toℕ-injective
    ( toℕ-cast eq₁ (suc a ↑ʳ (Fin.zero {c + n}))
      ■ toℕ-↑ʳ (suc a) (Fin.zero {c + n})
      ■ sym ( toℕ-↑ˡ (suc a ↑ʳ (Fin.zero {c})) n
              ■ toℕ-↑ʳ (suc a) (Fin.zero {c}) ) )

  -- `wkₚ a c` IS the composition of two `mk-thin`s (definitionally: the
  -- `Fin.cast` proofs are irrelevant and `_↑* 0` is the identity), so it
  -- inherits their inverters.
  inv-wkₚ :
    Inverter* (wkₚ {n} a c) (λ y → (y ≡ 0F) ⊎ (y ≡ wkₚ-gap₂))
  inv-wkₚ =
    inv*-∘ {f = proj₁ (mk-thin 0 (a + c + n) eq₀)}
           {g = proj₁ (mk-thin (suc a) (c + n) eq₁)}
      (inv⇒inv* (proj₁ (proj₂ (mk-thin 0 (a + c + n) eq₀))))
      (inv⇒inv* (proj₁ (proj₂ (mk-thin (suc a) (c + n) eq₁))))
      (λ y e → inj₂ e)
      (λ w e → inj₁ (cong (proj₁ (mk-thin (suc a) (c + n) eq₁)) e))

  wkₚ-≗ : (y : 𝔽 (a + c + n)) →
    proj₁ (mk-thin (suc a) (c + n) eq₁) (proj₁ (mk-thin 0 (a + c + n) eq₀) y)
      ≡ wkₚ {n} a c y
  wkₚ-≗ y = refl

module _ {m : ℕ} where
  -- The `R-Close` thinning: `weaken* 2`, skipping `0F` and `1F`.
  private
    thin₂ : m →ᵣ suc (suc m)
    thin₂ y = proj₁ (mk-thin 0 (suc m) refl) (proj₁ (mk-thin 0 m refl) y)

  inv-weaken*2 : Inverter* thin₂ (λ y → (y ≡ 0F) ⊎ (y ≡ 1F))
  inv-weaken*2 =
    inv*-∘ {f = proj₁ (mk-thin 0 m refl)} {g = proj₁ (mk-thin 0 (suc m) refl)}
      (inv⇒inv* (proj₁ (proj₂ (mk-thin 0 m refl))))
      (inv⇒inv* (proj₁ (proj₂ (mk-thin 0 (suc m) refl))))
      (λ y e → inj₁ e)
      (λ w e → inj₂ (cong (proj₁ (mk-thin 0 (suc m) refl)) e))

  weaken*2-≗ : (y : 𝔽 m) → thin₂ y ≡ weaken* ⦃ Kᵣ ⦄ 2 y
  weaken*2-≗ y =
    Fin.cast-is-id refl (weakenᵣ (Fin.cast refl (weakenᵣ y)))
    ■ cong weakenᵣ (Fin.cast-is-id refl (weakenᵣ y))
    ■ sym (weaken*~wkˡ ⦃ Kᵣ ⦄ 2 y)

------------------------------------------------------------------------
-- 3.  The two handles in the body structure of `TP-Res`.
--
-- `HeadConfine.count-handle-head` already does the FIRST endpoint's head
-- (variable `0F`); this is its mirror image on the second endpoint.

count-handle-snd : ∀ (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) {m} (γ : Struct m) →
  count ((sum (suc b₁ ∷ B₁) ↑ʳ (Fin.zero {b₂ + sum B₂})) ↑ˡ m)
    ( (structBinder (suc b₁ ∷ B₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (suc b₂ ∷ B₂)) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder (suc b₂ ∷ B₂) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (suc b₁ ∷ B₁)) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) )
  ≡ 1
count-handle-snd b₁ b₂ B₁ B₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = suc b₁ ∷ B₁
    C₂ : BindGroup
    C₂ = suc b₂ ∷ B₂
    loc : 𝔽 (sum C₁ + sum C₂)
    loc = sum C₁ ↑ʳ (Fin.zero {b₂ + sum B₂})
    h : 𝔽 (sum C₁ + sum C₂ + m)
    h = loc ↑ˡ m
    partA : count h (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) loc
          ■ count-⋯ᵣwkʳ-↑ʳ (sum C₂) (structBinder C₁) (Fin.zero {b₂ + sum B₂})
    partB : count h (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) loc
          ■ cong (count loc) (⋯ᵣwkˡ≡⋯weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-shift (sum C₁) (structBinder C₂) (Fin.zero {b₂ + sum B₂})
          ■ count-structBinder-lt C₂ (Fin.zero {b₂ + sum B₂}) (s≤s z≤n)
    toℕh : Fin.toℕ h ≡ sum C₁
    toℕh = toℕ-↑ˡ loc m ■ toℕ-↑ʳ (sum C₁) (Fin.zero {b₂ + sum B₂})
         ■ +-identityʳ (sum C₁)
    h< : Fin.toℕ h < sum C₁ + sum C₂
    h< = subst (Nat._< sum C₁ + sum C₂) (sym toℕh)
           (subst (Nat._≤ sum C₁ + sum C₂) (+-comm (sum C₁) 1)
             (+-monoʳ-≤ (sum C₁) {1} {sum C₂} (s≤s z≤n)))
    partC : count h (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ h h<

------------------------------------------------------------------------
-- 4.  The two confinement lemmas.

PairConfined : ∀ {m} (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (E₁ E₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m))
  (v : Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m))
  (P : 𝐓.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) → Set
PairConfined {m} b₁ b₂ B₁ B₂ E₁ E₂ v P =
  Σ (Frame* ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ E₁₀ →
    (E₁ ≡ E₁₀ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
  × Σ (Frame* ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ E₂₀ →
    (E₂ ≡ E₂₀ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
  × Σ (Tm ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ v₀ →
    (v ≡ v₀ ⋯ wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
  × Σ (𝐓.Proc ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ P₀ →
    P ≡ P₀ 𝐓.⋯ₚ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)

ClosePairConfined : ∀ {m} (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (E₁ E₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m))
  (P : 𝐓.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) → Set
ClosePairConfined {m} b₁ b₂ B₁ B₂ E₁ E₂ P =
  Σ (Frame* ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ E₁₀ →
    (E₁ ≡ E₁₀ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
  × Σ (Frame* ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ E₂₀ →
    (E₂ ≡ E₂₀ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
  × Σ (𝐓.Proc ((b₁ + sum B₁) + (b₂ + sum B₂) + m)) λ P₀ →
    P ≡ P₀ 𝐓.⋯ₚ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)

-- The `R-Com` handle of the SECOND endpoint, exactly as the rule writes it.
comHandle : ∀ (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) {m} →
  𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
comHandle b₁ b₂ B₁ B₂ {m} =
  wkʳ ⦃ Kᵣ ⦄ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

com-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  {E₁ E₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
  {v : Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
  {P : 𝐓.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
    ((𝐓.⟪ E₁ [ K `send ·¹ (v ⊗ (` 0F)) ]* ⟫
      𝐓.∥ 𝐓.⟪ E₂ [ K `recv ·¹ (` comHandle b₁ b₂ B₁ B₂) ]* ⟫)
     𝐓.∥ P) →
  PairConfined b₁ b₂ B₁ B₂ E₁ E₂ v P
com-confine {m = m} Γ-S {γ = γ} {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
            {E₁ = E₁} {E₂ = E₂} {v = v} {P = P} ⊢ν =
  let
    Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body = inv-ν ⊢ν
    Γ-body = ++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
    ¬u : (h : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) →
         ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    ¬u h u = ¬unr-handle (subst Unr (proj₂ (chanCx-lookup Γ-body h)) u)
    h₁ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    h₁ = 0F
    h₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    h₂ = comHandle b₁ b₂ B₁ B₂
    cγ₁ = count-handle-head b₁ B₁ (suc b₂ ∷ B₂) γ
    cγ₂ = count-handle-snd b₁ b₂ B₁ B₂ γ
    αβ , δ , αβδ≼ , ⊢pair , ⊢resid = inv-∥ ⊢body
    α , β , αβ≼ , ⊢th₁ , ⊢th₂ = inv-∥ ⊢pair
    β₁ , (_ , _ , ⊢plug₁) , support₁ , factor₁ = strengthen-frame* E₁ (inv-⟪⟫ ⊢th₁)
    β₂ , (_ , _ , ⊢plug₂) , support₂ , factor₂ = strengthen-frame* E₂ (inv-⟪⟫ ⊢th₂)
    αfn₁ , αarg₁ , _ , (_ , _ , ⊢arg₁) , cle₁ = inv-app ⊢plug₁
    αv , αx , (_ , _ , ⊢v) , (_ , _ , ⊢x) , cle₁′ = inv-pair ⊢arg₁
    αfn₂ , αarg₂ , _ , (_ , _ , ⊢y) , cle₂ = inv-app ⊢plug₂
    -- thread 1 owns h₁
    1≤αx = subst (Nat._≤ count h₁ αx) (count-self h₁) (inv-var-count ⊢x h₁ (¬u h₁))
    1≤β₁ = ≤-trans 1≤αx
             (≤-trans (m≤n+m (count h₁ αx) (count h₁ αv))
               (≤-trans (cle₁′ h₁ (¬u h₁))
                 (≤-trans (m≤n+m (count h₁ αarg₁) (count h₁ αfn₁)) (cle₁ h₁ (¬u h₁)))))
    1≤α = ≤-trans 1≤β₁ (support₁ h₁ (¬u h₁))
    -- thread 2 owns h₂
    1≤αarg₂ = subst (Nat._≤ count h₂ αarg₂) (count-self h₂) (inv-var-count ⊢y h₂ (¬u h₂))
    1≤β₂ = ≤-trans 1≤αarg₂
             (≤-trans (m≤n+m (count h₂ αarg₂) (count h₂ αfn₂)) (cle₂ h₂ (¬u h₂)))
    1≤β = ≤-trans 1≤β₂ (support₂ h₂ (¬u h₂))
    -- the linear budget of each handle in the whole body
    bud₁ = subst (count h₁ αβ + count h₁ δ Nat.≤_) cγ₁ (≼⇒count≤ (¬u h₁) αβδ≼)
    bud₂ = subst (count h₂ αβ + count h₂ δ Nat.≤_) cγ₂ (≼⇒count≤ (¬u h₂) αβδ≼)
    spl₁ = ≼⇒count≤ (¬u h₁) αβ≼
    spl₂ = ≼⇒count≤ (¬u h₂) αβ≼
    1≤αβ₁ = ≤-trans 1≤α (≤-trans (m≤m+n (count h₁ α) (count h₁ β)) spl₁)
    1≤αβ₂ = ≤-trans 1≤β (≤-trans (m≤n+m (count h₂ β) (count h₂ α)) spl₂)
    αβ≤1₁ = ≤-trans (m≤m+n (count h₁ αβ) (count h₁ δ)) bud₁
    αβ≤1₂ = ≤-trans (m≤m+n (count h₂ αβ) (count h₂ δ)) bud₂
    cδ₁0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₁ δ) 1≤αβ₁) bud₁))
    cδ₂0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₂ δ) 1≤αβ₂) bud₂))
    cβ₁0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₁ β) 1≤α) (≤-trans spl₁ αβ≤1₁)))
    cα₂0 = n≤0⇒n≡0 (s≤s⁻¹
             (subst (Nat._≤ 1) (+-comm (count h₂ α) 1)
               (≤-trans (+-monoʳ-≤ (count h₂ α) 1≤β) (≤-trans spl₂ αβ≤1₂))))
    α≤1₁ = ≤-trans (m≤m+n (count h₁ α) (count h₁ β)) (≤-trans spl₁ αβ≤1₁)
    β≤1₂ = ≤-trans (m≤n+m (count h₂ β) (count h₂ α)) (≤-trans spl₂ αβ≤1₂)
    -- the missing set and its inverter
    H : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m) → Set
    H y = (y ≡ h₁) ⊎ (y ≡ h₂)
    inv : Inverter* (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H
    inv = inv*-weaken
            (λ y → λ { (inj₁ e) → inj₁ e
                     ; (inj₂ e) → inj₂ (e ■ wkₚ-gap₂-eq (b₁ + sum B₁) (b₂ + sum B₂)) })
            (inv-wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
    Hu : (h : 𝔽 _) → H h → ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    Hu h _ = ¬u h
    Hc₁ : (h : 𝔽 _) → H h → count h α ≤ count h β₁
    Hc₁ = λ { h (inj₁ refl) → ≤-trans α≤1₁ 1≤β₁
            ; h (inj₂ refl) → subst (Nat._≤ count h₂ β₁) (sym cα₂0) z≤n }
    Hc₂ : (h : 𝔽 _) → H h → count h β ≤ count h β₂
    Hc₂ = λ { h (inj₁ refl) → subst (Nat._≤ count h₁ β₂) (sym cβ₁0) z≤n
            ; h (inj₂ refl) → ≤-trans β≤1₂ 1≤β₂ }
    E₁₀ , E₁eq = factor₁ (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv Hu Hc₁
    E₂₀ , E₂eq = factor₂ (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv Hu Hc₂
    -- the sent value avoids both handles
    cαv≤β₁ : (h : 𝔽 _) → count h αv + count h αx ≤ count h β₁
    cαv≤β₁ h = ≤-trans (cle₁′ h (¬u h))
                 (≤-trans (m≤n+m (count h αarg₁) (count h αfn₁)) (cle₁ h (¬u h)))
    cv₁0 = n≤0⇒n≡0 (s≤s⁻¹
             (subst (Nat._≤ 1) (+-comm (count h₁ αv) 1)
               (≤-trans (+-monoʳ-≤ (count h₁ αv) 1≤αx)
                 (≤-trans (cαv≤β₁ h₁) (≤-trans (support₁ h₁ (¬u h₁)) α≤1₁)))))
    cv₂0 = n≤0⇒n≡0
             (subst (count h₂ αv Nat.≤_) cα₂0
               (≤-trans (m≤m+n (count h₂ αv) (count h₂ αx))
                 (≤-trans (cαv≤β₁ h₂) (support₁ h₂ (¬u h₂)))))
    v₀ , veq = strengthen-Tm-gen* ⊢v (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv
                 (λ { z (inj₁ refl) → count0⇒∉dom αv cv₁0
                    ; z (inj₂ refl) → count0⇒∉dom αv cv₂0 })
    P₀ , Peq = strengthen-Proc-gen* ⊢resid (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv
                 (λ { z (inj₁ refl) → count0⇒∉dom δ cδ₁0
                    ; z (inj₂ refl) → count0⇒∉dom δ cδ₂0 })
  in E₁₀ , E₁eq , E₂₀ , E₂eq , v₀ , veq , P₀ , Peq

close-pair-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  {E₁ E₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
  {P : 𝐓.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
    ((𝐓.⟪ E₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
      𝐓.∥ 𝐓.⟪ E₂ [ K (`end ⁇) ·¹ (` comHandle b₁ b₂ B₁ B₂) ]* ⟫)
     𝐓.∥ P) →
  ClosePairConfined b₁ b₂ B₁ B₂ E₁ E₂ P
close-pair-confine {m = m} Γ-S {γ = γ} {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂}
                  {E₁ = E₁} {E₂ = E₂} {P = P} ⊢ν =
  let
    Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body = inv-ν ⊢ν
    Γ-body = ++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
    ¬u : (h : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) →
         ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    ¬u h u = ¬unr-handle (subst Unr (proj₂ (chanCx-lookup Γ-body h)) u)
    h₁ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    h₁ = 0F
    h₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)
    h₂ = comHandle b₁ b₂ B₁ B₂
    cγ₁ = count-handle-head b₁ B₁ (suc b₂ ∷ B₂) γ
    cγ₂ = count-handle-snd b₁ b₂ B₁ B₂ γ
    αβ , δ , αβδ≼ , ⊢pair , ⊢resid = inv-∥ ⊢body
    α , β , αβ≼ , ⊢th₁ , ⊢th₂ = inv-∥ ⊢pair
    β₁ , (_ , _ , ⊢plug₁) , support₁ , factor₁ = strengthen-frame* E₁ (inv-⟪⟫ ⊢th₁)
    β₂ , (_ , _ , ⊢plug₂) , support₂ , factor₂ = strengthen-frame* E₂ (inv-⟪⟫ ⊢th₂)
    αfn₁ , αarg₁ , _ , (_ , _ , ⊢x) , cle₁ = inv-app ⊢plug₁
    αfn₂ , αarg₂ , _ , (_ , _ , ⊢y) , cle₂ = inv-app ⊢plug₂
    -- thread 1 owns h₁
    1≤αarg₁ = subst (Nat._≤ count h₁ αarg₁) (count-self h₁) (inv-var-count ⊢x h₁ (¬u h₁))
    1≤β₁ = ≤-trans 1≤αarg₁
             (≤-trans (m≤n+m (count h₁ αarg₁) (count h₁ αfn₁)) (cle₁ h₁ (¬u h₁)))
    1≤α = ≤-trans 1≤β₁ (support₁ h₁ (¬u h₁))
    -- thread 2 owns h₂
    1≤αarg₂ = subst (Nat._≤ count h₂ αarg₂) (count-self h₂) (inv-var-count ⊢y h₂ (¬u h₂))
    1≤β₂ = ≤-trans 1≤αarg₂
             (≤-trans (m≤n+m (count h₂ αarg₂) (count h₂ αfn₂)) (cle₂ h₂ (¬u h₂)))
    1≤β = ≤-trans 1≤β₂ (support₂ h₂ (¬u h₂))
    -- the linear budget of each handle in the whole body
    bud₁ = subst (count h₁ αβ + count h₁ δ Nat.≤_) cγ₁ (≼⇒count≤ (¬u h₁) αβδ≼)
    bud₂ = subst (count h₂ αβ + count h₂ δ Nat.≤_) cγ₂ (≼⇒count≤ (¬u h₂) αβδ≼)
    spl₁ = ≼⇒count≤ (¬u h₁) αβ≼
    spl₂ = ≼⇒count≤ (¬u h₂) αβ≼
    1≤αβ₁ = ≤-trans 1≤α (≤-trans (m≤m+n (count h₁ α) (count h₁ β)) spl₁)
    1≤αβ₂ = ≤-trans 1≤β (≤-trans (m≤n+m (count h₂ β) (count h₂ α)) spl₂)
    αβ≤1₁ = ≤-trans (m≤m+n (count h₁ αβ) (count h₁ δ)) bud₁
    αβ≤1₂ = ≤-trans (m≤m+n (count h₂ αβ) (count h₂ δ)) bud₂
    cδ₁0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₁ δ) 1≤αβ₁) bud₁))
    cδ₂0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₂ δ) 1≤αβ₂) bud₂))
    cβ₁0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₁ β) 1≤α) (≤-trans spl₁ αβ≤1₁)))
    cα₂0 = n≤0⇒n≡0 (s≤s⁻¹
             (subst (Nat._≤ 1) (+-comm (count h₂ α) 1)
               (≤-trans (+-monoʳ-≤ (count h₂ α) 1≤β) (≤-trans spl₂ αβ≤1₂))))
    α≤1₁ = ≤-trans (m≤m+n (count h₁ α) (count h₁ β)) (≤-trans spl₁ αβ≤1₁)
    β≤1₂ = ≤-trans (m≤n+m (count h₂ β) (count h₂ α)) (≤-trans spl₂ αβ≤1₂)
    H : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m) → Set
    H y = (y ≡ h₁) ⊎ (y ≡ h₂)
    inv : Inverter* (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H
    inv = inv*-weaken
            (λ y → λ { (inj₁ e) → inj₁ e
                     ; (inj₂ e) → inj₂ (e ■ wkₚ-gap₂-eq (b₁ + sum B₁) (b₂ + sum B₂)) })
            (inv-wkₚ (b₁ + sum B₁) (b₂ + sum B₂))
    Hu : (h : 𝔽 _) → H h → ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    Hu h _ = ¬u h
    Hc₁ : (h : 𝔽 _) → H h → count h α ≤ count h β₁
    Hc₁ = λ { h (inj₁ refl) → ≤-trans α≤1₁ 1≤β₁
            ; h (inj₂ refl) → subst (Nat._≤ count h₂ β₁) (sym cα₂0) z≤n }
    Hc₂ : (h : 𝔽 _) → H h → count h β ≤ count h β₂
    Hc₂ = λ { h (inj₁ refl) → subst (Nat._≤ count h₁ β₂) (sym cβ₁0) z≤n
            ; h (inj₂ refl) → ≤-trans β≤1₂ 1≤β₂ }
    E₁₀ , E₁eq = factor₁ (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv Hu Hc₁
    E₂₀ , E₂eq = factor₂ (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv Hu Hc₂
    P₀ , Peq = strengthen-Proc-gen* ⊢resid (wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) H inv
                 (λ { z (inj₁ refl) → count0⇒∉dom δ cδ₁0
                    ; z (inj₂ refl) → count0⇒∉dom δ cδ₂0 })
  in E₁₀ , E₁eq , E₂₀ , E₂eq , P₀ , Peq

close-confine : ∀ {m} {Γ : Ctx m} → ChanCx Γ → {γ : Struct m}
  {E₁ E₂ : Frame* (1 + 1 + m)} →
  Γ ; γ ⊢ₚ 𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ E₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
     𝐓.∥ 𝐓.⟪ E₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫) →
  Σ (Frame* m) (λ E₁₀ → E₁ ≡ E₁₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2)
  × Σ (Frame* m) (λ E₂₀ → E₂ ≡ E₂₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2)
close-confine {m = m} Γ-S {γ = γ} {E₁ = E₁} {E₂ = E₂} ⊢ν =
  let
    Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body = inv-ν ⊢ν
    Γ-body = ++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
    ¬u : (h : 𝔽 (1 + 1 + m)) → ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    ¬u h u = ¬unr-handle (subst Unr (proj₂ (chanCx-lookup Γ-body h)) u)
    h₁ : 𝔽 (1 + 1 + m)
    h₁ = 0F
    h₂ : 𝔽 (1 + 1 + m)
    h₂ = 1F
    cγ₁ = count-handle-head 0 [] (1 ∷ []) γ
    cγ₂ = count-handle-snd 0 0 [] [] γ
    α , β , αβ≼ , ⊢th₁ , ⊢th₂ = inv-∥ ⊢body
    β₁ , (_ , _ , ⊢plug₁) , support₁ , factor₁ = strengthen-frame* E₁ (inv-⟪⟫ ⊢th₁)
    β₂ , (_ , _ , ⊢plug₂) , support₂ , factor₂ = strengthen-frame* E₂ (inv-⟪⟫ ⊢th₂)
    αfn₁ , αarg₁ , _ , (_ , _ , ⊢x) , cle₁ = inv-app ⊢plug₁
    αfn₂ , αarg₂ , _ , (_ , _ , ⊢y) , cle₂ = inv-app ⊢plug₂
    1≤αarg₁ = subst (Nat._≤ count h₁ αarg₁) (count-self h₁) (inv-var-count ⊢x h₁ (¬u h₁))
    1≤β₁ = ≤-trans 1≤αarg₁
             (≤-trans (m≤n+m (count h₁ αarg₁) (count h₁ αfn₁)) (cle₁ h₁ (¬u h₁)))
    1≤α = ≤-trans 1≤β₁ (support₁ h₁ (¬u h₁))
    1≤αarg₂ = subst (Nat._≤ count h₂ αarg₂) (count-self h₂) (inv-var-count ⊢y h₂ (¬u h₂))
    1≤β₂ = ≤-trans 1≤αarg₂
             (≤-trans (m≤n+m (count h₂ αarg₂) (count h₂ αfn₂)) (cle₂ h₂ (¬u h₂)))
    1≤β = ≤-trans 1≤β₂ (support₂ h₂ (¬u h₂))
    bud₁ = subst (count h₁ α + count h₁ β Nat.≤_) cγ₁ (≼⇒count≤ (¬u h₁) αβ≼)
    bud₂ = subst (count h₂ α + count h₂ β Nat.≤_) cγ₂ (≼⇒count≤ (¬u h₂) αβ≼)
    cβ₁0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count h₁ β) 1≤α) bud₁))
    cα₂0 = n≤0⇒n≡0 (s≤s⁻¹
             (subst (Nat._≤ 1) (+-comm (count h₂ α) 1)
               (≤-trans (+-monoʳ-≤ (count h₂ α) 1≤β) bud₂)))
    α≤1₁ = ≤-trans (m≤m+n (count h₁ α) (count h₁ β)) bud₁
    β≤1₂ = ≤-trans (m≤n+m (count h₂ β) (count h₂ α)) bud₂
    H : 𝔽 (1 + 1 + m) → Set
    H y = (y ≡ h₁) ⊎ (y ≡ h₂)
    inv₀ : Inverter* (weaken* ⦃ Kᵣ ⦄ 2) H
    inv₀ = λ y ¬Hy →
      let y₀ , e = inv-weaken*2 {m} y ¬Hy in y₀ , (sym (weaken*2-≗ {m} y₀) ■ e)
    Hu : (h : 𝔽 _) → H h → ¬ Unr (lookup ((Γ₁ ⸴* Γ₂) ⸴* _) h)
    Hu h _ = ¬u h
    Hc₁ : (h : 𝔽 _) → H h → count h α ≤ count h β₁
    Hc₁ = λ { h (inj₁ refl) → ≤-trans α≤1₁ 1≤β₁
            ; h (inj₂ refl) → subst (Nat._≤ count h₂ β₁) (sym cα₂0) z≤n }
    Hc₂ : (h : 𝔽 _) → H h → count h β ≤ count h β₂
    Hc₂ = λ { h (inj₁ refl) → subst (Nat._≤ count h₁ β₂) (sym cβ₁0) z≤n
            ; h (inj₂ refl) → ≤-trans β≤1₂ 1≤β₂ }
    E₁₀ , E₁eq = factor₁ (weaken* ⦃ Kᵣ ⦄ 2) H inv₀ Hu Hc₁
    E₂₀ , E₂eq = factor₂ (weaken* ⦃ Kᵣ ⦄ 2) H inv₀ Hu Hc₂
  in (E₁₀ , E₁eq) , (E₂₀ , E₂eq)
