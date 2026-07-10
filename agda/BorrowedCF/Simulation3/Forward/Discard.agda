-- | Forward simulation, R-Discard.  The administrative term-consuming discard.
--   Fire RU-Discard on the translated thread (lifted through ν and the UB
--   telescope via UB-cong-─→ — a SINGLE untyped step), then the binder-shrink
--   ≋ back-bridge (disc-single / disc-multi).  b₁ = 0 / B₁ nonempty is vacuous
--   (disc-b0-vac, via the typing).  Ported single-step from the old Theorems
--   R-Discard case; the helpers it needs are copied in below (their home,
--   Theorems.agda, is the broken forward monolith).
module BorrowedCF.Simulation3.Forward.Discard where

open import BorrowedCF.Simulation3.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation3.Support.Frames using (frame-plug*; frame-plug₁; frame*-⋯; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation3.Support.TranslationProperties
  using (≡→≋; UB-cong; UB-cong-─→; U-⋯ₚ; U-cong; ≋-subst)
open import BorrowedCF.Simulation3.Support.InvFrame using (strengthen-frame; arg-type)

open TP using (cons-ret/acq; cons; nil)

frame-plug*ᵣ : ∀ {m p} (E : Frame* m) {t : Tm m} (ρ : m →ᵣ p) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
⟨⟩≃ ⟨ eq ⟩ = eq

-- discard : ⟨ skip ⟩ →*M ⊤ — the discarded handle is forced ≅ ⟨ skip ⟩.
fn-discard-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `discard ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ⟨ skip ⟩ ≃ Tᵈ
fn-discard-dom (T-Const `discard)       = ≃-refl
fn-discard-dom (T-Conv (dom≃ `→ _) _ d) = ≃-trans (fn-discard-dom d) dom≃
fn-discard-dom (T-Weaken _ d)           = fn-discard-dom d

discard-handle-≃skip : ∀ {N} {Δ : Ctx N}{β}{x : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `discard ·¹ (` x) ∶ U ∣ ϵ
  → Δ x ≃ ⟨ skip ⟩
discard-handle-≃skip (T-AppUnr _ _ ⊢fn ⊢arg) = ≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))
discard-handle-≃skip (T-AppLin _ _ ⊢fn ⊢arg) = ≃-trans (arg-type ⊢arg) (≃-sym (fn-discard-dom ⊢fn))
discard-handle-≃skip (T-Conv _ _ d)          = discard-handle-≃skip d
discard-handle-≃skip (T-Weaken _ d)          = discard-handle-≃skip d

disc-b0-vac :
  {m : ℕ} {Γ : Ctx m} {g : Struct m} {x : ℕ} {xs B₂ : TP.BindGroup}
  {E : Frame* (sum (zero ∷ x ∷ xs) + sum B₂ + m)}
  {P : TP.Proc (sum (zero ∷ x ∷ xs) + sum B₂ + m)}
  → Γ ; g ⊢ₚ TP.ν (suc zero ∷ x ∷ xs) B₂
      (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) → ⊥
disc-b0-vac {E = E} ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , _ , _ , _
    , cons-ret/acq _ scra Γ≗ (cons s1ʰ s2ʰ ¬sk1 s≃1 Γ≗1 (nil skB)) tail
    , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢discT , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢discT)
... | _ , (_ , _ , ⊢plug) , _ , _
  = ¬sk1 (≃-skips s≃1 (Ss1 Skips.; skB))
  where
    head≃skip : s1ʰ ≃ skip
    head≃skip = ⟨⟩≃ (≃-trans (≃-reflexive (sym (sym (Γ≗ 0F) ■ sym (Γ≗1 0F)))) (discard-handle-≃skip ⊢plug))
    Ss1 : Skips s1ʰ
    Ss1 = ≃-skips (≃-sym head≃skip) Skips.skip


block-shift : ∀ p {A B N} (bL : suc p →ₛ N) (bR : p →ₛ N)
              (eq : ∀ k → bL (suc k) ≡ bR k)
              (ts : A →ₛ N) (rs : B →ₛ N) (i : 𝔽 (p + A + B)) →
              ((bL ++ₛ ts) ++ₛ rs) (suc i) ≡ ((bR ++ₛ ts) ++ₛ rs) i
block-shift p {A} {B} bL bR eq ts rs i with splitAt (p + A) i
... | inj₂ k = refl
... | inj₁ j with splitAt p j
... | inj₁ k = eq k
... | inj₂ k = refl

-- On a STAR-triple (*, c, *) both cut-slots are already *, so Ub[ b ] is the
-- constant chanTriple at every index — but Agda cannot see this for an abstract
-- b (Ub[_] is stuck on the numeral).  Prove it by induction on b.
Ub-star-const : ∀ b {N} (c : 𝔽 N) (x : 𝔽 b) →
                Ub[ b ] (* , c , *) x ≡ chanTriple (* , c , *)
Ub-star-const zero          c ()
Ub-star-const (suc zero)    c 0F      = refl
Ub-star-const (suc (suc b)) c 0F      = refl
Ub-star-const (suc (suc b)) c (suc x) = Ub-star-const (suc b) c x

-- Distributing-head one-level shift: the head block of a MULTI bind group is
-- Ub[ b ] (*, c, e₂), which is NOT constant (its e₂ cut-slot only survives at
-- the last index).  Dropping one borrow shifts Ub[ suc (suc b) ] ↦ Ub[ suc b ];
-- the two agree pointwise because Ub[ suc (suc b) ] (*,c,e₂) (suc k) reduces to
-- Ub[ suc b ] (*,c,e₂) k definitionally (third defining clause of Ub[_]).
ub-inner-shift : ∀ b {N N′ A} (c : 𝔽 N) (e₂ : Tm N) (w′ : N →ᵣ N′)
                 (ts : A →ₛ N′) (k : 𝔽 (suc b + A)) →
  ((λ j → Ub[ suc (suc b) ] (* , c , e₂) j ⋯ w′) ++ₛ ts) (suc k)
    ≡ ((λ j → Ub[ suc b ] (* , c , e₂) j ⋯ w′) ++ₛ ts) k
ub-inner-shift b c e₂ w′ ts k with splitAt (suc b) k
... | inj₁ k′ = refl
... | inj₂ k″ = refl

-- Single-chain case (B₁ = []).
disc-single : (b : ℕ) (B₂ : TP.BindGroup)
              (P : TP.Proc (sum (b ∷ []) + sum B₂ + n))
              (σ : n →ₛ m)
            → U[ TP.ν (suc b ∷ []) B₂ (P TP.⋯ₚ weakenᵣ) ] σ
                UP.≋ U[ TP.ν (b ∷ []) B₂ P ] σ
disc-single b B₂ P σ =
  UP.ν-cong (UB-cong B₂ (* , 1F , *) (λ τ₂ →
    ≡→≋ (U-⋯ₚ P ■ U-cong P (λ i →
      block-shift (b + 0)
        (λ j → Ub[ suc b + 0 ] (* , 0F , *) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        (λ j → Ub[ b + 0 ] (* , 0F , *) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        (λ k → cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
                 (Ub-star-const (suc b + 0) 0F (suc k)
                  ■ sym (Ub-star-const (b + 0) 0F k)))
        τ₂
        (λ j → σ j ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
        i))))

-- Multi case (b = suc b', B₁ nonempty).
disc-multi : (b' : ℕ) (x : ℕ) (xs : TP.BindGroup) (B₂ : TP.BindGroup)
             (P : TP.Proc (sum (suc b' ∷ x ∷ xs) + sum B₂ + n))
             (σ : n →ₛ m)
           → U[ TP.ν (suc (suc b') ∷ x ∷ xs) B₂ (P TP.⋯ₚ weakenᵣ) ] σ
               UP.≋ U[ TP.ν (suc b' ∷ x ∷ xs) B₂ P ] σ
disc-multi b' x xs B₂ P σ =
  UP.ν-cong (UP.φ-cong
    (UB-cong (x ∷ xs) ((` 0F) , 1F , *) (λ τ₁ →
      ≋-subst (sym (+-suc (syncs (x ∷ xs)) _))
        (UB-cong B₂ (* , wkmᵣ (weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) 1F , *) (λ τ₂ →
          ≡→≋ (U-⋯ₚ P ■ U-cong P (λ i →
            block-shift (suc b' + sum (x ∷ xs))
              (λ j → subst Tm (+-suc (syncs (x ∷ xs)) _)
                       ([ (λ k → Ub[ suc (suc b') ] (* , 1F , (` 0F)) k ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) , τ₁ ]′
                         (splitAt (suc (suc b')) j))
                     ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
              (λ j → subst Tm (+-suc (syncs (x ∷ xs)) _)
                       ([ (λ k → Ub[ suc b' ] (* , 1F , (` 0F)) k ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) , τ₁ ]′
                         (splitAt (suc b') j))
                     ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
              (λ k → cong (λ t → subst Tm (+-suc (syncs (x ∷ xs)) _) t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
                       (ub-inner-shift b' 1F (` 0F) (weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) τ₁ k))
              τ₂
              (λ j → σ j ⋯ wkmᵣ (wkmᵣ idᵣ) ⋯ wkmᵣ (weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
              i)))))))


-- Fire RU-Discard through ν and the UB telescope as a SINGLE untyped step
-- (UB-cong-─→ instead of the old UB-cong-⊎ dispatch); lands on the E[*] shape.
disc-fire-single : {m n : ℕ} (σ : m →ₛ n) → VSub σ → (b₁ : ℕ) (B₁ B₂ : TP.BindGroup)
            (E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m))
            (P : TP.Proc (sum (b₁ ∷ B₁) + sum B₂ + m))
          → U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
              UR.─→ₚ U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
disc-fire-single {m} {n} σ Vσ b₁ B₁ B₂ E P =
  UR.RU-Res
    (UB-cong-─→ (suc b₁ ∷ B₁) (* , 0F , *) (V-K , V-K)
      (λ σ₁ Vσ₁ → UB-cong-─→ B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₁)) 1F , *) (V-K , V-K)
        (λ σ₂ Vσ₂ → leaf-red σ₁ Vσ₁ σ₂ Vσ₂)))
  where
    C : TP.BindGroup
    C = suc b₁ ∷ B₁
    Ed : Frame* (sum C + sum B₂ + m)
    Ed = E ⋯ᶠ* weakenᵣ
    leafσ' : (σ₁ : sum C →ₛ syncs C + (2 + n))
             (σ₂ : sum B₂ →ₛ syncs B₂ + (syncs C + (2 + n)))
           → (sum C + sum B₂ + m →ₛ syncs B₂ + (syncs C + (2 + n)))
    leafσ' σ₁ σ₂ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ σ₂)
                  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs C) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
    leaf-red : (σ₁ : sum C →ₛ syncs C + (2 + n)) (Vσ₁ : VSub σ₁)
               (σ₂ : sum B₂ →ₛ syncs B₂ + (syncs C + (2 + n))) (Vσ₂ : VSub σ₂)
             → U[ TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ) ] (leafσ' σ₁ σ₂)
                 UR.─→ₚ U[ TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ) ] (leafσ' σ₁ σ₂)
    leaf-red σ₁ Vσ₁ σ₂ Vσ₂ = UR.RU-Par thread-red
      where
        Vleaf : VSub (leafσ' σ₁ σ₂)
        Vleaf = ++ₛ-VSub (++ₛ-VSub (weaken-VSub (syncs B₂) Vσ₁) Vσ₂)
                  (weaken-VSub (syncs B₂) (weaken-VSub (syncs C) (weaken-VSub 2 Vσ)))
        thread-red : UP.⟪ ((E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]*) ⋯ leafσ' σ₁ σ₂ ⟫
                       UR.─→ₚ UP.⟪ ((E ⋯ᶠ* weakenᵣ) [ * ]*) ⋯ leafσ' σ₁ σ₂ ⟫
        thread-red = subst₂ UR._─→ₚ_
            (sym (cong UP.⟪_⟫ (frame-plug* (E ⋯ᶠ* weakenᵣ) {t = K `discard ·¹ (` 0F)} (leafσ' σ₁ σ₂) Vleaf)))
            (sym (cong UP.⟪_⟫ (frame-plug* (E ⋯ᶠ* weakenᵣ) {t = *} (leafσ' σ₁ σ₂) Vleaf)))
            (UR.RU-Discard (frame*-⋯ (E ⋯ᶠ* weakenᵣ) (leafσ' σ₁ σ₂) Vleaf)
                           (value-⋯ (V-` {x = 0F}) (leafσ' σ₁ σ₂) Vleaf))


-- R-Discard, ported to a single untyped step.  RU-Struct wraps the
-- single-step fire (disc-fire-single) with the binder-shrink ≋ back-bridge;
-- b₁ = 0 / B₁ nonempty is vacuous (disc-b0-vac).
U-discard : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ → {g : Struct m}
  → {b₁ : ℕ} {B₁ B₂ : TP.BindGroup}
  → {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)} {P : TP.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)}
  → Γ ; g ⊢ₚ TP.ν (suc b₁ ∷ B₁) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ))
  → U[ TP.ν (suc b₁ ∷ B₁) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
      UR.─→ₚ U[ TP.ν (b₁ ∷ B₁) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
U-discard σ Vσ _ {b₁ = b₁} {B₁ = []} {B₂ = B₂} {E = E} {P = P} _ =
  UR.RU-Struct (≡→≋ refl) (disc-fire-single σ Vσ b₁ [] B₂ E P) back
  where
    back : U[ TP.ν (suc b₁ ∷ []) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
           UP.≋ U[ TP.ν (b₁ ∷ []) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
    back = subst (λ Q → U[ TP.ν (suc b₁ ∷ []) B₂ Q ] σ UP.≋ U[ TP.ν (b₁ ∷ []) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ)
             (sym (cong₂ TP._∥_ (cong TP.⟪_⟫ (sym (frame-plug*ᵣ E weakenᵣ))) refl))
             (disc-single b₁ B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) σ)
U-discard σ Vσ _ {b₁ = suc b'} {B₁ = x ∷ xs} {B₂ = B₂} {E = E} {P = P} _ =
  UR.RU-Struct (≡→≋ refl) (disc-fire-single σ Vσ (suc b') (x ∷ xs) B₂ E P) back
  where
    back : U[ TP.ν (suc (suc b') ∷ x ∷ xs) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
           UP.≋ U[ TP.ν (suc b' ∷ x ∷ xs) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
    back = subst (λ Q → U[ TP.ν (suc (suc b') ∷ x ∷ xs) B₂ Q ] σ UP.≋ U[ TP.ν (suc b' ∷ x ∷ xs) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ)
             (sym (cong₂ TP._∥_ (cong TP.⟪_⟫ (sym (frame-plug*ᵣ E weakenᵣ))) refl))
             (disc-multi b' x xs B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) σ)
U-discard σ Vσ _ {b₁ = zero} {B₁ = x ∷ xs} {B₂ = B₂} {E = E} {P = P} ⊢P =
  ⊥-elim (disc-b0-vac {x = x} {xs = xs} {B₂ = B₂} {E = E} {P = P} ⊢P)
