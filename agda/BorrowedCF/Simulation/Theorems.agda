module BorrowedCF.Simulation.Theorems where

-- | Forward simulation (sim→) for the reworked paper-matching process
--   definitions on git main.  This is a FRESH rebuild against the new
--   Processes.Typed / Processes.Untyped / Reduction.Processes.* / Bisim, NOT a
--   port of the old (now-broken) BorrowedCF.Simulation.* tree.
--
--   sim→ : for a well-typed P translating to U[ P ], every TYPED step
--   P ─→ₚ P′ is simulated by an UNTYPED step U[ P ] ─→ₚ U[ P′ ] (under a
--   value-substitution σ : m →ₛ n).
--
--   STATUS (kickoff): R-Exp and R-Par are PROVEN.  The remaining 12 cases are
--   interaction holes; each carries a one-line note on what it needs (which
--   helper lemma / which RU-rule it maps to) for the next agent.

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Simulation.Frames using (⋯→-⋯ₛ; frame-plug*; frame-plug₁; frame*-⋯; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation.Congruence using (U-≋)
open import BorrowedCF.Simulation.Theorems.Choice using (U-choice)
open import BorrowedCF.Simulation.Theorems.DropQ using (U-dropQ)
open import BorrowedCF.Simulation.Theorems.Com using (U-com)
open import BorrowedCF.Simulation.Theorems.Acq using (U-acq)
open import BorrowedCF.Simulation.Theorems.Splits using (U-lsplit; U-rsplit)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋; UB-cong-─→; UB-cong; ≋-subst; ─→-subst; Value-subst; chanTriple-V; VChan; U-⋯ₚ; U-cong; Ub-V)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap)
import Data.Sum as Sum
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)

infix 4 _UR─→ₚ*_
_UR─→ₚ*_ : {n : ℕ} → UP.Proc n → UP.Proc n → Set
_UR─→ₚ*_ = Star UR._─→ₚ_

─→ₚ*-subst : {a b : ℕ} (eq : a ≡ b) {x y : UP.Proc a} →
             x UR─→ₚ* y → subst UP.Proc eq x UR─→ₚ* subst UP.Proc eq y
─→ₚ*-subst refl s = s

-- Wrap a NON-EMPTY reduction star  (s₀ ◅ rest)  with structural congruences at
-- both ends.  front is folded into the first step; back is folded into the last
-- step (which may be the same first step when rest = ε).
wrapNE : {w x y′ z : UP.Proc n} → w UP.≋ x →
         {s₀tgt : UP.Proc n} → x UR.─→ₚ s₀tgt → s₀tgt UR─→ₚ* y′ → y′ UP.≋ z →
         w UR─→ₚ* z
wrapNE front s₀ ε        back = UR.RU-Struct front s₀ back ◅ ε
wrapNE front s₀ (t ◅ ts) back = UR.RU-Struct front s₀ ε ◅ wrapNE ε t ts back

-- Wrap a (possibly empty) star with congruences at both ends, dispatching back
-- into ⊎ : an empty star collapses to a pure ≋ (inj₂).
≋-wrap-⊎ : {w x y z : UP.Proc n} → w UP.≋ x → x UR─→ₚ* y → y UP.≋ z →
           (w UR─→ₚ* z) ⊎ (w UP.≋ z)
≋-wrap-⊎ front ε        back = inj₂ (front ◅◅ back)
≋-wrap-⊎ front (s ◅ ss) back = inj₁ (wrapNE front s ss back)

open TP using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; ⊢-≋; bindCtx⇒chanCtx; cons-ret/acq; cons; nil)

------------------------------------------------------------------------
-- R-Discard  b₁ = 0 / B₁ nonempty is VACUOUS (the discarded chain would
-- flip φ drop → φ acq, unreachable by the silent RU-Discard).  Typing forces
-- the discarded handle ≅ ⟨ skip ⟩, contradicting the cons ¬ Skips marker.
------------------------------------------------------------------------

open import BorrowedCF.Types.Equivalence
  using (_≃𝕊_; ≃-skips; ≃-refl; ≃-sym; ≃-trans; ≃-reflexive)
open import BorrowedCF.Simulation.InvFrame using (strengthen-frame; arg-type)

-- frame-plug for a plain renaming (generic over the renaming Kit).
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
    , cons-ret/acq {s₁ = sh} scra Γ≗ (cons {s₁ = s1ʰ} {s₂ = s2ʰ} ¬sk1 s≃1 Γ≗1 (nil skB)) tail
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




app₁-cong : {e₁ e₂ : Tm n} {d : Dir} {V?₁ : d ≡ L → Value e₁} {V?₂ : d ≡ L → Value e₂}
          → e₁ ≡ e₂ → app₁ e₁ d V?₁ ≡ app₁ e₂ d V?₂
app₁-cong refl = cong (app₁ _ _) (funext (λ x → Value-irr))

app₂-cong : {e₁ e₂ : Tm n} {d : Dir} {V?₁ : d ≡ 𝟙 Sum.⊎ d ≡ R → Value e₁} {V?₂ : d ≡ 𝟙 Sum.⊎ d ≡ R → Value e₂}
          → e₁ ≡ e₂ → app₂ e₁ d V?₁ ≡ app₂ e₂ d V?₂
app₂-cong refl = cong (app₂ _ _) (funext (λ x → Value-irr))

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (app₁ e d V?)  Vϕ Vψ eq = app₁-cong (⋯-cong e eq)
frame-cong (app₂ e d V?)  Vϕ Vψ eq = app₂-cong (⋯-cong e eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))
frame-cong (`inj□ i)      Vϕ Vψ eq = refl
frame-cong (`case□`of⟨ e₁ ; e₂ ⟩) Vϕ Vψ eq =
  cong₂ `case□`of⟨_;_⟩ (⋯-cong e₁ (eq ~↑)) (⋯-cong e₂ (eq ~↑))

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (app₁ e d V?)  {ϕ} Vϕ {ξ} Vξ Vϕξ = app₁-cong (fusion e ϕ ξ)
frame-fusion-gen (app₂ e d V?)  {ϕ} Vϕ {ξ} Vξ Vϕξ = app₂-cong (fusion e ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
frame-fusion-gen (`inj□ i)      {ϕ} Vϕ {ξ} Vξ Vϕξ = refl
frame-fusion-gen (`case□`of⟨ e₁ ; e₂ ⟩) {ϕ} Vϕ {ξ} Vξ Vϕξ =
  cong₂ `case□`of⟨_;_⟩ (fusion e₁ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₁ (λ x → sym (dist-↑-· ϕ ξ x)))
                        (fusion e₂ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₂ (λ x → sym (dist-↑-· ϕ ξ x)))



tL : Tm (4 + n)
tL = (((` 0F) ⊗ (` 3F)) ⊗ *) ⊗ (((` 1F) ⊗ (` 2F)) ⊗ *)

rnew-bridge : (E : Frame* m) (σ : m →ₛ n) (Vσ : VSub σ) →
  UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
        (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫))
    UP.≋
  U[ TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
        TP.⟪ (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 1F) ⊗ (` 0F) ]* ⟫ ] σ
rnew-bridge {m} {n} E σ Vσ =
  ≡→≋ (cong UP.ν (cong (UP.φ UP.acq) (cong (UP.φ UP.acq) (cong UP.⟪_⟫ bodyEq))))
  where
    A : 1 →ₛ (1 + (1 + (2 + n)))
    A = Ub[ 1 ] ((` 0F) , 1F , wk *) ·ₖ weaken* ⦃ Kᵣ ⦄ 1
    B : 1 →ₛ (1 + (1 + (2 + n)))
    B = Ub[ 1 ] ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *)
    Bσ : m →ₛ (1 + (1 + (2 + n)))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 1
    σ′ : (1 + 1 + m) →ₛ (1 + (1 + (2 + n)))
    σ′ = (A ++ₛ B) ++ₛ Bσ
    VA : VSub A
    VA j = value-⋯ (Ub-V 1 (` 0F) 1F (wk *) V-` (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)) j)
                   (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
    VB : VSub B
    VB j = Ub-V 1 (` 0F) (suc (weaken* ⦃ Kᵣ ⦄ 1 1F)) (wk *) V-`
                 (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)) j
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = A ++ₛ B}
            (++ₛ-VSub {σ₁ = A} VA VB)
            (weaken-VSub 1 (weaken-VSub 1 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 4)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 1)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1)
    perF : (F : Frame m) → frame-⋯ (F ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame-⋯ F σ Vσ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 4
    perF F = frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
           ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)) weakenEq
           ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)))
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_ (perF F) (frameEqA E*)
    leafTermEq : ((` 1F) ⊗ (` 0F)) ⋯ σ′ ≡ tL
    leafTermEq = refl
    bodyEq : (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]*
             ≡ ((E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 1F) ⊗ (` 0F) ]*) ⋯ σ′
    bodyEq = sym (frame-plug* (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E) leafTermEq)

block-shift : ∀ p {A B N} (bL : suc p →ₛ N) (bR : p →ₛ N)
              (eq : ∀ k → bL (suc k) ≡ bR k)
              (ts : A →ₛ N) (rs : B →ₛ N) (i : 𝔽 (p + A + B)) →
              ((bL ++ₛ ts) ++ₛ rs) (suc i) ≡ ((bR ++ₛ ts) ++ₛ rs) i
block-shift p {A} {B} bL bR eq ts rs i with splitAt (p + A) i
... | inj₂ k = refl
... | inj₁ j with splitAt p j
... | inj₁ k = eq k
... | inj₂ k = refl

-- One-level constant-prefix shift (inside a chanTriple block).
inner-shift : ∀ p {A N} (cc : Tm N) (ts : A →ₛ N) (k : 𝔽 (p + A)) →
              ((λ (_ : 𝔽 (suc p)) → cc) ++ₛ ts) (suc k)
                ≡ ((λ (_ : 𝔽 p) → cc) ++ₛ ts) k
inner-shift p cc ts k with splitAt p k
... | inj₁ _ = refl
... | inj₂ _ = refl

-- The constant-prefix specialisation (single chain).
prefix-shift : ∀ p {A B N} (cc : Tm N) (ts : A →ₛ N) (rs : B →ₛ N)
               (i : 𝔽 (p + A + B)) →
               (((λ (_ : 𝔽 (suc p)) → cc) ++ₛ ts) ++ₛ rs) (suc i)
                 ≡ (((λ (_ : 𝔽 p) → cc) ++ₛ ts) ++ₛ rs) i
prefix-shift p cc ts rs i =
  block-shift p (λ _ → cc) (λ _ → cc) (λ _ → refl) ts rs i

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

-- Unified dispatcher over the silent precondition.

-- Combined (step-or-silent) congruence under the φ-nest UB[_].  Mirrors the
-- internal structure of TranslationProperties.UB-cong-─→ / UB-cong, threading a
-- per-σ disjunction (real untyped step OR silent structural-congruence) out
-- through the telescope as a single uniform tag.
UB-cong-⊎ : (B : TP.BindGroup) (cc : UChan n) → VChan cc →
            {f g : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)} →
            (∀ σ → VSub σ → (f σ UR─→ₚ* g σ) ⊎ (f σ UP.≋ g σ)) →
            (UB[ B ] cc f UR─→ₚ* UB[ B ] cc g) ⊎ (UB[ B ] cc f UP.≋ UB[ B ] cc g)
UB-cong-⊎ []        cc Vcc h = h _ (λ ())
UB-cong-⊎ (b ∷ [])  (e₁ , c , e₂) (Ve₁ , Ve₂) h = h _ (λ j → Ub-V (b + 0) e₁ c e₂ Ve₁ Ve₂ j)
UB-cong-⊎ {n} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) (Ve₁ , Ve₂) h =
  [ (λ s → inj₁ (⋆-gmap (UP.φ ϕ[ b ]) UR.RU-Sync s)) , (λ e → inj₂ (UP.φ-cong e)) ]′
    (UB-cong-⊎ B (` 0F , suc x , e₂ ⋯ weakenᵣ) (V-` , Ve₂ ⋯ᵛ weakenᵣ)
      (λ σ Vσ → Sum.map (─→ₚ*-subst (sym (+-suc (syncs B) _)))
                        (≋-subst (sym (+-suc (syncs B) _)))
        (h _ (λ y → Value-subst (+-suc (syncs B) _) (argV σ Vσ (splitAt b y))))))
  where
    argV : (σ : sum B →ₛ syncs B + suc n) (Vσ : VSub σ)
           (s : 𝔽 b ⊎ 𝔽 (sum B)) →
           Value ([ (λ j → Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) , σ ]′ s)
    argV σ Vσ (inj₁ j) =
      value-⋯ (Ub-V b (e₁ ⋯ weakenᵣ) (suc x) (` 0F) (Ve₁ ⋯ᵛ weakenᵣ) V-` j)
              (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ z → V-`)
    argV σ Vσ (inj₂ k) = Vσ k

-- Fire RU-Discard on the translated thread, lifted through ν and the UB
-- telescope (mirrors R-Bind's UB-cong-⊎ dispatch); lands on the E[*] shape.
disc-fire : {m n : ℕ} (σ : m →ₛ n) → VSub σ → (b₁ : ℕ) (B₁ B₂ : TP.BindGroup)
            (E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m))
            (P : TP.Proc (sum (b₁ ∷ B₁) + sum B₂ + m))
          → (U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
              UR─→ₚ* U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ)
           ⊎ (U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `discard ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
              UP.≋ U[ TP.ν (suc b₁ ∷ B₁) B₂
                 (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ)
disc-fire {m} {n} σ Vσ b₁ B₁ B₂ E P =
  [ (λ s → inj₁ (⋆-gmap UP.ν UR.RU-Res s)) , (λ e → inj₂ (UP.ν-cong e)) ]′
    (UB-cong-⊎ (suc b₁ ∷ B₁) (* , 0F , *) (V-K , V-K)
      (λ σ₁ Vσ₁ → UB-cong-⊎ B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₁)) 1F , *) (V-K , V-K)
        (λ σ₂ Vσ₂ → inj₁ (leaf-red σ₁ Vσ₁ σ₂ Vσ₂ ◅ ε))))
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


sim→ : (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
     → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
     → {P′ : TP.Proc m} → P TR.─→ₚ P′
     → (U[ P ] σ UR─→ₚ* U[ P′ ] σ) ⊎ (U[ P ] σ UP.≋ U[ P′ ] σ)

-- R-Exp: expression head reduction respects value substitution → RU-Exp.
sim→ σ Vσ Γ-S ⊢P (TR.R-Exp x) = inj₁ (UR.RU-Exp (⋯→-⋯ₛ σ Vσ x) ◅ ε)

-- R-Par: invert the typing of P ∥ Q, recurse on the left, congruence RU-Par.
sim→ σ Vσ Γ-S ⊢P (TR.R-Par red)
  with _ , _ , _ , p , _ ← inv-∥ ⊢P =
  [ (λ s → inj₁ (⋆-gmap (UP._∥ _) UR.RU-Par s)) , (λ e → inj₂ (UP.∥-cong e ε)) ]′ (sim→ σ Vσ Γ-S p red)

-- R-Fork: F [ K `fork . e ] → thread split.  Needs frame-plug* (DONE in Frames)
--   to push U[ ] through the frame, then RU-Fork (with a Value for e).
sim→ σ Vσ Γ-S ⊢P (TR.R-Fork E V) =
  inj₁ (subst₂ UR._─→ₚ_ (sym (cong UP.⟪_⟫ (frame-plug* E σ Vσ)))
                  (cong₂ UP._∥_ (sym (cong UP.⟪_⟫ (frame-plug* E σ Vσ))) refl)
                  (UR.RU-Fork (frame*-⋯ E σ Vσ) (value-⋯ V σ Vσ)) ◅ ε)

-- R-New: BLOCKED (definition mismatch, needs an edit to a file owned elsewhere).
--   The LHS bridge (frame-plug*) and `RU-New (frame*-⋯ E σ Vσ)` fire fine; the ONLY
--   gap is the final  RU-New-output ≋ U[ rhs ] σ.  But the two chanTriple factors are
--   SWAPPED and the swap is irreconcilable by ≋:
--     RU-New output  : ν (φ acq (φ acq ⟪ F [ 𝓒[`0F×3F×*] ⊗ 𝓒[`1F×2F×*] ]* ⟫))
--     U[ typed-rhs ] : ν (φ acq (φ acq ⟪ F [ 𝓒[`1F×2F×*] ⊗ 𝓒[`0F×3F×*] ]* ⟫))
--   (verified by `normalize`).  The differing `a ⊗ b` vs `b ⊗ a` lives INSIDE ⟪ ⟫ as
--   an expression tensor; no untyped structural-congruence rule (∥/ν/φ-swap/comm, all
--   renaming-based) can reorder an expression-internal ⊗.  Fix = make RU-New's pair
--   order match U[ν]'s leaf order (swap the two 𝓒[…] factors in RU-New in
--   Reduction/Processes/Untyped.agda), OR swap the typed R-New body `(`0F) ⊗ (`1F)`,
--   OR swap σ₁/σ₂ in U[ν] (Bisim.agda).  All three are outside this module's edit scope.
sim→ σ Vσ Γ-S ⊢P (TR.R-New E) =
  inj₁ (UR.RU-Struct
    (≡→≋ (cong UP.⟪_⟫ (frame-plug* E σ Vσ)))
    (UR.RU-New (frame*-⋯ E σ Vσ))
    (rnew-bridge E σ Vσ) ◅ ε)

-- R-Com: send/recv rendezvous across the binder.  Needs WELL-TYPEDNESS (inv-ν +
--   the BindCtx chain to fix the recv channel index), frame-plug*, and the U[ν…]
--   telescope unfold → RU-Com.  cf. old Simulation/Theorems/Com.agda.
sim→ σ Vσ Γ-S ⊢P (TR.R-Com {b₁} {b₂} {B₁} {B₂} {P} {e} {E₁} {E₂} V) =
  U-com σ Vσ Γ-S {E₁ = E₁} {E₂ = E₂} V ⊢P

-- R-Choice: select/branch rendezvous → RU-Choice.  Wired to Theorems.Choice.U-choice.
--   U[_] is non-injective, so bind E₁/E₂/i (and b₁/b₂/B₁/B₂/P) explicitly and feed
--   them to U-choice so its result type is rigid.
sim→ σ Vσ Γ-S ⊢P (TR.R-Choice {b1} {B1} {b2} {B2} {P} {E₁} {E₂} {i}) =
  U-choice σ Vσ Γ-S {i = i} {E₁ = E₁} {E₂ = E₂} ⊢P

-- R-LSplit: local split duplicates the triple.  Needs a typing-driven binder-order
--   transpose (canonₛ-handle positional lemma) + frame-plug* → RU-LSplit.
--   cf. old Simulation/Theorems/LSplit.agda.
sim→ σ Vσ Γ-S ⊢P (TR.R-LSplit {E = E}) =
  U-lsplit σ Vσ Γ-S {E = E} ⊢P

-- R-RSplit: remote split allocates a fresh φ drop.  Needs typing + transpose → RU-RSplit.
--   cf. old Simulation/Theorems/RSplit.agda.
sim→ σ Vσ Γ-S ⊢P (TR.R-RSplit {E = E}) =
  U-rsplit σ Vσ Γ-S {E = E} ⊢P

-- R-Drop.  Goal (?5):
--   U[ ν (suc b₁ ∷ B₁) B₂ (⟪ E⋯ᶠ*weakenᵣ [ drop·(`0F) ] ⟫ ∥ (P⋯ₚweakenᵣ)) ] σ
--     ─→ₚ*  U[ ν (b₁ ∷ B₁) B₂ (⟪ E[*] ⟫ ∥ P) ] σ.
-- The translation places  φ ϕ[ suc b₁ ] = φ drop  at the TOP of UB[ suc b₁ ∷ B₁ ]
-- (good — RU-Drop wants φ drop), but the dropped handle `0F` only becomes the
-- chanTriple  𝓒[ e × suc x × `0F ]  (junction flag suc x ≥ 1 = drop) AFTER the
-- φ-nest substitution, and ONLY the BindCtx typing chain forces that middle
-- index to be a successor; under VSub alone it is FALSE (machine-checked
-- counterexample, memory simlsplit-lwk-id-false / DropAcqCounter).  Moreover for
-- |B₁| ≥ 2 or |B₂| ≥ 1 the φ drop does NOT directly wrap ⟪…⟫ ∥ P — further φ/ν
-- binders sit between, so RU-Drop must be commuted to the leaf via a
-- binder-order transpose (RU-Sync/RU-Res congruence + the canonₛ-handle
-- positional lemma).  Both ingredients live in the old BorrowedCF.Simulation
-- confine/transpose subsystem (Confine/HandleCount/StructDom/AcqHandle …), which
-- does NOT typecheck against the reworked Processes.Typed (StructDom: NotInScope
-- S.weaken*~wkr, ModuleDoesntExport structBinderWk/structBinder+2) and therefore
-- cannot be imported.  BLOCKED: needs that subsystem PORTED to the new defs
-- (out of this module's edit scope) — the typing-confinement (acq-confine /
-- HandleCount) plus the leaf transpose.
sim→ σ Vσ Γ-S ⊢P (TR.R-Drop {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {P = P} {E = E}) =
  U-dropQ σ Vσ Γ-S B₁ b₁ B₂ B {E = E} {P = P} ⊢P

-- R-Acq.  Goal (?6):
--   U[ ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪ E[ acq·(`0F) ] ⟫ ∥ P) ] σ
--     ─→ₚ*  U[ ν (suc b₁ ∷ B₁) B₂ (⟪ E[`0F] ⟫ ∥ P) ] σ.
-- Two untyped steps: RU-Acquire (φ acq → φ done, consuming a set/`1F` junction)
-- then RU-Cleanup (φ done P → P ⋯ₚ ⦅*⦆ₛ).  Same blocker as R-Drop: the acquired
-- handle `0F` only becomes 𝓒[ `0F × 1F × e ] (junction flag exactly 1F = set)
-- under the typing chain, FALSE under VSub alone, and the φ acq must be commuted
-- past the rest of the φ-nest to the leaf.  Needs the SAME ported acq-confine /
-- transpose machinery (memory: "needs acq-confine").  BLOCKED.
sim→ σ Vσ Γ-S ⊢P (TR.R-Acq {b₁} {B₁} {B₂} {P} {E}) = U-acq σ Vσ Γ-S {E = E} ⊢P

-- R-Close: end!! / end?? rendezvous → two units.  Needs frame-plug* + U[ν…] unfold → RU-Close.
sim→ {m = m} {n = n} σ Vσ Γ-S ⊢P (TR.R-Close {E₁ = E₁} {E₂ = E₂}) =
  inj₁ (UR.RU-Struct
    (≡→≋ (cong UP.ν (cong₂ UP._∥_ (thr ‼ E₁ 0F t₁ (⋯-id t₁ {ϕ = weaken* ⦃ Kᵣ ⦄ 0} (λ _ → refl))) (thr ⁇ E₂ 1F t₂ refl))))
    (UR.RU-Close (frame*-⋯ E₁ σ Vσ) (frame*-⋯ E₂ σ Vσ))
    (≡→≋ (sym (cong₂ UP._∥_ (cong UP.⟪_⟫ (frame-plug* E₁ σ Vσ)) (cong UP.⟪_⟫ (frame-plug* E₂ σ Vσ))))) ◅ ε)
  where
    t₁ : Tm (2 + n)
    t₁ = (K `unit ⊗ (` 0F)) ⊗ K `unit
    t₂ : Tm (2 + n)
    t₂ = (K `unit ⊗ (` 1F)) ⊗ K `unit
    σ₁ : 1 →ₛ (2 + n)
    σ₁ = Ub[ 1 + 0 ] (* , 0F , *)
    σ₂ : 1 →ₛ (2 + n)
    σ₂ = Ub[ 1 + 0 ] (* , 1F , *)
    Bσ : m →ₛ (2 + n)
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    σ′ : (1 + 1 + m) →ₛ (2 + n)
    σ′ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂) ++ₛ Bσ
    Vσ₁ : VSub σ₁
    Vσ₁ = λ j → Ub-V (1 + 0) * 0F * V-K V-K j
    Vσ₂ : VSub σ₂
    Vσ₂ = λ j → Ub-V (1 + 0) * 1F * V-K V-K j
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = (λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂}
            (++ₛ-VSub {σ₁ = λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0} (weaken-VSub 0 Vσ₁) Vσ₂)
            (weaken-VSub 0 (weaken-VSub 0 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0) (weaken* ⦃ Kᵣ ⦄ 0)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0 ·ₖ weaken* ⦃ Kᵣ ⦄ 0)
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_
      ( frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
      ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)) weakenEq
      ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))) )
      (frameEqA E*)
    thr : (pol : Pol) (E* : Frame* m) (x : 𝔽 (1 + 1 + m)) (t : Tm (2 + n)) → σ′ x ≡ t →
          UP.⟪ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end pol) ·⟨ 𝟙 ⟩ (` x) ]*) ⋯ σ′ ⟫
          ≡ UP.⟪ (frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end pol) ·⟨ 𝟙 ⟩ t ]* ⟫
    thr pol E* x t eq =
      cong UP.⟪_⟫ (frame-plug* (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E*) (cong (K (`end pol) ·⟨ 𝟙 ⟩_) eq))

-- R-Discard (NEW term-consuming rule).  Fire RU-Discard on the translated thread
-- (lifted through ν + the UB telescope via disc-fire), landing on the
-- administrative-discard shape (E[*] plugged), then close with the disc ≅-lemma.
-- b₁ = 0 / B₁ nonempty is vacuous (disc-b0-vac).
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b₁ = b₁} {B₁ = []} {B₂ = B₂} {P = P} {E = E}) =
  [ (λ s → ≋-wrap-⊎ ε s back) , (λ e → inj₂ (e ◅◅ back)) ]′ (disc-fire σ Vσ b₁ [] B₂ E P)
  where
    back : U[ TP.ν (suc b₁ ∷ []) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
           UP.≋ U[ TP.ν (b₁ ∷ []) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
    back = subst (λ Q → U[ TP.ν (suc b₁ ∷ []) B₂ Q ] σ UP.≋ U[ TP.ν (b₁ ∷ []) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ)
             (sym (cong₂ TP._∥_ (cong TP.⟪_⟫ (sym (frame-plug*ᵣ E weakenᵣ))) refl))
             (disc-single b₁ B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) σ)
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b₁ = suc b'} {B₁ = x ∷ xs} {B₂ = B₂} {P = P} {E = E}) =
  [ (λ s → ≋-wrap-⊎ ε s back) , (λ e → inj₂ (e ◅◅ back)) ]′ (disc-fire σ Vσ (suc b') (x ∷ xs) B₂ E P)
  where
    back : U[ TP.ν (suc (suc b') ∷ x ∷ xs) B₂ (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ * ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
           UP.≋ U[ TP.ν (suc b' ∷ x ∷ xs) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
    back = subst (λ Q → U[ TP.ν (suc (suc b') ∷ x ∷ xs) B₂ Q ] σ UP.≋ U[ TP.ν (suc b' ∷ x ∷ xs) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ)
             (sym (cong₂ TP._∥_ (cong TP.⟪_⟫ (sym (frame-plug*ᵣ E weakenᵣ))) refl))
             (disc-multi b' x xs B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) σ)
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b₁ = zero} {B₁ = x ∷ xs} {B₂ = B₂} {P = P} {E = E}) =
  ⊥-elim (disc-b0-vac {x = x} {xs = xs} {B₂ = B₂} {E = E} {P = P} ⊢P)

-- R-Bind: congruence under ν B₁ B₂.  U[ν B₁ B₂ ·] = ν (UB[B₁] (UB[B₂] U[·])); must
--   recurse under the UB telescope → nested RU-Res/RU-Sync.  Needs a
--   "UB-cong / recurse-under-telescope" lemma.
sim→ σ Vσ Γ-S ⊢P (TR.R-Bind {B₁} {B₂} red)
  with _ , _ , _ , _ , _ , _ , _ , C , C′ , ⊢Q ← inv-ν ⊢P =
  [ (λ s → inj₁ (⋆-gmap UP.ν UR.RU-Res s)) , (λ e → inj₂ (UP.ν-cong e)) ]′
    (UB-cong-⊎ B₁ (* , 0F , *) (V-K , V-K)
      (λ σ₁ Vσ₁ → UB-cong-⊎ B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *) (V-K , V-K)
        (λ σ₂ Vσ₂ → sim→ _
          (++ₛ-VSub (++ₛ-VSub (weaken-VSub (syncs B₂) Vσ₁) Vσ₂)
                    (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ))))
          (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) ⊢Q
          red)))

-- R-Struct: P ≋ P′ → P′ ─→ₚ Q′ → Q′ ≋ Q.  Needs: translation respects structural
--   congruence (U-≋ : P ≋ Q → U[P]σ ≋ U[Q]σ) + ChanCx-preservation of typing under ≋
--   (TP.⊢-≋) → RU-Struct.  cf. old Simulation/TranslationProperties (U-≋) — REBUILD.
sim→ σ Vσ Γ-S ⊢P (TR.R-Struct e r e′) with sim→ σ Vσ Γ-S (⊢-≋ Γ-S e ⊢P) r
... | inj₂ eq = inj₂ (U-≋ σ e ◅◅ eq ◅◅ U-≋ σ e′)
... | inj₁ s  = ≋-wrap-⊎ (U-≋ σ e) s (U-≋ σ e′)
