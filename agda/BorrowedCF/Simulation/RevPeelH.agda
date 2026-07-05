module BorrowedCF.Simulation.RevPeelH where

-- | Helpers for the simRes telescope peel (Task A2).  The peeled φ-prefix is
--   represented by SplitsH3.Pfx over the already-peeled block list D; Bφ-peel
--   is the decomposition that exposes the next cell.  This module provides the
--   Pfx transport lemmas (reduction with sc-preservation, ≈, ─→ᶜ?), the snoc
--   step for growing the peeled prefix, subst transports, and the
--   head-clash refutation for RU-Drop at a non-innermost cell.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Untyped as UR
open T using (BindGroup)
open import BorrowedCF.Simulation.Theorems.DropQH
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-φ-cong)
open import BorrowedCF.Simulation.RevCongStrong using (sc; ∣_∣)
import Data.Sum as Sum

------------------------------------------------------------------------
-- subst transports.
------------------------------------------------------------------------

subst-redU : ∀ {a b} (e : a ≡ b) {P Q : U.Proc a} → P UR.─→ₚ Q →
             subst U.Proc e P UR.─→ₚ subst U.Proc e Q
subst-redU refl r = r

sc-subst-redU : ∀ {a b} (e : a ≡ b) {P Q : U.Proc a} (r : P UR.─→ₚ Q) →
                sc (subst-redU e r) ≡ sc r
sc-subst-redU refl r = refl

≈-substU : ∀ {a b} (e : a ≡ b) {P Q : U.Proc a} → P ≈ Q →
           subst U.Proc e P ≈ subst U.Proc e Q
≈-substU refl c = c

------------------------------------------------------------------------
-- Pfx transports.
------------------------------------------------------------------------

Pfx-red : ∀ (D : BindGroup) {a : ℕ} {P Q : U.Proc (L.length D + a)} (r : P UR.─→ₚ Q) →
          Σ[ r′ ∈ (Pfx {a} D P UR.─→ₚ Pfx D Q) ] (sc r′ ≡ sc r)
Pfx-red []      r = r , refl
Pfx-red (b ∷ D) {a} {P} {Q} r =
  let r₁ = subst-redU (sym (+-suc (L.length D) a)) r
      r₂ , e₂ = Pfx-red D r₁
  in UR.RU-Sync r₂ , (e₂ ■ sc-subst-redU (sym (+-suc (L.length D) a)) r)

Pfx-≈ : ∀ (D : BindGroup) {a : ℕ} {P Q : U.Proc (L.length D + a)} → P ≈ Q →
        Pfx {a} D P ≈ Pfx D Q
Pfx-≈ []      c = c
Pfx-≈ (b ∷ D) {a} c = ≈-φ-cong (Pfx-≈ D (≈-substU (sym (+-suc (L.length D) a)) c))

Pfx-cl : ∀ (D : BindGroup) {a : ℕ} {P Q : U.Proc (L.length D + a)} →
         (P ≡ Q) Sum.⊎ (P UR.─→ₚ Q) →
         (Pfx {a} D P ≡ Pfx D Q) Sum.⊎ (Pfx {a} D P UR.─→ₚ Pfx D Q)
Pfx-cl D = Sum.map (cong (Pfx D)) (λ r → proj₁ (Pfx-red D r))

------------------------------------------------------------------------
-- growing the peeled prefix by one cell (snoc).
------------------------------------------------------------------------

snoc-eq : ∀ (D : BindGroup) (b : ℕ) (a : ℕ) →
          L.length (D ++ b ∷ []) + a ≡ suc (L.length D + a)
snoc-eq []      b a = refl
snoc-eq (d ∷ D) b a = cong suc (snoc-eq D b a)

Pfx-snoc : ∀ (D : BindGroup) (b : ℕ) {a : ℕ} (Y : U.Proc (L.length (D ++ b ∷ []) + a)) →
           Pfx {a} (D ++ b ∷ []) Y
           ≡ Pfx {a} D (U.φ ϕ[ b ] (subst U.Proc (snoc-eq D b a) Y))
Pfx-snoc []      b {a} Y = refl
Pfx-snoc (d ∷ D) b {a} Y =
  cong (U.φ ϕ[ d ])
    ( Pfx-snoc D b {suc a} (subst U.Proc (sym (+-suc (L.length (D ++ b ∷ [])) a)) Y)
    ■ cong (Pfx D) (cong (U.φ ϕ[ b ]) bodyeq) )
  where
    bodyeq : subst U.Proc (snoc-eq D b (suc a))
               (subst U.Proc (sym (+-suc (L.length (D ++ b ∷ [])) a)) Y)
             ≡ subst U.Proc (cong suc (sym (+-suc (L.length D) a)))
                 (subst U.Proc (snoc-eq (d ∷ D) b a) Y)
    bodyeq = ss-U (sym (+-suc (L.length (D ++ b ∷ [])) a)) (snoc-eq D b (suc a)) {t = Y}
           ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
           ■ sym (ss-U (snoc-eq (d ∷ D) b a) (cong suc (sym (+-suc (L.length D) a))) {t = Y})

------------------------------------------------------------------------
-- head-clash under a scope transport: a φ-headed process is never ∥ / ⟪⟫.
------------------------------------------------------------------------

substφ-¬∥ : ∀ {a b} (e : a ≡ b) {f : U.Flag} {Y : U.Proc (suc a)} {A B : U.Proc b} →
            subst U.Proc e (U.φ f Y) ≡ A U.∥ B → ⊥
substφ-¬∥ refl ()

substφ-¬⟪⟫ : ∀ {a b} (e : a ≡ b) {f : U.Flag} {Y : U.Proc (suc a)} {t : Tm b} →
             subst U.Proc e (U.φ f Y) ≡ U.⟪ t ⟫ → ⊥
substφ-¬⟪⟫ refl ()

------------------------------------------------------------------------
-- pushing a scope transport into the translation's substitution.
------------------------------------------------------------------------

U-substσP : ∀ {mm a b} (e : a ≡ b) (τ : mm →ₛ a) (P : T.Proc mm) →
            subst U.Proc e (U[ P ] τ) ≡ U[ P ] (λ i → subst Tm e (τ i))
U-substσP refl τ P = refl

subst-≋U : ∀ {a b} (e : a ≡ b) {P Q : U.Proc a} → P U.≋ Q →
           subst U.Proc e P U.≋ subst U.Proc e Q
subst-≋U refl c = c

Pfx-≋ : ∀ (D : BindGroup) {a : ℕ} {P Q : U.Proc (L.length D + a)} → P U.≋ Q →
        Pfx {a} D P U.≋ Pfx D Q
Pfx-≋ []      c = c
Pfx-≋ (b ∷ D) {a} c = U.φ-cong (Pfx-≋ D (subst-≋U (sym (+-suc (L.length D) a)) c))


∣-subst-redU : ∀ {a b} (e : a ≡ b) {P Q : U.Proc a} (r : P UR.─→ₚ Q) →
               ∣ subst-redU e r ∣ ≡ ∣ r ∣
∣-subst-redU refl r = refl

-- public Splits-family VSub for the flattened leaf substitution.
VSub-leafσP : ∀ {mm nn} (σ : mm →ₛ nn) → VSub σ → (Bx Bg : BindGroup) →
              VSub (leafσ σ Bx Bg)
VSub-leafσP σ Vσ Bx Bg i with Fin.splitAt (sum Bx + sum Bg) i
... | inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                 (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                 (weaken* ⦃ Kᵣ ⦄ (syncs Bx)) (λ _ → V-`))
                 (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`)
... | inj₁ d with Fin.splitAt (sum Bx) d
...   | inj₁ g1 = value-⋯ (VSub-canonₛ Bx (K `unit , 0F , K `unit) (V-K , V-K) g1)
                    (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`)
...   | inj₂ g2 = VSub-canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs Bx) 1F , K `unit) (V-K , V-K) g2

------------------------------------------------------------------------
-- Pfx over an append, and the full two-group reassembly.
------------------------------------------------------------------------

len-++A : ∀ (D D' : BindGroup) (a : ℕ) →
          L.length (D ++ D') + a ≡ L.length D' + (L.length D + a)
len-++A D D' a =
    cong (_+ a) (LP.length-++ D {D'})
  ■ Nat.+-assoc (L.length D) (L.length D') a
  ■ comm3 (L.length D) (L.length D') a

Pfx-++ : ∀ (D D' : BindGroup) {a : ℕ} (Y : U.Proc (L.length (D ++ D') + a)) →
         Pfx {a} (D ++ D') Y
         ≡ Pfx {a} D (Pfx {L.length D + a} D' (subst U.Proc (len-++A D D' a) Y))
Pfx-++ []      D' {a} Y = cong (Pfx D') (sym (cong (λ e → subst U.Proc e Y) (uipℕ (len-++A [] D' a) refl)))
Pfx-++ (d ∷ D) D' {a} Y =
  cong (U.φ ϕ[ d ])
    ( Pfx-++ D D' {suc a} (subst U.Proc (sym (+-suc (L.length (D ++ D')) a)) Y)
    ■ cong (Pfx D) bodyeq )
  where
    bodyeq : Pfx D' (subst U.Proc (len-++A D D' (suc a))
                       (subst U.Proc (sym (+-suc (L.length (D ++ D')) a)) Y))
             ≡ subst U.Proc (sym (+-suc (L.length D) a))
                 (Pfx D' (subst U.Proc (len-++A (d ∷ D) D' a) Y))
    bodyeq =
        cong (Pfx D')
          ( ss-U (sym (+-suc (L.length (D ++ D')) a)) (len-++A D D' (suc a)) {t = Y}
          ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
          ■ sym (ss-U (len-++A (d ∷ D) D' a) (cong (L.length D' +_) (sym (+-suc (L.length D) a))) {t = Y}) )
      ■ sym (subst-Pfx (sym (+-suc (L.length D) a)) D' (subst U.Proc (len-++A (d ∷ D) D' a) Y))

-- syncs of a group = number of its cells = length of its init.
syncs-len : ∀ (D : BindGroup) (l : ℕ) → syncs (D ++ l ∷ []) ≡ L.length D
syncs-len []           l = refl
syncs-len (d ∷ [])     l = refl
syncs-len (d ∷ e ∷ D)  l = cong suc (syncs-len (e ∷ D) l)

reasm-eq : ∀ (D₁ : BindGroup) (l₁ : ℕ) (D₂ : BindGroup) (l₂ : ℕ) (a : ℕ) →
           syncs (D₂ ++ l₂ ∷ []) + (syncs (D₁ ++ l₁ ∷ []) + a)
           ≡ L.length (D₁ ++ D₂) + a
reasm-eq D₁ l₁ D₂ l₂ a =
    cong₂ (λ u v → u + (v + a)) (syncs-len D₂ l₂) (syncs-len D₁ l₁)
  ■ sym (len-++A D₁ D₂ a)

reasm : ∀ (D₁ : BindGroup) (l₁ : ℕ) (D₂ : BindGroup) (l₂ : ℕ) {a : ℕ}
        (Y : U.Proc (syncs (D₂ ++ l₂ ∷ []) + (syncs (D₁ ++ l₁ ∷ []) + a))) →
        Bφ (D₁ ++ l₁ ∷ []) (Bφ (D₂ ++ l₂ ∷ []) Y)
        ≡ Pfx {a} (D₁ ++ D₂) (subst U.Proc (reasm-eq D₁ l₁ D₂ l₂ a) Y)
reasm D₁ l₁ D₂ l₂ {a} Y = pf
  where
    pe₁ = peel-eq D₁ l₁ [] {a}
    pf : Bφ (D₁ ++ l₁ ∷ []) (Bφ (D₂ ++ l₂ ∷ []) Y)
         ≡ Pfx {a} (D₁ ++ D₂) (subst U.Proc (reasm-eq D₁ l₁ D₂ l₂ a) Y)
    pf =
        Bφ-peel D₁ l₁ [] {a} (Bφ (D₂ ++ l₂ ∷ []) Y)
      ■ cong (Pfx D₁) (subst-Bφ pe₁ (D₂ ++ l₂ ∷ []) Y)
      ■ cong (Pfx D₁)
          ( Bφ-peel D₂ l₂ [] {L.length D₁ + a}
              (subst U.Proc (cong (syncs (D₂ ++ l₂ ∷ []) +_) pe₁) Y)
          ■ cong (Pfx D₂)
              ( ss-U (cong (syncs (D₂ ++ l₂ ∷ []) +_) pe₁) (peel-eq D₂ l₂ [] {L.length D₁ + a}) {t = Y}
              ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _) ) )
      ■ sym ( Pfx-++ D₁ D₂ {a} (subst U.Proc (reasm-eq D₁ l₁ D₂ l₂ a) Y)
            ■ cong (Pfx D₁ ∘ Pfx D₂)
                ( ss-U (reasm-eq D₁ l₁ D₂ l₂ a) (len-++A D₁ D₂ a) {t = Y}
                ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _) ) )
