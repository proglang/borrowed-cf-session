module BorrowedCF.Simulation.RevDropImage where

-- | Positional characterization of the innermost drop cell in leafσ's image:
--   a leaf entry of the shape (e ⊗ (` c)) ⊗ (` v) with toℕ v ≡ 0 can only be
--   the last slot of the second-to-last block of the innermost cell-carrying
--   group (drop-image₁ : cell in group 1, group 2 a singleton;
--   drop-image₂ : cell in group 2, group 1 arbitrary).

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as T
open import BorrowedCF.Simulation.Theorems.DropQH
open import BorrowedCF.Simulation.BlockPerm using (toℕ-weaken*ᵣ)
open T using (BindGroup)

private
  ⊗-injᵈ : ∀ {k} {a b c d : Tm k} → (a ⊗ b) ≡ (c ⊗ d) → (a ≡ c) × (b ≡ d)
  ⊗-injᵈ refl = refl , refl

  `-injᵈ : ∀ {k} {x y : 𝔽 k} → (Tm.` x) ≡ (` y) → x ≡ y
  `-injᵈ refl = refl

  0≢1+ : ∀ {q} → q ≡ 0 → 1 Nat.≤ q → ⊥
  0≢1+ refl ()

  subst-⋯ᵣ : ∀ {a a′ b} (pf : a ≡ a′) (X : Tm a) (ρ : a′ →ᵣ b) →
             subst Tm pf X ⋯ ρ ≡ X ⋯ (λ i → ρ (subst 𝔽 pf i))
  subst-⋯ᵣ refl X ρ = refl

  syncs-pos : ∀ (D : BindGroup) (w b : ℕ) → 1 Nat.≤ syncs (D ++ w ∷ b ∷ [])
  syncs-pos []           w b = Nat.s≤s Nat.z≤n
  syncs-pos (a ∷ [])     w b = Nat.s≤s Nat.z≤n
  syncs-pos (a ∷ d ∷ D″) w b = Nat.s≤s Nat.z≤n

  -- right slot of an Ub block whose e₂ is a constant is never a variable.
  Ub-right-K : ∀ b {k} (e₁ : Tm k) (c : 𝔽 k) (p : 𝔽 b)
               {E C : Tm k} {v : 𝔽 k} →
               Ub[ b ] (e₁ , c , K `unit) p ≡ (E ⊗ C) ⊗ (` v) → ⊥
  Ub-right-K (suc zero)    e₁ c 0F ()
  Ub-right-K (suc (suc b)) e₁ c 0F ()
  Ub-right-K (suc (suc b)) e₁ c (Fin.suc p) eq = Ub-right-K (suc b) * c p eq

  Ub-right-Kᵨ : ∀ b {k} (e₁ : Tm k) (c : 𝔽 k) (p : 𝔽 b) {M} (ρ : k →ᵣ M)
                {E C : Tm M} {v : 𝔽 M} →
                Ub[ b ] (e₁ , c , K `unit) p ⋯ ρ ≡ (E ⊗ C) ⊗ (` v) → ⊥
  Ub-right-Kᵨ (suc zero)    e₁ c 0F ρ ()
  Ub-right-Kᵨ (suc (suc b)) e₁ c 0F ρ ()
  Ub-right-Kᵨ (suc (suc b)) e₁ c (Fin.suc p) ρ eq = Ub-right-Kᵨ (suc b) * c p ρ eq

  -- an Ub block with e₂ = ` y yields a right-slot variable ONLY at its last
  -- index, and that variable is the ρ-image of y.
  Ub-right-pin : ∀ b {k} (e₁ : Tm k) (c y : 𝔽 k) (p : 𝔽 b) {M} (ρ : k →ᵣ M)
                 {E C : Tm M} {v : 𝔽 M} →
                 Ub[ b ] (e₁ , c , ` y) p ⋯ ρ ≡ (E ⊗ C) ⊗ (` v) →
                 (v ≡ ρ y) × (suc (Fin.toℕ p) ≡ b)
  Ub-right-pin (suc zero)    e₁ c y 0F ρ eq =
    sym (`-injᵈ (proj₂ (⊗-injᵈ eq))) , refl
  Ub-right-pin (suc (suc b)) e₁ c y 0F ρ ()
  Ub-right-pin (suc (suc b)) e₁ c y (Fin.suc p) ρ eq
    with veq , peq ← Ub-right-pin (suc b) * c y p ρ eq = veq , cong suc peq

  -- σ-tail region: a Value pushed under the leafσ tail shift never exposes a
  -- right-slot variable of index 0.
  shiftΔ : ∀ {k} (sA sB : ℕ) → Tm k → Tm (sB + (sA + (2 + k)))
  shiftΔ sA sB t = t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA ⋯ weaken* ⦃ Kᵣ ⦄ sB

  σtail-var : ∀ {k} {t : Tm k} → Value t → ∀ sA sB {v : 𝔽 (sB + (sA + (2 + k)))} →
              shiftΔ sA sB t ≡ ` v → Fin.toℕ v ≡ 0 → ⊥
  σtail-var (V-` {x = x}) sA sB {v} eq v0 = 0≢1+ (sym tv ■ tv0) ge1
    where
      tv : Fin.toℕ v ≡ sB + (sA + (2 + Fin.toℕ x))
      tv = cong Fin.toℕ (sym (`-injᵈ eq))
         ■ toℕ-weaken*ᵣ sB (weaken* ⦃ Kᵣ ⦄ sA (weaken* ⦃ Kᵣ ⦄ 2 x))
         ■ cong (sB +_) ( toℕ-weaken*ᵣ sA (weaken* ⦃ Kᵣ ⦄ 2 x)
                        ■ cong (sA +_) (toℕ-weaken*ᵣ 2 x) )
      tv0 : Fin.toℕ v ≡ 0
      tv0 = v0
      ge1 : 1 Nat.≤ sB + (sA + (2 + Fin.toℕ x))
      ge1 = Nat.≤-trans (Nat.s≤s Nat.z≤n)
              (Nat.≤-trans (Nat.m≤n+m (2 + Fin.toℕ x) sA)
                           (Nat.m≤n+m (sA + (2 + Fin.toℕ x)) sB))
  σtail-var V-K       sA sB ()
  σtail-var V-λ       sA sB ()
  σtail-var (V-⊗ _ _) sA sB ()
  σtail-var (V-⊕ _)   sA sB ()

  σtail-pair : ∀ {k} {t : Tm k} → Value t → ∀ sA sB
               {a : Tm (sB + (sA + (2 + k)))} {v : 𝔽 (sB + (sA + (2 + k)))} →
               shiftΔ sA sB t ≡ a ⊗ (` v) → Fin.toℕ v ≡ 0 → ⊥
  σtail-pair V-`         sA sB ()
  σtail-pair V-K         sA sB ()
  σtail-pair V-λ         sA sB ()
  σtail-pair (V-⊕ _)     sA sB ()
  σtail-pair (V-⊗ V₁ V₂) sA sB eq v0 =
    σtail-var V₂ sA sB (proj₂ (⊗-injᵈ eq)) v0

  -- group-carrying region: a canonₛ entry with constant e₂ whose right slot is
  -- a variable v with toℕ v ≡ 0 pins the index to the last slot of the
  -- second-to-last block.
  canonₛ-cell-pos : ∀ (D : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (w' b' : ℕ)
    (j : 𝔽 (sum (D ++ suc w' ∷ b' ∷ [])))
    {E C : Tm (syncs (D ++ suc w' ∷ b' ∷ []) + N)}
    {v : 𝔽 (syncs (D ++ suc w' ∷ b' ∷ []) + N)} →
    canonₛ (D ++ suc w' ∷ b' ∷ []) (e₁ , x , K `unit) j ≡ (E ⊗ C) ⊗ (` v) →
    Fin.toℕ v ≡ 0 → Fin.toℕ j ≡ sum D + w'
  canonₛ-cell-pos [] {N} e₁ x w' b' j {E} {C} {v} hyp v0
    with Fin.splitAt (suc w') j in seq
  ... | inj₁ p = jeq ■ Nat.suc-injective (proj₂ pin)
    where
      pin = Ub-right-pin (suc w') _ _ 0F p (weaken* ⦃ Kᵣ ⦄ 0) hyp
      jeq : Fin.toℕ j ≡ Fin.toℕ p
      jeq = cong Fin.toℕ ( sym (Fin.join-splitAt (suc w') (sum (b' ∷ [])) j)
                         ■ cong (Fin.join (suc w') (sum (b' ∷ []))) seq )
          ■ Fin.toℕ-↑ˡ p (sum (b' ∷ []))
  ... | inj₂ r = ⊥-elim (Ub-right-K (b' + 0) _ _ r hyp)
  canonₛ-cell-pos (a ∷ []) {N} e₁ x w' b' j {E} {C} {v} hyp v0
    with Fin.splitAt a j in seq
  ... | inj₁ p = ⊥-elim (0≢1+ (sym tv1 ■ v0) (Nat.s≤s Nat.z≤n))
    where
      pin = Ub-right-pin a _ _ 0F p (weaken* ⦃ Kᵣ ⦄ 1) hyp
      tv1 : Fin.toℕ v ≡ 1
      tv1 = cong Fin.toℕ (proj₁ pin) ■ toℕ-weaken*ᵣ 1 (Fin.zero {n = N})
  ... | inj₂ r =
      jeq
    ■ cong (a +_) (canonₛ-cell-pos [] (` 0F) (Fin.suc x) w' b' r hyp v0)
    ■ sym (Nat.+-assoc a 0 w')
    where
      jeq : Fin.toℕ j ≡ a + Fin.toℕ r
      jeq = cong Fin.toℕ ( sym (Fin.join-splitAt a (sum (suc w' ∷ b' ∷ [])) j)
                         ■ cong (Fin.join a (sum (suc w' ∷ b' ∷ []))) seq )
          ■ Fin.toℕ-↑ʳ a r
  canonₛ-cell-pos (a ∷ d ∷ D″) {N} e₁ x w' b' j {E} {C} {v} hyp v0
    with canonₛ-cell-pos (d ∷ D″) (` 0F) (Fin.suc x) w' b'
  ... | rec with Fin.splitAt a j in seq
  ... | inj₁ p = ⊥-elim (0≢1+ vT0 geT)
    where
      W  = (d ∷ D″) ++ suc w' ∷ b' ∷ []
      sT = syncs W
      pf : sT + suc N ≡ suc (sT + N)
      pf = +-suc sT N
      hyp′ : Ub[ a ] (wk e₁ , Fin.suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ sT
             ≡ ((subst Tm (sym pf) E ⊗ subst Tm (sym pf) C) ⊗ (` subst 𝔽 (sym pf) v))
      hyp′ = subst-flip pf hyp
           ■ subst-⊗ (sym pf) (E ⊗ C) (` v)
           ■ cong₂ _⊗_ (subst-⊗ (sym pf) E C) (subst-` (sym pf) v)
      pin = Ub-right-pin a _ _ 0F p (weaken* ⦃ Kᵣ ⦄ sT) hyp′
      vT : Fin.toℕ (subst 𝔽 (sym pf) v) ≡ sT + 0
      vT = cong Fin.toℕ (proj₁ pin) ■ toℕ-weaken*ᵣ sT 0F
      vT0 : sT + 0 ≡ 0
      vT0 = sym vT ■ toℕ-substᶠ (sym pf) v ■ v0
      geT : 1 Nat.≤ sT + 0
      geT = Nat.≤-trans (syncs-pos (d ∷ D″) (suc w') b') (Nat.m≤m+n sT 0)
  ... | inj₂ r = jeq
               ■ cong (a +_) (rec r hyp′ (toℕ-substᶠ (sym pf) v ■ v0))
               ■ sym (Nat.+-assoc a (sum (d ∷ D″)) w')
    where
      W  = (d ∷ D″) ++ suc w' ∷ b' ∷ []
      pf : syncs W + suc N ≡ suc (syncs W + N)
      pf = +-suc (syncs W) N
      hyp′ : canonₛ W (` 0F , Fin.suc x , K `unit) r
             ≡ ((subst Tm (sym pf) E ⊗ subst Tm (sym pf) C) ⊗ (` subst 𝔽 (sym pf) v))
      hyp′ = subst-flip pf hyp
           ■ subst-⊗ (sym pf) (E ⊗ C) (` v)
           ■ cong₂ _⊗_ (subst-⊗ (sym pf) E C) (subst-` (sym pf) v)
      jeq : Fin.toℕ j ≡ a + Fin.toℕ r
      jeq = cong Fin.toℕ ( sym (Fin.join-splitAt a (sum W) j)
                         ■ cong (Fin.join a (sum W)) seq )
          ■ Fin.toℕ-↑ʳ a r

  -- a canonₛ entry with constant e₂, post-composed with a renaming whose image
  -- avoids index 0, never exposes a right-slot variable of index 0.
  canonₛ-Kright-refute : ∀ (B : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N)
    {Mc : ℕ} (ρ : (syncs B + N) →ᵣ Mc) → (∀ i → 1 Nat.≤ Fin.toℕ (ρ i)) →
    (i : 𝔽 (sum B)) {E C : Tm Mc} {v : 𝔽 Mc} →
    canonₛ B (e₁ , x , K `unit) i ⋯ ρ ≡ (E ⊗ C) ⊗ (` v) →
    Fin.toℕ v ≡ 0 → ⊥
  canonₛ-Kright-refute [] e₁ x ρ bnd ()
  canonₛ-Kright-refute (b ∷ []) e₁ x ρ bnd i hyp v0 =
    Ub-right-Kᵨ (b + 0) _ _ i ρ hyp
  canonₛ-Kright-refute (b ∷ b′ ∷ B″) {N} e₁ x {Mc} ρ bnd i {E} {C} {v} hyp v0
    with canonₛ-Kright-refute (b′ ∷ B″) (` 0F) (Fin.suc x)
  ... | rec with Fin.splitAt b i in seq
  ... | inj₁ p = 0≢1+ vρ0 (bnd (subst 𝔽 pf (weaken* ⦃ Kᵣ ⦄ (syncs (b′ ∷ B″)) 0F)))
    where
      sT = syncs (b′ ∷ B″)
      pf : sT + suc N ≡ suc (sT + N)
      pf = +-suc sT N
      ρ′ : (sT + suc N) →ᵣ Mc
      ρ′ = λ q → ρ (subst 𝔽 pf q)
      X = Ub[ b ] (wk e₁ , Fin.suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ sT
      hyp′ : Ub[ b ] (wk e₁ , Fin.suc x , ` 0F) p ⋯ (weaken* ⦃ Kᵣ ⦄ sT ·ₖ ρ′)
             ≡ (E ⊗ C) ⊗ (` v)
      hyp′ = sym (fusion (Ub[ b ] (wk e₁ , Fin.suc x , ` 0F) p) (weaken* ⦃ Kᵣ ⦄ sT) ρ′)
           ■ sym (subst-⋯ᵣ pf X ρ)
           ■ hyp
      pin = Ub-right-pin b _ _ 0F p (weaken* ⦃ Kᵣ ⦄ sT ·ₖ ρ′) hyp′
      vρ0 : Fin.toℕ (ρ (subst 𝔽 pf (weaken* ⦃ Kᵣ ⦄ sT 0F))) ≡ 0
      vρ0 = sym (cong Fin.toℕ (proj₁ pin)) ■ v0
  ... | inj₂ r = rec ρ′ bnd′ r hyp′ v0
    where
      sT = syncs (b′ ∷ B″)
      pf : sT + suc N ≡ suc (sT + N)
      pf = +-suc sT N
      ρ′ : (sT + suc N) →ᵣ Mc
      ρ′ = λ q → ρ (subst 𝔽 pf q)
      bnd′ : ∀ q → 1 Nat.≤ Fin.toℕ (ρ′ q)
      bnd′ q = bnd (subst 𝔽 pf q)
      hyp′ : canonₛ (b′ ∷ B″) (` 0F , Fin.suc x , K `unit) r ⋯ ρ′ ≡ (E ⊗ C) ⊗ (` v)
      hyp′ = sym (subst-⋯ᵣ pf (canonₛ (b′ ∷ B″) (` 0F , Fin.suc x , K `unit) r) ρ)
           ■ hyp

drop-image₁ : ∀ {m n} (D₁ : T.BindGroup) (w' b' b₂ : ℕ)
              (σ : m →ₛ n) (Vσ : VSub σ)
              (z : 𝔽 (sum (D₁ ++ suc w' ∷ b' ∷ []) + sum (b₂ ∷ []) + m))
              {e : Tm (syncs (b₂ ∷ []) + (syncs (D₁ ++ suc w' ∷ b' ∷ []) + (2 + n)))}
              {c v : 𝔽 (syncs (b₂ ∷ []) + (syncs (D₁ ++ suc w' ∷ b' ∷ []) + (2 + n)))} →
              leafσ σ (D₁ ++ suc w' ∷ b' ∷ []) (b₂ ∷ []) z ≡ (e ⊗ (` c)) ⊗ (` v) →
              Fin.toℕ v ≡ 0 →
              Fin.toℕ z ≡ sum D₁ + w'
drop-image₁ {m} {n} D₁ w' b' b₂ σ Vσ z {e} {c} {v} hyp v0
  with Fin.splitAt (sum (D₁ ++ suc w' ∷ b' ∷ []) + sum (b₂ ∷ [])) z in seqZ
... | inj₂ u =
  ⊥-elim (σtail-pair (Vσ u) (syncs (D₁ ++ suc w' ∷ b' ∷ [])) (syncs (b₂ ∷ [])) hyp v0)
... | inj₁ d with Fin.splitAt (sum (D₁ ++ suc w' ∷ b' ∷ [])) d in seqD
...   | inj₂ k = ⊥-elim (Ub-right-K (b₂ + 0) _ _ k hyp)
...   | inj₁ j = zeq ■ deq ■ canonₛ-cell-pos D₁ (K `unit) 0F w' b' j hyp′ v0
  where
    B₁ = D₁ ++ suc w' ∷ b' ∷ []
    hyp′ : canonₛ B₁ (K `unit , 0F , K `unit) j ≡ (e ⊗ (` c)) ⊗ (` v)
    hyp′ = sym (⋯-id (canonₛ B₁ (K `unit , 0F , K `unit) j) (λ _ → refl)) ■ hyp
    zeq : Fin.toℕ z ≡ Fin.toℕ d
    zeq = cong Fin.toℕ ( sym (Fin.join-splitAt (sum B₁ + sum (b₂ ∷ [])) m z)
                       ■ cong (Fin.join (sum B₁ + sum (b₂ ∷ [])) m) seqZ )
        ■ Fin.toℕ-↑ˡ d m
    deq : Fin.toℕ d ≡ Fin.toℕ j
    deq = cong Fin.toℕ ( sym (Fin.join-splitAt (sum B₁) (sum (b₂ ∷ [])) d)
                       ■ cong (Fin.join (sum B₁) (sum (b₂ ∷ []))) seqD )
        ■ Fin.toℕ-↑ˡ j (sum (b₂ ∷ []))

drop-image₂ : ∀ {m n} (B₁ D₂ : T.BindGroup) (w' b' : ℕ)
              (σ : m →ₛ n) (Vσ : VSub σ)
              (z : 𝔽 (sum B₁ + sum (D₂ ++ suc w' ∷ b' ∷ []) + m))
              {e : Tm (syncs (D₂ ++ suc w' ∷ b' ∷ []) + (syncs B₁ + (2 + n)))}
              {c v : 𝔽 (syncs (D₂ ++ suc w' ∷ b' ∷ []) + (syncs B₁ + (2 + n)))} →
              leafσ σ B₁ (D₂ ++ suc w' ∷ b' ∷ []) z ≡ (e ⊗ (` c)) ⊗ (` v) →
              Fin.toℕ v ≡ 0 →
              Fin.toℕ z ≡ sum B₁ + (sum D₂ + w')
drop-image₂ {m} {n} B₁ D₂ w' b' σ Vσ z {e} {c} {v} hyp v0
  with Fin.splitAt (sum B₁ + sum (D₂ ++ suc w' ∷ b' ∷ [])) z in seqZ
... | inj₂ u =
  ⊥-elim (σtail-pair (Vσ u) (syncs B₁) (syncs (D₂ ++ suc w' ∷ b' ∷ [])) hyp v0)
... | inj₁ d with Fin.splitAt (sum B₁) d in seqD
...   | inj₁ i = ⊥-elim (canonₛ-Kright-refute B₁ (K `unit) 0F
                           (weaken* ⦃ Kᵣ ⦄ (syncs (D₂ ++ suc w' ∷ b' ∷ []))) bnd i hyp v0)
  where
    B₂ = D₂ ++ suc w' ∷ b' ∷ []
    bnd : ∀ (q : 𝔽 (syncs B₁ + (2 + n))) →
          1 Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ (syncs B₂) q)
    bnd q = subst (1 Nat.≤_) (sym (toℕ-weaken*ᵣ (syncs B₂) q))
              (Nat.≤-trans (syncs-pos D₂ (suc w') b') (Nat.m≤m+n (syncs B₂) (Fin.toℕ q)))
...   | inj₂ k = zeq ■ deq
               ■ cong (sum B₁ +_)
                   (canonₛ-cell-pos D₂ (K `unit) (weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F) w' b' k hyp v0)
  where
    B₂ = D₂ ++ suc w' ∷ b' ∷ []
    zeq : Fin.toℕ z ≡ Fin.toℕ d
    zeq = cong Fin.toℕ ( sym (Fin.join-splitAt (sum B₁ + sum B₂) m z)
                       ■ cong (Fin.join (sum B₁ + sum B₂) m) seqZ )
        ■ Fin.toℕ-↑ˡ d m
    deq : Fin.toℕ d ≡ sum B₁ + Fin.toℕ k
    deq = cong Fin.toℕ ( sym (Fin.join-splitAt (sum B₁) (sum B₂) d)
                       ■ cong (Fin.join (sum B₁) (sum B₂)) seqD )
        ■ Fin.toℕ-↑ʳ (sum B₁) k
