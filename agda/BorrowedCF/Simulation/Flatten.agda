module BorrowedCF.Simulation.Flatten where

-- | Flattening of UB[_] blocks. φ^ is the iterated async-channel (φ) binder; UB-flat
--   rewrites UB[ B ] cc f into a φ^-prefix over the flag cells and the leaf. φ-ext*
--   pulls a φ^-block past a parallel component — the obstruction-free engine.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap

Ubₛ : (b : ℕ) {M : ℕ} → UChan M → (b →ₛ M)
Ubₛ zero          cc            = λ ()
Ubₛ (suc zero)    (e₁ , x , e₂) = ((e₁ ⊗ (` x)) ⊗ e₂) ∷ₛ λ ()
Ubₛ (suc (suc b)) (e₁ , x , e₂) = ((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ Ubₛ (suc b) (K `unit , x , e₂)

Ub-comp : (b : ℕ) {M : ℕ} (cc : UChan M) (f : (b →ₛ M) → 𝐔.Proc M) → Ub[ b ] cc f ≡ f (Ubₛ b cc)
Ub-comp zero          cc            f = refl
Ub-comp (suc zero)    (e₁ , x , e₂) f = refl
Ub-comp (suc (suc b)) (e₁ , x , e₂) f =
  Ub-comp (suc b) (K `unit , x , e₂) (λ σ → f (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ))

φ^ : ∀ {n} (k : ℕ) → 𝐔.Proc (k + n) → 𝐔.Proc n
φ^ zero    P = P
φ^ (suc k) P = φ^ k (𝐔.φ P)

φ^-cong : ∀ {n} (k : ℕ) {P Q : 𝐔.Proc (k + n)} → P 𝐔.≋ Q → φ^ k P 𝐔.≋ φ^ k Q
φ^-cong zero    pq = pq
φ^-cong (suc k) pq = φ^-cong k (𝐔.φ-cong pq)

φ-φ^ : ∀ {m} k (X : 𝐔.Proc (k + suc m)) →
       𝐔.φ (φ^ k X) ≡ φ^ (suc k) (subst 𝐔.Proc (+-suc k m) X)
φ-φ^ zero    X = refl
φ-φ^ (suc k) X = φ-φ^ k (𝐔.φ X) ■ cong (φ^ (suc k)) (subst-φ-commute (+-suc k _) X)

φ-ext* : ∀ {n} (k : ℕ) {P : 𝐔.Proc n} {Q : 𝐔.Proc (k + n)} →
         P 𝐔.∥ φ^ k Q 𝐔.≋ φ^ k ((P 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ k) 𝐔.∥ Q)
φ-ext* zero    {P} {Q} = ≡→≋ (cong (𝐔._∥ Q) (sym (⋯ₚ-id P (λ _ → refl))))
φ-ext* (suc k) {P} {Q} =
     φ-ext* k {P} {𝐔.φ Q}
  ◅◅ φ^-cong k (Eq*.return 𝐔.φ-ext′)
  ◅◅ φ^-cong (suc k) (≡→≋ (cong (𝐔._∥ Q)
       (𝐔.fusionₚ P (weaken* ⦃ Kᵣ ⦄ k) (weaken* ⦃ Kᵣ ⦄ 1)
        ■ 𝐔.⋯ₚ-cong P (wk*-suc k))))

UBflat : (B : 𝐓.BindGroup) → UChan n →
         ((sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) → 𝐔.Proc (syncs B + n)
UBflat []            cc            f = f λ()
UBflat (c ∷ [])      (e₁ , x , e₂) f = Ub[ c ] (e₁ , x , e₂) (λ σh → f (σh ++ₛ λ()))
UBflat {n} (c ∷ (b ∷ B)) (e₁ , x , e₂) f =
  subst 𝐔.Proc (+-suc (syncs (b ∷ B)) n)
    (((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)))
     𝐔.∥ UBflat (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
           (λ σt → Ub[ c ] ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))
                           , weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) (suc x)
                           , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) )
                           (λ σh → subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                                     (f (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ σt))))))

UB-flat : (B : 𝐓.BindGroup) (cc : UChan n)
          (f : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) →
          UB[ B ] cc f 𝐔.≋ φ^ (syncs B) (UBflat B cc f)
UB-flat []           cc            f = ε
UB-flat (c ∷ [])     (e₁ , x , e₂) f = ε
UB-flat {n} (c ∷ (b ∷ B)) (e₁ , x , e₂) f =
     𝐔.φ-cong (𝐔.∥-cong ε (UB-flat (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ) leaffn))
  ◅◅ 𝐔.φ-cong (φ-ext* (syncs (b ∷ B)) {0F 𝐔.↦ ϕ[ c ]} {UBflat (b ∷ B) _ leaffn})
  ◅◅ ≡→≋ (φ-φ^ (syncs (b ∷ B)) _)
  where
    leaffn : (sum (b ∷ B) →ₛ syncs (b ∷ B) + suc n) → 𝐔.Proc (syncs (b ∷ B) + suc n)
    leaffn = λ σt → Ub[ c ] ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))
                            , weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) (suc x)
                            , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) )
                            (λ σh → subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                                      (f (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ σt))))

UBflat-cong : (B : 𝐓.BindGroup) (cc : UChan n)
              {f g : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)} →
              (∀ σ → f σ 𝐔.≋ g σ) → UBflat B cc f 𝐔.≋ UBflat B cc g
UBflat-cong []           cc            h = h (λ ())
UBflat-cong (c ∷ [])     (e₁ , x , e₂) {f} {g} h =
  ≡→≋ (Ub-comp c (e₁ , x , e₂) (λ σh → f (σh ++ₛ λ())))
  ◅◅ h _
  ◅◅ ≡→≋ (sym (Ub-comp c (e₁ , x , e₂) (λ σh → g (σh ++ₛ λ()))))
UBflat-cong {n} (c ∷ (b ∷ B)) (e₁ , x , e₂) {f} {g} h =
  subst-≋ (+-suc (syncs (b ∷ B)) n)
    (𝐔.∥-cong ε
      (UBflat-cong (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
        (λ σt → ≡→≋ (Ub-comp c cc'' (bodyf σt))
              ◅◅ subst-≋ (sym (+-suc (syncs (b ∷ B)) n))
                   (h (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (Ubₛ c cc'' ++ₛ σt)))
              ◅◅ ≡→≋ (sym (Ub-comp c cc'' (bodyg σt))))))
  where
    cc'' = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))
           , weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) (suc x)
           , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) )
    bodyf : (sum (b ∷ B) →ₛ syncs (b ∷ B) + suc n) → (c →ₛ _) → 𝐔.Proc _
    bodyf σt σh = subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                    (f (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ σt)))
    bodyg : (sum (b ∷ B) →ₛ syncs (b ∷ B) + suc n) → (c →ₛ _) → 𝐔.Proc _
    bodyg σt σh = subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                    (g (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ σt)))

-- Re-association of a flattened block into (channel-free flag chain) ∥ (leaf at the
-- canonical substitution). This separates the flags from the channel-carrying leaf, so
-- a φ^-block in the leaf can be pulled out past the flags without touching the channels.

Flags : ∀ {n} (B : 𝐓.BindGroup) → 𝐔.Proc (syncs B + n)
Flags []            = 𝐔.⟪ K `unit ⟫
Flags (c ∷ [])      = 𝐔.⟪ K `unit ⟫
Flags {n} (c ∷ (b ∷ B)) =
  subst 𝐔.Proc (+-suc (syncs (b ∷ B)) n)
    (((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))) 𝐔.∥ Flags (b ∷ B))

canonₛ : (B : 𝐓.BindGroup) → UChan n → (sum B →ₛ syncs B + n)
canonₛ []            cc            = λ ()
canonₛ (c ∷ [])      (e₁ , x , e₂) = Ubₛ c (e₁ , x , e₂) ++ₛ λ ()
canonₛ {n} (c ∷ (b ∷ B)) (e₁ , x , e₂) =
  subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n)
    (Ubₛ c ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))
           , weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) (suc x)
           , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) )
     ++ₛ canonₛ (b ∷ B) ((` 0F) , suc x , e₂ ⋯ weakenᵣ))

UBflat-assoc : (B : 𝐓.BindGroup) (cc : UChan n)
               (f : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)) →
               UBflat B cc f 𝐔.≋ Flags B 𝐔.∥ f (canonₛ B cc)
UBflat-assoc []           cc            f = Eq*.symmetric _ 𝐔.∥-unitˡ
UBflat-assoc (c ∷ [])     (e₁ , x , e₂) f =
  ≡→≋ (Ub-comp c (e₁ , x , e₂) (λ σh → f (σh ++ₛ λ()))) ◅◅ Eq*.symmetric _ 𝐔.∥-unitˡ
UBflat-assoc {n} (c ∷ (b ∷ B)) (e₁ , x , e₂) f =
     subst-≋ (+-suc (syncs (b ∷ B)) n)
       (𝐔.∥-cong ε (UBflat-assoc (b ∷ B) cc-rest leaffn) ◅◅ 𝐔.∥-assoc)
  ◅◅ ≡→≋ (subst-∥ (+-suc (syncs (b ∷ B)) n) flagFlags (leaffn (canonₛ (b ∷ B) cc-rest)))
  ◅◅ 𝐔.∥-cong ε (≡→≋ leafeq)
  where
    cc-rest = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    cc'' = ( e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))
           , weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) (suc x)
           , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B)) )
    bodyfn = λ σh → subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                      (f (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ canonₛ (b ∷ B) cc-rest)))
    leaffn = λ σt → Ub[ c ] cc'' (λ σh → subst 𝐔.Proc (sym (+-suc (syncs (b ∷ B)) n))
                      (f (subst (sum (c ∷ b ∷ B) →ₛ_) (+-suc (syncs (b ∷ B)) n) (σh ++ₛ σt))))
    flagFlags = ((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs (b ∷ B))) 𝐔.∥ Flags (b ∷ B)
    leafeq : subst 𝐔.Proc (+-suc (syncs (b ∷ B)) n) (leaffn (canonₛ (b ∷ B) cc-rest))
             ≡ f (canonₛ (c ∷ b ∷ B) (e₁ , x , e₂))
    leafeq = cong (subst 𝐔.Proc (+-suc (syncs (b ∷ B)) n)) (Ub-comp c cc'' bodyfn)
           ■ subst-subst-sym′ (+-suc (syncs (b ∷ B)) n)

-- Auxiliaries for Flags-⋯-cong.
subst-→ᵣ-app : ∀ {a b p} (eq : a ≡ b) (ρ : b →ᵣ p) (x : 𝔽 a) →
               subst (λ z → z →ᵣ p) (sym eq) ρ x ≡ ρ (subst 𝔽 eq x)
subst-→ᵣ-app refl ρ x = refl

toℕ-subst𝔽 : ∀ {a b} (eq : a ≡ b) (x : 𝔽 a) → Fin.toℕ (subst 𝔽 eq x) ≡ Fin.toℕ x
toℕ-subst𝔽 refl x = refl

castvar : ∀ {a m} (x : 𝔽 (a + suc m)) (j : 𝔽 (suc a)) → Fin.toℕ x ≡ Fin.toℕ j →
          subst 𝔽 (+-suc a m) x ≡ j ↑ˡ m
castvar {a} {m} x j eq = Fin.toℕ-injective (toℕ-subst𝔽 (+-suc a m) x ■ eq ■ sym (Fin.toℕ-↑ˡ j m))

-- Flags depends only on its sync-binder support: two renamings agreeing on the first
-- (syncs B) variables act the same on Flags B (up to re-basing).
Flags-⋯-cong : ∀ {m₁ m₂ p} (B : 𝐓.BindGroup) (ρ₁ : (syncs B + m₁) →ᵣ p) (ρ₂ : (syncs B + m₂) →ᵣ p) →
               (∀ (i : 𝔽 (syncs B)) → ρ₁ (i ↑ˡ m₁) ≡ ρ₂ (i ↑ˡ m₂)) →
               Flags {m₁} B 𝐔.⋯ₚ ρ₁ ≡ Flags {m₂} B 𝐔.⋯ₚ ρ₂
Flags-⋯-cong []           ρ₁ ρ₂ h = refl
Flags-⋯-cong (c ∷ [])     ρ₁ ρ₂ h = refl
Flags-⋯-cong {m₁} {m₂} {p} (c ∷ (b ∷ B)) ρ₁ ρ₂ h =
    subst-⋯ₚ′ (+-suc sB' m₁) flagFlags₁ ρ₁
  ■ cong₂ 𝐔._∥_ flagEq
      (Flags-⋯-cong (b ∷ B) ρ₁′ ρ₂′
        (λ i → subst-→ᵣ-app (+-suc sB' m₁) ρ₁ (i ↑ˡ suc m₁)
             ■ cong ρ₁ (castvar (i ↑ˡ suc m₁) (Fin.inject₁ i)
                         (Fin.toℕ-↑ˡ i (suc m₁) ■ sym (Fin.toℕ-inject₁ i)))
             ■ h (Fin.inject₁ i)
             ■ sym (cong ρ₂ (castvar (i ↑ˡ suc m₂) (Fin.inject₁ i)
                         (Fin.toℕ-↑ˡ i (suc m₂) ■ sym (Fin.toℕ-inject₁ i))))
             ■ sym (subst-→ᵣ-app (+-suc sB' m₂) ρ₂ (i ↑ˡ suc m₂))))
  ■ sym (subst-⋯ₚ′ (+-suc sB' m₂) flagFlags₂ ρ₂)
  where
    sB' = syncs (b ∷ B)
    flagFlags₁ = ((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB') 𝐔.∥ Flags {suc m₁} (b ∷ B)
    flagFlags₂ = ((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB') 𝐔.∥ Flags {suc m₂} (b ∷ B)
    ρ₁′ = subst (λ z → z →ᵣ p) (sym (+-suc sB' m₁)) ρ₁
    ρ₂′ = subst (λ z → z →ᵣ p) (sym (+-suc sB' m₂)) ρ₂
    flagEq : ((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB') 𝐔.⋯ₚ ρ₁′
             ≡ ((0F 𝐔.↦ ϕ[ c ]) 𝐔.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB') 𝐔.⋯ₚ ρ₂′
    flagvar : ∀ {q} (z : 𝔽 (suc q)) → Fin.toℕ z ≡ 0 →
              Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB' z) ≡ Fin.toℕ (Fin.fromℕ sB')
    flagvar z z≡0 = cong Fin.toℕ (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB' z) ■ Fin.toℕ-↑ʳ sB' z
                  ■ cong (sB' +_) z≡0 ■ +-identityʳ sB' ■ sym (Fin.toℕ-fromℕ sB')
    flagEq = cong (𝐔._↦ ϕ[ c ])
      ( subst-→ᵣ-app (+-suc sB' m₁) ρ₁ (weaken* ⦃ Kᵣ ⦄ sB' 0F)
      ■ cong ρ₁ (castvar (weaken* ⦃ Kᵣ ⦄ sB' 0F) (Fin.fromℕ sB') (flagvar 0F refl))
      ■ h (Fin.fromℕ sB')
      ■ sym (cong ρ₂ (castvar (weaken* ⦃ Kᵣ ⦄ sB' 0F) (Fin.fromℕ sB') (flagvar 0F refl)))
      ■ sym (subst-→ᵣ-app (+-suc sB' m₂) ρ₂ (weaken* ⦃ Kᵣ ⦄ sB' 0F)) )
