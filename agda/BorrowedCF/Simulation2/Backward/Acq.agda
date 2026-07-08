module BorrowedCF.Simulation2.Backward.Acq where

-- Reverse RU-Acquire: an untyped acquire fires only on a SINGLE-φ telescope
-- ν (φ acq (thread ∥ rest)) whose cell is the group-1 acq marker
-- (B₁ = 0 ∷ suc c' ∷ [], B₂ = b₂ ∷ []); the mirror shape with the cell in
-- group 2 is refuted by the handle-triple's slots.  The typed step is R-Acq
-- (no renaming), and the codomain recon collapses the cell substitution
-- ⦅ * ⦆ₛ into the φ-free leaf substitution.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; close-arg-var; head⊗′; U-ν-singleton; frameApp-reflect)
open import BorrowedCF.Simulation.RevUCong using (U-not-φ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋; U-cong; Ub-V)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Theorems.SplitsH2 using (frame*-cong)
open import BorrowedCF.Simulation.Theorems.Acq using (U-σ⋯ₛ; frame-fusion-gen)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Data.Sum as Sum
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Base using (NonZero)
open T using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)
open import Data.List.Relation.Unary.All as All using (All)

open Fin.Patterns

-- local copies of the head-inversion lemmas (defined in Reverse.agda, which
-- imports this module — no cycle allowed).
private
  inv-U-⟪⟫ : ∀ {m n} (P : T.Proc m) (σ : m →ₛ n) {e : Tm n}
           → U[ P ] σ ≡ U.⟪ e ⟫
           → Σ[ e₀ ∈ Tm m ] (P ≡ T.⟪ e₀ ⟫ × e ≡ e₀ ⋯ σ)
  inv-U-⟪⟫ (T.⟪ e₀ ⟫)    σ refl = e₀ , refl , refl
  inv-U-⟪⟫ (P T.∥ Q)     σ ()
  inv-U-⟪⟫ (T.ν B₁ B₂ P) σ ()

  inv-U-∥ : ∀ {m n} (P : T.Proc m) (σ : m →ₛ n) {A B : U.Proc n}
          → U[ P ] σ ≡ A U.∥ B
          → Σ[ P₁ ∈ T.Proc m ] Σ[ P₂ ∈ T.Proc m ]
              (P ≡ P₁ T.∥ P₂ × A ≡ U[ P₁ ] σ × B ≡ U[ P₂ ] σ)
  inv-U-∥ (T.⟪ e₀ ⟫)    σ ()
  inv-U-∥ (P T.∥ Q)     σ refl = P , Q , refl , refl , refl
  inv-U-∥ (T.ν B₁ B₂ P) σ ()

  inv-U-ν : ∀ {m n} (P : T.Proc m) (σ : m →ₛ n) {X : U.Proc (2 + n)}
          → U.ν X ≡ U[ P ] σ
          → Σ[ B₁ ∈ T.BindGroup ] Σ[ B₂ ∈ T.BindGroup ]
              Σ[ P₀ ∈ T.Proc (sum B₁ + sum B₂ + m) ]
              (P ≡ T.ν B₁ B₂ P₀ × U.ν X ≡ U[ T.ν B₁ B₂ P₀ ] σ)
  inv-U-ν (T.⟪ e₀ ⟫)    σ ()
  inv-U-ν (P T.∥ Q)     σ ()
  inv-U-ν (T.ν B₁ B₂ P) σ eq = B₁ , B₂ , P , refl , eq

private
  nonZero⇒suc : ∀ {c} → NonZero c → Σ[ c' ∈ ℕ ] c ≡ suc c'
  nonZero⇒suc {suc c'} _ = c' , refl

  V⦅*⦆ : ∀ {k} → VSub (⦅_⦆ₛ {n = k} *)
  V⦅*⦆ 0F      = V-K
  V⦅*⦆ (Fin.suc x) = V-`

  φ-inj : ∀ {k} {f g : U.Flag} {X Y : U.Proc (suc k)} →
          U.φ f X ≡ U.φ g Y → (f ≡ g) × (X ≡ Y)
  φ-inj refl = refl , refl

  ν-injU : ∀ {k} {X Y : U.Proc (2 + k)} → U.ν X ≡ U.ν Y → X ≡ Y
  ν-injU refl = refl

  ∥-injU : ∀ {k} {A B C D : U.Proc k} → (A U.∥ B) ≡ (C U.∥ D) → (A ≡ C) × (B ≡ D)
  ∥-injU refl = refl , refl

------------------------------------------------------------------------
-- The single-φ acq leaf substitution (the shape U[ ν (0∷suc c'∷[]) (b₂∷[]) ]
-- reduces to) and its ⦅ * ⦆ₛ-collapse onto the φ-free reduct substitution.
------------------------------------------------------------------------

νσᵃ : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) → (suc (c' + 0) + (b₂ + 0) + m) →ₛ (3 + n)
νσᵃ c' b₂ σ =
  ((λ i → Ub[ suc (c' + 0) ] ((` 0F) , 1F , *) i ⋯ weaken* ⦃ Kᵣ ⦄ 0)
    ++ₛ Ub[ b₂ + 0 ] (* , 2F , *))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0)

νσᵃ-VSub : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) → VSub σ → VSub (νσᵃ c' b₂ σ)
νσᵃ-VSub {m} {n} c' b₂ σ Vσ i with Fin.splitAt (suc (c' + 0) + (b₂ + 0)) i
... | Sum.inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
... | Sum.inj₁ d with Fin.splitAt (suc (c' + 0)) d
...   | Sum.inj₁ v = value-⋯ (Ub-V (suc (c' + 0)) (` 0F) 1F * V-` V-K v)
                       (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`)
...   | Sum.inj₂ w = Ub-V (b₂ + 0) * 2F * V-K V-K w

-- per-index collapse of an acq block entry.
private
  UbC : ∀ b {k} (e₁ : Tm (3 + k)) → e₁ ⋯ ⦅_⦆ₛ {n = 2 + k} * ≡ * → (x₀ : 𝔽 (2 + k)) (v : 𝔽 b) →
        (Ub[ b ] (e₁ , Fin.suc x₀ , *) v ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ ⦅ * ⦆ₛ
        ≡ ((* ⊗ (` x₀)) ⊗ *)
  UbC (suc zero) e₁ e₁* x₀ 0F =
    cong (λ z → ((z ⊗ (` x₀)) ⊗ *))
      (cong (_⋯ ⦅ * ⦆ₛ) (⋯-id e₁ (λ _ → refl) ) ■ e₁*)
  UbC (suc (suc b)) e₁ e₁* x₀ 0F =
    cong (λ z → ((z ⊗ (` x₀)) ⊗ *))
      (cong (_⋯ ⦅ * ⦆ₛ) (⋯-id e₁ (λ _ → refl) ) ■ e₁*)
  UbC (suc (suc b)) e₁ e₁* x₀ (Fin.suc v) = UbC (suc b) * refl x₀ v

  Ub-star-const : ∀ b {N} (c : 𝔽 N) (x : 𝔽 b) →
                  Ub[ b ] (* , c , *) x ≡ ((* ⊗ (` c)) ⊗ *)
  Ub-star-const (suc zero)    c 0F      = refl
  Ub-star-const (suc (suc b)) c 0F      = refl
  Ub-star-const (suc (suc b)) c (Fin.suc x) = Ub-star-const (suc b) c x

acq-collapse : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) (i : 𝔽 (suc (c' + 0) + (b₂ + 0) + m)) →
  νσᵃ c' b₂ σ i ⋯ ⦅ * ⦆ₛ ≡ νσ (suc c') b₂ σ i
acq-collapse {m} {n} c' b₂ σ i with Fin.splitAt (suc (c' + 0) + (b₂ + 0)) i
... | Sum.inj₂ u = amb
  where
    t2 : Tm (2 + n)
    t2 = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2
    amb : ((t2 ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ ⦅ * ⦆ₛ
          ≡ (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ weaken* ⦃ Kᵣ ⦄ 0
    amb = cong (_⋯ ⦅ * ⦆ₛ) (⋯-id (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 1) (λ _ → refl))
        ■ fusion t2 (weaken* ⦃ Kᵣ ⦄ 1) ⦅ * ⦆ₛ
        ■ ⋯-id t2 (λ _ → refl)
        ■ sym (⋯-id t2 (λ _ → refl))
        ■ sym (⋯-id (t2 ⋯ weaken* ⦃ Kᵣ ⦄ 0) (λ _ → refl))
... | Sum.inj₁ d with Fin.splitAt (suc (c' + 0)) d
...   | Sum.inj₁ v =
        UbC (suc (c' + 0)) (` 0F) refl 0F v
      ■ sym (cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) (Ub-star-const (suc c' + 0) 0F v))
...   | Sum.inj₂ w =
        cong (_⋯ ⦅ * ⦆ₛ) (Ub-star-const (b₂ + 0) 2F w)
      ■ sym (Ub-star-const (b₂ + 0) (weaken* ⦃ Kᵣ ⦄ 0 1F) w)

------------------------------------------------------------------------
-- Region analysis: the acquire handle triple pins the handle to 0F in the
-- good shape, and refutes the mirror shape (cell in group 2).
------------------------------------------------------------------------

private
  `-inj : ∀ {k} {x y : 𝔽 k} → (Tm.` x) ≡ (` y) → x ≡ y
  `-inj refl = refl

  -- every Ub entry is a triple with the block's middle channel.
  Ub-mid : ∀ b {k} (e₁ : Tm k) (c : 𝔽 k) (e₂ : Tm k) (x : 𝔽 b) →
           Σ[ l ∈ Tm k ] Σ[ r ∈ Tm k ] Ub[ b ] (e₁ , c , e₂) x ≡ ((l ⊗ (` c)) ⊗ r)
  Ub-mid (suc zero)    e₁ c e₂ 0F      = e₁ , e₂ , refl
  Ub-mid (suc (suc b)) e₁ c e₂ 0F      = e₁ , * , refl
  Ub-mid (suc (suc b)) e₁ c e₂ (Fin.suc x) = Ub-mid (suc b) * c e₂ x

  -- non-head entries of an acq block have a constant-* left slot.
  Ub-left* : ∀ b {k} (c : 𝔽 k) (e₂ : Tm k) (x : 𝔽 b) →
             Σ[ r ∈ Tm k ] Ub[ b ] (* , c , e₂) x ≡ ((* ⊗ (` c)) ⊗ r)
  Ub-left* (suc zero)    c e₂ 0F      = e₂ , refl
  Ub-left* (suc (suc b)) c e₂ 0F      = * , refl
  Ub-left* (suc (suc b)) c e₂ (Fin.suc x) = Ub-left* (suc b) c e₂ x

  1≢2F : ∀ {k} → (Fin.suc (Fin.zero {suc k})) ≡ Fin.suc (Fin.suc (Fin.zero {k})) → ⊥
  1≢2F ()

  Ub-acq-pin : ∀ b' {k} {e : Tm (3 + k)} (v : 𝔽 (suc b')) →
               ((` 0F) ⊗ (` 1F)) ⊗ e ≡ Ub[ suc b' ] ((` 0F) , 1F , *) v ⋯ weaken* ⦃ Kᵣ ⦄ 0 →
               (v ≡ 0F) × (e ≡ *)
  Ub-acq-pin zero     0F eq = refl , proj₂ (⊗-inj eq)
  Ub-acq-pin (suc b') 0F eq = refl , proj₂ (⊗-inj eq)
  Ub-acq-pin (suc b') (Fin.suc x) eq
    with r , ueq ← Ub-left* (suc b') 1F * x
    with () ← proj₁ (⊗-inj (proj₁ (⊗-inj (eq ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) ueq))))

  shift3ᵃ : ∀ {k} → Tm k → Tm (3 + k)
  shift3ᵃ t = t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0

  σreg3ᵃ-var : ∀ {k} {t : Tm k} → Value t → shift3ᵃ t ≡ ` 1F → ⊥
  σreg3ᵃ-var V-` ()
  σreg3ᵃ-var V-K ()
  σreg3ᵃ-var V-λ ()
  σreg3ᵃ-var (V-⊗ _ _) ()
  σreg3ᵃ-var (V-⊕ _) ()

  σreg3ᵃ-pair : ∀ {k} {t : Tm k} → Value t → ∀ {a : Tm (3 + k)} → shift3ᵃ t ≡ a ⊗ (` 1F) → ⊥
  σreg3ᵃ-pair V-` ()
  σreg3ᵃ-pair V-K ()
  σreg3ᵃ-pair V-λ ()
  σreg3ᵃ-pair (V-⊕ _) ()
  σreg3ᵃ-pair (V-⊗ V₁ V₂) eq = σreg3ᵃ-var V₂ (proj₂ (⊗-inj eq))

  σreg3ᵃ-mid : ∀ {k} {t : Tm k} → Value t → ∀ {a b : Tm (3 + k)} → shift3ᵃ t ≡ (a ⊗ (` 1F)) ⊗ b → ⊥
  σreg3ᵃ-mid V-` ()
  σreg3ᵃ-mid V-K ()
  σreg3ᵃ-mid V-λ ()
  σreg3ᵃ-mid (V-⊕ _) ()
  σreg3ᵃ-mid (V-⊗ V₁ V₂) eq = σreg3ᵃ-pair V₁ (proj₁ (⊗-inj eq))

  shift3ᵇ : ∀ {k} → Tm k → Tm (3 + k)
  shift3ᵇ t = t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 1

  σreg3ᵇ-var : ∀ {k} {t : Tm k} → Value t → shift3ᵇ t ≡ ` 1F → ⊥
  σreg3ᵇ-var V-` ()
  σreg3ᵇ-var V-K ()
  σreg3ᵇ-var V-λ ()
  σreg3ᵇ-var (V-⊗ _ _) ()
  σreg3ᵇ-var (V-⊕ _) ()

  σreg3ᵇ-pair : ∀ {k} {t : Tm k} → Value t → ∀ {a : Tm (3 + k)} → shift3ᵇ t ≡ a ⊗ (` 1F) → ⊥
  σreg3ᵇ-pair V-` ()
  σreg3ᵇ-pair V-K ()
  σreg3ᵇ-pair V-λ ()
  σreg3ᵇ-pair (V-⊕ _) ()
  σreg3ᵇ-pair (V-⊗ V₁ V₂) eq = σreg3ᵇ-var V₂ (proj₂ (⊗-inj eq))

  σreg3ᵇ-mid : ∀ {k} {t : Tm k} → Value t → ∀ {a b : Tm (3 + k)} → shift3ᵇ t ≡ (a ⊗ (` 1F)) ⊗ b → ⊥
  σreg3ᵇ-mid V-` ()
  σreg3ᵇ-mid V-K ()
  σreg3ᵇ-mid V-λ ()
  σreg3ᵇ-mid (V-⊕ _) ()
  σreg3ᵇ-mid (V-⊗ V₁ V₂) eq = σreg3ᵇ-pair V₁ (proj₁ (⊗-inj eq))

acq-image-0F : ∀ {m n} (c' b₂ : ℕ) (σ : m →ₛ n) (Vσ : VSub σ)
  (x : 𝔽 (suc (c' + 0) + (b₂ + 0) + m)) {e : Tm (3 + n)} →
  ((` 0F) ⊗ (` 1F)) ⊗ e ≡ (` x) ⋯ νσᵃ c' b₂ σ →
  (x ≡ 0F) × (e ≡ *)
acq-image-0F c' b₂ σ Vσ x {e} eq with Fin.splitAt (suc (c' + 0) + (b₂ + 0)) x in seq
... | Sum.inj₂ u = ⊥-elim (σreg3ᵃ-mid (Vσ u) (sym eq))
... | Sum.inj₁ d with Fin.splitAt (suc (c' + 0)) d in seqd
...   | Sum.inj₂ w
      with l , r , ueq ← Ub-mid (b₂ + 0) * 2F * w
      = ⊥-elim (1≢2F (`-inj (proj₂ (⊗-inj (proj₁ (⊗-inj (eq ■ ueq)))))))
...   | Sum.inj₁ v with v0 , e* ← Ub-acq-pin (c' + 0) v eq = x≡ , e*
  where
    x≡ : x ≡ 0F
    x≡ = sym (Fin.join-splitAt (suc (c' + 0) + (b₂ + 0)) _ x)
       ■ cong (Fin.join (suc (c' + 0) + (b₂ + 0)) _) seq
       ■ cong (_↑ˡ _)
           ( sym (Fin.join-splitAt (suc (c' + 0)) (b₂ + 0) d)
           ■ cong (Fin.join (suc (c' + 0)) (b₂ + 0)) seqd
           ■ cong (λ z → (z ↑ˡ (b₂ + 0))) v0 )

------------------------------------------------------------------------
-- The mirror shape (cell in group 2) is refuted by the handle triple.
------------------------------------------------------------------------

νσᵇ : ∀ {m n} (b₁ c : ℕ) (σ : m →ₛ n) → ((b₁ + 0) + (c + 0) + m) →ₛ (3 + n)
νσᵇ b₁ c σ =
  ((λ i → Ub[ b₁ + 0 ] (* , 0F , *) i ⋯ weaken* ⦃ Kᵣ ⦄ 1)
    ++ₛ Ub[ c + 0 ] ((` 0F) , 2F , *))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 1)

νσᵇ-VSub : ∀ {m n} (b₁ c : ℕ) (σ : m →ₛ n) → VSub σ → VSub (νσᵇ b₁ c σ)
νσᵇ-VSub b₁ c σ Vσ i with Fin.splitAt (b₁ + 0 + (c + 0)) i
... | Sum.inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 0) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
... | Sum.inj₁ d with Fin.splitAt (b₁ + 0) d
...   | Sum.inj₁ v = value-⋯ (Ub-V (b₁ + 0) * 0F * V-K V-K v)
                       (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
...   | Sum.inj₂ w = Ub-V (c + 0) (` 0F) 2F * V-` V-K w

acq-imageᵇ-⊥ : ∀ {m n} (b₁ c : ℕ) (σ : m →ₛ n) (Vσ : VSub σ)
  (x : 𝔽 ((b₁ + 0) + (c + 0) + m)) {e : Tm (3 + n)} →
  ((` 0F) ⊗ (` 1F)) ⊗ e ≡ (` x) ⋯ νσᵇ b₁ c σ → ⊥
acq-imageᵇ-⊥ b₁ c σ Vσ x {e} eq with Fin.splitAt (b₁ + 0 + (c + 0)) x
... | Sum.inj₂ u = σreg3ᵇ-mid (Vσ u) (sym eq)
... | Sum.inj₁ d with Fin.splitAt (b₁ + 0) d
...   | Sum.inj₂ w
      with l , r , ueq ← Ub-mid (c + 0) (` 0F) 2F * w
      = 1≢2F (`-inj (proj₂ (⊗-inj (proj₁ (⊗-inj (eq ■ ueq))))))
...   | Sum.inj₁ v
      with () ← proj₁ (⊗-inj (proj₁ (⊗-inj
           (eq ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 1) (Ub-star-const (b₁ + 0) 0F v)))))

------------------------------------------------------------------------
-- acq typing extractors.
------------------------------------------------------------------------

fn-acq-dom : ∀ {N} {Γ : Ctx N} {α : Struct N} {T Uu a ϵ}
  → Γ ; α ⊢ K `acq ∶ T ⟨ a ⟩→ Uu ∣ ϵ
  → Σ[ s ∈ 𝕊 0 ] (⟨ acq ; s ⟩ ≃ T)
fn-acq-dom (T-Const `acq) = _ , ≃-refl
fn-acq-dom (T-Conv (dom≃ `→ _) _ d) = let s , eq = fn-acq-dom d in s , ≃-trans eq dom≃
fn-acq-dom (T-Weaken _ d) = fn-acq-dom d

acq-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `acq ·¹ arg ∶ Uu ∣ ϵ
  → Σ[ s ∈ 𝕊 0 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ acq ; s ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
acq-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = let s , eq = fn-acq-dom ⊢fn in s , _ , _ , _ , eq , ⊢arg
acq-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = let s , eq = fn-acq-dom ⊢fn in s , _ , _ , _ , eq , ⊢arg
acq-arg-decomp (T-Conv _ _ d) = acq-arg-decomp d
acq-arg-decomp (T-Weaken _ d) = acq-arg-decomp d

------------------------------------------------------------------------
-- Frame*-level substitution-substitution fusion.
------------------------------------------------------------------------

F*-fuse : ∀ {N N₁ N₂} (E : Frame* N) {ϕ : N →ₛ N₁} (Vϕ : VSub ϕ)
          {ξ : N₁ →ₛ N₂} (Vξ : VSub ξ) (Vϕξ : VSub (ϕ ·ₖ ξ)) →
          frame*-⋯ (frame*-⋯ E ϕ Vϕ) ξ Vξ ≡ frame*-⋯ E (ϕ ·ₖ ξ) Vϕξ
F*-fuse []       Vϕ Vξ Vϕξ = refl
F*-fuse (Fr ∷ E) Vϕ Vξ Vϕξ =
  cong₂ _∷_ (frame-fusion-gen Fr Vϕ Vξ Vϕξ) (F*-fuse E Vϕ Vξ Vϕξ)

------------------------------------------------------------------------
-- acq-goB : shape dispatch on the bind groups.
------------------------------------------------------------------------

acq-goB :
  ∀ {m n} (B₁ B₂ : BindGroup) (σ : m →ₛ n) (Vσ : VSub σ)
    {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    (P₀ : T.Proc (sum B₁ + sum B₂ + m))
    (F : Frame* (3 + n)) {e' : Tm (3 + n)} {P₁ : U.Proc (3 + n)}
  → Γ ; g ⊢ₚ T.ν B₁ B₂ P₀
  → U.ν (U.φ U.acq (U.⟪ F [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ e') ]* ⟫ U.∥ P₁))
      ≡ U[ T.ν B₁ B₂ P₀ ] σ
  → Σ[ P′ ∈ T.Proc m ]
      ( Star TR._─→ₚ_ (T.ν B₁ B₂ P₀) P′ )
      × (U.ν ((U.⟪ F [ ((` 0F) ⊗ (` 1F)) ⊗ e' ]* ⟫ U.∥ P₁) U.⋯ₚ ⦅ * ⦆ₛ) ≈ U[ P′ ] σ)
acq-goB [] B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
  with _ , _ , _ , _ , _ , _ , _ , () , _ , _ ← inv-ν ⊢P
acq-goB (b ∷ []) [] σ Vσ Γ-S P₀ F ⊢P bodyeq
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
acq-goB (b ∷ []) (b₂ ∷ []) σ Vσ Γ-S P₀ F ⊢P bodyeq =
  ⊥-elim (U-not-φ P₀ (νσ b b₂ σ) (sym (ν-injU (bodyeq ■ U-ν-singleton b b₂ P₀ σ))))
acq-goB (b ∷ []) (suc b₂h ∷ c ∷ B₂t) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₁ (φ-inj (ν-injU bodyeq))
acq-goB (b ∷ []) (zero ∷ c ∷ d ∷ B₂t) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
acq-goB (b ∷ []) (zero ∷ c ∷ []) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with leafeq ← proj₂ (φ-inj (ν-injU bodyeq))
  with _ , _ , _ , _ , _ , _ , _ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with PL , Pr , refl , Leq , Preq ← inv-U-∥ P₀ (νσᵇ b c σ) (sym leafeq)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσᵇ b c σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢Pr ← inv-∥ ⊢body
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσᵇ b c σ) (νσᵇ-VSub b c σ Vσ) `acq F (sym Leq′)
  with 𝒫 , γr , _ , _ , _ , _ , ≼r , _ , _ , ⊢Fr , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `acq ·¹ arg₀) (inv-⟪⟫ ⊢PL)
  with sX , βX , RX , ϵX , acq≃ , ⊢argty ← acq-arg-decomp ⊢redex
  with x , refl ← close-arg-var arg₀ ⊢argty acq≃ (νσᵇ b c σ) (sym argeq)
  = ⊥-elim (acq-imageᵇ-⊥ b c σ Vσ x argeq)
acq-goB (suc b₁h ∷ c ∷ B₁t) B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₁ (φ-inj (ν-injU bodyeq))
acq-goB (zero ∷ c ∷ d ∷ B₁t) B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
acq-goB (zero ∷ c ∷ []) [] σ Vσ Γ-S P₀ F ⊢P bodyeq
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
acq-goB (zero ∷ c ∷ []) (b₂h ∷ e₂ ∷ B₂t) σ Vσ Γ-S P₀ F ⊢P bodyeq
  with () ← proj₂ (φ-inj (ν-injU bodyeq))
acq-goB (zero ∷ c ∷ []) (b₂ ∷ []) σ Vσ Γ-S P₀ F {e'} {P₁} ⊢P bodyeq
  with _ , _ , _ , _ , _ , ⊢B₁ , _ , C , C′ , ⊢body ← inv-ν ⊢P
  with c' , refl ← nonZero⇒suc (All.head ⊢B₁)
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with leafeq ← proj₂ (φ-inj (ν-injU bodyeq))
  with PL , Pr , refl , Leq , Preq ← inv-U-∥ P₀ (νσᵃ c' b₂ σ) (sym leafeq)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσᵃ c' b₂ σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢Pr ← inv-∥ ⊢body
  with F₀ , arg₀ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσᵃ c' b₂ σ) (νσᵃ-VSub c' b₂ σ Vσ) `acq F (sym Leq′)
  with 𝒫 , γr , _ , _ , _ , _ , ≼r , _ , _ , ⊢Fr , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `acq ·¹ arg₀) (inv-⟪⟫ ⊢PL)
  with sX , βX , RX , ϵX , acq≃ , ⊢argty ← acq-arg-decomp ⊢redex
  with x , refl ← close-arg-var arg₀ ⊢argty acq≃ (νσᵃ c' b₂ σ) (sym argeq)
  with x0 , _ ← acq-image-0F c' b₂ σ Vσ x argeq
  with refl ← x0
  = P′ , TR.R-Acq {b₁ = c'} {B₁ = []} {B₂ = b₂ ∷ []} {P = Pr} {E = F₀} ◅ ε
  , ≋⇒≈ (≡→≋ recon)
  where
    νσ' = νσ (suc c') b₂ σ
    Vνσ' = νσ-VSub (suc c') b₂ σ Vσ
    Vνσᵃ = νσᵃ-VSub c' b₂ σ Vσ
    V∘ : VSub (νσᵃ c' b₂ σ ·ₖ ⦅ * ⦆ₛ)
    V∘ i = value-⋯ (Vνσᵃ i) ⦅ * ⦆ₛ V⦅*⦆
    P′ : T.Proc _
    P′ = T.ν (suc c' ∷ []) (b₂ ∷ []) (T.⟪ F₀ [ ` 0F ]* ⟫ T.∥ Pr)
    threadEq : (F [ ((` 0F) ⊗ (` 1F)) ⊗ e' ]*) ⋯ ⦅ * ⦆ₛ ≡ (F₀ [ ` 0F ]*) ⋯ νσ'
    threadEq =
        frame-plug* F ⦅ * ⦆ₛ V⦅*⦆
      ■ cong₂ _[_]*
          ( cong (λ X → frame*-⋯ X ⦅ * ⦆ₛ V⦅*⦆) Feq
          ■ F*-fuse F₀ Vνσᵃ V⦅*⦆ V∘
          ■ frame*-cong F₀ V∘ Vνσ' (acq-collapse c' b₂ σ) )
          ( cong (_⋯ ⦅ * ⦆ₛ) argeq ■ acq-collapse c' b₂ σ 0F )
      ■ sym (frame-plug* F₀ νσ' Vνσ')
    restEq : P₁ U.⋯ₚ ⦅ * ⦆ₛ ≡ U[ Pr ] νσ'
    restEq = cong (U._⋯ₚ ⦅ * ⦆ₛ) Preq
           ■ U-σ⋯ₛ Pr
           ■ U-cong Pr (acq-collapse c' b₂ σ)
    recon : U.ν ((U.⟪ F [ ((` 0F) ⊗ (` 1F)) ⊗ e' ]* ⟫ U.∥ P₁) U.⋯ₚ ⦅ * ⦆ₛ) ≡ U[ P′ ] σ
    recon = cong U.ν (cong₂ U._∥_ (cong U.⟪_⟫ threadEq) restEq)

------------------------------------------------------------------------
-- Entry point for Reverse.agda's RU-Acquire clause.
------------------------------------------------------------------------

acq-go :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
    {P : T.Proc m} (F : Frame* (3 + n)) {e' : Tm (3 + n)} {P₁ : U.Proc (3 + n)}
  → Γ ; g ⊢ₚ P
  → U.ν (U.φ U.acq (U.⟪ F [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ e') ]* ⟫ U.∥ P₁)) ≡ U[ P ] σ
  → Σ[ P′ ∈ T.Proc m ]
      ( Star TR._─→ₚ_ P P′ )
      × (U.ν ((U.⟪ F [ ((` 0F) ⊗ (` 1F)) ⊗ e' ]* ⟫ U.∥ P₁) U.⋯ₚ ⦅ * ⦆ₛ) ≈ U[ P′ ] σ)
acq-go σ Vσ Γ-S {P = P} F ⊢P eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  = acq-goB B₁ B₂ σ Vσ Γ-S P₀ F ⊢P bodyeq
