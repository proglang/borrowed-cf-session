------------------------------------------------------------------------
-- The structure inequality for the two split rules.
--
-- After the split the ν-binder offers `structBinder` of a RESHAPED group
-- list.  `sb-lsplit` / `sb-rsplit` say that the old binder structure,
-- pushed along the split renaming and with the consumed handle expanded
-- into the two new handles, is below the new one.  For R-LSplit the
-- expansion is sequential (`lsplit` returns a Lo-biased pair), for
-- R-RSplit it is parallel (`rsplit` returns a 1-biased pair) and the group
-- is cut in two.
--
-- Everything is phrased over an arbitrary struct substitution, so the
-- lemmas are independent of the ambient context and of the concrete
-- renamings; the call sites in `LSplit.agda` / `RSplit.agda` instantiate
-- them through `P1q` / `P1rq`.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Struct where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder; structNSeq)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open Fin.Patterns

private variable N : ℕ

------------------------------------------------------------------------
-- Traversal plumbing (fusing a renaming into the following map).

⋯ᵣᵣ : ∀ {m n k} (α : Struct m) (ρ₁ : m 𝐂.→ᵣ n) (ρ₂ : n 𝐂.→ᵣ k) →
      α 𝐂.⋯ᵣ ρ₁ 𝐂.⋯ᵣ ρ₂ ≡ α 𝐂.⋯ᵣ (ρ₂ ∘ ρ₁)
⋯ᵣᵣ (` x)   ρ₁ ρ₂ = refl
⋯ᵣᵣ []      ρ₁ ρ₂ = refl
⋯ᵣᵣ (α ∥ β) ρ₁ ρ₂ = cong₂ _∥_ (⋯ᵣᵣ α ρ₁ ρ₂) (⋯ᵣᵣ β ρ₁ ρ₂)
⋯ᵣᵣ (α ; β) ρ₁ ρ₂ = cong₂ _;_ (⋯ᵣᵣ α ρ₁ ρ₂) (⋯ᵣᵣ β ρ₁ ρ₂)

⋯ᵣₛ : ∀ {m n k} (α : Struct m) (ρ : m 𝐂.→ᵣ n) (θ : n 𝐂.→ₛ k) →
      α 𝐂.⋯ᵣ ρ 𝐂.⋯ₛ θ ≡ α 𝐂.⋯ₛ (θ ∘ ρ)
⋯ᵣₛ (` x)   ρ θ = refl
⋯ᵣₛ []      ρ θ = refl
⋯ᵣₛ (α ∥ β) ρ θ = cong₂ _∥_ (⋯ᵣₛ α ρ θ) (⋯ᵣₛ β ρ θ)
⋯ᵣₛ (α ; β) ρ θ = cong₂ _;_ (⋯ᵣₛ α ρ θ) (⋯ᵣₛ β ρ θ)

⋯ᵣ⇒ₛ : ∀ {m n} (α : Struct m) (ρ : m 𝐂.→ᵣ n) → α 𝐂.⋯ᵣ ρ ≡ α 𝐂.⋯ₛ (`_ ∘ ρ)
⋯ᵣ⇒ₛ (` x)   ρ = refl
⋯ᵣ⇒ₛ []      ρ = refl
⋯ᵣ⇒ₛ (α ∥ β) ρ = cong₂ _∥_ (⋯ᵣ⇒ₛ α ρ) (⋯ᵣ⇒ₛ β ρ)
⋯ᵣ⇒ₛ (α ; β) ρ = cong₂ _;_ (⋯ᵣ⇒ₛ α ρ) (⋯ᵣ⇒ₛ β ρ)

⋯ₛ-cong : ∀ {m n} (α : Struct m) {θ₁ θ₂ : m 𝐂.→ₛ n} → θ₁ ≗ θ₂ → α 𝐂.⋯ₛ θ₁ ≡ α 𝐂.⋯ₛ θ₂
⋯ₛ-cong α e = 𝐂.⋯-cong α e

------------------------------------------------------------------------
-- `structNSeq` as an explicit chain.

seqOf : (w : ℕ) → (𝔽 w → Struct N) → Struct N
seqOf zero    θ = []
seqOf (suc w) θ = θ 0F ; seqOf w (θ ∘ suc)

seqOf-cong : ∀ (w : ℕ) {θ₁ θ₂ : 𝔽 w → Struct N} → θ₁ ≗ θ₂ → seqOf w θ₁ ≡ seqOf w θ₂
seqOf-cong zero    e = refl
seqOf-cong (suc w) e = cong₂ _;_ (e 0F) (seqOf-cong w (e ∘ suc))

nseq-seqOf : ∀ (w : ℕ) (θ : w 𝐂.→ₛ N) → structNSeq w 𝐂.⋯ₛ θ ≡ seqOf w θ
nseq-seqOf zero    θ = refl
nseq-seqOf (suc w) θ =
  cong₂ _;_ refl (⋯ᵣₛ (structNSeq w) 𝐂.weakenᵣ θ ■ nseq-seqOf w (θ ∘ suc))

------------------------------------------------------------------------
-- Group level: one chain entry becomes two, in sequence (R-LSplit).

seqOf-lsplit : ∀ {Γ : Ctx N} (q b : ℕ)
  (θ : 𝔽 (q + suc b) → Struct N) (g : 𝔽 (q + suc (suc b)) → Struct N) →
  (lo : ∀ j j′ → Fin.toℕ j Nat.< q → Fin.toℕ j′ ≡ Fin.toℕ j → θ j ≡ g j′) →
  (at : ∀ j j₁ j₂ → Fin.toℕ j ≡ q → Fin.toℕ j₁ ≡ q → Fin.toℕ j₂ ≡ suc q →
        θ j ≡ (g j₁ ; g j₂)) →
  (hi : ∀ j j′ → q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) → θ j ≡ g j′) →
  Γ ∶ seqOf (q + suc b) θ ≈ seqOf (q + suc (suc b)) g
seqOf-lsplit zero b θ g lo at hi =
  ≈-trans (≈-reflexive (cong₂ _;_ (at 0F 0F 1F refl refl refl)
                                  (seqOf-cong b tailEq)))
          ;-assoc
  where tailEq : ∀ i → θ (suc i) ≡ g (suc (suc i))
        tailEq i = hi (suc i) (suc (suc i)) (Nat.s≤s Nat.z≤n) refl
seqOf-lsplit (suc q) b θ g lo at hi =
  ;-cong (≈-reflexive (lo 0F 0F (Nat.s≤s Nat.z≤n) refl))
         (seqOf-lsplit q b (θ ∘ suc) (g ∘ suc)
           (λ j j′ lt e → lo (suc j) (suc j′) (Nat.s≤s lt) (cong suc e))
           (λ j j₁ j₂ e e₁ e₂ → at (suc j) (suc j₁) (suc j₂) (cong suc e) (cong suc e₁) (cong suc e₂))
           (λ j j′ gt e → hi (suc j) (suc j′) (Nat.s≤s gt) (cong suc e)))

------------------------------------------------------------------------
-- Group level: the chain is cut and the entry becomes two parallel
-- entries, one at the end of the first half, one at the head of the
-- second (R-RSplit).

seqOf-rsplit : ∀ {Γ : Ctx N} (q b : ℕ)
  (θ : 𝔽 (q + suc b) → Struct N)
  (g₁ : 𝔽 (q + 1) → Struct N) (g₂ : 𝔽 (suc b) → Struct N) →
  (lo : ∀ j j′ → Fin.toℕ j Nat.< q → Fin.toℕ j′ ≡ Fin.toℕ j → θ j ≡ g₁ j′) →
  (at : ∀ j j₁ → Fin.toℕ j ≡ q → Fin.toℕ j₁ ≡ q → θ j ≡ (g₁ j₁ ∥ g₂ 0F)) →
  (hi : ∀ j j′ → q Nat.< Fin.toℕ j → Fin.toℕ j ≡ q + Fin.toℕ j′ → θ j ≡ g₂ j′) →
  Γ ∶ seqOf (q + suc b) θ ≼ seqOf (q + 1) g₁ ∥ seqOf (suc b) g₂
seqOf-rsplit zero b θ g₁ g₂ lo at hi =
  ≼-trans (≼-refl (≈-trans (≈-reflexive step1) (;-cong ≈-refl (≈-sym ∥-unit₁)))) ≼-wk
  where
    step1 : seqOf (suc b) θ ≡ (g₁ 0F ∥ g₂ 0F) ; seqOf b (g₂ ∘ suc)
    step1 = cong₂ _;_ (at 0F 0F refl refl)
                      (seqOf-cong b (λ i → hi (suc i) (suc i) (Nat.s≤s Nat.z≤n) refl))
seqOf-rsplit (suc q) b θ g₁ g₂ lo at hi =
  ≼-trans (≼-refl (≈-reflexive (cong₂ _;_ (lo 0F 0F (Nat.s≤s Nat.z≤n) refl) refl)))
  (≼-trans (≼-cong-; (≼-refl ≈-refl) IH)
  (≼-trans (≼-refl (;-cong (≈-sym ∥-unit₂) ≈-refl))
  (≼-trans ≼-wk (≼-refl (∥-cong ≈-refl ;-unit₁)))))
  where
    IH = seqOf-rsplit q b (θ ∘ suc) (g₁ ∘ suc) g₂
           (λ j j′ lt e → lo (suc j) (suc j′) (Nat.s≤s lt) (cong suc e))
           (λ j j₁ e e₁ → at (suc j) (suc j₁) (cong suc e) (cong suc e₁))
           (λ j j′ gt e → hi (suc j) j′ (Nat.s≤s gt) (cong suc e))

------------------------------------------------------------------------
-- Binder-context level, R-LSplit.

sb-lsplit : ∀ {Γ : Ctx N} (B₁ : BindGroup) (q b : ℕ) (B₂ : BindGroup) {p : ℕ} →
  sum B₁ + q ≡ p →
  (θ : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)) → Struct N)
  (g : 𝔽 (sum (B₁ ++ (q + suc (suc b)) ∷ B₂)) → Struct N) →
  (lo : ∀ j j′ → Fin.toℕ j Nat.< p → Fin.toℕ j′ ≡ Fin.toℕ j → θ j ≡ g j′) →
  (at : ∀ j j₁ j₂ → Fin.toℕ j ≡ p → Fin.toℕ j₁ ≡ p → Fin.toℕ j₂ ≡ suc p →
        θ j ≡ (g j₁ ; g j₂)) →
  (hi : ∀ j j′ → p Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) → θ j ≡ g j′) →
  Γ ∶ structBinder (B₁ ++ (q + suc b) ∷ B₂) 𝐂.⋯ₛ θ
    ≈ structBinder (B₁ ++ (q + suc (suc b)) ∷ B₂) 𝐂.⋯ₛ g
sb-lsplit [] q b B₂ refl θ g lo at hi =
  ∥-cong (≈-trans (≈-reflexive eqL)
         (≈-trans (seqOf-lsplit q b (θ ∘ 𝐂.wkʳ (sum B₂)) (g ∘ 𝐂.wkʳ (sum B₂)) lo′ at′ hi′)
                  (≈-reflexive (sym eqR))))
         (≈-reflexive eqT)
  where
    eqL : (structNSeq (q + suc b) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ₛ θ
            ≡ seqOf (q + suc b) (θ ∘ 𝐂.wkʳ (sum B₂))
    eqL = ⋯ᵣₛ (structNSeq (q + suc b)) (𝐂.wkʳ (sum B₂)) θ
        ■ nseq-seqOf (q + suc b) (θ ∘ 𝐂.wkʳ (sum B₂))
    eqR : (structNSeq (q + suc (suc b)) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ₛ g
            ≡ seqOf (q + suc (suc b)) (g ∘ 𝐂.wkʳ (sum B₂))
    eqR = ⋯ᵣₛ (structNSeq (q + suc (suc b))) (𝐂.wkʳ (sum B₂)) g
        ■ nseq-seqOf (q + suc (suc b)) (g ∘ 𝐂.wkʳ (sum B₂))
    q<r : ∀ (r : 𝔽 (sum B₂)) → q Nat.< Fin.toℕ ((q + suc b) ↑ʳ r)
    q<r r = subst (suc q Nat.≤_) (sym (Fin.toℕ-↑ʳ (q + suc b) r))
              (Nat.≤-trans (subst (suc q Nat.≤_) (sym (Nat.+-suc q b)) (Nat.s≤s (Nat.m≤m+n q b)))
                           (Nat.m≤m+n (q + suc b) (Fin.toℕ r)))
    shiftr : ∀ (r : 𝔽 (sum B₂)) →
             Fin.toℕ ((q + suc (suc b)) ↑ʳ r) ≡ suc (Fin.toℕ ((q + suc b) ↑ʳ r))
    shiftr r = Fin.toℕ-↑ʳ (q + suc (suc b)) r
             ■ cong (Nat._+ Fin.toℕ r) (Nat.+-suc q (suc b))
             ■ cong suc (sym (Fin.toℕ-↑ʳ (q + suc b) r))
    tailEq : ∀ r → θ ((q + suc b) ↑ʳ r) ≡ g ((q + suc (suc b)) ↑ʳ r)
    tailEq r = hi ((q + suc b) ↑ʳ r) ((q + suc (suc b)) ↑ʳ r) (q<r r) (shiftr r)
    eqT : (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (q + suc b)) 𝐂.⋯ₛ θ
            ≡ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (q + suc (suc b))) 𝐂.⋯ₛ g
    eqT = ⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ (q + suc b)) θ
        ■ ⋯ₛ-cong (structBinder B₂) tailEq
        ■ sym (⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ (q + suc (suc b))) g)
    lo′ : ∀ j j′ → Fin.toℕ j Nat.< q → Fin.toℕ j′ ≡ Fin.toℕ j →
          θ (j ↑ˡ sum B₂) ≡ g (j′ ↑ˡ sum B₂)
    lo′ j j′ lt e = lo (j ↑ˡ sum B₂) (j′ ↑ˡ sum B₂)
                       (subst (Nat._< q) (sym (Fin.toℕ-↑ˡ j (sum B₂))) lt)
                       (Fin.toℕ-↑ˡ j′ (sum B₂) ■ e ■ sym (Fin.toℕ-↑ˡ j (sum B₂)))
    at′ : ∀ j j₁ j₂ → Fin.toℕ j ≡ q → Fin.toℕ j₁ ≡ q → Fin.toℕ j₂ ≡ suc q →
          θ (j ↑ˡ sum B₂) ≡ (g (j₁ ↑ˡ sum B₂) ; g (j₂ ↑ˡ sum B₂))
    at′ j j₁ j₂ e e₁ e₂ = at (j ↑ˡ sum B₂) (j₁ ↑ˡ sum B₂) (j₂ ↑ˡ sum B₂)
                             (Fin.toℕ-↑ˡ j (sum B₂) ■ e)
                             (Fin.toℕ-↑ˡ j₁ (sum B₂) ■ e₁)
                             (Fin.toℕ-↑ˡ j₂ (sum B₂) ■ e₂)
    hi′ : ∀ j j′ → q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
          θ (j ↑ˡ sum B₂) ≡ g (j′ ↑ˡ sum B₂)
    hi′ j j′ gt e = hi (j ↑ˡ sum B₂) (j′ ↑ˡ sum B₂)
                       (subst (q Nat.<_) (sym (Fin.toℕ-↑ˡ j (sum B₂))) gt)
                       (Fin.toℕ-↑ˡ j′ (sum B₂) ■ e ■ cong suc (sym (Fin.toℕ-↑ˡ j (sum B₂))))
sb-lsplit (b₀ ∷ B₁′) q b B₂ {p} peq θ g lo at hi =
  ∥-cong (≈-reflexive headEq)
         (≈-trans (≈-reflexive eqθ) (≈-trans IH (≈-reflexive (sym eqg))))
  where
    W  = sum (B₁′ ++ (q + suc b) ∷ B₂)
    W′ = sum (B₁′ ++ (q + suc (suc b)) ∷ B₂)
    b₀≤p : b₀ Nat.≤ p
    b₀≤p = subst (b₀ Nat.≤_) peq (Nat.≤-trans (Nat.m≤m+n b₀ (sum B₁′)) (Nat.m≤m+n (b₀ + sum B₁′) q))
    hEq : ∀ (j : 𝔽 b₀) → θ (j ↑ˡ W) ≡ g (j ↑ˡ W′)
    hEq j = lo (j ↑ˡ W) (j ↑ˡ W′)
               (subst (Nat._< p) (sym (Fin.toℕ-↑ˡ j W)) (Nat.<-≤-trans (Fin.toℕ<n j) b₀≤p))
               (Fin.toℕ-↑ˡ j W′ ■ sym (Fin.toℕ-↑ˡ j W))
    headEq : (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W) 𝐂.⋯ₛ θ ≡ (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W′) 𝐂.⋯ₛ g
    headEq = ⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W) θ
           ■ ⋯ₛ-cong (structNSeq b₀) hEq
           ■ sym (⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W′) g)
    eqθ : (structBinder (B₁′ ++ (q + suc b) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ θ
            ≡ structBinder (B₁′ ++ (q + suc b) ∷ B₂) 𝐂.⋯ₛ (θ ∘ 𝐂.wkˡ b₀)
    eqθ = ⋯ᵣₛ (structBinder (B₁′ ++ (q + suc b) ∷ B₂)) (𝐂.wkˡ b₀) θ
    eqg : (structBinder (B₁′ ++ (q + suc (suc b)) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ g
            ≡ structBinder (B₁′ ++ (q + suc (suc b)) ∷ B₂) 𝐂.⋯ₛ (g ∘ 𝐂.wkˡ b₀)
    eqg = ⋯ᵣₛ (structBinder (B₁′ ++ (q + suc (suc b)) ∷ B₂)) (𝐂.wkˡ b₀) g
    p≡ : b₀ + (sum B₁′ + q) ≡ p
    p≡ = sym (Nat.+-assoc b₀ (sum B₁′) q) ■ peq
    lo″ : ∀ j j′ → Fin.toℕ j Nat.< sum B₁′ + q → Fin.toℕ j′ ≡ Fin.toℕ j →
          θ (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    lo″ j j′ lt e = lo (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< p) (sym (Fin.toℕ-↑ʳ b₀ j))
                         (subst (b₀ + Fin.toℕ j Nat.<_) p≡ (Nat.+-monoʳ-< b₀ lt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e ■ sym (Fin.toℕ-↑ʳ b₀ j))
    at″ : ∀ j j₁ j₂ → Fin.toℕ j ≡ sum B₁′ + q → Fin.toℕ j₁ ≡ sum B₁′ + q →
          Fin.toℕ j₂ ≡ suc (sum B₁′ + q) →
          θ (b₀ ↑ʳ j) ≡ (g (b₀ ↑ʳ j₁) ; g (b₀ ↑ʳ j₂))
    at″ j j₁ j₂ e e₁ e₂ = at (b₀ ↑ʳ j) (b₀ ↑ʳ j₁) (b₀ ↑ʳ j₂)
                             (Fin.toℕ-↑ʳ b₀ j  ■ cong (b₀ +_) e  ■ p≡)
                             (Fin.toℕ-↑ʳ b₀ j₁ ■ cong (b₀ +_) e₁ ■ p≡)
                             (Fin.toℕ-↑ʳ b₀ j₂ ■ cong (b₀ +_) e₂
                               ■ Nat.+-suc b₀ (sum B₁′ + q) ■ cong suc p≡)
    hi″ : ∀ j j′ → sum B₁′ + q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
          θ (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    hi″ j j′ gt e = hi (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< Fin.toℕ (b₀ ↑ʳ j)) p≡
                         (subst (b₀ + (sum B₁′ + q) Nat.<_) (sym (Fin.toℕ-↑ʳ b₀ j))
                           (Nat.+-monoʳ-< b₀ gt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e
                         ■ Nat.+-suc b₀ (Fin.toℕ j) ■ cong suc (sym (Fin.toℕ-↑ʳ b₀ j)))
    IH = sb-lsplit B₁′ q b B₂ {sum B₁′ + q} refl (θ ∘ 𝐂.wkˡ b₀) (g ∘ 𝐂.wkˡ b₀) lo″ at″ hi″

------------------------------------------------------------------------
-- Binder-context level, R-RSplit.

sb-rsplit : ∀ {Γ : Ctx N} (B₁ : BindGroup) (q b : ℕ) (B₂ : BindGroup) {p : ℕ} →
  sum B₁ + q ≡ p →
  (θ : 𝔽 (sum (B₁ ++ (q + suc b) ∷ B₂)) → Struct N)
  (g : 𝔽 (sum (B₁ ++ (q + 1) ∷ suc b ∷ B₂)) → Struct N) →
  (lo : ∀ j j′ → Fin.toℕ j Nat.< p → Fin.toℕ j′ ≡ Fin.toℕ j → θ j ≡ g j′) →
  (at : ∀ j j₁ j₂ → Fin.toℕ j ≡ p → Fin.toℕ j₁ ≡ p → Fin.toℕ j₂ ≡ suc p →
        θ j ≡ (g j₁ ∥ g j₂)) →
  (hi : ∀ j j′ → p Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) → θ j ≡ g j′) →
  Γ ∶ structBinder (B₁ ++ (q + suc b) ∷ B₂) 𝐂.⋯ₛ θ
    ≼ structBinder (B₁ ++ (q + 1) ∷ suc b ∷ B₂) 𝐂.⋯ₛ g
sb-rsplit [] q b B₂ refl θ g lo at hi =
  ≼-trans (≼-refl (≈-reflexive (cong₂ _∥_ eqL eqT)))
  (≼-trans (≼-cong-∥ SR (≼-refl ≈-refl))
  (≼-trans (≼-refl ∥-assoc)
           (≼-refl (≈-reflexive (cong₂ _∥_ (sym eqR₁) (cong₂ _∥_ (sym eqR₂) refl))))))
  where
    θ₁ = θ ∘ 𝐂.wkʳ (sum B₂)
    g₁ = g ∘ 𝐂.wkʳ (suc b + sum B₂)
    g₂ = g ∘ 𝐂.wkˡ (q + 1) ∘ 𝐂.wkʳ (sum B₂)
    eqL : (structNSeq (q + suc b) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ₛ θ ≡ seqOf (q + suc b) θ₁
    eqL = ⋯ᵣₛ (structNSeq (q + suc b)) (𝐂.wkʳ (sum B₂)) θ ■ nseq-seqOf (q + suc b) θ₁
    eqR₁ : (structNSeq (q + 1) 𝐂.⋯ᵣ 𝐂.wkʳ (suc b + sum B₂)) 𝐂.⋯ₛ g ≡ seqOf (q + 1) g₁
    eqR₁ = ⋯ᵣₛ (structNSeq (q + 1)) (𝐂.wkʳ (suc b + sum B₂)) g ■ nseq-seqOf (q + 1) g₁
    eqR₂ : ((structNSeq (suc b) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ᵣ 𝐂.wkˡ (q + 1)) 𝐂.⋯ₛ g
             ≡ seqOf (suc b) g₂
    eqR₂ = cong (λ z → z 𝐂.⋯ₛ g) (⋯ᵣᵣ (structNSeq (suc b)) (𝐂.wkʳ (sum B₂)) (𝐂.wkˡ (q + 1)))
         ■ ⋯ᵣₛ (structNSeq (suc b)) (𝐂.wkˡ (q + 1) ∘ 𝐂.wkʳ (sum B₂)) g
         ■ nseq-seqOf (suc b) g₂
    q<r : ∀ (r : 𝔽 (sum B₂)) → q Nat.< Fin.toℕ ((q + suc b) ↑ʳ r)
    q<r r = subst (suc q Nat.≤_) (sym (Fin.toℕ-↑ʳ (q + suc b) r))
              (Nat.≤-trans (subst (suc q Nat.≤_) (sym (Nat.+-suc q b)) (Nat.s≤s (Nat.m≤m+n q b)))
                           (Nat.m≤m+n (q + suc b) (Fin.toℕ r)))
    arith : ∀ (r : ℕ) → (q + 1) + (suc b + r) ≡ suc ((q + suc b) + r)
    arith r = sym (Nat.+-assoc (q + 1) (suc b) r)
            ■ cong (Nat._+ r) (Nat.+-assoc q 1 (suc b) ■ Nat.+-suc q (suc b))
    tailEq : ∀ r → θ ((q + suc b) ↑ʳ r) ≡ g ((q + 1) ↑ʳ (suc b ↑ʳ r))
    tailEq r = hi ((q + suc b) ↑ʳ r) ((q + 1) ↑ʳ (suc b ↑ʳ r)) (q<r r)
                  ( Fin.toℕ-↑ʳ (q + 1) (suc b ↑ʳ r)
                  ■ cong ((q + 1) +_) (Fin.toℕ-↑ʳ (suc b) r)
                  ■ arith (Fin.toℕ r)
                  ■ cong suc (sym (Fin.toℕ-↑ʳ (q + suc b) r)) )
    eqT : (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (q + suc b)) 𝐂.⋯ₛ θ
            ≡ ((structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (suc b)) 𝐂.⋯ᵣ 𝐂.wkˡ (q + 1)) 𝐂.⋯ₛ g
    eqT = ⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ (q + suc b)) θ
        ■ ⋯ₛ-cong (structBinder B₂) tailEq
        ■ sym ( cong (λ z → z 𝐂.⋯ₛ g)
                     (⋯ᵣᵣ (structBinder B₂) (𝐂.wkˡ (suc b)) (𝐂.wkˡ (q + 1)))
              ■ ⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ (q + 1) ∘ 𝐂.wkˡ (suc b)) g )
    lo′ : ∀ j j′ → Fin.toℕ j Nat.< q → Fin.toℕ j′ ≡ Fin.toℕ j → θ₁ j ≡ g₁ j′
    lo′ j j′ lt e = lo (j ↑ˡ sum B₂) (j′ ↑ˡ (suc b + sum B₂))
                       (subst (Nat._< q) (sym (Fin.toℕ-↑ˡ j (sum B₂))) lt)
                       ( Fin.toℕ-↑ˡ j′ (suc b + sum B₂) ■ e
                       ■ sym (Fin.toℕ-↑ˡ j (sum B₂)) )
    at′ : ∀ j j₁ → Fin.toℕ j ≡ q → Fin.toℕ j₁ ≡ q → θ₁ j ≡ (g₁ j₁ ∥ g₂ 0F)
    at′ j j₁ e e₁ = at (j ↑ˡ sum B₂) (j₁ ↑ˡ (suc b + sum B₂)) ((q + 1) ↑ʳ (0F ↑ˡ sum B₂))
                       (Fin.toℕ-↑ˡ j (sum B₂) ■ e)
                       (Fin.toℕ-↑ˡ j₁ (suc b + sum B₂) ■ e₁)
                       ( Fin.toℕ-↑ʳ (q + 1) (0F ↑ˡ sum B₂)
                       ■ cong ((q + 1) +_) (Fin.toℕ-↑ˡ (Fin.zero {n = suc b}) (sum B₂))
                       ■ Nat.+-identityʳ (q + 1)
                       ■ Nat.+-comm q 1 )
    hi′ : ∀ j j′ → q Nat.< Fin.toℕ j → Fin.toℕ j ≡ q + Fin.toℕ j′ → θ₁ j ≡ g₂ j′
    hi′ j j′ gt e = hi (j ↑ˡ sum B₂) ((q + 1) ↑ʳ (j′ ↑ˡ sum B₂))
                       (subst (q Nat.<_) (sym (Fin.toℕ-↑ˡ j (sum B₂))) gt)
                       ( Fin.toℕ-↑ʳ (q + 1) (j′ ↑ˡ sum B₂)
                       ■ cong ((q + 1) +_) (Fin.toℕ-↑ˡ j′ (sum B₂))
                       ■ cong (Nat._+ Fin.toℕ j′) (Nat.+-comm q 1)
                       ■ cong suc (sym e)
                       ■ cong suc (sym (Fin.toℕ-↑ˡ j (sum B₂))) )
    SR = seqOf-rsplit q b θ₁ g₁ g₂ lo′ at′ hi′
sb-rsplit (b₀ ∷ B₁′) q b B₂ {p} peq θ g lo at hi =
  ≼-trans (≼-refl (≈-reflexive (cong₂ _∥_ headEq eqθ)))
  (≼-trans (≼-cong-∥ (≼-refl ≈-refl) IH)
           (≼-refl (≈-reflexive (cong₂ _∥_ refl (sym eqg)))))
  where
    W  = sum (B₁′ ++ (q + suc b) ∷ B₂)
    W′ = sum (B₁′ ++ (q + 1) ∷ suc b ∷ B₂)
    b₀≤p : b₀ Nat.≤ p
    b₀≤p = subst (b₀ Nat.≤_) peq (Nat.≤-trans (Nat.m≤m+n b₀ (sum B₁′)) (Nat.m≤m+n (b₀ + sum B₁′) q))
    hEq : ∀ (j : 𝔽 b₀) → θ (j ↑ˡ W) ≡ g (j ↑ˡ W′)
    hEq j = lo (j ↑ˡ W) (j ↑ˡ W′)
               (subst (Nat._< p) (sym (Fin.toℕ-↑ˡ j W)) (Nat.<-≤-trans (Fin.toℕ<n j) b₀≤p))
               (Fin.toℕ-↑ˡ j W′ ■ sym (Fin.toℕ-↑ˡ j W))
    headEq : (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W) 𝐂.⋯ₛ θ ≡ (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W′) 𝐂.⋯ₛ g
    headEq = ⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W) θ
           ■ ⋯ₛ-cong (structNSeq b₀) hEq
           ■ sym (⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W′) g)
    eqθ : (structBinder (B₁′ ++ (q + suc b) ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ θ
            ≡ structBinder (B₁′ ++ (q + suc b) ∷ B₂) 𝐂.⋯ₛ (θ ∘ 𝐂.wkˡ b₀)
    eqθ = ⋯ᵣₛ (structBinder (B₁′ ++ (q + suc b) ∷ B₂)) (𝐂.wkˡ b₀) θ
    eqg : (structBinder (B₁′ ++ (q + 1) ∷ suc b ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ g
            ≡ structBinder (B₁′ ++ (q + 1) ∷ suc b ∷ B₂) 𝐂.⋯ₛ (g ∘ 𝐂.wkˡ b₀)
    eqg = ⋯ᵣₛ (structBinder (B₁′ ++ (q + 1) ∷ suc b ∷ B₂)) (𝐂.wkˡ b₀) g
    p≡ : b₀ + (sum B₁′ + q) ≡ p
    p≡ = sym (Nat.+-assoc b₀ (sum B₁′) q) ■ peq
    lo″ : ∀ j j′ → Fin.toℕ j Nat.< sum B₁′ + q → Fin.toℕ j′ ≡ Fin.toℕ j →
          θ (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    lo″ j j′ lt e = lo (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< p) (sym (Fin.toℕ-↑ʳ b₀ j))
                         (subst (b₀ + Fin.toℕ j Nat.<_) p≡ (Nat.+-monoʳ-< b₀ lt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e ■ sym (Fin.toℕ-↑ʳ b₀ j))
    at″ : ∀ j j₁ j₂ → Fin.toℕ j ≡ sum B₁′ + q → Fin.toℕ j₁ ≡ sum B₁′ + q →
          Fin.toℕ j₂ ≡ suc (sum B₁′ + q) →
          θ (b₀ ↑ʳ j) ≡ (g (b₀ ↑ʳ j₁) ∥ g (b₀ ↑ʳ j₂))
    at″ j j₁ j₂ e e₁ e₂ = at (b₀ ↑ʳ j) (b₀ ↑ʳ j₁) (b₀ ↑ʳ j₂)
                             (Fin.toℕ-↑ʳ b₀ j  ■ cong (b₀ +_) e  ■ p≡)
                             (Fin.toℕ-↑ʳ b₀ j₁ ■ cong (b₀ +_) e₁ ■ p≡)
                             (Fin.toℕ-↑ʳ b₀ j₂ ■ cong (b₀ +_) e₂
                               ■ Nat.+-suc b₀ (sum B₁′ + q) ■ cong suc p≡)
    hi″ : ∀ j j′ → sum B₁′ + q Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
          θ (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    hi″ j j′ gt e = hi (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< Fin.toℕ (b₀ ↑ʳ j)) p≡
                         (subst (b₀ + (sum B₁′ + q) Nat.<_) (sym (Fin.toℕ-↑ʳ b₀ j))
                           (Nat.+-monoʳ-< b₀ gt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e
                         ■ Nat.+-suc b₀ (Fin.toℕ j) ■ cong suc (sym (Fin.toℕ-↑ʳ b₀ j)))
    IH = sb-rsplit B₁′ q b B₂ {sum B₁′ + q} refl (θ ∘ 𝐂.wkˡ b₀) (g ∘ 𝐂.wkˡ b₀) lo″ at″ hi″

------------------------------------------------------------------------
-- Plumbing for the call sites.

-- A renaming followed by a struct substitution collapses to one renaming
-- whenever the substitution is a renaming on the relevant image.
σ∘ : ∀ {m n k} (α : Struct m) (ρ : m 𝐂.→ᵣ n) (θ : n 𝐂.→ₛ k) (ψ : m 𝐂.→ᵣ k) →
     (∀ y → θ (ρ y) ≡ ` (ψ y)) →
     α 𝐂.⋯ₛ (`_ ∘ ρ) 𝐂.⋯ₛ θ ≡ α 𝐂.⋯ₛ (`_ ∘ ψ)
σ∘ α ρ θ ψ e = cong (𝐂._⋯ₛ θ) (sym (⋯ᵣ⇒ₛ α ρ)) ■ ⋯ᵣₛ α ρ θ ■ ⋯ₛ-cong α e

𝓅∘ : ∀ {m n k} (𝒫 : CxPat m) (ρ : m 𝐂.→ᵣ n) (θ : n 𝐂.→ₛ k) (ψ : m 𝐂.→ᵣ k) →
     (∀ y → θ (ρ y) ≡ ` (ψ y)) →
     (𝒫 ⋯𝓅 (`_ ∘ ρ)) ⋯𝓅 θ ≡ 𝒫 ⋯𝓅 (`_ ∘ ψ)
𝓅∘ []             ρ θ ψ e = refl
𝓅∘ ((d , α) ∷ 𝒫) ρ θ ψ e = cong₂ _∷_ (cong (d ,_) (σ∘ α ρ θ ψ e)) (𝓅∘ 𝒫 ρ θ ψ e)

join-unitʳ : ∀ {Γ : Ctx N} {α : Struct N} (d : Dir) → Γ ∶ join d α [] ≈ α
join-unitʳ 𝟙 = ∥-unit₂
join-unitʳ L = ;-unit₂
join-unitʳ R = ;-unit₁
