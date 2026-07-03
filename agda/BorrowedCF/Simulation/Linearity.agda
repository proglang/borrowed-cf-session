module BorrowedCF.Simulation.Linearity where

-- | LINEARITY SOUNDNESS for the channel-op simulation cases.
--   Originally built INSIDE BorrowedCF.Simulation.Theorems (for the R-Discard
--   b=0 vacuity witness `discard-b0-vac`); hoisted here so that the confinement
--   lemmas in BorrowedCF.Simulation.SplitConfine (which is imported by the case
--   modules, hence cannot import Theorems) can reuse them.
--
--   Core results: `conf-Tm` / `conf-Proc` — a well-typed term/process never
--   has more structural occurrences of a non-Unr variable than it textually
--   contains; together with `countTm-avoid` / `countProc-avoid` (factoring
--   through an avoiding renaming gives count 0) this drives the "the consumed
--   linear block is not referenced by E / P" arguments.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_)

open import BorrowedCF.Simulation.Confine
  using ( count; count-self; count0⇒∉dom; ∉dom⇒count0; count-≈; unrCx⇒count0
        ; count-join-Dir; count-join-PS; count-wk-suc; count-wk-zero)
open import BorrowedCF.Context using (dom; _∉_; _∈_; UnrCx; biasedDir; join; Dir; ParSeq)
open import BorrowedCF.Context.Subcontext
  using (_∶_≼_; ≼-refl; ≼-∅; ≼-wk; ≼-trans; ≼-cong-; ; ≼-cong-∥)
open import BorrowedCF.Types using (Unr; Arr)
import BorrowedCF.Context.Substitution as 𝐂S
import BorrowedCF.Context.Base as B
open import BorrowedCF.Simulation.StructDom using (count-⋯ᵣwkʳ-↑ʳ; count-weaken*-shift)
open import BorrowedCF.Context.Base using (_∥_; _⸴*_) renaming (`_ to `ˢ_)
open Nat using (_≤_; z≤n; s≤s; ≤-refl; ≤-reflexive; ≤-trans; m≤m+n; m≤n+m
               ; +-mono-≤; +-identityʳ; +-comm; +-assoc; n≤0⇒n≡0)

-- Occurrence count of a variable in a term.
countTm : 𝔽 n → Tm n → ℕ
countTm x (` y) with x Fin.≟ y
... | yes _ = 1
... | no  _ = 0
countTm x (K c) = 0
countTm x (ƛ d e) = countTm (suc x) e
countTm x (μ e) = countTm (suc x) e
countTm x (e₁ ·⟨ d ⟩ e₂) = countTm x e₁ + countTm x e₂
countTm x (e₁ ; e₂) = countTm x e₁ + countTm x e₂
countTm x (e₁ ⊗ e₂) = countTm x e₁ + countTm x e₂
countTm x (`let e₁ `in e₂) = countTm x e₁ + countTm (suc x) e₂
countTm x (`let⊗ e₁ `in e₂) = countTm x e₁ + countTm (suc (suc x)) e₂
countTm x (`inj i e) = countTm x e
countTm x (`case e `of⟨ e₁ ; e₂ ⟩) = countTm x e + (countTm (suc x) e₁ + countTm (suc x) e₂)

-- A renaming that avoids x contributes no x-occurrences after substitution.
avoid↑ : {ρ : m →ᵣ n} {x : 𝔽 n} → (∀ y → ρ y ≢ x) → (∀ y → (ρ ↑) y ≢ suc x)
avoid↑ av zero    ()
avoid↑ av (suc y) eq = av y (Fin.suc-injective eq)

countTm-avoid : (e : Tm m) {ρ : m →ᵣ n} {x : 𝔽 n} → (∀ y → ρ y ≢ x) → countTm x (e ⋯ ρ) ≡ 0
countTm-avoid (` y) {ρ} {x} av with x Fin.≟ ρ y
... | yes eq = ⊥-elim (av y (sym eq))
... | no  _  = refl
countTm-avoid (K c) av = refl
countTm-avoid (ƛ d e) av = countTm-avoid e (avoid↑ av)
countTm-avoid (μ e) av = countTm-avoid e (avoid↑ av)
countTm-avoid (e₁ ·⟨ d ⟩ e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ av)
countTm-avoid (e₁ ; e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ av)
countTm-avoid (e₁ ⊗ e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ av)
countTm-avoid (`let e₁ `in e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ (avoid↑ av))
countTm-avoid (`let⊗ e₁ `in e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ (avoid↑ (avoid↑ av)))
countTm-avoid (`inj i e) av = countTm-avoid e av
countTm-avoid (`case e `of⟨ e₁ ; e₂ ⟩) av =
  cong₂ _+_ (countTm-avoid e av) (cong₂ _+_ (countTm-avoid e₁ (avoid↑ av)) (countTm-avoid e₂ (avoid↑ av)))

-- ≼ never INCREASES the multiplicity of a non-unrestricted variable either:
-- the reverse of CF.≼⇒count≤.  (≼-∅ lands on an all-Unr struct, count 0.)
≼⇒count≥ : {Γ : Ctx n} {α β : Struct n} {x : 𝔽 n}
         → ¬ Unr (Γ x) → Γ ∶ α ≼ β → count x β ≤ count x α
≼⇒count≥ ¬u (≼-refl eq) = ≤-reflexive (sym (count-≈ ¬u eq))
≼⇒count≥ {x = x} ¬u (≼-∅ {α = α} U) = ≤-reflexive (unrCx⇒count0 ¬u U)
≼⇒count≥ {x = x} ¬u (≼-wk {α₁ = α₁} {α₂ = α₂} {β₁ = β₁} {β₂ = β₂}) =
  ≤-reflexive (lemma (count x α₁) (count x β₁) (count x α₂) (count x β₂))
  where
    lemma : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lemma a b c d rewrite +-assoc a b (c + d) | sym (+-assoc b c d) | +-comm b c
                        | +-assoc c b d | sym (+-assoc a c (b + d)) = refl
≼⇒count≥ ¬u (≼-trans p q) = ≤-trans (≼⇒count≥ ¬u q) (≼⇒count≥ ¬u p)
≼⇒count≥ ¬u (≼-cong-; p q) = +-mono-≤ (≼⇒count≥ ¬u p) (≼⇒count≥ ¬u q)
≼⇒count≥ ¬u (≼-cong-∥ p q) = +-mono-≤ (≼⇒count≥ ¬u p) (≼⇒count≥ ¬u q)

count-suc-zero : (x : 𝔽 n) → count {suc n} (suc x) (`ˢ 0F) ≡ 0
count-suc-zero x with suc x Fin.≟ 0F
... | no _ = refl

count-bind-Dir : (d : Dir) (γ : Struct n) (x : 𝔽 n)
               → count x γ ≡ count (suc x) (join d (`ˢ 0F) (𝐂S.wk γ))
count-bind-Dir d γ x =
  sym (count-join-Dir d (suc x) (`ˢ 0F) (𝐂S.wk γ)
       ■ cong₂ _+_ (count-suc-zero x) (count-wk-suc γ x))

count-bind-PS : (p/s : ParSeq) (γ : Struct n) (x : 𝔽 n)
              → count x γ ≡ count (suc x) (join p/s (`ˢ 0F) (𝐂S.wk γ))
count-bind-PS p/s γ x =
  sym (count-join-PS p/s (suc x) (`ˢ 0F) (𝐂S.wk γ)
       ■ cong₂ _+_ (count-suc-zero x) (count-wk-suc γ x))

count≡countTm-var : (x y : 𝔽 n) → count x (`ˢ y) ≡ countTm x (` y)
count≡countTm-var x y with x Fin.≟ y
... | yes _ = refl
... | no  _ = refl

-- LINEARITY SOUNDNESS (term level): the ordered context never claims more
-- occurrences of a non-Unr variable than the term actually contains.
conf-Tm : {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} {x : 𝔽 n}
        → Γ ; γ ⊢ e ∶ T ∣ ϵ → ¬ Unr (Γ x) → count x γ ≤ countTm x e
conf-Tm (T-Const _) ¬u = z≤n
conf-Tm {x = x} (T-Var y _) ¬u = ≤-reflexive (count≡countTm-var x y)
conf-Tm {γ = γ} {x = x} (T-Abs {a = a} _ _ ⊢e) ¬u =
  ≤-trans (≤-reflexive (count-bind-Dir (Arr.dir a) γ x)) (conf-Tm ⊢e ¬u)
conf-Tm {γ = γ} {x = x} (T-AbsRec _ _ ⊢e) ¬u =
  ≤-trans (≤-reflexive (eq γ x)) (conf-Tm ⊢e ¬u)
  where
    cz : (k : 𝔽 (suc (suc n))) (x : 𝔽 n) → suc (suc x) ≢ k → count (suc (suc x)) (`ˢ k) ≡ 0
    cz k x ne with suc (suc x) Fin.≟ k
    ... | yes p = ⊥-elim (ne p)
    ... | no  _ = refl
    eq : (γ : Struct n) (x : 𝔽 n)
       → count x γ ≡ count (suc (suc x)) ((`ˢ 0F) ∥ (`ˢ 1F) ∥ 𝐂S.wk (𝐂S.wk γ))
    eq γ x = sym (cong₂ _+_ (cz 0F x (λ ())) (cong₂ _+_ (cz 1F x (λ ()))
                 (count-wk-suc (𝐂S.wk γ) (suc x) ■ count-wk-suc γ x)))
conf-Tm (T-AppUnr _ _ ⊢e₁ ⊢e₂) ¬u = +-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u)
conf-Tm (T-AppLin _ _ ⊢e₁ ⊢e₂) ¬u = +-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u)
conf-Tm {x = x} (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢e₁ ⊢e₂) ¬u =
  ≤-trans (≤-reflexive (+-comm (count x γ₂) (count x γ₁)))
          (+-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u))
conf-Tm (T-AppRight _ _ ⊢e₁ ⊢e₂) ¬u = +-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u)
conf-Tm {x = x} (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) ¬u =
  ≤-trans (≤-reflexive (count-join-Dir (biasedDir p/s) x γ₁ γ₂))
          (+-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u))
conf-Tm {x = x} (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ¬u =
  ≤-trans (≤-reflexive (count-join-PS p/s x γ₁ γ₂))
          (+-mono-≤ (conf-Tm ⊢e₁ ¬u)
                    (≤-trans (≤-reflexive (count-bind-PS p/s γ₂ x)) (conf-Tm ⊢e₂ ¬u)))
conf-Tm (T-Seq _ ⊢e₁ ⊢e₂) ¬u = +-mono-≤ (conf-Tm ⊢e₁ ¬u) (conf-Tm ⊢e₂ ¬u)
conf-Tm {x = x} (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) ¬u =
  ≤-trans (≤-reflexive (count-join-PS p/s x γ₁ γ₂))
          (+-mono-≤ (conf-Tm ⊢e₁ ¬u)
                    (≤-trans (≤-reflexive (eq2 γ₂ x)) (conf-Tm ⊢e₂ ¬u)))
  where
    eq2 : (γ : Struct n) (x : 𝔽 n)
        → count x γ ≡ count (suc (suc x))
            (join p/s (join d (`ˢ 0F) (`ˢ 1F)) (𝐂S.wk (𝐂S.wk γ)))
    eq2 γ x = sym (count-join-PS p/s (suc (suc x)) (join d (`ˢ 0F) (`ˢ 1F)) (𝐂S.wk (𝐂S.wk γ))
              ■ cong₂ _+_ (count-join-Dir d (suc (suc x)) (`ˢ 0F) (`ˢ 1F)) refl
              ■ tidy)
      where tidy : (0 + 0) + count (suc (suc x)) (𝐂S.wk (𝐂S.wk γ)) ≡ count x γ
            tidy = count-wk-suc (𝐂S.wk γ) (suc x) ■ count-wk-suc γ x
conf-Tm (T-Inj ⊢e) ¬u = conf-Tm ⊢e ¬u
conf-Tm {x = x} (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) ¬u =
  ≤-trans (≤-reflexive (count-join-PS p/s x γ₁ γ₂))
          (+-mono-≤ (conf-Tm ⊢e ¬u)
                    (≤-trans (≤-trans (≤-reflexive (count-bind-PS p/s γ₂ x)) (conf-Tm ⊢e₁ ¬u))
                             (m≤m+n _ _)))
conf-Tm (T-Conv _ _ ⊢e) ¬u = conf-Tm ⊢e ¬u
conf-Tm ¬u-helper@(T-Weaken γ≤ ⊢e) ¬u = ≤-trans (≼⇒count≥ ¬u γ≤) (conf-Tm ⊢e ¬u)

-- Occurrence count of a variable in a process (shifting under ν binders).
countProc : 𝔽 n → TP.Proc n → ℕ
countProc x (TP.⟪ e ⟫) = countTm x e
countProc x (P TP.∥ Q) = countProc x P + countProc x Q
countProc x (TP.ν B₁ B₂ P) = countProc ((sum B₁ + sum B₂) Fin.↑ʳ x) P

-- countProc avoids x whenever the process factors through a renaming avoiding x.
↑ʳ-avoid : ∀ k {ρ : m →ᵣ n} {x : 𝔽 n} → (∀ y → ρ y ≢ x)
         → (∀ y → (ρ ↑* k) y ≢ (k Fin.↑ʳ x))
↑ʳ-avoid zero    av y       eq = av y eq
↑ʳ-avoid (suc k) av zero    ()
↑ʳ-avoid (suc k) {ρ} av (suc y) eq =
  ↑ʳ-avoid k {ρ} av y (Fin.suc-injective eq)

countProc-avoid : (P : TP.Proc m) {ρ : m →ᵣ n} {x : 𝔽 n}
                → (∀ y → ρ y ≢ x) → countProc x (P TP.⋯ₚ ρ) ≡ 0
countProc-avoid (TP.⟪ e ⟫) av = countTm-avoid e av
countProc-avoid (P TP.∥ Q) av = cong₂ _+_ (countProc-avoid P av) (countProc-avoid Q av)
countProc-avoid (TP.ν B₁ B₂ P) {ρ} {x} av =
  countProc-avoid P (↑ʳ-avoid (sum B₁ + sum B₂) {ρ} av)

-- Lookup past a Functional-vector append: (A ⸴* B)(k ↑ʳ x) = B x.
⸴*-↑ʳ : ∀ {k m} (A : Ctx k) (B : Ctx m) (x : 𝔽 m) → (A ⸴* B) (k Fin.↑ʳ x) ≡ B x
⸴*-↑ʳ {zero}  A B x = refl
⸴*-↑ʳ {suc k} A B x = sym (B.⸴-⸴*-cons {Γ₁ = A} {Γ₂ = B} (suc (k Fin.↑ʳ x))) ■ ⸴*-↑ʳ (A ∘ suc) B x

-- count of the shifted outer variable in the TP-Res body structure = count x γ.
countBody-shift : ∀ (B₁ B₂ : TP.BindGroup) {m} (γ : Struct m) (x : 𝔽 m)
  → count ((sum B₁ + sum B₂) Fin.↑ʳ x)
      ( (TP.structBinder B₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
        ∥ (TP.structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
        ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum B₁ + sum B₂)) )
    ≡ count x γ
countBody-shift B₁ B₂ {m} γ x = cong₂ _+_ (cong₂ _+_ pA pB) pC
  where
    sB = sum B₁ + sum B₂
    hh = sB Fin.↑ʳ x
    toℕ-h : Fin.toℕ hh ≡ sB + Fin.toℕ x
    toℕ-h = Fin.toℕ-↑ʳ sB x
    pA : count hh (TP.structBinder B₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    pA = count-⋯ᵣwkʳ-↑ʳ m (TP.structBinder B₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂)) x
    pB : count hh (TP.structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    pB = count-⋯ᵣwkʳ-↑ʳ m (TP.structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁)) x
    pC : count hh (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ sB) ≡ count x γ
    pC = count-weaken*-shift sB γ x

-- LINEARITY SOUNDNESS (process level).
conf-Proc : {Γ : Ctx n} {γ : Struct n} {Q : TP.Proc n} {x : 𝔽 n}
          → Γ ; γ ⊢ₚ Q → ¬ Unr (Γ x) → count x γ ≤ countProc x Q
conf-Proc (TP.TP-Expr ⊢e) ¬u = conf-Tm ⊢e ¬u
conf-Proc (TP.TP-Par ⊢P ⊢Q) ¬u = +-mono-≤ (conf-Proc ⊢P ¬u) (conf-Proc ⊢Q ¬u)
conf-Proc {γ = γ} {x = x} (TP.TP-Res {B₁ = B₁} {B₂ = B₂} N p ⊢B₁ ⊢B₂ {Γ₁ = Γ₁} {Γ₂ = Γ₂} C C′ ⊢body) ¬u =
  ≤-trans (≤-reflexive (sym (countBody-shift B₁ B₂ γ x)))
          (conf-Proc ⊢body ¬u′)
  where
    ¬u′ : ¬ Unr (((Γ₁ B.⸴* Γ₂) B.⸴* _) ((sum B₁ + sum B₂) Fin.↑ʳ x))
    ¬u′ = subst (λ z → ¬ Unr z) (sym (⸴*-↑ʳ (Γ₁ ⸴* Γ₂) _ x)) ¬u
conf-Proc (TP.TP-Weaken γ≤ ⊢Q) ¬u = ≤-trans (≼⇒count≥ ¬u γ≤) (conf-Proc ⊢Q ¬u)
