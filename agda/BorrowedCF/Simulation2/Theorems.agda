module BorrowedCF.Simulation2.Theorems where

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

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Frames using (⋯→-⋯ₛ; frame-plug*; frame*-⋯; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation2.Congruence using (U-≋)
open import BorrowedCF.Simulation2.Theorems.Choice using (U-choice)
open import BorrowedCF.Simulation2.Theorems.Drop using (U-drop)
open import BorrowedCF.Simulation2.Theorems.Com using (U-com)
open import BorrowedCF.Simulation2.TranslationProperties using (≡→≋; UB-cong-─→; UB-cong; ≋-subst; ─→-subst; Value-subst; chanTriple-V; VChan; U-⋯ₚ; U-cong)
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

open TP using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; ⊢-≋; bindCtx⇒chanCtx)

------------------------------------------------------------------------
-- R-Discard (b=0, nonempty tail) VACUITY infrastructure.
------------------------------------------------------------------------

open import BorrowedCF.Simulation2.Confine as CF
  using ( count; count-self; count0⇒∉dom; ∉dom⇒count0; count-≈; unrCx⇒count0
        ; count-join-Dir; count-join-PS; count-wk-suc; count-wk-zero)
open import BorrowedCF.Context using (dom; _∉_; _∈_; UnrCx; biasedDir; join; Dir; ParSeq)
open import BorrowedCF.Context.Subcontext
  using (_∶_≼_; ≼-refl; ≼-∅; ≼-wk; ≼-trans; ≼-cong-; ; ≼-cong-∥)
open import BorrowedCF.Types using (Unr; Arr)
import BorrowedCF.Context.Substitution as 𝐂S
import BorrowedCF.Context.Base as B
open import BorrowedCF.Simulation2.StructDom using (count-⋯ᵣwkʳ-↑ʳ; count-weaken*-shift)
open import BorrowedCF.Context.Base using (_∥_; _⸴*_) renaming (`_ to `ˢ_)
open Nat using (_≤_; z≤n; s≤s; ≤-refl; ≤-reflexive; ≤-trans; m≤m+n; m≤n+m
               ; +-mono-≤; +-identityʳ; +-comm; +-assoc; n≤0⇒n≡0)

-- Occurrence count of a variable in a term.
countTm : 𝔽 n → Tm n → ℕ
countTm x (` y) with x Fin.≟ y
... | yes _ = 1
... | no  _ = 0
countTm x (K c) = 0
countTm x (ƛ e) = countTm (suc x) e
countTm x (μ e) = countTm (suc x) e
countTm x (e₁ · e₂) = countTm x e₁ + countTm x e₂
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
countTm-avoid (ƛ e) av = countTm-avoid e (avoid↑ av)
countTm-avoid (μ e) av = countTm-avoid e (avoid↑ av)
countTm-avoid (e₁ · e₂) av = cong₂ _+_ (countTm-avoid e₁ av) (countTm-avoid e₂ av)
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
conf-Proc {γ = γ} {x = x} (TP.TP-Res {B₁ = B₁} {B₂ = B₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} N ⊢B₁ ⊢B₂ C C′ ⊢body) ¬u =
  ≤-trans (≤-reflexive (sym (countBody-shift B₁ B₂ γ x)))
          (conf-Proc ⊢body ¬u′)
  where
    ¬u′ : ¬ Unr (((Γ₁ B.⸴* Γ₂) B.⸴* _) ((sum B₁ + sum B₂) Fin.↑ʳ x))
    ¬u′ = subst (λ z → ¬ Unr z) (sym (⸴*-↑ʳ (Γ₁ ⸴* Γ₂) _ x)) ¬u
conf-Proc (TP.TP-Weaken γ≤ ⊢Q) ¬u = ≤-trans (≼⇒count≥ ¬u γ≤) (conf-Proc ⊢Q ¬u)

open import BorrowedCF.Simulation2.Theorems.B1VacProbe
  using (NoRet; RetTip; noRet-front-cons; noRet-front-last; retTip-≃; noRet-≃; noRet-;-fst)
open import BorrowedCF.Types.Equivalence using (_≃𝕊_; ≃-skips)
open import BorrowedCF.Types.Predicates using (New)
import Relation.Binary.Construct.Closure.Equivalence as EqC
open import BorrowedCF.Simulation2.StructDom using (count-⋯ᵣwkʳ-↑ˡ; count-structBinder-lt)
open import BorrowedCF.Simulation2.Strengthen using (skip-weakenᵣ)

-- The b=0 / nonempty-tail R-Discard redex ν (1 ∷ x ∷ xs) B₂ (P ⋯ₚ weakenᵣ) is
-- UNTYPEABLE: its head borrow ⟨ sA ⟩ is non-Unr (a ret-tip chain, ¬ Skips), so it
-- has structural count 1 at slot 0F, yet the body P ⋯ₚ weakenᵣ avoids 0F, forcing
-- count 0F = 0.  1 ≤ 0 is absurd.  Hence the case is vacuous.
discard-b0-vac :
  {m : ℕ} {Γ : Ctx m} {g : Struct m} {x : ℕ} {xs B₂ : TP.BindGroup}
  {P : TP.Proc (sum (zero ∷ x ∷ xs) + sum B₂ + m)}
  → Γ ; g ⊢ₚ TP.ν (suc zero ∷ x ∷ xs) B₂ (P TP.⋯ₚ weakenᵣ) → ⊥
discard-b0-vac {m} {Γ} {g} {x} {xs} {B₂} {P} ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , s , N , _ , _
    , TP.cons-ret/acq {s₁ = sf} scra Γ≗
        (TP.cons {s₁ = sA} {s₂ = sBh} ¬sk1 s≃1 Γ≗1 (TP.nil skB)) tail , _ , ⊢body
  = Nat.1+n≰n (Nat.≤-trans ge1 le0)
  where
    sC₁ = sum (suc zero ∷ x ∷ xs)
    part1 = TP.structBinder (suc zero ∷ x ∷ xs) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m
    part2 = TP.structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ sC₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ m
    part3 = g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (suc zero ∷ x ∷ xs) + sum B₂)
    βbody : Struct (sum (suc zero ∷ x ∷ xs) + sum B₂ + m)
    βbody = part1 ∥ part2 ∥ part3
    -- head borrow ⟨ sA ⟩ is non-Unr.
    noRet-sf : NoRet sf
    noRet-sf = noRet-;-fst (noRet-≃ (EqC.symmetric _≃𝕊_ scra) (noRet-front-last N))
    ¬SsA : ¬ Skips sA
    ¬SsA skA = ¬sk1 (≃-skips s≃1 (skA Skips.; skB))
    ¬Skips⇒¬Unr-head : ¬ Skips sA → ¬ Unr ⟨ sA ⟩
    ¬Skips⇒¬Unr-head ¬sk ⟨ sk ⟩ = ¬sk sk
    headeq : Γ₁ 0F ≡ ⟨ sA ⟩
    headeq = sym (Γ≗ 0F) ■ sym (Γ≗1 0F)
    ¬u-head : ¬ Unr (Γ₁ 0F)
    ¬u-head = subst (λ z → ¬ Unr z) (sym headeq) (¬Skips⇒¬Unr-head ¬SsA)
    ¬u-body : ¬ Unr (((Γ₁ ⸴* Γ₂) ⸴* Γ) 0F)
    ¬u-body = ¬u-head
    le0 : count 0F βbody ≤ 0
    le0 = ≤-trans (conf-Proc ⊢body ¬u-body)
                  (≤-reflexive (countProc-avoid P skip-weakenᵣ))
    0Fc : 𝔽 sC₁
    0Fc = 0F
    count0-part1 : count 0F part1 ≡ 1
    count0-part1 =
      count-⋯ᵣwkʳ-↑ˡ m (TP.structBinder (suc zero ∷ x ∷ xs) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂)) (0Fc Fin.↑ˡ sum B₂)
      ■ count-⋯ᵣwkʳ-↑ˡ (sum B₂) (TP.structBinder (suc zero ∷ x ∷ xs)) 0Fc
      ■ count-structBinder-lt (suc zero ∷ x ∷ xs) 0Fc (s≤s z≤n)
    ge1 : 1 ≤ count 0F βbody
    ge1 = ≤-trans (≤-reflexive (sym count0-part1))
                  (≤-trans (m≤m+n (count 0F part1) (count 0F part2))
                           (m≤m+n (count 0F part1 + count 0F part2) (count 0F part3)))




□·-cong : {e₁ e₂ : Tm n} → e₁ ≡ e₂ → (□· e₁) ≡ (□· e₂)
□·-cong refl = refl

·□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ·□) ≡ (V₂ ·□)
·□-cong refl = cong _·□ Value-irr

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (□· e₂)        Vϕ Vψ eq = cong □·_ (⋯-cong e₂ eq)
frame-cong (V₁ ·□)        Vϕ Vψ eq = ·□-cong (⋯-cong (vTm V₁) eq)
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
frame-fusion-gen (□· e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □·_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ·□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ·□-cong (fusion (vTm V₁) ϕ ξ)
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
    cA : Tm (1 + (1 + (2 + n)))
    cA = chanTriple ((` 0F) , 1F , wk *) ⋯ weaken* ⦃ Kᵣ ⦄ 1
    cB : Tm (1 + (1 + (2 + n)))
    cB = chanTriple ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *)
    A : 1 →ₛ (1 + (1 + (2 + n)))
    A = λ _ → cA
    B : 1 →ₛ (1 + (1 + (2 + n)))
    B = λ _ → cB
    Bσ : m →ₛ (1 + (1 + (2 + n)))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 1
    σ′ : (1 + 1 + m) →ₛ (1 + (1 + (2 + n)))
    σ′ = (A ++ₛ B) ++ₛ Bσ
    VcAch : Value (chanTriple ((` 0F) , 1F , wk *))
    VcAch = V-⊗ (V-⊗ V-` V-`) (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
    VcBch : Value (chanTriple ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *))
    VcBch = V-⊗ (V-⊗ V-` V-`) (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
    VcA : Value cA
    VcA = value-⋯ VcAch (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
    VA : VSub A
    VA = λ _ → VcA
    VB : VSub B
    VB = λ _ → VcBch
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

-- Single-chain case (B₁ = []).
disc-single : (b : ℕ) (B₂ : TP.BindGroup)
              (P : TP.Proc (sum (b ∷ []) + sum B₂ + n))
              (σ : n →ₛ m)
            → U[ TP.ν (suc b ∷ []) B₂ (P TP.⋯ₚ weakenᵣ) ] σ
                UP.≋ U[ TP.ν (b ∷ []) B₂ P ] σ
disc-single b B₂ P σ =
  UP.ν-cong (UB-cong B₂ (* , 1F , *) (λ τ₂ →
    ≡→≋ (U-⋯ₚ P ■ U-cong P (λ i →
      prefix-shift (b + 0)
        (chanTriple (* , 0F , *) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
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
                       ([ const (chanTriple (* , 1F , (` 0F)) ⋯ᵣ weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) , τ₁ ]′
                         (splitAt (suc (suc b')) j))
                     ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
              (λ j → subst Tm (+-suc (syncs (x ∷ xs)) _)
                       ([ const (chanTriple (* , 1F , (` 0F)) ⋯ᵣ weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) , τ₁ ]′
                         (splitAt (suc b') j))
                     ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
              (λ k → cong (λ t → subst Tm (+-suc (syncs (x ∷ xs)) _) t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
                       (inner-shift (suc b')
                         (chanTriple (* , 1F , (` 0F)) ⋯ᵣ weaken* ⦃ Kᵣ ⦄ (syncs (x ∷ xs))) τ₁ k))
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
UB-cong-⊎ (b ∷ [])  cc Vcc h = h _ (λ _ → chanTriple-V cc Vcc)
UB-cong-⊎ {n} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) (Ve₁ , Ve₂) h =
  [ (λ s → inj₁ (⋆-gmap (UP.φ ϕ[ b ]) UR.RU-Sync s)) , (λ e → inj₂ (UP.φ-cong e)) ]′
    (UB-cong-⊎ B (` 0F , suc x , e₂ ⋯ weakenᵣ) (V-` , Ve₂ ⋯ᵛ weakenᵣ)
      (λ σ Vσ → Sum.map (─→ₚ*-subst (sym (+-suc (syncs B) _)))
                        (≋-subst (sym (+-suc (syncs B) _)))
        (h _ (λ y → Value-subst (+-suc (syncs B) _) (argV σ Vσ (splitAt b y))))))
  where
    chV : Value (chanTriple (e₁ ⋯ weakenᵣ , suc x , ` 0F) ⋯ᵣ weaken* ⦃ Kᵣ ⦄ (syncs B))
    chV = value-⋯ (chanTriple-V _ (Ve₁ ⋯ᵛ weakenᵣ , V-`)) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ z → V-`)
    argV : (σ : sum B →ₛ syncs B + suc n) (Vσ : VSub σ)
           (s : 𝔽 b ⊎ 𝔽 (sum B)) →
           Value ([ const (chanTriple (e₁ ⋯ weakenᵣ , suc x , ` 0F) ⋯ᵣ weaken* ⦃ Kᵣ ⦄ (syncs B)) , σ ]′ s)
    argV σ Vσ (inj₁ j) = chV
    argV σ Vσ (inj₂ k) = Vσ k

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
sim→ σ Vσ Γ-S ⊢P TR.R-LSplit =
  inj₁ {! R-LSplit → RU-LSplit: binder-order transpose + frame-plug*; cf. Simulation/Theorems/LSplit.agda !}

-- R-RSplit: remote split allocates a fresh φ drop.  Needs typing + transpose → RU-RSplit.
--   cf. old Simulation/Theorems/RSplit.agda.
sim→ σ Vσ Γ-S ⊢P TR.R-RSplit =
  inj₁ {! R-RSplit → RU-RSplit: binder-order transpose + frame-plug*; cf. Simulation/Theorems/RSplit.agda !}

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
sim→ σ Vσ Γ-S ⊢P (TR.R-Drop {b₁} {B₁} {B₂} {P} {E}) =
  U-drop σ Vσ Γ-S {E = E} ⊢P

-- R-Acq.  Goal (?6):
--   U[ ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪ E[ acq·(`0F) ] ⟫ ∥ P) ] σ
--     ─→ₚ*  U[ ν (suc b₁ ∷ B₁) B₂ (⟪ E[`0F] ⟫ ∥ P) ] σ.
-- Two untyped steps: RU-Acquire (φ acq → φ done, consuming a set/`1F` junction)
-- then RU-Cleanup (φ done P → P ⋯ₚ ⦅*⦆ₛ).  Same blocker as R-Drop: the acquired
-- handle `0F` only becomes 𝓒[ `0F × 1F × e ] (junction flag exactly 1F = set)
-- under the typing chain, FALSE under VSub alone, and the φ acq must be commuted
-- past the rest of the φ-nest to the leaf.  Needs the SAME ported acq-confine /
-- transpose machinery (memory: "needs acq-confine").  BLOCKED.
sim→ σ Vσ Γ-S ⊢P TR.R-Acq =
  inj₁ {! R-Acq → RU-Acquire ; RU-Cleanup: needs ported acq-confine (chanTriple junction-flag = set 1F) + binder-order transpose; same un-portable Simulation confine subsystem as R-Drop !}

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
    σ₁ = λ _ → t₁
    σ₂ : 1 →ₛ (2 + n)
    σ₂ = λ _ → t₂
    Bσ : m →ₛ (2 + n)
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    σ′ : (1 + 1 + m) →ₛ (2 + n)
    σ′ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂) ++ₛ Bσ
    Vσ₁ : VSub σ₁
    Vσ₁ = λ _ → V-⊗ (V-⊗ V-K V-`) V-K
    Vσ₂ : VSub σ₂
    Vσ₂ = λ _ → V-⊗ (V-⊗ V-K V-`) V-K
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
          UP.⟪ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end pol) · (` x) ]*) ⋯ σ′ ⟫
          ≡ UP.⟪ (frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end pol) · t ]* ⟫
    thr pol E* x t eq =
      cong UP.⟪_⟫ (frame-plug* (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E*) (cong (K (`end pol) ·_) eq))

-- R-Discard: ν (suc b ∷ B₁) B₂ (P ⋯ₚ weakenr) → ν (b ∷ B₁) B₂ P.  NEW rule.  U[ ]
--   on the two sides differs by one φ binder plus a P-renaming; plausibly RU-Cleanup
--   (φ done → subst *) after a structural massage, OR a dedicated argument.  There is
--   NO untyped rule literally named "Discard".
-- R-Discard: administrative.  SILENT on the untyped side: U[LHS]σ ≡ U[RHS]σ
--   definitionally (refl) when the discarded head retains its flag, i.e. for a
--   single chain (B₁ = []) for any b, and for a nonempty tail when b ≥ 1 (the
--   junction flag stays φ drop).  The b = 0 / nonempty-tail sub-case flips
--   φ drop → φ acq and is the one known gap (see DiscardCheck.agda).
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b = b} {B₁ = []} {B₂ = B₂} {P = P}) = inj₂ (disc-single b B₂ P σ)
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b = suc b'} {B₁ = x ∷ xs} {B₂ = B₂} {P = P}) = inj₂ (disc-multi b' x xs B₂ P σ)
-- R-Discard b=0 / nonempty tail: VACUOUS.  The discarded head borrow is a non-Unr
-- ret-tip chain (structural count 1 at slot 0F), but the body P ⋯ₚ weakenᵣ avoids
-- 0F, forcing count 0F = 0 — a linearity contradiction (discard-b0-vac).
sim→ σ Vσ Γ-S ⊢P (TR.R-Discard {b = zero}  {B₁ = _ ∷ _}) =
  ⊥-elim (discard-b0-vac ⊢P)

-- R-Bind: congruence under ν B₁ B₂.  U[ν B₁ B₂ ·] = ν (UB[B₁] (UB[B₂] U[·])); must
--   recurse under the UB telescope → nested RU-Res/RU-Sync.  Needs a
--   "UB-cong / recurse-under-telescope" lemma.
sim→ σ Vσ Γ-S ⊢P (TR.R-Bind {B₁} {B₂} red)
  with _ , _ , _ , _ , _ , _ , C , C′ , ⊢Q ← inv-ν ⊢P =
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
