module BorrowedCF.TypedEq where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions using (inv-`⊤)
open import BorrowedCF.Context as 𝐂
import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Processes.Typed hiding (⊢-≋; _⊢⋯ₚ⁻¹_)
open import BorrowedCF.ProcessesInv using (⊢⋯ₚ⁻¹)
open import BorrowedCF.Context.Domain
import BorrowedCF.Context.Base as CB
open import BorrowedCF.DescendK using (dom-⋯wkʳ⊆fresh; freshᵏ; fsuc^; fsuc^∉fresh)
open import BorrowedCF.TermsInv using (brₛ)
open import Data.Fin.Subset using (Subset; ∁; _∈_; _∉_; _⊆_; ⁅_⁆; _∪_; inside) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
  using (x∈∁p⇒x∉p; x∉p⇒x∈∁p; x∉∁p⇒x∈p; _∈?_; x∈⁅x⁆; ⊆-trans; p⊆p∪q; q⊆p∪q; x∈p∪q⁻; x∈p∪q⁺; ∉⊥)
open import Data.Vec using (here; there)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)

open Nat.Variables

⋯ₚ-id≗ : (P : Proc n) {ϕ : n →ᵣ n} → ϕ ≗ id → P ⋯ₚ ϕ ≡ P
⋯ₚ-id≗ ⟪ e ⟫ eq = cong ⟪_⟫ (⋯-id e eq)
⋯ₚ-id≗ (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-id≗ P eq) (⋯ₚ-id≗ Q eq)
⋯ₚ-id≗ (ν B₁ B₂ P) eq = cong (ν B₁ B₂) (⋯ₚ-id≗ P (id↑* _ eq))

Inj-weaken* : ∀ {m} k → 𝐂.Inj (weaken* ⦃ Kᵣ ⦄ {n = m} k)
Inj-weaken* k {x} {y} eq =
  Fin.↑ʳ-injective k _ _ (sym (weaken*~wkˡ k x) ■ eq ■ weaken*~wkˡ k y)

swap-swap : ∀ a b {n} (x : 𝔽 (a + b + n)) → swapᵣ b a (swapᵣ a b x) ≡ x
swap-swap a b {n} x =
  cong (Fin.join (a + b) n ∘ Sum.map₁ (Fin.swap b))
       (Fin.splitAt-join (b + a) n (Sum.map₁ (Fin.swap a) (splitAt (a + b) x)))
  ■ cong (Fin.join (a + b) n) (mm (splitAt (a + b) x))
  ■ Fin.join-splitAt (a + b) n x
  where
    mm : (s : 𝔽 (a + b) ⊎ 𝔽 n) → Sum.map₁ (Fin.swap b) (Sum.map₁ (Fin.swap a) s) ≡ s
    mm (inj₁ z) = cong inj₁ (Fin.swap-involutive a z)
    mm (inj₂ w) = refl

swapₚ-inv : ∀ {a b n} (P : Proc (a + b + n)) → (P ⋯ₚ swapᵣ a b) ⋯ₚ swapᵣ b a ≡ P
swapₚ-inv {a} {b} P = fusionₚ P (swapᵣ a b) (swapᵣ b a) ■ ⋯ₚ-id≗ P (swap-swap a b)

assocSwap-swap : ∀ a b {n} (x : 𝔽 (a + (b + n))) → assocSwapᵣ b a (assocSwapᵣ a b x) ≡ x
assocSwap-swap a b {n} x with splitAt a x in eqa
... | inj₁ p rewrite Fin.splitAt-↑ʳ b (a + n) (p ↑ˡ n) | Fin.splitAt-↑ˡ a p n
      = sym (sym (Fin.join-splitAt a (b + n) x) ■ cong (Fin.join a (b + n)) eqa)
... | inj₂ q with splitAt b q in eqb
...   | inj₁ r rewrite Fin.splitAt-↑ˡ b r (a + n)
        = sym (sym (Fin.join-splitAt a (b + n) x)
               ■ cong (Fin.join a (b + n)) eqa
               ■ cong (a ↑ʳ_) (sym (Fin.join-splitAt b n q) ■ cong (Fin.join b n) eqb))
...   | inj₂ s rewrite Fin.splitAt-↑ʳ b (a + n) (a ↑ʳ s) | Fin.splitAt-↑ʳ a n s
        = sym (sym (Fin.join-splitAt a (b + n) x)
               ■ cong (Fin.join a (b + n)) eqa
               ■ cong (a ↑ʳ_) (sym (Fin.join-splitAt b n q) ■ cong (Fin.join b n) eqb))

assocSwapₚ-inv : ∀ {a b n} (P : Proc (a + (b + n))) → (P ⋯ₚ assocSwapᵣ a b) ⋯ₚ assocSwapᵣ b a ≡ P
assocSwapₚ-inv {a} {b} P = fusionₚ P (assocSwapᵣ a b) (assocSwapᵣ b a) ■ ⋯ₚ-id≗ P (assocSwap-swap a b)


νswap-ty : {Γ : Ctx n} → Γ ; γ ⊢ₚ ν B₁ B₂ P → Γ ; γ ⊢ₚ ν B₂ B₁ (P ⋯ₚ swapᵣ (sum B₁) (sum B₂))
νswap-ty {n} {γ = γ} {B₁ = B₁} {B₂ = B₂} p₀
  with Γ₁ , Γ₂ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , bp ← inv-ν p₀ =
  let open ≡-Reasoning
      eq₁ =
        structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ₛ `_ ∘ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ 𝐂.⋯-congᶜ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n) (λ _ → refl) ⟩
        structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ (cong (𝐂._⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)) (𝐂.fusion (structBinder B₂) _ _) ■ 𝐂.fusion (structBinder B₂) _ _) ⟩
        structBinder B₂ 𝐂.⋯ᵣ (𝐂.wkˡ (sum B₁) ·ₖ 𝐂.wkʳ n) ·ₖ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ 𝐂.⋯-cong (structBinder B₂) (𝐂.wkˡ-swap≗wkʳ (sum B₁) (sum B₂)) ⟩
        structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) ·ₖ 𝐂.wkʳ n
          ≡⟨ 𝐂.fusion (structBinder B₂) _ _ ⟨
        structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ n ∎
      eq₂ =
        structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ₛ `_ ∘ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ 𝐂.⋯-congᶜ (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n) (λ _ → refl) ⟩
        structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ (cong (𝐂._⋯ᵣ 𝐂.swapᵣ (sum B₁) (sum B₂)) (𝐂.fusion (structBinder B₁) _ _) ■ 𝐂.fusion (structBinder B₁) _ _) ⟩
        structBinder B₁ 𝐂.⋯ᵣ (𝐂.wkʳ (sum B₂) ·ₖ 𝐂.wkʳ n) ·ₖ 𝐂.swapᵣ (sum B₁) (sum B₂)
          ≡⟨ 𝐂.⋯-cong (structBinder B₁) (𝐂.wkʳ-swap≗wkˡ (sum B₁) (sum B₂)) ⟩
        structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₂) ·ₖ 𝐂.wkʳ n
          ≡⟨ 𝐂.fusion (structBinder B₁) _ _ ⟨
        structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n ∎
      eq = 𝐂.∥-cong
             (≈-trans 𝐂.∥-comm (𝐂.∥-cong (≈-reflexive eq₁) (≈-reflexive eq₂)))
             (≈-reflexive (𝐂.conv-⋯ᵣₛ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ■ 𝐂.weaken*-swap-⋯ γ (sum B₁) (sum B₂)))
  in TP-Res (new-dual N) (dualPol pol) ⊢B₂ ⊢B₁ C′
       (subst (λ z → BindCtx z B₁ Γ₁)
              (cong₂ (λ ss pp → ss ; end pp) (sym (dual-involutive _)) (sym (dualPol-involutive _))) C)
       (TP-Weaken (≼-refl eq) (bp ⊢⋯ₚ ⊢swapᵣ Γ₁ Γ₂))


finA-core : ∀ a b {n} (x : 𝔽 b) → 𝐂.assocSwapᵣ a b (a ↑ʳ (x ↑ˡ n)) ≡ x ↑ˡ (a + n)
finA-core a b {n} x rewrite Fin.splitAt-↑ʳ a (b + n) (x ↑ˡ n) | Fin.splitAt-↑ˡ b x n = refl

finA : ∀ a b {n} → ((𝐂.wkʳ n 𝐂.·ₖ 𝐂.weaken* a) 𝐂.·ₖ 𝐂.assocSwapᵣ a b) ≗ 𝐂.wkʳ {n = b} (a + n)
finA a b {n} x = cong (𝐂.assocSwapᵣ a b) (𝐂.weaken*~wkˡ a (x ↑ˡ n)) ■ finA-core a b x

finB-core : ∀ a b {n} (x : 𝔽 a) → 𝐂.assocSwapᵣ a b (x ↑ˡ (b + n)) ≡ b ↑ʳ (x ↑ˡ n)
finB-core a b {n} x rewrite Fin.splitAt-↑ˡ a x (b + n) = refl

finB : ∀ a b {n} → (𝐂.wkʳ (b + n) 𝐂.·ₖ 𝐂.assocSwapᵣ a b) ≗ (𝐂.wkʳ {n = a} n 𝐂.·ₖ 𝐂.weaken* b)
finB a b {n} x = finB-core a b x ■ sym (𝐂.weaken*~wkˡ b (x ↑ˡ n))

finC-core : ∀ a b {n} (x : 𝔽 n) → 𝐂.assocSwapᵣ a b (a ↑ʳ (b ↑ʳ x)) ≡ b ↑ʳ (a ↑ʳ x)
finC-core a b {n} x rewrite Fin.splitAt-↑ʳ a (b + n) (b ↑ʳ x) | Fin.splitAt-↑ʳ b n x = refl

finC : ∀ a b {n} → ((𝐂.weaken* b 𝐂.·ₖ 𝐂.weaken* a) 𝐂.·ₖ 𝐂.assocSwapᵣ a b) ≗ (𝐂.weaken* {n = n} a 𝐂.·ₖ 𝐂.weaken* b)
finC a b {n} x = cong (𝐂.assocSwapᵣ a b) (cong (𝐂.weaken* a) (𝐂.weaken*~wkˡ b x) ■ 𝐂.weaken*~wkˡ a (b ↑ʳ x))
                  ■ finC-core a b x
                  ■ sym (cong (𝐂.weaken* b) (𝐂.weaken*~wkˡ a x) ■ 𝐂.weaken*~wkˡ b (a ↑ʳ x))

νcomm-ty : {Γ : Ctx n} → Γ ; γ ⊢ₚ ν B₁ B₂ (ν A₁ A₂ P) →
  Γ ; γ ⊢ₚ ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))
νcomm-ty {n} {γ = γ} {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} p₀
  with Γ₁ , Γ₂ , _ , polᵇ , Nᵇ , ⊢B₁ , ⊢B₂ , Cᵇ , Cᵇ′ , pˣ ← inv-ν p₀
  with Γ₃ , Γ₄ , _ , polᵃ , Nᵃ , ⊢A₁ , ⊢A₂ , Cᵃ , Cᵃ′ , pʸ ← inv-ν pˣ
  = let open ≈-Reasoning
        kA = sum A₁ + sum A₂
        kB = sum B₁ + sum B₂
        Z0 = structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)
        Z1 = structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)
        Z2 = structBinder A₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum A₂)
        Z3 = structBinder A₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum A₁)
        l0 = 𝐂.conv-⋯ᵣₛ (Z0 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.weaken* kA) {ρ = 𝐂.assocSwapᵣ kA kB}
           ■ (cong (𝐂._⋯ᵣ 𝐂.assocSwapᵣ kA kB) (𝐂.fusion Z0 (𝐂.wkʳ n) (𝐂.weaken* kA)) ■ 𝐂.fusion Z0 (𝐂.wkʳ n 𝐂.·ₖ 𝐂.weaken* kA) (𝐂.assocSwapᵣ kA kB))
           ■ 𝐂.⋯-cong Z0 (finA kA kB)
        l1 = 𝐂.conv-⋯ᵣₛ (Z1 𝐂.⋯ᵣ 𝐂.wkʳ n 𝐂.⋯ᵣ 𝐂.weaken* kA) {ρ = 𝐂.assocSwapᵣ kA kB}
           ■ (cong (𝐂._⋯ᵣ 𝐂.assocSwapᵣ kA kB) (𝐂.fusion Z1 (𝐂.wkʳ n) (𝐂.weaken* kA)) ■ 𝐂.fusion Z1 (𝐂.wkʳ n 𝐂.·ₖ 𝐂.weaken* kA) (𝐂.assocSwapᵣ kA kB))
           ■ 𝐂.⋯-cong Z1 (finA kA kB)
        l2 = 𝐂.conv-⋯ᵣₛ (Z2 𝐂.⋯ᵣ 𝐂.wkʳ (kB + n)) {ρ = 𝐂.assocSwapᵣ kA kB}
           ■ 𝐂.fusion Z2 (𝐂.wkʳ (kB + n)) (𝐂.assocSwapᵣ kA kB)
           ■ 𝐂.⋯-cong Z2 (finB kA kB)
           ■ sym (𝐂.fusion Z2 (𝐂.wkʳ n) (𝐂.weaken* kB))
        l3 = 𝐂.conv-⋯ᵣₛ (Z3 𝐂.⋯ᵣ 𝐂.wkʳ (kB + n)) {ρ = 𝐂.assocSwapᵣ kA kB}
           ■ 𝐂.fusion Z3 (𝐂.wkʳ (kB + n)) (𝐂.assocSwapᵣ kA kB)
           ■ 𝐂.⋯-cong Z3 (finB kA kB)
           ■ sym (𝐂.fusion Z3 (𝐂.wkʳ n) (𝐂.weaken* kB))
        l4 = 𝐂.conv-⋯ᵣₛ (γ 𝐂.⋯ᵣ 𝐂.weaken* kB 𝐂.⋯ᵣ 𝐂.weaken* kA) {ρ = 𝐂.assocSwapᵣ kA kB}
           ■ (cong (𝐂._⋯ᵣ 𝐂.assocSwapᵣ kA kB) (𝐂.fusion γ (𝐂.weaken* kB) (𝐂.weaken* kA)) ■ 𝐂.fusion γ (𝐂.weaken* kB 𝐂.·ₖ 𝐂.weaken* kA) (𝐂.assocSwapᵣ kA kB))
           ■ 𝐂.⋯-cong γ (finC kA kB)
           ■ sym (𝐂.fusion γ (𝐂.weaken* kA) (𝐂.weaken* kB))
        eq = ≈-trans (≈-sym 𝐂.∥-assoc)
               $ ≈-trans (𝐂.∥-cong 𝐂.∥-comm ≈-refl)
               $ ≈-trans (𝐂.∥-cong (𝐂.∥-cong (𝐂.∥-cong (≈-reflexive l0) (≈-reflexive l1)) (𝐂.∥-cong (≈-reflexive l2) (≈-reflexive l3))) (≈-reflexive l4))
               𝐂.∥-assoc
    in TP-Res Nᵃ polᵃ ⊢A₁ ⊢A₂ Cᵃ Cᵃ′
         $ TP-Res Nᵇ polᵇ ⊢B₁ ⊢B₂ Cᵇ Cᵇ′
         $ TP-Weaken (≼-refl eq) $ pʸ ⊢⋯ₚ ⊢assocSwapᵣ (Γ₃ ⸴* Γ₄) (Γ₁ ⸴* Γ₂)

-- middle-4 exchange for ∥
∥-middle4 : ∀ {n} {Γ : Ctx n} {a b c d} → Γ ∶ (a ∥ b) ∥ (c ∥ d) ≈ (a ∥ c) ∥ (b ∥ d)
∥-middle4 {a = a}{b}{c}{d} = let open ≈-Reasoning in
  begin (a ∥ b) ∥ (c ∥ d) ≈⟨ 𝐂.∥-assoc ⟩
        a ∥ (b ∥ (c ∥ d))  ≈⟨ 𝐂.∥-cong ≈-refl (≈-sym 𝐂.∥-assoc) ⟩
        a ∥ ((b ∥ c) ∥ d)  ≈⟨ 𝐂.∥-cong ≈-refl (𝐂.∥-cong 𝐂.∥-comm ≈-refl) ⟩
        a ∥ ((c ∥ b) ∥ d)  ≈⟨ 𝐂.∥-cong ≈-refl 𝐂.∥-assoc ⟩
        a ∥ (c ∥ (b ∥ d))  ≈⟨ ≈-sym 𝐂.∥-assoc ⟩
        (a ∥ c) ∥ (b ∥ d)  ∎

-- region split of a context by a subset, as a ≼ (works for `;` via ≼-wk)
↓-split≼ : ∀ {n} {Γ : Ctx n} (γ : Struct n) (X : Subset n) → Γ ∶ γ ≼ (γ ↓ X) ∥ (γ ↓ ∁ X)
↓-split≼ (` x) X with x ∈? X | x ∈? ∁ X
... | yes _  | no _    = ≼-refl (≈-sym ∥-unit₂)
... | no _   | yes _   = ≼-refl (≈-sym ∥-unit₁)
... | yes x∈ | yes x∈∁ = ⊥-elim (x∈∁p⇒x∉p x∈∁ x∈)
... | no x∉  | no x∉∁  = ⊥-elim (x∉∁ (x∉p⇒x∈∁p x∉))
↓-split≼ [] X = ≼-refl (≈-sym ∥-unit₁)
↓-split≼ (α ∥ β) X = ≼-trans (≼-cong-∥ (↓-split≼ α X) (↓-split≼ β X)) (≼-refl ∥-middle4)
↓-split≼ (α ; β) X = ≼-trans (≼-cong-; (↓-split≼ α X) (↓-split≼ β X)) ≼-wk

-- a context restricted to a subset disjoint from its domain is ≈ []
↓-disj-empty : ∀ {n} {Γ : Ctx n} (γ : Struct n) {X} → (∀ {y} → y ∈ dom γ → y ∉ X) → Γ ∶ γ ↓ X ≈ []
↓-disj-empty (` x) {X} disj with x ∈? X
... | yes x∈ = ⊥-elim (disj (x∈⁅x⁆ x) x∈)
... | no _ = ≈-refl
↓-disj-empty [] disj = ≈-refl
↓-disj-empty (α ∥ β) disj =
  ≈-trans (𝐂.∥-cong (↓-disj-empty α (λ y∈ → disj (x∈p∪q⁺ (inj₁ y∈))))
                  (↓-disj-empty β (λ y∈ → disj (x∈p∪q⁺ (inj₂ y∈))))) ∥-unit₁
↓-disj-empty (α ; β) disj =
  ≈-trans (;-cong (↓-disj-empty α (λ y∈ → disj (x∈p∪q⁺ (inj₁ y∈))))
                  (↓-disj-empty β (λ y∈ → disj (x∈p∪q⁺ (inj₂ y∈))))) ;-unit₁

-- injectivity of the Context-level weaken*
Inj-wk* : ∀ {n} k → 𝐂.Inj {n} {k + n} (𝐂.weaken* k)
Inj-wk* k {x} {y} eq = ↑ʳ-injective k _ _ (sym (𝐂.weaken*~wkˡ k x) ■ eq ■ 𝐂.weaken*~wkˡ k y)

-- lookup: (Δ ⸴* Γ) at a weakened position is Γ
weaken*-lookup : ∀ {k n} (Δ : Ctx k) (Γ : Ctx n) (x : 𝔽 n) → (Δ ⸴* Γ) (𝐂.weaken* k x) ≡ Γ x
weaken*-lookup {k} {n} Δ Γ x = cong (Δ ⸴* Γ) (𝐂.weaken*~wkˡ k x) ■ lk
  where lk : (Δ ⸴* Γ) (k ↑ʳ x) ≡ Γ x
        lk rewrite Fin.splitAt-↑ʳ k n x = refl

weaken*-pres⇐ : ∀ {ℓ} {P : Pred 𝕋 ℓ} {k n} (Δ : Ctx k) {Γ : Ctx n} →
  𝐂._Preserves[_]_⇐_ ⦃ 𝐂.Kᵣ ⦄ (𝐂.weaken* k) P Γ (Δ ⸴* Γ)
weaken*-pres⇐ {P = P} Δ {Γ} {x} (` u) = subst P (weaken*-lookup Δ Γ x) u

-- weaken*'s image avoids the fresh (binder) region
wk*∈∁fresh : ∀ {n} k (x : 𝔽 n) → 𝐂.weaken* k x ∈ ∁ (freshᵏ n k)
wk*∈∁fresh k x = x∉p⇒x∈∁p (subst (_∉ freshᵏ _ k) (sym (wk*≡fsuc^ k x)) (fsuc^∉fresh k))
  where
    wk*≡fsuc^ : ∀ k (x : 𝔽 n) → 𝐂.weaken* k x ≡ fsuc^ k x
    wk*≡fsuc^ zero    x = refl
    wk*≡fsuc^ (suc k) x = 𝐂.weaken*~wkˡ (suc k) x ■ cong fsuc (sym (𝐂.weaken*~wkˡ k x) ■ wk*≡fsuc^ k x)

dom-⋯wk*⊆∁fresh : ∀ {n} k (X : Struct n) → dom (X 𝐂.⋯ᵣ 𝐂.weaken* k) ⊆ ∁ (freshᵏ n k)
dom-⋯wk*⊆∁fresh k X {y} y∈ with dom-⋯-InImage X {ϕ = 𝐂.weaken* k} y∈
... | x , eq = subst (_∈ ∁ (freshᵏ _ k)) eq (wk*∈∁fresh k x)

-- every non-fresh position is in the image of weaken*
∉fresh⇒image : ∀ {n} k (y : 𝔽 (k + n)) → y ∉ freshᵏ n k → InImage (𝐂.weaken* k) y
∉fresh⇒image zero    y y∉ = y , refl
∉fresh⇒image (suc k) fzero    y∉ = ⊥-elim (y∉ here)
∉fresh⇒image (suc k) (fsuc y′) y∉ =
  let x , eq = ∉fresh⇒image k y′ (λ p → y∉ (there p))
  in x , (𝐂.weaken*~wkˡ (suc k) x ■ cong fsuc (sym (𝐂.weaken*~wkˡ k x)) ■ cong fsuc eq)

-- | Region-split extrusion: from a body context `Γγ₁ ∥ Γγ₂` bounded by
--   `Fr ∥ (γ⋯wk)` (Fr in the binder region), where the left component is a
--   weakened process (P⋯wk, with base strip γ₁′), extrude a base context `ζ₂`
--   for the right component such that Γγ₂ fits the ν-body shape and γ₁′,ζ₂
--   together fit γ.  No P/Q disjointness is needed: the only "drop" is the
--   binder-region content of the weakened left component, which is Unr.
νext-split : ∀ {k n} (Δ : Ctx k) {Γ : Ctx n}
  {Fr Γγ₁ Γγ₂ : Struct (k + n)} {γ γ₁′ : Struct n}
  → dom Fr ⊆ freshᵏ n k
  → (Δ ⸴* Γ) ∶ Γγ₁ ∥ Γγ₂ ≼ Fr ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* k)
  → (Δ ⸴* Γ) ∶ (γ₁′ 𝐂.⋯ᵣ 𝐂.weaken* k) ≼ Γγ₁
  → ∃[ ζ₂ ] ((Δ ⸴* Γ) ∶ Γγ₂ ≼ Fr ∥ (ζ₂ 𝐂.⋯ᵣ 𝐂.weaken* k))
          × (Γ ∶ γ₁′ ∥ ζ₂ ≼ γ)
νext-split {k} {n} Δ {Γ} {Fr} {Γγ₁} {Γγ₂} {γ} {γ₁′} Fr⊆ H1 H2 = ζ₂ , O1 , O2
  where
    base : Subset (k + n)
    base = ∁ (freshᵏ n k)
    γwk = γ 𝐂.⋯ᵣ 𝐂.weaken* k

    pim₁ = preimage {ϕ = 𝐂.weaken* k} (Γγ₁ ↓ base)
             (λ y∈ → ∉fresh⇒image k _ (x∈∁p⇒x∉p (↓-dom Γγ₁ base y∈)))
    ζ₁ = proj₁ pim₁
    e₁ : ζ₁ 𝐂.⋯ᵣ 𝐂.weaken* k ≡ Γγ₁ ↓ base
    e₁ = proj₂ pim₁
    pim₂ = preimage {ϕ = 𝐂.weaken* k} (Γγ₂ ↓ base)
             (λ y∈ → ∉fresh⇒image k _ (x∈∁p⇒x∉p (↓-dom Γγ₂ base y∈)))
    ζ₂ = proj₁ pim₂
    e₂ : ζ₂ 𝐂.⋯ᵣ 𝐂.weaken* k ≡ Γγ₂ ↓ base
    e₂ = proj₂ pim₂

    RHSb≈ : (Δ ⸴* Γ) ∶ (Fr ↓ base) ∥ (γwk ↓ base) ≈ γwk
    RHSb≈ = let open ≈-Reasoning in
      begin (Fr ↓ base) ∥ (γwk ↓ base)
              ≈⟨ 𝐂.∥-cong (↓-disj-empty Fr (λ y∈ y∈b → x∈∁p⇒x∉p y∈b (Fr⊆ y∈))) ≈-refl ⟩
            [] ∥ (γwk ↓ base)   ≈⟨ ∥-unit₁ ⟩
            γwk ↓ base          ≈⟨ ≈-reflexive (↓-identity-⊆ γwk (dom-⋯wk*⊆∁fresh k γ)) ⟩
            γwk ∎
    H1b : (Δ ⸴* Γ) ∶ (Γγ₁ ↓ base) ∥ (Γγ₂ ↓ base) ≼ γwk
    H1b = ≼-respʳ-≈ RHSb≈ (↓-mono-≼ {X = base} H1)

    C : Γ ∶ ζ₁ ∥ ζ₂ ≼ γ
    C = ≼-⋯⁻¹ {ϕ = 𝐂.weaken* k} (Inj-wk* k) (weaken*-pres⇐ Δ) (weaken*-pres⇐ Δ)
          (subst (λ z → (Δ ⸴* Γ) ∶ z ≼ γwk) (sym (cong₂ _∥_ e₁ e₂)) H1b)

    D : Γ ∶ γ₁′ ≼ ζ₁
    D = ≼-⋯⁻¹ {ϕ = 𝐂.weaken* k} (Inj-wk* k) (weaken*-pres⇐ Δ) (weaken*-pres⇐ Δ)
          (subst₂ (λ a b → (Δ ⸴* Γ) ∶ a ≼ b)
                  (↓-identity-⊆ (γ₁′ 𝐂.⋯ᵣ 𝐂.weaken* k) {∁ (freshᵏ n k)} (dom-⋯wk*⊆∁fresh k γ₁′))
                  (sym e₁) (↓-mono-≼ {X = base} H2))

    O2 : Γ ∶ γ₁′ ∥ ζ₂ ≼ γ
    O2 = ≼-trans (≼-cong-∥ D (≼-refl ≈-refl)) C

    Γγ₁f-Unr : AllCx Unr (Δ ⸴* Γ) (Γγ₁ ↓ freshᵏ n k)
    Γγ₁f-Unr = ↓-⊆ Γγ₁ (λ y∈ → x∉p⇒x∈∁p (λ y∈d → x∈∁p⇒x∉p (dom-⋯wk*⊆∁fresh k γ₁′ y∈d) y∈))
                    (≼⇒extra-Unr H2)

    RHSf≈ : (Δ ⸴* Γ) ∶ (Fr ↓ freshᵏ n k) ∥ (γwk ↓ freshᵏ n k) ≈ Fr
    RHSf≈ = let open ≈-Reasoning in
      begin (Fr ↓ freshᵏ n k) ∥ (γwk ↓ freshᵏ n k)
              ≈⟨ 𝐂.∥-cong (≈-reflexive (↓-identity-⊆ Fr Fr⊆)) ≈-refl ⟩
            Fr ∥ (γwk ↓ freshᵏ n k)
              ≈⟨ 𝐂.∥-cong ≈-refl (↓-disj-empty γwk (λ y∈ → x∈∁p⇒x∉p (dom-⋯wk*⊆∁fresh k γ y∈))) ⟩
            Fr ∥ []   ≈⟨ ∥-unit₂ ⟩
            Fr ∎

    F : (Δ ⸴* Γ) ∶ (Γγ₂ ↓ freshᵏ n k) ≼ Fr
    F = ≼-trans (≼-trans (≼-refl (≈-sym ∥-unit₁)) (≼-cong-∥ (≼-∅ Γγ₁f-Unr) (≼-refl ≈-refl)))
                (≼-respʳ-≈ RHSf≈ (↓-mono-≼ {X = freshᵏ n k} H1))

    O1 : (Δ ⸴* Γ) ∶ Γγ₂ ≼ Fr ∥ (ζ₂ 𝐂.⋯ᵣ 𝐂.weaken* k)
    O1 = ≼-trans (subst (λ z → (Δ ⸴* Γ) ∶ Γγ₂ ≼ (Γγ₂ ↓ freshᵏ n k) ∥ z)
                        (sym e₂) (↓-split≼ Γγ₂ (freshᵏ n k)))
                 (≼-cong-∥ F (≼-refl ≈-refl))

-- convenience wrapper: body in the natural right-nested TP-Res shape
-- `Frₐ ∥ (Frᵦ ∥ (γ⋯wk))`, so callers need no 𝐂.∥-assoc reshaping.
νext-split′ : ∀ {k n} (Δ : Ctx k) {Γ : Ctx n}
  {Frₐ Frᵦ Γγ₁ Γγ₂ : Struct (k + n)} {γ γ₁′ : Struct n}
  → dom Frₐ ⊆ freshᵏ n k → dom Frᵦ ⊆ freshᵏ n k
  → (Δ ⸴* Γ) ∶ Γγ₁ ∥ Γγ₂ ≼ Frₐ ∥ (Frᵦ ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* k))
  → (Δ ⸴* Γ) ∶ (γ₁′ 𝐂.⋯ᵣ 𝐂.weaken* k) ≼ Γγ₁
  → ∃[ ζ₂ ] ((Δ ⸴* Γ) ∶ Γγ₂ ≼ Frₐ ∥ (Frᵦ ∥ (ζ₂ 𝐂.⋯ᵣ 𝐂.weaken* k)))
          × (Γ ∶ γ₁′ ∥ ζ₂ ≼ γ)
νext-split′ {k} {n} Δ {Γ} {Frₐ} {Frᵦ} {Γγ₁} {Γγ₂} {γ} {γ₁′} Frₐ⊆ Frᵦ⊆ H1 H2 =
  let dom⊆ : dom (Frₐ ∥ Frᵦ) ⊆ freshᵏ n k
      dom⊆ z∈ = [ Frₐ⊆ , Frᵦ⊆ ]′ (x∈p∪q⁻ _ _ z∈)
      ζ₂ , O1 , O2 = νext-split Δ {Fr = Frₐ ∥ Frᵦ} {γ = γ} dom⊆ (≼-respʳ-≈ (≈-sym 𝐂.∥-assoc) H1) H2
  in ζ₂ , ≼-respʳ-≈ 𝐂.∥-assoc O1 , O2


⊢-≋ : ChanCx Γ → P ≋ Q → Γ ; γ ⊢ₚ P → Γ ; γ ⊢ₚ Q
⊢-≋ Γ-S refl     = id
⊢-≋ Γ-S (x ◅ xs) = ⊢-≋ Γ-S xs ∘ go Γ-S x where
  go : ChanCx Γ → SymClosure _≋′_ P Q → Γ ; γ ⊢ₚ P → Γ ; γ ⊢ₚ Q
  go Γ-S (fwd ∥-comm′) p₀
    with _ , _ , γ≤ , p , q ← inv-∥ p₀
    = TP-Weaken (≼-respˡ-≈ 𝐂.∥-comm γ≤) (TP-Par q p)
  go Γ-S (fwd ∥-assoc′) p₀
    with γ₁ , γ′ , ≤₁ , p₁ , p′ ← inv-∥ p₀
    with γ₂ , γ₃ , ≤₂ , p₂ , p₃ ← inv-∥ p′
    = let open ≼-Reasoning in
      let ≤γ = begin (γ₁ ∥ γ₂) ∥ γ₃  ≈⟨ 𝐂.∥-assoc ⟩
                     γ₁ ∥ (γ₂ ∥ γ₃)  ≲⟨ ≼-cong-∥ (≼-refl refl) ≤₂ ⟩
                     γ₁ ∥ γ′         ≲⟨ ≤₁ ⟩
                     _               ∎
      in TP-Weaken ≤γ (TP-Par (TP-Par p₁ p₂) p₃)
  go Γ-S (fwd ∥-unit′) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    with _ , []≤  ← inv-`⊤ Γ-S V-K (inv-⟪⟫ p)
    = let open ≼-Reasoning in
      let ≤γ = begin γ₂       ≈⟨ 𝐂.∥-unit₁ ⟨
                     [] ∥ γ₂  ≲⟨ ≼-cong-∥ []≤ (≼-refl refl) ⟩
                     γ₁ ∥ γ₂  ≲⟨ ≤γ ⟩
                     _        ∎
      in TP-Weaken ≤γ q
  go Γ-S (fwd ν-swap′) p₀ = νswap-ty p₀
  go Γ-S (fwd ν-comm′) p₀ = νcomm-ty p₀
  go {γ = γ} Γ-S (fwd (ν-ext′ {B₁ = B₁} {B₂})) p₀
    with γ₁ , γ₂ , ≤γ , p₁ , p′ ← inv-∥ p₀
    with Γ₁ , Γ₂ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p₂ ← inv-ν p′
    = let
      open ≼-Reasoning
      ≤ = begin
            (γ₁ 𝐂.⋯ₛ 𝐂.weaken* (sum B₁ + sum B₂))
              ∥ ((structBinder B₁ 𝐂.⋯ 𝐂.wkʳ (sum B₂) 𝐂.⋯ 𝐂.wkʳ _)
                   ∥ (structBinder B₂ 𝐂.⋯ 𝐂.wkˡ (sum B₁) 𝐂.⋯ 𝐂.wkʳ _)
                   ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≡⟨ cong (_∥ _) (𝐂.⋯-congᶜ ⦃ 𝐂.Kₛ ⦄ ⦃ 𝐂.Kᵣ ⦄ γ₁ λ y → 𝐂.weaken*~wkˡ _ y ■ cong `_ (sym (𝐂.weaken*~wkˡ _ y))) ⟩
            (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
             ∥ ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≈⟨ 𝐂.∥-assoc ⟨
            (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
             ∥ ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
                  ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _))
             ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ≈⟨ 𝐂.∥-cong 𝐂.∥-comm ≈-refl ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
              ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ≈⟨ 𝐂.∥-assoc ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ ((γ₁ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)) ∥ (γ₂ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
          ≲⟨ ≼-cong-∥ (≼-refl refl) (𝐂.≼-⋯ (𝐂.wk*-preserves (Γ₁ ⸴* Γ₂)) (𝐂.wk*-preserves (Γ₁ ⸴* Γ₂)) ≤γ) ⟩
            (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
              ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))
          ∎
    in TP-Res N pol ⊢B₁ ⊢B₂ C C′ $ TP-Weaken ≤ $ TP-Par (p₁ ⊢⋯ₚ ⊢weaken* _ _) p₂
  go Γ-S (fwd (∥-cong′ eq)) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    = TP-Weaken ≤γ (TP-Par (go Γ-S (fwd eq) p) q)
  go Γ-S (fwd (ν-cong′ eq)) p₀
    with _ , _ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p ← inv-ν p₀
    = TP-Res N pol ⊢B₁ ⊢B₂ C C′ (go (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) (fwd eq) p)
  go Γ-S (bwd ∥-comm′) p₀
    with _ , _ , γ≤ , p , q ← inv-∥ p₀
    = TP-Weaken (≼-respˡ-≈ 𝐂.∥-comm γ≤) (TP-Par q p)
  go Γ-S (bwd ∥-assoc′) p₀
    with γ′ , γ₃ , ≤₁ , p′ , p₃ ← inv-∥ p₀
    with γ₁ , γ₂ , ≤₂ , p₁ , p₂ ← inv-∥ p′
    = let open ≼-Reasoning in
      let ≤γ = begin γ₁ ∥ (γ₂ ∥ γ₃)  ≈⟨ 𝐂.∥-assoc ⟨
                     (γ₁ ∥ γ₂) ∥ γ₃  ≲⟨ ≼-cong-∥ ≤₂ (≼-refl refl) ⟩
                     γ′ ∥ γ₃         ≲⟨ ≤₁ ⟩
                     _               ∎
      in TP-Weaken ≤γ (TP-Par p₁ (TP-Par p₂ p₃))
  go Γ-S (bwd ∥-unit′) p₀ = TP-Weaken (≼-refl 𝐂.∥-unit₁) (TP-Par (TP-Expr (T-Conv `⊤ ℙ≤ϵ (T-Const `unit))) p₀)
  go Γ-S (bwd (ν-swap′ {B₁ = B₁} {B₂ = B₂})) p₀ =
    subst (λ z → _ ; _ ⊢ₚ ν B₁ B₂ z) (swapₚ-inv {sum B₁} {sum B₂} _) (νswap-ty p₀)
  go Γ-S (bwd (ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂})) p₀ =
    subst (λ z → _ ; _ ⊢ₚ ν B₁ B₂ (ν A₁ A₂ z))
          (assocSwapₚ-inv {sum A₁ + sum A₂} {sum B₁ + sum B₂} _) (νcomm-ty p₀)
  go {Γ = Γ₀} Γ-S (bwd (ν-ext′ {B₁ = B₁} {B₂ = B₂})) p₀
    with Γ₁ , Γ₂ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p′ ← inv-ν p₀
    with Γγ₁ , Γγ₂ , H1raw , p₁ , p₂ ← inv-∥ p′
    with γ₁′ , H2 , p₁′ ← ⊢⋯ₚ⁻¹ (Inj-weaken* (sum B₁ + sum B₂)) p₁ (⊢weaken* (Γ₁ ⸴* Γ₂) _)
    with ζ₂ , O1 , O2 ← νext-split (Γ₁ ⸴* Γ₂)
                          (λ {z} z∈ → [ dom-⋯wkʳ⊆fresh (structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂))
                                     , dom-⋯wkʳ⊆fresh (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁)) ]′
                                     (x∈p∪q⁻ _ _ z∈))
                          H1raw
                          (subst (λ z → _ ∶ z ≼ Γγ₁)
                             (brₛ (⊢weaken* (Γ₁ ⸴* Γ₂) Γ₀) γ₁′
                              ■ 𝐂.⋯-cong γ₁′ (λ x → weaken*~wkˡ (sum B₁ + sum B₂) x
                                                    ■ sym (𝐂.weaken*~wkˡ (sum B₁ + sum B₂) x)))
                             H2)
    = TP-Weaken O2 (TP-Par p₁′ (TP-Res N pol ⊢B₁ ⊢B₂ C C′ (TP-Weaken O1 p₂)))
  go Γ-S (bwd (∥-cong′ eq)) p₀
    with γ₁ , γ₂ , ≤γ , p , q ← inv-∥ p₀
    = TP-Weaken ≤γ (TP-Par (go Γ-S (bwd eq) p) q)
  go Γ-S (bwd (ν-cong′ eq)) p₀
    with _ , _ , _ , pol , N , ⊢B₁ , ⊢B₂ , C , C′ , p ← inv-ν p₀
    = TP-Res N pol ⊢B₁ ⊢B₂ C C′ (go (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S) (bwd eq) p)
