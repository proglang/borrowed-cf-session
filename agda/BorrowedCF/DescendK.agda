module BorrowedCF.DescendK where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import BorrowedCF.DescendAbs
open import Data.Fin.Subset using (Subset; ∁; _∈_; _∉_; _⊆_; ⁅_⁆; _∪_; inside) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∉∁p⇒x∈p; x∈∁p⇒x∉p; x∉p⇒x∈∁p; _∈?_; x∈⁅x⁆; ⊆-trans; ⊆-refl; ∪-identityʳ; p⊆p∪q; q⊆p∪q; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; x∈p∪q⁺; ∉⊥)
import Data.Sum as Sum
import Data.Vec as Vec
open import Data.Vec using (_∷_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)

open Nat.Variables

-- k-fold weakening at Struct level
wk^ : (k : ℕ) → Struct n → Struct (k + n)
wk^ zero    γ = γ
wk^ (suc k) γ = 𝐂.wk (wk^ k γ)

-- bridge: k-fold wk ≡ ⋯ weaken* k
wkm≗·weaken : {ϕ : m →ᵣ n} → 𝐂.wkm ϕ ≗ (ϕ 𝐂.·ₖ 𝐂.weakenᵣ)
wkm≗·weaken x = refl

⋯-wkm : (γ : Struct m) {ϕ : m →ᵣ n} → γ 𝐂.⋯ᵣ 𝐂.wkm ϕ ≡ 𝐂.wk (γ 𝐂.⋯ᵣ ϕ)
⋯-wkm γ {ϕ} = 𝐂.⋯-cong γ wkm≗·weaken ■ sym (𝐂.fusion γ ϕ 𝐂.weakenᵣ)

weaken*-wk : (γ : Struct n) → γ 𝐂.⋯ᵣ 𝐂.weaken* (suc k) ≡ 𝐂.wk (γ 𝐂.⋯ᵣ 𝐂.weaken* k)
weaken*-wk {k = k} γ = ⋯-wkm γ {ϕ = 𝐂.weaken* k}

wk^≡weaken* : (k : ℕ) (γ : Struct n) → wk^ k γ ≡ γ 𝐂.⋯ᵣ 𝐂.weaken* k
wk^≡weaken* zero    γ = sym (𝐂.⋯-id γ (λ x → refl))
wk^≡weaken* (suc k) γ = cong 𝐂.wk (wk^≡weaken* k γ) ■ sym (weaken*-wk γ)

Inj-↑* : (k : ℕ) {ρ : m →ᵣ n} → 𝐂.Inj ρ → 𝐂.Inj (ρ 𝐂.↑* k)
Inj-↑* zero    inj = inj
Inj-↑* (suc k) inj = Inj-↑ (Inj-↑* k inj)

⋯ᵏ-↑-wk : (k : ℕ) (γ : Struct m) {ρ : m →ᵣ n} → (wk^ k γ) 𝐂.⋯ (ρ 𝐂.↑* k) ≡ wk^ k (γ 𝐂.⋯ᵣ ρ)
⋯ᵏ-↑-wk zero    γ = refl
⋯ᵏ-↑-wk (suc k) γ {ρ} = sym (𝐂.⋯-↑-wk (wk^ k γ) (ρ 𝐂.↑* k)) ■ cong 𝐂.wk (⋯ᵏ-↑-wk k γ)

dropᵏ : (k : ℕ) → Subset (k + n) → Subset n
dropᵏ zero    Z = Z
dropᵏ (suc k) Z = dropᵏ k (Vec.tail Z)

wk^↓ : (k : ℕ) (γ : Struct m) (Z : Subset (k + m)) → wk^ k γ ↓ Z ≡ wk^ k (γ ↓ dropᵏ k Z)
wk^↓ zero    γ Z = refl
wk^↓ (suc k) γ Z = wk↓' (wk^ k γ) Z ■ cong 𝐂.wk (wk^↓ k γ (Vec.tail Z))

dropᵏ-∁ : (k : ℕ) (Z : Subset (k + n)) → dropᵏ k (∁ Z) ≡ ∁ (dropᵏ k Z)
dropᵏ-∁ zero    Z = refl
dropᵏ-∁ (suc k) Z = cong (dropᵏ k) (tail-∁ Z) ■ dropᵏ-∁ k (Vec.tail Z)

fsuc^ : (k : ℕ) → 𝔽 n → 𝔽 (k + n)
fsuc^ zero    y = y
fsuc^ (suc k) y = fsuc (fsuc^ k y)

∈dropᵏ : (k : ℕ) {y : 𝔽 n} {Z : Subset (k + n)} → y ∈ dropᵏ k Z → fsuc^ k y ∈ Z
∈dropᵏ zero    p = p
∈dropᵏ (suc k) p = ∈tail (∈dropᵏ k p)

↑*-preimage : (k : ℕ) {ρ : m →ᵣ n} {z : 𝔽 (k + m)} {y : 𝔽 n} →
  (ρ 𝐂.↑* k) z ≡ fsuc^ k y → InImage ρ y
↑*-preimage zero    eq = _ , eq
↑*-preimage (suc k) {z = fzero}   ()
↑*-preimage (suc k) {z = fsuc z′} eq = ↑*-preimage k (suc-injective eq)

freshᵏ : (n k : ℕ) → Subset (k + n)
freshᵏ n zero    = ⁅⁆
freshᵏ n (suc k) = inside ∷ freshᵏ n k

fsuc^∉fresh : (k : ℕ) {y : 𝔽 n} → fsuc^ k y ∉ freshᵏ n k
fsuc^∉fresh zero            = ∉⊥
fsuc^∉fresh (suc k) (Vec.there p) = fsuc^∉fresh k p

dropᵏ⊆ : (k : ℕ) {A B : Subset (k + n)} → A ⊆ B → dropᵏ k A ⊆ dropᵏ k B
dropᵏ⊆ zero    A⊆B = A⊆B
dropᵏ⊆ (suc k) A⊆B = dropᵏ⊆ k (tail⊆ A⊆B)

un-wk^-Unr : (k : ℕ) (Δ : Ctx k) {Γ : Ctx n} {δ : Struct n} →
  AllCx Unr (Δ ⸴* Γ) (wk^ k δ) → AllCx Unr Γ δ
un-wk^-Unr zero    Δ a = a
un-wk^-Unr (suc k) Δ {Γ} a =
  un-wk^-Unr k (Δ ∘ suc) (un-wk-Unr (allCx-≗ (λ y → sym (⸴-⸴*-cons {Γ₁ = Δ} {Γ₂ = Γ} y)) a))

↑*ᵣ-preserves-⇐ : ∀ {ℓ} {P : Pred 𝕋 ℓ} (k : ℕ) (Δ : Ctx k) {ρ : m →ᵣ n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ρ 𝐂.Preserves[ P ] Γ₁ ⇐ Γ₂ → (ρ 𝐂.↑* k) 𝐂.Preserves[ P ] (Δ ⸴* Γ₁) ⇐ (Δ ⸴* Γ₂)
↑*ᵣ-preserves-⇐ zero    Δ pre = pre
↑*ᵣ-preserves-⇐ {P = P} (suc k) Δ {ρ} {Γ₁} {Γ₂} pre {x} au =
  subst P (⸴-⸴*-cons {Γ₁ = Δ} {Γ₂ = Γ₁} x)
    (↑ᵣ-preserves-⇐ (↑*ᵣ-preserves-⇐ k (Δ ∘ suc) pre) {x}
      (allCx-≗ (λ y → sym (⸴-⸴*-cons {Γ₁ = Δ} {Γ₂ = Γ₂} y)) au))

descend-absK : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {ρ : m →ᵣ n}
  (k : ℕ) (Δ : Ctx k) →
  𝐂.Inj ρ → ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ → ρ 𝐂.Preserves[ Mobile ] Γ₁ ⇐ Γ₂ →
  (dd : AD) (Fr : Struct (k + m)) (Fr′ : Struct (k + n))
  (A : Struct (k + m)) (γa : Struct n) →
  Fr 𝐂.⋯ (ρ 𝐂.↑* k) ≡ Fr′ →
  dom Fr′ ⊆ freshᵏ n k →
  (Δ ⸴* Γ₂) ∶ (A 𝐂.⋯ (ρ 𝐂.↑* k)) ≼ join dd Fr′ (wk^ k γa) →
  ∃[ γr ] ((Δ ⸴* Γ₁) ∶ A ≼ join dd Fr (wk^ k γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-absK {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ} k Δ inj-ρ pre preM dd Fr Fr′ A γa Frinv Frdom ≼b
  = γr , part1 , part2
  where
  Xtrue : Subset (k + n)
  Xtrue = dom (A 𝐂.⋯ (ρ 𝐂.↑* k))
  Xd0 : Subset (k + n)
  Xd0 = Xtrue ∪ freshᵏ n k
  img : ∀ {y} → y ∈ dom (γa ↓ dropᵏ k Xd0) → InImage ρ y
  img {y} y∈ with x∈p∪q⁻ Xtrue (freshᵏ n k) (∈dropᵏ k (↓-dom γa (dropᵏ k Xd0) y∈))
  ... | inj₁ sy∈   = ↑*-preimage k (proj₂ (dom-⋯-InImage A sy∈))
  ... | inj₂ sy∈fr = contradiction sy∈fr (fsuc^∉fresh k)
  pim = preimage {ϕ = ρ} (γa ↓ dropᵏ k Xd0) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ dropᵏ k Xd0
  eqr = proj₂ pim
  Fr-eq : Fr′ ↓ Xd0 ≡ Fr′
  Fr-eq = ↓-identity-⊆ Fr′ (⊆-trans Frdom (q⊆p∪q Xtrue (freshᵏ n k)))
  rhs-img : (join dd Fr (wk^ k γr)) 𝐂.⋯ (ρ 𝐂.↑* k) ≡ join dd Fr′ (wk^ k (γr 𝐂.⋯ ρ))
  rhs-img = join-⋯ dd {ϕ = ρ 𝐂.↑* k} Fr (wk^ k γr) ■ cong₂ (join dd) Frinv (⋯ᵏ-↑-wk k γr)
  rhs-eq : (join dd Fr′ (wk^ k γa)) ↓ Xd0 ≡ (join dd Fr (wk^ k γr)) 𝐂.⋯ (ρ 𝐂.↑* k)
  rhs-eq = ↓-join dd Fr′ (wk^ k γa) Xd0
           ■ (cong₂ (join dd) Fr-eq (wk^↓ k γa Xd0 ■ cong (wk^ k) (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ 𝐂.↑* k)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ 𝐂.↑* k)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ 𝐂.↑* k)) (p⊆p∪q (freshᵏ n k))
  part1 : (Δ ⸴* Γ₁) ∶ A ≼ join dd Fr (wk^ k γr)
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd Fr (wk^ k γr)} {ϕ = ρ 𝐂.↑* k}
            (Inj-↑* k inj-ρ) (λ {x} → ↑*ᵣ-preserves-⇐ k Δ pre {x})
            (λ {x} → ↑*ᵣ-preserves-⇐ k Δ preM {x})
            (subst₂ ((Δ ⸴* Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk^-eq : (wk^ k γa) ↓ ∁ Xtrue ≡ wk^ k (γa ↓ ∁ (dropᵏ k Xtrue))
  wk^-eq = wk^↓ k γa (∁ Xtrue) ■ cong (λ z → wk^ k (γa ↓ z)) (dropᵏ-∁ k Xtrue)
  unr-true : AllCx Unr Γ₂ (γa ↓ ∁ (dropᵏ k Xtrue))
  unr-true = un-wk^-Unr k Δ (subst (AllCx Unr (Δ ⸴* Γ₂)) wk^-eq
               (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b)))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (dropᵏ k Xd0))
  unr-part = ↓-⊆ γa (∁⊆ (dropᵏ⊆ k (p⊆p∪q {p = Xtrue} (freshᵏ n k)))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

rlift : (k : ℕ) → (m →ᵣ n) → (k + m →ᵣ k + n)
rlift k ρ = ρ 𝐂.↑* k

open import Data.Fin using (_↑ˡ_)
open import Data.Vec.Base using () renaming (here to vhere; there to vthere)

↑ˡ-fz : ∀ {k} n → (fzero {k}) ↑ˡ n ≡ fzero {k + n}
↑ˡ-fz n = refl

↑ˡ∈fresh : (k n : ℕ) (x : 𝔽 k) → (x ↑ˡ n) ∈ freshᵏ n k
↑ˡ∈fresh (suc k) n fzero    rewrite ↑ˡ-fz {suc k} n = vhere
↑ˡ∈fresh (suc k) n (fsuc x) = vthere (↑ˡ∈fresh k n x)

dom-⋯wkʳ⊆fresh : ∀ {k} (X : Struct k) {n} → dom (X 𝐂.⋯ᵣ 𝐂.wkʳ n) ⊆ freshᵏ n k
dom-⋯wkʳ⊆fresh X {n} {y} y∈ with dom-⋯-InImage X {ϕ = 𝐂.wkʳ n} y∈
... | x , eq = subst (_∈ freshᵏ n _) eq (↑ˡ∈fresh _ n x)
