-- | Unification-variable scope for algorithmic derivations (agent C2).
--
--   The algorithmic judgment threads a fresh-variable counter m (on entry) to n (on
--   exit).  `scope` says what that counter buys: the synthesised type and the
--   emitted constraints only mention unification variables that were allocated in
--   the window [k, n), so the substitutions of two sibling premises can be merged
--   (see `Scope.Merge`).
--
--   Two rules GUESS a type that the derivation does not determine: A-Const (the
--   type of `send`/`recv`/`acq`/`select`/`branch` is an arbitrary instance of the
--   constant's schema) and A-Ann (the annotation).  `GuessIn k d` collects exactly
--   these obligations; for a derivation built from a solved declarative derivation
--   every one of them is discharged by `solved⇒uvarsIn`.
module BorrowedCF.Completeness.Scope where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base using (SolvedCtx)

open import BorrowedCF.Completeness.Scope.Base public
open import BorrowedCF.Completeness.Scope.Merge public

open Nat.Variables

private variable
  N : ℕ
  ξ : Mode

------------------------------------------------------------------------
-- Inversions of UVarsIn (used to avoid `with` in scope)

uvarsIn-→₁ : UVarsIn m n (T ⟨ a ⟩→ U) → UVarsIn m n T
uvarsIn-→₁ (u ⟨ a ⟩→ v) = u

uvarsIn-→₂ : UVarsIn m n (T ⟨ a ⟩→ U) → UVarsIn m n U
uvarsIn-→₂ (u ⟨ a ⟩→ v) = v

uvarsIn-⊗₁ : UVarsIn m n (T ⊗⟨ d ⟩ U) → UVarsIn m n T
uvarsIn-⊗₁ (u ⊗⟨ d ⟩ v) = u

uvarsIn-⊗₂ : UVarsIn m n (T ⊗⟨ d ⟩ U) → UVarsIn m n U
uvarsIn-⊗₂ (u ⊗⟨ d ⟩ v) = v

uvarsIn-⊕₁ : UVarsIn m n (T ⊕ U) → UVarsIn m n T
uvarsIn-⊕₁ (u ⊕ v) = u

uvarsIn-⊕₂ : UVarsIn m n (T ⊕ U) → UVarsIn m n U
uvarsIn-⊕₂ (u ⊕ v) = v

------------------------------------------------------------------------
-- Contexts

-- A record, again so that Agda can invert it (a function type would leave the
-- context an unsolved meta at every use).
record UVarsInΓ (lo hi : ℕ) {N : ℕ} (Γ : Ctx N) : Set where
  constructor ctx
  field lookupΓ : ∀ (x : 𝔽 N) → UVarsIn lo hi (Γ ﹫ x)

open UVarsInΓ public

uvarsInΓ-mono : {Γ : Ctx N} → m′ Nat.≤ m → n Nat.≤ n′ → UVarsInΓ m n Γ → UVarsInΓ m′ n′ Γ
uvarsInΓ-mono lo hi uΓ = ctx λ x → uvarsIn-mono lo hi (lookupΓ uΓ x)

uvarsInΓ-⸴ : {Γ : Ctx N} → UVarsIn m n T → UVarsInΓ m n Γ → UVarsInΓ m n (T ⸴ Γ)
uvarsInΓ-⸴ uT uΓ = ctx λ where
  zero → uT
  (suc x) → lookupΓ uΓ x

solvedCtx⇒uvarsInΓ : {Γ : Ctx N} → SolvedCtx Γ → UVarsInΓ m n Γ
solvedCtx⇒uvarsInΓ SΓ = ctx λ x → solved⇒uvarsIn (SΓ x)

uvarsInΔ-allMobile : (Γ : Ctx N) (γ : Struct N) → UVarsInΓ m n Γ →
  UVarsInΔ m n (allMobile Γ γ)
uvarsInΔ-allMobile Γ (` x) uΓ = C-Mob (lookupΓ uΓ x) ∷ []
uvarsInΔ-allMobile Γ [] uΓ = []
uvarsInΔ-allMobile Γ (γ₁ ∥ γ₂) uΓ =
  uvarsInΔ-++ (uvarsInΔ-allMobile Γ γ₁ uΓ) (uvarsInΔ-allMobile Γ γ₂ uΓ)
uvarsInΔ-allMobile Γ (γ₁ ; γ₂) uΓ =
  uvarsInΔ-++ (uvarsInΔ-allMobile Γ γ₁ uΓ) (uvarsInΔ-allMobile Γ γ₂ uΓ)

uvarsInΔ-mobConstraints : (𝓂 : Mob) (Γ : Ctx N) (γ : Struct N) → UVarsInΓ m n Γ →
  UVarsInΔ m n (mobConstraints 𝓂 Γ γ)
uvarsInΔ-mobConstraints M Γ γ uΓ = uvarsInΔ-allMobile Γ γ uΓ
uvarsInΔ-mobConstraints S Γ γ uΓ = []

-- The structural premises `Γ ∶ γ₁ ≼ γ₂ ↑ Δ₀` of the A-rules emit exactly the
-- mobility constraints `C-Mob (Γ ﹫ x)` of `∥′-tmˡ↑` / `∥′-tmʳ↑`, so their scope is
-- the scope of the context.
uvarsInΔ-≈′↑ : {Γ : Ctx N} {γ₁ γ₂ : Struct N} → UVarsInΓ m n Γ →
  Γ ∶ γ₁ ≈′ γ₂ ↑ Δ → UVarsInΔ m n Δ
uvarsInΔ-≈′↑ uΓ sq′-assoc↑ = []
uvarsInΔ-≈′↑ uΓ (sq′-cong₁↑ d) = uvarsInΔ-≈′↑ uΓ d
uvarsInΔ-≈′↑ uΓ (sq′-cong₂↑ d) = uvarsInΔ-≈′↑ uΓ d
uvarsInΔ-≈′↑ uΓ ∥′-unit↑ = []
uvarsInΔ-≈′↑ uΓ ∥′-assoc↑ = []
uvarsInΔ-≈′↑ uΓ ∥′-comm↑ = []
uvarsInΔ-≈′↑ uΓ (∥′-cong₁↑ d) = uvarsInΔ-≈′↑ uΓ d
uvarsInΔ-≈′↑ uΓ (∥′-dup↑ U) = []
uvarsInΔ-≈′↑ {Γ = Γ} uΓ (∥′-tmˡ↑ {α = α}) = uvarsInΔ-allMobile Γ α uΓ
uvarsInΔ-≈′↑ {Γ = Γ} uΓ (∥′-tmʳ↑ {β = β}) = uvarsInΔ-allMobile Γ β uΓ

uvarsInΔ-≈↑ : {Γ : Ctx N} {γ₁ γ₂ : Struct N} → UVarsInΓ m n Γ →
  Γ ∶ γ₁ ≈ γ₂ ↑ Δ → UVarsInΔ m n Δ
uvarsInΔ-≈↑ uΓ ε↑ = []
uvarsInΔ-≈↑ uΓ (d ◅ᶠ ds) = uvarsInΔ-++ (uvarsInΔ-≈′↑ uΓ d) (uvarsInΔ-≈↑ uΓ ds)
uvarsInΔ-≈↑ uΓ (d ◅ᵇ ds) = uvarsInΔ-++ (uvarsInΔ-≈′↑ uΓ d) (uvarsInΔ-≈↑ uΓ ds)

uvarsInΔ-≼↑ : {Γ : Ctx N} {γ₁ γ₂ : Struct N} → UVarsInΓ m n Γ →
  Γ ∶ γ₁ ≼ γ₂ ↑ Δ → UVarsInΔ m n Δ
uvarsInΔ-≼↑ uΓ (≼-refl↑ d) = uvarsInΔ-≈↑ uΓ d
uvarsInΔ-≼↑ uΓ (≼-∅↑ U) = []
uvarsInΔ-≼↑ uΓ ≼-wk↑ = []
uvarsInΔ-≼↑ uΓ (≼-trans↑ d e) = uvarsInΔ-++ (uvarsInΔ-≼↑ uΓ d) (uvarsInΔ-≼↑ uΓ e)
uvarsInΔ-≼↑ uΓ (≼-cong-sq↑ d e) = uvarsInΔ-++ (uvarsInΔ-≼↑ uΓ d) (uvarsInΔ-≼↑ uΓ e)
uvarsInΔ-≼↑ uΓ (≼-cong-par↑ d e) = uvarsInΔ-++ (uvarsInΔ-≼↑ uΓ d) (uvarsInΔ-≼↑ uΓ e)

------------------------------------------------------------------------
-- Guessed types

-- The scope obligation on the two rules whose type is not determined by the
-- premises.  Everything else is a conjunction over the sub-derivations.
GuessIn : {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {m n : ℕ}
  (k : ℕ) → Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n → Set
GuessIn k (A-Var ≤γ) = ⊤
GuessIn {T = T} {m = m} k (A-Const ≤γ Ac ⊢c) = UVarsIn k m T
GuessIn {m = m} k (A-LSplit {s = s} ≤γ ¬sk) = UVarsIn k m s
GuessIn {m = m} k (A-RSplit {s = s} ≤γ ¬sk) = UVarsIn k m s
GuessIn k (A-App ec ≤γ d₁ d₂) = GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-Seq unrT ≤γ d₁ d₂) = GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-LetPair p/s ≤γ d₁ d₂) = GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-Let p/s ≤γ d₁ d₂) = GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-Case p/s ≤γ d d₁ d₂) = GuessIn k d × GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-Abs unrΓ ϵ≤ d eq) = GuessIn k d
GuessIn k (A-AbsRec unrΓ ωa ϵ≤ d) = GuessIn k d
GuessIn k (A-Pair p/s ≤γ sp d₁ d₂) = GuessIn k d₁ × GuessIn k d₂
GuessIn k (A-Inj d) = GuessIn k d
GuessIn k (A-Check d) = GuessIn k d
GuessIn {T = T} {m = m} k (A-Ann cf d) = UVarsIn k m T × GuessIn k d

-- What the mode contributes on the way in: in checking mode the type is an INPUT,
-- and A-Check turns it into the constraint `C-Eq T U`, so its variables must be in
-- scope already; in inference mode there is nothing to assume.
ScopeIn : Mode → ℕ → ℕ → 𝕋 → Set
ScopeIn inf k m T = ⊤
ScopeIn chk k m T = UVarsIn k m T

------------------------------------------------------------------------
-- The scope theorem

scope-gen : {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {k m n : ℕ}
  (d : Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n) →
  GuessIn k d → UVarsInΓ k m Γ → k Nat.≤ m → ScopeIn ξ k m T →
  m Nat.≤ n × UVarsIn k n T × UVarsInΔ k n Δ
scope-gen (A-Var {x = x} ≤γ) g uΓ k≤m sI =
  Nat.≤-refl , lookupΓ uΓ x , uvarsInΔ-≼↑ uΓ ≤γ
scope-gen (A-Const ≤γ Ac ⊢c) g uΓ k≤m sI = Nat.≤-refl , g , uvarsInΔ-≼↑ uΓ ≤γ
scope-gen {k = k} {m = m} (A-LSplit ≤γ ¬sk) g uΓ k≤m sI =
  let m≤1+m = Nat.n≤1+n m
      us = uvarsIn-mono Nat.≤-refl m≤1+m g
      uα = ``_ {α = UV.fresh m} (k≤m , Nat.≤-refl)
  in m≤1+m
   , (⟨ us ; uα ⟩ ⟨ _ ⟩→ (⟨ us ⟩ ⊗⟨ L ⟩ ⟨ uα ⟩))
   , uvarsInΔ-mono Nat.≤-refl m≤1+m (uvarsInΔ-≼↑ uΓ ≤γ)
scope-gen {k = k} {m = m} (A-RSplit ≤γ ¬sk) g uΓ k≤m sI =
  let m≤1+m = Nat.n≤1+n m
      us = uvarsIn-mono Nat.≤-refl m≤1+m g
      uα = ``_ {α = UV.fresh m} (k≤m , Nat.≤-refl)
  in m≤1+m
   , (⟨ us ; uα ⟩ ⟨ _ ⟩→ (⟨ us ; ret ⟩ ⊗⟨ 𝟙 ⟩ ⟨ acq ; uα ⟩))
   , uvarsInΔ-mono Nat.≤-refl m≤1+m (uvarsInΔ-≼↑ uΓ ≤γ)
scope-gen (A-App ec ≤γ d₁ d₂) (g₁ , g₂) uΓ k≤m sI =
  let m≤m′ , uTU , uΔ₁ = scope-gen d₁ g₁ uΓ k≤m tt
      m′≤n , _ , uΔ₂ = scope-gen d₂ g₂ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ)
                         (Nat.≤-trans k≤m m≤m′) (uvarsIn-→₁ uTU)
      m≤n = Nat.≤-trans m≤m′ m′≤n
  in m≤n
   , uvarsIn-mono Nat.≤-refl m′≤n (uvarsIn-→₂ uTU)
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤n uΔ₁) uΔ₂)
scope-gen (A-Seq unrT ≤γ d₁ d₂) (g₁ , g₂) uΓ k≤m sI =
  let m≤m′ , _ , uΔ₁ = scope-gen d₁ g₁ uΓ k≤m tt
      m′≤n , uU , uΔ₂ = scope-gen d₂ g₂ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ)
                          (Nat.≤-trans k≤m m≤m′) tt
      m≤n = Nat.≤-trans m≤m′ m′≤n
  in m≤n , uU
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤n uΔ₁) uΔ₂)
scope-gen (A-LetPair p/s ≤γ d₁ d₂) (g₁ , g₂) uΓ k≤m sI =
  let m≤m′ , uT₁₂ , uΔ₁ = scope-gen d₁ g₁ uΓ k≤m tt
      uΓ′ = uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ
      m′≤n , uU , uΔ₂ = scope-gen d₂ g₂
                          (uvarsInΓ-⸴ (uvarsIn-⊗₁ uT₁₂) (uvarsInΓ-⸴ (uvarsIn-⊗₂ uT₁₂) uΓ′))
                          (Nat.≤-trans k≤m m≤m′) tt
      m≤n = Nat.≤-trans m≤m′ m′≤n
  in m≤n , uU
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤n uΔ₁) uΔ₂)
scope-gen (A-Let p/s ≤γ d₁ d₂) (g₁ , g₂) uΓ k≤m sI =
  let m≤m′ , uT , uΔ₁ = scope-gen d₁ g₁ uΓ k≤m tt
      uΓ′ = uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ
      m′≤n , uU , uΔ₂ = scope-gen d₂ g₂ (uvarsInΓ-⸴ uT uΓ′) (Nat.≤-trans k≤m m≤m′) tt
      m≤n = Nat.≤-trans m≤m′ m′≤n
  in m≤n , uU
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤n uΔ₁) uΔ₂)
scope-gen (A-Case p/s ≤γ d d₁ d₂) (g , g₁ , g₂) uΓ k≤m sI =
  let m≤m₁ , uT , uΔ = scope-gen d g uΓ k≤m tt
      m₁≤m₂ , uU₁ , uΔ₁ = scope-gen d₁ g₁
                            (uvarsInΓ-⸴ (uvarsIn-⊕₁ uT) (uvarsInΓ-mono Nat.≤-refl m≤m₁ uΓ))
                            (Nat.≤-trans k≤m m≤m₁) tt
      m≤m₂ = Nat.≤-trans m≤m₁ m₁≤m₂
      m₂≤n , uU₂ , uΔ₂ = scope-gen d₂ g₂
                            (uvarsInΓ-⸴ (uvarsIn-mono Nat.≤-refl m₁≤m₂ (uvarsIn-⊕₂ uT))
                                        (uvarsInΓ-mono Nat.≤-refl m≤m₂ uΓ))
                            (Nat.≤-trans k≤m m≤m₂) tt
      m₁≤n = Nat.≤-trans m₁≤m₂ m₂≤n
      m≤n = Nat.≤-trans m≤m₁ m₁≤n
  in m≤n
   , uvarsIn-mono Nat.≤-refl m₂≤n uU₁
   , C-Eq (uvarsIn-mono Nat.≤-refl m₂≤n uU₁) uU₂
     ∷ uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
         (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m₁≤n uΔ)
           (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m₂≤n uΔ₁) uΔ₂))
scope-gen {Γ = Γ} {γ = γ} (A-Abs {a = a} unrΓ ϵ≤ d refl) g uΓ k≤m sI =
  let m≤n , uU , uΔ = scope-gen d g (uvarsInΓ-⸴ (uvarsIn-→₁ sI) uΓ) k≤m (uvarsIn-→₂ sI)
  in m≤n
   , uvarsIn-mono Nat.≤-refl m≤n sI
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-mobConstraints (Arr.mob a) Γ γ uΓ)) uΔ
scope-gen (A-AbsRec unrΓ ωa ϵ≤ d) g uΓ k≤m sI =
  let m≤n , uU , uΔ = scope-gen d g (uvarsInΓ-⸴ (uvarsIn-→₁ sI) (uvarsInΓ-⸴ sI uΓ)) k≤m
                        (uvarsIn-→₂ sI)
  in m≤n , uvarsIn-mono Nat.≤-refl m≤n sI , uΔ
scope-gen (A-Pair p/s ≤γ sp d₁ d₂) (g₁ , g₂) uΓ k≤m sI =
  let m≤m′ , _ , uΔ₁ = scope-gen d₁ g₁ uΓ k≤m (uvarsIn-⊗₁ sI)
      m′≤n , _ , uΔ₂ = scope-gen d₂ g₂ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ)
                         (Nat.≤-trans k≤m m≤m′)
                         (uvarsIn-mono Nat.≤-refl m≤m′ (uvarsIn-⊗₂ sI))
      m≤n = Nat.≤-trans m≤m′ m′≤n
  in m≤n
   , uvarsIn-mono Nat.≤-refl m≤n sI
   , uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m≤n (uvarsInΔ-≼↑ uΓ ≤γ))
       (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤n uΔ₁) uΔ₂)
scope-gen {k = k} {m = m} (A-Inj {i = i} d) g uΓ k≤m sI =
  let m≤n , _ , uΔ = scope-gen d g uΓ k≤m
                       (if[ UVarsIn k m ] i then uvarsIn-⊕₁ sI else uvarsIn-⊕₂ sI)
  in m≤n , uvarsIn-mono Nat.≤-refl m≤n sI , uΔ
scope-gen (A-Check d) g uΓ k≤m sI =
  let m≤n , uU , uΔ = scope-gen d g uΓ k≤m tt
      uT = uvarsIn-mono Nat.≤-refl m≤n sI
  in m≤n , uT , C-Eq uT uU ∷ uΔ
scope-gen (A-Ann cf d) (gT , g) uΓ k≤m sI = scope-gen d g uΓ k≤m gT

-- The theorem as used by the main proof: a solved context, the window starting at
-- the entry counter m.
scope : {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {m n : ℕ} →
  SolvedCtx Γ → (d : Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n) → GuessIn m d →
  ScopeIn ξ m m T →
  m Nat.≤ n × UVarsIn m n T × UVarsInΔ m n Δ
scope SΓ d g sI = scope-gen d g (solvedCtx⇒uvarsInΓ SΓ) Nat.≤-refl sI

scope⇒ : {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {m n : ℕ} →
  SolvedCtx Γ → (d : Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n) → GuessIn m d →
  m Nat.≤ n × UVarsIn m n T × UVarsInΔ m n Δ
scope⇒ SΓ d g = scope SΓ d g tt

scope⇐ : {Γ : Ctx N} {γ : Struct N} {e : Tm N} {T : 𝕋} {ϵ : Eff} {Δ : CSet} {m n : ℕ} →
  SolvedCtx Γ → SolvedTy T → (d : Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n) → GuessIn m d →
  m Nat.≤ n × UVarsInΔ m n Δ
scope⇐ SΓ ST d g =
  let m≤n , _ , uΔ = scope SΓ d g (solved⇒uvarsIn ST) in m≤n , uΔ

------------------------------------------------------------------------
-- Cheap facts about solved contexts and terms

subTy-ctx-id : {Γ : Ctx N} → SolvedCtx Γ → subCtx Γ σ ≡ Γ
subTy-ctx-id {Γ = []} SΓ = refl
subTy-ctx-id {Γ = T ⸴ Γ} SΓ = cong₂ _⸴_ (subTy-id (SΓ zero)) (subTy-ctx-id (SΓ ∘ suc))

solvedΓ-of : {Γ : Ctx N} → SolvedCtx Γ → SolvedΓ Γ σ
solvedΓ-of {σ = σ} SΓ x rewrite subTy-id (SΓ x) {σ} = SΓ x

-- The mobility constraints of A-Abs, discharged from the declarative MobCx of
-- T-Abs.  Every constraint is `C-Mob (Γ ﹫ x)` with Γ solved, so the substitution
-- plays no role (`subTy-id`).
mobCx⇒solvedΔ : {Γ : Ctx N} (γ : Struct N) → SolvedCtx Γ → MobCx Γ γ →
  SolvedΔ (allMobile Γ γ) σ
mobCx⇒solvedΔ {σ = σ} (` x) SΓ (` mx) = subst Mobile (sym (subTy-id (SΓ x) {σ})) mx ∷ []
mobCx⇒solvedΔ [] SΓ [] = []
mobCx⇒solvedΔ (γ₁ ∥ γ₂) SΓ (p ∥ q) =
  solvedΔ-++ (mobCx⇒solvedΔ γ₁ SΓ p) (mobCx⇒solvedΔ γ₂ SΓ q)
mobCx⇒solvedΔ (γ₁ ; γ₂) SΓ (p ; q) =
  solvedΔ-++ (mobCx⇒solvedΔ γ₁ SΓ p) (mobCx⇒solvedΔ γ₂ SΓ q)

mobConstraints-solved : {Γ : Ctx N} (𝓂 : Mob) (γ : Struct N) → SolvedCtx Γ →
  (𝓂 ≡ M → MobCx Γ γ) → SolvedΔ (mobConstraints 𝓂 Γ γ) σ
mobConstraints-solved M γ SΓ mob = mobCx⇒solvedΔ γ SΓ (mob refl)
mobConstraints-solved S γ SΓ mob = []

solvedTm-K : {c : Const} → SolvedTm {N} (K c) → SolvedC c
solvedTm-K (K sc) = sc

solvedC-lsplit : {s : 𝕊 0} → SolvedC (`lsplit s) → SolvedTy s
solvedC-lsplit (`lsplit ss) = ss

solvedC-rsplit : {s : 𝕊 0} → SolvedC (`rsplit s) → SolvedTy s
solvedC-rsplit (`rsplit ss) = ss

-- `subTm` and `subCtx` are the identity on a solved term/context, so the
-- declarative derivation transported by `⊢-sub` keeps its subject.
subTm-id-solved : {e : Tm N} → SolvedTm e → subTm e σ ≡ e
subTm-id-solved = subTm-id
