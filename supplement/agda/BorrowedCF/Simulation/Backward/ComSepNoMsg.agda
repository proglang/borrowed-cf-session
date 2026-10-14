module BorrowedCF.Simulation.Backward.ComSepNoMsg where

open import Data.Nat.ListAction using (sum)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec.Properties using (lookup-splitAt)

open import BorrowedCF.Prelude
open import BorrowedCF.Kits
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Context using (Ctx; _﹫_)
open import BorrowedCF.Reduction.Base using (ChanCx; chanCx-lookup)
open import BorrowedCF.Processes.Typed
  using (BindCtx; BindCtx′; nil; cons; last; cons-ret/acq; cons-acq
        ; bindCtx⇒chanCtx; bindCtx′⇒chanCtx)

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)

open Bin using (_Respects_)
open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- NoMsg : a session containing no `msg` atom anywhere.  Mirror of NoAcq
-- (CloseVacuityProbe), but the forbidden leaf is `msg`, so `acq` and the
-- unification-variable leaf `` α are ALLOWED and there is NO `msg` case.
------------------------------------------------------------------------

data NoMsg {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoMsg (` x)
  end  : NoMsg (end {n} p)
  ret  : NoMsg (ret {n})
  acq  : NoMsg (acq {n})
  skip : NoMsg (skip {n})
  ``-  : ∀ {α} → NoMsg (``_ {n} α)
  brn  : NoMsg s₁ → NoMsg s₂ → NoMsg (brn p s₁ s₂)
  mu   : NoMsg s → NoMsg (mu s)
  _;_  : NoMsg s₁ → NoMsg s₂ → NoMsg (s₁ ; s₂)

noMsg-msg-⊥ : ¬ NoMsg (msg {n} p T)
noMsg-msg-⊥ ()

noMsg-;-fst : NoMsg (s₁ ; s₂) → NoMsg s₁
noMsg-;-fst (x ; _) = x

noMsg-;-snd : NoMsg (s₁ ; s₂) → NoMsg s₂
noMsg-;-snd (_ ; y) = y

noMsg-acq : NoMsg (acq {n})
noMsg-acq = acq

noMsg-⋯ᵣ : NoMsg s → {ρ : m →ᵣ n} → NoMsg (s ⋯ ρ)
noMsg-⋯ᵣ `-          = `-
noMsg-⋯ᵣ end         = end
noMsg-⋯ᵣ ret         = ret
noMsg-⋯ᵣ acq         = acq
noMsg-⋯ᵣ skip        = skip
noMsg-⋯ᵣ ``-         = ``-
noMsg-⋯ᵣ (brn x y)   = brn (noMsg-⋯ᵣ x) (noMsg-⋯ᵣ y)
noMsg-⋯ᵣ (mu x)      = mu (noMsg-⋯ᵣ x)
noMsg-⋯ᵣ (x ; y)     = noMsg-⋯ᵣ x ; noMsg-⋯ᵣ y

noMsg-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoMsg s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoMsg (`/id (ϕ x))) → NoMsg (s ⋯ ϕ)
noMsg-⋯ `- ∀ϕ = ∀ϕ _
noMsg-⋯ end ∀ϕ = end
noMsg-⋯ ret ∀ϕ = ret
noMsg-⋯ acq ∀ϕ = acq
noMsg-⋯ skip ∀ϕ = skip
noMsg-⋯ ``- ∀ϕ = ``-
noMsg-⋯ (brn x y) ∀ϕ = brn (noMsg-⋯ x ∀ϕ) (noMsg-⋯ y ∀ϕ)
noMsg-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noMsg-⋯ x λ where
  zero    → subst NoMsg (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoMsg (wk-`/id _) (noMsg-⋯ᵣ (∀ϕ z))
noMsg-⋯ (x ; y) ∀ϕ = noMsg-⋯ x ∀ϕ ; noMsg-⋯ y ∀ϕ

noMsg-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoMsg (s ⋯ ϕ) → NoMsg s
noMsg-⋯⁻¹ {s = ` _} x = `-
noMsg-⋯⁻¹ {s = msg p t} x = ⊥-elim (noMsg-msg-⊥ x)
noMsg-⋯⁻¹ {s = end p} x = end
noMsg-⋯⁻¹ {s = ret} x = ret
noMsg-⋯⁻¹ {s = acq} x = acq
noMsg-⋯⁻¹ {s = skip} x = skip
noMsg-⋯⁻¹ {s = ``_ α} x = ``-
noMsg-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noMsg-⋯⁻¹ x) (noMsg-⋯⁻¹ y)
noMsg-⋯⁻¹ {s = mu s} (mu x) = mu (noMsg-⋯⁻¹ x)
noMsg-⋯⁻¹ {s = _ ; _} (x ; y) = noMsg-⋯⁻¹ x ; noMsg-⋯⁻¹ y

noMsg-≃ : NoMsg {n} Respects _≃_
noMsg-≃ refl na = na
noMsg-≃ (x ◅ xs) na = noMsg-≃ xs (go x na)
  where
  go : NoMsg {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noMsg-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (fwd (≃𝕊-msg eq))  ()
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noMsg-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y
  go (bwd (≃𝕊-msg eq))  ()
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)

------------------------------------------------------------------------
-- Per-channel: every channel session in a BindCtx of a msg-free `s` is
-- itself msg-free.  Mirrors bindCtx′-NoAcq / block-NoAcq (RevComConfine),
-- but produces a self-contained  (Γ ﹫ i ≡ ⟨ s′ ⟩)  witness so the
-- multi-block routing over  Γ₁ ⸴* Γ₂  goes through splitAt directly.
------------------------------------------------------------------------

bindCtx′-lookup-NoMsg : ∀ {w} {Γ : Ctx w} {s} → BindCtx′ s Γ → NoMsg s
                      → (i : 𝔽 w) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoMsg s′)
bindCtx′-lookup-NoMsg (cons s₁ s₂ ¬sk s≃ b) NMs 0F =
  s₁ , refl , noMsg-;-fst (noMsg-≃ (≃-sym s≃) NMs)
bindCtx′-lookup-NoMsg (cons s₁ s₂ ¬sk s≃ b) NMs (suc i) =
  bindCtx′-lookup-NoMsg b (noMsg-;-snd (noMsg-≃ (≃-sym s≃) NMs)) i

bindCtx-lookup-NoMsg : ∀ {BG} {Γ : Ctx (sum BG)} {s} → BindCtx s BG Γ → NoMsg s
                     → (i : 𝔽 (sum BG)) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoMsg s′)
bindCtx-lookup-NoMsg (last x) NMs i = bindCtx′-lookup-NoMsg x NMs i
bindCtx-lookup-NoMsg {BG = n ∷ B} (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ x C) NMs i
  with Fin.splitAt n i in eq
... | inj₁ j =
  let s′ , ej , NM = bindCtx′-lookup-NoMsg x (noMsg-;-fst (noMsg-≃ (≃-sym s≃) NMs) ; ret) j
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ej) , NM
... | inj₂ k =
  let s′ , ek , NM = bindCtx-lookup-NoMsg C (acq ; noMsg-;-snd (noMsg-≃ (≃-sym s≃) NMs)) k
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ek) , NM
bindCtx-lookup-NoMsg (cons-acq C) NMs i =
  bindCtx-lookup-NoMsg C (acq ; NMs) i

⟨⟩-inj : {s₁ s₂ : 𝕊 0} → _≡_ {A = 𝕋} ⟨ s₁ ⟩ ⟨ s₂ ⟩ → s₁ ≡ s₂
⟨⟩-inj refl = refl

bindCtx-NoMsg : ∀ {s BG} {Γ : Ctx (sum BG)} → (C : BindCtx s BG Γ) → NoMsg s
              → (i : 𝔽 (sum BG)) → NoMsg (proj₁ (chanCx-lookup (bindCtx⇒chanCtx C) i))
bindCtx-NoMsg C NMs i
  with bindCtx-lookup-NoMsg C NMs i | chanCx-lookup (bindCtx⇒chanCtx C) i
... | s′ , e1 , NM | s″ , e2 = subst NoMsg (⟨⟩-inj (sym e1 ■ e2)) NM

bindCtx-noMsg-not-msg : ∀ {s BG} {Γ : Ctx (sum BG)} {i} {T} → BindCtx s BG Γ → NoMsg s
                      → (Γ ﹫ i) ≃ ⟨ msg ‼ T ⟩ → ⊥
bindCtx-noMsg-not-msg {i = i} {T = T} C NMs eqm
  with bindCtx-lookup-NoMsg C NMs i
... | s′ , e1 , NM =
  noMsg-msg-⊥ (noMsg-≃ (≃-⟨⟩⁻¹ (subst (_≃ ⟨ msg ‼ T ⟩) e1 eqm)) NM)
