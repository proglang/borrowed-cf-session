module BorrowedCF.Simulation.Backward.ChoiceSepNoBrn where

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
-- NoBrn : a session containing no `brn` atom anywhere.  Twin of NoMsg
-- (ComSepNoMsg), but the forbidden leaf is `brn`, so `acq`, the msg leaf
-- and the unification-variable leaf `` α are ALLOWED and there is NO `brn`
-- case.
------------------------------------------------------------------------

data NoBrn {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoBrn (` x)
  end  : NoBrn (end {n} p)
  ret  : NoBrn (ret {n})
  acq  : NoBrn (acq {n})
  skip : NoBrn (skip {n})
  ``-  : ∀ {α} → NoBrn (``_ {n} α)
  msg  : NoBrn (msg {n} p T)
  mu   : NoBrn s → NoBrn (mu s)
  _;_  : NoBrn s₁ → NoBrn s₂ → NoBrn (s₁ ; s₂)

noBrn-brn-⊥ : ∀ {p s₁ s₂} → ¬ NoBrn (brn {n} p s₁ s₂)
noBrn-brn-⊥ ()

noBrn-;-fst : NoBrn (s₁ ; s₂) → NoBrn s₁
noBrn-;-fst (x ; _) = x

noBrn-;-snd : NoBrn (s₁ ; s₂) → NoBrn s₂
noBrn-;-snd (_ ; y) = y

noBrn-acq : NoBrn (acq {n})
noBrn-acq = acq

noBrn-⋯ᵣ : NoBrn s → {ρ : m →ᵣ n} → NoBrn (s ⋯ ρ)
noBrn-⋯ᵣ `-          = `-
noBrn-⋯ᵣ end         = end
noBrn-⋯ᵣ ret         = ret
noBrn-⋯ᵣ acq         = acq
noBrn-⋯ᵣ skip        = skip
noBrn-⋯ᵣ ``-         = ``-
noBrn-⋯ᵣ msg         = msg
noBrn-⋯ᵣ (mu x)      = mu (noBrn-⋯ᵣ x)
noBrn-⋯ᵣ (x ; y)     = noBrn-⋯ᵣ x ; noBrn-⋯ᵣ y

noBrn-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoBrn s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoBrn (`/id (ϕ x))) → NoBrn (s ⋯ ϕ)
noBrn-⋯ `- ∀ϕ = ∀ϕ _
noBrn-⋯ end ∀ϕ = end
noBrn-⋯ ret ∀ϕ = ret
noBrn-⋯ acq ∀ϕ = acq
noBrn-⋯ skip ∀ϕ = skip
noBrn-⋯ ``- ∀ϕ = ``-
noBrn-⋯ msg ∀ϕ = msg
noBrn-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noBrn-⋯ x λ where
  zero    → subst NoBrn (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoBrn (wk-`/id _) (noBrn-⋯ᵣ (∀ϕ z))
noBrn-⋯ (x ; y) ∀ϕ = noBrn-⋯ x ∀ϕ ; noBrn-⋯ y ∀ϕ

noBrn-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoBrn (s ⋯ ϕ) → NoBrn s
noBrn-⋯⁻¹ {s = ` _} x = `-
noBrn-⋯⁻¹ {s = msg p t} x = msg
noBrn-⋯⁻¹ {s = end p} x = end
noBrn-⋯⁻¹ {s = ret} x = ret
noBrn-⋯⁻¹ {s = acq} x = acq
noBrn-⋯⁻¹ {s = skip} x = skip
noBrn-⋯⁻¹ {s = ``_ α} x = ``-
noBrn-⋯⁻¹ {s = brn p _ _} x = ⊥-elim (noBrn-brn-⊥ x)
noBrn-⋯⁻¹ {s = mu s} (mu x) = mu (noBrn-⋯⁻¹ x)
noBrn-⋯⁻¹ {s = _ ; _} (x ; y) = noBrn-⋯⁻¹ x ; noBrn-⋯⁻¹ y

noBrn-≃ : NoBrn {n} Respects _≃_
noBrn-≃ refl na = na
noBrn-≃ (x ◅ xs) na = noBrn-≃ xs (go x na)
  where
  go : NoBrn {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noBrn-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (() ; y)
  go (fwd (≃𝕊-msg eq))  msg = msg
  go (fwd (≃𝕊-brn₁ eq)) ()
  go (fwd (≃𝕊-brn₂ eq)) ()
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noBrn-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) ()
  go (bwd (≃𝕊-msg eq))  msg = msg
  go (bwd (≃𝕊-brn₁ eq)) ()
  go (bwd (≃𝕊-brn₂ eq)) ()

------------------------------------------------------------------------
-- Per-channel: every channel session in a BindCtx of a brn-free `s` is
-- itself brn-free.  Twin of bindCtx′-lookup-NoMsg.
------------------------------------------------------------------------

bindCtx′-lookup-NoBrn : ∀ {w} {Γ : Ctx w} {s} → BindCtx′ s Γ → NoBrn s
                      → (i : 𝔽 w) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoBrn s′)
bindCtx′-lookup-NoBrn (cons s₁ s₂ ¬sk s≃ b) NBs 0F =
  s₁ , refl , noBrn-;-fst (noBrn-≃ (≃-sym s≃) NBs)
bindCtx′-lookup-NoBrn (cons s₁ s₂ ¬sk s≃ b) NBs (suc i) =
  bindCtx′-lookup-NoBrn b (noBrn-;-snd (noBrn-≃ (≃-sym s≃) NBs)) i

bindCtx-lookup-NoBrn : ∀ {BG} {Γ : Ctx (sum BG)} {s} → BindCtx s BG Γ → NoBrn s
                     → (i : 𝔽 (sum BG)) → ∃[ s′ ] ((Γ ﹫ i ≡ ⟨ s′ ⟩) × NoBrn s′)
bindCtx-lookup-NoBrn (last x) NBs i = bindCtx′-lookup-NoBrn x NBs i
bindCtx-lookup-NoBrn {BG = n ∷ B} (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ x C) NBs i
  with Fin.splitAt n i in eq
... | inj₁ j =
  let s′ , ej , NB = bindCtx′-lookup-NoBrn x (noBrn-;-fst (noBrn-≃ (≃-sym s≃) NBs) ; ret) j
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ej) , NB
... | inj₂ k =
  let s′ , ek , NB = bindCtx-lookup-NoBrn C (acq ; noBrn-;-snd (noBrn-≃ (≃-sym s≃) NBs)) k
  in s′ , (lookup-splitAt n Γ₁ Γ₂ i ■ cong [ lookup Γ₁ , lookup Γ₂ ]′ eq ■ ek) , NB
bindCtx-lookup-NoBrn (cons-acq C) NBs i =
  bindCtx-lookup-NoBrn C (acq ; NBs) i

⟨⟩-inj : {s₁ s₂ : 𝕊 0} → _≡_ {A = 𝕋} ⟨ s₁ ⟩ ⟨ s₂ ⟩ → s₁ ≡ s₂
⟨⟩-inj refl = refl

bindCtx-NoBrn : ∀ {s BG} {Γ : Ctx (sum BG)} → (C : BindCtx s BG Γ) → NoBrn s
              → (i : 𝔽 (sum BG)) → NoBrn (proj₁ (chanCx-lookup (bindCtx⇒chanCtx C) i))
bindCtx-NoBrn C NBs i
  with bindCtx-lookup-NoBrn C NBs i | chanCx-lookup (bindCtx⇒chanCtx C) i
... | s′ , e1 , NB | s″ , e2 = subst NoBrn (⟨⟩-inj (sym e1 ■ e2)) NB

bindCtx-noBrn-not-brn : ∀ {s BG} {Γ : Ctx (sum BG)} {i} {p sa sb} → BindCtx s BG Γ → NoBrn s
                      → (Γ ﹫ i) ≃ ⟨ brn p sa sb ⟩ → ⊥
bindCtx-noBrn-not-brn {i = i} C NBs eqb
  with bindCtx-lookup-NoBrn C NBs i
... | s′ , e1 , NB =
  noBrn-brn-⊥ (noBrn-≃ (≃-⟨⟩⁻¹ (subst (_≃ _) e1 eqb)) NB)
