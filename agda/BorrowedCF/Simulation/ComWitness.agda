{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.ComWitness where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as RR
open import BorrowedCF.Simulation.InvFrame using (arg-type)

import BorrowedCF.Context.Substitution as C

open Fin.Patterns
open Nat.Variables

sesS : 𝕊 0
sesS = msg ‼ `⊤ ; skip

gS : Ctx 1
gS = ⟨ msg ‼ `⊤ ⟩ F.∷ F.[]

bcS : BindCtx {1} sesS gS
bcS = -∷ []

gR : Ctx 1
gR = ⟨ msg ⁇ `⊤ ⟩ F.∷ F.[]

bcR : BindCtx {1} (dual sesS) gR
bcR = -∷ []

gOut : Ctx 1
gOut = ⟨ msg ‼ ⟨ msg ‼ `⊤ ⟩ ⟩ F.∷ F.[]

bodyCtx : Ctx 3
bodyCtx = (gS F.++ gR) F.++ gOut

-- RECV thread: typechecks, since gR 0 = ⟨ msg ⁇ `⊤ ⟩ is a valid recv channel,
-- message type `⊤ is Mobile (TPred `⊤).
recvExpr : bodyCtx ; ([] ∥ (` 1F)) ⊢ K `recv · (` 1F) ∶ `⊤ ∣ 𝕀
recvExpr = T-AppLin refl
  (T-Conv ≃-refl ℙ≤ϵ (T-Const (`recv `⊤)))
  (T-Conv ≃-refl ℙ≤ϵ (T-Var 1F refl))

-- SEND thread: the message is 0F : gS 0 = ⟨ msg ‼ `⊤ ⟩.
-- `send demands  Mobile (gS 0) = Mobile ⟨ msg ‼ `⊤ ⟩ ; the ONLY hole.
sendExpr : Mobile ⟨ msg ‼ `⊤ ⟩ →
           bodyCtx ; ([] ∥ ((` 0F) ∥ (` 2F))) ⊢ K `send · ((` 0F) ⊗ (` 2F)) ∶ `⊤ ∣ 𝕀
sendExpr mob = T-AppLin refl
  (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send mob)))
  (T-Pair par (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)) (T-Conv ≃-refl ℙ≤ϵ (T-Var 2F refl)) par)

-- ════════════════════════════════════════════════════════════════════
-- The obstruction, machine-checked.
-- ════════════════════════════════════════════════════════════════════

msgT : 𝕊 0
msgT = msg ‼ `⊤

-- msg-led sessions are never Bounded.
¬bounded-msg : ¬ Bounded msgT
¬bounded-msg ()

-- The send message  0F : ⟨ msg ‼ `⊤ ⟩  can NOT be proven Mobile:
-- the Skips disjunct fails (msg is not a skip), and the  ≃ acq ; s′  disjunct
-- would make  msg ‼ `⊤  Bounded (via ≃-bounded), which it is not.
¬mobile-send-msg : ¬ Mobile ⟨ msgT ⟩
¬mobile-send-msg ⟨ inj₁ () ⟩
¬mobile-send-msg ⟨ inj₂ (s′ , bnd , eq) ⟩ =
  ¬bounded-msg (≃-bounded (≃-sym eq) (-;₂ bnd))

-- ════════════════════════════════════════════════════════════════════
-- Capstone: the send THREAD is untypable in any struct, with NO Mobile
-- premise handed in.  Inversion drives the typing down to the demand
-- Mobile (Γ 0F) = Mobile ⟨ msg ‼ `⊤ ⟩, refuted above.
-- ════════════════════════════════════════════════════════════════════

-- `send's function typing carries  Mobile T₀  and domain ≃ T₀ ⊗¹ ⟨ msg ‼ T₀ ⟩.
fn-send-mob : ∀ {N} {Γ : Ctx N} {β : Struct N} {T U a ϵ}
  → Γ ; β ⊢ K `send ∶ T ⟨ a ⟩→ U ∣ ϵ
  → Σ[ T₀ ∈ 𝕋 ] Mobile T₀ × (T₀ ⊗¹ ⟨ msg ‼ T₀ ⟩ ≃ T)
fn-send-mob (T-Const (`send {T = T₀} mob)) = T₀ , mob , ≃-refl
fn-send-mob (T-Conv (dom≃ `→ cod≃) _ d) =
  let T₀ , mob , eq = fn-send-mob d in T₀ , mob , ≃-trans eq dom≃
fn-send-mob (T-Weaken _ d) = fn-send-mob d

-- Pair inversion exposing the ⊗ shape and its ≃ to the ascribed type.
pair-shape : ∀ {N} {Γ : Ctx N} {β : Struct N} {e₁ e₂ : Tm N} {T ϵ}
  → Γ ; β ⊢ e₁ ⊗ e₂ ∶ T ∣ ϵ
  → Σ[ d ∈ Dir ] Σ[ T₁ ∈ 𝕋 ] Σ[ T₂ ∈ 𝕋 ]
      (T₁ ⊗⟨ d ⟩ T₂ ≃ T)
      × (Σ[ β₁ ∈ Struct N ] Σ[ ϵ₁ ∈ Eff ] Γ ; β₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
pair-shape (T-Pair p/s {γ₁ = γ₁} ⊢e₁ ⊢e₂ _) =
  _ , _ , _ , ≃-refl , γ₁ , _ , ⊢e₁
pair-shape (T-Conv T≃ _ d) =
  let dd , T₁ , T₂ , eq , p = pair-shape d in dd , T₁ , T₂ , ≃-trans eq T≃ , p
pair-shape (T-Weaken _ d) = pair-shape d

-- Application inversion: function and argument typings (types un-linked
-- to the result, which is all we need).
app-parts : ∀ {N} {Γ : Ctx N} {β : Struct N} {e₁ e₂ : Tm N} {U ϵ}
  → Γ ; β ⊢ e₁ · e₂ ∶ U ∣ ϵ
  → Σ[ T ∈ 𝕋 ] Σ[ a ∈ Arr ] Σ[ U′ ∈ 𝕋 ]
      (Σ[ β₁ ∈ Struct N ] Σ[ ϵ₁ ∈ Eff ] Γ ; β₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U′ ∣ ϵ₁)
      × (Σ[ β₂ ∈ Struct N ] Σ[ ϵ₂ ∈ Eff ] Γ ; β₂ ⊢ e₂ ∶ T ∣ ϵ₂)
app-parts (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  _ , _ , _ , (γ₁ , _ , ⊢e₁) , (γ₂ , _ , ⊢e₂)
app-parts (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  _ , _ , _ , (γ₁ , _ , ⊢e₁) , (γ₂ , _ , ⊢e₂)
app-parts (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  _ , _ , _ , (γ₁ , _ , ⊢e₁) , (γ₂ , _ , ⊢e₂)
app-parts (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  _ , _ , _ , (γ₁ , _ , ⊢e₁) , (γ₂ , _ , ⊢e₂)
app-parts (T-Conv _ _ d) = app-parts d
app-parts (T-Weaken _ d) = app-parts d

-- ⊗ ≃-inversion (left component) for the specific shapes here.
⊗≃-left : ∀ {d₁ d₂} {A₁ A₂ B₁ B₂ : 𝕋} → A₁ ⊗⟨ d₁ ⟩ B₁ ≃ A₂ ⊗⟨ d₂ ⟩ B₂ → A₁ ≃ A₂
⊗≃-left (eqA ⊗ eqB) = eqA

-- THE THEOREM: the send thread has no typing in bodyCtx for any struct.
¬⊢send-thread : ∀ {β} → ¬ (bodyCtx ; β ⊢ₚ ⟪ K `send · ((` 0F) ⊗ (` 2F)) ⟫)
¬⊢send-thread ⊢thr =
  let ⊢app                         = inv-⟪⟫ ⊢thr
      T , a , U′ , (_ , _ , ⊢fn) , (_ , _ , ⊢arg) = app-parts ⊢app
      T₀ , mob , dom≃              = fn-send-mob ⊢fn
      d , T₁ , T₂ , pr≃ , (_ , _ , ⊢e₁) = pair-shape ⊢arg
      -- dom≃ : T₀ ⊗¹ ⟨ msg ‼ T₀ ⟩ ≃ T ;  pr≃ : T₁ ⊗⟨ d ⟩ T₂ ≃ T
      T₀≃T₁ : T₀ ≃ T₁
      T₀≃T₁ = ⊗≃-left (≃-trans dom≃ (≃-sym pr≃))
      -- ⊢e₁ : bodyCtx ; _ ⊢ ` 0F ∶ T₁ ;  arg-type : bodyCtx 0F ≃ T₁
      Γ0≃T₁ : bodyCtx 0F ≃ T₁
      Γ0≃T₁ = arg-type ⊢e₁
      -- bodyCtx 0F = gS 0 = ⟨ msg ‼ `⊤ ⟩
      mob0 : Mobile (bodyCtx 0F)
      mob0 = mobile-≃ (≃-trans T₀≃T₁ (≃-sym Γ0≃T₁)) mob
  in ¬mobile-send-msg mob0

-- ════════════════════════════════════════════════════════════════════
-- Tie to the phantom-tail R-Com pattern (b₁=0, B₁ = 0 ∷ [], non-empty).
--   sum (suc 0 ∷ 0 ∷ []) = 1 = sum (suc 0 ∷ []), so BindCtx and bodyCtx
--   coincide with the benign single-chain case: the SAME obstruction.
-- ════════════════════════════════════════════════════════════════════

-- The very same bind contexts type the phantom-tail front group  1 ∷ 0 ∷ []
-- (BindCtx is indexed only by  sum B = 1).
bcS-phantom : BindCtx {1} sesS gS
bcS-phantom = bcS

bcR-phantom : BindCtx {1} (dual sesS) gR
bcR-phantom = bcR

-- sum-level identity making bodyCtx / TP-Res blind to the phantom 0-chain.
phantom-sum : sum (suc 0 ∷ 0 ∷ []) ≡ sum (suc 0 ∷ [])
phantom-sum = refl
