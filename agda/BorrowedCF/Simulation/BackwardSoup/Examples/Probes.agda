-- Backward simulation, failure mode F4 of PLAN.md §2: the soup rules fire
-- on ANY thread that holds the right term, while `R-Drop`, `R-Discard` and
-- `R-Acq` all insist that the consumed handle be the variable `0F`, i.e.
-- the first handle of the first group of the LEFT binder list.
--
-- HISTORY.  `Pf4` (F4 a) and `Pf4b` (F4 b) below used to be genuine
-- counterexamples: WELL-TYPED closed processes on which the soup steps while
-- no typed rule applies, and whose soup reduct is the flattening of no
-- well-typed process at all (PLAN.md §4-5, remedy (i)).  Both are now
-- ILL-TYPED, because the split constants and the binder-group contexts have
-- been tightened:
--
--   * `lsplit` / `rsplit` demand `¬ Skips s` of the FIRST component as well
--     as of the second, so a split never produces a bare `⟨ skip ⟩` handle and
--     never moves a group's `acq` into a fresh group behind a `⟨ ret ⟩`;
--   * `BindCtx.cons-ret/acq` demands `¬skips₂ : ¬ Skips s₂` (a group boundary
--     is formed only in front of real work) and `acqHead : AcqHeadCtx Γ₂` (the
--     first bound handle of a non-first group carries that group's `acq`);
--     `BindCtx.cons-acq` demands the same `acqHead`.
--
-- The soup steps and the "the reduct is not a flattening" facts are kept; the
-- typing derivations are replaced by CHECKED refutations of the exact premise
-- that each of them would now have to discharge.
module BorrowedCF.Simulation.BackwardSoup.Examples.Probes where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context

open import Data.List.Relation.Unary.All using ([]; _∷_)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Reduction.ExpressionsSoup as 𝐒Red
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open 𝐓 using (_;_⊢ₚ_)
open 𝐓Tm using (_;_⊢_∶_∣_)

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

------------------------------------------------------------------------
-- F4 (a).  After an `lsplit` of a `⟨ s ; ret ⟩` handle, one thread holds the
-- `ret` half and another the live half.  The `ret` half is the SECOND
-- handle of its group, so `RUS-Drop` fires but `R-Drop` cannot.
--
-- Binder shape `0 ∷ 2 ∷ 1 ∷ []` on the left endpoint:
--   group 0 : width 0            -- the endpoint starts with an `acq` boundary
--   group 1 : width 2            -- the result of the lsplit: ⟨acq ; end ‼⟩, ⟨ret⟩
--   group 2 : width 1            -- what the partner may acquire afterwards

e0 e1 e2 e3 : 𝐓Tm.Tm 4
e0 = 𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 0F))
e1 = 𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 1F)
e2 = 𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 2F))
e3 = 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F)

Pf4 : 𝐓.Proc 0
Pf4 =
  𝐓.ν (0 ∷ 2 ∷ 1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ e0 ⟫ 𝐓.∥ 𝐓.⟪ e1 ⟫) 𝐓.∥ (𝐓.⟪ e2 ⟫ 𝐓.∥ 𝐓.⟪ e3 ⟫))

Cf4 : 𝐒.Config 1 4
Cf4 = 𝑪 Pf4

Cf4≡ :
  Cf4 ≡
  𝐒.config
    ((true , 𝐒.acq ∷ 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
          𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 1) ]) ∷
      (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
          𝓒[ 𝐒Tm.`phi (0F , 1) × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])
Cf4≡ = refl

-- Thread 1 holds exactly the `RUS-Drop` redex for slot 1 of endpoint 0.
Cf4′ : 𝐒.Config 1 4
Cf4′ =
  𝐒.config
    ((true , 𝐒.acq ∷ 𝐒.acq ∷ [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
          𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])) ∷
      𝐒Tm.* ∷
      (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
          𝓒[ 𝐒Tm.`phi (0F , 1) × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])

step-f4-drop : Cf4 𝐑.─→ₚ Cf4′
step-f4-drop = 𝐑.RUS-Drop 1F 0F 0F [] (𝐒.acq ∷ []) [] refl refl refl

------------------------------------------------------------------------
-- Typability of the F4 (a) probe.
--
-- The soup step above was only interesting because `Pf4` used to be well
-- typed.  Under the strict rules it is NOT, and the block below says exactly
-- which premise fails.

f4-B1 : 𝐓.⊢ᴮ (0 ∷ 2 ∷ 1 ∷ [])
f4-B1 = _ ∷ _ ∷ []

f4-B2 : 𝐓.⊢ᴮ (1 ∷ [])
f4-B2 = []

-- The left endpoint used to be typed by the binder context
--
--   𝐓.cons-acq
--     (𝐓.cons-ret/acq (acq ; end ‼)
--       (≃-trans ≃-skipʳ (≃-; ≃-refl (≃-sym ≃-skipˡ)))          -- s≃, see below
--       (𝐓.cons (acq ; end ‼) ret (λ { (_ ; ()) }) ≃-refl
--         (𝐓.cons ret skip (λ ()) ≃-skipʳ (𝐓.nil skip)))
--       f4-tail-block)                                        -- see below
--
-- an initial `acq` boundary, then the two halves of the lsplit, then a second
-- boundary and the remainder.  Under the STRICT rules that derivation is gone:
-- the inner `cons-ret/acq` must also supply `¬skips₂ : ¬ Skips s₂`, and both
-- its `s≃` premise and its continuation block force `s₂ ≡ skip`.

f4-head f4-rest : 𝕊 0
f4-head = acq ; end ‼          -- the live half of the lsplit
f4-rest = skip ; end ‼         -- what the group's `acq` releases

-- The `s≃` premise of the blocked `cons-ret/acq`: the second boundary sits
-- directly in front of the next group's `acq`, so the group's own remainder
-- `s₂` is `skip`.
f4-second-boundary : (f4-head ; skip) ≃ (acq ; f4-rest)
f4-second-boundary = ≃-trans ≃-skipʳ (≃-; ≃-refl (≃-sym ≃-skipˡ))

-- ... and the continuation block forces the same `s₂ ≡ skip`.
f4-tail-block : 𝐓.BindCtx (acq ; skip) (1 ∷ []) (⟨ acq ⟩ ∷ [])
f4-tail-block = 𝐓.last (𝐓.cons acq skip (λ { (() ; _) }) ≃-refl (𝐓.nil skip))

-- So `cons-ret/acq` would have to discharge `¬ Skips skip`, which is absurd:
-- a group boundary is only formed before real work.  `Pf4` is ill-typed.
f4-boundary-blocked : ¬ (¬ Skips {0} skip)
f4-boundary-blocked ¬sk = ¬sk skip

f4-C2 : 𝐓.BindCtx (skip ; end ⁇) (1 ∷ []) (⟨ end ⁇ ⟩ ∷ [])
f4-C2 =
  𝐓.last
    (𝐓.cons (end ⁇) skip (λ { (_ ; ()) })
      (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (𝐓.nil skip))

f4-Γ : Ctx 4
f4-Γ = ⟨ acq ; end ‼ ⟩ ∷ ⟨ ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

-- The live half of the split is a BORROWED handle, hence mobile: this is
-- what lets its use commute with the drop of the `ret` half.
f4-mobile0 : MobCx f4-Γ (` 0F)
f4-mobile0 = ` ⟨ end ‼ , end , ≃-refl ⟩

⊢e0 : f4-Γ ; ([] ∥ ([] ∥ (` 0F))) ⊢ e0 ∶ `⊤ ∣ 𝕀
⊢e0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-AppUnr refl ℙ≤ϵ
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl)))

⊢e1 : f4-Γ ; ([] ∥ (` 1F)) ⊢ e1 ∶ `⊤ ∣ 𝕀
⊢e1 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`drop))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl))

⊢e2 : f4-Γ ; ([] ∥ ([] ∥ (` 2F))) ⊢ e2 ∶ `⊤ ∣ 𝕀
⊢e2 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
    (𝐓Tm.T-AppUnr refl ℙ≤ϵ
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
      (𝐓Tm.T-Conv ⟨ ≃-sym ≃-skipʳ ⟩ ℙ≤ϵ (𝐓Tm.T-Var 2F refl)))

⊢e3 : f4-Γ ; ([] ∥ (` 3F)) ⊢ e3 ∶ `⊤ ∣ 𝕀
⊢e3 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 3F refl))

-- The structure the four threads produce, and the structure `TP-Res`
-- prescribes for the body.
f4-der f4-γ : Struct 4
f4-der =
  (([] ∥ ([] ∥ (` 0F))) ∥ ([] ∥ (` 1F))) ∥
  (([] ∥ ([] ∥ (` 2F))) ∥ ([] ∥ (` 3F)))
f4-γ =
  ([] ∥ (((` 0F) ; ((` 1F) ; [])) ∥ (((` 2F) ; []) ∥ []))) ∥
  (((` 3F) ; []) ∥ []) ∥ []

f4-normal : Struct 4
f4-normal = (((` 0F) ; (` 1F)) ∥ (` 2F)) ∥ (` 3F)

-- Threads compose in PARALLEL, but the binder group `2` sequences its two
-- handles.  `∥/;-transmute` bridges the two -- and it needs one side to be
-- MOBILE.  Handle 0F is `⟨ acq ; end ‼ ⟩`, a borrowed handle, hence mobile.
f4-der≈ : f4-Γ ∶ f4-der ≈ f4-normal
f4-der≈ =
  ≈-trans
    (∥-cong (∥-cong (≈-trans ∥-unit₁ ∥-unit₁) ∥-unit₁)
            (∥-cong (≈-trans ∥-unit₁ ∥-unit₁) ∥-unit₁))
    (≈-trans (∥-cong (∥/;-transmute (inj₁ f4-mobile0)) ≈-refl)
             (≈-sym ∥-assoc))

f4-γ≈ : f4-Γ ∶ f4-γ ≈ f4-normal
f4-γ≈ =
  ≈-trans ∥-unit₂
    (∥-cong
      (≈-trans ∥-unit₁
        (∥-cong (;-cong ≈-refl ;-unit₂)
                (≈-trans ∥-unit₂ ;-unit₂)))
      (≈-trans ∥-unit₂ ;-unit₂))

f4-≼ : f4-Γ ∶ f4-der ≼ f4-γ
f4-≼ = ≼-refl (≈-trans f4-der≈ (≈-sym f4-γ≈))

-- Everything ELSE about `Pf4` still checks: the group shapes `f4-B1`/`f4-B2`,
-- the four thread derivations `⊢e0`-`⊢e3`, the structure reshuffling `f4-≼`
-- (via `∥/;-transmute` on the mobile handle `0F`) and the right endpoint
-- `f4-C2`.  Only the left binder context is now unavailable, by
-- `f4-boundary-blocked` above:
--
--   𝐓.TP-Res skip ‼ f4-B1 f4-B2 <NO SUCH BindCtx> f4-C2
--     (𝐓.TP-Weaken f4-≼
--       (𝐓.TP-Par
--         (𝐓.TP-Par (𝐓.TP-Expr ⊢e0) (𝐓.TP-Expr ⊢e1))
--         (𝐓.TP-Par (𝐓.TP-Expr ⊢e2) (𝐓.TP-Expr ⊢e3))))


-- Reading the reduct back.  `RUS-Drop` flips the boundary flag to `acq`,
-- i.e. it RELEASES the boundary -- correct only when the dropped handle was
-- the last one left in its group, which is not the case here.  The reduct's
-- left-endpoint flag list `acq ∷ acq ∷ []` can only come from a binder list
-- `0 ∷ 0 ∷ b ∷ []` (`ϕ[ b ] ≡ acq` iff `b ≡ 0`) ...
f4-flags-0-0-1 :
  proj₂ (𝐔.UB[ 0 ∷ 0 ∷ 1 ∷ [] ] (𝐒.leftEnd {n = 1} 0F)
       (𝐒Tm.* , 𝐒.leftEnd {n = 1} 0F , 𝐒Tm.*))
  ≡ 𝐒.acq ∷ 𝐒.acq ∷ []
f4-flags-0-0-1 = refl

-- ... whereas merely SHRINKING the split group keeps the boundary blocked:
f4-flags-0-1-1 :
  proj₂ (𝐔.UB[ 0 ∷ 1 ∷ 1 ∷ [] ] (𝐒.leftEnd {n = 1} 0F)
       (𝐒Tm.* , 𝐒.leftEnd {n = 1} 0F , 𝐒Tm.*))
  ≡ 𝐒.acq ∷ 𝐒.drop ∷ []
f4-flags-0-1-1 = refl

-- ... and `⊢ᴮ` rejects `0 ∷ 0 ∷ 1 ∷ []`: only the FIRST group may be empty.
-- So `Cf4′` is not the flattening of any well-typed process at all.
f4-reduct-shape-untypable : ¬ (𝐓.⊢ᴮ (0 ∷ 0 ∷ 1 ∷ []))
f4-reduct-shape-untypable (nz ∷ _) with Nat.>-nonZero⁻¹ 0 ⦃ nz ⦄
... | ()

-- `R-Drop` would have to fire on variable `0F`, which here is the LIVE half
-- of the split, not the `ret` half; and no `≋` rule permutes handles inside
-- a binder group.
f4-handle-0F : lookup f4-Γ 0F ≡ ⟨ acq ; end ‼ ⟩
f4-handle-0F = refl

f4-handle-1F : lookup f4-Γ 1F ≡ ⟨ ret ⟩
f4-handle-1F = refl

------------------------------------------------------------------------
-- F4 (b).  `discard` on a non-first handle of a group.
--
-- Binder shape `1 ∷ 2 ∷ []`: the `⟨ skip ⟩` handle is the FIRST handle of
-- the second group, hence variable `1F`, and `R-Discard` wants `0F`.
-- Here no mobility is needed: handles `1F` and `2F` are sequenced inside
-- their group, and one thread uses them in that order.

b0 b1 b2 : 𝐓Tm.Tm 4
b0 = 𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 0F)
b1 = (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 1F))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 2F)))
b2 = 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F)

Pf4b : 𝐓.Proc 0
Pf4b =
  𝐓.ν (1 ∷ 2 ∷ []) (1 ∷ [])
    ((𝐓.⟪ b0 ⟫ 𝐓.∥ 𝐓.⟪ b1 ⟫) 𝐓.∥ 𝐓.⟪ b2 ⟫)

Cf4b : 𝐒.Config 1 3
Cf4b = 𝑪 Pf4b

Cf4b≡ :
  Cf4b ≡
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹
         𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ])
       𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
             (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])
Cf4b≡ = refl

Cf4b′ : 𝐒.Config 1 3
Cf4b′ =
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      (𝐒Tm.* 𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
             (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])

step-f4b-discard : Cf4b 𝐑.─→ₚ Cf4b′
step-f4b-discard =
  𝐑.RUS-Discard 1F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷ [])
    (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-phi 𝐒Red.V-`) 𝐒Red.V-K)
    refl

f4b-Γ : Ctx 4
f4b-Γ = ⟨ ret ⟩ ∷ ⟨ skip ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

-- The left endpoint used to be typed by
--
--   𝐓.cons-ret/acq skip ≃-refl
--     (𝐓.cons ret skip (λ { (_ ; ()) })
--       (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (𝐓.nil skip))
--     f4b-second-group
--
-- Its `s₂` is `end ‼`, so the new `¬skips₂` premise would be fine here.  What
-- blocks the derivation is the other new premise, `acqHead`: the second
-- group's FIRST bound handle is the `⟨ skip ⟩` that an `lsplit` peeled off
-- `⟨ acq ; end ‼ ⟩ ≃ ⟨ skip ; (acq ; end ‼) ⟩`, i.e. a group head that does not
-- carry its group's `acq`.  (That `lsplit` is itself now ruled out as well, by
-- the new `¬ Skips s` premise of the `lsplit` constant.)

-- The second group, exactly as the old derivation had it:
f4b-second-group :
  𝐓.BindCtx (acq ; end ‼) (2 ∷ []) (⟨ skip ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
f4b-second-group =
  𝐓.last
    (𝐓.cons skip (acq ; end ‼) (λ { (() ; _) }) ≃-skipˡ
      (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ (𝐓.nil skip)))

-- ... and `AcqHeadCtx` of its context is `¬ Skips skip`, which is refutable.
f4b-acqHead-blocked : ¬ 𝐓.AcqHeadCtx (⟨ skip ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])
f4b-acqHead-blocked ah = ah skip

⊢b0 : f4b-Γ ; ([] ∥ (` 0F)) ⊢ b0 ∶ `⊤ ∣ 𝕀
⊢b0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`drop))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl))

⊢b1 :
  f4b-Γ ; (([] ∥ (` 1F)) ; ([] ∥ ([] ∥ (` 2F)))) ⊢ b1 ∶ `⊤ ∣ 𝕀
⊢b1 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 1F refl)))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-AppUnr refl ℙ≤ϵ
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl))))

⊢b2 : f4b-Γ ; ([] ∥ (` 3F)) ⊢ b2 ∶ `⊤ ∣ 𝕀
⊢b2 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 3F refl))

f4b-der f4b-γ f4b-normal : Struct 4
f4b-der =
  (([] ∥ (` 0F)) ∥ (([] ∥ (` 1F)) ; ([] ∥ ([] ∥ (` 2F))))) ∥ ([] ∥ (` 3F))
f4b-γ =
  (((` 0F) ; []) ∥ (((` 1F) ; ((` 2F) ; [])) ∥ [])) ∥
  (((` 3F) ; []) ∥ []) ∥ []
f4b-normal = ((` 0F) ∥ ((` 1F) ; (` 2F))) ∥ (` 3F)

f4b-≼ : f4b-Γ ∶ f4b-der ≼ f4b-γ
f4b-≼ =
  ≼-refl
    (≈-trans
      (∥-cong (∥-cong ∥-unit₁
                      (;-cong ∥-unit₁ (≈-trans ∥-unit₁ ∥-unit₁)))
              ∥-unit₁)
      (≈-sym
        (≈-trans ∥-unit₂
          (∥-cong
            (∥-cong ;-unit₂
                    (≈-trans ∥-unit₂ (;-cong ≈-refl ;-unit₂)))
            (≈-trans ∥-unit₂ ;-unit₂)))))

-- As for `Pf4`, only the left binder context is missing; the rest checks:
--
--   𝐓.TP-Res skip ‼ (_ ∷ []) [] <NO SUCH BindCtx> f4-C2
--     (𝐓.TP-Weaken f4b-≼
--       (𝐓.TP-Par (𝐓.TP-Par (𝐓.TP-Expr ⊢b0) (𝐓.TP-Expr ⊢b1))
--                 (𝐓.TP-Expr ⊢b2)))

------------------------------------------------------------------------
-- F4 (c).  `acq` on the first handle of a group that is not the first.
--
-- Binder shape `1 ∷ 0 ∷ 2 ∷ []`: the width-0 group in the MIDDLE turns the
-- second boundary into `acq`, so `RUS-Acquire` fires on the first handle of
-- the third group (variable `1F`).  `R-Acq` insists on `ν (0 ∷ suc b ∷ B) …`
-- with the handle at `0F`, and no `≋` rule permutes binder groups.

c0 c1 c2 : 𝐓Tm.Tm 4
c0 = 𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 0F)
c1 = (𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 1F)))
     𝐓Tm.; (𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 2F)))
c2 = 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 3F)

Pf4c : 𝐓.Proc 0
Pf4c =
  𝐓.ν (1 ∷ 0 ∷ 2 ∷ []) (1 ∷ [])
    ((𝐓.⟪ c0 ⟫ 𝐓.∥ 𝐓.⟪ c1 ⟫) 𝐓.∥ 𝐓.⟪ c2 ⟫)

Cf4c : 𝐒.Config 1 3
Cf4c = 𝑪 Pf4c

Cf4c≡ :
  Cf4c ≡
  𝐒.config
    ((true , 𝐒.drop ∷ 𝐒.acq ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹
         (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
           𝓒[ 𝐒Tm.`phi (0F , 1) × 0F × 𝐒Tm.* ]))
       𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
             (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])
Cf4c≡ = refl

Cf4c′ : 𝐒.Config 1 3
Cf4c′ =
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
       𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
             (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])

step-f4c-acq : Cf4c 𝐑.─→ₚ Cf4c′
step-f4c-acq =
  𝐑.RUS-Acquire 1F 0F 0F
    ((𝐒Red.□; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
        (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]))) ∷
     𝐒Red.app₂ (𝐒Tm.K 𝐒Tm.`discard) 𝟙 (λ _ → 𝐒Red.V-K) ∷ [])
    (𝐒.drop ∷ []) []
    refl refl refl

f4c-Γ : Ctx 4
f4c-Γ = ⟨ ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ ⟨ end ⁇ ⟩ ∷ []

f4c-C1 :
  𝐓.BindCtx (skip ; end ‼) (1 ∷ 0 ∷ 2 ∷ [])
    ((⟨ ret ⟩ ∷ []) V.++ (⟨ acq ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ []))
f4c-C1 =
  𝐓.cons-ret/acq skip ≃-refl (λ ())
    (𝐓.cons ret skip (λ { (_ ; ()) })
      (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (𝐓.nil skip))
    (𝐓.cons-acq
      (𝐓.last
        (𝐓.cons acq (acq ; end ‼) (λ { (() ; _) }) ≃-refl
          (𝐓.cons (acq ; end ‼) skip (λ { (() ; _) }) ≃-skipʳ
            (𝐓.nil skip))))
      (λ ()))
    (λ ())

⊢c0 : f4c-Γ ; ([] ∥ (` 0F)) ⊢ c0 ∶ `⊤ ∣ 𝕀
⊢c0 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`drop))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 0F refl))

⊢c1 :
  f4c-Γ ; (([] ∥ ([] ∥ (` 1F))) ; ([] ∥ ([] ∥ (` 2F))))
  ⊢ c1 ∶ `⊤ ∣ 𝕀
⊢c1 =
  𝐓Tm.T-Seq `⊤
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`discard))
      (𝐓Tm.T-AppUnr refl ℙ≤ϵ
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
        (𝐓Tm.T-Conv ⟨ ≃-sym ≃-skipʳ ⟩ ℙ≤ϵ (𝐓Tm.T-Var 1F refl))))
    (𝐓Tm.T-AppUnr refl 𝕀≤𝕀
      (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
      (𝐓Tm.T-AppUnr refl ℙ≤ϵ
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`acq))
        (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 2F refl))))

⊢c2 : f4c-Γ ; ([] ∥ (` 3F)) ⊢ c2 ∶ `⊤ ∣ 𝕀
⊢c2 =
  𝐓Tm.T-AppUnr refl 𝕀≤𝕀
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Const 𝐓Tm.`end))
    (𝐓Tm.T-Conv ≃-refl ℙ≤ϵ (𝐓Tm.T-Var 3F refl))

f4c-der f4c-γ : Struct 4
f4c-der =
  (([] ∥ (` 0F)) ∥
   (([] ∥ ([] ∥ (` 1F))) ; ([] ∥ ([] ∥ (` 2F))))) ∥ ([] ∥ (` 3F))
f4c-γ =
  (((` 0F) ; []) ∥ ([] ∥ (((` 1F) ; ((` 2F) ; [])) ∥ []))) ∥
  (((` 3F) ; []) ∥ []) ∥ []

f4c-≼ : f4c-Γ ∶ f4c-der ≼ f4c-γ
f4c-≼ =
  ≼-refl
    (≈-trans
      (∥-cong (∥-cong ∥-unit₁
                      (;-cong (≈-trans ∥-unit₁ ∥-unit₁)
                             (≈-trans ∥-unit₁ ∥-unit₁)))
              ∥-unit₁)
      (≈-sym
        (≈-trans ∥-unit₂
          (∥-cong
            (∥-cong ;-unit₂
                    (≈-trans ∥-unit₁
                      (≈-trans ∥-unit₂ (;-cong ≈-refl ;-unit₂))))
            (≈-trans ∥-unit₂ ;-unit₂)))))

-- ... and here the typability attempt FAILS, for a reason that settles the
-- question: `⊢ᴮ` allows an empty binder group only in FIRST position, so a
-- width-0 group in the middle is rejected by `TP-Res` outright.  Everything
-- else about `Pf4c` is fine -- the binder context `f4c-C1` and the four
-- expression derivations above all check.
f4c-shape-untypable : ¬ (𝐓.⊢ᴮ (1 ∷ 0 ∷ 2 ∷ []))
f4c-shape-untypable (nz ∷ _) with Nat.>-nonZero⁻¹ 0 ⦃ nz ⦄
... | ()

-- The general argument: `RUS-Acquire`'s redex `𝓒[ phi (x , k) × x × e ]` is
-- the FIRST handle of group `k+1`, and its side condition asks flag `k` to
-- be `acq`, i.e. `ϕ[ B ‼ k ] ≡ acq`, i.e. group `k` is empty.  With `⊢ᴮ`
-- that forces `k ≡ 0`, so the handle is the variable `0F` of a `ν` whose
-- first group is empty -- exactly `R-Acq`.  The typed rules are COMPLETE
-- for acquire on flattenings of well-typed processes.
--
-- `Cf4c` is nevertheless a legitimate soup configuration: it is the kind of
-- state that the F4 (a) step above CREATES (a boundary released while its
-- group is still populated), and the soup can then acquire across it.


------------------------------------------------------------------------
-- What goes wrong in (b) and (c), stated on `UB[_]`.
--
-- `RUS-Discard` and `RUS-Acquire` both leave the surviving handle with an
-- EMPTY left context (`𝓒[ * × x × … ]`), because that is what the redex
-- pattern rewrites to.  For a handle that is the head of the endpoint that
-- is right; for a handle inside a later group it is not -- `UB[_]` gives
-- such a handle the group's incoming boundary as its left context.

f4b-typed-survivor :
  proj₁ (𝐔.UB[ 1 ∷ 1 ∷ [] ] (𝐒.leftEnd {n = 1} 0F)
          (𝐒Tm.* , 𝐒.leftEnd {n = 1} 0F , 𝐒Tm.*)) 1F
  ≡ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]
f4b-typed-survivor = refl

f4c-typed-survivor :
  proj₁ (𝐔.UB[ 1 ∷ 2 ∷ [] ] (𝐒.leftEnd {n = 1} 0F)
          (𝐒Tm.* , 𝐒.leftEnd {n = 1} 0F , 𝐒Tm.*)) 1F
  ≡ 𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]
f4c-typed-survivor = refl

-- The soup instead produced `𝓒[ * × 0F × * ]` in both cases:
f4c-soup-survivor :
  lookup (𝐒.threads Cf4c′) 1F
  ≡ ((𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
     𝐒Tm.; (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹
           (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])))
f4c-soup-survivor = refl
