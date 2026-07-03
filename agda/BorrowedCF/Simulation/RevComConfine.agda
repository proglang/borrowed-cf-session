module BorrowedCF.Simulation.RevComConfine where

-- Reverse-direction confinement for RU-Com / RU-Choice.
--
-- CORE NEW INGREDIENT (impurity fact, machine-verified in ComHandleProbe):
-- an impure (𝕀) head redex cannot be placed ;-before a live borrow, because the
-- only two ;-before CxPat producers — TF-app₂ on an R-arrow and TF-⊗□ on a seq
-- pair — force the ;-later hole PURE (ℙ).  Formally: the frame stack above an 𝕀
-- redex is entirely LeftPat (every CxPat entry has direction 𝟙 or R, never L),
-- because the effect is 𝕀 at every level (𝕀 is ≤ϵ-maximal and the frame chain is
-- non-decreasing bottom→top).  This is the send/select-handle ≡ 0F confinement's
-- linchpin, absent for the PURE ops (drop/acq/lsplit/rsplit).

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern using (LeftPat; CxPat; _[_]𝓅)
open import BorrowedCF.Reduction.Base
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import BorrowedCF.Simulation.Confine using (count; +≡0; count-join-Dir)
open import BorrowedCF.Simulation.BeforeOrder using (before; before⇒mem)
open import BorrowedCF.Context.Join using (join)
open import BorrowedCF.Context.Pattern using (foldPattern)
open import Data.List using ([]; _∷_)
open import BorrowedCF.Simulation.BeforeOrder
  using (before-structNSeq; before-⋯ᵣ-inj; before-mono-≼; count-≼-eq)
open import BorrowedCF.Simulation.Confine using (≼⇒count≤)
open import Data.Sum using ([_,_]′)
open import BorrowedCF.Processes.Typed using (structBinder; structNSeq; BindGroup)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Base using (_↑ˡ_)
open import Data.Fin.Properties using (↑ˡ-injective)

open Nat.Variables
open Fin.Patterns
open Nat using (+-assoc; _≤_; ≤-trans; m≤m+n; m≤n+m; +-monoˡ-≤; +-monoʳ-≤; +-comm; n≤0⇒n≡0; s≤s⁻¹)

-- ── step 4(a): the send handle's binder-context has 0F ;-before it whenever the
--    block-1 index z₀ is not the minimal 0F.  The inner binder of
--    ν (b₁ ∷ []) (b₂ ∷ []) _ places 0F ;-before every LATER block-1 leaf
--    (structNSeq is a ;-chain), lifted through the two right-weakenings.  This is
--    the ONE `before` fact the LeftPat/¬before squeeze contradicts to force z₀ ≡ 0F. ──
inj-wkʳ : ∀ {n} k → 𝐂S.Inj (𝐂S.wkʳ {n = n} k)
inj-wkʳ k {x} {y} eq = ↑ˡ-injective k x y eq

before-com-binderᴸ : ∀ (b₁ b₂ : ℕ) {m} (γ : Struct m) (z₀ : 𝔽 (suc b₁)) → Fin.toℕ z₀ ≢ 0 →
  let C₁ = suc b₁ ∷ []
      C₂ = b₂ ∷ [] in
  before 0F (((z₀ ↑ˡ 0) ↑ˡ (b₂ + 0)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) )
before-com-binderᴸ b₁ b₂ {m} γ 0F       z₀≢ = ⊥-elim (z₀≢ refl)
before-com-binderᴸ b₁ b₂ {m} γ (suc z′) z₀≢ =
  inj₁ (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
         (structBinder (suc b₁ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (b₂ + 0))
         (before-⋯ᵣ-inj (𝐂S.wkʳ (b₂ + 0)) (inj-wkʳ (b₂ + 0))
           (structBinder (suc b₁ ∷ []))
           (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ 0) (inj-wkʳ 0) (structNSeq (suc b₁))
                   (before-structNSeq b₁ z′))))))

-- ── step 3(b): count is ADDITIVE over pattern-plugging.  Plugging δ into the hole
--    of a frame context 𝒫 adds count z δ on top of the frame-context count (the
--    frames themselves are unchanged; each level is a `join`, which is
--    count-additive).  Feeds the squeeze count xS 𝒫[[]] ≡ 0 once count xS 𝒫[δ] ≤ 1
--    and count xS δ ≥ 1. ──
count-plug-add : ∀ {n} (𝒫 : CxPat n) (δ : Struct n) (z : 𝔽 n)
  → count z (𝒫 [ δ ]𝓅) ≡ count z (𝒫 [ [] ]𝓅) + count z δ
count-plug-add [] δ z = refl
count-plug-add ((d , γ) ∷ 𝒫) δ z =
  count-join-Dir d z γ (𝒫 [ δ ]𝓅)
  ■ cong (count z γ +_) (count-plug-add 𝒫 δ z)
  ■ sym (+-assoc (count z γ) (count z (𝒫 [ [] ]𝓅)) (count z δ))
  ■ cong (_+ count z δ) (sym (count-join-Dir d z γ (𝒫 [ [] ]𝓅)))

-- A single frame above an 𝕀 hole: its output effect is 𝕀 and its one CxPat
-- entry is LeftPat.
frame-𝕀 : ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame n} {U T ϵ} →
          Γ ; 𝒫 ⊢ E ∶ U ∣ 𝕀 ⟶ T ∣ ϵ → (ϵ ≡ 𝕀) × LeftPat 𝒫
frame-𝕀 (TF-app₁ {a} ≤ₐ appPar appLeft appRight x) with Arr.dir a
... | L = case (appLeft refl) of λ{ (() , _) }
... | R = sym (appRight refl .proj₁) , (inj₂ refl ∷ [])
... | 𝟙 = sym (appPar   refl .proj₁) , (inj₁ refl ∷ [])
frame-𝕀 (TF-app₂ {a} ≤ₐ appPar appLeft appRight x) with Arr.dir a
... | L = sym (appLeft refl .proj₂) , (inj₂ refl ∷ [])
... | R = case (appRight refl) of λ{ (_ , ()) }
... | 𝟙 = sym (appPar  refl .proj₂) , (inj₁ refl ∷ [])
frame-𝕀 (TF-□⊗ par seq⇒p x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-□⊗ seq seq⇒p x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-⊗□ par par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-⊗□ seq () x)
frame-𝕀 (TF-; uT x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`let par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`let seq x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`let⊗ par x) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`let⊗ seq x) = refl , (inj₂ refl ∷ [])
frame-𝕀 (TF-`inj□ i) = refl , []
frame-𝕀 (TF-`case□ par x₁ x₂) = refl , (inj₁ refl ∷ [])
frame-𝕀 (TF-`case□ seq x₁ x₂) = refl , (inj₂ refl ∷ [])

-- The whole frame stack above an 𝕀 redex is LeftPat (and its top effect is 𝕀).
frames-𝕀 : ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E* : Frame* n} {U T ϵ} →
           Γ ; 𝒫 ⊢* E* ∶ U ∣ 𝕀 ⟶ T ∣ ϵ → (ϵ ≡ 𝕀) × LeftPat 𝒫
frames-𝕀 [] = refl , []
frames-𝕀 (E ∷⟨ U≃ , ϵ≤ ⟩ E*) with frames-𝕀 E*
... | refl , lp* with ϵ≤
...   | 𝕀≤𝕀 with frame-𝕀 E
...     | refl , lp = refl , ++⁺ lp lp*


-- The ≈ version (commented out in Context.Pattern) is FALSE: ≼-wk gives only one
-- direction, ((α∥B);γ ≼ α∥(B;γ)), so pulling the ∥-front out of a LeftPat context
-- holds only up to ≼, never ≈.  This ≼ version is what the count argument needs.
leftPat-pullOut-∥-≼ : ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {α β : Struct n}
                    → LeftPat 𝒫 → Γ ∶ 𝒫 [ α ∥ β ]𝓅 ≼ α ∥ 𝒫 [ β ]𝓅
leftPat-pullOut-∥-≼ {𝒫 = []} [] = ≼-refl ≈-refl
leftPat-pullOut-∥-≼ {𝒫 = (𝟙 , γ) ∷ 𝒫} {α} {β} (inj₁ refl ∷ lp) =
  ≼-trans (≼-cong-∥ (≼-refl ≈-refl) (leftPat-pullOut-∥-≼ lp))
          (≼-refl (≈-trans (≈-sym ∥-assoc)
                   (≈-trans (∥-cong ∥-comm ≈-refl) ∥-assoc)))
leftPat-pullOut-∥-≼ {𝒫 = (R , γ) ∷ 𝒫} {α} {β} (inj₂ refl ∷ lp) =
  ≼-trans (≼-cong-; (leftPat-pullOut-∥-≼ lp) (≼-refl ≈-refl))
          (≼-trans (≼-refl (;-cong ≈-refl (≈-sym ∥-unit₁)))
                   (≼-trans ≼-wk (≼-refl (∥-cong ;-unit₂ ≈-refl))))


-- ── step 2(a): a LeftPat frame context has NOTHING ;-before the hole channel xS,
--    provided xS is absent from the frame contexts (count 0 in 𝒫[[]]).  This is
--    the ;-minimality of an impure head redex, pushed into `before`. ──
leftPat-¬before : ∀ {n} {𝒫 : CxPat n} {δ : Struct n} {z xS : 𝔽 n}
  → LeftPat 𝒫 → count xS (𝒫 [ [] ]𝓅) ≡ 0 → ¬ before z xS δ
  → ¬ before z xS (𝒫 [ δ ]𝓅)
leftPat-¬before {𝒫 = []} [] c0 ¬bδ b = ¬bδ b
leftPat-¬before {𝒫 = (𝟙 , γ) ∷ 𝒫′} {δ} {z} {xS} (inj₁ refl ∷ lp) c0 ¬bδ (inj₁ bγ) =
  proj₂ (before⇒mem γ bγ) (proj₁ (+≡0 {count xS γ} c0))
leftPat-¬before {𝒫 = (𝟙 , γ) ∷ 𝒫′} {δ} {z} {xS} (inj₁ refl ∷ lp) c0 ¬bδ (inj₂ brest) =
  leftPat-¬before lp (proj₂ (+≡0 {count xS γ} c0)) ¬bδ brest
leftPat-¬before {𝒫 = (R , γ) ∷ 𝒫′} {δ} {z} {xS} (inj₂ refl ∷ lp) c0 ¬bδ (inj₁ (z∈ , xS∈)) =
  xS∈ (proj₂ (+≡0 {count xS (𝒫′ [ [] ]𝓅)} c0))
leftPat-¬before {𝒫 = (R , γ) ∷ 𝒫′} {δ} {z} {xS} (inj₂ refl ∷ lp) c0 ¬bδ (inj₂ (inj₁ brest)) =
  leftPat-¬before lp (proj₁ (+≡0 {count xS (𝒫′ [ [] ]𝓅)} c0)) ¬bδ brest
leftPat-¬before {𝒫 = (R , γ) ∷ 𝒫′} {δ} {z} {xS} (inj₂ refl ∷ lp) c0 ¬bδ (inj₂ (inj₂ bγ)) =
  proj₂ (before⇒mem γ bγ) (proj₂ (+≡0 {count xS (𝒫′ [ [] ]𝓅)} c0))

-- ── step 4(b): the ASSEMBLED ;-minimality contradiction.  Given the send handle
--    xS is a live borrow that (i) is confined to the redex (LeftPat frame stack +
--    count xS γrˢ ≥ 1 + the cross-thread linearity count xS γinner ≡ 1) and (ii)
--    has 0F ;-before it in the binder (before-com-binderᴸ, i.e. xS ≠ 0F), we reach
--    a contradiction.  Contrapositive: a well-typed com send handle is ;-minimal.
--    Combine with before-com-binderᴸ to force z₀ ≡ 0F. ──
com-xS-min : ∀ {n} {Γ : Ctx n} {𝒫ˢ : CxPat n} {γrˢ α β γinner : Struct n} {xS y : 𝔽 n}
  → ¬ Unr (Γ xS) → ¬ Unr (Γ y)
  → LeftPat 𝒫ˢ
  → Γ ∶ 𝒫ˢ [ γrˢ ]𝓅 ≼ α
  → Γ ∶ α ∥ β ≼ γinner
  → count xS γinner ≡ 1
  → before y xS γinner
  → 1 ≤ count xS γrˢ
  → ¬ before y xS γrˢ
  → ⊥
com-xS-min {Γ = Γ} {𝒫ˢ} {γrˢ} {α} {β} {γinner} {xS} {y} ¬uxS ¬uy lp ≼ˢ αβ≼ cγ1 bγ 1≤rˢ ¬brˢ =
  [ (λ bα → ¬bα (before-mono-≼ ¬uy ¬uxS ≼ˢ bα))
  , (λ bβ → proj₂ (before⇒mem β bβ) cβ0)
  ]′ (before-mono-≼ ¬uy ¬uxS αβ≼ bγ)
  where
    cαβ≤1 : count xS α + count xS β ≤ 1
    cαβ≤1 = subst (count xS α + count xS β ≤_) cγ1 (≼⇒count≤ {x = xS} ¬uxS αβ≼)
    cα≤1 : count xS α ≤ 1
    cα≤1 = ≤-trans (m≤m+n (count xS α) (count xS β)) cαβ≤1
    cα≡ : count xS α ≡ count xS (𝒫ˢ [ [] ]𝓅) + count xS γrˢ
    cα≡ = sym (count-≼-eq ¬uxS ≼ˢ) ■ count-plug-add 𝒫ˢ γrˢ xS
    c𝒫0 : count xS (𝒫ˢ [ [] ]𝓅) ≡ 0
    c𝒫0 = n≤0⇒n≡0 (s≤s⁻¹
            (subst (_≤ 1) (+-comm (count xS (𝒫ˢ [ [] ]𝓅)) 1)
              (≤-trans (+-monoʳ-≤ (count xS (𝒫ˢ [ [] ]𝓅)) 1≤rˢ)
                (subst (_≤ 1) cα≡ cα≤1))))
    ¬bα : ¬ before y xS (𝒫ˢ [ γrˢ ]𝓅)
    ¬bα = leftPat-¬before lp c𝒫0 ¬brˢ
    1≤α : 1 ≤ count xS α
    1≤α = ≤-trans 1≤rˢ (subst (count xS γrˢ ≤_) (sym cα≡)
            (m≤n+m (count xS γrˢ) (count xS (𝒫ˢ [ [] ]𝓅))))
    cβ0 : count xS β ≡ 0
    cβ0 = n≤0⇒n≡0 (s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count xS β) 1≤α) cαβ≤1))
