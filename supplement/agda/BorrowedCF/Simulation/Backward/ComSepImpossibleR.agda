-- | The com-reflect recv-side "leading-cons-acq zero-branch" is un-typeable.
--
--   RECV mirror of ComSepImpossible.sep-com-¬wt.  When the recv handle of a
--   reverse RU-Com sits in a BR block whose bind-group prefix begins with a
--   `zero` (a leading cons-acq marker), the redex is un-typeable.  Reuses the
--   POLARITY-GENERAL navigation/block-shape core from ComSepImpossible (which is
--   independent of the msg polarity); only the four `msg`-headed wrappers
--   (front-msg / block-analysis / extract-block) are re-derived here with an
--   abstract polarity `p`, together with the ᴿ before-order lemma
--   `before-com-binderᴿ-later` and the final `sep-com-¬wt-R` assembly.
module BorrowedCF.Simulation.Backward.ComSepImpossibleR where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Types.ContainsEnd using (HasT; seqˡ; seqʳ)
open import BorrowedCF.Context using (Ctx; _⸴*_)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil; bindCtx-B≢[])
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_)
open import BorrowedCF.Simulation.Backward.ComSepNoMsg
  using (NoMsg; noMsg-acq; noMsg-≃; noMsg-msg-⊥; noMsg-;-snd; bindCtx-noMsg-not-msg; bindCtx-lookup-NoMsg; bindCtx′-lookup-NoMsg; _;_; skip; ret)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Properties using (lookup-++ʳ; lookup-++ˡ)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; toℕ-injective; toℕ<n; toℕ-fromℕ<)
open import Data.Fin using (splitAt; fromℕ<)
open import Data.List using (length)
open import Data.Fin.Base using (_↑ʳ_; _↑ˡ_)
open import BorrowedCF.Processes.Typed using (bindCtx-inv-cons)
open Fin.Patterns
open import BorrowedCF.Terms
open import BorrowedCF.Context using (Struct; _∶_≼_; _∥_)
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅; LeftPat)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Processes.Typed using (structBinder)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before; before-⋯ᵣ-inj)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.RevComConfine using (com-xS-min)
open import BorrowedCF.Simulation.Support.RevGrindC
  using (count-handle-groupᴿ; inj-wkˡ; inj-wkʳ)
open import BorrowedCF.Simulation.Backward.ComSepBefore using (before-structBinder-later)
open import BorrowedCF.Simulation.Support.RevGrindA using (choice-¬before; barevar-arg-count)
open import BorrowedCF.Simulation.Backward.ComConfineGen using (recv-¬mobile)
open import BorrowedCF.Types using (unr⇒mobile)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 using (recv-handle-≃msg-app)
open import Data.Sum using (inj₁; inj₂) renaming (map to ⊎-map)
import Data.Sum as Sum

open import BorrowedCF.Simulation.Backward.ComSepImpossible
  using ( AmbInvAcq; base-acq; Inv; descend; 0<len++
        ; BlockShape; bsEnd; bsRet; split-acqhd
        ; front-msg-end-⊥; front-msg-ret-⊥
        ; mob⇒noMsg-ar )

open AmbInvAcq

-- polarity-general re-derivation of bindCtx′-noMsg-not-msg (its ‼ counterpart
-- in ComSepImpossible is proof-identical; noMsg-msg-⊥ is polarity-agnostic).
bindCtx′-noMsg-not-msgᴾ : ∀ {w} {Γ : Ctx w} {ar} {i : 𝔽 w} {p T} →
  BindCtx′ ar Γ → NoMsg ar → lookup Γ i ≃ ⟨ msg p T ⟩ → ⊥
bindCtx′-noMsg-not-msgᴾ {i = i} bt nm eq with bindCtx′-lookup-NoMsg bt nm i
... | s' , ej , NMs' =
      noMsg-msg-⊥ (noMsg-≃ (≃-⟨⟩⁻¹ (≃-trans (≃-reflexive (sym ej)) eq)) NMs')

bindCtx-noMsg-not-msgᴾ : ∀ {s BG} {Γ : Ctx (sum BG)} {i} {p T} → BindCtx s BG Γ → NoMsg s
                       → lookup Γ i ≃ ⟨ msg p T ⟩ → ⊥
bindCtx-noMsg-not-msgᴾ {i = i} C NMs eqm with bindCtx-lookup-NoMsg C NMs i
... | s′ , e1 , NM =
  noMsg-msg-⊥ (noMsg-≃ (≃-⟨⟩⁻¹ (subst (_≃ _) e1 eqm)) NM)

------------------------------------------------------------------------
-- msg-headed block wrappers, POLARITY-GENERAL (abstract `p`).  Copied from
-- ComSepImpossible's ‼ versions; the proofs are polarity-agnostic (the
-- polarity-free `mob⇒noMsg-ar` is reused directly).
------------------------------------------------------------------------

front-msg-shape-⊥ᴾ : {a a-rest SB : 𝕊 0} {p : Pol} {T : 𝕋} →
  a ≃ msg p T → a ; a-rest ≃ SB → BlockShape SB → ⊥
front-msg-shape-⊥ᴾ a≃msg aeq (bsEnd nhQ eq) =
  front-msg-end-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq) eq)
front-msg-shape-⊥ᴾ a≃msg aeq (bsRet nhQ split eq) with split-acqhd split
... | y' , Q' , s₁y' =
      front-msg-ret-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃msg) ≃-refl) aeq) eq) s₁y'

block-analysisᴾ : ∀ {w'} {SB a a-rest : 𝕊 0} {ΓBt : Ctx w'} {p : Pol} {T : 𝕋} →
  a ; a-rest ≃ SB → BindCtx′ a-rest ΓBt → BlockShape SB →
  (h : 𝔽 (suc w')) → lookup (⟨ a ⟩ ∷ ΓBt) h ≃ ⟨ msg p T ⟩ →
  ⊥ ⊎ (¬ Mobile ⟨ a ⟩ × Fin.toℕ h ≢ 0)
block-analysisᴾ aeq bc-tail bs 0F hmsg =
  inj₁ (front-msg-shape-⊥ᴾ (≃-⟨⟩⁻¹ hmsg) aeq bs)
block-analysisᴾ aeq bc-tail bs (suc h′) hmsg = inj₂ (¬mob-a , λ ())
  where
    ¬mob-a : ¬ Mobile ⟨ _ ⟩
    ¬mob-a mob = bindCtx′-noMsg-not-msgᴾ bc-tail (mob⇒noMsg-ar mob bs aeq) hmsg

extract-blockᴾ : ∀ {sh : 𝕊 0} {W'} {B₂ : BindGroup} {Γh : Ctx (suc W' + sum B₂)} {p : Pol} {T : 𝕋}
  → AmbInvAcq sh → BindCtx sh (suc W' ∷ B₂) Γh
  → (k : 𝔽 (suc W' + sum B₂)) → Fin.toℕ k Nat.< suc W' → lookup Γh k ≃ ⟨ msg p T ⟩
  → ⊥ ⊎ (¬ Mobile (lookup Γh 0F) × Fin.toℕ k ≢ 0)
extract-blockᴾ aia (last (cons a ar ¬sk aeq bt)) k k<sW' hmsg =
  block-analysisᴾ aeq bt (bsEnd (AmbInvAcq.nhQ aia) (AmbInvAcq.eq aia)) k hmsg
extract-blockᴾ {W' = W'} {B₂ = B₂} aia
  (cons-ret/acq s₁ {Γ₁ = Γ1} {Γ₂ = Γ2} split (cons a ar ¬sk aeq bt) rest) k k<sW' hmsg =
  ⊎-map (λ z → z) (λ (¬m , k₁≢0) → ¬m , (λ e → k₁≢0 (tk₁ ■ e)))
    (block-analysisᴾ aeq bt
       (bsRet (AmbInvAcq.nhQ aia) (≃-trans split (AmbInvAcq.eq aia)) ≃-refl)
       k₁ hmsg₁)
  where
    k₁ : 𝔽 (suc W')
    k₁ = fromℕ< k<sW'
    tk₁ : Fin.toℕ k₁ ≡ Fin.toℕ k
    tk₁ = toℕ-fromℕ< k<sW'
    k≡ : k ≡ k₁ ↑ˡ sum B₂
    k≡ = toℕ-injective (sym (toℕ-↑ˡ k₁ (sum B₂) ■ tk₁))
    hmsg₁ : lookup Γ1 k₁ ≃ ⟨ msg _ _ ⟩
    hmsg₁ = subst (_≃ _)
             (cong (lookup (Γ1 ⸴* Γ2)) k≡ ■ lookup-++ˡ Γ1 Γ2 k₁) hmsg

------------------------------------------------------------------------
-- before-com-binderᴿ-later : the RIGHT-group mirror of
-- ComSepBefore.before-com-binderᴸ-later, threading a later same-block handle
-- through the BR component of the com binder.
------------------------------------------------------------------------

before-com-binderᴿ-later : ∀ (B₁ B₂ BL : BindGroup) {m q} (γ : Struct m)
    (fr x : 𝔽 (sum (B₁ ++ B₂)))
    → Fin.toℕ fr ≡ sum B₁ → Fin.toℕ x ≡ sum B₁ + q → q ≢ 0 →
  before ((𝐂S.wkˡ (sum BL) fr) ↑ˡ m) ((𝐂S.wkˡ (sum BL) x) ↑ˡ m)
    ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (B₁ ++ B₂)) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder (B₁ ++ B₂) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum (B₁ ++ B₂))) )
before-com-binderᴿ-later B₁ B₂ BL {m} γ fr x tfr tx qne =
  inj₁ (inj₂ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
    (structBinder (B₁ ++ B₂) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL))
    (before-⋯ᵣ-inj (𝐂S.wkˡ (sum BL)) (inj-wkˡ (sum BL)) (structBinder (B₁ ++ B₂))
      (before-structBinder-later B₁ B₂ fr x tfr tx qne))))

------------------------------------------------------------------------
-- The export: the com-reflect recv-side leading-cons-acq zero-branch is
-- un-typeable.  Structural mirror of sep-com-¬wt with Γ₂/BR/recv confinement.
------------------------------------------------------------------------

sep-com-¬wt-R : ∀ {m} (BL BR : BindGroup)
  {Γ₁ : Ctx (sum BL)} {Γ₂ : Ctx (sum BR)} {Γ : Ctx m}
  {s'' : 𝕊 0} {p'' : Pol} {restR B₂ᴿ : BindGroup} {qᴿ b₁ᴿ : ℕ}
  {g : Struct m} {𝒫ᴿ : CxPat (sum BL + sum BR + m)}
  {γrᴿ α β : Struct (sum BL + sum BR + m)}
  {xR : 𝔽 (sum BL + sum BR + m)} {U : 𝕋}
  → New s''
  → BindCtx (s'' ; end p'') BR Γ₂
  → LeftPat 𝒫ᴿ
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ; γrᴿ ⊢ K `recv ·¹ (` xR) ∶ U ∣ 𝕀
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ 𝒫ᴿ [ γrᴿ ]𝓅 ≼ α
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ α ∥ β ≼
      ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → BR ≡ zero ∷ restR ++ (qᴿ + suc b₁ᴿ) ∷ B₂ᴿ
  → Fin.toℕ xR ≡ sum BL + (sum (zero ∷ restR) + qᴿ)
  → ⊥
sep-com-¬wt-R {m} BL BR {Γ₁} {Γ₂} {Γ} {s''} {p''} {restR} {B₂ᴿ} {qᴿ} {b₁ᴿ}
            {g} {𝒫ᴿ} {γrᴿ} {α} {β} {xR} {U}
            Nnew C lpᴿ ⊢redexᴿ ≼ᴿ ≼₁ BReq xtoℕ0
  rewrite BReq ■ cong (λ w → zero ∷ restR ++ w ∷ B₂ᴿ) (Nat.+-suc qᴿ b₁ᴿ)
  with bindCtx-inv-cons {B = restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ} (0<len++ restR (suc (qᴿ + b₁ᴿ)) B₂ᴿ) C
... | inj₁ (_ , _ , _ , _ , _ , _ , nil (_ ; ()) , _)
... | inj₂ (_ , C1)
  with descend restR (suc (qᴿ + b₁ᴿ)) B₂ᴿ (inj₁ (base-acq Nnew)) C1
... | Γh , sh , inv-h , C-h , recon = go inv-h
  where
    Δ : Ctx (sum BL + sum (restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ) + m)
    Δ = (Γ₁ ⸴* Γ₂) ⸴* Γ
    qᴿ<hb : qᴿ Nat.< suc (qᴿ + b₁ᴿ)
    qᴿ<hb = Nat.s≤s (Nat.m≤m+n qᴿ b₁ᴿ)
    khandle : 𝔽 (sum (suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ))
    khandle = fromℕ< (Nat.<-≤-trans qᴿ<hb (Nat.m≤m+n (suc (qᴿ + b₁ᴿ)) (sum B₂ᴿ)))
    tkh : Fin.toℕ khandle ≡ qᴿ
    tkh = toℕ-fromℕ< _
    xlt : sum restR + qᴿ Nat.< sum (restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ)
    xlt = subst (sum restR + qᴿ Nat.<_) (sym (sum-++ restR (suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ)))
            (Nat.+-monoʳ-< (sum restR) (Nat.<-≤-trans qᴿ<hb (Nat.m≤m+n (suc (qᴿ + b₁ᴿ)) (sum B₂ᴿ))))
    xpos : 𝔽 (sum (restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ))
    xpos = fromℕ< xlt
    txpos : Fin.toℕ xpos ≡ sum restR + qᴿ
    txpos = toℕ-fromℕ< xlt
    xposG≡xR : (sum BL ↑ʳ xpos) ↑ˡ m ≡ xR
    xposG≡xR = toℕ-injective
      (toℕ-↑ˡ (sum BL ↑ʳ xpos) m ■ toℕ-↑ʳ (sum BL) xpos ■ cong (sum BL +_) txpos ■ sym xtoℕ0)
    lookupΔ : lookup Δ ((sum BL ↑ʳ xpos) ↑ˡ m) ≡ lookup Γ₂ xpos
    lookupΔ = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum BL ↑ʳ xpos) ■ lookup-++ʳ Γ₁ Γ₂ xpos
    Δhandle≃ : ∀ {T} → lookup Δ xR ≃ ⟨ msg ⁇ T ⟩ → lookup Γ₂ xpos ≃ ⟨ msg ⁇ T ⟩
    Δhandle≃ msg≃ = subst (_≃ _) (cong (lookup Δ) (sym xposG≡xR) ■ lookupΔ) msg≃
    reconxk : lookup Γ₂ xpos ≡ lookup Γh khandle
    reconxk = recon xpos khandle (txpos ■ cong (sum restR +_) (sym tkh))
    handle≃ : ∀ {T} → lookup Δ xR ≃ ⟨ msg ⁇ T ⟩ → lookup Γh khandle ≃ ⟨ msg ⁇ T ⟩
    handle≃ msg≃ = subst (_≃ _) reconxk (Δhandle≃ msg≃)
    flt : sum restR Nat.< sum (restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ)
    flt = Nat.≤-<-trans (Nat.m≤m+n (sum restR) qᴿ) xlt
    fpos : 𝔽 (sum (restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ))
    fpos = fromℕ< flt
    tfpos : Fin.toℕ fpos ≡ sum restR
    tfpos = toℕ-fromℕ< flt
    lookupΔf : lookup Δ ((sum BL ↑ʳ fpos) ↑ˡ m) ≡ lookup Γ₂ fpos
    lookupΔf = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum BL ↑ʳ fpos) ■ lookup-++ʳ Γ₁ Γ₂ fpos
    reconf : lookup Γ₂ fpos ≡ lookup Γh 0F
    reconf = recon fpos 0F (tfpos ■ sym (Nat.+-identityʳ (sum restR)))
    comxs : ¬ Mobile (lookup Γh 0F) → qᴿ ≢ 0 → ⊥
    comxs ¬mob0 qᴿ≢0 with recv-handle-≃msg-app ⊢redexᴿ
    ... | T , msg≃ =
      com-xS-min ¬uxR ¬uy lpᴿ ≼ᴿ ≼₁ cnt1 bfr 1≤cR ¬bfr
      where
        BRr : BindGroup
        BRr = zero ∷ restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ
        γ₁ : Struct (sum BL + sum BRr + m)
        γ₁ = (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BRr) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (structBinder BRr 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BRr))
        ¬uxR : ¬ Mobile (lookup Δ xR)
        ¬uxR = recv-¬mobile ⊢redexᴿ
        ¬uy : ¬ Mobile (lookup Δ ((sum BL ↑ʳ fpos) ↑ˡ m))
        ¬uy = subst (λ v → ¬ Mobile v) (sym (lookupΔf ■ reconf)) ¬mob0
        cnt1 = subst (λ v → count v γ₁ ≡ 1) xposG≡xR
                 (count-handle-groupᴿ BL BRr g xpos)
        bfr = subst (λ v → before ((sum BL ↑ʳ fpos) ↑ˡ m) v γ₁) xposG≡xR
                (before-com-binderᴿ-later (zero ∷ restR) (suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ) BL g
                  fpos xpos tfpos txpos qᴿ≢0)
        1≤cR : 1 Nat.≤ count xR γrᴿ
        1≤cR = barevar-arg-count (λ u → ¬uxR (unr⇒mobile u)) ⊢redexᴿ
        ¬bfr : ¬ before ((sum BL ↑ʳ fpos) ↑ˡ m) xR γrᴿ
        ¬bfr = choice-¬before ¬uxR ¬uy ⊢redexᴿ
    go : Inv sh → ⊥
    go (inj₂ nm) with recv-handle-≃msg-app ⊢redexᴿ
    ... | T , msg≃ = bindCtx-noMsg-not-msgᴾ C-h nm (handle≃ msg≃)
    go (inj₁ aia) with recv-handle-≃msg-app ⊢redexᴿ
    ... | T , msg≃
      with extract-blockᴾ aia C-h khandle
             (subst (Nat._< suc (qᴿ + b₁ᴿ)) (sym tkh) qᴿ<hb) (handle≃ msg≃)
    ...   | inj₁ bot = bot
    ...   | inj₂ (¬mob0 , k≢0) = comxs ¬mob0 (λ q0 → k≢0 (tkh ■ q0))
