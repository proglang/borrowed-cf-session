-- | The close-reflect "leading-cons-acq zero-branch" is un-typeable.
--
--   end (close ‼/⁇) TWIN of ComSepImpossible.sep-com-¬wt /
--   ChoiceSep.sep-close-¬wt.  The navigation / block-shape / count-reconciliation
--   core is op-general and imported directly from ComSepImpossible; only the
--   end-headed wrappers (front-end / block-analysis / extract-block) and the
--   handle-≃end extraction are re-derived, using the end-vs-acq head clash
--   (end-headed sessions are never acq-headed, via the atomKind head rigidity of
--   AtomHead — `atomKind≢⇒≄-;ˡ` / `startskind-;⁻` + `≃-startskind`).  The NoEnd
--   subsystem is CloseSepNoEnd (twin of ChoiceSepNoEnd).
module BorrowedCF.Simulation.Backward.CloseSep where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)
open import BorrowedCF.Types.AtomHead using (StartsKind; ≃-startskind; startskind-;⁻; startskind-atom-kind; atomKind≢⇒≄-;ˡ)
open import BorrowedCF.Types.AtomSnoc using (ClosedKind; ¬skips-atom)
open import BorrowedCF.Context using (Ctx; _⸴*_)
open import BorrowedCF.Processes.Typed
  using (BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil; bindCtx-B≢[])
open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_)
open import BorrowedCF.Simulation.Backward.CloseSepNoEnd
open import BorrowedCF.Simulation.Support.CloseVacuityProbe using (NoEnd; noEnd-≃; ¬noEnd-end; ¬mobile-noAcq; NoAcq)
open BorrowedCF.Simulation.Support.CloseVacuityProbe.NoEnd
open import BorrowedCF.Types.ContainsEnd using (≃-hasT; seqʳ)
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
open import BorrowedCF.Simulation.Support.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Support.RevGrindC using (count-handle-groupᴿ; inj-wkˡ; inj-wkʳ)
open import BorrowedCF.Simulation.Backward.ComSepBefore using (before-com-binderᴸ-later; before-structBinder-later)
open import BorrowedCF.Simulation.Support.RevGrindA using (choice-¬before; barevar-arg-count; invApp-fn; invApp-arg)
open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Simulation.Support.ReverseConfine using (fn-end-dom)
open import BorrowedCF.Types using (unr⇒mobile; mobile-≃)
import Data.Sum as Sum
open import BorrowedCF.Simulation.Backward.ComSepImpossible
  using ( AmbInvAcq; mkAIA; step-acq; base-acq; 0<len++
        ; BlockShape; bsEnd; bsRet; split-acqhd
        ; mob-front-whole-end; nha-acq-seq; bad-gen; mobile⇒bounded; skips-fst )

------------------------------------------------------------------------
-- end-vs-acq head rigidity.  A close handle is `end`-typed; an end-headed
-- session (end p ; a-rest) is never acq-headed / ret-headed (distinct leading
-- atoms), via the atomKind head rigidity of AtomHead.  The genuinely new
-- reasoning of the close twin (mirrors ChoiceSep's brn-vs-acq clash).
------------------------------------------------------------------------

end;≄acq; : ∀ {p : Pol} {s₂ s′ : 𝕊 0} → (end p ; s₂) ≄ (acq ; s′)
end;≄acq; = atomKind≢⇒≄-;ˡ Atom.end Atom.acq (λ ())

¬startskind-end; : ∀ {k : AtomKind 0} {p} {a-rest : 𝕊 0}
  → ¬ (k ≡ atomKind (Atom.end {p = p})) → ¬ StartsKind k (end p ; a-rest)
¬startskind-end; ne sk with startskind-;⁻ sk
... | inj₁ (Sk , _) = ¬skips-atom Atom.end Sk
... | inj₂ ske      = ne (sym (startskind-atom-kind Atom.end ske))

front-end-end-⊥ : {a-rest Q : 𝕊 0} {p q : Pol} →
  (end p ; a-rest) ≃ ((acq ; Q) ; end q) → ⊥
front-end-end-⊥ eq = end;≄acq; (≃-trans eq ≃-assoc-;)

front-end-ret-⊥ : {a-rest s₁ y' Q : 𝕊 0} {p : Pol} →
  (end p ; a-rest) ≃ (s₁ ; ret) → (s₁ ; y' ≃ acq ; Q) → ⊥
front-end-ret-⊥ eq s₁y'
  with startskind-;⁻ (≃-startskind ClosedKind.acq (≃-sym s₁y')
                        (StartsKind.▸ (StartsKind.here Atom.acq refl)))
... | inj₂ sk-s₁ =
      ¬startskind-end; (λ ()) (≃-startskind ClosedKind.acq (≃-sym eq) (StartsKind.▸ sk-s₁))
... | inj₁ (Sk-s₁ , _) =
      ¬startskind-end; (λ ()) (≃-startskind ClosedKind.ret
        (≃-sym (≃-trans eq (≃-skipsˡ Sk-s₁))) (StartsKind.here Atom.ret refl))

front-end-shape-⊥ : {a a-rest SB : 𝕊 0} {p : Pol} →
  a ≃ end p → a ; a-rest ≃ SB → BlockShape SB → ⊥
front-end-shape-⊥ a≃end aeq (bsEnd nhQ eq) =
  front-end-end-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃end) ≃-refl) aeq) eq)
front-end-shape-⊥ a≃end aeq (bsRet nhQ split eq) with split-acqhd split
... | y' , Q' , s₁y' =
      front-end-ret-⊥ (≃-trans (≃-trans (≃-; (≃-sym a≃end) ≃-refl) aeq) eq) s₁y'

------------------------------------------------------------------------
-- A Mobile (Bounded) front leaves only NoEnd behind it.  Twin of
-- mob⇒noMsg-ar (proof-identical mod NoMsg → NoEnd).
------------------------------------------------------------------------

skips⇒noEnd : {s : 𝕊 0} → Skips s → NoEnd s
skips⇒noEnd Sk = noEnd-≃ (skips⇒skip≃ Sk) skip

mob⇒noEnd-ar : {a a-rest SB : 𝕊 0} → Mobile ⟨ a ⟩ → BlockShape SB → a ; a-rest ≃ SB → NoEnd a-rest
mob⇒noEnd-ar mob (bsEnd nhQ eq) aeq =
  skips⇒noEnd (mob-front-whole-end mob (nha-acq-seq nhQ) (≃-trans aeq eq))
mob⇒noEnd-ar {a-rest = a-rest} mob (bsRet {s₁} {s₂} {Q} nhQ split eq) aeq
  with atom-;-unsnoc ret (≃-trans aeq eq)
... | inj₁ Sk = skips⇒noEnd Sk
... | inj₂ (y' , ay' , y'ret)
  with atom-;-unsnoc end (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; ay' ≃-refl) split))
...   | inj₁ Sky's₂ = noEnd-≃ (≃-sym arest≃ret) ret
        where
          Sky' : Skips y'
          Sky' = skips-fst Sky's₂
          arest≃ret : a-rest ≃ ret
          arest≃ret = ≃-trans (≃-sym y'ret)
                        (≃-trans (≃-; (≃-sym (skips⇒skip≃ Sky')) ≃-refl) ≃-skipˡ)
...   | inj₂ (y'' , ay'' , _) = ⊥-elim (bad-gen (mobile⇒bounded mob) (nha-acq-seq nhQ) ay'')

bindCtx′-noEnd-not-end : ∀ {w} {Γ : Ctx w} {ar} {i : 𝔽 w} {p} →
  BindCtx′ ar Γ → NoEnd ar → lookup Γ i ≃ ⟨ end p ⟩ → ⊥
bindCtx′-noEnd-not-end {i = i} bt nm eq with bindCtx′-lookup-NoEnd bt nm i
... | s' , ej , NEs' =
      ¬noEnd-end (noEnd-≃ (≃-⟨⟩⁻¹ (≃-trans (≃-reflexive (sym ej)) eq)) NEs')

------------------------------------------------------------------------
-- Navigation invariant, NoEnd flavour.  Twin of ComSepImpossible's Inv /
-- descend (whose degraded branch carries NoMsg); here the degraded branch
-- carries NoEnd.  The AmbInvAcq half is op-general and reused directly.
------------------------------------------------------------------------

InvE : 𝕊 0 → Set
InvE s = AmbInvAcq s ⊎ NoEnd s

noEnd-acq-seq : {s : 𝕊 0} → NoEnd s → NoEnd (acq ; s)
noEnd-acq-seq nm = noEnd-acq ; nm

inv-step-acqE : ∀ {s} → InvE s → InvE (acq ; s)
inv-step-acqE (inj₁ aia) = inj₁ (step-acq aia)
inv-step-acqE (inj₂ nm)  = inj₂ (noEnd-acq-seq nm)

inv-step-retacqE : ∀ {s s₁ s₂} → InvE s → s₁ ; s₂ ≃ s → InvE (acq ; s₂)
inv-step-retacqE (inj₁ (mkAIA {Q} {pol} nhQ eq)) split
  with atom-;-unsnoc end (≃-trans split eq)
... | inj₁ Sk = inj₂ (noEnd-acq-seq (skips⇒noEnd Sk))
... | inj₂ (y' , s₁y' , y'end) =
      inj₁ (mkAIA {Q = y'} {pol = pol}
             (λ h → nha-acq-seq nhQ (≃-hasT s₁y' (seqʳ h)))
             (≃-trans (≃-; ≃-refl (≃-sym y'end)) (≃-sym ≃-assoc-;)))
inv-step-retacqE (inj₂ nm) split = inj₂ (noEnd-acq-seq (noEnd-;-snd (noEnd-≃ (≃-sym split) nm)))

descendE : ∀ {s} (B₁ : BindGroup) (hb : ℕ) (B₂ : BindGroup)
    {Γ : Ctx (sum (B₁ ++ hb ∷ B₂))} → InvE s
  → BindCtx s (B₁ ++ hb ∷ B₂) Γ
  → Σ[ Γh ∈ Ctx (sum (hb ∷ B₂)) ] Σ[ sh ∈ 𝕊 0 ]
      InvE sh × BindCtx sh (hb ∷ B₂) Γh
      × (∀ (p : 𝔽 (sum (B₁ ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
          → Fin.toℕ p ≡ sum B₁ + Fin.toℕ k → lookup Γ p ≡ lookup Γh k)
descendE {s} [] hb B₂ {Γ} inv C =
  Γ , s , inv , C , λ p k tp → cong (lookup Γ) (toℕ-injective tp)
descendE (b ∷ B₁) hb B₂ {Γ} inv C
  with bindCtx-inv-cons {B = B₁ ++ hb ∷ B₂} (0<len++ B₁ hb B₂) C
... | inj₂ (refl , C') = descendE B₁ hb B₂ (inv-step-acqE inv) C'
... | inj₁ (s₁ , s₂ , Γ₁' , Γ₂' , split , refl , _ , C') =
      let Γh , sh , inv-h , C-h , rec = descendE B₁ hb B₂ (inv-step-retacqE inv split) C'
      in Γh , sh , inv-h , C-h , recon Γh rec
  where
    recon : (Γh : Ctx (sum (hb ∷ B₂)))
      → (∀ (p' : 𝔽 (sum (B₁ ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
          → Fin.toℕ p' ≡ sum B₁ + Fin.toℕ k → lookup Γ₂' p' ≡ lookup Γh k)
      → (p : 𝔽 (sum ((b ∷ B₁) ++ hb ∷ B₂))) (k : 𝔽 (sum (hb ∷ B₂)))
      → Fin.toℕ p ≡ sum (b ∷ B₁) + Fin.toℕ k → lookup (Γ₁' ⸴* Γ₂') p ≡ lookup Γh k
    recon Γh rec p k tp with splitAt b p in seq
    ... | inj₁ j = ⊥-elim (Nat.<-irrefl refl (Nat.≤-<-trans b≤p p<b))
      where
        p≡j : j ↑ˡ _ ≡ p
        p≡j = splitAt⁻¹-↑ˡ seq
        tj : Fin.toℕ p ≡ Fin.toℕ j
        tj = sym (cong Fin.toℕ p≡j) ■ toℕ-↑ˡ j _
        p<b : Fin.toℕ p Nat.< b
        p<b = subst (Nat._< b) (sym tj) (toℕ<n j)
        b≤p : b Nat.≤ Fin.toℕ p
        b≤p = subst (b Nat.≤_) (sym tp)
                (Nat.≤-trans (Nat.m≤m+n b (sum B₁ + Fin.toℕ k))
                  (Nat.≤-reflexive (sym (Nat.+-assoc b (sum B₁) (Fin.toℕ k)))))
    ... | inj₂ p'' =
          cong (lookup (Γ₁' ⸴* Γ₂')) (sym (splitAt⁻¹-↑ʳ seq))
            ■ lookup-++ʳ Γ₁' Γ₂' p'' ■ rec p'' k tp''
      where
        p≡ : b ↑ʳ p'' ≡ p
        p≡ = splitAt⁻¹-↑ʳ seq
        tp'' : Fin.toℕ p'' ≡ sum B₁ + Fin.toℕ k
        tp'' = Nat.+-cancelˡ-≡ b _ _
                 (sym (toℕ-↑ʳ b p'') ■ cong Fin.toℕ p≡ ■ tp ■ Nat.+-assoc b (sum B₁) (Fin.toℕ k))

------------------------------------------------------------------------
-- Block analysis.  Polarity-general (abstract p) — used for both the close
-- (‼) and close (⁇) handle.
------------------------------------------------------------------------

block-analysis-end : ∀ {w'} {SB a a-rest : 𝕊 0} {ΓBt : Ctx w'} {p : Pol} →
  a ; a-rest ≃ SB → BindCtx′ a-rest ΓBt → BlockShape SB →
  (h : 𝔽 (suc w')) → lookup (⟨ a ⟩ ∷ ΓBt) h ≃ ⟨ end p ⟩ →
  ⊥ ⊎ (¬ Mobile ⟨ a ⟩ × Fin.toℕ h ≢ 0)
block-analysis-end aeq bc-tail bs 0F hend =
  inj₁ (front-end-shape-⊥ (≃-⟨⟩⁻¹ hend) aeq bs)
block-analysis-end aeq bc-tail bs (suc h′) hend = inj₂ (¬mob-a , λ ())
  where
    ¬mob-a : ¬ Mobile ⟨ _ ⟩
    ¬mob-a mob = bindCtx′-noEnd-not-end bc-tail (mob⇒noEnd-ar mob bs aeq) hend

extract-block-end : ∀ {sh : 𝕊 0} {W'} {B₂ : BindGroup} {Γh : Ctx (suc W' + sum B₂)} {p : Pol}
  → AmbInvAcq sh → BindCtx sh (suc W' ∷ B₂) Γh
  → (k : 𝔽 (suc W' + sum B₂)) → Fin.toℕ k Nat.< suc W' → lookup Γh k ≃ ⟨ end p ⟩
  → ⊥ ⊎ (¬ Mobile (lookup Γh 0F) × Fin.toℕ k ≢ 0)
extract-block-end aia (last (cons a ar ¬sk aeq bt)) k k<sW' hend =
  block-analysis-end aeq bt (bsEnd (AmbInvAcq.nhQ aia) (AmbInvAcq.eq aia)) k hend
extract-block-end {W' = W'} {B₂ = B₂} aia
  (cons-ret/acq s₁ {Γ₁ = Γ1} {Γ₂ = Γ2} split (cons a ar ¬sk aeq bt) rest) k k<sW' hend =
  Sum.map (λ z → z) (λ (¬m , k₁≢0) → ¬m , (λ e → k₁≢0 (tk₁ ■ e)))
    (block-analysis-end aeq bt
       (bsRet (AmbInvAcq.nhQ aia) (≃-trans split (AmbInvAcq.eq aia)) ≃-refl)
       k₁ hend₁)
  where
    k₁ : 𝔽 (suc W')
    k₁ = fromℕ< k<sW'
    tk₁ : Fin.toℕ k₁ ≡ Fin.toℕ k
    tk₁ = toℕ-fromℕ< k<sW'
    k≡ : k ≡ k₁ ↑ˡ sum B₂
    k≡ = toℕ-injective (sym (toℕ-↑ˡ k₁ (sum B₂) ■ tk₁))
    hend₁ : lookup Γ1 k₁ ≃ ⟨ end _ ⟩
    hend₁ = subst (_≃ _)
             (cong (lookup (Γ1 ⸴* Γ2)) k≡ ■ lookup-++ˡ Γ1 Γ2 k₁) hend

------------------------------------------------------------------------
-- close-handle extraction.  The channel of a well-typed close redex is
-- `end`-typed, hence ¬ Mobile.
------------------------------------------------------------------------

close-handle-L : ∀ {N} {Γ : Ctx N} {γ : Struct N} {x : 𝔽 N} {U ϵ}
  → Γ ; γ ⊢ K (`end ‼) ·¹ (` x) ∶ U ∣ ϵ
  → lookup Γ x ≃ ⟨ end ‼ ⟩
close-handle-L ⊢redex with inv-· ⊢redex
... | _ , _ , _ , _ , _ , _ , _ , invapp with invApp-fn invapp | invApp-arg invapp
... | _ , ⊢fn | _ , ⊢arg = ≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))

close-handle-R : ∀ {N} {Γ : Ctx N} {γ : Struct N} {x : 𝔽 N} {U ϵ}
  → Γ ; γ ⊢ K (`end ⁇) ·¹ (` x) ∶ U ∣ ϵ
  → lookup Γ x ≃ ⟨ end ⁇ ⟩
close-handle-R ⊢redex with inv-· ⊢redex
... | _ , _ , _ , _ , _ , _ , _ , invapp with invApp-fn invapp | invApp-arg invapp
... | _ , ⊢fn | _ , ⊢arg = ≃-trans (arg-type ⊢arg) (≃-sym (fn-end-dom ⊢fn))

close-¬mobile-L : ∀ {N} {Γ : Ctx N} {γ : Struct N} {x : 𝔽 N} {U ϵ}
  → Γ ; γ ⊢ K (`end ‼) ·¹ (` x) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ x)
close-¬mobile-L ⊢redex mob = ¬mobile-noAcq NoAcq.end (mobile-≃ (close-handle-L ⊢redex) mob)

close-¬mobile-R : ∀ {N} {Γ : Ctx N} {γ : Struct N} {x : 𝔽 N} {U ϵ}
  → Γ ; γ ⊢ K (`end ⁇) ·¹ (` x) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ x)
close-¬mobile-R ⊢redex mob = ¬mobile-noAcq NoAcq.end (mobile-≃ (close-handle-R ⊢redex) mob)

------------------------------------------------------------------------
-- before-com-binderᴿ-later : the RIGHT-group before-order lemma (verbatim
-- op-general copy of ComSepImpossibleR's).
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
-- The exports.
------------------------------------------------------------------------

sep-close-¬wt : ∀ {m} (BL BR : BindGroup)
  {Γ₁ : Ctx (sum BL)} {Γ₂ : Ctx (sum BR)} {Γ : Ctx m}
  {s' : 𝕊 0} {p' : Pol} {rest B₂ˢ : BindGroup} {qˢ b₁ˢ : ℕ}
  {g : Struct m} {𝒫ˢ : CxPat (sum BL + sum BR + m)}
  {γrˢ α β : Struct (sum BL + sum BR + m)}
  {xS : 𝔽 (sum BL + sum BR + m)} {U : 𝕋}
  → New s'
  → BindCtx (s' ; end p') BL Γ₁
  → LeftPat 𝒫ˢ
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ; γrˢ ⊢ K (`end ‼) ·¹ (` xS) ∶ U ∣ 𝕀
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ 𝒫ˢ [ γrˢ ]𝓅 ≼ α
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ α ∥ β ≼
      ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → BL ≡ zero ∷ rest ++ (qˢ + suc b₁ˢ) ∷ B₂ˢ
  → Fin.toℕ xS ≡ sum (zero ∷ rest) + qˢ
  → ⊥
sep-close-¬wt {m} BL BR {Γ₁} {Γ₂} {Γ} {s'} {p'} {rest} {B₂ˢ} {qˢ} {b₁ˢ}
            {g} {𝒫ˢ} {γrˢ} {α} {β} {xS} {U}
            Nnew C lpˢ ⊢redexˢ ≼ˢ ≼₁ BLeq xtoℕ0
  rewrite BLeq ■ cong (λ w → zero ∷ rest ++ w ∷ B₂ˢ) (Nat.+-suc qˢ b₁ˢ)
  with bindCtx-inv-cons {B = rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ} (0<len++ rest (suc (qˢ + b₁ˢ)) B₂ˢ) C
... | inj₁ (_ , _ , _ , _ , _ , _ , nil (_ ; ()) , _)
... | inj₂ (_ , C1)
  with descendE rest (suc (qˢ + b₁ˢ)) B₂ˢ (inj₁ (base-acq Nnew)) C1
... | Γh , sh , inv-h , C-h , recon = go inv-h
  where
    Δ : Ctx (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ) + sum BR + m)
    Δ = (Γ₁ ⸴* Γ₂) ⸴* Γ
    qˢ<hb : qˢ Nat.< suc (qˢ + b₁ˢ)
    qˢ<hb = Nat.s≤s (Nat.m≤m+n qˢ b₁ˢ)
    khandle : 𝔽 (sum (suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    khandle = fromℕ< (Nat.<-≤-trans qˢ<hb (Nat.m≤m+n (suc (qˢ + b₁ˢ)) (sum B₂ˢ)))
    tkh : Fin.toℕ khandle ≡ qˢ
    tkh = toℕ-fromℕ< _
    xlt : sum rest + qˢ Nat.< sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ)
    xlt = subst (sum rest + qˢ Nat.<_) (sym (sum-++ rest (suc (qˢ + b₁ˢ) ∷ B₂ˢ)))
            (Nat.+-monoʳ-< (sum rest) (Nat.<-≤-trans qˢ<hb (Nat.m≤m+n (suc (qˢ + b₁ˢ)) (sum B₂ˢ))))
    xpos : 𝔽 (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    xpos = fromℕ< xlt
    txpos : Fin.toℕ xpos ≡ sum rest + qˢ
    txpos = toℕ-fromℕ< xlt
    xposG≡xS : (xpos ↑ˡ sum BR) ↑ˡ m ≡ xS
    xposG≡xS = toℕ-injective
      (toℕ-↑ˡ (xpos ↑ˡ sum BR) m ■ toℕ-↑ˡ xpos (sum BR) ■ txpos ■ sym xtoℕ0)
    lookupΔ : lookup Δ ((xpos ↑ˡ sum BR) ↑ˡ m) ≡ lookup Γ₁ xpos
    lookupΔ = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (xpos ↑ˡ sum BR) ■ lookup-++ˡ Γ₁ Γ₂ xpos
    Δhandle≃ : ∀ {p} → lookup Δ xS ≃ ⟨ end p ⟩ → lookup Γ₁ xpos ≃ ⟨ end p ⟩
    Δhandle≃ e≃ = subst (_≃ _) (cong (lookup Δ) (sym xposG≡xS) ■ lookupΔ) e≃
    reconxk : lookup Γ₁ xpos ≡ lookup Γh khandle
    reconxk = recon xpos khandle (txpos ■ cong (sum rest +_) (sym tkh))
    handle≃ : ∀ {p} → lookup Δ xS ≃ ⟨ end p ⟩ → lookup Γh khandle ≃ ⟨ end p ⟩
    handle≃ e≃ = subst (_≃ _) reconxk (Δhandle≃ e≃)
    flt : sum rest Nat.< sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ)
    flt = Nat.≤-<-trans (Nat.m≤m+n (sum rest) qˢ) xlt
    fpos : 𝔽 (sum (rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ))
    fpos = fromℕ< flt
    tfpos : Fin.toℕ fpos ≡ sum rest
    tfpos = toℕ-fromℕ< flt
    lookupΔf : lookup Δ ((fpos ↑ˡ sum BR) ↑ˡ m) ≡ lookup Γ₁ fpos
    lookupΔf = lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (fpos ↑ˡ sum BR) ■ lookup-++ˡ Γ₁ Γ₂ fpos
    reconf : lookup Γ₁ fpos ≡ lookup Γh 0F
    reconf = recon fpos 0F (tfpos ■ sym (Nat.+-identityʳ (sum rest)))
    comxs : ¬ Mobile (lookup Γh 0F) → qˢ ≢ 0 → ⊥
    comxs ¬mob0 qˢ≢0 =
      com-xS-min ¬uxS ¬uy lpˢ ≼ˢ ≼₁ cnt1 bfr 1≤cS ¬bfr
      where
        BLr : BindGroup
        BLr = zero ∷ rest ++ suc (qˢ + b₁ˢ) ∷ B₂ˢ
        γ₁ : Struct (sum BLr + sum BR + m)
        γ₁ = (structBinder BLr 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BLr) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BLr + sum BR))
        ¬uxS : ¬ Mobile (lookup Δ xS)
        ¬uxS = close-¬mobile-L ⊢redexˢ
        ¬uy : ¬ Mobile (lookup Δ ((fpos ↑ˡ sum BR) ↑ˡ m))
        ¬uy = subst (λ v → ¬ Mobile v) (sym (lookupΔf ■ reconf)) ¬mob0
        cnt1 = subst (λ v → count v γ₁ ≡ 1) xposG≡xS
                 (count-handle-groupᴸ BLr BR g xpos)
        bfr = subst (λ v → before ((fpos ↑ˡ sum BR) ↑ˡ m) v γ₁) xposG≡xS
                (before-com-binderᴸ-later (zero ∷ rest) (suc (qˢ + b₁ˢ) ∷ B₂ˢ) BR g
                  fpos xpos tfpos txpos qˢ≢0)
        1≤cS : 1 Nat.≤ count xS γrˢ
        1≤cS = barevar-arg-count (λ u → ¬uxS (unr⇒mobile u)) ⊢redexˢ
        ¬bfr : ¬ before ((fpos ↑ˡ sum BR) ↑ˡ m) xS γrˢ
        ¬bfr = choice-¬before ¬uxS ¬uy ⊢redexˢ
    go : InvE sh → ⊥
    go (inj₂ nm) = bindCtx-noEnd-not-end C-h nm (handle≃ (close-handle-L ⊢redexˢ))
    go (inj₁ aia)
      with extract-block-end aia C-h khandle
             (subst (Nat._< suc (qˢ + b₁ˢ)) (sym tkh) qˢ<hb) (handle≃ (close-handle-L ⊢redexˢ))
    ...   | inj₁ bot = bot
    ...   | inj₂ (¬mob0 , k≢0) = comxs ¬mob0 (λ q0 → k≢0 (tkh ■ q0))

sep-close-¬wt-R : ∀ {m} (BL BR : BindGroup)
  {Γ₁ : Ctx (sum BL)} {Γ₂ : Ctx (sum BR)} {Γ : Ctx m}
  {s'' : 𝕊 0} {p'' : Pol} {restR B₂ᴿ : BindGroup} {qᴿ b₁ᴿ : ℕ}
  {g : Struct m} {𝒫ᴿ : CxPat (sum BL + sum BR + m)}
  {γrᴿ α β : Struct (sum BL + sum BR + m)}
  {xR : 𝔽 (sum BL + sum BR + m)} {U : 𝕋}
  → New s''
  → BindCtx (s'' ; end p'') BR Γ₂
  → LeftPat 𝒫ᴿ
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ; γrᴿ ⊢ K (`end ⁇) ·¹ (` xR) ∶ U ∣ 𝕀
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ 𝒫ᴿ [ γrᴿ ]𝓅 ≼ α
  → (Γ₁ ⸴* Γ₂) ⸴* Γ ∶ α ∥ β ≼
      ( (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
      ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BR)) )
  → BR ≡ zero ∷ restR ++ (qᴿ + suc b₁ᴿ) ∷ B₂ᴿ
  → Fin.toℕ xR ≡ sum BL + (sum (zero ∷ restR) + qᴿ)
  → ⊥
sep-close-¬wt-R {m} BL BR {Γ₁} {Γ₂} {Γ} {s''} {p''} {restR} {B₂ᴿ} {qᴿ} {b₁ᴿ}
            {g} {𝒫ᴿ} {γrᴿ} {α} {β} {xR} {U}
            Nnew C lpᴿ ⊢redexᴿ ≼ᴿ ≼₁ BReq xtoℕ0
  rewrite BReq ■ cong (λ w → zero ∷ restR ++ w ∷ B₂ᴿ) (Nat.+-suc qᴿ b₁ᴿ)
  with bindCtx-inv-cons {B = restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ} (0<len++ restR (suc (qᴿ + b₁ᴿ)) B₂ᴿ) C
... | inj₁ (_ , _ , _ , _ , _ , _ , nil (_ ; ()) , _)
... | inj₂ (_ , C1)
  with descendE restR (suc (qᴿ + b₁ᴿ)) B₂ᴿ (inj₁ (base-acq Nnew)) C1
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
    Δhandle≃ : ∀ {p} → lookup Δ xR ≃ ⟨ end p ⟩ → lookup Γ₂ xpos ≃ ⟨ end p ⟩
    Δhandle≃ e≃ = subst (_≃ _) (cong (lookup Δ) (sym xposG≡xR) ■ lookupΔ) e≃
    reconxk : lookup Γ₂ xpos ≡ lookup Γh khandle
    reconxk = recon xpos khandle (txpos ■ cong (sum restR +_) (sym tkh))
    handle≃ : ∀ {p} → lookup Δ xR ≃ ⟨ end p ⟩ → lookup Γh khandle ≃ ⟨ end p ⟩
    handle≃ e≃ = subst (_≃ _) reconxk (Δhandle≃ e≃)
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
    comxs ¬mob0 qᴿ≢0 =
      com-xS-min ¬uxR ¬uy lpᴿ ≼ᴿ ≼₁ cnt1 bfr 1≤cR ¬bfr
      where
        BRr : BindGroup
        BRr = zero ∷ restR ++ suc (qᴿ + b₁ᴿ) ∷ B₂ᴿ
        γ₁ : Struct (sum BL + sum BRr + m)
        γ₁ = (structBinder BL 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BRr) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (structBinder BRr 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum BL) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
           ∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum BL + sum BRr))
        ¬uxR : ¬ Mobile (lookup Δ xR)
        ¬uxR = close-¬mobile-R ⊢redexᴿ
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
    go : InvE sh → ⊥
    go (inj₂ nm) = bindCtx-noEnd-not-end C-h nm (handle≃ (close-handle-R ⊢redexᴿ))
    go (inj₁ aia)
      with extract-block-end aia C-h khandle
             (subst (Nat._< suc (qᴿ + b₁ᴿ)) (sym tkh) qᴿ<hb) (handle≃ (close-handle-R ⊢redexᴿ))
    ...   | inj₁ bot = bot
    ...   | inj₂ (¬mob0 , k≢0) = comxs ¬mob0 (λ q0 → k≢0 (tkh ■ q0))
