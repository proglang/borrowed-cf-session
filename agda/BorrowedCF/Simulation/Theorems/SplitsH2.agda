module BorrowedCF.Simulation.Theorems.SplitsH2 where
open import BorrowedCF.Terms using (module SplitRenamings)

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.SplitConfine using (lsplit-confine; rsplit-confine)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ
        ; VChan; chanTriple-V; Value-subst; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)

open import BorrowedCF.Simulation.Theorems.SplitsLQ public

subst-∥f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (P Q : U.Proc (h x)) →
           subst (λ z → U.Proc (h z)) eq (P U.∥ Q)
           ≡ subst (λ z → U.Proc (h z)) eq P U.∥ subst (λ z → U.Proc (h z)) eq Q
subst-∥f h refl P Q = refl

subst-⟪⟫f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (e : Tm (h x)) →
            subst (λ z → U.Proc (h z)) eq U.⟪ e ⟫ ≡ U.⟪ subst (λ z → Tm (h z)) eq e ⟫
subst-⟪⟫f h refl e = refl

subst-frame-plug : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (F : Frame* (h x)) (t : Tm (h x)) →
                   subst (λ z → Tm (h z)) eq (F [ t ]*)
                   ≡ subst (λ z → Frame* (h z)) eq F [ subst (λ z → Tm (h z)) eq t ]*
subst-frame-plug h refl F t = refl

subst-⊗f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (a b : Tm (h x)) →
           subst (λ z → Tm (h z)) eq (a ⊗ b)
           ≡ subst (λ z → Tm (h z)) eq a ⊗ subst (λ z → Tm (h z)) eq b
subst-⊗f h refl a b = refl

transport-⋯t : {kk kk′ : ℕ} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′)
               (t : Tm (fg kk)) →
               subst (λ j → Tm (gg j)) eq (t ⋯ ρ kk)
               ≡ (subst (λ j → Tm (fg j)) eq t) ⋯ ρ kk′
transport-⋯t fg gg ρ refl t = refl

ss-U : ∀ {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) {t : U.Proc x} →
       subst U.Proc q (subst U.Proc p t) ≡ subst U.Proc (p ■ q) t
ss-U refl refl = refl

-- Bφ on the grown bind group equals Bφ on the ungrown one (the flag-list shapes
-- match; only the domain scope shifts by syncs-lwk).  Induction on B₁.
Bφ-lwk : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
         (Y : U.Proc (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + a)) →
         Bφ (B₁ ++ (q + suc b₁) ∷ B₂) Y
         ≡ Bφ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) (subst U.Proc (cong (_+ a) (syncs-lwkq B₁)) Y)
Bφ-lwk []        {q} {b₁} {[]}      Y = refl
Bφ-lwk []        {q} {b₁} {b' ∷ B'} Y =
  cong (λ f → U.φ f _)
    (cong ϕ[_] (Nat.+-suc q b₁) ■ sym (cong ϕ[_] (Nat.+-suc q (suc b₁))))
Bφ-lwk (a ∷ [])      {q} {b₁} {B₂} {aa} Y =
  cong (U.φ ϕ[ a ])
    ( Bφ-lwk [] {q} {b₁} {B₂} (subst U.Proc (sym (+-suc (syncs ([] ++ (q + suc b₁) ∷ B₂)) aa)) Y)
    ■ cong (Bφ ([] ++ (q + suc (suc b₁)) ∷ B₂)) bodyeq )
  where
    aa-eq = cong (_+ aa) (syncs-lwkq (a ∷ []) {q} {b₁} {B₂})
    bodyeq : subst U.Proc (cong (_+ suc aa) (syncs-lwkq [] {q} {b₁} {B₂}))
               (subst U.Proc (sym (+-suc (syncs ([] ++ (q + suc b₁) ∷ B₂)) aa)) Y)
             ≡ subst U.Proc (sym (+-suc (syncs ([] ++ (q + suc (suc b₁)) ∷ B₂)) aa))
                 (subst U.Proc aa-eq Y)
    bodyeq = ss-U (sym (+-suc (syncs ([] ++ (q + suc b₁) ∷ B₂)) aa)) (cong (_+ suc aa) (syncs-lwkq [] {q} {b₁} {B₂})) {t = Y}
           ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
           ■ sym (ss-U aa-eq (sym (+-suc (syncs ([] ++ (q + suc (suc b₁)) ∷ B₂)) aa)) {t = Y})
Bφ-lwk (a ∷ d ∷ B₁″) {q} {b₁} {B₂} {aa} Y =
  cong (U.φ ϕ[ a ])
    ( Bφ-lwk (d ∷ B₁″) {q} {b₁} {B₂} (subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) aa)) Y)
    ■ cong (Bφ ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) bodyeq )
  where
    aa-eq = cong (_+ aa) (syncs-lwkq (a ∷ d ∷ B₁″) {q} {b₁} {B₂})
    bodyeq : subst U.Proc (cong (_+ suc aa) (syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂}))
               (subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) aa)) Y)
             ≡ subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) aa))
                 (subst U.Proc aa-eq Y)
    bodyeq = ss-U (sym (+-suc (syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)) aa)) (cong (_+ suc aa) (syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂})) {t = Y}
           ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
           ■ sym (ss-U aa-eq (sym (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) aa)) {t = Y})

subst-wkB : ∀ (sB : ℕ) {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
            subst (λ j → Tm (sB + (j + N))) eq (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
            ≡ (subst (λ j → Tm (j + N)) eq t) ⋯ weaken* ⦃ Kᵣ ⦄ sB
subst-wkB sB refl t = refl

subst-cong+ : ∀ {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
              subst Tm (cong (_+ N) eq) t ≡ subst (λ j → Tm (j + N)) eq t
subst-cong+ refl t = refl

-- leafσ on the grown bind group agrees with the transported ungrown leafσ away
-- from the consumed handle atk (q ↑ʳ 0F) (lwk just inserts the new data slot).
leafσ-lwk-id : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ B : BindGroup) (q b₁ : ℕ)
               (i : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
               i ≢ SplitRenamings.atk B₁ B₂ B {q + suc b₁} {m} (q ↑ʳ 0F) →
               subst (λ j → Tm (syncs B + (j + (2 + n)))) (syncs-lwkq B₁)
                 (leafσ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i)
               ≡ leafσ σ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} i)
leafσ-lwk-id {m} {n} σ B₁ B₂ B q b₁ i i≢
  with Fin.splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) i in seqo
... | inj₂ u
  rewrite leafσ-tail {n = n} σ (B₁ ++ (q + suc b₁) ∷ B₂) B i u seqo
        | leafσ-tail {n = n} σ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} i) u
            (cong (Fin.splitAt (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B))
               (cong (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo) ■ P3q B₁ B₂ B {q} {b₁} {m} u)
            ■ Fin.splitAt-↑ʳ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) m u) = σ-coh
  where
    sA  = syncs (B₁ ++ (q + suc b₁) ∷ B₂)
    sA′ = syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
    sB  = syncs B
    ieq : i ≡ (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) ↑ʳ u
    ieq = sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i)
        ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo
    σfn : (j : ℕ) → Tm (sB + (j + (2 + n)))
    σfn j = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ j ⋯ weaken* ⦃ Kᵣ ⦄ sB
    σ-coh : subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwkq B₁) (σfn sA) ≡ σfn sA′
    σ-coh = cohh (syncs-lwkq B₁)
      where cohh : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (sB + (j + (2 + n)))) eq (σfn sA) ≡ σfn s′
            cohh refl = refl
... | inj₁ db with Fin.splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) db in seqi
...   | inj₂ w
  rewrite leafσ-B₁ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i db w seqo seqi
        | leafσ-B₁ σ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} i) (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w) w
            (cong (Fin.splitAt (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B)) (cong (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ P2q B₁ B₂ B {q} {b₁} {m} w)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) ↑ʳ w) m)
            (Fin.splitAt-↑ʳ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) (sum B) w) = canonB-coh
  where
    sA  = syncs (B₁ ++ (q + suc b₁) ∷ B₂)
    sA′ = syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂)
    sB  = syncs B
    cfn : (j : ℕ) → Tm (sB + (j + (2 + n)))
    cfn j = canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ j 1F , K `unit) w
    canonB-coh : subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwkq B₁) (cfn sA) ≡ cfn sA′
    canonB-coh = cohh (syncs-lwkq B₁)
      where cohh : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (sB + (j + (2 + n)))) eq (cfn sA) ≡ cfn s′
            cohh refl = refl
...   | inj₁ d
  rewrite leafσ-A₁ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i db d seqo seqi
        | leafσ-A₁ σ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m} i) (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) (dlwkq B₁ q b₁ B₂ d)
            (cong (Fin.splitAt (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B)) (cong (SplitRenamings.lwk B₁ B₂ B {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ P1q B₁ B₂ B {q} {b₁} {m} d)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + sum B) (dlwkq B₁ q b₁ B₂ d ↑ˡ sum B) m)
            (Fin.splitAt-↑ˡ (sum (B₁ ++ (q + suc (suc b₁)) ∷ B₂)) (dlwkq B₁ q b₁ B₂ d) (sum B)) =
      subst-wkB (syncs B) (syncs-lwkq B₁) (canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) (K `unit , 0F , K `unit) d)
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
        ( sym (subst-cong+ (syncs-lwkq B₁) (canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) (K `unit , 0F , K `unit) d))
        ■ canonₛ-lwkq B₁ (K `unit , 0F , K `unit) q b₁ B₂ d
            (λ d≡ → i≢ ((sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡)) )

substP-∘ : ∀ {kk kk′} (fg : ℕ → ℕ) (e : kk ≡ kk′) (X : U.Proc (fg kk)) →
           subst U.Proc (cong fg e) X ≡ subst (λ j → U.Proc (fg j)) e X
substP-∘ fg refl X = refl

transport-⋯ₚ : ∀ {kk kk′} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′) (X : U.Proc (fg kk)) →
               subst (λ j → U.Proc (gg j)) eq (X U.⋯ₚ ρ kk)
               ≡ (subst (λ j → U.Proc (fg j)) eq X) U.⋯ₚ ρ kk′
transport-⋯ₚ fg gg ρ refl X = refl

-- Grown-handle borrow-1 triple: the SECOND borrow of a grown (width ≥ 2) handle
-- chain, at flat position sum B₁ ↑ʳ 1F.  Mirrors canonₛ-handle (borrow-0) but at
-- index 1F; since the singleton leaf now DISTRIBUTES (Ub[ b+0 ]) the last chain
-- behaves like any Ub head (left slot *, right slot the threaded e₂/` 0F/*).
module _ where
  substTripⱼ : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
               subst Tm eq ((A ⊗ (` jj)) ⊗ C) ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
  substTripⱼ refl A jj C = refl
  toℕ-substᶠ : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
  toℕ-substᶠ refl y = refl
  -- lift a slot-equality (at scope suc N) through the +-suc scope-shuffle that
  -- canonₛ-handle / canonₛ-handle-b1 apply when peeling a B₁ chain (scope N).
  chainT : ∀ {N s s′} (e : s ≡ s′) {X : Tm (s + suc N)} {Y : Tm (s′ + suc N)} →
           subst Tm (cong (_+ suc N) e) X ≡ Y →
           subst Tm (cong (_+ N) (cong suc e)) (subst Tm (+-suc s N) X) ≡ subst Tm (+-suc s′ N) Y
  chainT {N} refl {X} refl = refl

Ub-L-* : ∀ w {N} (e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) → proj₁ (Ub-triple w * e2 c p) ≡ *
Ub-L-* (suc zero)    e2 c zero    = refl
Ub-L-* (suc zero)    e2 c (suc ())
Ub-L-* (suc (suc b)) e2 c zero    = refl
Ub-L-* (suc (suc b)) e2 c (suc x) = Ub-L-* (suc b) e2 c x

Ub-L-pos>0 : ∀ w {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) →
             0 Nat.< Fin.toℕ p → proj₁ (Ub-triple w e1 e2 c p) ≡ *
Ub-L-pos>0 (suc zero)    e1 e2 c zero    ()
Ub-L-pos>0 (suc zero)    e1 e2 c (suc ())
Ub-L-pos>0 (suc (suc b)) e1 e2 c zero    ()
Ub-L-pos>0 (suc (suc b)) e1 e2 c (suc x) lt = Ub-L-* (suc b) e2 c x

Ub-L-pos0 : ∀ w {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) →
            Fin.toℕ p ≡ 0 → proj₁ (Ub-triple w e1 e2 c p) ≡ e1
Ub-L-pos0 (suc zero)    e1 e2 c zero    eq = refl
Ub-L-pos0 (suc zero)    e1 e2 c (suc ())
Ub-L-pos0 (suc (suc b)) e1 e2 c zero    eq = refl
Ub-L-pos0 (suc (suc b)) e1 e2 c (suc x) ()

Ub-R-far : ∀ w {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) →
           suc (Fin.toℕ p) Nat.< w → proj₁ (proj₂ (Ub-triple w e1 e2 c p)) ≡ *
Ub-R-far (suc zero)    e1 e2 c zero    (Nat.s≤s ())
Ub-R-far (suc zero)    e1 e2 c (suc ())
Ub-R-far (suc (suc b)) e1 e2 c zero    lt = refl
Ub-R-far (suc (suc b)) e1 e2 c (suc x) lt = Ub-R-far (suc b) * e2 c x (Nat.s≤s⁻¹ lt)

Ub-R-last : ∀ w {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) →
            suc (Fin.toℕ p) ≡ w → proj₁ (proj₂ (Ub-triple w e1 e2 c p)) ≡ e2
Ub-R-last (suc zero)    e1 e2 c zero    eq = refl
Ub-R-last (suc zero)    e1 e2 c (suc ())
Ub-R-last (suc (suc b)) e1 e2 c zero    ()
Ub-R-last (suc (suc b)) e1 e2 c (suc x) eq = Ub-R-last (suc b) * e2 c x (Nat.suc-injective eq)

canonₛ-head-tripleq-b1 : ∀ (q b₁ : ℕ) (B₂ : BindGroup) {N} (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs ((q + suc (suc b₁)) ∷ B₂) + N) ] Σ[ c ∈ Tm (syncs ((q + suc (suc b₁)) ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs ((q + suc (suc b₁)) ∷ B₂) + N) ]
    (canonₛ ((q + suc (suc b₁)) ∷ B₂) (e1 , x , e2) ((q ↑ʳ 1F) ↑ˡ sum B₂) ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs ((q + suc (suc b₁)) ∷ B₂) + Fin.toℕ x)
canonₛ-head-tripleq-b1 q b₁ [] e1 e2 x
  with Ub-triple ((q + suc (suc b₁)) + 0) e1 e2 x ((q ↑ʳ 1F) ↑ˡ 0)
... | a , e2' , ubeq = a , e2' , x , ubeq , refl
canonₛ-head-tripleq-b1 q b₁ (c′ ∷ B) {N} e1 e2 x
  with Ub-triple (q + suc (suc b₁)) (wk e1) (` 0F) (suc x) (q ↑ʳ 1F)
... | a , e2' , ubeq =
  ( subst Tm (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq , junceq )
  where
    sB = syncs (c′ ∷ B)
    spliteq : splitAt (q + suc (suc b₁)) ((q ↑ʳ 1F) ↑ˡ sum (c′ ∷ B)) ≡ inj₁ (q ↑ʳ 1F)
    spliteq = Fin.splitAt-↑ˡ (q + suc (suc b₁)) (q ↑ʳ 1F) (sum (c′ ∷ B))
    tripeq : canonₛ ((q + suc (suc b₁)) ∷ c′ ∷ B) (e1 , x , e2) ((q ↑ʳ 1F) ↑ˡ sum (c′ ∷ B))
             ≡ (subst Tm (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ q + suc (suc b₁) ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ (c′ ∷ B) (` 0F , suc x , wk e2) ]′ spliteq
               ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) ubeq)
           ■ substTripⱼ (+-suc sB N) (a ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) (e2' ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)

canonₛ-handleq-b1 : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + N) ]
    (canonₛ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂)
        (Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)))
       ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (B₁ ++ (q + suc (suc b₁)) ∷ B₂) + Fin.toℕ x)
canonₛ-handleq-b1 [] {N} e₁ x e₂ q b₁ B₂ =
  proj₁ h , proj₁ (proj₂ h) , proj₁ (proj₂ (proj₂ h))
  , castidx (proj₁ (proj₂ (proj₂ (proj₂ h))))
  , proj₂ (proj₂ (proj₂ (proj₂ h)))
  where
    h = canonₛ-head-tripleq-b1 q b₁ B₂ e₁ e₂ x
    castidx : canonₛ ((q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂) ((q ↑ʳ 1F) ↑ˡ sum B₂)
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h) →
              canonₛ ((q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂)
                (Fin.cast (sym (sum-++ [] ((q + suc (suc b₁)) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)))
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h)
    castidx = subst (λ z → canonₛ ((q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂) z
                            ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h))
                (sym (Fin.toℕ-injective (Fin.toℕ-cast (sym (sum-++ [] ((q + suc (suc b₁)) ∷ B₂))) (sum [] ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂)))))
canonₛ-handleq-b1 (a ∷ []) {N} e₁ x e₂ q b₁ B₂
  with canonₛ-handleq-b1 [] (` 0F) (suc x) (wk e₂) q b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ ([])) ((q + suc (suc b₁)) ∷ B₂))) (sum (a ∷ ([])) ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
    cp′ = Fin.cast (sym (sum-++ ([]) ((q + suc (suc b₁)) ∷ B₂))) (sum ([]) ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a ([]) (q + suc (suc b₁)) B₂ ((q ↑ʳ 1F) ↑ˡ sum B₂))
            ■ Fin.splitAt-↑ʳ a (sum (([]) ++ (q + suc (suc b₁)) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ ([]) ++ (q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ (([]) ++ (q + suc (suc b₁)) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripⱼ (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)
canonₛ-handleq-b1 (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂
  with canonₛ-handleq-b1 (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ (d ∷ B₁″)) ((q + suc (suc b₁)) ∷ B₂))) (sum (a ∷ (d ∷ B₁″)) ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
    cp′ = Fin.cast (sym (sum-++ (d ∷ B₁″) ((q + suc (suc b₁)) ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a (d ∷ B₁″) (q + suc (suc b₁)) B₂ ((q ↑ʳ 1F) ↑ˡ sum B₂))
            ■ Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ (d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripⱼ (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)

-- toℕ of the handle positions
private
  toℕ↑0 : ∀ q {r} → Fin.toℕ (q ↑ʳ (Fin.zero {n = r})) ≡ q
  toℕ↑0 q = Fin.toℕ-↑ʳ q Fin.zero ■ Nat.+-identityʳ q
  toℕ↑1 : ∀ q {r} → Fin.toℕ (q ↑ʳ (Fin.suc (Fin.zero {n = r}))) ≡ suc q
  toℕ↑1 q = Fin.toℕ-↑ʳ q (Fin.suc Fin.zero) ■ Nat.+-comm q 1
  toℕ↑0ˡ : ∀ q {r z} → Fin.toℕ ((q ↑ʳ (Fin.zero {n = r})) ↑ˡ z) ≡ q
  toℕ↑0ˡ q {r} {z} = Fin.toℕ-↑ˡ (q ↑ʳ Fin.zero) z ■ toℕ↑0 q
  toℕ↑1ˡ : ∀ q {r z} → Fin.toℕ ((q ↑ʳ (Fin.suc (Fin.zero {n = r}))) ↑ˡ z) ≡ suc q
  toℕ↑1ˡ q {r} {z} = Fin.toℕ-↑ˡ (q ↑ʳ (Fin.suc Fin.zero)) z ■ toℕ↑1 q

private
  0<n : ∀ {n} → n ≢ 0 → 0 Nat.< n
  0<n {zero}  ne = ⊥-elim (ne refl)
  0<n {suc n} ne = Nat.s≤s Nat.z≤n

-- L slot at equal positions is width-independent.
UbL-grow-gen : ∀ {w w'} {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) (p' : 𝔽 w') →
  Fin.toℕ p ≡ Fin.toℕ p' →
  proj₁ (Ub-triple w e1 e2 c p) ≡ proj₁ (Ub-triple w' e1 e2 c p')
UbL-grow-gen {w} {w'} e1 e2 c p p' pp with Fin.toℕ p Nat.≟ 0
... | yes eq0 = Ub-L-pos0 w e1 e2 c p eq0 ■ sym (Ub-L-pos0 w' e1 e2 c p' (sym pp ■ eq0))
... | no ¬eq0 = Ub-L-pos>0 w e1 e2 c p (0<n ¬eq0)
              ■ sym (Ub-L-pos>0 w' e1 e2 c p' (0<n (λ e → ¬eq0 (pp ■ e))))

handle-L-lwkq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (_+ N) (syncs-lwkq B₁))
    (proj₁ (canonₛ-handleq B₁ e₁ x e₂ q b₁ B₂))
  ≡ proj₁ (canonₛ-handleq B₁ e₁ x e₂ q (suc b₁) B₂)
handle-L-lwkq []        {N} e₁ x e₂ q b₁ []      =
  UbL-grow-gen e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0) ((q ↑ʳ 0F) ↑ˡ 0) (toℕ↑0ˡ q ■ sym (toℕ↑0ˡ q))
handle-L-lwkq []        {N} e₁ x e₂ q b₁ (c′ ∷ B) =
  cong (λ z → subst Tm (+-suc (syncs (c′ ∷ B)) N) (z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
    (UbL-grow-gen (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F) (q ↑ʳ 0F) (toℕ↑0 q ■ sym (toℕ↑0 q)))
handle-L-lwkq (a ∷ [])      {N} e₁ x e₂ q b₁ B₂ =
  chainT (syncs-lwkq [] {q} {b₁} {B₂}) (handle-L-lwkq [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
handle-L-lwkq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
  chainT (syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂}) (handle-L-lwkq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)

private
  lt-far : ∀ q b → suc q Nat.< q + suc (suc b)
  lt-far q b = subst (suc (suc q) Nat.≤_) (sym (Nat.+-suc q (suc b) ■ cong suc (Nat.+-suc q b)))
                 (Nat.s≤s (Nat.s≤s (Nat.m≤m+n q b)))

-- grown borrow-0 R slot is * (remaining suc (suc b₁) ≥ 2).
handle-R0-*q : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (proj₂ (canonₛ-handleq B₁ e₁ x e₂ q (suc b₁) B₂)) ≡ *
handle-R0-*q []        {N} e₁ x e₂ q b₁ []      =
  Ub-R-far ((q + suc (suc b₁)) + 0) e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0)
    (subst (λ k → suc k Nat.< (q + suc (suc b₁)) + 0) (sym (toℕ↑0ˡ q))
      (subst (suc q Nat.<_) (sym (Nat.+-identityʳ (q + suc (suc b₁)))) (lt-far q b₁)))
handle-R0-*q []        {N} e₁ x e₂ q b₁ (c′ ∷ B) =
  cong (λ z → subst Tm (+-suc (syncs (c′ ∷ B)) N) (z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
    (Ub-R-far (q + suc (suc b₁)) (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F)
      (subst (λ k → suc k Nat.< q + suc (suc b₁)) (sym (toℕ↑0 q)) (lt-far q b₁)))
  ■ subst-Kunit (+-suc (syncs (c′ ∷ B)) N)
handle-R0-*q (a ∷ [])      {N} e₁ x e₂ q b₁ B₂ =
  cong (subst Tm (+-suc (syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)) N)) (handle-R0-*q [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ subst-Kunit (+-suc (syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)) N)
handle-R0-*q (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
  cong (subst Tm (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) N)) (handle-R0-*q (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) N)

-- grown borrow-1 L slot is * (position q+1 > 0).
handle-b1-L-*q : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (canonₛ-handleq-b1 B₁ e₁ x e₂ q b₁ B₂) ≡ *
handle-b1-L-*q []        {N} e₁ x e₂ q b₁ []      =
  Ub-L-pos>0 ((q + suc (suc b₁)) + 0) e₁ e₂ x ((q ↑ʳ 1F) ↑ˡ 0)
    (subst (0 Nat.<_) (sym (toℕ↑1ˡ q)) (Nat.s≤s Nat.z≤n))
handle-b1-L-*q []        {N} e₁ x e₂ q b₁ (c′ ∷ B) =
  cong (λ z → subst Tm (+-suc (syncs (c′ ∷ B)) N) (z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
    (Ub-L-pos>0 (q + suc (suc b₁)) (wk e₁) (` 0F) (suc x) (q ↑ʳ 1F)
      (subst (0 Nat.<_) (sym (toℕ↑1 q)) (Nat.s≤s Nat.z≤n)))
  ■ subst-Kunit (+-suc (syncs (c′ ∷ B)) N)
handle-b1-L-*q (a ∷ [])      {N} e₁ x e₂ q b₁ B₂ =
  cong (subst Tm (+-suc (syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)) N)) (handle-b1-L-*q [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ subst-Kunit (+-suc (syncs (([]) ++ (q + suc (suc b₁)) ∷ B₂)) N)
handle-b1-L-*q (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
  cong (subst Tm (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) N)) (handle-b1-L-*q (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ((d ∷ B₁″) ++ (q + suc (suc b₁)) ∷ B₂)) N)

private
  mkLast : ∀ {w} {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) (k : ℕ) →
           Fin.toℕ p ≡ k → w ≡ suc k → proj₁ (proj₂ (Ub-triple w e1 e2 c p)) ≡ e2
  mkLast e1 e2 c p k tp we = Ub-R-last _ e1 e2 c p (cong suc tp ■ sym we)
  mkFar : ∀ {w} {N} (e1 e2 : Tm N) (c : 𝔽 N) (p : 𝔽 w) (k rem : ℕ) →
          Fin.toℕ p ≡ k → w ≡ suc (suc k) + rem → proj₁ (proj₂ (Ub-triple w e1 e2 c p)) ≡ *
  mkFar e1 e2 c p k rem tp we =
    Ub-R-far _ e1 e2 c p
      (subst (suc (Fin.toℕ p) Nat.<_) (sym we)
        (subst (λ z → suc z Nat.< suc (suc k) + rem) (sym tp) (Nat.m≤m+n (suc (suc k)) rem)))
  wl0  : ∀ q → (q + suc 0) + 0 ≡ suc q
  wl0  q = solve 1 (λ q → (q :+ (con 1 :+ con 0)) :+ con 0 := con 1 :+ q) refl q
  wl1  : ∀ q → (q + suc (suc 0)) + 0 ≡ suc (suc q)
  wl1  q = solve 1 (λ q → (q :+ (con 1 :+ (con 1 :+ con 0))) :+ con 0 := con 1 :+ (con 1 :+ q)) refl q
  wf0  : ∀ q b → (q + suc (suc b)) + 0 ≡ suc (suc q) + b
  wf0  q b = solve 2 (λ q b → (q :+ (con 1 :+ (con 1 :+ b))) :+ con 0 := (con 1 :+ (con 1 :+ q)) :+ b) refl q b
  wf1  : ∀ q b → (q + suc (suc (suc b))) + 0 ≡ suc (suc (suc q)) + b
  wf1  q b = solve 2 (λ q b → (q :+ (con 1 :+ (con 1 :+ (con 1 :+ b)))) :+ con 0 := (con 1 :+ (con 1 :+ (con 1 :+ q))) :+ b) refl q b
  wl0′ : ∀ q → q + suc 0 ≡ suc q
  wl0′ q = solve 1 (λ q → q :+ (con 1 :+ con 0) := con 1 :+ q) refl q
  wl1′ : ∀ q → q + suc (suc 0) ≡ suc (suc q)
  wl1′ q = solve 1 (λ q → q :+ (con 1 :+ (con 1 :+ con 0)) := con 1 :+ (con 1 :+ q)) refl q
  wf0′ : ∀ q b → q + suc (suc b) ≡ suc (suc q) + b
  wf0′ q b = solve 2 (λ q b → q :+ (con 1 :+ (con 1 :+ b)) := (con 1 :+ (con 1 :+ q)) :+ b) refl q b
  wf1′ : ∀ q b → q + suc (suc (suc b)) ≡ suc (suc (suc q)) + b
  wf1′ q b = solve 2 (λ q b → q :+ (con 1 :+ (con 1 :+ (con 1 :+ b))) := (con 1 :+ (con 1 :+ (con 1 :+ q))) :+ b) refl q b

-- ungrown handle R slot = grown borrow-1 handle R slot (both (b₁=0 ? e₂ : *)).
handle-R-lwkq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (_+ N) (syncs-lwkq B₁))
    (proj₁ (proj₂ (canonₛ-handleq B₁ e₁ x e₂ q b₁ B₂)))
  ≡ proj₁ (proj₂ (canonₛ-handleq-b1 B₁ e₁ x e₂ q b₁ B₂))
handle-R-lwkq []        {N} e₁ x e₂ q zero    []      =
  mkLast e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0) q (toℕ↑0ˡ q) (wl0 q)
  ■ sym (mkLast e₁ e₂ x ((q ↑ʳ 1F) ↑ˡ 0) (suc q) (toℕ↑1ˡ q) (wl1 q))
handle-R-lwkq []        {N} e₁ x e₂ q (suc b₁) []      =
  mkFar e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0) q b₁ (toℕ↑0ˡ q) (wf0 q b₁)
  ■ sym (mkFar e₁ e₂ x ((q ↑ʳ 1F) ↑ˡ 0) (suc q) b₁ (toℕ↑1ˡ q) (wf1 q b₁))
handle-R-lwkq []        {N} e₁ x e₂ q zero    (c′ ∷ B) =
  cong (λ z → subst Tm (+-suc (syncs (c′ ∷ B)) N) (z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
    ( mkLast (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F) q (toℕ↑0 q) (wl0′ q)
    ■ sym (mkLast (wk e₁) (` 0F) (suc x) (q ↑ʳ 1F) (suc q) (toℕ↑1 q) (wl1′ q)) )
handle-R-lwkq []        {N} e₁ x e₂ q (suc b₁) (c′ ∷ B) =
  cong (λ z → subst Tm (+-suc (syncs (c′ ∷ B)) N) (z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
    ( mkFar (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F) q b₁ (toℕ↑0 q) (wf0′ q b₁)
    ■ sym (mkFar (wk e₁) (` 0F) (suc x) (q ↑ʳ 1F) (suc q) b₁ (toℕ↑1 q) (wf1′ q b₁)) )
handle-R-lwkq (a ∷ [])      {N} e₁ x e₂ q b₁ B₂ =
  chainT (syncs-lwkq [] {q} {b₁} {B₂}) (handle-R-lwkq [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
handle-R-lwkq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
  chainT (syncs-lwkq (d ∷ B₁″) {q} {b₁} {B₂}) (handle-R-lwkq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)

open T using (_;_⊢ₚ_)

-- Ported frame-cong / frame-fusion-gen (verbatim from Simulation2.Theorems).
app₁-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ L → Value e₁} {V₂ : d ≡ L → Value e₂}
          → e₁ ≡ e₂ → app₁ e₁ d V₁ ≡ app₁ e₂ d V₂
app₁-cong refl = cong (app₁ _ _) (funext (λ x → Value-irr))

app₂-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ 𝟙 ⊎ d ≡ R → Value e₁} {V₂ : d ≡ 𝟙 ⊎ d ≡ R → Value e₂}
          → e₁ ≡ e₂ → app₂ e₁ d V₁ ≡ app₂ e₂ d V₂
app₂-cong refl = cong (app₂ _ _) (funext (λ x → Value-irr))

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (app₁ e₂ d V?) Vϕ Vψ eq = app₁-cong (⋯-cong e₂ eq)
frame-cong (app₂ e₁ d V?) Vϕ Vψ eq = app₂-cong (⋯-cong e₁ eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))
frame-cong (`inj□ i)      Vϕ Vψ eq = refl
frame-cong (`case□`of⟨ e₁ ; e₂ ⟩) Vϕ Vψ eq =
  cong₂ `case□`of⟨_;_⟩ (⋯-cong e₁ (eq ~↑)) (⋯-cong e₂ (eq ~↑))

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (app₁ e₂ d V?) {ϕ} Vϕ {ξ} Vξ Vϕξ = app₁-cong (fusion e₂ ϕ ξ)
frame-fusion-gen (app₂ e₁ d V?) {ϕ} Vϕ {ξ} Vξ Vϕξ = app₂-cong (fusion e₁ ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
frame-fusion-gen (`inj□ i)      {ϕ} Vϕ {ξ} Vξ Vϕξ = refl
frame-fusion-gen (`case□`of⟨ e₁ ; e₂ ⟩) {ϕ} Vϕ {ξ} Vξ Vϕξ =
  cong₂ `case□`of⟨_;_⟩ (fusion e₁ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₁ (λ x → sym (dist-↑-· ϕ ξ x)))
                        (fusion e₂ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₂ (λ x → sym (dist-↑-· ϕ ξ x)))

-- The two exported simulation cases.

-- | Frame-level analogues of the U-cong / U-⋯p / transport helpers used in
--   PrestRec, for the FRAME side of redexRec (ccEqR).

frame*-cong : (E : Frame* m) {σ τ : m →ₛ n} (Vσ : VSub σ) (Vτ : VSub τ) → σ ≗ τ →
              frame*-⋯ E σ Vσ ≡ frame*-⋯ E τ Vτ
frame*-cong []       Vσ Vτ eq = refl
frame*-cong (F ∷ E*) Vσ Vτ eq = cong₂ _∷_ (frame-cong F Vσ Vτ eq) (frame*-cong E* Vσ Vτ eq)

-- frame*-⋯ of a frame renaming fuses into the substitution (frame analogue of U-⋯p).
F-⋯f*-fuse : (E : Frame* m) {p : ℕ} {ρ : m →ᵣ p} {τ : p →ₛ n} (Vτ : VSub τ) (Vρτ : VSub (ρ ·ₖ τ)) →
             frame*-⋯ (E ⋯ᶠ* ρ) τ Vτ ≡ frame*-⋯ E (ρ ·ₖ τ) Vρτ
F-⋯f*-fuse []       Vτ Vρτ = refl
F-⋯f*-fuse (F ∷ E*) {ρ} {τ} Vτ Vρτ =
  cong₂ _∷_ (frame-fusion-gen F (λ _ → V-`) Vτ Vρτ) (F-⋯f*-fuse E* Vτ Vρτ)

subst-VSub : {a : ℕ} (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) {σ : a →ₛ h x} → VSub σ →
             VSub (subst (λ z → a →ₛ h z) eq σ)
subst-VSub h refl V = V

·ₖ-VSubᵣ : {m p n : ℕ} (ρ : m →ᵣ p) {τ : p →ₛ n} → VSub τ → VSub (ρ ·ₖ τ)
·ₖ-VSubᵣ ρ {τ} Vτ i = Vτ (ρ i)

-- transport of frame*-⋯ along a codomain scope equality (frame analogue of U-cod-transport).
F-cod-transport : {a : ℕ} (E : Frame* a) (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y)
                  {σ : a →ₛ h x} (Vσ : VSub σ) →
                  subst (λ z → Frame* (h z)) eq (frame*-⋯ E σ Vσ)
                  ≡ frame*-⋯ E (subst (λ z → a →ₛ h z) eq σ) (subst-VSub h eq Vσ)
F-cod-transport E h refl Vσ = refl

substF-⋯ : {kk kk′ : ℕ} (fg : ℕ → ℕ) (e : kk ≡ kk′) (E : Frame* (fg kk)) →
           subst Frame* (cong fg e) E ≡ subst (λ j → Frame* (fg j)) e E
substF-⋯ fg refl E = refl

transport-⋯f* : {kk kk′ : ℕ} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′)
                (E : Frame* (fg kk)) →
                subst (λ j → Frame* (gg j)) eq (E ⋯ᶠ* ρ kk)
                ≡ (subst (λ j → Frame* (fg j)) eq E) ⋯ᶠ* ρ kk′
transport-⋯f* fg gg ρ refl E = refl


U-lsplit : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → {P : T.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     Γ ; γ ⊢ₚ T.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
                 (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P))
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     (U[ T.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
              (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P) ] σ
       UR─→ₚ*
      U[ T.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)) ] σ)
     ⊎
     (U[ T.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
              (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P) ] σ
       U.≋
      U[ T.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)) ] σ))
U-lsplit {m} {n} σ Vσ Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with lsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq = ≋-wrap-⊎ front fire back
  where
    module 𝐒 = SplitRenamings B₁ B₂ (sum B)
    C₁ C₁′ : BindGroup
    C₁  = B₁ ++ (q + suc b₁) ∷ B₂
    C₁′ = B₁ ++ (q + suc (suc b₁)) ∷ B₂
    QL : T.Proc (sum C₁ + sum B + m)
    QL = T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P
    QR : T.Proc (sum C₁′ + sum B + m)
    QR = T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)
    sA sA′ sB : ℕ
    sA  = syncs C₁
    sA′ = syncs C₁′
    sB  = syncs B
    τ : sum C₁ + sum B + m →ₛ syncs B + (syncs C₁ + (2 + n))
    τ = leafσ σ C₁ B
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    push : ∀ {kk} → U.Proc (sB + (sA + (2 + kk))) → U.Proc (2 + (sB + (sA + kk)))
    push {kk} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    XL : U.Proc (sB + (sA + (2 + n)))
    XL = U[ QL ] τ
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ C₁ (Bφ B X)) U.≋ Bφ C₁ (Bφ B (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ C₁ (Bφ B X)
      ◅◅ Bφ-cong C₁ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong C₁ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν C₁ B QL ] σ U.≋ Bφ C₁ (Bφ B (U.ν (push XL)))
    front = ≡→≋ (Uν-flat σ C₁ B QL) ◅◅ ν↓ XL
    castpos : 𝔽 (sum C₁)
    castpos = Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    -- the lsplit handle translated at the leaf.
    hc = canonₛ-handleq B₁ (K `unit) 0F (K `unit) q b₁ B₂
    cc : Tm (2 + (sB + (sA + n)))
    cc = rn (τ (𝐒.atk (q ↑ʳ 0F)))
    -- τ (inj 0F) = canonₛ C₁ cc1 castpos ⋯ weaken* sB
    τinj0 : τ (𝐒.atk (q ↑ʳ 0F)) ≡ canonₛ C₁ (K `unit , 0F , K `unit) castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τinj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
    ccTriple : cc ≡ ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` 0F))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
    ccTriple =
        cong rn (τinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc)))))
      ■ cong (λ z → ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` z))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂))
          (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc))))
    Fr : Frame* (2 + (sB + (sA + n)))
    Fr = (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ P ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    threadEq : (Ef : Frame* (sum C₁ + sum B + m)) (p : Tm (sum C₁ + sum B + m)) →
               (U[ T.⟪ Ef [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* Ef τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ Ef τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    YL≡ : push XL ≡ U.⟪ Fr [ K (`lsplit s) ·¹ cc ]* ⟫ U.∥ RP
    YL≡ = cong₂ U._∥_
            (threadEq E (K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F))))
            refl
    ccA ccC : Tm (2 + (sB + (sA + n)))
    ccA = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccC = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccL0 ccR0 : Tm (2 + (sB + (sA + n)))
    ccL0 = ((ccA ⊗ (` 0F)) ⊗ *)
    ccR0 = ((* ⊗ (` 0F)) ⊗ ccC)
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = U.⟪ Fr [ K (`lsplit s) ·¹ cc ]* ⟫ U.∥ RP
    contractumR : U.Proc (2 + (sB + (sA + n)))
    contractumR = U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫ U.∥ RP
    lsplitStep : U.ν redexL UR.─→ₚ U.ν contractumR
    lsplitStep = subst (λ z → U.ν (U.⟪ Fr [ K (`lsplit s) ·¹ z ]* ⟫ U.∥ RP)
                              UR.─→ₚ U.ν contractumR)
                   (sym ccTriple) (UR.RU-LSplit {e₁ = ccA} {e₂ = ccC} Fr)
    leaf-fire : U.ν (push XL) UR.─→ₚ U.ν contractumR
    leaf-fire = UR.RU-Struct (U.ν-cong (≡→≋ YL≡)) lsplitStep ε
    fire : Bφ C₁ (Bφ B (U.ν (push XL))) UR─→ₚ* Bφ C₁ (Bφ B (U.ν contractumR))
    fire = Bφ-lift-step C₁ (Bφ-lift-step B leaf-fire) ◅ ε
    τ′ : sum C₁′ + sum B + m →ₛ syncs B + (syncs C₁′ + (2 + n))
    τ′ = leafσ σ C₁′ B
    Vτ′ : VSub τ′
    Vτ′ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA′ 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA′) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    XR′ : U.Proc (sB + (sA′ + (2 + n)))
    XR′ = U[ QR ] τ′
    pushR : ∀ {kk} → U.Proc (sB + (sA′ + (2 + kk))) → U.Proc (2 + (sB + (sA′ + kk)))
    pushR {kk} X = (X U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ν↓′ : ∀ (X : U.Proc (sB + (sA′ + (2 + n)))) →
          U.ν (Bφ C₁′ (Bφ B X)) U.≋ Bφ C₁′ (Bφ B (U.ν (pushR X)))
    ν↓′ X =
         ν-past-Bφ C₁′ (Bφ B X)
      ◅◅ Bφ-cong C₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA′ 2))))
      ◅◅ Bφ-cong C₁′ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)))
    rhs : U[ T.ν C₁′ B QR ] σ U.≋ Bφ C₁′ (Bφ B (U.ν (pushR XR′)))
    rhs = ≡→≋ (Uν-flat σ C₁′ B QR) ◅◅ ν↓′ XR′
    e1 : sA ≡ sA′
    e1 = syncs-lwkq B₁
    -- the transported contractum at the leaf must match pushR XR′.
    eqP : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
    eqP = cong (2 +_) (cong (sB +_) (cong (_+ n) e1))
    pushR-thread : U.Proc (2 + (sB + (sA′ + n)))
    pushR-thread = (U[ T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ ] τ′ U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    pushR-P : U.Proc (2 + (sB + (sA′ + n)))
    pushR-P = (U[ P T.⋯ₚ 𝐒.lwk ] τ′ U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ρ₁′ : (sB + (sA′ + (2 + n))) →ᵣ (sB + (2 + (sA′ + n)))
    ρ₁′ = assocSwapᵣ sA′ 2 ↑* sB
    ρ₂′ : (sB + (2 + (sA′ + n))) →ᵣ (2 + (sB + (sA′ + n)))
    ρ₂′ = assocSwapᵣ sB 2
    rn′ : Tm (sB + (sA′ + (2 + n))) → Tm (2 + (sB + (sA′ + n)))
    rn′ t = (t ⋯ ρ₁′) ⋯ ρ₂′
    Fr′ : Frame* (2 + (sB + (sA′ + n)))
    Fr′ = (frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′ ⋯ᶠ* ρ₁′) ⋯ᶠ* ρ₂′
    threadEq′ : (Ef : Frame* (sum C₁′ + sum B + m)) (p : Tm (sum C₁′ + sum B + m)) →
                (U[ T.⟪ Ef [ p ]* ⟫ ] τ′ U.⋯ₚ ρ₁′) U.⋯ₚ ρ₂′
                ≡ U.⟪ ((frame*-⋯ Ef τ′ Vτ′ ⋯ᶠ* ρ₁′) ⋯ᶠ* ρ₂′) [ rn′ (p ⋯ τ′) ]* ⟫
    threadEq′ Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁′) ⋯ ρ₂′) (frame-plug* Ef τ′ Vτ′)
      ■ cong (_⋯ ρ₂′) (frame-plug*ᵣ (frame*-⋯ Ef τ′ Vτ′) ρ₁′)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ′ Vτ′ ⋯ᶠ* ρ₁′) ρ₂′ )
    pushR-threadEq : pushR-thread ≡ U.⟪ Fr′ [ rn′ (τ′ (𝐒.atk (q ↑ʳ 0F))) ⊗ rn′ (τ′ (𝐒.atk (q ↑ʳ 1F))) ]* ⟫
    pushR-threadEq = threadEq′ (E ⋯ᶠ* 𝐒.lwk) ((` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)))
    -- the grown handle (inj 0F in C₁′), pushed, has junction 0F: same chanTriple shape as cc.
    hc′ = canonₛ-handleq B₁ {N = 2 + n} (K `unit) 0F (K `unit) q (suc b₁) B₂
    castpos′ : 𝔽 (sum C₁′)
    castpos′ = Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
    τ′inj0 : τ′ (𝐒.atk (q ↑ʳ 0F)) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos′ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τ′inj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos′ ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos′ (sum B))
    ccEqR : subst U.Proc eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) ≡ pushR-thread
    ccEqR =
        cong (λ pf → subst U.Proc pf (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫)) (uipℕ eqP eqPh)
      ■ substP-∘ hF e1 (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫)
      ■ subst-⟪⟫f hF e1 (Fr [ ccL0 ⊗ ccR0 ]*)
      ■ cong U.⟪_⟫ (subst-frame-plug hF e1 Fr (ccL0 ⊗ ccR0))
      ■ cong U.⟪_⟫ (cong₂ _[_]* frameTransport bodyTransport)
      ■ sym pushR-threadEq
      where
        hF : ℕ → ℕ
        hF j = 2 + (sB + (j + n))
        eqPh : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
        eqPh = cong hF e1
        frameLeafeq : subst (λ j → Frame* (sB + (j + (2 + n)))) e1 (frame*-⋯ E τ Vτ)
                      ≡ frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′
        frameLeafeq =
            F-cod-transport E (λ j → sB + (j + (2 + n))) e1 Vτ
          ■ cong (λ EE → frame*-⋯ EE (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)
                            (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)) Eeq
          ■ F-⋯f*-fuse E₀ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)
                       (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
          ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
                           (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
              (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                   ■ leafσ-lwk-id σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y))
          ■ sym (F-⋯f*-fuse E₀ (·ₖ-VSubᵣ 𝐒.lwk Vτ′) (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′)))
          ■ cong (λ EE → frame*-⋯ EE (𝐒.lwk ·ₖ τ′) (·ₖ-VSubᵣ 𝐒.lwk Vτ′)) (sym Eeq)
          ■ sym (F-⋯f*-fuse E Vτ′ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
          where
            substσ-app : (h : ℕ → ℕ) {x yy : ℕ} (eq : x ≡ yy) {aa : ℕ} (ϱ : aa →ₛ h x) (i : 𝔽 aa) →
                         subst (λ j → aa →ₛ h j) eq ϱ i ≡ subst (λ j → Tm (h j)) eq (ϱ i)
            substσ-app h refl ϱ i = refl
        frameTransport : subst (λ j → Frame* (hF j)) e1 Fr ≡ Fr′
        frameTransport =
            transport-⋯f* (λ j → sB + (2 + (j + n))) hF (λ j → assocSwapᵣ sB 2 {j + n}) e1 (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁)
          ■ cong (λ z → z ⋯ᶠ* assocSwapᵣ sB 2 {sA′ + n})
              ( transport-⋯f* (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) (λ j → assocSwapᵣ j 2 {n} ↑* sB) e1 (frame*-⋯ E τ Vτ)
              ■ cong (λ z → z ⋯ᶠ* (assocSwapᵣ sA′ 2 {n} ↑* sB)) frameLeafeq )
        castpos1′ : 𝔽 (sum C₁′)
        castpos1′ = Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
        τ′inj1 : τ′ (𝐒.atk (q ↑ʳ 1F)) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos1′ ⋯ weaken* {{ Kᵣ }} sB
        τ′inj1 =
            cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos1′ ↑ˡ sum B) m)
          ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos1′ (sum B))
        -- grown handle borrow-1 triple (left slot *, right slot = grown borrow-1 R-slot).
        hb1 = canonₛ-handleq-b1 B₁ {N = 2 + n} (K `unit) 0F (K `unit) q b₁ B₂
        -- pushed grown borrow-0 triple: right slot is * (grown width ≥ 2).
        hc′triple : rn′ (τ′ (𝐒.atk (q ↑ʳ 0F)))
                    ≡ ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                      ⊗ (proj₁ (proj₂ hc′) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        hc′triple =
            cong rn′ (τ′inj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc′)))))
          ■ cong (λ z → ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` z))
                        ⊗ (proj₁ (proj₂ hc′) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
              (Fin.toℕ-injective (assocPush-junc sA′ sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′)))) jvtoℕ′ (Nat.s≤s Nat.z≤n)))
          where
            jvtoℕ′ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′)))) ≡ sB + (sA′ + 0)
            jvtoℕ′ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc′))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc′))))
        -- pushed grown borrow-1 triple.
        hc′triple1 : rn′ (τ′ (𝐒.atk (q ↑ʳ 1F)))
                     ≡ ((proj₁ hb1 ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                       ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        hc′triple1 =
            cong rn′ (τ′inj1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hb1)))))
          ■ cong (λ z → ((proj₁ hb1 ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` z))
                        ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
              (Fin.toℕ-injective (assocPush-junc sA′ sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1)))) jv1toℕ (Nat.s≤s Nat.z≤n)))
          where
            jv1toℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1)))) ≡ sB + (sA′ + 0)
            jv1toℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hb1))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hb1))))
        -- slot correspondences under handle growth.
        L-inv : subst Tm (cong (_+ (2 + n)) e1) (proj₁ hc) ≡ proj₁ hc′
        L-inv = handle-L-lwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂
        R0-* : proj₁ (proj₂ hc′) ≡ *
        R0-* = handle-R0-*q B₁ (K `unit) 0F (K `unit) q b₁ B₂
        R-corr : subst Tm (cong (_+ (2 + n)) e1) (proj₁ (proj₂ hc)) ≡ proj₁ (proj₂ hb1)
        R-corr = handle-R-lwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂
        L0-* : proj₁ hb1 ≡ *
        L0-* = handle-b1-L-*q B₁ (K `unit) 0F (K `unit) q b₁ B₂
        -- push a single ungrown slot (with its wk sB) forward to the grown side.
        pushSlot : (t : Tm (sA + (2 + n))) {t′ : Tm (sA′ + (2 + n))}
                   → subst Tm (cong (_+ (2 + n)) e1) t ≡ t′
                   → subst (λ j → Tm (hF j)) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
                     ≡ (t′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        pushSlot t {t′} et =
            transport-⋯t (λ j → sB + (2 + (j + n))) hF (λ j → assocSwapᵣ sB 2 {j + n}) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁)
          ■ cong (_⋯ assocSwapᵣ sB 2 {sA′ + n})
              ( transport-⋯t (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) (λ j → assocSwapᵣ j 2 {n} ↑* sB) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
              ■ cong (_⋯ (assocSwapᵣ sA′ 2 {n} ↑* sB))
                  ( subst-wkB sB e1 t
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+ e1 t) ■ et) ) )
        pushJunc : subst (λ j → Tm (hF j)) e1 (` 0F) ≡ (` 0F)
        pushJunc = go e1
          where go : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (2 + (sB + (j + n)))) eq (` 0F) ≡ (` 0F)
                go refl = refl
        pushKunit : subst (λ j → Tm (hF j)) e1 * ≡ *
        pushKunit = go e1
          where go : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (2 + (sB + (j + n)))) eq * ≡ *
                go refl = refl
        bodyTransport : subst (λ j → Tm (hF j)) e1 (ccL0 ⊗ ccR0)
                        ≡ rn′ (τ′ (𝐒.atk (q ↑ʳ 0F))) ⊗ rn′ (τ′ (𝐒.atk (q ↑ʳ 1F)))
        bodyTransport =
            subst-⊗f hF e1 ccL0 ccR0
          ■ cong₂ _⊗_
              ( subst-⊗f hF e1 (ccA ⊗ (` 0F)) *
              ■ cong₂ _⊗_ (subst-⊗f hF e1 ccA (` 0F) ■ cong₂ _⊗_ (pushSlot (proj₁ hc) L-inv) pushJunc)
                          pushKunit
              ■ sym hc′triple₀ )
              ( subst-⊗f hF e1 (* ⊗ (` 0F)) ccC
              ■ cong₂ _⊗_ (subst-⊗f hF e1 * (` 0F) ■ cong₂ _⊗_ pushKunit pushJunc)
                          (pushSlot (proj₁ (proj₂ hc)) R-corr)
              ■ sym hc′triple1₀ )
          where
            -- grown borrow-0 triple with right slot rewritten to *.
            hc′triple₀ : rn′ (τ′ (𝐒.atk (q ↑ʳ 0F)))
                         ≡ ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F)) ⊗ *
            hc′triple₀ = hc′triple
              ■ cong (λ z → ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F)) ⊗ z)
                  (cong (λ w → w ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) R0-*)
            -- grown borrow-1 triple with left slot rewritten to *.
            hc′triple1₀ : rn′ (τ′ (𝐒.atk (q ↑ʳ 1F)))
                          ≡ ((* ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                            ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
            hc′triple1₀ = hc′triple1
              ■ cong (λ z → ((z ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                            ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
                  L0-*
    redexRec : subst U.Proc eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) ≡ pushR-thread
    redexRec = ccEqR
    ρ₂F : (j : ℕ) → (sB + (2 + (j + n))) →ᵣ (2 + (sB + (j + n)))
    ρ₂F j = assocSwapᵣ sB 2 {j + n}
    ρ₁F : (j : ℕ) → (sB + (j + (2 + n))) →ᵣ (sB + (2 + (j + n)))
    ρ₁F j = assocSwapᵣ j 2 {n} ↑* sB
    Pleafeq : subst (λ j → U.Proc (sB + (j + (2 + n)))) e1 (U[ P ] τ) ≡ U[ P T.⋯ₚ 𝐒.lwk ] τ′
    Pleafeq =
        U-cod-transport P (λ j → sB + (j + (2 + n))) e1 τ
      ■ cong (λ p → U[ p ] (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)) Peq
      ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                       ■ leafσ-lwk-id σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y))
      ■ sym (U-⋯ₚ P₀)
      ■ cong (λ p → U[ p ] (𝐒.lwk ·ₖ τ′)) (sym Peq)
      ■ sym (U-⋯ₚ P)
      where
        substσ-app : (h : ℕ → ℕ) {x yy : ℕ} (eq : x ≡ yy) {aa : ℕ} (ρ : aa →ₛ h x) (i : 𝔽 aa) →
                     subst (λ j → aa →ₛ h j) eq ρ i ≡ subst (λ j → Tm (h j)) eq (ρ i)
        substσ-app h refl ρ i = refl
    eqP′ : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
    eqP′ = cong (λ j → 2 + (sB + (j + n))) e1
    PrestRec : subst U.Proc eqP RP ≡ pushR-P
    PrestRec =
        cong (λ pf → subst U.Proc pf RP) (uipℕ eqP eqP′)
      ■ substP-∘ (λ j → 2 + (sB + (j + n))) e1 RP
      ■ transport-⋯ₚ (λ j → sB + (2 + (j + n))) (λ j → 2 + (sB + (j + n))) ρ₂F e1 (U[ P ] τ U.⋯ₚ ρ₁)
      ■ cong (λ z → z U.⋯ₚ ρ₂F sA′)
          ( transport-⋯ₚ (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) ρ₁F e1 (U[ P ] τ)
          ■ cong (λ z → z U.⋯ₚ ρ₁F sA′) Pleafeq )
    bodyReconcile : subst U.Proc eqP contractumR
                    U.≋ pushR XR′
    bodyReconcile = ≡→≋
      ( subst-∥f (λ z → z) eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) RP
      ■ cong₂ U._∥_ redexRec PrestRec )
    middleReconcile : Bφ C₁ (Bφ B (U.ν contractumR)) U.≋ Bφ C₁′ (Bφ B (U.ν (pushR XR′)))
    middleReconcile =
         ≡→≋ (Bφ-lwk B₁ {q} {b₁} {B₂} {a = n} (Bφ B (U.ν contractumR)))
      ◅◅ Bφ-cong C₁′
           ( ≡→≋ ( subst-Bφ (cong (_+ n) e1) B (U.ν contractumR)
                 ■ cong (Bφ B) (subst-ν (cong (sB +_) (cong (_+ n) e1)) contractumR) )
           ◅◅ Bφ-cong B (U.ν-cong bodyReconcile) )
    back : Bφ C₁ (Bφ B (U.ν contractumR)) U.≋ U[ T.ν C₁′ B QR ] σ
    back = middleReconcile ◅◅ Eq*.symmetric _ rhs


-- ============================================================================
--   RSPLIT-specific infrastructure.  rwk inserts a fresh data block `1 ∷` at
--   flat position `sum B₁` (vs lwk's slot-bump at `sum B₁ + 1`), so the bind
--   group GROWS by one block: C₁ᴿ = B₁ ++ 1 ∷ suc b₁ ∷ B₂.
-- ============================================================================

-- the grown rsplit bind group has exactly one more sync (ϕ[1]=drop, and the
-- inserted block is non-last).  Induction on B₁.
syncs-rwk : ∀ (B₁ : T.BindGroup) {b₁ : ℕ} {B₂ : T.BindGroup} →
            syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂))
syncs-rwk []            {b₁} {B₂}      = refl
syncs-rwk (a ∷ [])      {b₁} {B₂}      = cong suc (syncs-rwk [] {b₁} {B₂})
syncs-rwk (a ∷ d ∷ B₁″) {b₁} {B₂}      = cong suc (syncs-rwk (d ∷ B₁″) {b₁} {B₂})

-- The rsplit-grown bind group has exactly one more data slot.
sum-rwk : ∀ (B₁ : T.BindGroup) {b₁ B₂} →
          sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂))
sum-rwk B₁ {b₁} {B₂} = sum-++ B₁ (1 ∷ suc b₁ ∷ B₂)
                     ■ Nat.+-suc (sum B₁) (sum (suc b₁ ∷ B₂))
                     ■ cong suc (sym (sum-++ B₁ (suc b₁ ∷ B₂)))

sB₁≤sumC₁r : ∀ (B₁ : T.BindGroup) {b₁ B₂} → sum B₁ Nat.≤ sum (B₁ ++ suc b₁ ∷ B₂)
sB₁≤sumC₁r B₁ {b₁} {B₂} =
  subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (Nat.m≤m+n (sum B₁) (sum (suc b₁ ∷ B₂)))

-- drwk inserts a slot at flat position `sum B₁`: below it, toℕ preserved; at/above, +1.
drwk : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) →
       sum (B₁ ++ suc b₁ ∷ B₂) →ᵣ sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)
drwk []        b₁ B₂ i = weakenᵣ i
drwk (a ∷ B₁') b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) , (λ r → a ↑ʳ drwk B₁' b₁ B₂ r) ]′ (splitAt a i)

