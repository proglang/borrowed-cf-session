-- | Preservation of process typing for the communication rule `R-Com`.
--
--   The session-type content is `Support.MsgSplit.com-split`; the de Bruijn
--   content is `Support.ComWeaken` (erasing the two communicated handles from
--   a structure).  What is left here is the inversion cascade and the
--   rebuilding of the two threads, in which the sent value's structure moves
--   from the sender's context pattern to the receiver's -- legal because the
--   payload is `Mobile`.
module BorrowedCF.Safety.Preservation.Com where

open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat.ListAction using (sum)
open import Data.Vec.Relation.Unary.All as Allⱽ using () renaming (All to Allⱽ)

import Data.Vec.Relation.Unary.All.Properties as Allⱽ

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Renamings
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Support.ComWeaken
open import BorrowedCF.Safety.Preservation.Support.MsgSplit

open Variables
open Fin.Patterns

private variable b₁ b₂ : ℕ

-- `_⊗¹_` in the type of `send` pins the pair former to the parallel join.
join-𝟙 : (p/s : ParSeq) → biasedDir p/s ≡ 𝟙 → ∀ {n} {α β : Struct n} → join p/s α β ≡ α ∥ β
join-𝟙 par refl = refl

pres-Com : {Γ : Ctx n} {e : Tm (b₁ + sum B₁ + (b₂ + sum B₂) + n)}
           {E₁ E₂ : Frame* (b₁ + sum B₁ + (b₂ + sum B₂) + n)}
           {P : Proc (b₁ + sum B₁ + (b₂ + sum B₂) + n)} →
  ChanCx Γ → (V : Value e) →
  (let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
   Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
     ((⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
       ∥ ⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ n (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
       ∥ (P ⋯ₚ wkρ))) →
  Γ ; γ ⊢ₚ ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ e ]* ⟫) ∥ P)
pres-Com {n = n} {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂} {γ = γ} {Γ = Γ} {e = e}
         {E₁ = E₁} {E₂ = E₂} {P = P} Γ-S Vv p
  with (T₁ ⸴ Γ₁) , (T₂ ⸴ Γ₂) , s , pl , N , ⊢B₁ , ⊢B₂ , C₁ , C₂ , p′ ← inv-ν p
  with αβ , γP , αβγ≤ , p″ , q ← inv-∥ p′
  with α , β , αβ≤ , p₁ , p₂ ← inv-∥ p″
  with 𝓟₁ , α′ , _ , _ , _ , _ , ≤α , eqU₁ , ϵ≤₁ , ⊢E₁ , ⊢send·vc₁ ← ⊢[]*⁻¹ (E₁ ⋯ᶠ* _) _ (inv-⟪⟫ p₁)
  with 𝓟₂ , β′ , _ , _ , _ , _ , ≤β , eqU₂ , ϵ≤₂ , ⊢E₂ , ⊢recv·c₂ ← ⊢[]*⁻¹ (E₂ ⋯ᶠ* _) _ (inv-⟪⟫ p₂)
  with a₁ , α-send , α-vc₁ , _ , ≤α′ , ≤a₁ , refl , ⊢send , ⊢vc₁
    ← inv-·-unr ⊢send·vc₁ (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with a₂ , β-recv , β-c₂ , _ , ≤β′ , ≤a₂ , refl , ⊢recv , ⊢c₂
    ← inv-·-unr ⊢recv·c₂ (λ x → constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂))
  with _ , (T≃₁ ⊗ ⟨ ‼T≃ ⟩) `→ ‵⊤≃ , []≤α-send , `send MT₁ ← inv-K ⊢send
  with _ , ⟨ ⁇T≃ ⟩ `→ T≃₂ , []≤β-recv , `recv MT₂ ← inv-K ⊢recv
  with p/s , α-v , α-c₁ , _ , _ , _ , _ , ≤α-vc₁ , vc₁≃ , ϵ≤₁′ , seq⇒p , ⊢v , ⊢c₁ ← inv-⊗ ⊢vc₁
  with v≃ , p/s≡𝟙 , ⟨ c₁≃ ⟩ ← ≃-⊗⁻¹ vc₁≃
  with ⟨ eq-c₁ ⟩ , `c₁≤ ← inv-` ⊢c₁
  with eq-c₂′ , `c₂≤ ← inv-` ⊢c₂
  with ⟨ eq-c₂ ⟩ ← subst (_ ≃_)
        (V.lookup-++ˡ (Γ₁ ⸴* T₂ ⸴ Γ₂) Γ (b₁ + sum B₁ ↑ʳ 0F) ■ V.lookup-++ʳ Γ₁ (T₂ ⸴ Γ₂) 0F)
        eq-c₂′
  with s₁′ , ‼T#;#s₁′≃ , C₁′ ← bindCtx-inv-msg (≃-trans (≃-trans (≃-sym eq-c₁) c₁≃) (≃-sym ‼T≃)) C₁
  with s₂′ , ⁇T#;#s₂′≃ , C₂′ ← bindCtx-inv-msg (≃-trans (≃-sym eq-c₂) (≃-sym ⁇T≃)) C₂
  with s* , N* , U≃ , s₁≃ , s₂≃ ← com-split N pl ‼T#;#s₁′≃ ⁇T#;#s₂′≃
  = let ⊢ρ = ⊢wkₚ Γ₁ Γ₂ Γ {T₁} {T₂}
        ρ-inj = wkₚ-inj (b₁ + sum B₁) (b₂ + sum B₂) n
        γ″ , ≤γ″ , q′ = q ⊢⋯ₚ⁻¹ ⊢ρ / ρ-inj
        𝒫₁ , 𝒫₁≤ , ⊢E₁′ = ⊢E₁ ⊢⋯ᶠ*⁻¹ ⊢ρ / ρ-inj
        𝒫₂ , 𝒫₂≤ , ⊢E₂′ = ⊢E₂ ⊢⋯ᶠ*⁻¹ ⊢ρ / ρ-inj
        α-v′ , α-v′≤ , ⊢v′ = ⊢v ⊢⋯⁻¹ ⊢ρ / ρ-inj

        Γ-S′ = Allⱽ.++⁺ (Allⱽ.++⁺ (bindCtx⇒chanCtx C₁′) (bindCtx⇒chanCtx C₂′)) Γ-S

        Ta≃Tv = ≃-trans v≃ (≃-sym T≃₁)
        mob = mobile×value⇒mobCx Γ-S′ (mobile-≃ (≃-sym Ta≃Tv) MT₁) Vv ⊢v′

        inner₁ = ≼-trans (≼-cong-∥ α-v′≤ `c₁≤)
                 (≼-trans (subst (_ ∶_≼ α-vc₁) (join-𝟙 p/s p/s≡𝟙) ≤α-vc₁)
                 (≼-trans (≼-respˡ-≈ (join-[]₂ (Arr.dir a₁))
                             (≼-join (Arr.dir a₁) (≼-refl ≈-refl) []≤α-send))
                          ≤α′))
        inner₂ = ≼-trans `c₂≤
                 (≼-trans (≼-respˡ-≈ (join-[]₂ (Arr.dir a₂))
                             (≼-join (Arr.dir a₂) (≼-refl ≈-refl) []≤β-recv))
                          ≤β′)

        big≤ = ≼-trans (≼-cong-∥
                          (≼-trans (≼-cong-∥ (≼-trans (𝒫₁≤ inner₁) ≤α)
                                             (≼-trans (𝒫₂≤ inner₂) ≤β))
                                   αβ≤)
                          ≤γ″)
                       αβγ≤

        Xδ≡ = cong₂ _∥_
                (cong₂ _∥_
                  ([-]-dist-⋯ (𝒫₁ ⋯𝓅 _) _ (del (b₁ + sum B₁) (b₂ + sum B₂))
                    ■ cong₂ _[_]𝓅 (⋯𝓅-cancel (b₁ + sum B₁) (b₂ + sum B₂) 𝒫₁ (λ _ → refl))
                        (cong₂ _∥_ (⋯-cancel (b₁ + sum B₁) (b₂ + sum B₂) α-v′ (λ _ → refl))
                                   (del-x (b₁ + sum B₁) (b₂ + sum B₂))))
                  ([-]-dist-⋯ (𝒫₂ ⋯𝓅 _) _ (del (b₁ + sum B₁) (b₂ + sum B₂))
                    ■ cong₂ _[_]𝓅 (⋯𝓅-cancel (b₁ + sum B₁) (b₂ + sum B₂) 𝒫₂ (λ _ → refl))
                        (del-y (b₁ + sum B₁) (b₂ + sum B₂))))
                (⋯-cancel (b₁ + sum B₁) (b₂ + sum B₂) γ″ (λ _ → refl))

        lhs≈ = 𝐂.∥-cong (≈-trans (𝐂.∥-cong (≈-trans ([-]𝓅-≈ 𝒫₁ 𝐂.∥-unit₂) (pullOutMobile 𝒫₁ mob)) ≈-refl)
                               (≈-trans (𝐂.∥-cong 𝐂.∥-comm ≈-refl) 𝐂.∥-assoc))
                      ≈-refl
        rhs≈ = 𝐂.∥-cong (𝐂.∥-cong ≈-refl (pullOutMobile 𝒫₂ mob)) ≈-refl

        small≤ = ≼-respˡ-≈ (≈-trans (≈-reflexive Xδ≡) (≈-trans lhs≈ (≈-sym rhs≈)))
                   (≼-respʳ-≈ (Fr-del b₁ B₁ b₂ B₂ γ)
                     (≼-⋯ (del-⇒ Γ₁ Γ₂ Γ) big≤))
    in
    TP-Res N* pl ⊢B₁ ⊢B₂ (bindCtx-≃ s₁≃ C₁′) (bindCtx-≃ s₂≃ C₂′)
      (TP-Weaken small≤
        (TP-Par
          (TP-Par (TP-Expr (T-Conv eqU₁ ϵ≤₁ ⊢⟨ ⊢E₁′ [ T-Conv ‵⊤≃ ℙ≤ϵ (T-Const `unit) ]*⟩))
                  (TP-Expr (T-Conv eqU₂ ϵ≤₂ ⊢⟨ ⊢E₂′
                             [ T-Conv (≃-trans Ta≃Tv (≃-trans U≃ T≃₂)) ℙ≤ϵ
                                 (value⇒pure Vv ⊢v′) ]*⟩)))
          q′))
