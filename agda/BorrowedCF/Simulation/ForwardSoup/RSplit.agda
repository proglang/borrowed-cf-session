module BorrowedCF.Simulation.ForwardSoup.RSplit where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP
import Data.Vec.Properties as VecP
import Data.Vec.Relation.Unary.All as All

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
open import BorrowedCF.Processes.Renamings using (𝔽-cast-injective)
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open Typed using (_;_⊢ₚ_)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image
open import BorrowedCF.Simulation.Support.SplitConfine using (rsplit-confine)

open Nat.Variables
open Fin.Patterns

private
  plug*ˢ : SourceReduction.Frame* n → Source.Tm n → Source.Tm n
  plug*ˢ = SourceReduction._[_]*

  plug*ᵘ : SoupExpression.Frame* n → SoupTerm.Tm n → SoupTerm.Tm n
  plug*ᵘ = SoupExpression._[_]*

  chanTriple : SoupTerm.Tm n → 𝔽 n → SoupTerm.Tm n → SoupTerm.Tm n
  chanTriple e₁ x e₂ = Translation.chanTriple (e₁ , x , e₂)

  emptyEnv : Translation.Env 0 n
  emptyEnv ()

  ++ₛ-lookupˡ :
    ∀ {a b n} (sigma₁ : Translation.Env a n)
      (sigma₂ : Translation.Env b n) (i : 𝔽 a) →
    (sigma₁ Translation.++ₛ sigma₂) (i ↑ˡ b) ≡ sigma₁ i
  ++ₛ-lookupˡ {a = a} {b = b} sigma₁ sigma₂ i =
    cong [ sigma₁ , sigma₂ ]′ (Fin.splitAt-↑ˡ a i b)

  ++ₛ-lookupʳ :
    ∀ {a b n} (sigma₁ : Translation.Env a n)
      (sigma₂ : Translation.Env b n) (i : 𝔽 b) →
    (sigma₁ Translation.++ₛ sigma₂) (a ↑ʳ i) ≡ sigma₂ i
  ++ₛ-lookupʳ {a = a} {b = b} sigma₁ sigma₂ i =
    cong [ sigma₁ , sigma₂ ]′ (Fin.splitAt-↑ʳ a b i)

  ++ₛ-Value :
    ∀ {a b n} {sigma₁ : Translation.Env a n}
      {sigma₂ : Translation.Env b n} →
    ValueEnv sigma₁ → ValueEnv sigma₂ →
    ValueEnv (sigma₁ Translation.++ₛ sigma₂)
  ++ₛ-Value {a = a} Vsigma₁ Vsigma₂ i with Fin.splitAt a i
  ... | inj₁ x = Vsigma₁ x
  ... | inj₂ x = Vsigma₂ x

  chanTriple-value :
    ∀ {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
    SoupExpression.Value e₁ → SoupExpression.Value e₂ →
    SoupExpression.Value (Translation.chanTriple (e₁ , c , e₂))
  chanTriple-value V₁ V₂ =
    SoupExpression.V-⊗ (SoupExpression.V-⊗ V₁ SoupExpression.V-`) V₂

  Ub-Value :
    ∀ b {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
    SoupExpression.Value e₁ → SoupExpression.Value e₂ →
    ValueEnv (Translation.Ub[ b ] (e₁ , c , e₂))
  Ub-Value zero V₁ V₂ ()
  Ub-Value (suc zero) V₁ V₂ zero = chanTriple-value V₁ V₂
  Ub-Value (suc (suc b)) V₁ V₂ zero =
    chanTriple-value V₁ SoupExpression.V-K
  Ub-Value (suc (suc b)) V₁ V₂ (suc x) =
    Ub-Value (suc b) SoupExpression.V-K V₂ x

  UBFrom-Value :
    ∀ k (B : Typed.BindGroup) (r : 𝔽 n)
      {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
    SoupExpression.Value e₁ → SoupExpression.Value e₂ →
    ValueEnv (proj₁ (Translation.UBFrom k B r (e₁ , c , e₂)))
  UBFrom-Value k [] r V₁ V₂ ()
  UBFrom-Value k (b ∷ []) r {e₁} {e₂} {c} V₁ V₂ =
    subst
      (λ k → ValueEnv (Translation.Ub[ k ] (e₁ , c , e₂)))
      (sym (+-identityʳ b))
      (Ub-Value b V₁ V₂)
  UBFrom-Value k (b ∷ B@(b′ ∷ B′)) r {e₁} {e₂} {c} V₁ V₂ y
    with Translation.UBFrom (suc k) B r
           (SoupTerm.`phi (r , k) , c , e₂) in ubEq
       | UBFrom-Value (suc k) B r SoupExpression.V-phi V₂
  ... | sigma , flags | Vsigma with Fin.splitAt b y
  ...   | inj₁ x = Ub-Value b V₁ SoupExpression.V-phi x
  ...   | inj₂ x =
    subst SoupExpression.Value
      (cong (λ result → proj₁ result x) ubEq)
      (Vsigma x)

  UB-Value :
    ∀ (B : Typed.BindGroup) (r : 𝔽 n)
      {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
    SoupExpression.Value e₁ → SoupExpression.Value e₂ →
    ValueEnv (proj₁ (Translation.UB[ B ] r (e₁ , c , e₂)))
  UB-Value B = UBFrom-Value zero B

  leftGroup : Typed.BindGroup → ℕ → ℕ → Typed.BindGroup → Typed.BindGroup
  leftGroup B₁ q b₁ B₂ = B₁ ++ (q + suc b₁) ∷ B₂

  rightGroup : Typed.BindGroup → ℕ → ℕ → Typed.BindGroup → Typed.BindGroup
  rightGroup B₁ q b₁ B₂ = B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂

  channelCount-⋯ₚ :
    (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
    Translation.channelCount (Typed._⋯ₚ_ P ρ) ≡
    Translation.channelCount P
  channelCount-⋯ₚ (Typed.⟪ e ⟫) ρ = refl
  channelCount-⋯ₚ (P Typed.∥ Q) ρ =
    cong₂ _+_ (channelCount-⋯ₚ P ρ) (channelCount-⋯ₚ Q ρ)
  channelCount-⋯ₚ (Typed.ν B₁ B₂ P) ρ =
    cong suc (channelCount-⋯ₚ P (Source._↑*_ ρ (sum B₁ + sum B₂)))

  processCount-⋯ₚ :
    (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
    Translation.processCount (Typed._⋯ₚ_ P ρ) ≡
    Translation.processCount P
  processCount-⋯ₚ (Typed.⟪ e ⟫) ρ = refl
  processCount-⋯ₚ (P Typed.∥ Q) ρ =
    cong₂ _+_ (processCount-⋯ₚ P ρ) (processCount-⋯ₚ Q ρ)
  processCount-⋯ₚ (Typed.ν B₁ B₂ P) ρ =
    processCount-⋯ₚ P (Source._↑*_ ρ (sum B₁ + sum B₂))

  flatten-channel-open :
    ∀ {c} →
    (P : Typed.Proc n)
    (cs : Vec (𝔽 c) (Translation.channelCount P))
    (sigma : Translation.Env n (2 *ℕ c))
    (i : 𝔽 (Translation.channelCount P)) →
    proj₁ (lookup (proj₁ (Translation.flatten P cs sigma)) i) ≡ true
  flatten-channel-open (Typed.⟪ e ⟫) [] sigma ()
  flatten-channel-open (P Typed.∥ Q) cs sigma i
    with Translation.flatten P (V.take (Translation.channelCount P) cs) sigma in flatP
       | Translation.flatten Q (V.drop (Translation.channelCount P) cs) sigma in flatQ
       | Fin.splitAt (Translation.channelCount P) i in split
  ... | channels₁ , threads₁ | channels₂ , threads₂ | inj₁ j =
    subst
      (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
      (sym (cong (Fin.join (Translation.channelCount P)
                      (Translation.channelCount Q)) split) ■
       Fin.join-splitAt (Translation.channelCount P)
         (Translation.channelCount Q) i)
      (cong proj₁ (V.lookup-++ˡ channels₁ channels₂ j) ■
       cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatP) ■
       flatten-channel-open P
         (V.take (Translation.channelCount P) cs) sigma j)
  ... | channels₁ , threads₁ | channels₂ , threads₂ | inj₂ j =
    subst
      (λ k → proj₁ (lookup (channels₁ V.++ channels₂) k) ≡ true)
      (sym (cong (Fin.join (Translation.channelCount P)
                      (Translation.channelCount Q)) split) ■
       Fin.join-splitAt (Translation.channelCount P)
         (Translation.channelCount Q) i)
      (cong proj₁ (V.lookup-++ʳ channels₁ channels₂ j) ■
       cong (λ result → proj₁ (lookup (proj₁ result) j)) (sym flatQ) ■
       flatten-channel-open Q
         (V.drop (Translation.channelCount P) cs) sigma j)
  flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) sigma zero = refl
  flatten-channel-open (Typed.ν B₁ B₂ P) (i ∷ cs) sigma (suc j)
    with Translation.UB[ B₁ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)
       | Translation.UB[ B₂ ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)
  ... | sigma₁ , flags₁ | sigma₂ , flags₂ =
    flatten-channel-open P cs
      ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) j

  canonical-channel-open :
    (P : Typed.Proc 0) (i : 𝔽 (Translation.channelCount P)) →
    proj₁ (lookup (canonicalChannels P) i) ≡ true
  canonical-channel-open P i =
    flatten-channel-open P (V.allFin (Translation.channelCount P)) (λ ()) i

  image-channel-open :
    {P : Typed.Proc 0} {C : Soup.Config n m} →
    (image : SoupImage P C) (i : 𝔽 (Translation.channelCount P)) →
    proj₁ (lookup (Soup.channels C) (channelEmbedding image i)) ≡ true
  image-channel-open {P = P} image i =
    cong proj₁ (live-channel image i) ■ canonical-channel-open P i

  rsplitSource :
    ∀ B₁ B₂ B q b₁ →
    Types.𝕊 0 →
    SourceReduction.Frame* (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) →
    Typed.Proc (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) →
    Typed.Proc 0
  rsplitSource B₁ B₂ B q b₁ s E P =
    let module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B) in
    Typed.ν (leftGroup B₁ q b₁ B₂) B
      (Typed.⟪ plug*ˢ E
          (Source.K (Source.`rsplit s) Source.·¹
           (Source.` (𝐒.atk (q ↑ʳ 0F)))) ⟫
       Typed.∥ P)

  rsplitTarget :
    ∀ B₁ B₂ B q b₁ →
    Types.𝕊 0 →
    SourceReduction.Frame* (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) →
    Typed.Proc (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) →
    Typed.Proc 0
  rsplitTarget B₁ B₂ B q b₁ s E P =
    let module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B) in
    Typed.ν (rightGroup B₁ q b₁ B₂) B
      (Typed.⟪ plug*ˢ (E SourceReduction.⋯ᶠ* 𝐒.rwk)
          ((Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
            ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) Source.⊗
           (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
            ((q + 1) ↑ʳ 0F)))) ⟫
       Typed.∥ (P Typed.⋯ₚ 𝐒.rwk))

  sourceEnv :
    ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ c : ℕ} →
    𝔽 c →
    Translation.Env (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) (2 *ℕ c)
  sourceEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i =
    (proj₁
      (Translation.UB[ leftGroup B₁ q b₁ B₂ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
    Translation.++ₛ
    proj₁
      (Translation.UB[ B ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
    Translation.++ₛ (λ ())

  targetEnv :
    ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ c : ℕ} →
    𝔽 c →
    Translation.Env (sum (rightGroup B₁ q b₁ B₂) + sum B + 0) (2 *ℕ c)
  targetEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i =
    (proj₁
      (Translation.UB[ rightGroup B₁ q b₁ B₂ ] (Soup.leftEnd i)
        (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
    Translation.++ₛ
    proj₁
      (Translation.UB[ B ] (Soup.rightEnd i)
        (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
    Translation.++ₛ (λ ())

  sourceValueEnv :
    ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ c : ℕ} (i : 𝔽 c) →
    ValueEnv (sourceEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i)
  sourceValueEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value (leftGroup B₁ q b₁ B₂) (Soup.leftEnd i)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value B (Soup.rightEnd i)
          SoupExpression.V-K SoupExpression.V-K))
      (λ ())

  targetValueEnv :
    ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ c : ℕ} (i : 𝔽 c) →
    ValueEnv (targetEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i)
  targetValueEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value (rightGroup B₁ q b₁ B₂) (Soup.leftEnd i)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value B (Soup.rightEnd i)
          SoupExpression.V-K SoupExpression.V-K))
      (λ ())

  blockAt : ∀ B₁ B₂ w → 𝔽 w → 𝔽 (sum (B₁ ++ w ∷ B₂))
  blockAt [] B₂ w x = x ↑ˡ sum B₂
  blockAt (b ∷ B₁) B₂ w x = b ↑ʳ blockAt B₁ B₂ w x

  pos-split-gen :
    ∀ a B₁ c B₂ (i : 𝔽 (c + sum B₂)) →
    Fin.cast (sym (sum-++ (a ∷ B₁) (c ∷ B₂))) (sum (a ∷ B₁) ↑ʳ i) ≡
    a ↑ʳ Fin.cast (sym (sum-++ B₁ (c ∷ B₂))) (sum B₁ ↑ʳ i)
  pos-split-gen a B₁ c B₂ i = Fin.toℕ-injective
    ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁) (c ∷ B₂)))
        (sum (a ∷ B₁) ↑ʳ i)
    ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁)) i
    ■ +-assoc a (sum B₁) (Fin.toℕ i)
    ■ sym ( Fin.toℕ-↑ʳ a
              (Fin.cast (sym (sum-++ B₁ (c ∷ B₂))) (sum B₁ ↑ʳ i))
          ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ B₁ (c ∷ B₂)))
                             (sum B₁ ↑ʳ i)
                         ■ Fin.toℕ-↑ʳ (sum B₁) i ) ) )

  blockAt-cast :
    ∀ B₁ B₂ w (x : 𝔽 w) →
    blockAt B₁ B₂ w x ≡
    Fin.cast (sym (sum-++ B₁ (w ∷ B₂))) (sum B₁ ↑ʳ (x ↑ˡ sum B₂))
  blockAt-cast [] B₂ w x =
    sym (Fin.toℕ-injective
      ( Fin.toℕ-cast (sym (sum-++ [] (w ∷ B₂)))
          (sum [] ↑ʳ (x ↑ˡ sum B₂))
      ■ Fin.toℕ-↑ʳ (sum []) (x ↑ˡ sum B₂) ))
  blockAt-cast (b ∷ B₁) B₂ w x =
    cong (b ↑ʳ_) (blockAt-cast B₁ B₂ w x)
    ■ sym (pos-split-gen b B₁ w B₂ (x ↑ˡ sum B₂))

  atk-blockAt :
    ∀ B₁ B₂ B w (x : 𝔽 w) →
    let module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B) in
    𝐒.atk {w} {0} x ≡ blockAt B₁ B₂ w x ↑ˡ sum B ↑ˡ 0
  atk-blockAt B₁ B₂ B w x =
    cong (λ z → z ↑ˡ sum B ↑ˡ 0) (sym (blockAt-cast B₁ B₂ w x))

  endpoint-cast :
    ∀ {n n′ : ℕ} (eq : n ≡ n′) (i : 𝔽 n) side →
    Fin.cast (cong (2 *ℕ_) eq) (Soup.endpoint i side) ≡
    Soup.endpoint (Fin.cast eq i) side
  endpoint-cast refl i side =
    FinP.cast-is-id refl (Soup.endpoint i side)
    ■ cong (λ z → Soup.endpoint z side) (sym (FinP.cast-is-id refl i))

  cast-zero :
    ∀ {m n : ℕ} (eq : suc m ≡ suc n) →
    Fin.cast eq 0F ≡ 0F
  cast-zero refl = FinP.cast-is-id refl 0F

  UBFrom-flags-cong :
    ∀ k (B : Typed.BindGroup) {n₁ n₂ : ℕ}
      (r₁ : 𝔽 n₁) (c₁ : Translation.UChan n₁)
      (r₂ : 𝔽 n₂) (c₂ : Translation.UChan n₂) →
    proj₂ (Translation.UBFrom k B r₁ c₁) ≡
    proj₂ (Translation.UBFrom k B r₂ c₂)
  UBFrom-flags-cong k [] r₁ c₁ r₂ c₂ = refl
  UBFrom-flags-cong k (b ∷ []) r₁ c₁ r₂ c₂ = refl
  UBFrom-flags-cong k (b ∷ B@(b′ ∷ B′)) r₁ (e₁ , c₁ , e₂) r₂ (e₁′ , c₂ , e₂′)
    with Translation.UBFrom (suc k) B r₁
           (SoupTerm.`phi (r₁ , k) , c₁ , e₂)
       | Translation.UBFrom (suc k) B r₂
           (SoupTerm.`phi (r₂ , k) , c₂ , e₂′)
       | UBFrom-flags-cong (suc k) B r₁
           (SoupTerm.`phi (r₁ , k) , c₁ , e₂)
           r₂
           (SoupTerm.`phi (r₂ , k) , c₂ , e₂′)
  ... | σ₁ , fs₁ | σ₂ , fs₂ | eq =
    cong (Translation.ϕ[ b ] ∷_) eq

  UB-flags-cong :
    ∀ (B : Typed.BindGroup) {n₁ n₂ : ℕ}
      (r₁ : 𝔽 n₁) (c₁ : Translation.UChan n₁)
      (r₂ : 𝔽 n₂) (c₂ : Translation.UChan n₂) →
    proj₂ (Translation.UB[ B ] r₁ c₁) ≡
    proj₂ (Translation.UB[ B ] r₂ c₂)
  UB-flags-cong B = UBFrom-flags-cong zero B

  positive-flag : ∀ q b →
    Translation.ϕ[ q + suc b ] ≡ Soup.drop
  positive-flag zero b = refl
  positive-flag (suc q) b = refl

  bindFlags : Typed.BindGroup → List Soup.Flag
  bindFlags [] = []
  bindFlags (b ∷ []) = []
  bindFlags (b ∷ B@(_ ∷ _)) = Translation.ϕ[ b ] ∷ bindFlags B

  UBFrom-flags-shape :
    ∀ k (B : Typed.BindGroup) {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    proj₂ (Translation.UBFrom k B r (e₁ , c , e₂)) ≡ bindFlags B
  UBFrom-flags-shape k [] r c e₁ e₂ = refl
  UBFrom-flags-shape k (b ∷ []) r c e₁ e₂ = refl
  UBFrom-flags-shape k (b ∷ B@(b′ ∷ B′)) r c e₁ e₂
    with Translation.UBFrom (suc k) B r
           (SoupTerm.`phi (r , k) , c , e₂)
       | UBFrom-flags-shape (suc k) B r c
           (SoupTerm.`phi (r , k)) e₂
  ... | σ , fs | eq = cong (Translation.ϕ[ b ] ∷_) eq

  UB-flags-shape :
    ∀ (B : Typed.BindGroup) {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    proj₂ (Translation.UB[ B ] r (e₁ , c , e₂)) ≡ bindFlags B
  UB-flags-shape B = UBFrom-flags-shape zero B

  bindFlags-rsplit : ∀ B₁ B₂ q b →
    bindFlags (leftGroup B₁ q b B₂) ++ Soup.drop ∷ [] ≡
    bindFlags (rightGroup B₁ q b B₂)
  bindFlags-rsplit B₁ B₂ q b = {!!}

  channelShape :
    (P : Typed.Proc n) → Vec Soup.Channel (Translation.channelCount P)
  channelShape (Typed.⟪ e ⟫) = []
  channelShape (P Typed.∥ Q) = channelShape P V.++ channelShape Q
  channelShape (Typed.ν B₁ B₂ P) =
    (true , bindFlags B₁ , bindFlags B₂) ∷ channelShape P

  flatten-channels-shape :
    ∀ {c : ℕ} (P : Typed.Proc n)
    (cs : Vec (𝔽 c) (Translation.channelCount P))
    (σ : Translation.Env n (2 *ℕ c)) →
    proj₁ (Translation.flatten P cs σ) ≡ channelShape P
  flatten-channels-shape (Typed.⟪ e ⟫) [] σ = refl
  flatten-channels-shape (P Typed.∥ Q) cs σ
    with Translation.flatten P (V.take (Translation.channelCount P) cs) σ
       | Translation.flatten Q (V.drop (Translation.channelCount P) cs) σ
       | flatten-channels-shape P
           (V.take (Translation.channelCount P) cs) σ
       | flatten-channels-shape Q
           (V.drop (Translation.channelCount P) cs) σ
  ... | channels₁ , threads₁ | channels₂ , threads₂ | eq₁ | eq₂ =
    cong₂ V._++_ eq₁ eq₂
  flatten-channels-shape (Typed.ν B₁ B₂ P) (i ∷ cs) σ
    rewrite UB-flags-shape B₁ (Soup.leftEnd i) (Soup.leftEnd i)
              SoupTerm.* SoupTerm.*
          | UB-flags-shape B₂ (Soup.rightEnd i) (Soup.rightEnd i)
              SoupTerm.* SoupTerm.*
    with Translation.UB[ B₁ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)
       | Translation.UB[ B₂ ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)
       | flatten-channels-shape P cs
           ((proj₁ (Translation.UB[ B₁ ] (Soup.leftEnd i)
               (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
             Translation.++ₛ
             proj₁ (Translation.UB[ B₂ ] (Soup.rightEnd i)
               (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
            Translation.++ₛ σ)
  ... | σ₁ , fs₁ | σ₂ , fs₂ | eq =
    cong ((true , bindFlags B₁ , bindFlags B₂) ∷_) eq

  cast-++ :
    ∀ {A : Set} {a a′ b b′ : ℕ}
      (ea : a ≡ a′) (eb : b ≡ b′)
      (xs : Vec A a) (ys : Vec A b) →
    V.cast (cong₂ _+_ ea eb) (xs V.++ ys) ≡
    V.cast ea xs V.++ V.cast eb ys
  cast-++ refl refl xs ys =
    VecP.cast-is-id refl (xs V.++ ys)
    ■ cong₂ V._++_
        (sym (VecP.cast-is-id refl xs))
        (sym (VecP.cast-is-id refl ys))

  cast-∷ :
    ∀ {A : Set} {a a′ : ℕ} (e : a ≡ a′) (x : A) (xs : Vec A a) →
    V.cast (cong suc e) (x ∷ xs) ≡ x ∷ V.cast e xs
  cast-∷ refl x xs =
    VecP.cast-is-id refl (x ∷ xs)
    ■ cong (x ∷_) (sym (VecP.cast-is-id refl xs))

  channelShape-⋯ₚ :
    (P : Typed.Proc n) (θ : 𝔽 n → 𝔽 n′) →
    V.cast (channelCount-⋯ₚ P θ)
      (channelShape (P Typed.⋯ₚ θ)) ≡ channelShape P
  channelShape-⋯ₚ (Typed.⟪ e ⟫) θ = VecP.cast-is-id refl []
  channelShape-⋯ₚ (P Typed.∥ Q) θ =
    cast-++ (channelCount-⋯ₚ P θ) (channelCount-⋯ₚ Q θ)
      (channelShape (P Typed.⋯ₚ θ))
      (channelShape (Q Typed.⋯ₚ θ))
    ■ cong₂ V._++_
        (channelShape-⋯ₚ P θ)
        (channelShape-⋯ₚ Q θ)
  channelShape-⋯ₚ (Typed.ν B₁ B₂ P) θ =
    cast-∷ (channelCount-⋯ₚ P (Source._↑*_ θ (sum B₁ + sum B₂)))
      (true , bindFlags B₁ , bindFlags B₂)
      (channelShape
        (P Typed.⋯ₚ Source._↑*_ θ (sum B₁ + sum B₂)))
    ■ cong ((true , bindFlags B₁ , bindFlags B₂) ∷_)
        (channelShape-⋯ₚ P (Source._↑*_ θ (sum B₁ + sum B₂)))

  UBFrom-lookupʳ :
    ∀ k b B {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
    proj₁ (Translation.UBFrom k (b ∷ B) r (e₁ , c , e₂)) (b ↑ʳ x) ≡
    proj₁ (Translation.UBFrom (suc k) B r
      (SoupTerm.`phi (r , k) , c , e₂)) x
  UBFrom-lookupʳ k b [] r c e₁ e₂ ()
  UBFrom-lookupʳ k b (b′ ∷ B) r c e₁ e₂ x
    with Translation.UBFrom (suc k) (b′ ∷ B) r
           (SoupTerm.`phi (r , k) , c , e₂)
  ... | σ , flags =
    ++ₛ-lookupʳ
      (Translation.Ub[ b ] (e₁ , c ,
        SoupTerm.`phi (r , k)))
      σ x

  UB-lookupʳ :
    ∀ b B {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) (x : 𝔽 (sum B)) →
    proj₁ (Translation.UB[ b ∷ B ] r (e₁ , c , e₂)) (b ↑ʳ x) ≡
    proj₁ (Translation.UBFrom 1 B r
      (SoupTerm.`phi (r , 0) , c , e₂)) x
  UB-lookupʳ b B = UBFrom-lookupʳ zero b B

  ub-at :
    ∀ w {n : ℕ} (p : 𝔽 w) (c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    Σ[ e₁′ ∈ SoupTerm.Tm n ]
    Σ[ e₂′ ∈ SoupTerm.Tm n ]
      Translation.Ub[ w ] (e₁ , c , e₂) p ≡
      chanTriple e₁′ c e₂′
  ub-at zero ()
  ub-at (suc zero) zero c e₁ e₂ =
    e₁ , e₂ , refl
  ub-at (suc (suc w)) zero c e₁ e₂ =
    e₁ , SoupTerm.* , refl
  ub-at (suc (suc w)) (suc p) c e₁ e₂ =
    ub-at (suc w) p c SoupTerm.* e₂

  ub-+0 :
    ∀ w {n : ℕ} (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) (p : 𝔽 w) →
    Translation.Ub[ w + 0 ] (e₁ , c , e₂) (p ↑ˡ 0) ≡
    Translation.Ub[ w ] (e₁ , c , e₂) p
  ub-+0 zero c e₁ e₂ ()
  ub-+0 (suc zero) c e₁ e₂ zero = refl
  ub-+0 (suc (suc w)) c e₁ e₂ zero = refl
  ub-+0 (suc (suc w)) c e₁ e₂ (suc p) =
    ub-+0 (suc w) c SoupTerm.* e₂ p

  ub-suc-zero :
    ∀ q b {n : ℕ} (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
    Translation.Ub[ suc q + suc b ] (e₁ , c , e₂) (suc q ↑ʳ 0F) ≡
    Translation.Ub[ q + suc b ] (SoupTerm.* , c , e₂) (q ↑ʳ 0F)
  ub-suc-zero zero b c e₁ e₂ = refl
  ub-suc-zero (suc q) b c e₁ e₂ = refl

  ub-suc-zero′ :
    ∀ q b {n : ℕ} (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
    Translation.Ub[ suc q + suc (suc b) ] (e₁ , c , e₂) (suc q ↑ʳ 0F) ≡
    Translation.Ub[ q + suc (suc b) ] (SoupTerm.* , c , e₂) (q ↑ʳ 0F)
  ub-suc-zero′ zero b c e₁ e₂ = refl
  ub-suc-zero′ (suc q) b c e₁ e₂ = refl

  ub-suc-one′ :
    ∀ q b {n : ℕ} (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
    Translation.Ub[ suc q + suc (suc b) ] (e₁ , c , e₂) (suc q ↑ʳ 1F) ≡
    Translation.Ub[ q + suc (suc b) ] (SoupTerm.* , c , e₂) (q ↑ʳ 1F)
  ub-suc-one′ zero b c e₁ e₂ = refl
  ub-suc-one′ (suc q) b c e₁ e₂ = refl

  ub-lsplit :
    ∀ q b {n : ℕ} (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n) →
    Σ[ e₁′ ∈ SoupTerm.Tm n ]
    Σ[ e₂′ ∈ SoupTerm.Tm n ]
      (Translation.Ub[ q + suc b ] (e₁ , c , e₂) (q ↑ʳ 0F) ≡
       chanTriple e₁′ c e₂′)
    × (Translation.Ub[ q + suc (suc b) ] (e₁ , c , e₂) (q ↑ʳ 0F) ≡
       chanTriple e₁′ c SoupTerm.*)
    × (Translation.Ub[ q + suc (suc b) ] (e₁ , c , e₂) (q ↑ʳ 1F) ≡
       chanTriple SoupTerm.* c e₂′)
  ub-lsplit zero zero c e₁ e₂ =
    e₁ , e₂ , refl , refl , refl
  ub-lsplit zero (suc b) c e₁ e₂ =
    e₁ , SoupTerm.* , refl , refl , refl
  ub-lsplit (suc q) b c e₁ e₂
    with ub-lsplit q b c SoupTerm.* e₂
  ... | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
    e₁′ , e₂′ ,
    (ub-suc-zero q b c e₁ e₂ ■ eq₀) ,
    (ub-suc-zero′ q b c e₁ e₂ ■ eq₁) ,
    (ub-suc-one′ q b c e₁ e₂ ■ eq₂)

  ub-witness-ren :
    ∀ q b {n n′ n″ : ℕ}
      (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n)
      (c′ : 𝔽 n′) (e₁′ e₂′ : SoupTerm.Tm n′)
      (ρ : 𝔽 n → 𝔽 n″) (τ : 𝔽 n′ → 𝔽 n″) →
    e₁ SoupTerm.⋯ᵣ ρ ≡ e₁′ SoupTerm.⋯ᵣ τ →
    e₂ SoupTerm.⋯ᵣ ρ ≡ e₂′ SoupTerm.⋯ᵣ τ →
    ρ c ≡ τ c′ →
    (proj₁ (ub-lsplit q b c e₁ e₂) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (ub-lsplit q b c′ e₁′ e₂′) SoupTerm.⋯ᵣ τ)
    ×
    (proj₁ (proj₂ (ub-lsplit q b c e₁ e₂)) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (proj₂ (ub-lsplit q b c′ e₁′ e₂′)) SoupTerm.⋯ᵣ τ)
  ub-witness-ren zero zero c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq =
    e₁eq , e₂eq
  ub-witness-ren zero (suc b) c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq =
    e₁eq , refl
  ub-witness-ren (suc q) b c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq =
    ub-witness-ren q b c SoupTerm.* e₂ c′ SoupTerm.* e₂′ ρ τ refl e₂eq ceq

  group-lsplit-shape-from :
    ∀ k B₁ B₂ q b {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    Σ[ e₁′ ∈ SoupTerm.Tm n ]
    Σ[ e₂′ ∈ SoupTerm.Tm n ]
      (proj₁ (Translation.UBFrom k (B₁ ++ (q + suc b) ∷ B₂) r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ c e₂′)
    × (proj₁ (Translation.UBFrom k (B₁ ++ (q + suc (suc b)) ∷ B₂) r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ c SoupTerm.*)
    × (proj₁ (Translation.UBFrom k (B₁ ++ (q + suc (suc b)) ∷ B₂) r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F)) ≡
       chanTriple SoupTerm.* c e₂′)
  group-lsplit-shape-from k [] [] q b r c e₁ e₂ =
    let h = ub-lsplit q b c e₁ e₂ in
    proj₁ h , proj₁ (proj₂ h) ,
    (ub-+0 (q + suc b) c e₁ e₂ (q ↑ʳ 0F)
     ■ proj₁ (proj₂ (proj₂ h))) ,
    (ub-+0 (q + suc (suc b)) c e₁ e₂ (q ↑ʳ 0F)
     ■ proj₁ (proj₂ (proj₂ (proj₂ h)))) ,
    (ub-+0 (q + suc (suc b)) c e₁ e₂ (q ↑ʳ 1F)
     ■ proj₂ (proj₂ (proj₂ (proj₂ h))))
  group-lsplit-shape-from k [] (b₂ ∷ B₂) q b r c e₁ e₂
    with Translation.UBFrom (suc k) (b₂ ∷ B₂) r
           (SoupTerm.`phi (r , k) , c , e₂)
       | ub-lsplit q b c e₁
           (SoupTerm.`phi (r , k))
  ... | σ , flags | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
    e₁′ , e₂′ ,
    (++ₛ-lookupˡ
      (Translation.Ub[ q + suc b ] (e₁ , c ,
        SoupTerm.`phi (r , k)))
      σ (q ↑ʳ 0F)
     ■ eq₀) ,
    (++ₛ-lookupˡ
      (Translation.Ub[ q + suc (suc b) ] (e₁ , c ,
        SoupTerm.`phi (r , k)))
      σ (q ↑ʳ 0F)
     ■ eq₁) ,
    (++ₛ-lookupˡ
      (Translation.Ub[ q + suc (suc b) ] (e₁ , c ,
        SoupTerm.`phi (r , k)))
      σ (q ↑ʳ 1F)
     ■ eq₂)
  group-lsplit-shape-from k (b₀ ∷ B₁) B₂ q b r c e₁ e₂
    with Translation.UBFrom (suc k) (B₁ ++ (q + suc b) ∷ B₂) r
           (SoupTerm.`phi (r , k) , c , e₂) in ubEq
       | Translation.UBFrom (suc k) (B₁ ++ (q + suc (suc b)) ∷ B₂) r
           (SoupTerm.`phi (r , k) , c , e₂) in ubEq′
       | group-lsplit-shape-from (suc k) B₁ B₂ q b r c
           (SoupTerm.`phi (r , k))
           e₂
  ... | σ₀ , flags₀ | σ₁ , flags₁ | e₁′ , e₂′ , eq₀ , eq₁ , eq₂ =
    e₁′ , e₂′ ,
    let z₀ = blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)
        z₁ = blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F)
        z₂ = blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F)
    in
    (UBFrom-lookupʳ k b₀ (B₁ ++ (q + suc b) ∷ B₂) r c e₁ e₂ z₀
     ■ cong (λ result → proj₁ result z₀) ubEq
     ■ eq₀) ,
    (UBFrom-lookupʳ k b₀ (B₁ ++ (q + suc (suc b)) ∷ B₂) r c e₁ e₂ z₁
     ■ cong (λ result → proj₁ result z₁) ubEq′
     ■ eq₁) ,
    (UBFrom-lookupʳ k b₀ (B₁ ++ (q + suc (suc b)) ∷ B₂) r c e₁ e₂ z₂
     ■ cong (λ result → proj₁ result z₂) ubEq′
     ■ eq₂)

  group-lsplit-shape :
    ∀ B₁ B₂ q b {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    Σ[ e₁′ ∈ SoupTerm.Tm n ]
    Σ[ e₂′ ∈ SoupTerm.Tm n ]
      (proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ c e₂′)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b)) ∷ B₂ ] r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ c SoupTerm.*)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b)) ∷ B₂ ] r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc (suc b)) (q ↑ʳ 1F)) ≡
       chanTriple SoupTerm.* c e₂′)
  group-lsplit-shape = group-lsplit-shape-from zero

  group-lsplit :
    ∀ B₁ B₂ q b {n : ℕ} (r c : 𝔽 n)
      (e₁ e₂ : SoupTerm.Tm n) →
    Σ[ e₁′ ∈ SoupTerm.Tm n ]
    Σ[ e₂′ ∈ SoupTerm.Tm n ]
      proj₁ (Translation.UB[ B₁ ++ (q + suc b) ∷ B₂ ] r
        (e₁ , c , e₂))
        (blockAt B₁ B₂ (q + suc b) (q ↑ʳ 0F)) ≡
      chanTriple e₁′ c e₂′
  group-lsplit B₁ B₂ q b r c e₁ e₂ =
    let h = group-lsplit-shape B₁ B₂ q b r c e₁ e₂ in
    proj₁ h , proj₁ (proj₂ h) , proj₁ (proj₂ (proj₂ h))

  group-witness-ren-from :
    ∀ k B₁ B₂ q b {n n′ n″ : ℕ}
      (r c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n)
      (r′ c′ : 𝔽 n′) (e₁′ e₂′ : SoupTerm.Tm n′)
      (ρ : 𝔽 n → 𝔽 n″) (τ : 𝔽 n′ → 𝔽 n″) →
    e₁ SoupTerm.⋯ᵣ ρ ≡ e₁′ SoupTerm.⋯ᵣ τ →
    e₂ SoupTerm.⋯ᵣ ρ ≡ e₂′ SoupTerm.⋯ᵣ τ →
    ρ r ≡ τ r′ →
    ρ c ≡ τ c′ →
    (proj₁ (group-lsplit-shape-from k B₁ B₂ q b r c e₁ e₂) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (group-lsplit-shape-from k B₁ B₂ q b r′ c′ e₁′ e₂′) SoupTerm.⋯ᵣ τ)
    ×
    (proj₁ (proj₂ (group-lsplit-shape-from k B₁ B₂ q b r c e₁ e₂)) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (proj₂ (group-lsplit-shape-from k B₁ B₂ q b r′ c′ e₁′ e₂′)) SoupTerm.⋯ᵣ τ)
  group-witness-ren-from k [] [] q b r c e₁ e₂ r′ c′ e₁′ e₂′ ρ τ e₁eq e₂eq req ceq =
    ub-witness-ren q b c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq
  group-witness-ren-from k [] (b₂ ∷ B₂) q b r c e₁ e₂ r′ c′ e₁′ e₂′ ρ τ e₁eq e₂eq req ceq =
    ub-witness-ren q b c e₁
      (SoupTerm.`phi (r , k))
      c′ e₁′
      (SoupTerm.`phi (r′ , k))
      ρ τ e₁eq
      (cong SoupTerm.`phi (cong (λ z → z , k) req))
      ceq
  group-witness-ren-from k (b₀ ∷ B₁) B₂ q b r c e₁ e₂ r′ c′ e₁′ e₂′ ρ τ e₁eq e₂eq req ceq =
    group-witness-ren-from (suc k) B₁ B₂ q b r c
      (SoupTerm.`phi (r , k))
      e₂
      r′ c′
      (SoupTerm.`phi (r′ , k))
      e₂′
      ρ τ
      (cong SoupTerm.`phi
        (cong (λ z → z , k) req))
      e₂eq req ceq

  group-witness-ren :
    ∀ B₁ B₂ q b {n n′ n″ : ℕ}
      (r c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n)
      (r′ c′ : 𝔽 n′) (e₁′ e₂′ : SoupTerm.Tm n′)
      (ρ : 𝔽 n → 𝔽 n″) (τ : 𝔽 n′ → 𝔽 n″) →
    e₁ SoupTerm.⋯ᵣ ρ ≡ e₁′ SoupTerm.⋯ᵣ τ →
    e₂ SoupTerm.⋯ᵣ ρ ≡ e₂′ SoupTerm.⋯ᵣ τ →
    ρ r ≡ τ r′ →
    ρ c ≡ τ c′ →
    (proj₁ (group-lsplit-shape B₁ B₂ q b r c e₁ e₂) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (group-lsplit-shape B₁ B₂ q b r′ c′ e₁′ e₂′) SoupTerm.⋯ᵣ τ)
    ×
    (proj₁ (proj₂ (group-lsplit-shape B₁ B₂ q b r c e₁ e₂)) SoupTerm.⋯ᵣ ρ ≡
     proj₁ (proj₂ (group-lsplit-shape B₁ B₂ q b r′ c′ e₁′ e₂′)) SoupTerm.⋯ᵣ τ)
  group-witness-ren = group-witness-ren-from zero

  chanTriple-ren :
    ∀ {n n′ n″ : ℕ}
      (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n)
      (c′ : 𝔽 n′) (e₁′ e₂′ : SoupTerm.Tm n′)
      (ρ : 𝔽 n → 𝔽 n″) (τ : 𝔽 n′ → 𝔽 n″) →
    e₁ SoupTerm.⋯ᵣ ρ ≡ e₁′ SoupTerm.⋯ᵣ τ →
    e₂ SoupTerm.⋯ᵣ ρ ≡ e₂′ SoupTerm.⋯ᵣ τ →
    ρ c ≡ τ c′ →
    chanTriple e₁ c e₂ SoupTerm.⋯ᵣ ρ ≡
    chanTriple e₁′ c′ e₂′ SoupTerm.⋯ᵣ τ
  chanTriple-ren c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq =
    cong₂ SoupTerm._⊗_
      (cong₂ SoupTerm._⊗_ e₁eq (cong (λ z → SoupTerm.` z) ceq))
      e₂eq

  Ub-env-ren :
    ∀ w {n n′ n″ : ℕ}
      (c : 𝔽 n) (e₁ e₂ : SoupTerm.Tm n)
      (c′ : 𝔽 n′) (e₁′ e₂′ : SoupTerm.Tm n′)
      (ρ : 𝔽 n → 𝔽 n″) (τ : 𝔽 n′ → 𝔽 n″) →
    e₁ SoupTerm.⋯ᵣ ρ ≡ e₁′ SoupTerm.⋯ᵣ τ →
    e₂ SoupTerm.⋯ᵣ ρ ≡ e₂′ SoupTerm.⋯ᵣ τ →
    ρ c ≡ τ c′ →
    (x : 𝔽 w) →
    Translation.Ub[ w ] (e₁ , c , e₂) x SoupTerm.⋯ᵣ ρ ≡
    Translation.Ub[ w ] (e₁′ , c′ , e₂′) x SoupTerm.⋯ᵣ τ
  Ub-env-ren zero c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq ()
  Ub-env-ren (suc zero) c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq zero =
    chanTriple-ren c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq
  Ub-env-ren (suc (suc w)) c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq zero =
    chanTriple-ren c e₁ SoupTerm.* c′ e₁′ SoupTerm.* ρ τ e₁eq refl ceq
  Ub-env-ren (suc (suc w)) c e₁ e₂ c′ e₁′ e₂′ ρ τ e₁eq e₂eq ceq (suc x) =
    Ub-env-ren (suc w) c SoupTerm.* e₂ c′ SoupTerm.* e₂′
      ρ τ refl e₂eq ceq x

  lookup-left-at₀ :
    ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ c : ℕ} (i : 𝔽 c) →
    let x = blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F) ↑ˡ sum B ↑ˡ 0 in
    Σ[ e₁ ∈ SoupTerm.Tm (2 *ℕ c) ]
    Σ[ e₂ ∈ SoupTerm.Tm (2 *ℕ c) ]
      sourceEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i x ≡
      chanTriple e₁ (Soup.leftEnd i) e₂
  lookup-left-at₀ {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} i =
    let h = group-lsplit B₁ B₂ q b₁ (Soup.leftEnd i) (Soup.leftEnd i)
              SoupTerm.* SoupTerm.*
    in proj₁ h , proj₁ (proj₂ h) ,
       (++ₛ-lookupˡ
         (proj₁ (Translation.UB[ leftGroup B₁ q b₁ B₂ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*))
          Translation.++ₛ
          proj₁ (Translation.UB[ B ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
         (λ ())
         (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F) ↑ˡ sum B)
       ■ ++ₛ-lookupˡ
         (proj₁ (Translation.UB[ leftGroup B₁ q b₁ B₂ ] (Soup.leftEnd i)
           (SoupTerm.* , Soup.leftEnd i , SoupTerm.*)))
         (proj₁ (Translation.UB[ B ] (Soup.rightEnd i)
           (SoupTerm.* , Soup.rightEnd i , SoupTerm.*)))
         (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F))
       ■ proj₂ (proj₂ h))

U-rsplit :
  ∀ {B₁ B₂ B : Typed.BindGroup} {q b₁ : ℕ} {s : Types.𝕊 0}
    {E : SourceReduction.Frame*
           (sum (leftGroup B₁ q b₁ B₂) + sum B + 0)}
    {P : Typed.Proc (sum (leftGroup B₁ q b₁ B₂) + sum B + 0)}
    {n m : ℕ} {C : Soup.Config n m} →
  V.[] ; Context.[]
    ⊢ₚ rsplitSource B₁ B₂ B q b₁ s E P →
  SoupImage (rsplitSource B₁ B₂ B q b₁ s E P) C →
  Σ[ C′ ∈ Soup.Config n m ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (rsplitTarget B₁ B₂ B q b₁ s E P) C′
U-rsplit {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁}
  {s = s} {E = E} {P = P} {n = n} {m = m} {C = C} ⊢P image
  with rsplit-confine All.[]
    {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁}
    {s = s} {E = E} {P = P} ⊢P
... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq =
  C′ ,
  {!!} ,
  record
    { channelEmbedding = channelEmbedding′
    ; channelEmbedding-injective = channelEmbedding-injective′
    ; threadEmbedding = threadEmbedding′
    ; threadEmbedding-injective = threadEmbedding-injective′
    ; endpointEmbedding = endpointEmbedding′
    ; endpoint-respects-channel = endpoint-respects-channel′
    ; live-channel = live-channel′
    ; live-thread = live-thread′
    ; garbage-channel = garbage-channel′
    ; garbage-thread = garbage-thread′
    }
  where
  SourceProc TargetProc : Typed.Proc 0
  SourceProc = rsplitSource B₁ B₂ B q b₁ s E P
  TargetProc = rsplitTarget B₁ B₂ B q b₁ s E P

  module 𝐒 = Source.SplitRenamings B₁ B₂ (sum B)

  channelCountEq :
    Translation.channelCount TargetProc ≡ Translation.channelCount SourceProc
  channelCountEq = cong suc (channelCount-⋯ₚ P 𝐒.rwk)

  processCountEq :
    Translation.processCount TargetProc ≡ Translation.processCount SourceProc
  processCountEq = cong suc (processCount-⋯ₚ P 𝐒.rwk)

  channelEmbedding′ :
    𝔽 (Translation.channelCount TargetProc) → 𝔽 n
  channelEmbedding′ l = channelEmbedding image (Fin.cast channelCountEq l)

  channelEmbedding-injective′ :
    ∀ {l k} →
    channelEmbedding′ l ≡ channelEmbedding′ k → l ≡ k
  channelEmbedding-injective′ eq =
    𝔽-cast-injective channelCountEq (channelEmbedding-injective image eq)

  threadEmbedding′ :
    𝔽 (Translation.processCount TargetProc) → 𝔽 m
  threadEmbedding′ l = threadEmbedding image (Fin.cast processCountEq l)

  threadEmbedding-injective′ :
    ∀ {l k} →
    threadEmbedding′ l ≡ threadEmbedding′ k → l ≡ k
  threadEmbedding-injective′ eq =
    𝔽-cast-injective processCountEq (threadEmbedding-injective image eq)

  endpointCountEq :
    2 *ℕ Translation.channelCount TargetProc ≡
    2 *ℕ Translation.channelCount SourceProc
  endpointCountEq = cong (2 *ℕ_) channelCountEq

  endpointEmbedding′ :
    𝔽 (2 *ℕ Translation.channelCount TargetProc) → 𝔽 (2 *ℕ n)
  endpointEmbedding′ x = endpointEmbedding image (Fin.cast endpointCountEq x)

  ρ : 𝔽 (2 *ℕ Translation.channelCount SourceProc) → 𝔽 (2 *ℕ n)
  ρ = endpointEmbedding image

  endpoint-respects-channel′ :
    ∀ i side →
    endpointEmbedding′ (Soup.endpoint i side) ≡
    Soup.endpoint (channelEmbedding′ i) side
  endpoint-respects-channel′ i side =
    cong ρ (endpoint-cast channelCountEq i side)
    ■ endpoint-respects-channel image (Fin.cast channelCountEq i) side

  j : 𝔽 m
  j = threadEmbedding′ 0F

  i : 𝔽 n
  i = channelEmbedding′ 0F

  σ₀ : Translation.Env (sum (leftGroup B₁ q b₁ B₂) + sum B + 0)
         (2 *ℕ Translation.channelCount SourceProc)
  σ₀ = sourceEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} 0F

  Vσ₀ : ValueEnv σ₀
  Vσ₀ = sourceValueEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} 0F

  τ₀ : Translation.Env (sum (rightGroup B₁ q b₁ B₂) + sum B + 0)
         (2 *ℕ Translation.channelCount TargetProc)
  τ₀ = targetEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} 0F

  τ : Translation.Env (sum (rightGroup B₁ q b₁ B₂) + sum B + 0) (2 *ℕ n)
  τ x = τ₀ x SoupTerm.⋯ᵣ endpointEmbedding′

  Vτ : ValueEnv τ
  Vτ x =
    SoupExpression.value-rename
      (targetValueEnv {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} 0F x)
      endpointEmbedding′

  σ : Translation.Env (sum (leftGroup B₁ q b₁ B₂) + sum B + 0) (2 *ℕ n)
  σ x = σ₀ x SoupTerm.⋯ᵣ ρ

  Vσ : ValueEnv σ
  Vσ x = SoupExpression.value-rename (Vσ₀ x) ρ

  F : SoupExpression.Frame* (2 *ℕ n)
  F = Tᶠ*[ E ] {σ = σ} Vσ

  x : 𝔽 (sum (leftGroup B₁ q b₁ B₂) + sum B + 0)
  x = 𝐒.atk {q + suc b₁} {0} (q ↑ʳ 0F)

  sourceSplitShape :
    Σ[ e₁′ ∈ SoupTerm.Tm (2 *ℕ Translation.channelCount SourceProc) ]
    Σ[ e₂′ ∈ SoupTerm.Tm (2 *ℕ Translation.channelCount SourceProc) ]
      (proj₁ (Translation.UB[ B₁ ++ (q + suc b₁) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ (Soup.leftEnd 0F) e₂′)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b₁)) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ (Soup.leftEnd 0F) SoupTerm.*)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b₁)) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 1F)) ≡
       chanTriple SoupTerm.* (Soup.leftEnd 0F) e₂′)
  sourceSplitShape =
    group-lsplit-shape B₁ B₂ q b₁
      (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
      (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
      SoupTerm.* SoupTerm.*

  e₁⁰ e₂⁰ : SoupTerm.Tm (2 *ℕ Translation.channelCount SourceProc)
  e₁⁰ = proj₁ sourceSplitShape
  e₂⁰ = proj₁ (proj₂ sourceSplitShape)

  e₁ e₂ : SoupTerm.Tm (2 *ℕ n)
  e₁ = e₁⁰ SoupTerm.⋯ᵣ ρ
  e₂ = e₂⁰ SoupTerm.⋯ᵣ ρ

  targetSplitShape :
    Σ[ e₁′ ∈ SoupTerm.Tm (2 *ℕ Translation.channelCount TargetProc) ]
    Σ[ e₂′ ∈ SoupTerm.Tm (2 *ℕ Translation.channelCount TargetProc) ]
      (proj₁ (Translation.UB[ B₁ ++ (q + suc b₁) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc b₁) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ (Soup.leftEnd 0F) e₂′)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b₁)) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 0F)) ≡
       chanTriple e₁′ (Soup.leftEnd 0F) SoupTerm.*)
    × (proj₁ (Translation.UB[ B₁ ++ (q + suc (suc b₁)) ∷ B₂ ]
        (Soup.leftEnd 0F)
        (SoupTerm.* , Soup.leftEnd 0F , SoupTerm.*))
        (blockAt B₁ B₂ (q + suc (suc b₁)) (q ↑ʳ 1F)) ≡
       chanTriple SoupTerm.* (Soup.leftEnd 0F) e₂′)
  targetSplitShape =
    group-lsplit-shape B₁ B₂ q b₁
      (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
      (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
      SoupTerm.* SoupTerm.*

  e₁ᵗ e₂ᵗ : SoupTerm.Tm (2 *ℕ Translation.channelCount TargetProc)
  e₁ᵗ = proj₁ targetSplitShape
  e₂ᵗ = proj₁ (proj₂ targetSplitShape)

  endpoint-left-source-target :
    ρ (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F) ≡
    endpointEmbedding′ (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
  endpoint-left-source-target =
    endpoint-respects-channel image 0F zero
    ■ cong (λ z → Soup.endpoint z zero)
        (cong (channelEmbedding image) (sym (cast-zero channelCountEq)))
    ■ sym (endpoint-respects-channel′ 0F zero)

  split-witness-source-target :
    (e₁ ≡ e₁ᵗ SoupTerm.⋯ᵣ endpointEmbedding′) ×
    (e₂ ≡ e₂ᵗ SoupTerm.⋯ᵣ endpointEmbedding′)
  split-witness-source-target =
    group-witness-ren B₁ B₂ q b₁
      (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
      (Soup.leftEnd {n = Translation.channelCount SourceProc} 0F)
      SoupTerm.* SoupTerm.*
      (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
      (Soup.leftEnd {n = Translation.channelCount TargetProc} 0F)
      SoupTerm.* SoupTerm.*
      ρ endpointEmbedding′
      refl refl
      endpoint-left-source-target
      endpoint-left-source-target

  triple : SoupTerm.Tm (2 *ℕ n)
  triple = chanTriple e₁ (Soup.endpoint i zero) e₂

  parent : Soup.Thread n
  parent =
    plug*ᵘ F
      (chanTriple e₁ (Soup.endpoint i zero) SoupTerm.* SoupTerm.⊗
       chanTriple SoupTerm.* (Soup.endpoint i zero) e₂)

  threads′ : Vec (Soup.Thread n) m
  threads′ = SoupReduction.replaceAt (Soup.threads C) j parent

  C′ : Soup.Config n m
  C′ = Soup.config (Soup.channels C) threads′

  live-channel′ :
    (l : 𝔽 (Translation.channelCount TargetProc)) →
    lookup (Soup.channels C′) (channelEmbedding′ l) ≡
    lookup (canonicalChannels TargetProc) l
  live-channel′ zero = {!!}
  live-channel′ (suc l) =
    live-channel image (suc (Fin.cast (channelCount-⋯ₚ P 𝐒.rwk) l))
    ■ cong
        (λ channels →
          lookup channels (Fin.cast (channelCount-⋯ₚ P 𝐒.rwk) l))
        (flatten-channels-shape P
          (V.tabulate (λ x → suc x)) σ₀)
    ■ cong
        (λ channels →
          lookup channels (Fin.cast (channelCount-⋯ₚ P 𝐒.rwk) l))
        (sym (channelShape-⋯ₚ P 𝐒.rwk))
    ■ VecP.lookup-cast (channelCount-⋯ₚ P 𝐒.rwk)
        (channelShape (P Typed.⋯ₚ 𝐒.rwk)) l
    ■ cong (λ channels → lookup channels l)
        (sym (flatten-channels-shape (P Typed.⋯ₚ 𝐒.rwk)
          (V.tabulate (λ x → suc x)) τ₀))

  garbage-channel′ :
    (l : 𝔽 n) →
    ChannelOutside {P = TargetProc} channelEmbedding′ l →
    lookup (Soup.channels C′) l ≡ (false , [] , [])
  garbage-channel′ l outside =
    garbage-channel image l outside-source
    where
    outside-source : ChannelOutside {P = SourceProc} (channelEmbedding image) l
    outside-source k eq =
      outside (Fin.cast (sym channelCountEq) k)
        (cong (channelEmbedding image)
          (Fin.cast-involutive channelCountEq (sym channelCountEq) k)
         ■ eq)

  selected-channel :
    proj₁ (lookup (Soup.channels C) i) ≡ true
  selected-channel = image-channel-open image 0F

  x-triple :
    σ x ≡ triple
  x-triple =
    cong (SoupTerm._⋯ᵣ ρ)
      (cong σ₀ (atk-blockAt B₁ B₂ B (q + suc b₁) (q ↑ʳ 0F))
       ■ proj₂ (proj₂ (lookup-left-at₀ {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} 0F)))
    ■ cong (λ z → chanTriple e₁ z e₂)
        (endpoint-respects-channel image 0F zero)

  selected-thread :
    lookup (Soup.threads C) j ≡
    plug*ᵘ F (SoupTerm.K (Source.`rsplit s) SoupTerm.·¹ triple)
  selected-thread =
    live-thread image 0F
    ■ sym (T[_]-renEnv (plug*ˢ E
          (Source.K (Source.`rsplit s) Source.·¹ (Source.` x))) σ₀ ρ)
    ■ T[_]-plugᶠ* E Vσ
    ■ cong (λ z → plug*ᵘ F (SoupTerm.K (Source.`rsplit s) SoupTerm.·¹ z))
        x-triple

  target-body :
    parent
    ≡
    plug*ᵘ F
      (Translation.T[
        (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
          ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) Source.⊗
        (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
          ((q + 1) ↑ʳ 0F)))
      ] τ)
  target-body = {!!}

  T-ren-ren-coh :
    ∀ {a b c d : ℕ} (e : Source.Tm a)
      (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
      (σ₁ : Translation.Env b d) (σ₂ : Translation.Env c d) →
    ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ (κ (θ x))) →
    Translation.T[ Source._⋯_ e θ ] σ₁ ≡
    Translation.T[ Source._⋯_ (Source._⋯_ e θ) κ ] σ₂
  T-ren-ren-coh e θ κ σ₁ σ₂ coh =
    T[_]-⋯ᵣ e θ σ₁
    ■ T[_]-Env-cong e coh
    ■ sym (T[_]-⋯ᵣ e θ (σ₂ ∘ κ))
    ■ sym (T[_]-⋯ᵣ (Source._⋯_ e θ) κ σ₂)

  lift-ren-ren-coh :
    ∀ {a b c d : ℕ}
      (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
      (σ₁ : Translation.Env b d) (σ₂ : Translation.Env c d) →
    ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ (κ (θ x))) →
    (x : 𝔽 (1 + a)) →
    Translation.liftEnv σ₁ ((θ Source.↑ᵣ) x) ≡
    Translation.liftEnv σ₂ ((κ Source.↑ᵣ) ((θ Source.↑ᵣ) x))
  lift-ren-ren-coh θ κ σ₁ σ₂ coh zero = refl
  lift-ren-ren-coh θ κ σ₁ σ₂ coh (suc x) =
    cong SoupTerm.wk (coh x)

  Tᶠ-plug-ren-ren-coh :
    ∀ {a b c d : ℕ} (F₀ : SourceReduction.Frame a)
      (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
      (σ₁ : Translation.Env b d) (σ₂ : Translation.Env c d)
      (Vσ₁ : ValueEnv σ₁) (Vσ₂ : ValueEnv σ₂) →
    ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ (κ (θ x))) →
    (t : SoupTerm.Tm d) →
    SoupExpression._[_]
      (Tᶠ[ SourceReduction._⋯ᶠ_ F₀ θ ] {σ = σ₁} Vσ₁) t
    ≡
    SoupExpression._[_]
      (Tᶠ[ SourceReduction._⋯ᶠ_
             (SourceReduction._⋯ᶠ_ F₀ θ) κ ] {σ = σ₂} Vσ₂) t
  Tᶠ-plug-ren-ren-coh (SourceReduction.app₁ e d V?) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → t SoupTerm.·⟨ d ⟩ z)
      (T-ren-ren-coh e θ κ σ₁ σ₂ coh)
  Tᶠ-plug-ren-ren-coh (SourceReduction.app₂ e d V?) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → z SoupTerm.·⟨ d ⟩ t)
      (T-ren-ren-coh e θ κ σ₁ σ₂ coh)
  Tᶠ-plug-ren-ren-coh (SourceReduction.□⊗ e) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → t SoupTerm.⊗ z)
      (T-ren-ren-coh e θ κ σ₁ σ₂ coh)
  Tᶠ-plug-ren-ren-coh (V SourceReduction.⊗□) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → z SoupTerm.⊗ t)
      (T-ren-ren-coh (SourceReduction.vTm V) θ κ σ₁ σ₂ coh)
  Tᶠ-plug-ren-ren-coh (SourceReduction.□; e) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → t SoupTerm.; z)
      (T-ren-ren-coh e θ κ σ₁ σ₂ coh)
  Tᶠ-plug-ren-ren-coh (SourceReduction.`let-`in e) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → SoupTerm.`let t `in z)
      (T-ren-ren-coh e (θ Source.↑ᵣ) (κ Source.↑ᵣ)
        (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
        (lift-ren-ren-coh θ κ σ₁ σ₂ coh))
  Tᶠ-plug-ren-ren-coh (SourceReduction.`let⊗-`in e) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong (λ z → SoupTerm.`let⊗ t `in z)
      (T-ren-ren-coh e ((θ Source.↑ᵣ) Source.↑ᵣ)
        ((κ Source.↑ᵣ) Source.↑ᵣ)
        (Translation.liftEnv (Translation.liftEnv σ₁))
        (Translation.liftEnv (Translation.liftEnv σ₂))
        (lift-ren-ren-coh (θ Source.↑ᵣ) (κ Source.↑ᵣ)
          (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
          (lift-ren-ren-coh θ κ σ₁ σ₂ coh)))
  Tᶠ-plug-ren-ren-coh (SourceReduction.`inj□ i) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    refl
  Tᶠ-plug-ren-ren-coh (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    cong₂ (λ z₁ z₂ → SoupTerm.`case t `of⟨ z₁ ; z₂ ⟩)
      (T-ren-ren-coh e₁ (θ Source.↑ᵣ) (κ Source.↑ᵣ)
        (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
        (lift-ren-ren-coh θ κ σ₁ σ₂ coh))
      (T-ren-ren-coh e₂ (θ Source.↑ᵣ) (κ Source.↑ᵣ)
        (Translation.liftEnv σ₁) (Translation.liftEnv σ₂)
        (lift-ren-ren-coh θ κ σ₁ σ₂ coh))

  Tᶠ*-plug-ren-ren-coh :
    ∀ {a b c d : ℕ} (E₁ : SourceReduction.Frame* a)
      (θ : 𝔽 a → 𝔽 b) (κ : 𝔽 b → 𝔽 c)
      (σ₁ : Translation.Env b d) (σ₂ : Translation.Env c d)
      (Vσ₁ : ValueEnv σ₁) (Vσ₂ : ValueEnv σ₂) →
    ((x : 𝔽 a) → σ₁ (θ x) ≡ σ₂ (κ (θ x))) →
    (t : SoupTerm.Tm d) →
    plug*ᵘ
      (Tᶠ*[ E₁ SourceReduction.⋯ᶠ* θ ] {σ = σ₁} Vσ₁) t
    ≡
    plug*ᵘ
      (Tᶠ*[ (E₁ SourceReduction.⋯ᶠ* θ)
               SourceReduction.⋯ᶠ* κ ] {σ = σ₂} Vσ₂) t
  Tᶠ*-plug-ren-ren-coh [] θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    refl
  Tᶠ*-plug-ren-ren-coh (F₀ ∷ E₁) θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t =
    Tᶠ-plug-ren-ren-coh F₀ θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh
      (plug*ᵘ
        (Tᶠ*[ E₁ SourceReduction.⋯ᶠ* θ ] {σ = σ₁} Vσ₁) t)
    ■ cong
        (SoupExpression._[_]
          (Tᶠ[ SourceReduction._⋯ᶠ_
                 (SourceReduction._⋯ᶠ_ F₀ θ) κ ] {σ = σ₂} Vσ₂))
        (Tᶠ*-plug-ren-ren-coh E₁ θ κ σ₁ σ₂ Vσ₁ Vσ₂ coh t)

  source-target-lwk :
    (y : 𝔽 (sum (leftGroup B₁ q b₁ B₂) + sum B + 0)) →
    y ≢ x →
    σ y ≡ τ (𝐒.rwk y)
  source-target-lwk y y≢ with
    Fin.splitAt (sum (leftGroup B₁ q b₁ B₂) + sum B) y
  ... | inj₂ ()
  ... | inj₁ yz with Fin.splitAt (sum (leftGroup B₁ q b₁ B₂)) yz
  ...   | inj₁ yl = {!!}
  ...   | inj₂ yb = {!!}

  frame-lwk :
    (t : SoupTerm.Tm (2 *ℕ n)) →
    plug*ᵘ F t ≡
    plug*ᵘ
      (Tᶠ*[ E SourceReduction.⋯ᶠ* 𝐒.rwk ] {σ = τ} Vτ)
      t
  frame-lwk t =
    cong (λ E′ → plug*ᵘ (Tᶠ*[ E′ ] {σ = σ} Vσ) t) Eeq
    ■ Tᶠ*-plug-ren-ren-coh E₀ ρ⁻ 𝐒.rwk σ τ Vσ Vτ
        (λ y → source-target-lwk (ρ⁻ y) (ρ⁻-skip y)) t
    ■ cong
        (λ E′ →
          plug*ᵘ
            (Tᶠ*[ E′ SourceReduction.⋯ᶠ* 𝐒.rwk ] {σ = τ} Vτ) t)
        (sym Eeq)

  parent-live :
    parent ≡
    lookup (canonicalThreads TargetProc) 0F SoupTerm.⋯ᵣ endpointEmbedding′
  parent-live =
    target-body
    ■ frame-lwk
        (Translation.T[
          (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
            ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) Source.⊗
          (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
            ((q + 1) ↑ʳ 0F)))
        ] τ)
    ■ sym (T[_]-plugᶠ*
        (E SourceReduction.⋯ᶠ* 𝐒.rwk)
        Vτ)
    ■ T[_]-renEnv
        (plug*ˢ (E SourceReduction.⋯ᶠ* 𝐒.rwk)
          ((Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
             ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) Source.⊗
           (Source.` (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []}
             ((q + 1) ↑ʳ 0F)))))
        τ₀ endpointEmbedding′

  live-thread′ :
    (l : 𝔽 (Translation.processCount TargetProc)) →
    lookup (Soup.threads C′) (threadEmbedding′ l) ≡
    lookup (canonicalThreads TargetProc) l SoupTerm.⋯ᵣ endpointEmbedding′
  live-thread′ zero =
    VecP.lookup∘updateAt j (Soup.threads C)
    ■ parent-live
  live-thread′ (suc l) =
    VecP.lookup∘updateAt′ (threadEmbedding′ (suc l)) j
      (λ eq → case threadEmbedding-injective′ {l = suc l} {k = 0F} eq of λ ())
      (Soup.threads C)
    ■ live-thread image (Fin.cast processCountEq (suc l))
    ■ {!!}

  garbage-thread′ :
    (l : 𝔽 m) →
    ThreadOutside {P = TargetProc} threadEmbedding′ l →
    lookup (Soup.threads C′) l ≡ SoupTerm.K Source.`unit
  garbage-thread′ l outside =
    VecP.lookup∘updateAt′ l j (λ l≡j → outside 0F (sym l≡j))
      (Soup.threads C)
    ■ garbage-thread image l outside-source
    where
    outside-source : ThreadOutside {P = SourceProc} (threadEmbedding image) l
    outside-source k eq =
      outside (Fin.cast (sym processCountEq) k)
        (cong (threadEmbedding image)
          (Fin.cast-involutive processCountEq (sym processCountEq) k)
         ■ eq)
