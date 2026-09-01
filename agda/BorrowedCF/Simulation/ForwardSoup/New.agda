module BorrowedCF.Simulation.ForwardSoup.New where

open import Data.Fin.Base as FinBase using (punchOut)
import Data.Fin.Properties as FinP
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Simulation.ForwardSoup.Expressions
open import BorrowedCF.Simulation.ForwardSoup.Image

open Nat.Variables
open Fin.Patterns

private
  emptyEnv : Translation.Env 0 n
  emptyEnv ()

  emptyValueEnv : {n : ℕ} → ValueEnv (emptyEnv {n = n})
  emptyValueEnv ()

  plug*ˢ : SourceReduction.Frame* n → Source.Tm n → Source.Tm n
  plug*ˢ = SourceReduction._[_]*

  plug*ᵘ : SoupExpression.Frame* n → SoupTerm.Tm n → SoupTerm.Tm n
  plug*ᵘ = SoupExpression._[_]*

  newRedex : Types.𝕊 0 → Source.Tm 0
  newRedex s = Source.K (Source.`new s) Source.·¹ Source.*

  newSource : SourceReduction.Frame* 0 → Types.𝕊 0 → Typed.Proc 0
  newSource E s = Typed.⟪ plug*ˢ E (newRedex s) ⟫

  newTarget : SourceReduction.Frame* 0 → Typed.Proc 0
  newTarget E =
    Typed.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
      (Typed.⟪ plug*ˢ (SourceReduction._⋯ᶠ*_ E (Source.weaken* 2))
        (Source._⊗_ (Source.` 0F) (Source.` 1F)) ⟫)

  endpointEmbedding-new : 𝔽 (2 *ℕ 1) → 𝔽 (2 *ℕ suc n)
  endpointEmbedding-new {n = n} zero = Soup.leftEnd {n = suc n} 0F
  endpointEmbedding-new {n = n} (suc zero) = Soup.rightEnd {n = suc n} 0F

  translated-renamed :
    (e : Source.Tm 0) (ρ : 𝔽 0 → 𝔽 n) →
    Translation.T[ e ] emptyEnv ≡
    (Translation.T[ e ] (emptyEnv {n = 0})) SoupTerm.⋯ᵣ ρ
  translated-renamed e ρ =
    T[_]-Env-cong e (λ ()) ■
    T[_]-renEnv e (emptyEnv {n = 0}) ρ

  canonical-empty :
    {n : ℕ} →
    (e : Source.Tm 0) →
    Translation.T[ e ] (λ ()) ≡
    Translation.T[ e ] (emptyEnv {n = n})
  canonical-empty e = T[_]-Env-cong e (λ ())

  source-frame-env :
    SourceReduction.Frame* 0 →
    SoupExpression.Frame* (2 *ℕ n)
  source-frame-env {n = n} E =
    Tᶠ*[ E ] {σ = emptyEnv {n = 2 *ℕ n}} (emptyValueEnv {n = 2 *ℕ n})

  rhsEnv : Translation.Env 2 (2 *ℕ 1)
  rhsEnv =
    (proj₁
      (Translation.UB[ 0 ∷ 1 ∷ [] ] (Soup.leftEnd {n = 1} 0F)
        (SoupTerm.* , Soup.leftEnd {n = 1} 0F , SoupTerm.*))
    Translation.++ₛ
    proj₁
      (Translation.UB[ 0 ∷ 1 ∷ [] ] (Soup.rightEnd {n = 1} 0F)
        (SoupTerm.* , Soup.rightEnd {n = 1} 0F , SoupTerm.*)))
    Translation.++ₛ (λ ())

  T-ren-comm :
    {k k′ a b c : ℕ} →
    (e : Source.Tm k)
    (θ : 𝔽 k → 𝔽 k′)
    (σ : Translation.Env k′ a)
    (τ : Translation.Env k b)
    (η : 𝔽 b → 𝔽 c)
    (ρ : 𝔽 a → 𝔽 c) →
    (∀ x → (τ x SoupTerm.⋯ᵣ η) ≡ (σ (θ x) SoupTerm.⋯ᵣ ρ)) →
    (Translation.T[ e ] τ SoupTerm.⋯ᵣ η) ≡
    (Translation.T[ Source._⋯_ e θ ] σ SoupTerm.⋯ᵣ ρ)
  T-ren-comm e θ σ τ η ρ point =
    sym (T[_]-renEnv e τ η)
    ■ T[_]-Env-cong e point
    ■ T[_]-renEnv e (σ ∘ θ) ρ
    ■ cong (SoupTerm._⋯ᵣ ρ) (sym (T[_]-⋯ᵣ e θ σ))

  insertEndpoint0 : 𝔽 (2 *ℕ n) → 𝔽 (2 *ℕ suc n)
  insertEndpoint0 {n = n} = SoupReduction.insertEndpoint {n = n} zero

  T-new0 :
    {n : ℕ} (e : Source.Tm 0) →
    (Translation.T[ e ] (emptyEnv {n = 2 *ℕ n}) SoupTerm.⋯ᵣ insertEndpoint0 {n = n}) ≡
    (Translation.T[ Source._⋯_ e (Source.weaken* 2) ] rhsEnv
      SoupTerm.⋯ᵣ endpointEmbedding-new {n = n})
  T-new0 e =
    T-ren-comm e (Source.weaken* 2) rhsEnv emptyEnv
      insertEndpoint0 endpointEmbedding-new
      (λ ())

  T-new1 :
    {n : ℕ} (e : Source.Tm 1) →
    (Translation.T[ e ] (Translation.liftEnv (emptyEnv {n = 2 *ℕ n}))
      SoupTerm.⋯ᵣ SoupTerm.liftRen (insertEndpoint0 {n = n})) ≡
    (Translation.T[ Source._⋯_ e ((Source.weaken* 2) Source.↑ᵣ) ]
      (Translation.liftEnv rhsEnv)
      SoupTerm.⋯ᵣ SoupTerm.liftRen (endpointEmbedding-new {n = n}))
  T-new1 e =
    T-ren-comm e ((Source.weaken* 2) Source.↑ᵣ)
      (Translation.liftEnv rhsEnv)
      (Translation.liftEnv emptyEnv)
      (SoupTerm.liftRen insertEndpoint0)
      (SoupTerm.liftRen endpointEmbedding-new)
      λ where
        zero → refl
        (suc ())

  T-new2 :
    {n : ℕ} (e : Source.Tm 2) →
    (Translation.T[ e ]
      (Translation.liftEnv (Translation.liftEnv (emptyEnv {n = 2 *ℕ n})))
      SoupTerm.⋯ᵣ SoupTerm.liftRen (SoupTerm.liftRen (insertEndpoint0 {n = n}))) ≡
    (Translation.T[ Source._⋯_ e (((Source.weaken* 2) Source.↑ᵣ) Source.↑ᵣ) ]
      (Translation.liftEnv (Translation.liftEnv rhsEnv))
      SoupTerm.⋯ᵣ SoupTerm.liftRen (SoupTerm.liftRen (endpointEmbedding-new {n = n})))
  T-new2 e =
    T-ren-comm e (((Source.weaken* 2) Source.↑ᵣ) Source.↑ᵣ)
      (Translation.liftEnv (Translation.liftEnv rhsEnv))
      (Translation.liftEnv (Translation.liftEnv emptyEnv))
      (SoupTerm.liftRen (SoupTerm.liftRen insertEndpoint0))
      (SoupTerm.liftRen (SoupTerm.liftRen endpointEmbedding-new))
      λ where
        zero → refl
        (suc zero) → refl
        (suc (suc ()))

  newResult-canonical :
    {n : ℕ} →
    (E : SourceReduction.Frame* 0) →
    SoupReduction.newResult {n = n} zero (source-frame-env {n = n} E) ≡
    lookup (canonicalThreads (newTarget E)) 0F SoupTerm.⋯ᵣ endpointEmbedding-new {n = n}
  newResult-canonical [] = refl
  newResult-canonical {n = n} (SourceReduction.app₁ e d V? ∷ Es) =
    cong₂ (SoupTerm._·⟨ d ⟩_)
      (newResult-canonical {n = n} Es)
      (T-new0 {n = n} e)
  newResult-canonical {n = n} (SourceReduction.app₂ e d V? ∷ Es) =
    cong₂ (SoupTerm._·⟨ d ⟩_)
      (T-new0 {n = n} e)
      (newResult-canonical {n = n} Es)
  newResult-canonical {n = n} (SourceReduction.□⊗ e ∷ Es) =
    cong₂ SoupTerm._⊗_
      (newResult-canonical {n = n} Es)
      (T-new0 {n = n} e)
  newResult-canonical {n = n} (V SourceReduction.⊗□ ∷ Es) =
    cong₂ SoupTerm._⊗_
      (T-new0 {n = n} (SourceReduction.vTm V))
      (newResult-canonical {n = n} Es)
  newResult-canonical {n = n} (SourceReduction.□; e ∷ Es) =
    cong₂ SoupTerm._;_
      (newResult-canonical {n = n} Es)
      (T-new0 {n = n} e)
  newResult-canonical {n = n} (SourceReduction.`let-`in e ∷ Es) =
    cong₂ SoupTerm.`let_`in_
      (newResult-canonical {n = n} Es)
      (T-new1 {n = n} e)
  newResult-canonical {n = n} (SourceReduction.`let⊗-`in e ∷ Es) =
    cong₂ SoupTerm.`let⊗_`in_
      (newResult-canonical {n = n} Es)
      (T-new2 {n = n} e)
  newResult-canonical {n = n} (SourceReduction.`inj□ i ∷ Es) =
    cong (SoupTerm.`inj i)
      (newResult-canonical {n = n} Es)
  newResult-canonical {n = n} (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩ ∷ Es) =
    cong₂ (λ e es → SoupTerm.`case e `of⟨ proj₁ es ; proj₂ es ⟩)
      (newResult-canonical {n = n} Es)
      (cong₂ _,_ (T-new1 {n = n} e₁) (T-new1 {n = n} e₂))

U-new :
  {E : SourceReduction.Frame* 0} {s : Types.𝕊 0}
  {n m : ℕ} {C : Soup.Config n m} →
  SoupImage (newSource E s) C →
  Σ[ C′ ∈ Soup.Config (suc n) m ]
    (C SoupReduction.─→ₚ C′) ×
    SoupImage (newTarget E) C′
U-new {E = E} {s = s} {n = n} {m = m} {C = C} image =
  C′ ,
  SoupReduction.RUS-New j 0F F selected ,
  record
    { channelEmbedding = λ _ → 0F
    ; channelEmbedding-injective = λ { {zero} {zero} _ → refl }
    ; threadEmbedding = λ _ → j
    ; threadEmbedding-injective = λ { {zero} {zero} _ → refl }
    ; endpointEmbedding = endpointEmbedding-new
    ; endpoint-respects-channel = endpoint-respects-channel′
    ; live-channel = live-channel′
    ; live-thread = live-thread′
    ; garbage-channel = garbage-channel′
    ; garbage-thread = garbage-thread′
    }
  where
  j : 𝔽 m
  j = threadEmbedding image 0F

  ρ : 𝔽 0 → 𝔽 (2 *ℕ n)
  ρ = endpointEmbedding image

  F : SoupExpression.Frame* (2 *ℕ n)
  F = source-frame-env {n = n} E

  newThread : SoupTerm.Tm (2 *ℕ suc n)
  newThread = SoupReduction.newResult {n = n} zero F

  threads′ : Vec (Soup.Thread (suc n)) m
  threads′ =
    SoupReduction.replaceAt
      (V.map (SoupReduction.insertThreadEndpoints 0F) (Soup.threads C))
      j
      newThread

  C′ : Soup.Config (suc n) m
  C′ =
    Soup.config
      (V.insertAt (Soup.channels C) 0F (true , Soup.acq ∷ [] , Soup.acq ∷ []))
      threads′

  selected :
    lookup (Soup.threads C) j ≡
    plug*ᵘ F (SoupTerm.K (Source.`new s) SoupTerm.·¹ SoupTerm.*)
  selected =
    live-thread image 0F
    ■ cong (SoupTerm._⋯ᵣ ρ) (canonical-empty {n = 0} (plug*ˢ E (newRedex s)))
    ■ sym (translated-renamed (plug*ˢ E (newRedex s)) ρ)
    ■ T[_]-plugᶠ* E (emptyValueEnv {n = 2 *ℕ n})

  endpoint-respects-channel′ :
    (i : 𝔽 (Translation.channelCount (newTarget E))) (side : 𝔽 2) →
    endpointEmbedding-new (Soup.endpoint i side) ≡
    Soup.endpoint zero side
  endpoint-respects-channel′ zero zero = refl
  endpoint-respects-channel′ zero (suc zero) = refl

  live-channel′ :
    (i : 𝔽 (Translation.channelCount (newTarget E))) →
    lookup (Soup.channels C′) 0F ≡
    lookup (canonicalChannels (newTarget E)) i
  live-channel′ zero =
    VecP.insertAt-lookup
      (Soup.channels C) 0F
      (true , Soup.acq ∷ [] , Soup.acq ∷ [])

  live-thread′ :
    (k : 𝔽 (Translation.processCount (newTarget E))) →
    lookup (Soup.threads C′) j ≡
    lookup (canonicalThreads (newTarget E)) k SoupTerm.⋯ᵣ endpointEmbedding-new
  live-thread′ zero =
    VecP.lookup∘updateAt j
      (V.map (SoupReduction.insertThreadEndpoints 0F) (Soup.threads C))
    ■ newResult-canonical E

  garbage-channel′ :
    (i : 𝔽 (suc n)) →
    ChannelOutside {P = newTarget E} (λ _ → 0F) i →
    lookup (Soup.channels C′) i ≡ (false , [] , [])
  garbage-channel′ zero outside = ⊥-elim (outside 0F refl)
  garbage-channel′ (suc i) outside =
    VecP.insertAt-punchIn
      (Soup.channels C) 0F
      (true , Soup.acq ∷ [] , Soup.acq ∷ [])
      i
    ■ garbage-channel image i (λ ())

  garbage-thread′ :
    (k : 𝔽 m) →
    ThreadOutside {P = newTarget E} (λ _ → j) k →
    lookup (Soup.threads C′) k ≡ SoupTerm.K Source.`unit
  garbage-thread′ k outside =
    VecP.lookup∘updateAt′ k j (λ k≡j → outside 0F (sym k≡j))
      (V.map (SoupReduction.insertThreadEndpoints 0F) (Soup.threads C))
    ■ VecP.lookup-map k (SoupReduction.insertThreadEndpoints 0F) (Soup.threads C)
    ■ cong (SoupReduction.insertThreadEndpoints 0F)
        (garbage-thread image k (λ { zero old≡k → outside 0F old≡k }))
