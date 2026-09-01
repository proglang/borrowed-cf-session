module BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage

open Nat.Variables
open Fin.Patterns

private variable A : Set

rotate : ∀ p {q} → Vec A (p + q) → Vec A (q + p)
rotate p xs = V.drop p xs V.++ V.take p xs

take-++ˡ : (xs : Vec A n) (ys : Vec A m) →
  V.take n (xs V.++ ys) ≡ xs
take-++ˡ [] ys = refl
take-++ˡ (x ∷ xs) ys = cong (x ∷_) (take-++ˡ xs ys)

drop-++ˡ : (xs : Vec A n) (ys : Vec A m) →
  V.drop n (xs V.++ ys) ≡ ys
drop-++ˡ [] ys = refl
drop-++ˡ (x ∷ xs) ys = drop-++ˡ xs ys

swap-↑ˡ : (p : ℕ) (i : 𝔽 n) →
  Fin.swap n (i ↑ˡ p) ≡ p ↑ʳ i
swap-↑ˡ p i =
  cong (Fin.join p _ ∘ Sum.swap) (Fin.splitAt-↑ˡ _ i p)

swap-↑ʳ : (q : ℕ) (i : 𝔽 n) →
  Fin.swap q (q ↑ʳ i) ≡ i ↑ˡ q
swap-↑ʳ q i =
  cong (Fin.join _ q ∘ Sum.swap) (Fin.splitAt-↑ʳ q _ i)

lookup-drop :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) (i : 𝔽 q) →
  lookup (V.drop p xs) i ≡ lookup xs (p ↑ʳ i)
lookup-drop p xs i =
  sym (V.lookup-++ʳ (V.take p xs) (V.drop p xs) i) ■
  cong (λ ys → lookup ys (p ↑ʳ i)) (V.take++drop≡id p xs)

lookup-take :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) (i : 𝔽 p) →
  lookup (V.take p xs) i ≡ lookup xs (i ↑ˡ q)
lookup-take p {q} xs i =
  sym (V.lookup-++ˡ (V.take p xs) (V.drop p xs) i) ■
  cong (λ ys → lookup ys (i ↑ˡ q)) (V.take++drop≡id p xs)

lookup-rotate-split :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q))
  (part : 𝔽 q ⊎ 𝔽 p) →
  lookup (rotate p xs) (Fin.join q p part) ≡
  lookup xs (Fin.join p q (Sum.swap part))
lookup-rotate-split p xs (inj₁ j) =
  V.lookup-++ˡ (V.drop p xs) (V.take p xs) j ■
  lookup-drop p xs j
lookup-rotate-split p xs (inj₂ j) =
  V.lookup-++ʳ (V.drop p xs) (V.take p xs) j ■
  lookup-take p xs j

lookup-rotate :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) (i : 𝔽 (q + p)) →
  lookup (rotate p xs) i ≡ lookup xs (Fin.swap q i)
lookup-rotate p {q} xs i =
  cong (lookup (rotate p xs)) (sym (Fin.join-splitAt q p i)) ■
  lookup-rotate-split p xs (Fin.splitAt q i)

take-rotate :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) →
  V.take q (rotate p xs) ≡ V.drop p xs
take-rotate p xs = take-++ˡ (V.drop p xs) (V.take p xs)

drop-rotate :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) →
  V.drop q (rotate p xs) ≡ V.take p xs
drop-rotate p xs = drop-++ˡ (V.drop p xs) (V.take p xs)

rotate-++ :
  (xs : Vec A n) (ys : Vec A m) →
  rotate n (xs V.++ ys) ≡ ys V.++ xs
rotate-++ xs ys =
  cong₂ V._++_ (drop-++ˡ xs ys) (take-++ˡ xs ys)

unitProcess : ∀ {n} → Typed.Proc n
unitProcess = Typed.⟪ Source.K Source.`unit ⟫

retarget-thread :
  {threads : Vec (Soup.Thread n) m} {slot : Maybe (𝔽 m)}
  {before after : Soup.Thread n} →
  before ≡ after →
  OptionalThreadImage {n = n} threads slot before →
  OptionalThreadImage {n = n} threads slot after
retarget-thread equal (present l embedded live) =
  present l embedded (live ■ equal)
retarget-thread equal (omitted omittedEq unitEq) =
  omitted omittedEq (sym equal ■ unitEq)

record ImageReindex
  {P Q : Typed.Proc n}
  (sourceChannels : Vec (OrientedChannel c) (Translation.channelCount P))
  (targetChannels : Vec (OrientedChannel c) (Translation.channelCount Q))
  (sigma : Translation.Env n (2 *ℕ c)) : Set where
  field
    channelBackward :
      𝔽 (Translation.channelCount Q) →
      𝔽 (Translation.channelCount P)
    channelForward :
      𝔽 (Translation.channelCount P) →
      𝔽 (Translation.channelCount Q)
    channel-forward-backward :
      (i : 𝔽 (Translation.channelCount Q)) →
      channelForward (channelBackward i) ≡ i
    channel-backward-forward :
      (i : 𝔽 (Translation.channelCount P)) →
      channelBackward (channelForward i) ≡ i
    channel-entry :
      (i : 𝔽 (Translation.channelCount Q)) →
      physicalChannel (lookup targetChannels i) ≡
      physicalChannel (lookup sourceChannels (channelBackward i))
    channel-content :
      (i : 𝔽 (Translation.channelCount Q)) →
      lookup (proj₁ (flattenOriented P sourceChannels sigma))
        (channelBackward i) ≡
      lookup (proj₁ (flattenOriented Q targetChannels sigma)) i

    threadBackward :
      𝔽 (Translation.processCount Q) →
      𝔽 (Translation.processCount P)
    threadForward :
      𝔽 (Translation.processCount P) →
      𝔽 (Translation.processCount Q)
    thread-forward-backward :
      (i : 𝔽 (Translation.processCount Q)) →
      threadForward (threadBackward i) ≡ i
    thread-backward-forward :
      (i : 𝔽 (Translation.processCount P)) →
      threadBackward (threadForward i) ≡ i
    thread-content :
      (i : 𝔽 (Translation.processCount Q)) →
      lookup (proj₂ (flattenOriented P sourceChannels sigma))
        (threadBackward i) ≡
      lookup (proj₂ (flattenOriented Q targetChannels sigma)) i

open ImageReindex public

reindex-image :
  {P Q : Typed.Proc n}
  {sourceChannels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {targetChannels : Vec (OrientedChannel c) (Translation.channelCount Q)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  ImageReindex {P = P} {Q = Q} sourceChannels targetChannels sigma →
  LocalImage P sourceChannels sigma ambientChannel ambientThread C →
  LocalImage Q targetChannels sigma ambientChannel ambientThread C
reindex-image {P = P} {Q = Q}
  {sourceChannels = sourceChannels}
  {targetChannels = targetChannels} {C = C} reindex image = record
  { channelEmbedding-injective = λ {i} {j} equal →
      sym (channel-forward-backward reindex i) ■
      cong (channelForward reindex)
        (channelEmbedding-injective image
          (sym (channel-entry reindex i) ■
           equal ■
           channel-entry reindex j)) ■
      channel-forward-backward reindex j
  ; threadEmbedding = threadEmbedding image ∘ threadBackward reindex
  ; threadEmbedding-injective = λ equalᵢ equalⱼ →
      sym (thread-forward-backward reindex _) ■
      cong (threadForward reindex)
        (threadEmbedding-injective image equalᵢ equalⱼ) ■
      thread-forward-backward reindex _
  ; live-channel = λ i →
      cong (lookup (Soup.channels C))
        (channel-entry reindex i) ■
      live-channel image (channelBackward reindex i) ■
      channel-content reindex i
  ; live-thread = λ i →
      retarget-thread {threads = Soup.threads C}
        (thread-content reindex i)
        (live-thread image (threadBackward reindex i))
  ; garbage-channel = λ i outside →
      garbage-channel image i (λ k equal →
        outside (channelForward reindex k)
          (channel-entry reindex (channelForward reindex k) ■
           cong (physicalChannel ∘ lookup sourceChannels)
             (channel-backward-forward reindex k) ■
           equal))
  ; garbage-thread = λ i outside →
      garbage-thread image i (λ k equal →
        outside (threadForward reindex k)
          (cong (threadEmbedding image)
             (thread-backward-forward reindex k) ■
           equal))
  }

flatten-par-channels :
  (P Q : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P + Translation.channelCount Q))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₁ (flattenOriented (P Typed.∥ Q) channels sigma) ≡
  proj₁ (flattenOriented P
    (V.take (Translation.channelCount P) channels) sigma) V.++
  proj₁ (flattenOriented Q
    (V.drop (Translation.channelCount P) channels) sigma)
flatten-par-channels P Q channels sigma
  with flattenOriented P
         (V.take (Translation.channelCount P) channels) sigma
     | flattenOriented Q
         (V.drop (Translation.channelCount P) channels) sigma
... | channelsP , threadsP | channelsQ , threadsQ = refl

flatten-par-threads :
  (P Q : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P + Translation.channelCount Q))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₂ (flattenOriented (P Typed.∥ Q) channels sigma) ≡
  proj₂ (flattenOriented P
    (V.take (Translation.channelCount P) channels) sigma) V.++
  proj₂ (flattenOriented Q
    (V.drop (Translation.channelCount P) channels) sigma)
flatten-par-threads P Q channels sigma
  with flattenOriented P
         (V.take (Translation.channelCount P) channels) sigma
     | flattenOriented Q
         (V.drop (Translation.channelCount P) channels) sigma
... | channelsP , threadsP | channelsQ , threadsQ = refl

parallel-swap-channels :
  (P Q : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P + Translation.channelCount Q))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₁ (flattenOriented (Q Typed.∥ P)
    (rotate (Translation.channelCount P) channels) sigma) ≡
  rotate (Translation.channelCount P)
    (proj₁ (flattenOriented (P Typed.∥ Q) channels sigma))
parallel-swap-channels P Q channels sigma =
  flatten-par-channels Q P
    (rotate (Translation.channelCount P) channels) sigma ■
  cong₂ V._++_
    (cong (λ xs → proj₁ (flattenOriented Q xs sigma))
      (take-rotate (Translation.channelCount P) channels))
    (cong (λ xs → proj₁ (flattenOriented P xs sigma))
      (drop-rotate (Translation.channelCount P) channels)) ■
  sym (rotate-++
    (proj₁ (flattenOriented P
      (V.take (Translation.channelCount P) channels) sigma))
    (proj₁ (flattenOriented Q
      (V.drop (Translation.channelCount P) channels) sigma))) ■
  cong (rotate (Translation.channelCount P))
    (sym (flatten-par-channels P Q channels sigma))

parallel-swap-threads :
  (P Q : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P + Translation.channelCount Q))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₂ (flattenOriented (Q Typed.∥ P)
    (rotate (Translation.channelCount P) channels) sigma) ≡
  rotate (Translation.processCount P)
    (proj₂ (flattenOriented (P Typed.∥ Q) channels sigma))
parallel-swap-threads P Q channels sigma =
  flatten-par-threads Q P
    (rotate (Translation.channelCount P) channels) sigma ■
  cong₂ V._++_
    (cong (λ xs → proj₂ (flattenOriented Q xs sigma))
      (take-rotate (Translation.channelCount P) channels))
    (cong (λ xs → proj₂ (flattenOriented P xs sigma))
      (drop-rotate (Translation.channelCount P) channels)) ■
  sym (rotate-++
    (proj₂ (flattenOriented P
      (V.take (Translation.channelCount P) channels) sigma))
    (proj₂ (flattenOriented Q
      (V.drop (Translation.channelCount P) channels) sigma))) ■
  cong (rotate (Translation.processCount P))
    (sym (flatten-par-threads P Q channels sigma))

parallel-swap-image :
  {P Q : Typed.Proc n}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount P + Translation.channelCount Q)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (P Typed.∥ Q) channels sigma
    ambientChannel ambientThread C →
  LocalImage (Q Typed.∥ P)
    (rotate (Translation.channelCount P) channels) sigma
    ambientChannel ambientThread C
parallel-swap-image {P = P} {Q = Q} {channels = channels}
  {sigma = sigma} image = reindex-image reindex image
  where
  reindex :
    ImageReindex {P = P Typed.∥ Q} {Q = Q Typed.∥ P}
      channels (rotate (Translation.channelCount P) channels) sigma
  reindex = record
    { channelBackward = Fin.swap (Translation.channelCount Q)
    ; channelForward = Fin.swap (Translation.channelCount P)
    ; channel-forward-backward =
        Fin.swap-involutive (Translation.channelCount Q)
    ; channel-backward-forward =
        Fin.swap-involutive (Translation.channelCount P)
    ; channel-entry = λ i → cong physicalChannel
        (lookup-rotate (Translation.channelCount P) channels i)
    ; channel-content = λ i →
        sym (lookup-rotate (Translation.channelCount P)
          (proj₁ (flattenOriented (P Typed.∥ Q) channels sigma)) i) ■
        cong (λ xs → lookup xs i)
          (sym (parallel-swap-channels P Q channels sigma))
    ; threadBackward = Fin.swap (Translation.processCount Q)
    ; threadForward = Fin.swap (Translation.processCount P)
    ; thread-forward-backward =
        Fin.swap-involutive (Translation.processCount Q)
    ; thread-backward-forward =
        Fin.swap-involutive (Translation.processCount P)
    ; thread-content = λ i →
        sym (lookup-rotate (Translation.processCount P)
          (proj₂ (flattenOriented (P Typed.∥ Q) channels sigma)) i) ■
        cong (λ xs → lookup xs i)
          (sym (parallel-swap-threads P Q channels sigma))
    }

associate :
  (p q : ℕ) {r : ℕ} →
  Vec A (p + (q + r)) → Vec A ((p + q) + r)
associate p q xs =
  let rest = V.drop p xs
  in (V.take p xs V.++ V.take q rest) V.++ V.drop q rest

associate-grouped :
  (p q : ℕ) {r : ℕ} (xs : Vec A (p + (q + r))) →
  V.take p xs V.++
    (V.take q (V.drop p xs) V.++ V.drop q (V.drop p xs)) ≡ xs
associate-grouped p q xs =
  cong (V.take p xs V.++_) (V.take++drop≡id q (V.drop p xs)) ■
  V.take++drop≡id p xs

associate-cast :
  (p q : ℕ) {r : ℕ} (xs : Vec A (p + (q + r))) →
  associate p q xs ≡ V.cast (sym (Nat.+-assoc p q r)) xs
associate-cast p q {r} xs =
  sym (VecP.cast-sym (Nat.+-assoc p q r)
    (VecP.++-assoc-eqFree
      (V.take p xs)
      (V.take q (V.drop p xs))
      (V.drop q (V.drop p xs)))) ■
  cong (V.cast (sym (Nat.+-assoc p q r)))
    (associate-grouped p q xs)

associate-left :
  (p q : ℕ) {r : ℕ} (xs : Vec A (p + (q + r))) →
  V.take p (V.take (p + q) (associate p q xs)) ≡ V.take p xs
associate-left p q xs =
  cong (V.take p) (take-++ˡ
    (V.take p xs V.++ V.take q (V.drop p xs))
    (V.drop q (V.drop p xs))) ■
  take-++ˡ (V.take p xs) (V.take q (V.drop p xs))

associate-middle :
  (p q : ℕ) {r : ℕ} (xs : Vec A (p + (q + r))) →
  V.drop p (V.take (p + q) (associate p q xs)) ≡
  V.take q (V.drop p xs)
associate-middle p q xs =
  cong (V.drop p) (take-++ˡ
    (V.take p xs V.++ V.take q (V.drop p xs))
    (V.drop q (V.drop p xs))) ■
  drop-++ˡ (V.take p xs) (V.take q (V.drop p xs))

associate-right :
  (p q : ℕ) {r : ℕ} (xs : Vec A (p + (q + r))) →
  V.drop (p + q) (associate p q xs) ≡
  V.drop q (V.drop p xs)
associate-right p q xs =
  drop-++ˡ
    (V.take p xs V.++ V.take q (V.drop p xs))
    (V.drop q (V.drop p xs))

parallel-assoc-channels :
  (P Q R : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P +
      (Translation.channelCount Q + Translation.channelCount R)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₁ (flattenOriented ((P Typed.∥ Q) Typed.∥ R)
    (associate (Translation.channelCount P)
      (Translation.channelCount Q) channels) sigma) ≡
  V.cast (sym (Nat.+-assoc
    (Translation.channelCount P)
    (Translation.channelCount Q)
    (Translation.channelCount R)))
    (proj₁ (flattenOriented (P Typed.∥ (Q Typed.∥ R)) channels sigma))
parallel-assoc-channels P Q R channels sigma
  =
  flatten-par-channels (P Typed.∥ Q) R
    (associate p q channels) sigma ■
  cong₂ V._++_
    (flatten-par-channels P Q
      (V.take (p + q) (associate p q channels)) sigma)
    refl ■
  cong₂ V._++_
    (cong₂ V._++_
      (cong (λ xs → proj₁ (flattenOriented P xs sigma))
        (associate-left p q channels))
      (cong (λ xs → proj₁ (flattenOriented Q xs sigma))
        (associate-middle p q channels)))
    (cong (λ xs → proj₁ (flattenOriented R xs sigma))
      (associate-right p q channels)) ■
  sym (VecP.cast-sym (Nat.+-assoc pc qc rc)
    (VecP.++-assoc-eqFree channelsP channelsQ channelsR)) ■
  cong (V.cast (sym (Nat.+-assoc pc qc rc)))
    (cong (channelsP V.++_)
      (sym (flatten-par-channels Q R (V.drop p channels) sigma))) ■
  cong (V.cast (sym (Nat.+-assoc pc qc rc)))
    (sym (flatten-par-channels P (Q Typed.∥ R) channels sigma))
  where
  p = Translation.channelCount P
  q = Translation.channelCount Q
  pc = Translation.channelCount P
  qc = Translation.channelCount Q
  rc = Translation.channelCount R
  channelsP = proj₁ (flattenOriented P (V.take p channels) sigma)
  channelsQ = proj₁ (flattenOriented Q
    (V.take q (V.drop p channels)) sigma)
  channelsR = proj₁ (flattenOriented R
    (V.drop q (V.drop p channels)) sigma)

parallel-assoc-threads :
  (P Q R : Typed.Proc n)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount P +
      (Translation.channelCount Q + Translation.channelCount R)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  proj₂ (flattenOriented ((P Typed.∥ Q) Typed.∥ R)
    (associate (Translation.channelCount P)
      (Translation.channelCount Q) channels) sigma) ≡
  V.cast (sym (Nat.+-assoc
    (Translation.processCount P)
    (Translation.processCount Q)
    (Translation.processCount R)))
    (proj₂ (flattenOriented (P Typed.∥ (Q Typed.∥ R)) channels sigma))
parallel-assoc-threads P Q R channels sigma
  =
  flatten-par-threads (P Typed.∥ Q) R
    (associate p q channels) sigma ■
  cong₂ V._++_
    (flatten-par-threads P Q
      (V.take (p + q) (associate p q channels)) sigma)
    refl ■
  cong₂ V._++_
    (cong₂ V._++_
      (cong (λ xs → proj₂ (flattenOriented P xs sigma))
        (associate-left p q channels))
      (cong (λ xs → proj₂ (flattenOriented Q xs sigma))
        (associate-middle p q channels)))
    (cong (λ xs → proj₂ (flattenOriented R xs sigma))
      (associate-right p q channels)) ■
  sym (VecP.cast-sym (Nat.+-assoc pp pq pr)
    (VecP.++-assoc-eqFree threadsP threadsQ threadsR)) ■
  cong (V.cast (sym (Nat.+-assoc pp pq pr)))
    (cong (threadsP V.++_)
      (sym (flatten-par-threads Q R (V.drop p channels) sigma))) ■
  cong (V.cast (sym (Nat.+-assoc pp pq pr)))
    (sym (flatten-par-threads P (Q Typed.∥ R) channels sigma))
  where
  p = Translation.channelCount P
  q = Translation.channelCount Q
  pp = Translation.processCount P
  pq = Translation.processCount Q
  pr = Translation.processCount R
  threadsP = proj₂ (flattenOriented P (V.take p channels) sigma)
  threadsQ = proj₂ (flattenOriented Q
    (V.take q (V.drop p channels)) sigma)
  threadsR = proj₂ (flattenOriented R
    (V.drop q (V.drop p channels)) sigma)

parallel-assoc-image :
  {P Q R : Typed.Proc n}
  {channels : Vec (OrientedChannel c)
    (Translation.channelCount P +
      (Translation.channelCount Q + Translation.channelCount R))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (P Typed.∥ (Q Typed.∥ R)) channels sigma
    ambientChannel ambientThread C →
  LocalImage ((P Typed.∥ Q) Typed.∥ R)
    (associate (Translation.channelCount P)
      (Translation.channelCount Q) channels) sigma
    ambientChannel ambientThread C
parallel-assoc-image {P = P} {Q = Q} {R = R} {channels = channels}
  {sigma = sigma} image = reindex-image reindex image
  where
  pc = Translation.channelCount P
  qc = Translation.channelCount Q
  rc = Translation.channelCount R
  pp = Translation.processCount P
  pq = Translation.processCount Q
  pr = Translation.processCount R
  channelAssoc = Nat.+-assoc pc qc rc
  processAssoc = Nat.+-assoc pp pq pr

  reindex :
    ImageReindex
      {P = P Typed.∥ (Q Typed.∥ R)}
      {Q = (P Typed.∥ Q) Typed.∥ R}
      channels (associate pc qc channels) sigma
  reindex = record
    { channelBackward = Fin.cast channelAssoc
    ; channelForward = Fin.cast (sym channelAssoc)
    ; channel-forward-backward =
        Fin.cast-involutive (sym channelAssoc) channelAssoc
    ; channel-backward-forward =
        Fin.cast-involutive channelAssoc (sym channelAssoc)
    ; channel-entry = λ i →
        cong physicalChannel
          (cong (λ xs → lookup xs i) (associate-cast pc qc channels) ■
           VecP.lookup-cast₁ (sym channelAssoc) channels i)
    ; channel-content = λ i →
        sym (VecP.lookup-cast₁ (sym channelAssoc)
          (proj₁ (flattenOriented
            (P Typed.∥ (Q Typed.∥ R)) channels sigma)) i) ■
        cong (λ xs → lookup xs i)
          (sym (parallel-assoc-channels P Q R channels sigma))
    ; threadBackward = Fin.cast processAssoc
    ; threadForward = Fin.cast (sym processAssoc)
    ; thread-forward-backward =
        Fin.cast-involutive (sym processAssoc) processAssoc
    ; thread-backward-forward =
        Fin.cast-involutive processAssoc (sym processAssoc)
    ; thread-content = λ i →
        sym (VecP.lookup-cast₁ (sym processAssoc)
          (proj₂ (flattenOriented
            (P Typed.∥ (Q Typed.∥ R)) channels sigma)) i) ■
        cong (λ xs → lookup xs i)
          (sym (parallel-assoc-threads P Q R channels sigma))
    }

unit-head-thread :
  (P : Typed.Proc n)
  (channels : Vec (OrientedChannel c) (Translation.channelCount P))
  (sigma : Translation.Env n (2 *ℕ c)) →
  lookup (proj₂ (flattenOriented (unitProcess Typed.∥ P) channels sigma))
    0F ≡ SoupTerm.K Source.`unit
unit-head-thread P channels sigma
  with flattenOriented P channels sigma
... | channelsP , threadsP = refl

unit-tail-thread :
  (P : Typed.Proc n)
  (channels : Vec (OrientedChannel c) (Translation.channelCount P))
  (sigma : Translation.Env n (2 *ℕ c))
  (j : 𝔽 (Translation.processCount P)) →
  lookup (proj₂ (flattenOriented (unitProcess Typed.∥ P) channels sigma))
    (suc j) ≡
  lookup (proj₂ (flattenOriented P channels sigma)) j
unit-tail-thread P channels sigma j
  with flattenOriented P channels sigma
... | channelsP , threadsP = refl

unit-left-elim :
  {P : Typed.Proc n}
  {channels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (unitProcess Typed.∥ P) channels sigma
    ambientChannel ambientThread C →
  LocalImage P channels sigma ambientChannel ambientThread C
unit-left-elim {c = c} {m = m} {P = P} {channels = channels} {sigma = sigma}
  {ambientThread = ambientThread} {C = C} image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image ∘ suc
  ; threadEmbedding-injective = λ equalᵢ equalⱼ →
      Fin.suc-injective (threadEmbedding-injective image equalᵢ equalⱼ)
  ; live-channel = live-channel image
  ; live-thread = λ j →
      retarget-thread {n = c} {threads = Soup.threads C}
        (unit-tail-thread P channels sigma j)
        (live-thread image (suc j))
  ; garbage-channel = garbage-channel image
  ; garbage-thread = garbageThread
  }
  where
  garbageThread :
    (j : 𝔽 m) →
    OptionalOutside (threadEmbedding image ∘ suc) j →
    ¬ ambientThread j →
    lookup (Soup.threads C) j ≡ SoupTerm.K Source.`unit
  garbageThread j outside notAmbient
    with live-thread image 0F
  ... | omitted omittedEq unitEq =
    garbage-thread image j oldOutside notAmbient
    where
    oldOutside : OptionalOutside (threadEmbedding image) j
    oldOutside zero equal = case sym omittedEq ■ equal of λ ()
    oldOutside (suc k) = outside k
  ... | present l embedded live with FinP._≟_ l j
  ...   | yes refl =
    live ■ unit-head-thread P channels sigma
  ...   | no l≠j =
    garbage-thread image j oldOutside notAmbient
    where
    oldOutside : OptionalOutside (threadEmbedding image) j
    oldOutside zero equal = l≠j (just-injective (sym embedded ■ equal))
    oldOutside (suc k) = outside k

unit-left-intro :
  {P : Typed.Proc n}
  {channels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage P channels sigma ambientChannel ambientThread C →
  LocalImage (unitProcess Typed.∥ P) channels sigma
    ambientChannel ambientThread C
unit-left-intro {c = c} {m = m} {P = P} {channels = channels}
  {sigma = sigma} {C = C} image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = embedding′
  ; threadEmbedding-injective = embedding′-injective
  ; live-channel = live-channel image
  ; live-thread = λ where
      zero → omitted refl (unit-head-thread P channels sigma)
      (suc j) →
        retarget-thread {n = c} {threads = Soup.threads C}
          (sym (unit-tail-thread P channels sigma j))
          (live-thread image j)
  ; garbage-channel = garbage-channel image
  ; garbage-thread = λ j outside →
      garbage-thread image j (λ k → outside (suc k))
  }
  where
  embedding′ : 𝔽 (suc (Translation.processCount P)) → Maybe (𝔽 m)
  embedding′ zero = nothing
  embedding′ (suc j) = threadEmbedding image j

  embedding′-injective :
    ∀ {i j l} →
    embedding′ i ≡ just l →
    embedding′ j ≡ just l →
    i ≡ j
  embedding′-injective {zero} ()
  embedding′-injective {suc i} {zero} equalᵢ ()
  embedding′-injective {suc i} {suc j} equalᵢ equalⱼ =
    cong suc (threadEmbedding-injective image equalᵢ equalⱼ)
