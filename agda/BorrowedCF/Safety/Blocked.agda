-- The paper's blocked-process predicate (tex/rules/blocked.tex), transcribed.
--
-- Naming map to the tex figure `fig:blocked-expr-proc`:
--
--   B-Unit     ~ B-ExpValueBlocked
--   B-Const    ~ B-ExpConstBlocked
--   B-Par      ~ B-ParBlocked
--   B-Nu       ~ B-NuBlocked
--   B-NuAcqˡ   ~ B-NuBlockedAcq with i = 1
--   B-NuAcqʳ   ~ B-NuBlockedAcq with i = 2
--
-- `Blocked⁺` is the precise variant: B-NuBlockedAcq is imprecise when BOTH
-- binder groups start with a separator, because it declares the process blocked
-- as soon as ONE separator head is not acquired although R-Acq can still fire on
-- the other head.  `Blocked⁺` demands that EVERY separator-led side has its head
-- outside AC(P); `Blocked⁺⇒Blocked` shows the precise variant is stronger.
--
-- Owner: agent F.
module BorrowedCF.Safety.Blocked where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base hiding (Blocked)
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Safety.Progress.Expr.Plug

open Variables
open Fin.Patterns

private variable
  x y : 𝔽 n
  c : Const
  ρ : m →ᵣ n

--------------------------------------------------------------------------------
-- Blocking constants
--
-- tex B-ExpConstBlocked has the side condition
--   c ∉ {new, fork, lsplit, rsplit, drop, discard}.
-- Agda's `Const` additionally has `unit`, which the tex figure treats as the
-- value * rather than as a constant, so it is excluded here as well.

data BlockingConst : Const → Set where
  B-send   : BlockingConst `send
  B-recv   : BlockingConst `recv
  B-select : ∀ i → BlockingConst (`select i)
  B-branch : BlockingConst `branch
  B-end    : ∀ p → BlockingConst (`end p)
  B-acq    : BlockingConst `acq

blockingConst? : (c : Const) → Dec (BlockingConst c)
blockingConst? `unit        = no λ()
blockingConst? `fork        = no λ()
blockingConst? `send        = yes B-send
blockingConst? `recv        = yes B-recv
blockingConst? `drop        = no λ()
blockingConst? `acq         = yes B-acq
blockingConst? `discard     = no λ()
blockingConst? (`end p)     = yes (B-end p)
blockingConst? (`new s)     = no λ()
blockingConst? (`lsplit s)  = no λ()
blockingConst? (`rsplit s)  = no λ()
blockingConst? (`select i)  = yes (B-select i)
blockingConst? `branch      = yes B-branch

--------------------------------------------------------------------------------
-- Stuck expressions: the shape F[c v] of tex B-ExpConstBlocked.

Stuck : Tm n → Set
Stuck {n} e =
  Σ[ E ∈ Frame* n ] Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ v ∈ Tm n ]
    Value v × BlockingConst c × e ≡ E [ K c ·⟨ d ⟩ v ]*

data StuckRedex {n} : Tm n → Set where
  st : ∀ {c d} {v : Tm n} → Value v → BlockingConst c → StuckRedex (K c ·⟨ d ⟩ v)

--------------------------------------------------------------------------------
-- The BC and AC tables of the tex figure, as redex shapes.

data BCRedex {n} (x : 𝔽 n) : Tm n → Set where
  bc-send   : ∀ {d} {v : Tm n} → Value v → BCRedex x (K `send ·⟨ d ⟩ (v ⊗ (` x)))
  bc-recv   : ∀ {d} → BCRedex x (K `recv ·⟨ d ⟩ (` x))
  bc-select : ∀ {d} i → BCRedex x (K (`select i) ·⟨ d ⟩ (` x))
  bc-branch : ∀ {d} → BCRedex x (K `branch ·⟨ d ⟩ (` x))
  bc-end    : ∀ {d} p → BCRedex x (K (`end p) ·⟨ d ⟩ (` x))

data ACRedex {n} (x : 𝔽 n) : Tm n → Set where
  ac-acq : ∀ {d} → ACRedex x (K `acq ·⟨ d ⟩ (` x))

-- BC(F[c v]) on threads.  `E [ … ]*` is the tex F[·].
infix 4 _∈BCe_ _∈ACe_

data _∈BCe_ {n} (x : 𝔽 n) : Tm n → Set where
  send   : ∀ (E : Frame* n) {d} {v : Tm n} → Value v →
           x ∈BCe (E [ K `send ·⟨ d ⟩ (v ⊗ (` x)) ]*)
  recv   : ∀ (E : Frame* n) {d} → x ∈BCe (E [ K `recv ·⟨ d ⟩ (` x) ]*)
  select : ∀ (E : Frame* n) {d} i → x ∈BCe (E [ K (`select i) ·⟨ d ⟩ (` x) ]*)
  branch : ∀ (E : Frame* n) {d} → x ∈BCe (E [ K `branch ·⟨ d ⟩ (` x) ]*)
  end    : ∀ (E : Frame* n) {d} p → x ∈BCe (E [ K (`end p) ·⟨ d ⟩ (` x) ]*)

data _∈ACe_ {n} (x : 𝔽 n) : Tm n → Set where
  acq : ∀ (E : Frame* n) {d} → x ∈ACe (E [ K `acq ·⟨ d ⟩ (` x) ]*)

--------------------------------------------------------------------------------
-- Translation between the `Frame*` presentation and the structural `Plug` one.

bcRedex⇒∈BCe : (E : Frame* n) {r : Tm n} → BCRedex x r → x ∈BCe (E [ r ]*)
bcRedex⇒∈BCe E (bc-send V)    = send E V
bcRedex⇒∈BCe E bc-recv        = recv E
bcRedex⇒∈BCe E (bc-select i)  = select E i
bcRedex⇒∈BCe E bc-branch      = branch E
bcRedex⇒∈BCe E (bc-end p)     = end E p

acRedex⇒∈ACe : (E : Frame* n) {r : Tm n} → ACRedex x r → x ∈ACe (E [ r ]*)
acRedex⇒∈ACe E ac-acq = acq E

∈BCe⇒plug : x ∈BCe e → Plug (BCRedex x) e
∈BCe⇒plug (send E V)   = plug-frame* E (here (bc-send V))
∈BCe⇒plug (recv E)     = plug-frame* E (here bc-recv)
∈BCe⇒plug (select E i) = plug-frame* E (here (bc-select i))
∈BCe⇒plug (branch E)   = plug-frame* E (here bc-branch)
∈BCe⇒plug (end E p)    = plug-frame* E (here (bc-end p))

plug⇒∈BCe : Plug (BCRedex x) e → x ∈BCe e
plug⇒∈BCe p with E , r , bc , refl ← plug⇒ctx p = bcRedex⇒∈BCe E bc

∈ACe⇒plug : x ∈ACe e → Plug (ACRedex x) e
∈ACe⇒plug (acq E) = plug-frame* E (here ac-acq)

plug⇒∈ACe : Plug (ACRedex x) e → x ∈ACe e
plug⇒∈ACe p with E , r , ac , refl ← plug⇒ctx p = acRedex⇒∈ACe E ac

stuck⇒plug : Stuck e → Plug StuckRedex e
stuck⇒plug (E , c , d , v , V , BC , refl) = plug-frame* E (here (st V BC))

plug⇒stuck : Plug StuckRedex e → Stuck e
plug⇒stuck p with E , r , st V BC , refl ← plug⇒ctx p = E , _ , _ , _ , V , BC , refl

--------------------------------------------------------------------------------
-- Deciding the redex shapes.

KApp : Tm n → Set
KApp {n} e = Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ e₂ ∈ Tm n ] e ≡ K c ·⟨ d ⟩ e₂

constApp? : (e : Tm n) → Dec (KApp e)
constApp? (` x)                          = no λ{ (_ , _ , _ , ()) }
constApp? (K c)                          = no λ{ (_ , _ , _ , ()) }
constApp? (ƛ e)                          = no λ{ (_ , _ , _ , ()) }
constApp? (μ e)                          = no λ{ (_ , _ , _ , ()) }
constApp? (e₁ ; e₂)                      = no λ{ (_ , _ , _ , ()) }
constApp? (e₁ ⊗ e₂)                      = no λ{ (_ , _ , _ , ()) }
constApp? (`let e₁ `in e₂)               = no λ{ (_ , _ , _ , ()) }
constApp? (`let⊗ e₁ `in e₂)              = no λ{ (_ , _ , _ , ()) }
constApp? (`inj i e)                     = no λ{ (_ , _ , _ , ()) }
constApp? (`case e `of⟨ e₁ ; e₂ ⟩)       = no λ{ (_ , _ , _ , ()) }
constApp? (K c ·⟨ d ⟩ e₂)                = yes (c , d , e₂ , refl)
constApp? ((` x) ·⟨ d ⟩ e₂)              = no λ{ (_ , _ , _ , ()) }
constApp? ((ƛ e) ·⟨ d ⟩ e₂)              = no λ{ (_ , _ , _ , ()) }
constApp? ((μ e) ·⟨ d ⟩ e₂)              = no λ{ (_ , _ , _ , ()) }
constApp? ((e ·⟨ d′ ⟩ e′) ·⟨ d ⟩ e₂)     = no λ{ (_ , _ , _ , ()) }
constApp? ((e ; e′) ·⟨ d ⟩ e₂)           = no λ{ (_ , _ , _ , ()) }
constApp? ((e ⊗ e′) ·⟨ d ⟩ e₂)           = no λ{ (_ , _ , _ , ()) }
constApp? ((`let e `in e′) ·⟨ d ⟩ e₂)    = no λ{ (_ , _ , _ , ()) }
constApp? ((`let⊗ e `in e′) ·⟨ d ⟩ e₂)   = no λ{ (_ , _ , _ , ()) }
constApp? ((`inj i e) ·⟨ d ⟩ e₂)         = no λ{ (_ , _ , _ , ()) }
constApp? ((`case e `of⟨ e′ ; e″ ⟩) ·⟨ d ⟩ e₂) = no λ{ (_ , _ , _ , ()) }

isVar? : (x : 𝔽 n) (e : Tm n) → Dec (e ≡ ` x)
isVar? x (K c)                     = no λ()
isVar? x (ƛ e)                     = no λ()
isVar? x (μ e)                     = no λ()
isVar? x (e₁ ·⟨ d ⟩ e₂)            = no λ()
isVar? x (e₁ ; e₂)                 = no λ()
isVar? x (e₁ ⊗ e₂)                 = no λ()
isVar? x (`let e₁ `in e₂)          = no λ()
isVar? x (`let⊗ e₁ `in e₂)         = no λ()
isVar? x (`inj i e)                = no λ()
isVar? x (`case e `of⟨ e₁ ; e₂ ⟩)  = no λ()
isVar? x (` y) with y Fin.≟ x
... | yes refl = yes refl
... | no ¬eq   = no λ{ refl → ¬eq refl }

SendArg : 𝔽 n → Tm n → Set
SendArg {n} x e = Σ[ v ∈ Tm n ] Value v × e ≡ v ⊗ (` x)

sendArg? : (x : 𝔽 n) (e : Tm n) → Dec (SendArg x e)
sendArg? x (` y)                     = no λ{ (_ , _ , ()) }
sendArg? x (K c)                     = no λ{ (_ , _ , ()) }
sendArg? x (ƛ e)                     = no λ{ (_ , _ , ()) }
sendArg? x (μ e)                     = no λ{ (_ , _ , ()) }
sendArg? x (e₁ ·⟨ d ⟩ e₂)            = no λ{ (_ , _ , ()) }
sendArg? x (e₁ ; e₂)                 = no λ{ (_ , _ , ()) }
sendArg? x (`let e₁ `in e₂)          = no λ{ (_ , _ , ()) }
sendArg? x (`let⊗ e₁ `in e₂)         = no λ{ (_ , _ , ()) }
sendArg? x (`inj i e)                = no λ{ (_ , _ , ()) }
sendArg? x (`case e `of⟨ e₁ ; e₂ ⟩)  = no λ{ (_ , _ , ()) }
sendArg? x (e₁ ⊗ e₂) with value? e₁ ×? isVar? x e₂
... | yes (V , refl) = yes (e₁ , V , refl)
... | no ¬q          = no λ{ (v , V , refl) → ¬q (V , refl) }

bcRedex? : (x : 𝔽 n) (e : Tm n) → Dec (BCRedex x e)
bcRedex? x e with constApp? e
bcRedex? x .(K c ·⟨ d ⟩ e₂) | yes (c , d , e₂ , refl) = go c
  where
  go : ∀ c → Dec (BCRedex x (K c ·⟨ d ⟩ e₂))
  go `unit       = no λ()
  go `fork       = no λ()
  go `drop       = no λ()
  go `acq        = no λ()
  go `discard    = no λ()
  go (`new s)    = no λ()
  go (`lsplit s) = no λ()
  go (`rsplit s) = no λ()
  go `send with sendArg? x e₂
  ... | yes (v , V , refl) = yes (bc-send V)
  ... | no ¬q              = no λ{ (bc-send V) → ¬q (_ , V , refl) }
  go `recv with isVar? x e₂
  ... | yes refl = yes bc-recv
  ... | no ¬eq   = no λ{ bc-recv → ¬eq refl }
  go (`select i) with isVar? x e₂
  ... | yes refl = yes (bc-select i)
  ... | no ¬eq   = no λ{ (bc-select _) → ¬eq refl }
  go `branch with isVar? x e₂
  ... | yes refl = yes bc-branch
  ... | no ¬eq   = no λ{ bc-branch → ¬eq refl }
  go (`end p) with isVar? x e₂
  ... | yes refl = yes (bc-end p)
  ... | no ¬eq   = no λ{ (bc-end _) → ¬eq refl }
bcRedex? x e | no ¬q = no λ where
  (bc-send V)   → ¬q (_ , _ , _ , refl)
  bc-recv       → ¬q (_ , _ , _ , refl)
  (bc-select i) → ¬q (_ , _ , _ , refl)
  bc-branch     → ¬q (_ , _ , _ , refl)
  (bc-end p)    → ¬q (_ , _ , _ , refl)

acRedex? : (x : 𝔽 n) (e : Tm n) → Dec (ACRedex x e)
acRedex? x e with constApp? e
acRedex? x .(K c ·⟨ d ⟩ e₂) | yes (c , d , e₂ , refl) = go c
  where
  go : ∀ c → Dec (ACRedex x (K c ·⟨ d ⟩ e₂))
  go `unit       = no λ()
  go `fork       = no λ()
  go `send       = no λ()
  go `recv       = no λ()
  go `drop       = no λ()
  go `discard    = no λ()
  go (`end p)    = no λ()
  go (`new s)    = no λ()
  go (`lsplit s) = no λ()
  go (`rsplit s) = no λ()
  go (`select i) = no λ()
  go `branch     = no λ()
  go `acq with isVar? x e₂
  ... | yes refl = yes ac-acq
  ... | no ¬eq   = no λ{ ac-acq → ¬eq refl }
acRedex? x e | no ¬q = no λ{ ac-acq → ¬q (_ , _ , _ , refl) }

stuckRedex? : (e : Tm n) → Dec (StuckRedex e)
stuckRedex? e with constApp? e
stuckRedex? .(K c ·⟨ d ⟩ e₂) | yes (c , d , e₂ , refl) with blockingConst? c ×? value? e₂
... | yes (BC , V) = yes (st V BC)
... | no ¬q        = no λ{ (st V BC) → ¬q (BC , V) }
stuckRedex? e | no ¬q = no λ{ (st V BC) → ¬q (_ , _ , _ , refl) }

infix 4 _∈BCe?_ _∈ACe?_

_∈BCe?_ : (x : 𝔽 n) (e : Tm n) → Dec (x ∈BCe e)
x ∈BCe? e with plug? (bcRedex? x) e
... | yes p = yes (plug⇒∈BCe p)
... | no ¬p = no (¬p ∘ ∈BCe⇒plug)

_∈ACe?_ : (x : 𝔽 n) (e : Tm n) → Dec (x ∈ACe e)
x ∈ACe? e with plug? (acRedex? x) e
... | yes p = yes (plug⇒∈ACe p)
... | no ¬p = no (¬p ∘ ∈ACe⇒plug)

stuck? : (e : Tm n) → Dec (Stuck e)
stuck? e with plug? stuckRedex? e
... | yes p = yes (plug⇒stuck p)
... | no ¬p = no (¬p ∘ stuck⇒plug)

--------------------------------------------------------------------------------
-- BC and AC lifted to processes.

infix 4 _∈BC_ _∈AC_

data _∈BC_ {n} (x : 𝔽 n) : Proc n → Set where
  thr : ∀ {e : Tm n} → x ∈BCe e → x ∈BC ⟪ e ⟫
  ∥ˡ  : ∀ {P Q : Proc n} → x ∈BC P → x ∈BC (P ∥ Q)
  ∥ʳ  : ∀ {P Q : Proc n} → x ∈BC Q → x ∈BC (P ∥ Q)
  res : ∀ {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} →
        ((sum B₁ + sum B₂) ↑ʳ x) ∈BC P → x ∈BC (ν B₁ B₂ P)

data _∈AC_ {n} (x : 𝔽 n) : Proc n → Set where
  thr : ∀ {e : Tm n} → x ∈ACe e → x ∈AC ⟪ e ⟫
  ∥ˡ  : ∀ {P Q : Proc n} → x ∈AC P → x ∈AC (P ∥ Q)
  ∥ʳ  : ∀ {P Q : Proc n} → x ∈AC Q → x ∈AC (P ∥ Q)
  res : ∀ {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} →
        ((sum B₁ + sum B₂) ↑ʳ x) ∈AC P → x ∈AC (ν B₁ B₂ P)

infix 4 _∈BC?_ _∈AC?_

_∈BC?_ : (x : 𝔽 n) (P : Proc n) → Dec (x ∈BC P)
x ∈BC? ⟪ e ⟫ with x ∈BCe? e
... | yes m = yes (thr m)
... | no ¬m = no λ{ (thr m) → ¬m m }
x ∈BC? (P ∥ Q) with x ∈BC? P | x ∈BC? Q
... | yes m | _     = yes (∥ˡ m)
... | no _  | yes m = yes (∥ʳ m)
... | no ¬p | no ¬q = no λ{ (∥ˡ m) → ¬p m ; (∥ʳ m) → ¬q m }
x ∈BC? ν B₁ B₂ P with ((sum B₁ + sum B₂) ↑ʳ x) ∈BC? P
... | yes m = yes (res m)
... | no ¬m = no λ{ (res m) → ¬m m }

_∈AC?_ : (x : 𝔽 n) (P : Proc n) → Dec (x ∈AC P)
x ∈AC? ⟪ e ⟫ with x ∈ACe? e
... | yes m = yes (thr m)
... | no ¬m = no λ{ (thr m) → ¬m m }
x ∈AC? (P ∥ Q) with x ∈AC? P | x ∈AC? Q
... | yes m | _     = yes (∥ˡ m)
... | no _  | yes m = yes (∥ʳ m)
... | no ¬p | no ¬q = no λ{ (∥ˡ m) → ¬p m ; (∥ʳ m) → ¬q m }
x ∈AC? ν B₁ B₂ P with ((sum B₁ + sum B₂) ↑ʳ x) ∈AC? P
... | yes m = yes (res m)
... | no ¬m = no λ{ (res m) → ¬m m }

--------------------------------------------------------------------------------
-- The two head variables of a restriction.
--
-- In `ν B₁ B₂ P` the variables of `P` are laid out as
--   [side-1 variables (sum B₁)] ++ [side-2 variables (sum B₂)] ++ [outer n],
-- so the first variable of side 1 is `0F` (whenever `sum B₁` is a successor) and
-- the first variable of side 2 is `head₂`, spelled exactly as in R-Com.

head₂ : ∀ {n} (B₁ : BindGroup) (k : ℕ) (B₂ : BindGroup) → 𝔽 (sum B₁ + (suc k + sum B₂) + n)
head₂ {n} B₁ k B₂ = wkʳ ⦃ Kᵣ ⦄ n (wkˡ ⦃ Kᵣ ⦄ (sum B₁) (Fin.zero {k + sum B₂}))

--------------------------------------------------------------------------------
-- Blocked

data Blocked {n} : Proc n → Set where
  -- tex B-ExpValueBlocked
  B-Unit : Blocked ⟪ * ⟫

  -- tex B-ExpConstBlocked
  B-Const : ∀ {e : Tm n} → Stuck e → Blocked ⟪ e ⟫

  -- tex B-ParBlocked
  B-Par : ∀ {P Q : Proc n} → Blocked P → Blocked Q → Blocked (P ∥ Q)

  -- tex B-NuBlocked: {x,y} ∩ BC(P) ≠ {x,y}, i.e. not both heads are in BC(P)
  B-Nu : ∀ {b₁ b₂ B₁ B₂} {P : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + n)} →
    ¬ (0F ∈BC P × head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC P) →
    Blocked P →
    Blocked (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) P)

  -- tex B-NuBlockedAcq, i = 1
  B-NuAcqˡ : ∀ {b B₁ B₂} {P : Proc (sum (0 ∷ suc b ∷ B₁) + sum B₂ + n)} →
    ¬ (0F ∈AC P) →
    Blocked P →
    Blocked (ν (0 ∷ suc b ∷ B₁) B₂ P)

  -- tex B-NuBlockedAcq, i = 2
  B-NuAcqʳ : ∀ {B₁ b B₂} {P : Proc (sum B₁ + sum (0 ∷ suc b ∷ B₂) + n)} →
    ¬ (head₂ B₁ b B₂ ∈AC P) →
    Blocked P →
    Blocked (ν B₁ (0 ∷ suc b ∷ B₂) P)

-- The precise variant: every separator-led side must have its head out of AC(P).
data Blocked⁺ {n} : Proc n → Set where
  B-Unit⁺ : Blocked⁺ ⟪ * ⟫

  B-Const⁺ : ∀ {e : Tm n} → Stuck e → Blocked⁺ ⟪ e ⟫

  B-Par⁺ : ∀ {P Q : Proc n} → Blocked⁺ P → Blocked⁺ Q → Blocked⁺ (P ∥ Q)

  B-Nu⁺ : ∀ {b₁ b₂ B₁ B₂} {P : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + n)} →
    ¬ (0F ∈BC P × head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC P) →
    Blocked⁺ P →
    Blocked⁺ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) P)

  B-NuAcqˡ⁺ : ∀ {b b₂ B₁ B₂} {P : Proc (sum (0 ∷ suc b ∷ B₁) + sum (suc b₂ ∷ B₂) + n)} →
    ¬ (0F ∈AC P) →
    Blocked⁺ P →
    Blocked⁺ (ν (0 ∷ suc b ∷ B₁) (suc b₂ ∷ B₂) P)

  B-NuAcqʳ⁺ : ∀ {b₁ b B₁ B₂} {P : Proc (sum (suc b₁ ∷ B₁) + sum (0 ∷ suc b ∷ B₂) + n)} →
    ¬ (head₂ (suc b₁ ∷ B₁) b B₂ ∈AC P) →
    Blocked⁺ P →
    Blocked⁺ (ν (suc b₁ ∷ B₁) (0 ∷ suc b ∷ B₂) P)

  B-NuAcqˡʳ⁺ : ∀ {b b′ B₁ B₂} {P : Proc (sum (0 ∷ suc b ∷ B₁) + sum (0 ∷ suc b′ ∷ B₂) + n)} →
    ¬ (0F ∈AC P) →
    ¬ (head₂ (0 ∷ suc b ∷ B₁) b′ B₂ ∈AC P) →
    Blocked⁺ P →
    Blocked⁺ (ν (0 ∷ suc b ∷ B₁) (0 ∷ suc b′ ∷ B₂) P)

Blocked⁺⇒Blocked : {P : Proc n} → Blocked⁺ P → Blocked P
Blocked⁺⇒Blocked B-Unit⁺              = B-Unit
Blocked⁺⇒Blocked (B-Const⁺ s)         = B-Const s
Blocked⁺⇒Blocked (B-Par⁺ p q)         = B-Par (Blocked⁺⇒Blocked p) (Blocked⁺⇒Blocked q)
Blocked⁺⇒Blocked (B-Nu⁺ ¬bc p)        = B-Nu ¬bc (Blocked⁺⇒Blocked p)
Blocked⁺⇒Blocked (B-NuAcqˡ⁺ ¬ac p)    = B-NuAcqˡ ¬ac (Blocked⁺⇒Blocked p)
Blocked⁺⇒Blocked (B-NuAcqʳ⁺ ¬ac p)    = B-NuAcqʳ ¬ac (Blocked⁺⇒Blocked p)
Blocked⁺⇒Blocked (B-NuAcqˡʳ⁺ ¬acˡ ¬acʳ p) = B-NuAcqˡ ¬acˡ (Blocked⁺⇒Blocked p)

--------------------------------------------------------------------------------
-- Renamings.
--
-- Needed to move BC / AC / Blocked through the structural congruences ν-comm and
-- ν-ext, whose right-hand sides rename the body.

private
  inj-≡ : {σ : m →ᵣ n} → Inj σ → (u w : 𝔽 m) → σ u ≡ σ w → u ≡ w
  inj-≡ inj u w eq = inj eq

-- `ρ ↑* k` is the identity on the k bound variables and acts as ρ on the rest.

↑*-↑ʳ : ∀ k (ρ : m →ᵣ n) (x : 𝔽 m) → (ρ ↑* k) (k ↑ʳ x) ≡ k ↑ʳ ρ x
↑*-↑ʳ zero    ρ x = refl
↑*-↑ʳ (suc k) ρ x = cong Fin.suc (↑*-↑ʳ k ρ x)

↑*-↑ˡ : ∀ k (ρ : m →ᵣ n) (z : 𝔽 k) → (ρ ↑* k) (z ↑ˡ m) ≡ z ↑ˡ n
↑*-↑ˡ (suc k) ρ Fin.zero    = refl
↑*-↑ˡ (suc k) ρ (Fin.suc z) = cong Fin.suc (↑*-↑ˡ k ρ z)

↑*-↑ʳ⁻¹ : ∀ k (ρ : m →ᵣ n) (z : 𝔽 (k + m)) {y : 𝔽 n} →
  (ρ ↑* k) z ≡ k ↑ʳ y → ∃[ x ] z ≡ k ↑ʳ x × ρ x ≡ y
↑*-↑ʳ⁻¹ zero    ρ z           eq = z , refl , eq
↑*-↑ʳ⁻¹ (suc k) ρ Fin.zero    ()
↑*-↑ʳ⁻¹ (suc k) ρ (Fin.suc z) eq
  with x , refl , eq′ ← ↑*-↑ʳ⁻¹ k ρ z (Fin.suc-injective eq) = x , refl , eq′

-- Reflecting the shape of a term through a renaming.

private
  ·-inj : {a₁ a₂ b₁ b₂ : Tm n} {d₁ d₂ : Dir} →
    a₁ ·⟨ d₁ ⟩ b₁ ≡ a₂ ·⟨ d₂ ⟩ b₂ → a₁ ≡ a₂ × d₁ ≡ d₂ × b₁ ≡ b₂
  ·-inj refl = refl , refl , refl

⋯ᵣ-K⁻¹ : (ρ : m →ᵣ n) (r : Tm m) {c : Const} → r ⋯ ρ ≡ K c → r ≡ K c
⋯ᵣ-K⁻¹ ρ (K c) refl                    = refl
⋯ᵣ-K⁻¹ ρ (` x)                     ()
⋯ᵣ-K⁻¹ ρ (ƛ e)                     ()
⋯ᵣ-K⁻¹ ρ (μ e)                     ()
⋯ᵣ-K⁻¹ ρ (e₁ ·⟨ d ⟩ e₂)            ()
⋯ᵣ-K⁻¹ ρ (e₁ ; e₂)                 ()
⋯ᵣ-K⁻¹ ρ (e₁ ⊗ e₂)                 ()
⋯ᵣ-K⁻¹ ρ (`let e₁ `in e₂)          ()
⋯ᵣ-K⁻¹ ρ (`let⊗ e₁ `in e₂)         ()
⋯ᵣ-K⁻¹ ρ (`inj i e)                ()
⋯ᵣ-K⁻¹ ρ (`case e `of⟨ e₁ ; e₂ ⟩)  ()

⋯ᵣ-var⁻¹ : (ρ : m →ᵣ n) (r : Tm m) {y : 𝔽 n} → r ⋯ ρ ≡ ` y → ∃[ x ] r ≡ ` x × ρ x ≡ y
⋯ᵣ-var⁻¹ ρ (` x) refl                    = x , refl , refl
⋯ᵣ-var⁻¹ ρ (K c)                     ()
⋯ᵣ-var⁻¹ ρ (ƛ e)                     ()
⋯ᵣ-var⁻¹ ρ (μ e)                     ()
⋯ᵣ-var⁻¹ ρ (e₁ ·⟨ d ⟩ e₂)            ()
⋯ᵣ-var⁻¹ ρ (e₁ ; e₂)                 ()
⋯ᵣ-var⁻¹ ρ (e₁ ⊗ e₂)                 ()
⋯ᵣ-var⁻¹ ρ (`let e₁ `in e₂)          ()
⋯ᵣ-var⁻¹ ρ (`let⊗ e₁ `in e₂)         ()
⋯ᵣ-var⁻¹ ρ (`inj i e)                ()
⋯ᵣ-var⁻¹ ρ (`case e `of⟨ e₁ ; e₂ ⟩)  ()

⋯ᵣ-pair⁻¹ : (ρ : m →ᵣ n) (r : Tm m) {u w : Tm n} → r ⋯ ρ ≡ u ⊗ w →
  ∃[ u₀ ] ∃[ w₀ ] r ≡ u₀ ⊗ w₀ × u₀ ⋯ ρ ≡ u × w₀ ⋯ ρ ≡ w
⋯ᵣ-pair⁻¹ ρ (e₁ ⊗ e₂) refl                = e₁ , e₂ , refl , refl , refl
⋯ᵣ-pair⁻¹ ρ (` x)                     ()
⋯ᵣ-pair⁻¹ ρ (K c)                     ()
⋯ᵣ-pair⁻¹ ρ (ƛ e)                     ()
⋯ᵣ-pair⁻¹ ρ (μ e)                     ()
⋯ᵣ-pair⁻¹ ρ (e₁ ·⟨ d ⟩ e₂)            ()
⋯ᵣ-pair⁻¹ ρ (e₁ ; e₂)                 ()
⋯ᵣ-pair⁻¹ ρ (`let e₁ `in e₂)          ()
⋯ᵣ-pair⁻¹ ρ (`let⊗ e₁ `in e₂)         ()
⋯ᵣ-pair⁻¹ ρ (`inj i e)                ()
⋯ᵣ-pair⁻¹ ρ (`case e `of⟨ e₁ ; e₂ ⟩)  ()

⋯ᵣ-KApp⁻¹ : (ρ : m →ᵣ n) (r : Tm m) {c : Const} {d : Dir} {v : Tm n} →
  r ⋯ ρ ≡ K c ·⟨ d ⟩ v → ∃[ v₀ ] r ≡ K c ·⟨ d ⟩ v₀ × v₀ ⋯ ρ ≡ v
⋯ᵣ-KApp⁻¹ ρ (e₁ ·⟨ d ⟩ e₂) eq
  with eq₁ , refl , refl ← ·-inj eq
  with refl ← ⋯ᵣ-K⁻¹ ρ e₁ eq₁ = e₂ , refl , refl
⋯ᵣ-KApp⁻¹ ρ (` x)                     ()
⋯ᵣ-KApp⁻¹ ρ (K c)                     ()
⋯ᵣ-KApp⁻¹ ρ (ƛ e)                     ()
⋯ᵣ-KApp⁻¹ ρ (μ e)                     ()
⋯ᵣ-KApp⁻¹ ρ (e₁ ; e₂)                 ()
⋯ᵣ-KApp⁻¹ ρ (e₁ ⊗ e₂)                 ()
⋯ᵣ-KApp⁻¹ ρ (`let e₁ `in e₂)          ()
⋯ᵣ-KApp⁻¹ ρ (`let⊗ e₁ `in e₂)         ()
⋯ᵣ-KApp⁻¹ ρ (`inj i e)                ()
⋯ᵣ-KApp⁻¹ ρ (`case e `of⟨ e₁ ; e₂ ⟩)  ()

-- Redex shapes transport and reflect.

bcRedex-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} (r : Tm m) → BCRedex x r → BCRedex (ρ x) (r ⋯ ρ)
bcRedex-⋯ᵣ ρ _ (bc-send V)   = bc-send (V ⋯ᵛ ρ)
bcRedex-⋯ᵣ ρ _ bc-recv       = bc-recv
bcRedex-⋯ᵣ ρ _ (bc-select i) = bc-select i
bcRedex-⋯ᵣ ρ _ bc-branch     = bc-branch
bcRedex-⋯ᵣ ρ _ (bc-end p)    = bc-end p

acRedex-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} (r : Tm m) → ACRedex x r → ACRedex (ρ x) (r ⋯ ρ)
acRedex-⋯ᵣ ρ _ ac-acq = ac-acq

stuckRedex-⋯ᵣ : (ρ : m →ᵣ n) (r : Tm m) → StuckRedex r → StuckRedex (r ⋯ ρ)
stuckRedex-⋯ᵣ ρ _ (st V bc) = st (V ⋯ᵛ ρ) bc

bcRedex-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (r : Tm m) {t : Tm n} → r ⋯ ρ ≡ t →
  BCRedex y t → ∃[ x ] ρ x ≡ y × BCRedex x r
bcRedex-⋯ᵣ⁻¹ ρ r eq (bc-send V)
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with a₀ , b₀ , refl , eqa , eqb ← ⋯ᵣ-pair⁻¹ ρ v₀ eqv
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ b₀ eqb
  = x , refl , bc-send (value-⋯ᵣ⁻¹ a₀ ρ (subst Value (sym eqa) V))
bcRedex-⋯ᵣ⁻¹ ρ r eq bc-recv
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ v₀ eqv = x , refl , bc-recv
bcRedex-⋯ᵣ⁻¹ ρ r eq (bc-select i)
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ v₀ eqv = x , refl , bc-select i
bcRedex-⋯ᵣ⁻¹ ρ r eq bc-branch
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ v₀ eqv = x , refl , bc-branch
bcRedex-⋯ᵣ⁻¹ ρ r eq (bc-end p)
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ v₀ eqv = x , refl , bc-end p

acRedex-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (r : Tm m) {t : Tm n} → r ⋯ ρ ≡ t →
  ACRedex y t → ∃[ x ] ρ x ≡ y × ACRedex x r
acRedex-⋯ᵣ⁻¹ ρ r eq ac-acq
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  with x , refl , refl ← ⋯ᵣ-var⁻¹ ρ v₀ eqv = x , refl , ac-acq

stuckRedex-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) (r : Tm m) {t : Tm n} → r ⋯ ρ ≡ t → StuckRedex t → StuckRedex r
stuckRedex-⋯ᵣ⁻¹ ρ r eq (st V bc)
  with v₀ , refl , eqv ← ⋯ᵣ-KApp⁻¹ ρ r eq
  = st (value-⋯ᵣ⁻¹ v₀ ρ (subst Value (sym eqv) V)) bc

-- BC / AC / Stuck at the expression level.

∈BCe-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} {e : Tm m} → x ∈BCe e → ρ x ∈BCe (e ⋯ ρ)
∈BCe-⋯ᵣ ρ mem = plug⇒∈BCe (plug-⋯ᵣ ρ (bcRedex-⋯ᵣ ρ) _ (∈BCe⇒plug mem))

∈ACe-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} {e : Tm m} → x ∈ACe e → ρ x ∈ACe (e ⋯ ρ)
∈ACe-⋯ᵣ ρ mem = plug⇒∈ACe (plug-⋯ᵣ ρ (acRedex-⋯ᵣ ρ) _ (∈ACe⇒plug mem))

Stuck-⋯ᵣ : (ρ : m →ᵣ n) {e : Tm m} → Stuck e → Stuck (e ⋯ ρ)
Stuck-⋯ᵣ ρ s = plug⇒stuck (plug-⋯ᵣ ρ (stuckRedex-⋯ᵣ ρ) _ (stuck⇒plug s))

∈BCe-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (e : Tm m) → y ∈BCe (e ⋯ ρ) →
  ∃[ x ] ρ x ≡ y × x ∈BCe e
∈BCe-⋯ᵣ⁻¹ ρ {y} e mem
  with E , r , (x , eqx , br) , refl ←
    plug⇒ctx (plug-⋯ᵣ⁻¹ {Red = λ r → ∃[ x ] ρ x ≡ y × BCRedex x r} ρ
                (λ r br → bcRedex-⋯ᵣ⁻¹ ρ r refl br) e (∈BCe⇒plug mem))
  = x , eqx , bcRedex⇒∈BCe E br

∈ACe-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (e : Tm m) → y ∈ACe (e ⋯ ρ) →
  ∃[ x ] ρ x ≡ y × x ∈ACe e
∈ACe-⋯ᵣ⁻¹ ρ {y} e mem
  with E , r , (x , eqx , ar) , refl ←
    plug⇒ctx (plug-⋯ᵣ⁻¹ {Red = λ r → ∃[ x ] ρ x ≡ y × ACRedex x r} ρ
                (λ r ar → acRedex-⋯ᵣ⁻¹ ρ r refl ar) e (∈ACe⇒plug mem))
  = x , eqx , acRedex⇒∈ACe E ar

Stuck-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) (e : Tm m) → Stuck (e ⋯ ρ) → Stuck e
Stuck-⋯ᵣ⁻¹ ρ e s =
  plug⇒stuck (plug-⋯ᵣ⁻¹ ρ (λ r sr → stuckRedex-⋯ᵣ⁻¹ ρ r refl sr) e (stuck⇒plug s))

-- BC / AC at the process level.

∈BC-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} (P : Proc m) → x ∈BC P → ρ x ∈BC (P ⋯ₚ ρ)
∈BC-⋯ᵣ ρ ⟪ e ⟫    (thr mem) = thr (∈BCe-⋯ᵣ ρ mem)
∈BC-⋯ᵣ ρ (P ∥ Q)  (∥ˡ mem)  = ∥ˡ (∈BC-⋯ᵣ ρ P mem)
∈BC-⋯ᵣ ρ (P ∥ Q)  (∥ʳ mem)  = ∥ʳ (∈BC-⋯ᵣ ρ Q mem)
∈BC-⋯ᵣ ρ (ν B₁ B₂ P) (res mem) =
  res (subst (_∈BC (P ⋯ₚ ρ ↑* (sum B₁ + sum B₂)))
             (↑*-↑ʳ (sum B₁ + sum B₂) ρ _)
             (∈BC-⋯ᵣ (ρ ↑* (sum B₁ + sum B₂)) P mem))

∈AC-⋯ᵣ : (ρ : m →ᵣ n) {x : 𝔽 m} (P : Proc m) → x ∈AC P → ρ x ∈AC (P ⋯ₚ ρ)
∈AC-⋯ᵣ ρ ⟪ e ⟫    (thr mem) = thr (∈ACe-⋯ᵣ ρ mem)
∈AC-⋯ᵣ ρ (P ∥ Q)  (∥ˡ mem)  = ∥ˡ (∈AC-⋯ᵣ ρ P mem)
∈AC-⋯ᵣ ρ (P ∥ Q)  (∥ʳ mem)  = ∥ʳ (∈AC-⋯ᵣ ρ Q mem)
∈AC-⋯ᵣ ρ (ν B₁ B₂ P) (res mem) =
  res (subst (_∈AC (P ⋯ₚ ρ ↑* (sum B₁ + sum B₂)))
             (↑*-↑ʳ (sum B₁ + sum B₂) ρ _)
             (∈AC-⋯ᵣ (ρ ↑* (sum B₁ + sum B₂)) P mem))

∈BC-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (P : Proc m) → y ∈BC (P ⋯ₚ ρ) →
  ∃[ x ] ρ x ≡ y × x ∈BC P
∈BC-⋯ᵣ⁻¹ ρ ⟪ e ⟫ (thr mem)
  with x , eq , mem′ ← ∈BCe-⋯ᵣ⁻¹ ρ e mem = x , eq , thr mem′
∈BC-⋯ᵣ⁻¹ ρ (P ∥ Q) (∥ˡ mem)
  with x , eq , mem′ ← ∈BC-⋯ᵣ⁻¹ ρ P mem = x , eq , ∥ˡ mem′
∈BC-⋯ᵣ⁻¹ ρ (P ∥ Q) (∥ʳ mem)
  with x , eq , mem′ ← ∈BC-⋯ᵣ⁻¹ ρ Q mem = x , eq , ∥ʳ mem′
∈BC-⋯ᵣ⁻¹ ρ (ν B₁ B₂ P) (res mem)
  with z , eqz , mem′ ← ∈BC-⋯ᵣ⁻¹ (ρ ↑* (sum B₁ + sum B₂)) P mem
  with x , refl , refl ← ↑*-↑ʳ⁻¹ (sum B₁ + sum B₂) ρ z eqz
  = x , refl , res mem′

∈AC-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) {y : 𝔽 n} (P : Proc m) → y ∈AC (P ⋯ₚ ρ) →
  ∃[ x ] ρ x ≡ y × x ∈AC P
∈AC-⋯ᵣ⁻¹ ρ ⟪ e ⟫ (thr mem)
  with x , eq , mem′ ← ∈ACe-⋯ᵣ⁻¹ ρ e mem = x , eq , thr mem′
∈AC-⋯ᵣ⁻¹ ρ (P ∥ Q) (∥ˡ mem)
  with x , eq , mem′ ← ∈AC-⋯ᵣ⁻¹ ρ P mem = x , eq , ∥ˡ mem′
∈AC-⋯ᵣ⁻¹ ρ (P ∥ Q) (∥ʳ mem)
  with x , eq , mem′ ← ∈AC-⋯ᵣ⁻¹ ρ Q mem = x , eq , ∥ʳ mem′
∈AC-⋯ᵣ⁻¹ ρ (ν B₁ B₂ P) (res mem)
  with z , eqz , mem′ ← ∈AC-⋯ᵣ⁻¹ (ρ ↑* (sum B₁ + sum B₂)) P mem
  with x , refl , refl ← ↑*-↑ʳ⁻¹ (sum B₁ + sum B₂) ρ z eqz
  = x , refl , res mem′

-- Blocked itself.  The forward direction needs injectivity (its ν premises are
-- negations of BC/AC membership, so they are reflected, not transported); the
-- backward direction does not.

private
  head₂-fix : ∀ (B₁ : BindGroup) (j : ℕ) (B₂ : BindGroup) (ρ : m →ᵣ n) →
    (ρ ↑* (sum B₁ + (suc j + sum B₂))) (head₂ {m} B₁ j B₂) ≡ head₂ {n} B₁ j B₂
  head₂-fix {m} B₁ j B₂ ρ =
    ↑*-↑ˡ (sum B₁ + (suc j + sum B₂)) ρ (wkˡ ⦃ Kᵣ ⦄ (sum B₁) (Fin.zero {j + sum B₂}))

  ¬bc-transport : (ρ : m →ᵣ n) → Inj ρ → ∀ b₁ (B₁ : BindGroup) b₂ (B₂ : BindGroup)
    (P : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) →
    ¬ (0F ∈BC P × head₂ {m} (suc b₁ ∷ B₁) b₂ B₂ ∈BC P) →
    ¬ ( 0F ∈BC (P ⋯ₚ ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)))
      × head₂ {n} (suc b₁ ∷ B₁) b₂ B₂ ∈BC (P ⋯ₚ ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))))
  ¬bc-transport ρ inj b₁ B₁ b₂ B₂ P ¬bc (mem₁ , mem₂)
    with z₁ , eq₁ , mem₁′ ← ∈BC-⋯ᵣ⁻¹ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) P mem₁
    with z₂ , eq₂ , mem₂′ ← ∈BC-⋯ᵣ⁻¹ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) P mem₂
    with refl ← inj-≡ (↑*-inj (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) inj) z₁ 0F eq₁
    with refl ← inj-≡ (↑*-inj (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) inj)
                      z₂ (head₂ (suc b₁ ∷ B₁) b₂ B₂)
                      (eq₂ ■ sym (head₂-fix (suc b₁ ∷ B₁) b₂ B₂ ρ))
    = ¬bc (mem₁′ , mem₂′)

  ¬bc-reflect : (ρ : m →ᵣ n) → ∀ b₁ (B₁ : BindGroup) b₂ (B₂ : BindGroup)
    (P : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)) →
    ¬ ( 0F ∈BC (P ⋯ₚ ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)))
      × head₂ {n} (suc b₁ ∷ B₁) b₂ B₂ ∈BC (P ⋯ₚ ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)))) →
    ¬ (0F ∈BC P × head₂ {m} (suc b₁ ∷ B₁) b₂ B₂ ∈BC P)
  ¬bc-reflect ρ b₁ B₁ b₂ B₂ P ¬bc (mem₁ , mem₂) =
    ¬bc ( ∈BC-⋯ᵣ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) P mem₁
        , subst (_∈BC (P ⋯ₚ ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))))
                (head₂-fix (suc b₁ ∷ B₁) b₂ B₂ ρ)
                (∈BC-⋯ᵣ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) P mem₂) )

  ¬acˡ-transport : (ρ : m →ᵣ n) → Inj ρ → ∀ b (B₁ B₂ : BindGroup)
    (P : Proc (sum (0 ∷ suc b ∷ B₁) + sum B₂ + m)) →
    ¬ (0F ∈AC P) → ¬ (0F ∈AC (P ⋯ₚ ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂)))
  ¬acˡ-transport ρ inj b B₁ B₂ P ¬ac mem
    with z , eq , mem′ ← ∈AC-⋯ᵣ⁻¹ (ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂)) P mem
    with refl ← inj-≡ (↑*-inj (sum (0 ∷ suc b ∷ B₁) + sum B₂) inj) z 0F eq
    = ¬ac mem′

  ¬acˡ-reflect : (ρ : m →ᵣ n) → ∀ b (B₁ B₂ : BindGroup)
    (P : Proc (sum (0 ∷ suc b ∷ B₁) + sum B₂ + m)) →
    ¬ (0F ∈AC (P ⋯ₚ ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂))) → ¬ (0F ∈AC P)
  ¬acˡ-reflect ρ b B₁ B₂ P ¬ac mem = ¬ac (∈AC-⋯ᵣ (ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂)) P mem)

  ¬acʳ-transport : (ρ : m →ᵣ n) → Inj ρ → ∀ (B₁ : BindGroup) b (B₂ : BindGroup)
    (P : Proc (sum B₁ + sum (0 ∷ suc b ∷ B₂) + m)) →
    ¬ (head₂ {m} B₁ b B₂ ∈AC P) →
    ¬ (head₂ {n} B₁ b B₂ ∈AC (P ⋯ₚ ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂))))
  ¬acʳ-transport ρ inj B₁ b B₂ P ¬ac mem
    with z , eq , mem′ ← ∈AC-⋯ᵣ⁻¹ (ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂))) P mem
    with refl ← inj-≡ (↑*-inj (sum B₁ + sum (0 ∷ suc b ∷ B₂)) inj) z (head₂ B₁ b B₂)
                      (eq ■ sym (head₂-fix B₁ b B₂ ρ))
    = ¬ac mem′

  ¬acʳ-reflect : (ρ : m →ᵣ n) → ∀ (B₁ : BindGroup) b (B₂ : BindGroup)
    (P : Proc (sum B₁ + sum (0 ∷ suc b ∷ B₂) + m)) →
    ¬ (head₂ {n} B₁ b B₂ ∈AC (P ⋯ₚ ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂)))) →
    ¬ (head₂ {m} B₁ b B₂ ∈AC P)
  ¬acʳ-reflect ρ B₁ b B₂ P ¬ac mem =
    ¬ac (subst (_∈AC (P ⋯ₚ ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂)))) (head₂-fix B₁ b B₂ ρ)
               (∈AC-⋯ᵣ (ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂))) P mem))

Blocked-⋯ᵣ : (ρ : m →ᵣ n) → Inj ρ → {P : Proc m} → Blocked P → Blocked (P ⋯ₚ ρ)
Blocked-⋯ᵣ ρ inj B-Unit      = B-Unit
Blocked-⋯ᵣ ρ inj (B-Const s) = B-Const (Stuck-⋯ᵣ ρ s)
Blocked-⋯ᵣ ρ inj (B-Par p q) = B-Par (Blocked-⋯ᵣ ρ inj p) (Blocked-⋯ᵣ ρ inj q)
Blocked-⋯ᵣ ρ inj (B-Nu {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {P = P} ¬bc bl) =
  B-Nu (¬bc-transport ρ inj b₁ B₁ b₂ B₂ P ¬bc)
       (Blocked-⋯ᵣ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)))
                   (↑*-inj (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂)) inj) bl)
Blocked-⋯ᵣ ρ inj (B-NuAcqˡ {b = b} {B₁ = B₁} {B₂ = B₂} {P = P} ¬ac bl) =
  B-NuAcqˡ (¬acˡ-transport ρ inj b B₁ B₂ P ¬ac)
           (Blocked-⋯ᵣ (ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂))
                       (↑*-inj (sum (0 ∷ suc b ∷ B₁) + sum B₂) inj) bl)
Blocked-⋯ᵣ ρ inj (B-NuAcqʳ {B₁ = B₁} {b = b} {B₂ = B₂} {P = P} ¬ac bl) =
  B-NuAcqʳ (¬acʳ-transport ρ inj B₁ b B₂ P ¬ac)
           (Blocked-⋯ᵣ (ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂)))
                       (↑*-inj (sum B₁ + sum (0 ∷ suc b ∷ B₂)) inj) bl)

-- Reflecting the shape of a process through a renaming.

⋯ₚ-⟪⟫⁻¹ : (ρ : m →ᵣ n) (P : Proc m) {e : Tm n} → P ⋯ₚ ρ ≡ ⟪ e ⟫ →
  ∃[ e₀ ] P ≡ ⟪ e₀ ⟫ × e₀ ⋯ ρ ≡ e
⋯ₚ-⟪⟫⁻¹ ρ ⟪ e ⟫ refl    = e , refl , refl
⋯ₚ-⟪⟫⁻¹ ρ (P ∥ Q)       ()
⋯ₚ-⟪⟫⁻¹ ρ (ν A₁ A₂ P)   ()

⋯ₚ-∥⁻¹ : (ρ : m →ᵣ n) (R : Proc m) {P Q : Proc n} → R ⋯ₚ ρ ≡ P ∥ Q →
  ∃[ P₀ ] ∃[ Q₀ ] R ≡ P₀ ∥ Q₀ × P₀ ⋯ₚ ρ ≡ P × Q₀ ⋯ₚ ρ ≡ Q
⋯ₚ-∥⁻¹ ρ (P ∥ Q) refl   = P , Q , refl , refl , refl
⋯ₚ-∥⁻¹ ρ ⟪ e ⟫          ()
⋯ₚ-∥⁻¹ ρ (ν A₁ A₂ P)    ()

⋯ₚ-ν⁻¹ : (ρ : m →ᵣ n) (R : Proc m) {B₁ B₂ : BindGroup} {S : Proc (sum B₁ + sum B₂ + n)} →
  R ⋯ₚ ρ ≡ ν B₁ B₂ S →
  ∃[ S₀ ] R ≡ ν B₁ B₂ S₀ × S₀ ⋯ₚ (ρ ↑* (sum B₁ + sum B₂)) ≡ S
⋯ₚ-ν⁻¹ ρ (ν A₁ A₂ P) refl = P , refl , refl
⋯ₚ-ν⁻¹ ρ ⟪ e ⟫            ()
⋯ₚ-ν⁻¹ ρ (P ∥ Q)          ()

Blocked-⋯ᵣ⁻¹′ : (ρ : m →ᵣ n) (P : Proc m) {Q : Proc n} → P ⋯ₚ ρ ≡ Q → Blocked Q → Blocked P
Blocked-⋯ᵣ⁻¹′ ρ P eq B-Unit
  with e₀ , refl , eqe ← ⋯ₚ-⟪⟫⁻¹ ρ P eq
  with refl ← ⋯ᵣ-K⁻¹ ρ e₀ eqe = B-Unit
Blocked-⋯ᵣ⁻¹′ ρ P eq (B-Const s)
  with e₀ , refl , refl ← ⋯ₚ-⟪⟫⁻¹ ρ P eq = B-Const (Stuck-⋯ᵣ⁻¹ ρ e₀ s)
Blocked-⋯ᵣ⁻¹′ ρ P eq (B-Par bp bq)
  with P₀ , Q₀ , refl , eqp , eqq ← ⋯ₚ-∥⁻¹ ρ P eq
  = B-Par (Blocked-⋯ᵣ⁻¹′ ρ P₀ eqp bp) (Blocked-⋯ᵣ⁻¹′ ρ Q₀ eqq bq)
Blocked-⋯ᵣ⁻¹′ ρ P eq (B-Nu {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} ¬bc bl)
  with S₀ , refl , refl ← ⋯ₚ-ν⁻¹ ρ P eq
  = B-Nu (¬bc-reflect ρ b₁ B₁ b₂ B₂ S₀ ¬bc)
         (Blocked-⋯ᵣ⁻¹′ (ρ ↑* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂))) S₀ refl bl)
Blocked-⋯ᵣ⁻¹′ ρ P eq (B-NuAcqˡ {b = b} {B₁ = B₁} {B₂ = B₂} ¬ac bl)
  with S₀ , refl , refl ← ⋯ₚ-ν⁻¹ ρ P eq
  = B-NuAcqˡ (¬acˡ-reflect ρ b B₁ B₂ S₀ ¬ac)
             (Blocked-⋯ᵣ⁻¹′ (ρ ↑* (sum (0 ∷ suc b ∷ B₁) + sum B₂)) S₀ refl bl)
Blocked-⋯ᵣ⁻¹′ ρ P eq (B-NuAcqʳ {B₁ = B₁} {b = b} {B₂ = B₂} ¬ac bl)
  with S₀ , refl , refl ← ⋯ₚ-ν⁻¹ ρ P eq
  = B-NuAcqʳ (¬acʳ-reflect ρ B₁ b B₂ S₀ ¬ac)
             (Blocked-⋯ᵣ⁻¹′ (ρ ↑* (sum B₁ + sum (0 ∷ suc b ∷ B₂))) S₀ refl bl)

Blocked-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) (P : Proc m) → Blocked (P ⋯ₚ ρ) → Blocked P
Blocked-⋯ᵣ⁻¹ ρ P bl = Blocked-⋯ᵣ⁻¹′ ρ P refl bl
